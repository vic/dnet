//! Milestone M1 — the network never-recompute oracle (dist-network-transport.md
//! §4/§6.5.4). The PROVEN in-process `two_node_never_recompute`
//! (`replication.rs:64-129`) with the `export`/`import` calls routed through
//! `write_msg`/`read_msg` over a loopback `TcpStream`: node A serves blobs by
//! hash over a socket, node B fetches what it lacks, imports by re-hash gate,
//! and serves the result with `interactions == 0` and a byte-for-byte identical
//! `canonical_hash`. **Identical assertions; only the channel changed.**
//!
//! The security boundary is unchanged: `import` re-hashes the untrusted wire
//! blob and rejects a mismatch (`HashMismatch`), so a tampered byte in flight is
//! caught on arrival, never stored — the network analogue of
//! `import_rejects_corrupt_blob` (`replication.rs:135-165`).

use std::sync::Arc;

use dnx_core::effect::EffectRow;
use dnx_core::{
    canonical_hash, normalize, Blake3Hash, Canonical, DnxError, LOPath, Net, PortId, Proper, ΔL,
};
use dnx_dist::{
    bind_serve, normalize_cached, probe, probe_then_pull, read_msg, serve, sync_pull, write_msg,
    CacheError, DiskCache, Msg, ResultCache,
};

const ROOT: &str = "res";

/// (λx.x) arg — one β-reduction, pure, ΔL (verbatim from `replication.rs`).
fn id_applied() -> Result<Net<Proper, ΔL>, DnxError> {
    id_applied_with(0)
}

/// (λx.x) arg, parameterized by `key_id` — the same one-β-redex shape as
/// `id_applied`, but the ROOT free var is `free(key_id + 1)`. The β-reduction
/// fires regardless of free-var labels (the redex is the abs⋈app active pair),
/// so every `key_id` does real work (`interactions > 0`); the root free var's
/// id is what the canonical serialization emits first (`canonical_hash.rs:159-163`,
/// the DFS starts at root), so distinct `key_id`s ⇒ distinct content-addresses
/// (empirically verified; asserted as ORACLE 1 in the multi-key test). This is
/// the minimal way to mint N distinct CAS artifacts from one net shape. NOTE the
/// `arg` free var is consumed by the identity reduction and does NOT survive into
/// the NF, so it is the ROOT label — not the arg — that must vary. `key_id == 0`
/// reproduces `id_applied` byte-for-byte (root `free(1)`), so the rest of the
/// suite is unaffected.
fn id_applied_with(key_id: u32) -> Result<Net<Proper, ΔL>, DnxError> {
    let mut n = Net::<Proper, ΔL>::new(16);
    let abs = n.alloc_abs()?;
    let app = n.alloc_app()?;
    let arg = n.alloc_free(0)?;
    let res = n.alloc_free(key_id.wrapping_add(1))?;
    n.connect(abs.aux0, abs.aux1, LOPath::root())?;
    n.connect(app.aux0, res, LOPath::root())?;
    n.connect(app.aux1, arg, LOPath::root())?;
    n.connect(abs.principal, app.principal, LOPath::root())?;
    n.add_root(Arc::from(ROOT), res);
    Ok(n)
}

fn root_of(net: &Net<Canonical, ΔL>) -> Result<PortId, DnxError> {
    net.roots()
        .get(ROOT)
        .copied()
        .ok_or(DnxError::ReadbackIncomplete)
}

fn scratch(tag: &str) -> std::path::PathBuf {
    let mut p = std::env::temp_dir();
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    p.push(format!("dnx-dist-net-{tag}-{}-{nanos}", std::process::id()));
    p
}

/// THE HEADLINE (M1): A computes once and serves blobs over a TCP socket; B,
/// holding only the hash with an empty cache, pulls over the wire, imports by
/// re-hash gate, and serves the result with `interactions == 0` and an
/// identical `canonical_hash` — never recompute, over the network.
#[test]
fn two_node_never_recompute_over_tcp() -> Result<(), CacheError> {
    let dir_a = scratch("a");
    let dir_b = scratch("b");
    let disk_a = DiskCache::open(&dir_a)?;
    let disk_b = DiskCache::open(&dir_b)?;
    let pure = EffectRow::pure();

    // The caller HOLDS the content-hash of the result (computed once, up front).
    let (probe, _) = normalize(id_applied()?)?;
    let probe_root = root_of(&probe)?;
    let key: Blake3Hash = canonical_hash(&probe, probe_root)?;

    // ── Node A: compute the artifact (real work) and publish its blob. ──
    let mut mem_a = ResultCache::<ΔL>::new();
    let (result_a, stats_a) = normalize_cached(&mut mem_a, key, id_applied()?, probe_root, &pure)?;
    assert!(stats_a.interactions > 0, "A must do real reduction work");
    let root_a = root_of(&result_a)?;
    let stored = disk_a.store(&result_a, root_a)?;
    assert_eq!(
        stored, key,
        "the stored key is the result's content-address"
    );

    // ── Node A serves on a loopback TCP port (background thread). ──
    // Bind to :0 so the OS picks a free port; hand the real addr to the client.
    let listener = std::net::TcpListener::bind("127.0.0.1:0").map_err(CacheError::Io)?;
    let addr = listener.local_addr().map_err(CacheError::Io)?;
    let server = std::thread::spawn(move || serve(&listener, &disk_a));

    // ── Node B: holds `key`, empty cache → ask A only for what it lacks. ──
    let have = disk_b.missing(&[key]);
    assert_eq!(
        have,
        vec![key],
        "B lacks the key, so it must request exactly it"
    );

    // Fetch over the wire: Want(have) → Blobs(pairs) → import (re-hash gate).
    sync_pull::<ΔL>(&addr.to_string(), &have, &disk_b)?;
    assert!(disk_b.contains(&key), "import must persist B's copy");
    assert!(
        disk_b.missing(&[key]).is_empty(),
        "after the wire fetch, B lacks nothing"
    );

    // ── Node B serves the result — WITHOUT recomputing. ──
    let (net_b, root_b): (Net<Canonical, ΔL>, PortId) = disk_b
        .load(&key)?
        .ok_or(CacheError::Decode(DnxError::ReadbackIncomplete))?;
    let mut mem_b = ResultCache::<ΔL>::new();
    mem_b.insert(key, Arc::new(net_b), root_b)?;
    let (served, stats_b) = normalize_cached(&mut mem_b, key, id_applied()?, probe_root, &pure)?;

    assert_eq!(
        stats_b.interactions, 0,
        "B fetched by hash over TCP — ZERO steps"
    );
    assert_eq!(
        canonical_hash(&served, root_b)?,
        key,
        "B's served value is byte-for-byte A's value (identical hash)"
    );

    // The server thread loops over `incoming`; dropping the client closes the
    // single connection. Joining is best-effort (it blocks on the next accept),
    // so we detach: the OS reclaims the socket on test-process exit.
    drop(server);

    let _ = std::fs::remove_dir_all(&dir_a);
    let _ = std::fs::remove_dir_all(&dir_b);
    Ok(())
}

/// The negative trust beat over the wire: a `Blobs` payload whose bytes are
/// tampered re-hashes to something other than its claimed key, so `import`
/// rejects it (`HashMismatch`) — nothing stored. Same gate as
/// `import_rejects_corrupt_blob`, exercised through `write_msg`/`read_msg`.
#[test]
fn wire_blob_tamper_is_rejected_on_import() -> Result<(), CacheError> {
    let dir_a = scratch("ta");
    let dir_b = scratch("tb");
    let disk_a = DiskCache::open(&dir_a)?;
    let disk_b = DiskCache::open(&dir_b)?;

    let (result, _) = normalize(id_applied()?)?;
    let root = root_of(&result)?;
    let key = disk_a.store(&result, root)?;
    let blob = disk_a
        .export(&key)?
        .ok_or(CacheError::Decode(DnxError::ReadbackIncomplete))?;

    // A's server tampers one byte of the blob before framing it onto the wire.
    let listener = std::net::TcpListener::bind("127.0.0.1:0").map_err(CacheError::Io)?;
    let addr = listener.local_addr().map_err(CacheError::Io)?;
    let server = std::thread::spawn(move || -> Result<(), CacheError> {
        let (mut conn, _) = listener.accept().map_err(CacheError::Io)?;
        let mut tampered = blob;
        let last = tampered.len() - 1;
        tampered[last] ^= 0xff;
        // Drain the client's Want, then reply with the corrupted Blobs frame.
        let _ = dnx_dist::read_msg(&mut conn)?;
        dnx_dist::write_msg(&mut conn, &Msg::Blobs(vec![(key, tampered)]))
    });

    let r = sync_pull::<ΔL>(&addr.to_string(), &[key], &disk_b);
    assert!(
        matches!(
            r,
            Err(CacheError::HashMismatch) | Err(CacheError::Decode(_))
        ),
        "a tampered wire blob must be rejected on import, got {r:?}"
    );
    assert!(
        !disk_b.contains(&key),
        "a rejected wire import must leave nothing on disk"
    );

    let _ = server.join();
    let _ = std::fs::remove_dir_all(&dir_a);
    let _ = std::fs::remove_dir_all(&dir_b);
    Ok(())
}

/// The advertise probe (dist-network-transport.md §3.2a): node B asks A "do you
/// hold these?" over the wire and gets a per-key `Held` answer that is exactly
/// A's `contains` — `true` for the stored key, `false` for an absent one. This
/// lets B probe before pulling, and the reply carries no blob bytes (a pure
/// optimization hint, outside the TCB).
#[test]
fn probe_reports_what_peer_holds() -> Result<(), CacheError> {
    let dir_a = scratch("pa");
    let disk_a = DiskCache::open(&dir_a)?;

    // A holds exactly one artifact's blob.
    let (result, _) = normalize(id_applied()?)?;
    let root = root_of(&result)?;
    let held_key = disk_a.store(&result, root)?;
    let absent_key: Blake3Hash = [0xab; 32];
    assert_ne!(held_key, absent_key, "the absent key must differ from A's");

    let listener = std::net::TcpListener::bind("127.0.0.1:0").map_err(CacheError::Io)?;
    let addr = listener.local_addr().map_err(CacheError::Io)?;
    let server = std::thread::spawn(move || serve(&listener, &disk_a));

    // B probes a held key and an absent one — the answer is A's `contains`.
    let present = probe(&addr.to_string(), &[held_key, absent_key])?;
    assert_eq!(
        present,
        vec![true, false],
        "Held mirrors A's per-key contains: held → true, absent → false"
    );

    drop(server);
    let _ = std::fs::remove_dir_all(&dir_a);
    Ok(())
}

/// The skip-optimization wired into the fetch path (dist-network-transport.md
/// §3.2a:154-159): B `probe_then_pull`s a key A HOLDS and a key A LACKS. The
/// proof that the lacked key is skipped — not merely missing — is the server's
/// recorded `Want`: it contains ONLY the held key, so B never sent a `Want` for
/// the absent one. The held key still lands by re-hash gate; the absent key is
/// neither requested nor stored.
#[test]
fn probe_then_pull_skips_keys_the_peer_lacks() -> Result<(), CacheError> {
    let dir_a = scratch("sa");
    let dir_b = scratch("sb");
    let disk_a = DiskCache::open(&dir_a)?;
    let disk_b = DiskCache::open(&dir_b)?;

    // A holds exactly one artifact; the second key is one A cannot serve.
    let (result, _) = normalize(id_applied()?)?;
    let root = root_of(&result)?;
    let held_key = disk_a.store(&result, root)?;
    let absent_key: Blake3Hash = [0xcd; 32];
    assert_ne!(held_key, absent_key, "the absent key must differ from A's");

    // A's server: conn 1 answers the Have probe with the real `contains`; conn 2
    // answers the Want, RECORDING which keys B actually requested. The recorded
    // Want is the oracle for "the lacked key was skipped".
    let listener = std::net::TcpListener::bind("127.0.0.1:0").map_err(CacheError::Io)?;
    let addr = listener.local_addr().map_err(CacheError::Io)?;
    let (tx, rx) = std::sync::mpsc::channel::<Vec<Blake3Hash>>();
    let server = std::thread::spawn(move || -> Result<(), CacheError> {
        let mut conns = listener.incoming();
        // conn 1: the probe.
        let mut probe_s = conns
            .next()
            .ok_or_else(|| CacheError::Io(std::io::Error::other("no probe conn")))?
            .map_err(CacheError::Io)?;
        match read_msg(&mut probe_s)? {
            Msg::Have(keys) => {
                let present = keys.iter().map(|k| disk_a.contains(k)).collect();
                write_msg(&mut probe_s, &Msg::Held(present))?;
            }
            other => write_msg(
                &mut probe_s,
                &Msg::Failed(2, format!("want Have, got {other:?}")),
            )?,
        }
        // conn 2: the pull — record the requested keys, then serve `export`.
        let mut pull_s = conns
            .next()
            .ok_or_else(|| CacheError::Io(std::io::Error::other("no pull conn")))?
            .map_err(CacheError::Io)?;
        match read_msg(&mut pull_s)? {
            Msg::Want(keys) => {
                let _ = tx.send(keys.clone());
                let mut pairs = Vec::new();
                for k in keys {
                    if let Some(blob) = disk_a.export(&k)? {
                        pairs.push((k, blob));
                    }
                }
                write_msg(&mut pull_s, &Msg::Blobs(pairs))?;
            }
            other => write_msg(
                &mut pull_s,
                &Msg::Failed(2, format!("want Want, got {other:?}")),
            )?,
        }
        Ok(())
    });

    // B holds neither key; probe-before-pull narrows the request to A's holdings.
    probe_then_pull::<ΔL>(&addr.to_string(), &[held_key, absent_key], &disk_b)?;

    // THE ORACLE: the server's recorded Want is exactly the held key — the
    // absent key was skipped, never requested over the wire.
    let requested = rx
        .recv()
        .map_err(|_| CacheError::Io(std::io::Error::other("server recorded no Want")))?;
    assert_eq!(
        requested,
        vec![held_key],
        "B must request ONLY the key A advertised holding — the lacked key is skipped"
    );

    assert!(disk_b.contains(&held_key), "the held key is imported");
    assert!(
        !disk_b.contains(&absent_key),
        "the skipped key is never stored"
    );

    let _ = server.join();
    let _ = std::fs::remove_dir_all(&dir_a);
    let _ = std::fs::remove_dir_all(&dir_b);
    Ok(())
}

/// The all-lacked corner: if the peer holds NONE of `want`, `probe_then_pull`
/// opens NO pull connection at all — the request is skipped, not sent empty
/// (dist-network-transport.md:157). The single probe connection is the whole
/// exchange; B stores nothing and errors nowhere.
#[test]
fn probe_then_pull_opens_no_pull_when_peer_holds_nothing() -> Result<(), CacheError> {
    let dir_b = scratch("nb");
    let disk_b = DiskCache::open(&dir_b)?;
    let absent_key: Blake3Hash = [0xef; 32];

    // A serves but holds nothing of what B wants; its `contains` is all-false.
    let dir_a = scratch("na");
    let disk_a = DiskCache::open(&dir_a)?;
    let listener = std::net::TcpListener::bind("127.0.0.1:0").map_err(CacheError::Io)?;
    let addr = listener.local_addr().map_err(CacheError::Io)?;
    let (tx, rx) = std::sync::mpsc::channel::<()>();
    let server = std::thread::spawn(move || -> Result<(), CacheError> {
        let mut conns = listener.incoming();
        let mut probe_s = conns
            .next()
            .ok_or_else(|| CacheError::Io(std::io::Error::other("no probe conn")))?
            .map_err(CacheError::Io)?;
        match read_msg(&mut probe_s)? {
            Msg::Have(keys) => {
                let present = keys.iter().map(|k| disk_a.contains(k)).collect();
                write_msg(&mut probe_s, &Msg::Held(present))?;
            }
            other => write_msg(
                &mut probe_s,
                &Msg::Failed(2, format!("want Have, got {other:?}")),
            )?,
        }
        // Signal that the probe completed; a second `incoming` would be a pull —
        // if B (correctly) opens none, this thread ends after the probe.
        let _ = tx.send(());
        Ok(())
    });

    probe_then_pull::<ΔL>(&addr.to_string(), &[absent_key], &disk_b)?;

    rx.recv()
        .map_err(|_| CacheError::Io(std::io::Error::other("probe never completed")))?;
    assert!(
        !disk_b.contains(&absent_key),
        "nothing held by the peer ⇒ nothing pulled, nothing stored"
    );

    let _ = server.join();
    let _ = std::fs::remove_dir_all(&dir_a);
    let _ = std::fs::remove_dir_all(&dir_b);
    Ok(())
}

/// THE CLIENT-HARNESS HEADLINE: the production fetch path end-to-end. B holds
/// only `net_hash` with an empty cache and runs `probe_then_pull` against A's
/// REAL `serve` loop (not a hand-rolled per-conn stub) — probe narrows the
/// request to A's holdings, then the pull lands the blob by re-hash gate. B then
/// runs the §6.5.3 never-recompute tail (`load` → re-hash-verified `insert` →
/// `normalize_cached`) and serves the result with `interactions == 0` and a
/// byte-for-byte identical `canonical_hash`.
///
/// This joins the two already-green halves the suite proves separately:
/// `probe_then_pull_skips_keys_the_peer_lacks` (`:228`, the skip oracle, but on
/// a stub server and stopping at `contains`) and `two_node_never_recompute_over_tcp`
/// (`:64`, the never-recompute tail, but via `sync_pull`). `serve` (`wire.rs:256`)
/// answers `probe_then_pull`'s two sequential connections (Have→Held, then
/// Want→Blobs) on its serial `incoming` loop — the real server, the real fetch
/// path (dist-network-transport.md §3.2a:150-159 + §6.5.3:401-409).
#[test]
fn probe_then_pull_over_serve_never_recomputes() -> Result<(), CacheError> {
    let dir_a = scratch("ha");
    let dir_b = scratch("hb");
    let disk_a = DiskCache::open(&dir_a)?;
    let disk_b = DiskCache::open(&dir_b)?;
    let pure = EffectRow::pure();

    // The caller HOLDS the content-hash of the result (computed once, up front).
    let (nf, _) = normalize(id_applied()?)?;
    let probe_root = root_of(&nf)?;
    let key: Blake3Hash = canonical_hash(&nf, probe_root)?;

    // ── Node A: compute the artifact (real work) and publish its blob. ──
    let mut mem_a = ResultCache::<ΔL>::new();
    let (result_a, stats_a) = normalize_cached(&mut mem_a, key, id_applied()?, probe_root, &pure)?;
    assert!(stats_a.interactions > 0, "A must do real reduction work");
    let root_a = root_of(&result_a)?;
    let stored = disk_a.store(&result_a, root_a)?;
    assert_eq!(
        stored, key,
        "the stored key is the result's content-address"
    );

    // ── Node A serves on a loopback port via the REAL `serve` loop. ──
    let listener = std::net::TcpListener::bind("127.0.0.1:0").map_err(CacheError::Io)?;
    let addr = listener.local_addr().map_err(CacheError::Io)?;
    let server = std::thread::spawn(move || serve(&listener, &disk_a));

    // ── Node B: empty cache → probe-before-pull the production fetch path. ──
    let want = disk_b.missing(&[key]);
    assert_eq!(
        want,
        vec![key],
        "B lacks the key, so it must request exactly it"
    );
    probe_then_pull::<ΔL>(&addr.to_string(), &want, &disk_b)?;
    assert!(disk_b.contains(&key), "probe_then_pull must land B's copy");
    assert!(
        disk_b.missing(&[key]).is_empty(),
        "after probe_then_pull, B lacks nothing"
    );

    // ── Node B serves the result — WITHOUT recomputing (§6.5.3:401-409). ──
    let (net_b, root_b): (Net<Canonical, ΔL>, PortId) = disk_b
        .load(&key)?
        .ok_or(CacheError::Decode(DnxError::ReadbackIncomplete))?;
    let mut mem_b = ResultCache::<ΔL>::new();
    mem_b.insert(key, Arc::new(net_b), root_b)?;
    let (served, stats_b) = normalize_cached(&mut mem_b, key, id_applied()?, probe_root, &pure)?;

    assert_eq!(
        stats_b.interactions, 0,
        "B fetched by hash via probe_then_pull — ZERO steps"
    );
    assert_eq!(
        canonical_hash(&served, root_b)?,
        key,
        "B's served value is byte-for-byte A's value (identical hash)"
    );

    drop(server);
    let _ = std::fs::remove_dir_all(&dir_a);
    let _ = std::fs::remove_dir_all(&dir_b);
    Ok(())
}

/// THE HARNESS HEADLINE: A publishes via the thin addr-binding `bind_serve`
/// entry — the harness BINDS the configured loopback address itself (the bin's
/// core, dist-network-transport.md §6.5.2:354-355) instead of the test handing
/// in a pre-bound listener. The test passes port `0` and learns the real port
/// from the harness's `ready` channel (the SAME binding — no drop-then-rebind,
/// no fixed-port flake, §6.5.4). B then runs the production `probe_then_pull`
/// never-recompute tail against it and serves the result with `interactions == 0`
/// and a byte-for-byte identical `canonical_hash`. Identical oracle to
/// `probe_then_pull_over_serve_never_recomputes` (`:374`); only A's bind moved
/// from the test into the harness (wire.rs:251-255 — "the thin serve binary
/// binds the configured address and hands it here").
#[test]
fn bind_serve_binds_addr_and_never_recomputes() -> Result<(), CacheError> {
    let dir_a = scratch("ba");
    let dir_b = scratch("bb");
    let disk_a = DiskCache::open(&dir_a)?;
    let disk_b = DiskCache::open(&dir_b)?;
    let pure = EffectRow::pure();

    let (nf, _) = normalize(id_applied()?)?;
    let probe_root = root_of(&nf)?;
    let key: Blake3Hash = canonical_hash(&nf, probe_root)?;

    // ── Node A: compute the artifact (real work) and publish its blob. ──
    let mut mem_a = ResultCache::<ΔL>::new();
    let (result_a, stats_a) = normalize_cached(&mut mem_a, key, id_applied()?, probe_root, &pure)?;
    assert!(stats_a.interactions > 0, "A must do real reduction work");
    let root_a = root_of(&result_a)?;
    let stored = disk_a.store(&result_a, root_a)?;
    assert_eq!(
        stored, key,
        "the stored key is the result's content-address"
    );

    // ── Node A serves via the thin harness — it binds the addr ITSELF; the
    //    real bound port arrives on `ready` (port 0 ⇒ OS picks, no flake). ──
    let (ready_tx, ready_rx) = std::sync::mpsc::channel();
    let server = std::thread::spawn(move || bind_serve("127.0.0.1:0", &ready_tx, &disk_a));
    let addr = ready_rx
        .recv()
        .map_err(|_| CacheError::Io(std::io::Error::other("harness never bound")))?
        .to_string();

    // ── Node B: empty cache → probe-before-pull the production fetch path. ──
    let want = disk_b.missing(&[key]);
    assert_eq!(
        want,
        vec![key],
        "B lacks the key, so it must request exactly it"
    );
    probe_then_pull::<ΔL>(&addr, &want, &disk_b)?;
    assert!(disk_b.contains(&key), "probe_then_pull must land B's copy");

    // ── Node B serves the result — WITHOUT recomputing (§6.5.3:401-409). ──
    let (net_b, root_b): (Net<Canonical, ΔL>, PortId) = disk_b
        .load(&key)?
        .ok_or(CacheError::Decode(DnxError::ReadbackIncomplete))?;
    let mut mem_b = ResultCache::<ΔL>::new();
    mem_b.insert(key, Arc::new(net_b), root_b)?;
    let (served, stats_b) = normalize_cached(&mut mem_b, key, id_applied()?, probe_root, &pure)?;

    assert_eq!(
        stats_b.interactions, 0,
        "B fetched by hash from the harness-bound server — ZERO steps"
    );
    assert_eq!(
        canonical_hash(&served, root_b)?,
        key,
        "B's served value is byte-for-byte A's value (identical hash)"
    );

    drop(server);
    let _ = std::fs::remove_dir_all(&dir_a);
    let _ = std::fs::remove_dir_all(&dir_b);
    Ok(())
}

/// Compute artifact `key_id` (real reduction work) and publish its blob into
/// `disk`; returns its content-address. Asserts the compute did >0 interactions
/// so the later `interactions == 0` on B is a genuine fetch, not a no-op.
fn publish(disk: &DiskCache, key_id: u32, pure: &EffectRow) -> Result<Blake3Hash, CacheError> {
    let (nf, _) = normalize(id_applied_with(key_id)?)?;
    let root = root_of(&nf)?;
    let key = canonical_hash(&nf, root)?;
    let mut mem = ResultCache::<ΔL>::new();
    let (result, stats) = normalize_cached(&mut mem, key, id_applied_with(key_id)?, root, pure)?;
    assert!(
        stats.interactions > 0,
        "publishing artifact {key_id} must do real work"
    );
    let stored = disk.store(&result, root_of(&result)?)?;
    assert_eq!(
        stored, key,
        "the stored key is the artifact's content-address"
    );
    Ok(key)
}

/// THE MULTI-KEY HEADLINE: A's CAS holds N=3 distinct artifacts; B (empty cache)
/// fetches only a SUBSET of 2 over the wire and serves each WITHOUT recomputing,
/// byte-for-byte identical to A's — while the un-requested third artifact is
/// never transferred nor stored. This lifts the single-key never-recompute proof
/// (`bind_serve_binds_addr_and_never_recomputes`, `:445`) to a many-artifact CAS
/// with a partial fetch, the realistic distribution shape: a peer holds many
/// results, a node pulls just the ones it needs (dist-network-transport.md
/// §3.2a:150-159 + §6.5.3:401-409).
///
/// Three independent oracles:
///   1. DISTINCT KEYS — the three `key_id`s mint three distinct content-addresses
///      (the fixture's correctness; a collapse would make "subset" meaningless).
///   2. SUBSET ONLY — after the fetch, B holds exactly the two requested keys and
///      `missing` still reports the third: the un-asked blob never crossed.
///   3. NEVER RECOMPUTE — each fetched artifact serves with `interactions == 0`
///      and a `canonical_hash` byte-identical to A's stored key.
#[test]
fn multi_key_subset_fetch_never_recomputes() -> Result<(), CacheError> {
    let dir_a = scratch("ma");
    let dir_b = scratch("mb");
    let disk_a = DiskCache::open(&dir_a)?;
    let disk_b = DiskCache::open(&dir_b)?;
    let pure = EffectRow::pure();

    // ── Node A: compute and publish N=3 distinct artifacts (real work each). ──
    let k0 = publish(&disk_a, 2, &pure)?;
    let k1 = publish(&disk_a, 3, &pure)?;
    let k2 = publish(&disk_a, 4, &pure)?;

    // ORACLE 1: distinct `key_id`s ⇒ distinct content-addresses. Without this the
    // notion of fetching "a subset" is vacuous (all keys would alias).
    assert_ne!(k0, k1, "distinct artifacts must have distinct keys");
    assert_ne!(k1, k2, "distinct artifacts must have distinct keys");
    assert_ne!(k0, k2, "distinct artifacts must have distinct keys");

    // ── Node A serves its whole CAS via the thin harness (binds :0, reports the
    //    real port on `ready`). The SAME server answers every connection. ──
    let (ready_tx, ready_rx) = std::sync::mpsc::channel();
    let server = std::thread::spawn(move || bind_serve("127.0.0.1:0", &ready_tx, &disk_a));
    let addr = ready_rx
        .recv()
        .map_err(|_| CacheError::Io(std::io::Error::other("harness never bound")))?
        .to_string();

    // ── Node B: empty cache, wants only the SUBSET {k0, k2}; k1 stays on A. ──
    let want = [k0, k2];
    assert_eq!(
        disk_b.missing(&want),
        want.to_vec(),
        "B lacks both requested keys up front"
    );
    probe_then_pull::<ΔL>(&addr, &want, &disk_b)?;

    // ORACLE 2: B holds EXACTLY the requested subset — the third artifact, never
    // asked for, never crossed the wire and is absent from B's CAS.
    assert!(disk_b.contains(&k0), "requested key k0 landed");
    assert!(disk_b.contains(&k2), "requested key k2 landed");
    assert!(
        !disk_b.contains(&k1),
        "the un-requested key k1 was never fetched"
    );
    assert_eq!(
        disk_b.missing(&[k0, k1, k2]),
        vec![k1],
        "B still lacks ONLY the artifact it did not request"
    );

    // ── ORACLE 3: B serves each fetched artifact WITHOUT recomputing — zero
    //    interactions and a byte-for-byte identical canonical_hash (§6.5.3). ──
    for (key, key_id) in [(k0, 2u32), (k2, 4u32)] {
        let (net_b, root_b): (Net<Canonical, ΔL>, PortId) = disk_b
            .load(&key)?
            .ok_or(CacheError::Decode(DnxError::ReadbackIncomplete))?;
        let mut mem_b = ResultCache::<ΔL>::new();
        mem_b.insert(key, Arc::new(net_b), root_b)?;
        let (served, stats_b) =
            normalize_cached(&mut mem_b, key, id_applied_with(key_id)?, root_b, &pure)?;
        assert_eq!(
            stats_b.interactions, 0,
            "B fetched artifact {key_id} by hash — ZERO steps"
        );
        assert_eq!(
            canonical_hash(&served, root_b)?,
            key,
            "B's served value is byte-for-byte A's value (artifact {key_id})"
        );
    }

    drop(server);
    let _ = std::fs::remove_dir_all(&dir_a);
    let _ = std::fs::remove_dir_all(&dir_b);
    Ok(())
}
