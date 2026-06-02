//! M1 oracle: "compute once, serve many" (J1), plus the §2.4 wire smoke test.
//!
//! J1 has two faces, both proved here on real APIs:
//!   (a) build-dedup    — two identical `Daemon::build` realize ONCE
//!                         (a counting `Realizer` is the build-count oracle).
//!   (b) eval-dedup     — two identical `normalize_cached` over the warm
//!                         `ResultCache` recompute ONCE: the second returns
//!                         `interactions == 0` (the literal "0 steps" slogan).
//! Mirrors `dnx-dist/tests/replication.rs::two_node_never_recompute`.

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use dnx_core::effect::EffectRow;
use dnx_core::{
    canonical_hash, normalize, to_blob, Blake3Hash, Canonical, DnxError, LOPath, Net, PortId,
    Proper, ΔL,
};
use dnx_daemon::{daemon_status, ping, serve, Daemon, DaemonError, Realizer, PROTO_VERSION};
use dnx_dist::{normalize_cached, ResultCache};
use dnx_drv::Derivation;
use dnx_store::{Store, StorePath};

const ROOT: &str = "res";

// ── fixtures ────────────────────────────────────────────────────────────────

/// A unique throwaway directory under the OS temp dir (no `tempfile` dep;
/// mirrors the dist oracle's `scratch`).
fn scratch(tag: &str) -> std::path::PathBuf {
    static CTR: AtomicU64 = AtomicU64::new(0);
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    std::env::temp_dir().join(format!(
        "dnx-daemon-{tag}-{}-{n}-{nanos}",
        std::process::id()
    ))
}

fn scratch_store(tag: &str) -> Store {
    Store::open_at(scratch(tag)).expect("open scratch store")
}

/// A simple derivation. Never realized by the J1 build-dedup oracle (a counting
/// `Realizer` stands in), so the builder command is irrelevant there.
fn drv(name: &str) -> Derivation {
    Derivation {
        name: Arc::from(name),
        builder: Arc::from("/bin/sh"),
        args: vec![Arc::from("-c"), Arc::from("echo -n hi > $out")],
        env: BTreeMap::new(),
        input_srcs: Vec::new(),
        outputs: vec![Arc::from("out")],
    }
}

/// A counting realizer: every `realize` bumps an `AtomicU64`. The returned path
/// is fixed (the oracle measures *how many times* realize ran, not its bytes).
struct CountingRealizer {
    calls: AtomicU64,
    out: StorePath,
}

impl CountingRealizer {
    fn new() -> Self {
        let out = StorePath::new([7u8; 32], "out").expect("valid store path");
        CountingRealizer {
            calls: AtomicU64::new(0),
            out,
        }
    }

    fn count(&self) -> u64 {
        self.calls.load(Ordering::SeqCst)
    }
}

impl Realizer for CountingRealizer {
    fn realize(&self, _drv: &Derivation) -> Result<StorePath, DaemonError> {
        self.calls.fetch_add(1, Ordering::SeqCst);
        Ok(self.out.clone())
    }
}

/// (λx.x) arg — one β-reduction, pure, ΔL (the dist oracle's net).
fn id_applied() -> Result<Net<Proper, ΔL>, DnxError> {
    let mut n = Net::<Proper, ΔL>::new(16);
    let abs = n.alloc_abs()?;
    let app = n.alloc_app()?;
    let arg = n.alloc_free(0)?;
    let res = n.alloc_free(1)?;
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

// ── J1 (a): build-dedup — TWO identical builds realize ONCE ─────────────────

#[test]
fn j1_two_identical_builds_realize_once() -> Result<(), DaemonError> {
    let mut daemon = Daemon::new(scratch_store("build-once"));
    let realizer = CountingRealizer::new();
    let d = drv("big");

    let out1 = daemon.build(&d, &realizer)?;
    let out2 = daemon.build(&d.clone(), &realizer)?;

    assert_eq!(out1, out2, "both clients get the SAME store path");
    assert_eq!(
        realizer.count(),
        1,
        "the SAME derivation is realized exactly ONCE (compute once)"
    );
    assert_eq!(
        daemon.built_count(),
        1,
        "exactly one distinct build memoized"
    );
    Ok(())
}

#[test]
fn distinct_builds_each_realize() -> Result<(), DaemonError> {
    let mut daemon = Daemon::new(scratch_store("build-distinct"));
    let realizer = CountingRealizer::new();

    daemon.build(&drv("a"), &realizer)?;
    daemon.build(&drv("b"), &realizer)?;

    assert_eq!(realizer.count(), 2, "two DISTINCT drvs realize twice");
    assert_eq!(daemon.built_count(), 2);
    Ok(())
}

// ── J1 (b): eval-dedup — second normalize is ZERO interactions ──────────────

#[test]
fn j1_warm_cache_second_eval_is_zero_interactions() -> Result<(), Box<dyn std::error::Error>> {
    let pure = EffectRow::pure();

    // Compute the result's content-hash once, up front (the caller-held key).
    let (probe, _) = normalize(id_applied()?)?;
    let probe_root = root_of(&probe)?;
    let key: Blake3Hash = canonical_hash(&probe, probe_root)?;

    let mut warm = ResultCache::<ΔL>::new();

    // First eval: real reduction work (a MISS computes it).
    let (_first, stats1) = normalize_cached(&mut warm, key, id_applied()?, probe_root, &pure)?;
    assert!(stats1.interactions > 0, "first eval does real work");

    // Second identical eval: a HIT — `normalize` is never called.
    let (served, stats2) = normalize_cached(&mut warm, key, id_applied()?, probe_root, &pure)?;
    assert_eq!(
        stats2.interactions, 0,
        "second eval is served from the warm cache: ZERO interactions"
    );
    assert_eq!(
        canonical_hash(&served, probe_root)?,
        key,
        "the served value is byte-for-byte the first value (identical hash)"
    );
    Ok(())
}

// ── wire smoke: the §2.4 protocol end-to-end over a real UnixListener ───────

/// Spawn `serve` on a temp socket in a background thread; return the socket
/// path and the join handle. The caller drives it over the wire, then sends
/// `Shutdown` (via a Ping-less path) to stop it.
fn spawn_daemon(daemon: Daemon, tag: &str) -> (std::path::PathBuf, std::thread::JoinHandle<()>) {
    let sock = scratch(tag).join("dnx.sock");
    let sock_for_thread = sock.clone();
    let handle = std::thread::spawn(move || {
        let _ = serve(&sock_for_thread, daemon);
    });
    // Wait for the listener to bind before returning (poll `ping`).
    for _ in 0..200 {
        if ping(&sock).is_some() {
            break;
        }
        std::thread::sleep(std::time::Duration::from_millis(5));
    }
    (sock, handle)
}

#[test]
fn wire_ping_storequery_cachelookup() -> Result<(), Box<dyn std::error::Error>> {
    // Seed the daemon: one store member + one warm cache blob.
    let store = scratch_store("wire");
    let present = store.add("hello", b"hello bytes")?;

    let (result, _) = normalize(id_applied()?)?;
    let root = root_of(&result)?;
    let blob_key: Blake3Hash = canonical_hash(&result, root)?;
    let blob = to_blob::<ΔL>(&result, root)?;

    let mut daemon = Daemon::new(store);
    daemon.warm_insert(blob_key, blob.clone());

    let (sock, handle) = spawn_daemon(daemon, "wire-srv");

    // Ping → Pong{version: 1}.
    assert_eq!(ping(&sock), Some(PROTO_VERSION), "daemon answers Ping");
    assert_eq!(PROTO_VERSION, 1, "M1 protocol version is 1");

    // StoreQuery: present hash → true, an absent hash → false.
    let absent: Blake3Hash = [0xab; 32];
    let client = dnx_daemon::DaemonBuilder::new(&sock);
    assert!(
        client.store_query(present.hash())?,
        "a stored hash is reported present (J3)"
    );
    assert!(
        !client.store_query(&absent)?,
        "an unknown hash is reported absent"
    );

    // CacheLookup over the wire: a hit returns the blob, a from_blob of it
    // reproduces the value WITHOUT normalize (0 reduction steps), a miss → None.
    let hit = cache_lookup(&sock, &blob_key)?;
    assert_eq!(
        hit.as_deref(),
        Some(blob.as_slice()),
        "warm cache hit serves the exact blob (J4)"
    );
    let (restored, restored_root) = dnx_core::from_blob::<ΔL>(&hit.expect("hit"))?;
    assert_eq!(
        canonical_hash(&restored, restored_root)?,
        blob_key,
        "the served blob from_blobs back to the same content hash (0 steps)"
    );
    assert!(
        cache_lookup(&sock, &absent)?.is_none(),
        "an unknown hash is a cache miss"
    );

    // Shutdown stops the accept loop; the socket is unlinked.
    shutdown(&sock)?;
    handle.join().expect("daemon thread joins cleanly");
    assert!(ping(&sock).is_none(), "after Shutdown the daemon is gone");
    Ok(())
}

// ── build over the wire: DaemonBuilder::enqueue → daemon realize → drvPath ───

/// A deterministic, host-independent derivation: `builtin:write` copies its
/// `text` env var into `$out` in-process (no `/bin/sh`, no coreutils, no host
/// PATH — `dnx-drv` drv.rs builtin), so the build-over-wire test runs anywhere.
fn write_drv(name: &str, text: &str) -> Derivation {
    let mut env = BTreeMap::new();
    env.insert(Arc::from("text"), Arc::from(text));
    Derivation {
        name: Arc::from(name),
        builder: Arc::from("builtin:write"),
        args: Vec::new(),
        env,
        input_srcs: Vec::new(),
        outputs: vec![Arc::from("out")],
    }
}

#[test]
fn build_over_wire_realizes_and_returns_outpath() -> Result<(), Box<dyn std::error::Error>> {
    use dnx_daemon::{Builder, DaemonBuilder};

    // A store at a known root: the daemon owns one handle; the test opens a
    // second handle at the same root to read the realized output back.
    let root = scratch("build-wire-store");
    let store = Store::open_at(root.clone())?;
    let readback = Store::open_at(root)?;

    let (sock, handle) = spawn_daemon(Daemon::new(store), "build-wire-srv");
    let client = DaemonBuilder::new(&sock);

    // Build a derivation entirely over the socket: enqueue ships `to_bytes`,
    // the daemon `from_bytes`-decodes + realizes, and replies with the outPath.
    let out1 = client.enqueue(write_drv("wired", "hello over the wire"))?;

    // The realized output is really in the store, with the builder's bytes.
    let bytes = readback.get(&out1)?.expect("output present in store");
    assert_eq!(
        bytes, b"hello over the wire",
        "the daemon realized the build"
    );

    // J1 over the wire: a SECOND identical build returns the SAME path (the
    // worker deduped it — no second realize), the "compute once, serve many".
    let out2 = client.enqueue(write_drv("wired", "hello over the wire"))?;
    assert_eq!(out1, out2, "two identical builds yield the same store path");

    // And it is registered: the membership query (J3) now finds the output.
    assert!(
        client.registered(out1.hash()),
        "the realized output is a registered store member"
    );

    shutdown(&sock)?;
    handle.join().expect("daemon thread joins cleanly");
    Ok(())
}

#[test]
fn build_over_wire_propagates_a_typed_build_failure() -> Result<(), Box<dyn std::error::Error>> {
    use dnx_daemon::{Builder, DaemonBuilder};

    // An unknown builtin is a typed DrvError inside the daemon; over the wire it
    // comes back as a `Failed` the client reconstructs — never a panic, never a
    // silent success.
    let (sock, handle) = spawn_daemon(Daemon::new(scratch_store("build-fail")), "build-fail-srv");
    let client = DaemonBuilder::new(&sock);

    let bad = Derivation {
        name: Arc::from("bogus"),
        builder: Arc::from("builtin:nope"),
        args: Vec::new(),
        env: BTreeMap::new(),
        input_srcs: Vec::new(),
        outputs: vec![Arc::from("out")],
    };
    assert!(
        client.enqueue(bad).is_err(),
        "a failing build surfaces as a typed error over the wire"
    );

    shutdown(&sock)?;
    handle.join().expect("daemon thread joins cleanly");
    Ok(())
}

#[test]
fn ping_absent_socket_is_none() {
    let sock = scratch("noproc").join("dnx.sock");
    assert_eq!(ping(&sock), None, "no daemon → ping is None");
}

// ── lifecycle: stale-socket recovery + one-daemon-per-socket (design §3.2) ───

/// Stale-socket recovery (design §3.2:198 "no Pong ⇒ stale file ⇒ unlink +
/// rebind"). A leftover file at the socket path from a crashed daemon answers
/// no `Ping`; `serve` must reclaim it and bind a fresh, live daemon — not fail
/// with `AddrInUse`. The crashed daemon is simulated by a plain file at the
/// path (`UnixStream::connect` to it yields no `Pong`, so `ping` is `None`).
#[test]
fn serve_reclaims_a_stale_socket_file() -> Result<(), Box<dyn std::error::Error>> {
    let dir = scratch("stale");
    std::fs::create_dir_all(&dir)?;
    let sock = dir.join("dnx.sock");

    // A leftover, non-listening file sits at the socket path; no daemon answers.
    std::fs::write(&sock, b"crashed daemon leftover")?;
    assert_eq!(ping(&sock), None, "the stale file answers no Ping");

    // serve must unlink the stale file and bind a live daemon at the same path.
    let sock_for_thread = sock.clone();
    let handle = std::thread::spawn(move || {
        let _ = serve(&sock_for_thread, Daemon::new(scratch_store("stale-rebind")));
    });
    for _ in 0..200 {
        if ping(&sock).is_some() {
            break;
        }
        std::thread::sleep(std::time::Duration::from_millis(5));
    }

    assert_eq!(
        ping(&sock),
        Some(PROTO_VERSION),
        "after reclaiming the stale file, a fresh daemon is live at the path"
    );

    shutdown(&sock)?;
    handle.join().expect("rebound daemon joins cleanly");
    Ok(())
}

/// One daemon per socket (design §3.2:199 "a live Pong ⇒ refuse to start").
/// While a daemon holds the socket, a second `serve` on the SAME path must NOT
/// steal it: `reclaim_stale` pings, sees the live `Pong`, leaves the file, and
/// `bind` then fails (`AddrInUse` → typed `DaemonError`). The first daemon is
/// untouched — it still answers.
#[test]
fn serve_on_a_live_socket_refuses_to_steal_it() -> Result<(), Box<dyn std::error::Error>> {
    let (sock, handle) = spawn_daemon(Daemon::new(scratch_store("live")), "live-srv");
    assert_eq!(ping(&sock), Some(PROTO_VERSION), "the first daemon is live");

    // A second serve on the same live path returns a typed error (bind fails);
    // it does not enter the accept loop, so the call returns promptly.
    let second = serve(&sock, Daemon::new(scratch_store("live-second")));
    assert!(
        matches!(second, Err(DaemonError::Io(_))),
        "a second daemon on a LIVE socket is refused, not silently stolen: {second:?}"
    );

    // The first daemon survived the failed second bind and still answers.
    assert_eq!(
        ping(&sock),
        Some(PROTO_VERSION),
        "the original daemon is untouched by the refused second bind"
    );

    shutdown(&sock)?;
    handle.join().expect("daemon thread joins cleanly");
    Ok(())
}

// ── status round-trip: `dnx daemon status` surfaces version + queue depth ────

/// Backs `dnx daemon status` (design §3.1:190 "Ping → print Pong{version} +
/// queue depth"). `ping` returns version only; `daemon_status` carries the full
/// `Pong` so the CLI can report depth too. M1's worker is serial (design
/// §3.2:195), so the queue is empty at rest → depth 0 is the honest value.
#[test]
fn wire_status_reports_version_and_queue_depth() -> Result<(), Box<dyn std::error::Error>> {
    let (sock, handle) = spawn_daemon(Daemon::new(scratch_store("status")), "status-srv");

    let st = daemon_status(&sock).expect("a live daemon reports status");
    assert_eq!(
        st.version, PROTO_VERSION,
        "status carries the proto version"
    );
    assert_eq!(
        st.queue_depth, 0,
        "serial M1 worker has an empty queue at rest"
    );
    assert_eq!(st.built, 0, "a fresh daemon has realized nothing yet");
    assert_eq!(
        ping(&sock),
        Some(st.version),
        "ping is the version-only projection of status"
    );

    shutdown(&sock)?;
    handle.join().expect("daemon thread joins cleanly");
    assert!(
        daemon_status(&sock).is_none(),
        "no daemon → status is None (CLI prints \"not running\")"
    );
    Ok(())
}

// ── concurrent dedup: TWO wire clients racing the SAME drv build it ONCE ─────

/// The literal J1 headline over the WIRE, concurrently (design §4.2:232-235
/// "two `dnx build .#x` of the SAME drv racing → built ONCE, both clients get
/// the same `Built{out}`"; the build-count oracle, §8.5.4:544-551 "a build-count
/// of 1"). Two threads each open their own `UnixStream` and send `Build` for the
/// SAME derivation at once; the single accept loop serializes them, so the
/// second hits the dedup memo and never re-realizes. Proven by: both clients get
/// the SAME store path, AND the daemon's wire-reported `built` count is exactly
/// 1 (compute once, serve many).
#[test]
fn concurrent_wire_clients_same_drv_build_once() -> Result<(), Box<dyn std::error::Error>> {
    use dnx_daemon::{Builder, DaemonBuilder};

    let (sock, handle) = spawn_daemon(Daemon::new(scratch_store("concurrent")), "concurrent-srv");

    // Two clients, same derivation, racing on separate threads / sockets.
    let d = write_drv("raced", "computed once");
    let s1 = sock.clone();
    let s2 = sock.clone();
    let d1 = d.clone();
    let t1 = std::thread::spawn(move || DaemonBuilder::new(&s1).enqueue(d1));
    let t2 = std::thread::spawn(move || DaemonBuilder::new(&s2).enqueue(d));

    let out1 = t1.join().expect("client thread 1 joins")?;
    let out2 = t2.join().expect("client thread 2 joins")?;

    assert_eq!(
        out1, out2,
        "two concurrent clients of the SAME drv get the SAME store path"
    );

    // The daemon realized exactly ONE distinct build: the second request, racing
    // or arriving second, was served from the dedup memo (compute once).
    let st = daemon_status(&sock).expect("daemon reports status");
    assert_eq!(
        st.built, 1,
        "the SAME derivation is realized exactly ONCE across concurrent clients"
    );

    shutdown(&sock)?;
    handle.join().expect("daemon thread joins cleanly");
    Ok(())
}

// ── graceful shutdown: a Quit request unlinks the socket file (design §3.2) ──

/// Graceful shutdown removes the socket from the filesystem (design §3.2:189
/// "**unlink the socket** on exit"). The existing wire test only checks the
/// daemon stops answering `Ping`; this pins the on-disk half of the contract:
/// while the daemon is live the socket path EXISTS, and once a `Shutdown`
/// request has drained the accept loop (the thread joins, so `serve`'s
/// post-loop `remove_file` has run — no race), the path is GONE. A clean exit
/// leaves no stale file for the next `start` to reclaim.
#[test]
fn graceful_shutdown_unlinks_the_socket_file() -> Result<(), Box<dyn std::error::Error>> {
    let (sock, handle) = spawn_daemon(Daemon::new(scratch_store("quit-unlink")), "quit-unlink-srv");

    // A bound AF_UNIX listener is a real filesystem entry while it is live.
    assert!(
        sock.exists(),
        "the socket path exists on disk while the daemon is bound to it"
    );

    // Ask the daemon to quit, then join the worker so `serve`'s post-loop
    // unlink is guaranteed to have run before we look (the join is the barrier).
    shutdown(&sock)?;
    handle
        .join()
        .expect("daemon thread joins cleanly after Shutdown");

    assert!(
        !sock.exists(),
        "graceful shutdown removed the socket file: no stale leftover (design §3.2)"
    );
    Ok(())
}

// ── thin wire helpers (exercise the public client surface) ──────────────────

/// CacheLookup is not on the `Builder` trait (it is a serve-path, not a build),
/// so the test drives it through the same socket the daemon listens on, using
/// the public protocol via a raw round-trip helper kept here.
fn cache_lookup(sock: &Path, hash: &Blake3Hash) -> Result<Option<Vec<u8>>, DaemonError> {
    dnx_daemon::client_cache_lookup(sock, hash)
}

fn shutdown(sock: &Path) -> Result<(), DaemonError> {
    dnx_daemon::client_shutdown(sock)
}

use std::path::Path;
