//! Phase-2 two-node replication oracle (distribution-mvp-plan.md §E/§F):
//! node A computes a pure artifact (real reduction work), publishes its blob
//! into A's on-disk CAS; node B holds the SAME content-hash but an EMPTY cache,
//! asks A only for what it lacks (`missing`), imports A's blob by hash
//! (`import` re-hashes and rejects a mismatch), then serves the result with
//! `interactions == 0` and a byte-for-byte identical `canonical_hash` — the
//! "compute once, fetch-by-hash everywhere, never recompute" guarantee
//! (distribution-design.md:271-277).
//!
//! SOUNDNESS CAVEAT (honest): the never-recompute guarantee is a *function*
//! `net_hash -> result` only because a pure canonical net has a UNIQUE normal
//! form (Church-Rosser), which is ASSERTED, not yet machine-proved
//! (canonical-hash.md:48-51). This is in-process replication across two
//! `DiskCache`s, NOT a network transport (the wire is deferred; see plan
//! §E:251-256).

use std::sync::Arc;

use dnx_core::effect::EffectRow;
use dnx_core::{
    canonical_hash, normalize, Blake3Hash, Canonical, DnxError, LOPath, Net, PortId, Proper, ΔL,
};
use dnx_dist::{normalize_cached, CacheError, DiskCache, ResultCache};

const ROOT: &str = "res";

/// (λx.x) arg — one β-reduction, pure, ΔL (mirrors the Phase-0/1 builders).
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

/// The root port of a canonical net under the well-known `ROOT` name.
fn root_of(net: &Net<Canonical, ΔL>) -> Result<PortId, DnxError> {
    net.roots()
        .get(ROOT)
        .copied()
        .ok_or(DnxError::ReadbackIncomplete)
}

/// A throwaway unique directory under the OS temp dir (no `tempfile` dep;
/// mirrors the Phase-1 disk oracle's `scratch`).
fn scratch(tag: &str) -> std::path::PathBuf {
    let mut p = std::env::temp_dir();
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    p.push(format!(
        "dnx-dist-repl-{tag}-{}-{nanos}",
        std::process::id()
    ));
    p
}

/// THE HEADLINE: A computes (interactions > 0); B fetches A's blob by hash and
/// serves the result with interactions == 0 and an identical canonical_hash.
#[test]
fn two_node_never_recompute() -> Result<(), CacheError> {
    let dir_a = scratch("a");
    let dir_b = scratch("b");
    let disk_a = DiskCache::open(&dir_a)?;
    let disk_b = DiskCache::open(&dir_b)?;
    let pure = EffectRow::pure();

    // The caller HOLDS the content-hash of the result (computed once, up front).
    let (probe, _) = normalize(id_applied()?)?;
    let key: Blake3Hash = canonical_hash(&probe, root_of(&probe)?)?;

    // ── Node A: compute the artifact (real work) and publish its blob. ──
    // The result's hash root (a named free-var port) is stable across
    // `normalize`, so the caller can supply it up front (here via a probe).
    let probe_root = root_of(&probe)?;
    let mut mem_a = ResultCache::<ΔL>::new();
    let (result_a, stats_a) = normalize_cached(&mut mem_a, key, id_applied()?, probe_root, &pure)?;
    assert!(stats_a.interactions > 0, "A must do real reduction work");
    let root_a = root_of(&result_a)?;
    let stored = disk_a.store(&result_a, root_a)?;
    assert_eq!(
        stored, key,
        "the stored key is the result's content-address"
    );

    // ── Node B: holds `key`, empty cache → ask A only for what it lacks. ──
    assert_eq!(
        disk_b.missing(&[key]),
        vec![key],
        "B lacks the key, so it must request exactly it"
    );
    let blob = disk_a
        .export(&key)?
        .ok_or(CacheError::Decode(DnxError::ReadbackIncomplete))?;

    // Import by hash: re-hash must equal `key` (verify-on-import); persist.
    disk_b.import::<ΔL>(key, &blob)?;
    assert!(disk_b.contains(&key), "import must persist B's copy");
    assert!(
        disk_b.missing(&[key]).is_empty(),
        "after import B lacks nothing"
    );

    // ── Node B serves the result — WITHOUT recomputing. ──
    // Seed B's in-memory cache from the imported (verified) net, then the
    // result-cache lookup is a HIT: `normalize` is never called, so the
    // reduction-step counter is mechanically zero (plan §E:247-248).
    let (net_b, root_b): (Net<Canonical, ΔL>, PortId) = disk_b
        .load(&key)?
        .ok_or(CacheError::Decode(DnxError::ReadbackIncomplete))?;
    let mut mem_b = ResultCache::<ΔL>::new();
    // Seeding is verified: the imported net must content-address to `key`.
    mem_b.insert(key, Arc::new(net_b), root_b)?;
    let (served, stats_b) = normalize_cached(&mut mem_b, key, id_applied()?, probe_root, &pure)?;

    assert_eq!(stats_b.interactions, 0, "B fetched by hash — ZERO steps");
    assert_eq!(
        canonical_hash(&served, root_b)?,
        key,
        "B's served value is byte-for-byte A's value (identical hash)"
    );

    let _ = std::fs::remove_dir_all(&dir_a);
    let _ = std::fs::remove_dir_all(&dir_b);
    Ok(())
}

/// Import REJECTS a corrupted blob: a single flipped byte makes the re-hash
/// differ from the claimed key → `HashMismatch`, never a false accept
/// (distribution-design.md:219-221).
#[test]
fn import_rejects_corrupt_blob() -> Result<(), CacheError> {
    let dir_a = scratch("ca");
    let dir_b = scratch("cb");
    let disk_a = DiskCache::open(&dir_a)?;
    let disk_b = DiskCache::open(&dir_b)?;

    let (result, _) = normalize(id_applied()?)?;
    let root = root_of(&result)?;
    let key = disk_a.store(&result, root)?;
    let mut blob = disk_a
        .export(&key)?
        .ok_or(CacheError::Decode(DnxError::ReadbackIncomplete))?;

    // Tamper one byte in transit; the claimed key is unchanged.
    let last = blob.len() - 1;
    blob[last] ^= 0xff;

    let r = disk_b.import::<ΔL>(key, &blob);
    assert!(
        matches!(
            r,
            Err(CacheError::HashMismatch) | Err(CacheError::Decode(_))
        ),
        "a tampered blob must be rejected, never stored"
    );
    assert!(
        !disk_b.contains(&key),
        "a rejected import must leave nothing on disk"
    );

    let _ = std::fs::remove_dir_all(&dir_a);
    let _ = std::fs::remove_dir_all(&dir_b);
    Ok(())
}

/// `missing` is the fetch-frontier diff: B asks A only for keys it lacks
/// (plan §E:234, the Unison missing-dependency frontier, degenerate for the
/// monolithic-blob MVP).
#[test]
fn missing_reports_only_absent_keys() -> Result<(), CacheError> {
    let dir = scratch("miss");
    let disk = DiskCache::open(&dir)?;

    let (result, _) = normalize(id_applied()?)?;
    let root = root_of(&result)?;
    let present = disk.store(&result, root)?;
    let mut absent: Blake3Hash = present;
    absent[0] ^= 0xff;

    assert_eq!(
        disk.missing(&[present, absent]),
        vec![absent],
        "only the absent key is requested"
    );
    assert!(
        disk.missing(&[present]).is_empty(),
        "a fully-present set requests nothing"
    );

    let _ = std::fs::remove_dir_all(&dir);
    Ok(())
}
