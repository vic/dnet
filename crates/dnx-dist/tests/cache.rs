//! Phase-0 result-cache oracle (distribution-mvp-plan.md §B done-test):
//! a pure computation is normalized once; a second lookup by the same
//! content-hash key is a HIT with `interactions == 0` and an identical
//! result. A different key must MISS (no false hit).

use std::sync::Arc;

use dnx_core::effect::EffectRow;
use dnx_core::{
    canonical_hash, normalize, Blake3Hash, Canonical, DnxError, LOPath, Net, PortId, Proper, ΔL,
};
use dnx_dist::{normalize_cached, CacheError, ResultCache};

const ROOT: &str = "res";

/// (λx.x) arg — one β-reduction, pure, ΔL (mirrors dnx-core oracle builder).
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

/// The root port under the well-known `ROOT` name (the result's hash root).
fn root_of(net: &Net<Canonical, ΔL>) -> Result<PortId, DnxError> {
    net.roots()
        .get(ROOT)
        .copied()
        .ok_or(DnxError::ReadbackIncomplete)
}

/// Content-hash of a net's normal form (the key the caller HOLDS — computed once).
fn hash_of(net: &Net<Canonical, ΔL>) -> Result<Blake3Hash, DnxError> {
    canonical_hash(net, root_of(net)?)
}

/// DEMO ORACLE — the "live cache wow" (distribution-mvp-plan.md §B:104-105,
/// distribution-design.md:260-265). Evaluate ONE pure non-recursive expression
/// TWICE through the same cache and prove the headline claim, end to end:
///
///   * eval #1 (`s1`) does REAL reduction work        → `s1.interactions  > 0`
///   * eval #2 (`s2`) of the same expression is FREE   → `s2.interactions == 0`
///   * both evals return the byte-for-byte SAME result → `canonical_hash` equal
///
/// This is the demo's proof that the second eval recomputes NOTHING. The key is
/// the content-hash of the (pure) input's normal form, computed once up front —
/// the realistic single-process flow the plan endorses (§B:129-137): "same input
/// elaborated twice → same canonical net → same key → second call skips
/// `normalize`'s reduction work." A pure input has a UNIQUE normal form
/// (Church–Rosser), so this `net_hash → result` map is a function
/// (canonical-hash.md:48-51).
#[test]
fn demo_second_eval_is_free() -> Result<(), CacheError> {
    // The caller's content-address for this pure computation: hash of its NF.
    // (Computing it requires one normalize — that IS eval #1's reduction work,
    // which `s1` below records; nothing is normalized "for free" to set up.)
    let (nf, _) = normalize(id_applied()?)?;
    let key = hash_of(&nf)?;
    let root = root_of(&nf)?;

    let mut cache = ResultCache::<ΔL>::new();
    let pure = EffectRow::pure();
    assert!(cache.is_empty(), "the demo starts with a cold cache");

    // EVAL #1 — cold cache: a real β-reduction runs; the verified result is
    // stored under its content-hash.
    let (r1, s1) = normalize_cached(&mut cache, key, id_applied()?, root, &pure)?;
    assert!(
        s1.interactions > 0,
        "eval #1 must do real reduction work, got {s1:?}"
    );
    assert_eq!(cache.len(), 1, "eval #1 must memoize exactly one result");

    // EVAL #2 — same expression, warm cache: a content-addressed HIT. `normalize`
    // is NEVER entered, so the step counter is exactly zero.
    let (r2, s2) = normalize_cached(&mut cache, key, id_applied()?, root, &pure)?;
    assert_eq!(
        s2.interactions, 0,
        "eval #2 must recompute NOTHING (the cache wow), got {s2:?}"
    );

    // The two evals agree byte-for-byte (the cache served the real result, not a
    // forgery): identical content-hash, and the HIT shared the stored `Arc`.
    assert_eq!(
        hash_of(&r1)?,
        hash_of(&r2)?,
        "both evals must yield a hash-equal result net"
    );
    assert!(
        Arc::ptr_eq(&r1, &r2),
        "the HIT must return the stored result by reference, not recompute it"
    );
    assert_eq!(cache.len(), 1, "the HIT must not grow the cache");

    Ok(())
}

#[test]
fn hit_does_zero_work() -> Result<(), CacheError> {
    // Caller computes the key (and the stable result root) once, up front.
    let (probe, _) = normalize(id_applied()?)?;
    let key = hash_of(&probe)?;
    let root = root_of(&probe)?;

    let mut cache = ResultCache::<ΔL>::new();
    let pure = EffectRow::pure();

    // Call A — MISS: real reduction work, result bound to its key and stored.
    let (a, sa) = normalize_cached(&mut cache, key, id_applied()?, root, &pure)?;
    assert!(sa.interactions > 0, "MISS must do reduction work");
    assert_eq!(cache.len(), 1, "MISS must store the result");

    // Call B — HIT on the same key: zero work, identical result.
    let (b, sb) = normalize_cached(&mut cache, key, id_applied()?, root, &pure)?;
    assert_eq!(sb.interactions, 0, "HIT must never recompute");
    assert_eq!(cache.len(), 1, "HIT must not grow the cache");
    assert!(Arc::ptr_eq(&a, &b), "HIT must return the stored Arc");
    assert_eq!(hash_of(&a)?, hash_of(&b)?, "HIT result must hash-equal");

    Ok(())
}

#[test]
fn wrong_key_misses() -> Result<(), CacheError> {
    let (probe, _) = normalize(id_applied()?)?;
    let key = hash_of(&probe)?;
    let root = root_of(&probe)?;
    let mut other = key;
    other[0] ^= 0xff; // a different content-hash

    let mut cache = ResultCache::<ΔL>::new();
    let pure = EffectRow::pure();

    let _ = normalize_cached(&mut cache, key, id_applied()?, root, &pure)?;
    // A different key does NOT collide with the stored entry — but it also must
    // not bind a result it doesn't hash to: `other` ≠ hash(result) → rejected.
    let r = normalize_cached(&mut cache, other, id_applied()?, root, &pure);
    assert!(
        matches!(r, Err(CacheError::HashMismatch)),
        "a key that does not content-address the result must be rejected"
    );
    assert_eq!(cache.len(), 1, "a mismatched key stores nothing");

    Ok(())
}

#[test]
fn insert_rejects_wrong_key() -> Result<(), CacheError> {
    // Seed-poisoning: a caller tries to bind a real canonical result under a
    // FORGED key. `insert` recomputes the content-address and must reject the
    // mismatch — otherwise a later `normalize_cached(forged_key)` HIT would
    // serve this result for a computation it is NOT the normal form of,
    // poisoning the content-addressed cache.
    let (result, _) = normalize(id_applied()?)?;
    let root = root_of(&result)?;
    let real = canonical_hash(&result, root)?;
    let mut forged = real;
    forged[0] ^= 0xff;

    let mut cache = ResultCache::<ΔL>::new();
    let shared = Arc::new(result);

    // Forged key → rejected, nothing stored.
    let bad = cache.insert(forged, Arc::clone(&shared), root);
    assert!(
        matches!(bad, Err(CacheError::HashMismatch)),
        "forged key must be rejected"
    );
    assert!(cache.is_empty(), "a rejected seed stores nothing");

    // The honest key → accepted.
    cache.insert(real, shared, root)?;
    assert_eq!(cache.len(), 1, "the content-address key seeds the entry");

    Ok(())
}
