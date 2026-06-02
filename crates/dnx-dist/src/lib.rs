#![forbid(unsafe_code)]

//! Phase-0 content-addressed result cache (distribution wedge #2).
//!
//! Unison keying model: the caller HOLDS the content-hash of the
//! computation and looks it up. A hit returns the stored canonical net
//! with zero reduction work — the "never recompute" proof. Sound only for
//! pure inputs (unique normal form, Church–Rosser); effectful inputs are
//! normalized but never cached.

mod disk;
mod wire;

pub use disk::{CacheError, DiskCache, LoadedNet};
pub use wire::{
    bind_serve, probe, probe_then_pull, read_msg, serve, sync_pull, write_msg, Msg, Wire, MAX_FRAME,
};

use std::collections::HashMap;
use std::sync::Arc;

use dnx_core::effect::EffectRow;
use dnx_core::{
    canonical_hash, normalize, Blake3Hash, CRules, Canonical, Net, PortId, Proper, ReduceStats,
};

/// Content-addressed result cache: input content-hash → normalized net.
///
/// Stores `Arc<Net<Canonical, C>>` because `Net` is not `Clone`; a hit
/// shares the result by `Arc::clone`.
pub struct ResultCache<C: CRules> {
    entries: HashMap<Blake3Hash, Arc<Net<Canonical, C>>>,
}

impl<C: CRules> Default for ResultCache<C> {
    fn default() -> Self {
        ResultCache {
            entries: HashMap::new(),
        }
    }
}

impl<C: CRules> ResultCache<C> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Seed an entry under a caller-held `key` — the bridge from a fetched
    /// (already-verified) blob into the in-memory result cache. After a node
    /// imports a peer's blob (`DiskCache::import`), seeding it here makes the
    /// subsequent `normalize_cached(key)` a HIT with `interactions == 0`: the
    /// result was fetched by hash, never recomputed (distribution-design.md:240-244).
    ///
    /// The seed is NOT trusted: `key` MUST be the content-address of
    /// `(result, root)`. We recompute `canonical_hash(result, root)` and reject
    /// a mismatch with [`CacheError::HashMismatch`] — otherwise a caller could
    /// bind an arbitrary net under a chosen key and poison every later
    /// content-addressed HIT (a forged-`Net<Canonical>` is admissible here only
    /// because `from_blob` already gated it; the key↔value binding is the
    /// remaining integrity check, distribution-design.md:219-221).
    pub fn insert(
        &mut self,
        key: Blake3Hash,
        result: Arc<Net<Canonical, C>>,
        root: PortId,
    ) -> Result<(), CacheError> {
        if canonical_hash(&result, root)? != key {
            return Err(CacheError::HashMismatch);
        }
        self.entries.insert(key, result);
        Ok(())
    }
}

/// Normalize `net`, caching the result under the caller-held `key`.
///
/// - HIT on `key` → `Arc::clone` of the stored result with
///   `ReduceStats::default()` (`interactions == 0`); `normalize` is never
///   called — the never-recompute guarantee.
/// - MISS → `normalize` (real stats), then bind: the freshly-computed result
///   MUST content-address to `key` (`canonical_hash(result, root) == key`),
///   else [`CacheError::HashMismatch`]. Only a verified entry is stored, so a
///   caller cannot bind a chosen `key` to a result it does not actually hash to
///   (cache poisoning). `root` is the result's hash root — for a named free-var
///   root it is stable across `normalize`, so the caller supplies it up front.
///
/// CONTRACT: `row` MUST be the effect row of `net`. Caching is sound only for
/// pure inputs ([`EffectRow::is_pure`]); an effectful `net` is normalized but
/// never cached (its value depends on the handler world). The caller is
/// responsible for `row`-matches-`net` — a mislabelled pure-but-effectful net
/// would be wrongly cached; the type system cannot witness this here, so it is
/// a documented precondition (distribution-design.md:240-244).
pub fn normalize_cached<C: CRules>(
    cache: &mut ResultCache<C>,
    key: Blake3Hash,
    net: Net<Proper, C>,
    root: PortId,
    row: &EffectRow,
) -> Result<(Arc<Net<Canonical, C>>, ReduceStats), CacheError> {
    if row.is_pure() {
        if let Some(hit) = cache.entries.get(&key) {
            return Ok((Arc::clone(hit), ReduceStats::default()));
        }
    }

    let (result, stats) = normalize(net)?;
    let result = Arc::new(result);

    if row.is_pure() {
        // Bind the result to its claimed key before trusting it as a cache
        // entry; a lying key never poisons the content-addressed store.
        if canonical_hash(&result, root)? != key {
            return Err(CacheError::HashMismatch);
        }
        cache.entries.insert(key, Arc::clone(&result));
    }

    Ok((result, stats))
}
