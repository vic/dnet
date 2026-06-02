//! dnx runtime micro-benchmarks — concrete demo numbers, measured through the
//! PUBLIC APIs of dnx-core / dnx-sched / dnx-dist. No runtime crate is edited;
//! this only constructs nets and times their reduction.
//!
//! Three measurements (all on TERMINATING nets — recursion/divergence cases such
//! as `fix`/Y are deliberately excluded; they have no normal form to time):
//!   1. Reduction throughput   — interactions/sec normalizing a wide net.
//!   2. Parallel speedup       — sequential `normalize` vs `normalize_par(P)`.
//!   3. Never-recompute        — `ResultCache` cold MISS (real interactions) vs warm HIT (0).
//!
//! Run (release, optimizer on): `cargo run -p dnx-bench --example bench --release`.

use std::fmt;
use std::sync::Arc;
use std::time::{Duration, Instant};

use dnx_core::effect::EffectRow;
use dnx_core::{
    canonical_hash, normalize, Blake3Hash, CRules, Canonical, DnxError, LOPath, Net, PortId,
    Proper, ΔI, ΔL,
};
use dnx_dist::{normalize_cached, CacheError, ResultCache};
use dnx_sched::normalize_par;

/// Bench errors — typed, no stringly errors, no panics on fallible paths.
#[derive(Debug)]
enum BenchError {
    Net(DnxError),
    Cache(CacheError),
    /// A named root expected on a net was absent (a builder/readback invariant).
    MissingRoot(&'static str),
}

impl fmt::Display for BenchError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BenchError::Net(e) => write!(f, "net reduction error: {e:?}"),
            BenchError::Cache(e) => write!(f, "result-cache error: {e:?}"),
            BenchError::MissingRoot(r) => write!(f, "expected root {r:?} absent on net"),
        }
    }
}

impl From<DnxError> for BenchError {
    fn from(e: DnxError) -> Self {
        BenchError::Net(e)
    }
}
impl From<CacheError> for BenchError {
    fn from(e: CacheError) -> Self {
        BenchError::Cache(e)
    }
}

// ── net builders (terminating, no rep/recursion) ───────────────────────────────

/// Unique mutually-distinct LOPath for copy `i` over `bits` binary steps; distinct
/// keys ⇒ all copies coexist in frontier1 ⇒ ONE prefix-independent parallel batch
/// (the antichain the parallel scheduler fires at once). Same trick as the sched
/// wide-equivalence oracle (`parallel_equiv_wide.rs::distinct_path`).
fn distinct_path(i: u64, bits: u32) -> Result<LOPath, DnxError> {
    let mut p = LOPath::root();
    for b in (0..bits).rev() {
        p = if (i >> b) & 1 == 1 {
            p.extend_right()?
        } else {
            p.extend_left()?
        };
    }
    Ok(p)
}

/// `k` independent `(λx.x) free` copies stamped at distinct lo-paths under roots
/// `r{i}`. Normalizes to `k` β-interactions, all in one antichain (max parallelism).
fn wide_id(k: u64, bits: u32) -> Result<Net<Proper, ΔL>, DnxError> {
    let mut n = Net::<Proper, ΔL>::new((k as u32) * 32 + 64);
    for i in 0..k {
        let lo = distinct_path(i, bits)?;
        let abs = n.alloc_abs()?;
        let app = n.alloc_app()?;
        let arg = n.alloc_free((i as u32) * 2)?;
        let res = n.alloc_free((i as u32) * 2 + 1)?;
        n.connect(abs.aux0, abs.aux1, lo.clone())?;
        n.connect(app.aux0, res, lo.clone())?;
        n.connect(app.aux1, arg, lo.clone())?;
        n.connect(abs.principal, app.principal, lo.clone())?;
        n.add_root(Arc::from(format!("r{i}")), res);
    }
    Ok(n)
}

/// `k` independent `(λx. x x) id` copies (ΔI) at distinct lo-paths under roots `r{i}`.
/// Heavier per-unit work than `wide_id`: each unit fires a rep duplication + C2 merge,
/// so the per-antichain-cell cost is large enough to amortise parallel overhead. This
/// is the proven C2-firing sharing gadget from the dnx-sched wide-equivalence oracle
/// (`parallel_equiv_wide.rs::wide_self_apply`); replicated here, not imported (test code).
fn wide_self_apply(k: u64, bits: u32) -> Result<Net<Proper, ΔI>, DnxError> {
    let mut n = Net::<Proper, ΔI>::new((k as u32) * 64 + 64);
    for i in 0..k {
        let lo = distinct_path(i, bits)?;
        let outer = n.alloc_abs()?;
        let rep = n.alloc_rep_in(0, 0, 0)?;
        let inner_app = n.alloc_app()?;
        n.connect(rep.principal, outer.aux1, lo.clone())?;
        n.connect(rep.aux0, inner_app.principal, lo.clone())?;
        n.connect(rep.aux1, inner_app.aux1, lo.clone())?;
        n.connect(inner_app.aux0, outer.aux0, lo.clone())?;
        let id = n.alloc_abs()?;
        n.connect(id.aux0, id.aux1, lo.clone())?;
        let app = n.alloc_app()?;
        let res = n.alloc_free(i as u32)?;
        n.connect(app.principal, outer.principal, lo.clone())?;
        n.connect(app.aux1, id.principal, lo.clone())?;
        n.connect(app.aux0, res, lo.clone())?;
        n.add_root(Arc::from(format!("r{i}")), res);
    }
    Ok(n)
}

// ── timing helpers ──────────────────────────────────────────────────────────────

/// Best (min) wall time over `reps` runs of `f`, plus `f`'s last return value.
/// Min is the least-noisy estimator of intrinsic cost (fewest scheduler hiccups).
fn best_of<T, F>(reps: u32, mut f: F) -> Result<(Duration, T), BenchError>
where
    F: FnMut() -> Result<T, BenchError>,
{
    let mut best = Duration::MAX;
    let mut last = f()?; // warm-up + seed `last`
    for _ in 0..reps {
        let t0 = Instant::now();
        last = f()?;
        let dt = t0.elapsed();
        if dt < best {
            best = dt;
        }
    }
    Ok((best, last))
}

fn secs(d: Duration) -> f64 {
    d.as_secs_f64()
}

// ── bench 1: reduction throughput ────────────────────────────────────────────────

fn bench_throughput() -> Result<(), BenchError> {
    println!("== 1. REDUCTION THROUGHPUT (sequential `normalize`) ==");
    println!("   net: K independent (λx.x)·free copies, ΔL, K β-interactions, terminating");
    for &(k, bits) in &[(1_000u64, 12u32), (10_000, 16), (100_000, 20)] {
        // Time `normalize` ALONE: rebuild a fresh net each rep (normalize consumes
        // it) OUTSIDE the timed region so net construction never inflates the rate.
        let mut best = Duration::MAX;
        let mut interactions = 0u64;
        for _ in 0..6 {
            let net = wide_id(k, bits)?;
            let t0 = Instant::now();
            let (_, stats) = normalize(net)?;
            let dt = t0.elapsed();
            interactions = stats.interactions;
            if dt < best {
                best = dt;
            }
        }
        let s = secs(best);
        let rate = interactions as f64 / s;
        println!(
            "   K={k:>7}  interactions={interactions:>7}  time={:>9.3} ms  ->  {:>11.0} interactions/sec ({:.2} M/s)",
            s * 1e3,
            rate,
            rate / 1e6
        );
    }
    println!();
    Ok(())
}

// ── bench 2: parallel speedup ─────────────────────────────────────────────────────

/// Sequential vs `normalize_par(P)` for one net builder, P in {2,4,8}. Builds a fresh
/// net per timed run (normalize consumes it); reports ×speedup = seq_time / par_time.
fn compare_par<C, F>(label: &str, k: u64, bits: u32, mk: F) -> Result<(), BenchError>
where
    C: CRules,
    F: Fn(u64, u32) -> Result<Net<Proper, C>, DnxError>,
{
    let (seq_dt, seq_int) = best_of(5, || Ok(normalize(mk(k, bits)?)?.1.interactions))?;
    let seq_s = secs(seq_dt);
    println!(
        "   --- {label}  K={k}  (seq interactions={seq_int}, seq time={:.3} ms) ---",
        seq_s * 1e3
    );
    for &p in &[2usize, 4, 8] {
        let (par_dt, par_int) = best_of(5, || Ok(normalize_par(mk(k, bits)?, p)?.1.interactions))?;
        let par_s = secs(par_dt);
        let speedup = seq_s / par_s;
        println!(
            "   P={p}: time={:>9.3} ms  interactions={par_int:>8}  speedup={speedup:>5.2}x",
            par_s * 1e3
        );
    }
    Ok(())
}

fn bench_parallel() -> Result<(), BenchError> {
    println!("== 2. PARALLEL SPEEDUP (seq `normalize` vs `normalize_par(P)`) ==");
    println!("   each net = wide antichain (all units fire in one parallel batch)");
    // Cheap cell: 1 β per unit (ΔL). Exposes scheduler overhead — parallel cannot win
    // when per-cell work is a single interaction.
    compare_par("cheap-cell (λx.x)·free ΔL", 200_000, 20, wide_id)?;
    // Heavy cell: rep-duplication + C2 merge per unit (ΔI). Per-cell work large enough
    // to amortise the batch/coordinator overhead — where parallelism can pay off.
    compare_par("heavy-cell (λx.x x)·id ΔI", 50_000, 18, wide_self_apply)?;
    println!();
    Ok(())
}

// ── bench 3: never-recompute (ResultCache cold vs warm) ───────────────────────────

const CACHE_ROOT: &str = "res";

/// A single `(λx. x x) id` unit (ΔI) under root `res` — the cache subject. Heavier
/// than a lone β so the COLD reduction has real interactions for the HIT to save.
fn cache_subject() -> Result<Net<Proper, ΔI>, DnxError> {
    let mut n = Net::<Proper, ΔI>::new(64);
    let lo = LOPath::root();
    let outer = n.alloc_abs()?;
    let rep = n.alloc_rep_in(0, 0, 0)?;
    let inner_app = n.alloc_app()?;
    n.connect(rep.principal, outer.aux1, lo.clone())?;
    n.connect(rep.aux0, inner_app.principal, lo.clone())?;
    n.connect(rep.aux1, inner_app.aux1, lo.clone())?;
    n.connect(inner_app.aux0, outer.aux0, lo.clone())?;
    let id = n.alloc_abs()?;
    n.connect(id.aux0, id.aux1, lo.clone())?;
    let app = n.alloc_app()?;
    let res = n.alloc_free(0)?;
    n.connect(app.principal, outer.principal, lo.clone())?;
    n.connect(app.aux1, id.principal, lo.clone())?;
    n.connect(app.aux0, res, lo)?;
    n.add_root(Arc::from(CACHE_ROOT), res);
    Ok(n)
}

fn root_of(net: &Net<Canonical, ΔI>) -> Result<PortId, BenchError> {
    net.roots()
        .get(CACHE_ROOT)
        .copied()
        .ok_or(BenchError::MissingRoot(CACHE_ROOT))
}

fn key_of(net: &Net<Canonical, ΔI>) -> Result<Blake3Hash, BenchError> {
    Ok(canonical_hash(net, root_of(net)?)?)
}

fn bench_cache() -> Result<(), BenchError> {
    println!("== 3. NEVER-RECOMPUTE (dnx-dist `ResultCache` cold MISS vs warm HIT) ==");
    println!("   net: (λx.x x)·id, ΔI, pure EffectRow; key = canonical_hash(normal form)");

    // Caller holds the content-hash + stable result root, computed once.
    let (probe, _) = normalize(cache_subject()?)?;
    let key = key_of(&probe)?;
    let root = root_of(&probe)?;
    let pure = EffectRow::pure();

    // COLD: fresh cache every rep ⇒ always a MISS ⇒ real reduction happens.
    let (cold_dt, cold_int) = best_of(200, || {
        let mut cache = ResultCache::<ΔI>::new();
        let (_, stats) = normalize_cached(&mut cache, key, cache_subject()?, root, &pure)?;
        Ok(stats.interactions)
    })?;

    // WARM: one shared pre-seeded cache ⇒ every call is a HIT ⇒ interactions == 0.
    let mut warm_cache = ResultCache::<ΔI>::new();
    let (_, _seed) = normalize_cached(&mut warm_cache, key, cache_subject()?, root, &pure)?;
    let (warm_dt, warm_int) = best_of(200, || {
        let (_, stats) = normalize_cached(&mut warm_cache, key, cache_subject()?, root, &pure)?;
        Ok(stats.interactions)
    })?;

    let cold_us = secs(cold_dt) * 1e6;
    let warm_us = secs(warm_dt) * 1e6;
    let ratio = if warm_us > 0.0 {
        cold_us / warm_us
    } else {
        f64::INFINITY
    };
    println!("   COLD (MISS): time={cold_us:>9.3} us  interactions={cold_int} (real reduction)");
    println!("   WARM (HIT) : time={warm_us:>9.3} us  interactions={warm_int} (never recomputed)");
    println!("   cache-hit win: {ratio:>6.1}x faster, {cold_int} interactions -> 0");
    println!();
    Ok(())
}

fn main() -> Result<(), BenchError> {
    println!("dnx runtime benchmarks (release). Terminating nets only; fix/Y recursion excluded.");
    println!("cpu threads available: {}\n", cpu_threads());
    bench_throughput()?;
    bench_parallel()?;
    bench_cache()?;
    Ok(())
}

/// Logical CPUs, reported for context (not used to drive any bench; `normalize_par`
/// takes an explicit thread count). 0 if the count is unavailable.
fn cpu_threads() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(0)
}
