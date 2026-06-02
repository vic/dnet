#![forbid(unsafe_code)]

//! `dnx test` — a parallel `nix-unit`-style test runner on dnx's reducer.
//!
//! Each `{ expr; expected; }` case is an independent, closed, pure Nix
//! expression. The runner evaluates `expr` and `expected` to their normal forms
//! and passes the case iff they are convertible (`NixEvalResult::conv_eq`) —
//! dnx's native equality, sound because the reducer is confluent
//! (dnx-test-runner-design.md §3). Cases are evaluated with rayon `par_iter`
//! across an `--jobs`-sized pool (design §4): the evaluator owns no cross-call
//! state (`NixRuntime` is a unit struct), so a parallel run yields byte-identical
//! pass/fail to `--jobs 1` — the confluence self-oracle that is the headline
//! correctness property (dnx-test-demo.md §5).
//!
//! Re-running an unchanged suite never recomputes: each case's result is cached
//! by the content hash of its source (the Unison input-keyed model,
//! distribution-mvp-plan.md:107-127). A cache HIT does zero reduction
//! (`interactions == 0`) — the never-recompute property (design §5). The cache
//! is the runner's own source-keyed store rather than `dnx-dist`'s
//! content-addressed result cache, because the latter hashes the *result net*
//! and that hash is not yet defined for scalar/prim normal forms
//! (canonical_hash.rs:193); the dnx-dist primitive is exercised on the prim-free
//! path it supports in the crate's tests.

mod cache;
mod scan;

use std::time::Instant;

use rayon::prelude::*;

use dnx_core::prim::PrimValue;
use dnx_lang::runtime::{NixEvalResult, NixRuntime};
use dnx_lang::{discover_computed, parse_test_suite, TestCase, ValueCase};

pub use cache::DiskResultCache;
pub use scan::{collect_nix_files, scan_dir, FailKind, FileOutcome, FileReport, ScanReport};

/// The verdict for one case.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// `expr` and `expected` are convertible.
    Pass,
    /// They differ; carries the two rendered normal forms for display.
    Fail { expected: String, got: String },
    /// Evaluation of one side failed (parse / elaborate / divergence).
    Error(String),
}

/// A case's result plus how it was obtained.
#[derive(Debug, Clone)]
pub struct CaseReport {
    pub path: String,
    pub outcome: Outcome,
    /// Total reduction interactions across both sides (`0` ⇒ served from cache).
    pub interactions: u64,
    /// `true` iff this result was a cache HIT (no evaluation performed).
    pub cached: bool,
    pub micros: u128,
}

impl CaseReport {
    pub fn passed(&self) -> bool {
        matches!(self.outcome, Outcome::Pass)
    }
}

/// The whole-suite result.
#[derive(Debug, Clone)]
pub struct RunReport {
    pub cases: Vec<CaseReport>,
    pub jobs: usize,
    pub wall_micros: u128,
}

impl RunReport {
    pub fn passed(&self) -> usize {
        self.cases.iter().filter(|c| c.passed()).count()
    }
    pub fn failed(&self) -> usize {
        self.cases
            .iter()
            .filter(|c| matches!(c.outcome, Outcome::Fail { .. }))
            .count()
    }
    pub fn errored(&self) -> usize {
        self.cases
            .iter()
            .filter(|c| matches!(c.outcome, Outcome::Error(_)))
            .count()
    }
    pub fn cached(&self) -> usize {
        self.cases.iter().filter(|c| c.cached).count()
    }
    /// CI gate: every case passed.
    pub fn all_passed(&self) -> bool {
        self.cases.iter().all(CaseReport::passed)
    }
}

/// Render a `NixEvalResult` to a short human string (for FAIL display).
fn render(v: &NixEvalResult) -> String {
    match v {
        NixEvalResult::Int(n) => n.to_string(),
        NixEvalResult::Float(f) => f.to_string(),
        NixEvalResult::Str(s) => format!("{s:?}"),
        NixEvalResult::Bool(b) => b.to_string(),
        NixEvalResult::Null => "null".to_string(),
        NixEvalResult::List(xs) => format!("[ {} items ]", xs.len()),
        NixEvalResult::AttrSet(kvs) => format!("{{ {} attrs }}", kvs.len()),
        NixEvalResult::Lambda(_) => "<lambda>".to_string(),
        NixEvalResult::Error(e) => format!("<error: {e}>"),
    }
}

/// Render a reduced `PrimValue` to the same short human string as [`render`]
/// (for FAIL display on the computed-suite path, where the sides are already
/// values rather than `NixEvalResult`s).
fn render_pv(v: &PrimValue) -> String {
    match v {
        PrimValue::Int(n) => n.to_string(),
        PrimValue::Float(f) => f.to_string(),
        PrimValue::Str(s) => format!("{s:?}"),
        PrimValue::Path(p) => p.to_string(),
        PrimValue::Bool(b) => b.to_string(),
        PrimValue::Null => "null".to_string(),
        PrimValue::List(xs) => format!("[ {} items ]", xs.len()),
        PrimValue::AttrSet(kvs) => format!("{{ {} attrs }}", kvs.len()),
        PrimValue::Closure(_) | PrimValue::Lambda => "<lambda>".to_string(),
    }
}

/// Compare a computed case: its two sides are already reduced `PrimValue`s read
/// from the suite's value tree, so the verdict is a direct value equality — no
/// second evaluation. Soundness is the same confluence argument as `conv_eq`:
/// the reducer's unique normal form makes convertible sides reduce to equal
/// values (computed-suite-runner.md §2c).
fn compare_value_case(case: &ValueCase) -> Outcome {
    if case.expr == case.expected {
        Outcome::Pass
    } else {
        Outcome::Fail {
            expected: render_pv(&case.expected),
            got: render_pv(&case.expr),
        }
    }
}

/// Evaluate both sides of a case and compare. Pure: no shared state, so it is
/// safe to call concurrently (design §4).
fn eval_case(rt: &NixRuntime, case: &TestCase) -> (Outcome, u64) {
    let expr = rt.eval_canonical(&case.expr);
    let expected = rt.eval_canonical(&case.expected);
    match (expr, expected) {
        (Ok((ev, ei)), Ok((xv, xi))) => {
            let outcome = if ev.conv_eq(&xv) {
                Outcome::Pass
            } else {
                Outcome::Fail {
                    expected: render(&xv),
                    got: render(&ev),
                }
            };
            (outcome, ei + xi)
        }
        (Err(e), _) => (Outcome::Error(format!("expr: {e}")), 0),
        (_, Err(e)) => (Outcome::Error(format!("expected: {e}")), 0),
    }
}

/// Run one case, consulting `cache` first when present. A cache HIT performs no
/// reduction (`interactions == 0`, `cached == true`).
fn run_one(case: &TestCase, cache: Option<&DiskResultCache>) -> CaseReport {
    let start = Instant::now();
    let key = cache::case_key(case);

    if let Some(c) = cache {
        if let Some(outcome) = c.get(&key) {
            return CaseReport {
                path: case.path.clone(),
                outcome,
                interactions: 0,
                cached: true,
                micros: start.elapsed().as_micros(),
            };
        }
    }

    let rt = NixRuntime::pure();
    let (outcome, interactions) = eval_case(&rt, case);
    if let Some(c) = cache {
        c.put(&key, &outcome);
    }
    CaseReport {
        path: case.path.clone(),
        outcome,
        interactions,
        cached: false,
        micros: start.elapsed().as_micros(),
    }
}

/// Parse `src` as a test suite and run every case across a `jobs`-sized rayon
/// pool. With `cache`, unchanged cases HIT (0 interactions) on a re-run.
///
/// `jobs == 1` is the sequential self-oracle: by confluence the pass/fail vector
/// is identical to any `jobs > 1` run (design §4). Returns an error only if the
/// suite file itself fails to parse; a case that fails to evaluate is reported
/// as `Outcome::Error`, never an early return.
pub fn run_suite(
    src: &str,
    jobs: usize,
    cache: Option<&DiskResultCache>,
) -> Result<RunReport, String> {
    let cases = parse_test_suite(src).map_err(|e| e.to_string())?;
    let jobs = jobs.max(1);
    let start = Instant::now();

    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(jobs)
        .build()
        .map_err(|e| e.to_string())?;
    let reports = pool.install(|| cases.par_iter().map(|c| run_one(c, cache)).collect());

    Ok(RunReport {
        cases: reports,
        jobs,
        wall_micros: start.elapsed().as_micros(),
    })
}

/// Run one computed case: a pure value comparison. `interactions` is `0` and
/// `cached` is `false` — the suite's reduction was amortized into the single
/// whole-file eval in [`run_computed_suite`], not performed per case
/// (computed-suite-runner.md §2d).
fn run_one_value(case: &ValueCase) -> CaseReport {
    let start = Instant::now();
    CaseReport {
        path: case.path.clone(),
        outcome: compare_value_case(case),
        interactions: 0,
        cached: false,
        micros: start.elapsed().as_micros(),
    }
}

/// Run a COMPUTED suite: a file whose top level is an application/`mapAttrs`/
/// `flatten` rather than a literal attrset. The file is evaluated once to a value
/// tree ([`discover_computed`]); each leaf's two sides are then compared by value
/// across a `jobs`-sized rayon pool. Returns an error only if the file itself
/// fails to reduce (or reduces to a non-attrset).
///
/// `jobs == 1` is the sequential self-oracle: the file eval is deterministic and
/// the per-case compare is pure, so any `jobs > 1` run yields the identical
/// pass/fail vector (computed-suite-runner.md §5). No disk cache: the cost is the
/// one file eval, and a per-case value-hash key buys nothing for the gate.
pub fn run_computed_suite(src: &str, jobs: usize) -> Result<RunReport, String> {
    let cases = discover_computed(src).map_err(|e| e.to_string())?;
    let jobs = jobs.max(1);
    let start = Instant::now();

    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(jobs)
        .build()
        .map_err(|e| e.to_string())?;
    let reports = pool.install(|| cases.par_iter().map(run_one_value).collect());

    Ok(RunReport {
        cases: reports,
        jobs,
        wall_micros: start.elapsed().as_micros(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const SUITE: &str = "{ \
        testAdd  = { expr = 1 + 2;        expected = 3; }; \
        testConv = { expr = 2 + 2;        expected = 4; }; \
        testStr  = { expr = \"a\" + \"b\"; expected = \"ab\"; }; \
        testIf   = { expr = if 1 < 2 then 10 else 0; expected = 10; }; \
        testBad  = { expr = 1 + 1;        expected = 3; }; \
    }";

    #[test]
    fn runs_and_reports_pass_fail() {
        let r = run_suite(SUITE, 1, None).expect("suite");
        assert_eq!(r.cases.len(), 5);
        assert_eq!(r.passed(), 4, "four convertible cases pass");
        assert_eq!(r.failed(), 1, "testBad (1+1 vs 3) fails");
        assert!(!r.all_passed());
    }

    #[test]
    fn top_level_let_bindings_are_in_scope_for_cases() {
        // P0 #3: a suite with top-level bindings must run each case with those
        // bindings in scope, not standalone-from-empty (gen-dnx-readiness.md #3).
        let suite = "let lib = { f = 7; }; v = 101; \
            in { a = { expr = lib.f; expected = 7; }; \
                 b = { expr = v;     expected = 101; }; }";
        let r = run_suite(suite, 1, None).expect("suite");
        assert_eq!(r.cases.len(), 2);
        assert_eq!(r.errored(), 0, "no unbound-variable errors: {:?}", r.cases);
        assert!(r.all_passed(), "both let-scoped cases pass: {:?}", r.cases);
    }

    #[test]
    fn seq_equals_parallel() {
        // The confluence self-oracle: --jobs 1 and --jobs 4 must give the SAME
        // per-case pass/fail (design §4, dnx-test-demo.md §5 headline).
        let seq = run_suite(SUITE, 1, None).expect("seq");
        let par = run_suite(SUITE, 4, None).expect("par");
        let s: Vec<_> = seq.cases.iter().map(|c| (&c.path, c.passed())).collect();
        let p: Vec<_> = par.cases.iter().map(|c| (&c.path, c.passed())).collect();
        assert_eq!(s, p, "parallel pass/fail must equal sequential");
    }

    #[test]
    fn rerun_hits_cache_zero_interactions() {
        let dir = std::env::temp_dir().join(format!("dnx-test-cache-{}", std::process::id()));
        let cache = DiskResultCache::open(&dir).expect("cache");

        let first = run_suite(SUITE, 4, Some(&cache)).expect("first");
        assert_eq!(first.cached(), 0, "first run computes everything");
        assert!(
            first.cases.iter().any(|c| c.interactions > 0),
            "first run does real reduction work"
        );

        let second = run_suite(SUITE, 4, Some(&cache)).expect("second");
        assert_eq!(second.cached(), 5, "re-run hits cache for every case");
        assert!(
            second.cases.iter().all(|c| c.interactions == 0),
            "a cache HIT does zero reduction (never recompute)"
        );
        // Same verdicts, cached or not.
        let a: Vec<_> = first.cases.iter().map(|c| (&c.path, c.passed())).collect();
        let b: Vec<_> = second.cases.iter().map(|c| (&c.path, c.passed())).collect();
        assert_eq!(a, b, "cached verdicts match the computed ones");

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn editing_one_case_misses_only_that_case() {
        let dir = std::env::temp_dir().join(format!("dnx-test-fine-{}", std::process::id()));
        let cache = DiskResultCache::open(&dir).expect("cache");
        let _ = run_suite(SUITE, 2, Some(&cache)).expect("warm");

        // Change exactly one case's expr; its source-hash changes → it MISSes,
        // every sibling still HITs (design §5 fine-grained invalidation).
        let edited = SUITE.replace("expr = 1 + 2;", "expr = 1 + 4;");
        let r = run_suite(&edited, 2, Some(&cache)).expect("edited");
        assert_eq!(r.cached(), 4, "only the edited case misses");
        let edited_case = r
            .cases
            .iter()
            .find(|c| c.path == "testAdd")
            .expect("testAdd");
        assert!(!edited_case.cached, "the edited case recomputed");

        let _ = std::fs::remove_dir_all(&dir);
    }

    // ── computed suites (computed-suite-runner.md) ───────────────────────────
    //
    // The top level is an APPLICATION, which the literal `run_suite` path rejects
    // with "tests file must be an attrset"; `run_computed_suite` evaluates it to a
    // value tree and runs the leaves. The suites here reduce to a single-entry
    // tree on purpose: a computed result whose attrset has ≥2 entries hits the
    // reducer's known `insert`-chain frontier (an upstream dnx-core limit, not the
    // runner's), so the gate is exercised with single-leaf computed suites.

    const COMPUTED_PASS: &str = "(x: { c = { expr = x; expected = 7; }; }) 7";
    const COMPUTED_FAIL: &str = "(x: { c = { expr = x; expected = 99; }; }) 7";

    #[test]
    fn computed_suite_discovers_and_runs_a_passing_case() {
        let r = run_computed_suite(COMPUTED_PASS, 1).expect("computed suite");
        assert_eq!(r.cases.len(), 1, "leaf discovered: {:?}", r.cases);
        assert_eq!(r.cases[0].path, "c");
        assert!(r.all_passed(), "expr == expected: {:?}", r.cases);
        // Reduction amortized into the file eval (§2d): 0 per-case interactions.
        assert!(r.cases.iter().all(|c| c.interactions == 0 && !c.cached));
        // The literal path cannot even discover this application-shaped suite.
        assert!(run_suite(COMPUTED_PASS, 1, None).is_err());
    }

    #[test]
    fn computed_suite_reports_a_failing_case() {
        let r = run_computed_suite(COMPUTED_FAIL, 1).expect("computed suite");
        assert_eq!(r.cases.len(), 1);
        assert_eq!(r.failed(), 1, "7 vs 99 fails: {:?}", r.cases);
        match &r.cases[0].outcome {
            Outcome::Fail { expected, got } => {
                assert_eq!(expected, "99");
                assert_eq!(got, "7");
            }
            other => panic!("expected Fail, got {other:?}"),
        }
    }

    #[test]
    fn computed_seq_equals_parallel() {
        // The confluence self-oracle on the computed path: --jobs 1 and --jobs 4
        // give the SAME per-case pass/fail (computed-suite-runner.md §5).
        let seq = run_computed_suite(COMPUTED_PASS, 1).expect("seq");
        let par = run_computed_suite(COMPUTED_PASS, 4).expect("par");
        let s: Vec<_> = seq.cases.iter().map(|c| (&c.path, c.passed())).collect();
        let p: Vec<_> = par.cases.iter().map(|c| (&c.path, c.passed())).collect();
        assert_eq!(s, p, "parallel pass/fail must equal sequential");
    }
}
