//! The import-tree GATE, as a reproducible test.
//!
//! `~/hk/import-tree/tests.nix` is a real `nix-unit` suite (34 cases) that leans
//! entirely on features outside dnx's eval subset — `<nixpkgs/lib>`, `import`,
//! path literals, recursion (`leafs`/`filter`), `evalModules`, `expectedError`
//! — and it does not even parse as a suite, because its top level is a
//! `let … in { … }` rather than a bare attrset (suite.rs `as_attrset` unwraps
//! only parens/root). So 0/34 upstream cases run today; the full blocker
//! catalogue is in `vic/notes/import-tree-gate-results.md`.
//!
//! This test pins the *runnable slice*: a suite in the same nix-unit shape
//! (nested groups, `{ expr; expected; }`, dotted paths) restricted to the
//! verified-green subset (`tests/fixtures/import-tree-slice.nix`). It asserts the
//! gate the runner actually clears, and the two headline properties:
//!   * every slice case passes (CI gate `all_passed`), and
//!   * `--jobs 1` and `--jobs N` produce an identical pass/fail vector
//!     (the confluence self-oracle, dnx-test-runner-design.md §4).

use dnx_test::run_suite;

const SLICE: &str = include_str!("fixtures/import-tree-slice.nix");

#[test]
fn slice_all_passes() {
    let report = run_suite(SLICE, 1, None).expect("slice parses as a suite");
    let failed: Vec<&str> = report
        .cases
        .iter()
        .filter(|c| !c.passed())
        .map(|c| c.path.as_str())
        .collect();
    assert!(
        failed.is_empty(),
        "every slice case must clear the gate; not passing: {failed:?}"
    );
    assert!(report.all_passed());
    // The slice is the demo cut (design §9): a non-trivial number of independent
    // pure cases. Guard the count so a silently-shrunk fixture can't fake a pass.
    assert!(
        report.cases.len() >= 40,
        "slice should hold the full demo cut, found {} cases",
        report.cases.len()
    );
}

#[test]
fn slice_seq_equals_parallel() {
    // Confluence self-oracle: a parallel run must yield byte-identical verdicts
    // to the sequential one — the correctness guarantee behind the speedup.
    let seq = run_suite(SLICE, 1, None).expect("seq");
    let par = run_suite(SLICE, 8, None).expect("par");
    let s: Vec<(&String, bool)> = seq.cases.iter().map(|c| (&c.path, c.passed())).collect();
    let p: Vec<(&String, bool)> = par.cases.iter().map(|c| (&c.path, c.passed())).collect();
    assert_eq!(s, p, "parallel pass/fail must equal sequential");
}
