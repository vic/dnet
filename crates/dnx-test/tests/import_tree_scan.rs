//! The import-tree directory SCAN, as a reproducible test.
//!
//! `dnx test`'s per-file scanner pointed at the real `~/hk/import-tree` checkout.
//! This is the HONEST tally the project gate wants: how many `.nix` files reduce
//! to a value on dnx's eval subset today, how many fail, and *why* (by typed
//! failure kind). It forces no passes — the count is the deliverable.
//!
//! The tree is the upstream `import-tree` library (a heavy `lib`/module-system
//! codebase), so most of its top-level files lean on features outside the subset
//! (`<nixpkgs/lib>`, `inherit`, ellipsis-pattern lambdas). The leaf `tree/*`
//! fixtures, by contrast, are trivial scalars/attrsets and do evaluate. The exact
//! per-kind breakdown is pinned below; if the evaluator's coverage changes, this
//! test changes with it (it is the regression oracle for the tally).
//!
//! The scan also re-asserts the confluence self-oracle at the file granularity:
//! a parallel scan yields the identical per-file verdict vector as a sequential
//! one (the same property `run_suite` has for cases).

use std::path::Path;

use dnx_test::{scan_dir, FailKind};

const ROOT: &str = "/home/vic/hk/import-tree";

#[test]
fn import_tree_scan_tally() {
    let root = Path::new(ROOT);
    if !root.is_dir() {
        eprintln!("skipping: {ROOT} not present on this host");
        return;
    }

    let report = scan_dir(root, 8).expect("scan builds a pool");

    // 14 `.nix` files in the checkout (4 top-level + 10 under tree/).
    assert_eq!(report.total(), 14, "import-tree .nix file count");

    // 8 reduce to a value on the dnx subset today: the trivial tree/ leaves
    // (six `{ }`, one `true`, one `"z"`, one `{ hello = "world"; }`).
    assert_eq!(report.evaluated(), 8, "files that reach a value");
    assert_eq!(report.failed(), 6, "files that fail");

    // The honest per-kind failure breakdown. Pattern-lambda linearity now
    // elaborates most ellipsis (`{ a, ... }:`) patterns, and the dynamic-attr /
    // `inherit` parser work lets the heavy top-level files parse further, so the
    // remaining 6 failures split across three kinds:
    //   * 2 elaborate  — files that parse but hit an unsupported elaborate
    //                    construct (module-system / `inherit (e) …` shapes);
    //   * 2 linearity  — `@`-pattern / non-linear attrset-arg reuse still rejected;
    //   * 2 parse      — `import <nixpkgs/lib>` search-path resolution.
    assert_eq!(
        report.fails_of(FailKind::Elaborate),
        2,
        "elaborate failures"
    );
    assert_eq!(
        report.fails_of(FailKind::Linearity),
        2,
        "linearity failures"
    );
    assert_eq!(
        report.fails_of(FailKind::Parse),
        2,
        "search-path / parse failures"
    );

    // The histogram accounts for every failure, no leftover buckets.
    let from_hist: usize = report.fail_histogram().iter().map(|(_, n)| n).sum();
    assert_eq!(from_hist, report.failed(), "histogram covers all failures");
}

#[test]
fn import_tree_scan_seq_equals_parallel() {
    let root = Path::new(ROOT);
    if !root.is_dir() {
        eprintln!("skipping: {ROOT} not present on this host");
        return;
    }
    let seq = scan_dir(root, 1).expect("seq scan");
    let par = scan_dir(root, 8).expect("par scan");
    let s: Vec<(&Path, bool)> = seq
        .files
        .iter()
        .map(|f| (f.path.as_path(), f.outcome.is_value()))
        .collect();
    let p: Vec<(&Path, bool)> = par
        .files
        .iter()
        .map(|f| (f.path.as_path(), f.outcome.is_value()))
        .collect();
    assert_eq!(s, p, "parallel per-file verdict must equal sequential");
}
