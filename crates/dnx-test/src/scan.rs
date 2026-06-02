//! Directory scan: evaluate every `.nix` file under a root in parallel and tally
//! the outcome of each, so a real Nix codebase can be measured against dnx's eval
//! subset honestly (how many parse, how many reach a value, how many fail and
//! *why* — by failure kind, not a forced pass).
//!
//! This is the per-*file* companion to the per-*case* suite runner: a `.nix` file
//! is one whole expression, evaluated to its normal form with the file's parent
//! directory as the `import` base ([`NixRuntime::eval_file`]). Files are scanned
//! across a rayon pool exactly like suite cases (`lib.rs` `run_suite`), and for
//! the same reason it is sound: `NixRuntime` is a unit struct holding no
//! cross-call state, so a parallel scan yields the same per-file verdict as a
//! sequential one.
//!
//! A failure is bucketed by the *typed* error it produced ([`FailKind`], a
//! faithful projection of `NixEvalError`/`NixError`), never by string matching —
//! the category is whatever variant the evaluator returned.

use std::path::{Path, PathBuf};

use rayon::prelude::*;

use dnx_core::DnxError;
use dnx_lang::error::NixError;
use dnx_lang::runtime::{NixEvalError, NixEvalResult, NixRuntime};

/// Why a file did not reduce to a value — a one-to-one projection of the
/// evaluator's typed error (`NixEvalError`, and the `NixError` it nests for the
/// parse/elaborate front). Bucketing on the variant (not the rendered message)
/// keeps the tally honest and stable across message wording.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FailKind {
    /// `rnix` could not parse the source, or a parse-time `import` failed.
    Parse,
    /// A construct dnx does not yet elaborate (e.g. `inherit`).
    Unsupported,
    /// A free identifier with no binding, prelude def, or builtin.
    Unbound,
    /// A variable used a number of times the linear core forbids.
    Linearity,
    /// An internal invariant in the front-end was violated.
    Internal,
    /// `import` re-entered a file already being resolved (cycle / depth cap).
    ImportCycle,
    /// Net construction or reduction failed (agent/step limit, bad redex).
    Elaborate,
    /// The normal form could not be read back to a value (e.g. open term).
    Readback,
}

impl FailKind {
    fn of(err: &NixEvalError) -> Self {
        match err {
            NixEvalError::Parse(e) => match e {
                NixError::ParseError(_) => FailKind::Parse,
                NixError::UnsupportedSyntax(_) => FailKind::Unsupported,
                NixError::UnboundVariable(_) => FailKind::Unbound,
                NixError::LinearityViolation(_) => FailKind::Linearity,
                NixError::InternalError(_) => FailKind::Internal,
                NixError::ImportCycle(_) => FailKind::ImportCycle,
                NixError::SearchPathUnset(_) => FailKind::Parse,
            },
            // Net construction over `DnxError`: a linearity violation buried here
            // is still a linearity failure; anything else (step/arena/delta
            // limits, stale/ABA, prim) is a true elaborate/reduce failure.
            NixEvalError::Elaborate(DnxError::LinError(_)) => FailKind::Linearity,
            NixEvalError::Elaborate(_) => FailKind::Elaborate,
            // `pass1` reports the linear-usage check directly as a `LinError`.
            NixEvalError::Elaborate2(_) => FailKind::Linearity,
            NixEvalError::Readback(_) => FailKind::Readback,
        }
    }

    /// Stable lowercase tag for reports.
    pub fn tag(self) -> &'static str {
        match self {
            FailKind::Parse => "parse",
            FailKind::Unsupported => "unsupported",
            FailKind::Unbound => "unbound",
            FailKind::Linearity => "linearity",
            FailKind::Internal => "internal",
            FailKind::ImportCycle => "import-cycle",
            FailKind::Elaborate => "elaborate",
            FailKind::Readback => "readback",
        }
    }
}

/// The result of evaluating one `.nix` file: either it reached a value (carrying
/// a short rendering of what kind) or it failed (carrying the failure kind and
/// the rendered error message for the report).
#[derive(Debug, Clone)]
pub enum FileOutcome {
    /// Reduced to a value; the string is a short kind label (`int`, `attrset`…).
    Value(String),
    /// Failed to reduce; carries the typed kind and the full error text.
    Failed { kind: FailKind, message: String },
}

impl FileOutcome {
    pub fn is_value(&self) -> bool {
        matches!(self, FileOutcome::Value(_))
    }
}

/// One scanned file: its path (relative to the scan root) and its outcome.
#[derive(Debug, Clone)]
pub struct FileReport {
    pub path: PathBuf,
    pub outcome: FileOutcome,
}

/// The whole-directory scan result.
#[derive(Debug, Clone)]
pub struct ScanReport {
    pub files: Vec<FileReport>,
}

impl ScanReport {
    pub fn total(&self) -> usize {
        self.files.len()
    }
    /// Files that reduced to a value.
    pub fn evaluated(&self) -> usize {
        self.files.iter().filter(|f| f.outcome.is_value()).count()
    }
    /// Files that failed (for any reason).
    pub fn failed(&self) -> usize {
        self.total() - self.evaluated()
    }
    /// Count of failures of exactly `kind`.
    pub fn fails_of(&self, kind: FailKind) -> usize {
        self.files
            .iter()
            .filter(|f| matches!(&f.outcome, FileOutcome::Failed { kind: k, .. } if *k == kind))
            .count()
    }
    /// Failure tallies by kind, descending by count then tag — the report's
    /// "top error categories".
    pub fn fail_histogram(&self) -> Vec<(FailKind, usize)> {
        use FailKind::*;
        let mut hist: Vec<(FailKind, usize)> = [
            Parse,
            Unsupported,
            Unbound,
            Linearity,
            Internal,
            ImportCycle,
            Elaborate,
            Readback,
        ]
        .into_iter()
        .map(|k| (k, self.fails_of(k)))
        .filter(|(_, n)| *n > 0)
        .collect();
        hist.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.tag().cmp(b.0.tag())));
        hist
    }
}

/// Short kind label for a successfully-read value (no contents, just the shape).
fn value_kind(v: &NixEvalResult) -> String {
    match v {
        NixEvalResult::Int(_) => "int".into(),
        NixEvalResult::Float(_) => "float".into(),
        NixEvalResult::Str(_) => "string".into(),
        NixEvalResult::Bool(_) => "bool".into(),
        NixEvalResult::Null => "null".into(),
        NixEvalResult::List(xs) => format!("list[{}]", xs.len()),
        NixEvalResult::AttrSet(kv) => format!("attrset{{{}}}", kv.len()),
        NixEvalResult::Lambda(_) => "lambda".into(),
        // An `Error` value here is the readback path's own failure (not the
        // `Err` channel); surface it as a Readback failure with its message.
        NixEvalResult::Error(_) => "error".into(),
    }
}

/// Evaluate one file and classify the result. Pure (no shared state): safe to
/// call concurrently.
fn eval_one(root: &Path, file: &Path) -> FileReport {
    let rt = NixRuntime::pure();
    let outcome = match rt.eval_file(file) {
        NixEvalResult::Error(e) => FileOutcome::Failed {
            kind: FailKind::of(&e),
            message: e.to_string(),
        },
        v => FileOutcome::Value(value_kind(&v)),
    };
    FileReport {
        path: file.strip_prefix(root).unwrap_or(file).to_path_buf(),
        outcome,
    }
}

/// Collect every `*.nix` file under `root`, recursively, in deterministic
/// (sorted) order. A non-readable directory contributes nothing rather than
/// aborting the walk — a scan reports what it can reach.
pub fn collect_nix_files(root: &Path) -> Vec<PathBuf> {
    fn rec(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(rd) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in rd.flatten() {
            let p = entry.path();
            if p.is_dir() {
                rec(&p, out);
            } else if p.extension().and_then(|s| s.to_str()) == Some("nix") {
                out.push(p);
            }
        }
    }
    let mut out = Vec::new();
    rec(root, &mut out);
    out.sort();
    out
}

/// Scan every `.nix` file under `root`, evaluating each across a `jobs`-sized
/// rayon pool. `jobs == 1` is the sequential oracle: by confluence the per-file
/// verdict vector is identical to any `jobs > 1` run.
///
/// Returns an error only if the rayon pool cannot be built; an individual file
/// that fails to evaluate is reported as a `FileOutcome::Failed`, never an early
/// return — the tally is the deliverable.
pub fn scan_dir(root: &Path, jobs: usize) -> Result<ScanReport, String> {
    let files = collect_nix_files(root);
    let jobs = jobs.max(1);
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(jobs)
        .build()
        .map_err(|e| e.to_string())?;
    let reports = pool.install(|| files.par_iter().map(|f| eval_one(root, f)).collect());
    Ok(ScanReport { files: reports })
}

#[cfg(test)]
mod tests {
    use super::*;
    use dnx_core::LinError;
    use std::sync::Arc;

    fn failed(kind: FailKind) -> FileReport {
        FileReport {
            path: PathBuf::from("x.nix"),
            outcome: FileOutcome::Failed {
                kind,
                message: String::new(),
            },
        }
    }
    fn value() -> FileReport {
        FileReport {
            path: PathBuf::from("v.nix"),
            outcome: FileOutcome::Value("int".into()),
        }
    }

    #[test]
    fn failkind_projects_each_typed_error() {
        // Every front-end error variant maps to exactly its bucket — this is the
        // honest-tally contract, so it is pinned per variant.
        let n = Arc::from("v");
        assert_eq!(
            FailKind::of(&NixEvalError::Parse(NixError::ParseError("x".into()))),
            FailKind::Parse
        );
        assert_eq!(
            FailKind::of(&NixEvalError::Parse(NixError::UnsupportedSyntax(
                "x".into()
            ))),
            FailKind::Unsupported
        );
        assert_eq!(
            FailKind::of(&NixEvalError::Parse(NixError::UnboundVariable(Arc::clone(
                &n
            )))),
            FailKind::Unbound
        );
        assert_eq!(
            FailKind::of(&NixEvalError::Parse(NixError::LinearityViolation(
                "x".into()
            ))),
            FailKind::Linearity
        );
        // The two paths a *real* linearity violation actually travels: pass1's
        // direct `LinError` (Elaborate2) and a buried `DnxError::LinError`.
        assert_eq!(
            FailKind::of(&NixEvalError::Elaborate2(LinError::MultiUse(n, 2))),
            FailKind::Linearity
        );
        assert_eq!(
            FailKind::of(&NixEvalError::Elaborate(DnxError::LinError(
                LinError::TooManyFreeVars
            ))),
            FailKind::Linearity
        );
        // A non-linearity reduce failure stays in the elaborate bucket.
        assert_eq!(
            FailKind::of(&NixEvalError::Elaborate(DnxError::StepLimitExceeded(9))),
            FailKind::Elaborate
        );
        assert_eq!(
            FailKind::of(&NixEvalError::Readback("open".into())),
            FailKind::Readback
        );
    }

    #[test]
    fn report_counts_and_histogram() {
        let report = ScanReport {
            files: vec![
                value(),
                value(),
                failed(FailKind::Linearity),
                failed(FailKind::Linearity),
                failed(FailKind::Unsupported),
            ],
        };
        assert_eq!(report.total(), 5);
        assert_eq!(report.evaluated(), 2);
        assert_eq!(report.failed(), 3);
        assert_eq!(report.fails_of(FailKind::Linearity), 2);
        // Histogram: descending by count, only non-empty buckets.
        assert_eq!(
            report.fail_histogram(),
            vec![(FailKind::Linearity, 2), (FailKind::Unsupported, 1)]
        );
        let summed: usize = report.fail_histogram().iter().map(|(_, n)| n).sum();
        assert_eq!(summed, report.failed());
    }

    #[test]
    fn collect_is_sorted_and_nix_only() {
        let dir = std::env::temp_dir().join(format!("dnx-scan-ut-{}", std::process::id()));
        let sub = dir.join("sub");
        std::fs::create_dir_all(&sub).expect("mkdir");
        std::fs::write(dir.join("b.nix"), "1").expect("w");
        std::fs::write(dir.join("a.nix"), "1").expect("w");
        std::fs::write(dir.join("note.txt"), "x").expect("w");
        std::fs::write(sub.join("c.nix"), "1").expect("w");

        let files = collect_nix_files(&dir);
        let rels: Vec<String> = files
            .iter()
            .map(|p| p.strip_prefix(&dir).unwrap_or(p).display().to_string())
            .collect();
        // Only .nix, recursive, sorted (the txt is excluded).
        assert_eq!(rels, vec!["a.nix", "b.nix", "sub/c.nix"]);

        let _ = std::fs::remove_dir_all(&dir);
    }
}
