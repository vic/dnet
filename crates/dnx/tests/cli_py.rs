//! CLI oracle for the `dnx py` subcommand: a Python-subset expression / file
//! evaluates through the SAME δ-net pipeline as Nix and prints in the SAME
//! `print_eval` form (dnx-py-interop.md §4). The headline case drives the
//! built binary on examples/hello.py and the equivalent examples/hello.nix and
//! asserts they read back to the same value — one substrate, two languages.

use std::path::PathBuf;
use std::process::Command;

/// Run `dnx ARGS…`, returning trimmed stdout. Panics (test-only) with stderr on
/// a non-zero exit so a failed eval never masquerades as an empty success.
fn dnx(args: &[&str]) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_dnx"))
        .args(args)
        .output()
        .expect("spawn dnx");
    assert!(
        out.status.success(),
        "dnx {args:?} failed ({}): {}",
        out.status,
        String::from_utf8_lossy(&out.stderr),
    );
    String::from_utf8(out.stdout)
        .expect("utf8 stdout")
        .trim_end()
        .to_string()
}

/// Absolute path to a file under this crate's `examples/` dir.
fn example(name: &str) -> String {
    let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    p.push("examples");
    p.push(name);
    p.to_string_lossy().into_owned()
}

#[test]
fn py_eval_inline_arithmetic() {
    // Mirrors the pyparse `arithmetic_precedence` oracle, through the binary.
    assert_eq!(dnx(&["py", "eval", "1 + 2 * 3"]), "7");
}

#[test]
fn py_eval_inline_string() {
    assert_eq!(dnx(&["py", "eval", r#""a" + "b""#]), "ab");
}

#[test]
fn py_file_evaluates() {
    // `dnx py FILE.py` — the file form. hello.py is a derivation → attrset.
    assert_eq!(dnx(&["py", &example("hello.py")]), "{ 4 attrs }");
}

#[test]
fn py_eval_file_flag() {
    // `dnx py eval --file FILE.py` is equivalent to `dnx py FILE.py`.
    assert_eq!(
        dnx(&["py", "eval", "--file", &example("hello.py")]),
        dnx(&["py", &example("hello.py")]),
    );
}

/// The cross-language beat through the binary: the Python frontend
/// (`dnx py hello.py`) and the Nix frontend (`dnx eval --file hello.nix`) read
/// the same derivation back to the identical printed value.
#[test]
fn py_file_reads_back_like_nix_file() {
    let py = dnx(&["py", &example("hello.py")]);
    let nix = dnx(&["eval", "--file", &example("hello.nix")]);
    assert_eq!(
        py, nix,
        "python and nix derivations must read back the same"
    );
}

#[test]
fn py_unknown_subcommand_fails() {
    let out = Command::new(env!("CARGO_BIN_EXE_dnx"))
        .args(["py", "wat"])
        .output()
        .expect("spawn dnx");
    assert!(!out.status.success(), "py wat must exit non-zero");
}
