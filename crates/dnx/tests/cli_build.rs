//! CLI oracle for the polished `dnx` surface: (1) per-subcommand `--help` no
//! longer evaluates `--help` as Nix (the "--help trap", cli-ux.md §2/§5) — it
//! prints a usage line and exits 0; (2) `dnx build EXPR` accepts an inline Nix
//! expression (not just `-f PATH` / `.#ATTR`) and realizes it to a
//! content-addressed store path, rootless, with no `/nix`
//! (e2e-derivation-demo.md §1 + §6).

use std::path::PathBuf;
use std::process::{Command, Output};

/// Run `dnx ARGS…` with `DNX_STORE` pointed at `store` (so a build never
/// mutates the real user store), returning the raw `Output`.
fn dnx_in(store: &std::path::Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_dnx"))
        .args(args)
        .env("DNX_STORE", store)
        .output()
        .expect("spawn dnx")
}

/// A unique scratch store dir for one test (content-addressed, so contents are
/// deterministic regardless of the dir). Removed implicitly with the temp root.
fn scratch_store(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("dnx-test-store-{tag}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    dir
}

/// The headline `builtin:write` derivation as an inline expression (no list
/// field, so it dodges the list-forcing seam — e2e-derivation-demo.md §1).
const WRITE_DRV: &str =
    r#"derivationStrict { name="x"; builder="builtin:write"; text="hi"; system="x86_64-linux"; }"#;

#[test]
fn build_inline_expr_realizes_to_store_path() {
    let store = scratch_store("inline");
    let out = dnx_in(&store, &["build", WRITE_DRV]);
    assert!(
        out.status.success(),
        "inline build failed ({}): {}",
        out.status,
        String::from_utf8_lossy(&out.stderr),
    );
    let path = String::from_utf8(out.stdout)
        .expect("utf8")
        .trim()
        .to_owned();
    // A content-addressed `-out` store path component, with no `/nix` anywhere.
    assert!(
        path.ends_with("-out"),
        "expected an `-out` path, got {path:?}"
    );
    assert!(
        !path.contains("/nix"),
        "store path must not touch /nix: {path:?}"
    );
    // The printed path's basename is the realized file inside the scratch store;
    // its bytes are the derivation's `text` field.
    let written = std::fs::read_to_string(store.join(&path)).expect("read built store file");
    assert_eq!(written, "hi", "the build must write its `text` field");
    let _ = std::fs::remove_dir_all(&store);
}

#[test]
fn build_inline_expr_is_deterministic() {
    let store = scratch_store("determinism");
    let first = dnx_in(&store, &["build", WRITE_DRV]);
    let second = dnx_in(&store, &["build", WRITE_DRV]);
    assert!(
        first.status.success() && second.status.success(),
        "both builds must succeed"
    );
    assert_eq!(
        first.stdout, second.stdout,
        "the same derivation must build to the same store path",
    );
    let _ = std::fs::remove_dir_all(&store);
}

#[test]
fn build_inline_non_derivation_errors_cleanly() {
    // A non-derivation inline expr is a clean typed error, never a panic.
    let store = scratch_store("nondrv");
    let out = dnx_in(&store, &["build", "1 + 2"]);
    assert!(!out.status.success(), "building an int must exit non-zero");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        err.contains("derivation attrset"),
        "error should explain the type mismatch, got: {err}",
    );
    let _ = std::fs::remove_dir_all(&store);
}

/// `dnx <cmd> --help` prints usage and exits 0 — it no longer evaluates
/// `--help` as Nix (the trap). Covers every `cmd_*` guard in one table.
#[test]
fn subcommand_help_prints_usage_and_exits_zero() {
    let store = scratch_store("help");
    for cmd in ["eval", "build", "flake", "store", "test", "py", "daemon"] {
        for flag in ["--help", "-h"] {
            let out = dnx_in(&store, &[cmd, flag]);
            assert!(
                out.status.success(),
                "`dnx {cmd} {flag}` must exit 0, got {} / stderr: {}",
                out.status,
                String::from_utf8_lossy(&out.stderr),
            );
            let stdout = String::from_utf8_lossy(&out.stdout);
            assert!(
                stdout.starts_with("usage: dnx"),
                "`dnx {cmd} {flag}` should print a usage line, got: {stdout}",
            );
        }
    }
}

/// Top-level `dnx --help` / `dnx -h` / `dnx help` list the subcommands (exit 0),
/// while `dnx` with no args still exits 1 (a missing command is an error).
#[test]
fn top_level_help_and_no_args() {
    let store = scratch_store("toplevel");
    for arg in ["--help", "-h", "help"] {
        let out = dnx_in(&store, &[arg]);
        assert!(out.status.success(), "`dnx {arg}` must exit 0");
        assert!(
            String::from_utf8_lossy(&out.stdout).contains("usage: dnx <command>"),
            "`dnx {arg}` should print the top-level usage",
        );
    }
    let none = dnx_in(&store, &[]);
    assert!(
        !none.status.success(),
        "`dnx` with no args must exit non-zero"
    );
}
