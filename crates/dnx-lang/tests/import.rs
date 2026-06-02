use dnx_lang::error::NixError;
use dnx_lang::runtime::{NixEvalError, NixEvalResult, NixRuntime};
use std::sync::atomic::{AtomicU64, Ordering};

fn scratch_dir() -> std::path::PathBuf {
    static CTR: AtomicU64 = AtomicU64::new(0);
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("dnx-import-test-{}-{}", std::process::id(), n));
    std::fs::create_dir_all(&dir).expect("mk scratch dir");
    dir
}

fn int(r: NixEvalResult) -> i64 {
    match r {
        NixEvalResult::Int(n) => n,
        NixEvalResult::Error(e) => panic!("eval error: {e:?}"),
        _ => panic!("expected int"),
    }
}

#[test]
fn import_evaluates_imported_expr() {
    let dir = scratch_dir();
    std::fs::write(dir.join("val.nix"), "1 + 2").expect("write val.nix");
    std::fs::write(dir.join("main.nix"), "(import ./val.nix) + 10").expect("write main.nix");

    let r = NixRuntime::pure().eval_file(&dir.join("main.nix"));
    assert_eq!(int(r), 13, "imported (1+2) then +10");
}

#[test]
fn import_resolves_relative_to_importer() {
    // main imports a/inner.nix, which itself imports b.nix in the SAME dir.
    let dir = scratch_dir();
    let sub = dir.join("a");
    std::fs::create_dir_all(&sub).expect("mk sub");
    std::fs::write(sub.join("b.nix"), "5").expect("write b");
    std::fs::write(sub.join("inner.nix"), "(import ./b.nix) * 4").expect("write inner");
    std::fs::write(dir.join("top.nix"), "import ./a/inner.nix").expect("write top");

    let r = NixRuntime::pure().eval_file(&dir.join("top.nix"));
    assert_eq!(
        int(r),
        20,
        "nested import resolves relative to inner.nix dir"
    );
}

#[test]
fn import_lambda_is_applicable() {
    let dir = scratch_dir();
    std::fs::write(dir.join("f.nix"), "x: x + 1").expect("write f");
    std::fs::write(dir.join("use.nix"), "(import ./f.nix) 41").expect("write use");

    let r = NixRuntime::pure().eval_file(&dir.join("use.nix"));
    assert_eq!(int(r), 42, "imported lambda applied");
}

fn is_cycle(r: NixEvalResult) -> bool {
    matches!(
        r,
        NixEvalResult::Error(NixEvalError::Parse(NixError::ImportCycle(_)))
    )
}

#[test]
fn import_two_file_cycle_is_typed_error_not_crash() {
    // a.nix imports b.nix imports a.nix. Must terminate with a typed
    // ImportCycle error, never recurse the Rust stack into SIGSEGV.
    let dir = scratch_dir();
    std::fs::write(dir.join("a.nix"), "import ./b.nix").expect("write a");
    std::fs::write(dir.join("b.nix"), "import ./a.nix").expect("write b");

    let r = NixRuntime::pure().eval_file(&dir.join("a.nix"));
    assert!(is_cycle(r), "2-file import cycle must be ImportCycle error");
}

#[test]
fn import_self_cycle_is_typed_error_not_crash() {
    // a.nix imports itself.
    let dir = scratch_dir();
    std::fs::write(dir.join("a.nix"), "import ./a.nix").expect("write a");

    let r = NixRuntime::pure().eval_file(&dir.join("a.nix"));
    assert!(is_cycle(r), "self-import cycle must be ImportCycle error");
}

#[test]
fn import_missing_file_errors() {
    let dir = scratch_dir();
    std::fs::write(dir.join("bad.nix"), "import ./nope.nix").expect("write bad");
    match NixRuntime::pure().eval_file(&dir.join("bad.nix")) {
        NixEvalResult::Error(_) => {}
        _ => panic!("missing import must error"),
    }
}

#[test]
fn import_absolute_path_resolves() {
    // An absolute `import /abs/leaf.nix` is used as-is, independent of any base
    // dir. The importer embeds the absolute path of the target literally.
    let dir = scratch_dir();
    let leaf = dir.join("leaf.nix");
    std::fs::write(&leaf, "30 + 3").expect("write leaf");
    // `import <abs>` written into a file that itself has no relevant base dir.
    let src = format!("(import {}) + 9", leaf.display());
    std::fs::write(dir.join("abs.nix"), &src).expect("write abs");

    let r = NixRuntime::pure().eval_file(&dir.join("abs.nix"));
    assert_eq!(int(r), 42, "absolute-path import resolves as-is");
}

#[test]
fn import_nested_three_levels_reroot_per_file() {
    // a.nix → ./mid/b.nix → ./c.nix (the `./c.nix` inside b.nix must resolve
    // against b.nix's OWN dir `mid/`, NOT against a.nix's dir). Proves the base
    // dir is re-rooted at each imported file (imports-design.md §2.4).
    let dir = scratch_dir();
    let mid = dir.join("mid");
    std::fs::create_dir_all(&mid).expect("mk mid");
    std::fs::write(mid.join("c.nix"), "6").expect("write c");
    std::fs::write(mid.join("b.nix"), "(import ./c.nix) * 7").expect("write b");
    std::fs::write(dir.join("a.nix"), "import ./mid/b.nix").expect("write a");

    let r = NixRuntime::pure().eval_file(&dir.join("a.nix"));
    assert_eq!(int(r), 42, "a→mid/b→mid/c re-roots per importing file");
}

#[test]
fn import_directory_resolves_default_nix() {
    // `import ./pkg` (a directory) resolves to `./pkg/default.nix`
    // (imports-design.md §1/§2.2).
    let dir = scratch_dir();
    let pkg = dir.join("pkg");
    std::fs::create_dir_all(&pkg).expect("mk pkg");
    std::fs::write(pkg.join("default.nix"), "21 + 21").expect("write default.nix");
    std::fs::write(dir.join("main.nix"), "import ./pkg").expect("write main");

    let r = NixRuntime::pure().eval_file(&dir.join("main.nix"));
    assert_eq!(int(r), 42, "directory import loads default.nix");
}

#[test]
fn import_depth_cap_is_typed_error_not_stack_overflow() {
    // A NON-cyclic but pathologically deep chain (each file imports a distinct
    // next file) must terminate with a typed `ImportCycle` (the depth-cap reuses
    // that variant) before exhausting the Rust stack. Build a chain longer than
    // MAX_IMPORT_DEPTH (256) so the cap fires.
    let dir = scratch_dir();
    let depth = 400usize;
    // chain_{depth-1} is a leaf scalar; chain_i imports chain_{i+1}.
    std::fs::write(dir.join(format!("chain_{}.nix", depth - 1)), "0").expect("write leaf of chain");
    for i in 0..depth - 1 {
        let body = format!("import ./chain_{}.nix", i + 1);
        std::fs::write(dir.join(format!("chain_{i}.nix")), body).expect("write chain link");
    }

    let r = NixRuntime::pure().eval_file(&dir.join("chain_0.nix"));
    assert!(
        is_cycle(r),
        "an over-deep import chain must be a typed ImportCycle (depth cap), not a crash"
    );
}

#[test]
fn import_non_literal_arg_is_unsupported_syntax() {
    // `import 5` (arg is not a literal path/string) must surface a typed
    // UnsupportedSyntax error, not a cryptic "readback incomplete"
    // (imports-design.md:172).
    let r = NixRuntime::pure().eval("import 5");
    assert!(
        matches!(
            r,
            NixEvalResult::Error(NixEvalError::Parse(NixError::UnsupportedSyntax(_)))
        ),
        "import <non-literal> must be UnsupportedSyntax"
    );
}

#[test]
fn import_unset_search_path_is_typed_error() {
    // `import <name>` for a root absent from the DNX_PATH registry surfaces a
    // typed `SearchPathUnset`, distinct from a filesystem ENOENT `ParseError`
    // (nixpkgs-lib-design.md §1.4). Uses an absurd root so no real DNX_PATH
    // entry can satisfy it — no environment mutation, race-free.
    let r = NixRuntime::pure().eval("import <__dnx_no_such_root_zzz/lib>");
    assert!(
        matches!(
            r,
            NixEvalResult::Error(NixEvalError::Parse(NixError::SearchPathUnset(_)))
        ),
        "unset search-path import must be SearchPathUnset"
    );
}
