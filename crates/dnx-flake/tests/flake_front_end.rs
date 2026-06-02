use std::path::PathBuf;
use std::sync::atomic::{AtomicU32, Ordering};

use dnx_flake::{Flake, FlakeError, FlakeInputs, LockFile, LockStatus, OutputKind};
use dnx_lang::runtime::NixEvalResult;
use dnx_store::Store;

static CTR: AtomicU32 = AtomicU32::new(0);

/// A throwaway temp directory, cleaned on drop. No external dep.
struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new() -> TempDir {
        let n = CTR.fetch_add(1, Ordering::Relaxed);
        let mut path = std::env::temp_dir();
        path.push(format!("dnx-flake-test-{}-{n}", std::process::id()));
        std::fs::create_dir_all(&path).expect("test setup: mkdir temp");
        TempDir { path }
    }
    fn write(&self, name: &str, content: &str) -> PathBuf {
        let p = self.path.join(name);
        std::fs::write(&p, content).expect("test setup: write file");
        p
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

// Nested attribute sets (not flat `packages.<sys>.<attr> = ...` attrpaths):
// the evaluator's green subset desugars nested literals correctly, while flat
// multi-segment attrpath definitions are not yet selectable (see the
// `resolve_attr_flat_attrpath_*` test documenting that limit).
const MINIMAL_FLAKE: &str = r#"{
  description = "a minimal dnx flake";
  inputs = { self = { url = "."; }; };
  outputs = inputs: {
    packages = {
      x86_64-linux = {
        hello = 1;
        world = 2;
      };
    };
    apps = {
      x86_64-linux = {
        run = 3;
      };
    };
  };
}"#;

#[test]
fn load_parses_a_minimal_flake() {
    let dir = TempDir::new();
    dir.write("flake.nix", MINIMAL_FLAKE);
    let flake = Flake::load(&dir.path).expect("minimal flake.nix should load");
    let _ = flake;
}

#[test]
fn load_rejects_a_non_flake() {
    let dir = TempDir::new();
    dir.write("flake.nix", "1 + 1");
    assert!(
        Flake::load(&dir.path).is_err(),
        "a bare expression is not a flake (no outputs)"
    );
}

#[test]
fn show_enumerates_output_attr_names() {
    let dir = TempDir::new();
    dir.write("flake.nix", MINIMAL_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    let out = flake.show().expect("show");
    let names: Vec<&str> = out.paths().iter().map(|s| s.as_ref()).collect();
    assert_eq!(
        names,
        vec![
            "apps.x86_64-linux.run",
            "packages.x86_64-linux.hello",
            "packages.x86_64-linux.world",
        ],
        "show lists fully-qualified output paths, sorted"
    );
}

// A shallow-output flake: `outputs` returns a single-level attribute set of
// scalars. This is the evaluator's green subset for `resolve_attr` (applying
// the outputs function and selecting a scalar leaf reaches WHNF).
const SHALLOW_FLAKE: &str = r#"{
  outputs = inputs: {
    answer = 42;
    greeting = "hi";
  };
}"#;

#[test]
fn resolve_attr_evaluates_an_output_path_to_whnf() {
    let dir = TempDir::new();
    dir.write("flake.nix", SHALLOW_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    // Applying the outputs fn and selecting a scalar leaf reaches WHNF: proves
    // the eval seam (a drv layer consumes this) is live.
    match flake.resolve_attr("answer") {
        Ok(NixEvalResult::Int(42)) => {}
        Ok(NixEvalResult::Int(n)) => panic!("expected Int(42) at WHNF, got Int({n})"),
        Ok(_) => panic!("expected Int(42) at WHNF, got a non-int value"),
        Err(e) => panic!("expected Int(42) at WHNF, got error: {e}"),
    }
}

#[test]
fn resolve_attr_missing_path_is_an_error() {
    let dir = TempDir::new();
    dir.write("flake.nix", SHALLOW_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    assert!(
        flake.resolve_attr("nope").is_err(),
        "a missing output path is a typed error, not a panic"
    );
}

// Documents the honest eval seam (a future drv layer extends it): the
// evaluator flattens a flat multi-segment attrpath definition
// (`packages.<sys>.<attr> = v`) into a single dotted key, which a nested
// `.packages.<sys>.<attr>` select cannot reach. `show` still enumerates such
// paths from the surface AST; only `resolve_attr` (which evaluates) is limited.
const FLAT_FLAKE: &str = r#"{
  outputs = inputs: {
    packages.x86_64-linux.hello = 1;
  };
}"#;

#[test]
fn show_enumerates_flat_attrpath_outputs() {
    let dir = TempDir::new();
    dir.write("flake.nix", FLAT_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    let out = flake.show().expect("show");
    let names: Vec<&str> = out.paths().iter().map(|s| s.as_ref()).collect();
    assert_eq!(names, vec!["packages.x86_64-linux.hello"]);
}

#[test]
fn resolve_attr_flat_attrpath_is_an_unevaluable_seam() {
    let dir = TempDir::new();
    dir.write("flake.nix", FLAT_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    // Flat attrpath outputs are enumerable but not yet evaluable: the seam a
    // future drv layer would extend. Today this is a typed error, never a panic.
    assert!(
        flake.resolve_attr("packages.x86_64-linux.hello").is_err(),
        "flat-attrpath output is an honest eval-seam limit"
    );
}

#[test]
fn lock_round_trips_a_local_path_input_pinned_by_blake3() {
    let dir = TempDir::new();
    let input = dir.write("dep.txt", "hello dnx");
    let expected = blake3::hash(b"hello dnx");

    let mut lock = LockFile::default();
    lock.pin("dep", &input, &input).expect("pin local path");

    // The recorded hash is BLAKE3 of the input content.
    assert_eq!(lock.entries().len(), 1);
    assert_eq!(lock.entries()[0].name(), "dep");
    assert_eq!(lock.entries()[0].hash(), expected.as_bytes());

    // Round-trip: serialize, re-parse, structurally identical.
    let text = lock.to_text();
    let reparsed = LockFile::from_text(&text).expect("from_text");
    assert_eq!(reparsed, lock, "lock survives a write/read round-trip");

    // Verify re-hashes the path and confirms the pin still matches. The stored
    // path is absolute here, so it resolves regardless of the base.
    reparsed
        .verify(&dir.path)
        .expect("verify a freshly pinned input");
}

#[test]
fn lock_verify_detects_a_changed_input() {
    let dir = TempDir::new();
    let input = dir.write("dep.txt", "original");
    let mut lock = LockFile::default();
    lock.pin("dep", &input, &input).expect("pin");

    // Mutate the input after pinning: verify must reject.
    dir.write("dep.txt", "tampered");
    assert!(
        lock.verify(&dir.path).is_err(),
        "verify rejects an input whose content no longer matches its hash"
    );
}

// A flake whose `outputs` is applied to `{}` by `resolve_attr`. The attr-path
// is spliced into a built Nix selector; a path must therefore never be able to
// inject or break that expression (review: flake.rs:70 Nix-source injection).
const SEAM_FLAKE: &str = r#"{
  outputs = inputs: {
    packages = { x86_64-linux = { hello = 7; }; };
  };
}"#;

#[test]
fn resolve_attr_rejects_a_statement_injection_path() {
    let dir = TempDir::new();
    dir.write("flake.nix", SEAM_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    // `x; builtins.currentTime` would, if spliced raw, turn the selector into a
    // second statement evaluating an impure builtin. The guard rejects the path
    // as an invalid attr-path segment *before* any eval.
    match flake.resolve_attr("x; builtins.currentTime") {
        Err(FlakeError::AttrNotFound(_)) => {}
        Err(e) => panic!("expected AttrNotFound for an injection path, got error: {e}"),
        Ok(_) => panic!("an injection path must never be evaluated"),
    }
}

#[test]
fn resolve_attr_rejects_a_brace_breaking_path() {
    let dir = TempDir::new();
    dir.write("flake.nix", SEAM_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    // A `}`-containing path would close the applied-inputs set and corrupt the
    // parse. Rejected as an invalid segment, never evaluated.
    match flake.resolve_attr("hello}.x") {
        Err(FlakeError::AttrNotFound(_)) => {}
        Err(e) => panic!("expected AttrNotFound for a brace-breaking path, got error: {e}"),
        Ok(_) => panic!("a brace-breaking path must never be evaluated"),
    }
}

#[test]
fn resolve_attr_accepts_a_valid_dotted_path_at_the_guard() {
    let dir = TempDir::new();
    dir.write("flake.nix", SEAM_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    // The valid `packages.x86_64-linux.hello` path must pass the injection guard
    // (it is not rejected as a bad segment). Whether it then reaches WHNF or hits
    // the documented deep-output eval seam, the guard is never the thing that
    // rejects a legitimate dotted path.
    if let Err(FlakeError::AttrNotFound(p)) = flake.resolve_attr("packages.x86_64-linux.hello") {
        panic!("guard wrongly rejected a valid dotted path: {p}")
    }
}

// A flake with a dynamic (`${...}`) output attribute key. Such a key cannot be
// enumerated statically and must never be fabricated into an empty / partial
// segment (review: flake.rs:163 interpolation-key collapse).
const DYNAMIC_KEY_FLAKE: &str = r#"{
  outputs = inputs: {
    "${sys}" = 1;
  };
}"#;

#[test]
fn show_rejects_a_dynamic_output_key() {
    let dir = TempDir::new();
    dir.write("flake.nix", DYNAMIC_KEY_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    // `"${sys}"` is a dynamic key: `show` must raise a typed parse error, not
    // accept a bogus empty segment.
    match flake.show() {
        Err(FlakeError::Parse(_)) => {}
        other => panic!("expected Parse for a dynamic output key, got {other:?}"),
    }
}

// A flake whose output reads a formal (`nixpkgs`) that is NOT a declared input:
// `inputs` resolves to a set without `nixpkgs`, so forcing the output errors on
// the missing input. An undeclared input that an output actually consumes is a
// typed eval error, never a silent resolve against a fabricated value.
const FORMALS_FLAKE: &str = r#"{
  outputs = { self, nixpkgs }: {
    answer = nixpkgs.answer;
  };
}"#;

#[test]
fn resolve_attr_rejects_a_consumed_undeclared_input() {
    let dir = TempDir::new();
    dir.write("flake.nix", FORMALS_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    match flake.resolve_attr("answer") {
        Err(FlakeError::Eval(_)) => {}
        Err(e) => panic!("expected Eval error for a consumed undeclared input, got error: {e}"),
        Ok(_) => panic!("a consumed undeclared input must not silently resolve"),
    }
}

// A flake whose `outputs` consumes a declared local-path input: `dep`'s flake
// exposes `answer = 7`, and this flake's output references `dep.answer`. Wiring
// inputs → outputs (resolve each declared input's flake outputs, pass them as
// the `outputs` function argument) is what makes `consumes` evaluate (NOT cppNix
// compat — our local-path schema, arch.md:70). `self` (url ".") resolves to this
// flake's own outputs, one level deep (genuine recursion stays the honest gate,
// arch.md:45).
const DEP_FLAKE: &str = r#"{
  outputs = inputs: { answer = 7; };
}"#;
const CONSUMER_FLAKE: &str = r#"{
  inputs = {
    self = { url = "."; };
    dep = { url = "./dep"; };
  };
  outputs = { self, dep, ... }: {
    consumes = dep.answer;
  };
}"#;

#[test]
fn resolve_attr_wires_a_declared_input_into_outputs() {
    let dir = TempDir::new();
    dir.write("flake.nix", CONSUMER_FLAKE);
    std::fs::create_dir_all(dir.path.join("dep")).expect("mkdir dep");
    dir.write("dep/flake.nix", DEP_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    // The output `consumes` reads `dep.answer`; the resolved `dep` input (its
    // flake's `outputs {}`) supplies `answer = 7`.
    match flake.resolve_attr("consumes") {
        Ok(NixEvalResult::Int(7)) => {}
        Ok(NixEvalResult::Int(n)) => panic!("expected Int(7) from a wired input, got Int({n})"),
        Ok(_) => panic!("expected Int(7) from a wired input, got a non-int value"),
        Err(e) => panic!("expected Int(7) from a wired input, got error: {e}"),
    }
}

// Transitive inputs (input-of-input): the consumer reads `mid.value`; `mid`'s
// own `value` reads `leaf.answer` from *its* declared input. A one-level
// resolution would apply `mid`'s outputs to `{}`, leaving `leaf` undefined and
// erroring; transitive resolution applies `mid`'s outputs to `mid`'s resolved
// inputs, so `leaf.answer` flows two levels up.
const TRANSITIVE_CONSUMER_FLAKE: &str = r#"{
  inputs = { mid = { url = "./mid"; }; };
  outputs = { mid, ... }: { top = mid.value; };
}"#;
const TRANSITIVE_MID_FLAKE: &str = r#"{
  inputs = { leaf = { url = "./leaf"; }; };
  outputs = { leaf, ... }: { value = leaf.answer; };
}"#;
const TRANSITIVE_LEAF_FLAKE: &str = r#"{
  outputs = inputs: { answer = 9; };
}"#;

#[test]
fn resolve_attr_resolves_transitive_inputs() {
    let dir = TempDir::new();
    dir.write("flake.nix", TRANSITIVE_CONSUMER_FLAKE);
    std::fs::create_dir_all(dir.path.join("mid/leaf")).expect("mkdir mid/leaf");
    dir.write("mid/flake.nix", TRANSITIVE_MID_FLAKE);
    dir.write("mid/leaf/flake.nix", TRANSITIVE_LEAF_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    // `top` reads `mid.value`, and `mid.value` reads `leaf.answer = 9`: the input
    // of an input flowed through, proving transitive (not one-level) resolution.
    match flake.resolve_attr("top") {
        Ok(NixEvalResult::Int(9)) => {}
        Ok(NixEvalResult::Int(n)) => {
            panic!("expected Int(9) through transitive inputs, got Int({n})")
        }
        Ok(_) => panic!("expected Int(9) through transitive inputs, got a non-int value"),
        Err(e) => panic!("expected Int(9) through transitive inputs, got error: {e}"),
    }
}

// A back-edge cycle `A -> B -> A`: `A` declares input `b`, and `b` declares an
// input pointing back at `A`'s directory. Transitive resolution must terminate
// (the revisited directory resolves to a source marker, never recursing
// forever). `A`'s output reads `b.tag`, a plain value `b` exposes without
// touching the back-edge, so the output still reaches WHNF.
const CYCLE_A_FLAKE: &str = r#"{
  inputs = { b = { url = "./b"; }; };
  outputs = { b, ... }: { fromB = b.tag; };
}"#;
const CYCLE_B_FLAKE: &str = r#"{
  inputs = { a = { url = ".."; }; };
  outputs = { a, ... }: { tag = 5; };
}"#;

#[test]
fn resolve_attr_terminates_on_an_input_cycle() {
    let dir = TempDir::new();
    dir.write("flake.nix", CYCLE_A_FLAKE);
    std::fs::create_dir_all(dir.path.join("b")).expect("mkdir b");
    dir.write("b/flake.nix", CYCLE_B_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    // `b`'s input `a` points back at the root: it resolves to a source marker, so
    // resolution terminates and `b.tag = 5` still reaches WHNF.
    match flake.resolve_attr("fromB") {
        Ok(NixEvalResult::Int(5)) => {}
        Ok(NixEvalResult::Int(n)) => {
            panic!("expected Int(5) past a terminated cycle, got Int({n})")
        }
        Ok(_) => panic!("expected Int(5) past a terminated cycle, got a non-int value"),
        Err(e) => panic!("expected Int(5) past a terminated cycle, got error: {e}"),
    }
}

// `dnx flake lock` (arch.md:70): build our `flake.lock` from the declared
// `inputs`, pinning each local path by BLAKE3. `self` (".") pins the flake's own
// `flake.nix`; `dep` pins its `flake.nix`. Our format, not the cppNix node graph.
#[test]
fn lock_pins_declared_inputs_from_a_flake() {
    let dir = TempDir::new();
    dir.write("flake.nix", CONSUMER_FLAKE);
    std::fs::create_dir_all(dir.path.join("dep")).expect("mkdir dep");
    dir.write("dep/flake.nix", DEP_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    let lock = flake.lock().expect("lock");
    let names: Vec<&str> = lock.entries().iter().map(|e| e.name()).collect();
    assert_eq!(
        names,
        vec!["dep", "self"],
        "lock pins every declared input, sorted"
    );
    // The pinned hashes are BLAKE3 of each resolved input's flake.nix content.
    let dep_hash = blake3::hash(DEP_FLAKE.as_bytes());
    let self_hash = blake3::hash(CONSUMER_FLAKE.as_bytes());
    let by = |n: &str| {
        lock.entries()
            .iter()
            .find(|e| e.name() == n)
            .expect("entry")
    };
    assert_eq!(by("dep").hash(), dep_hash.as_bytes());
    assert_eq!(by("self").hash(), self_hash.as_bytes());
    lock.verify(&dir.path).expect("freshly built lock verifies");
}

// Lock determinism + portability (audit-flake.md MED): the `flake.lock` for a
// flake must not depend on how its directory was spelled. Pre-fix the lock's
// path column was `self.dir.join(url)` verbatim, so a non-canonical dir (`.`-
// padded, `..`-routed, or absolute) produced a DIFFERENT lock for the same
// flake. The stored path is now flake-relative, so every spelling of the same
// directory yields a byte-identical lock — and the lock has no absolute,
// machine-specific path in it at all.
#[test]
fn lock_is_deterministic_across_dir_spellings_and_portable() {
    let dir = TempDir::new();
    dir.write("flake.nix", CONSUMER_FLAKE);
    std::fs::create_dir_all(dir.path.join("dep")).expect("mkdir dep");
    dir.write("dep/flake.nix", DEP_FLAKE);

    // Three spellings of the SAME directory: absolute, `.`-padded, and routed
    // through the parent (`<dir>/dep/..` == `<dir>`). The first stands in for an
    // absolute `dnx flake lock <abs>`; the others for a non-canonical spelling
    // such as `dnx flake lock .`.
    let abs = dir.path.clone();
    let dotted = dir.path.join(".");
    let routed = dir.path.join("dep").join("..");

    let lock_abs = Flake::load(&abs)
        .expect("load abs")
        .lock()
        .expect("lock abs");
    let lock_dotted = Flake::load(&dotted)
        .expect("load dotted")
        .lock()
        .expect("lock dotted");
    let lock_routed = Flake::load(&routed)
        .expect("load routed")
        .lock()
        .expect("lock routed");

    assert_eq!(
        lock_abs.to_text(),
        lock_dotted.to_text(),
        "the lock for a `.`-padded dir must equal the lock for the absolute dir"
    );
    assert_eq!(
        lock_abs.to_text(),
        lock_routed.to_text(),
        "the lock for a `..`-routed dir must equal the lock for the absolute dir"
    );

    // Portable: no absolute path leaks into the lock's path column.
    let text = lock_abs.to_text();
    assert!(
        !text.contains(dir.path.to_str().expect("utf-8 temp path")),
        "a portable lock records no machine-specific absolute path, got:\n{text}"
    );

    // The relative paths still verify against the flake dir (any spelling).
    lock_abs.verify(&abs).expect("verify against abs");
    lock_abs.verify(&dotted).expect("verify against dotted");
}

// `Flake::load` accepts a `flake.nix` file path directly, not only its parent
// directory — `dnx flake show <file>` passes the file through unchanged.
#[test]
fn load_accepts_a_flake_file_path() {
    let dir = TempDir::new();
    let file = dir.write("flake.nix", SHALLOW_FLAKE);
    Flake::load(&file).expect("load from a flake.nix file path");
    Flake::load(&dir.path).expect("load from the containing directory");
}

// A flake whose one output is a derivation. `packages` is defined before the
// scalar sibling: a scalar field preceding a nested-attrset field trips a
// pre-existing evaluator `insert` limit (an honest eval seam, owned by the
// engine), so the demo orders the nested output first.
const DRV_FLAKE: &str = r#"{
  outputs = inputs: {
    packages = {
      x86_64-linux = {
        default = builtins.derivationStrict {
          name = "hello";
          builder = "/bin/sh";
          system = "x86_64-linux";
        };
      };
    };
    answer = 42;
  };
}"#;

fn store_in(dir: &TempDir) -> Store {
    Store::open_at(dir.path.join("store")).expect("open temp store")
}

#[test]
fn report_classifies_a_derivation_output_with_a_drv_path() {
    let dir = TempDir::new();
    dir.write("flake.nix", DRV_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    let report = flake.report(&store_in(&dir)).expect("report");

    // The derivation leaf is recognized and instantiated to a drvPath; the
    // scalar leaf is a plain value. Both resolved, so the report is `ok`.
    let drv = report
        .entries()
        .iter()
        .find(|(p, _)| p.as_ref() == "packages.x86_64-linux.default")
        .map(|(_, k)| k)
        .expect("derivation output present");
    match drv {
        OutputKind::Derivation { drv_path } => {
            assert!(
                drv_path.name().ends_with(".drv"),
                "a derivation output instantiates to a .drv store path, got {drv_path}"
            );
        }
        other => panic!("expected a Derivation output, got {other:?}"),
    }
    let answer = report
        .entries()
        .iter()
        .find(|(p, _)| p.as_ref() == "answer")
        .map(|(_, k)| k)
        .expect("scalar output present");
    assert!(
        matches!(answer, OutputKind::Value { .. }),
        "a scalar leaf is a plain value, got {answer:?}"
    );
    assert!(report.ok(), "every output resolved, so the report is ok");
}

// A scalar defined *before* a nested attrset used to trip the LOPath
// frontier-collision in `insert` and surface as `Unresolved`. With the
// collision-free App fn-side LOPath (pass2), both outputs now resolve and the
// report is `ok`. See crates/dnx-lang/tests/insert_nonscalar.rs.
const SCALAR_BEFORE_NESTED_FLAKE: &str = r#"{
  outputs = inputs: {
    answer = 42;
    packages = { x86_64-linux = { default = 1; }; };
  };
}"#;

#[test]
fn report_resolves_scalar_before_nested_output() {
    let dir = TempDir::new();
    dir.write("flake.nix", SCALAR_BEFORE_NESTED_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    let report = flake.report(&store_in(&dir)).expect("report");
    assert!(
        report
            .entries()
            .iter()
            .all(|(_, k)| !matches!(k, OutputKind::Unresolved { .. })),
        "no output hits the eval seam: all resolve, got {:?}",
        report.entries()
    );
    assert!(
        report.ok(),
        "a report with every output resolved is ok (check exits zero)"
    );
}

// A flake whose derivation output *consumes a declared input*: `dep` exposes
// `system`, and the consumer's `packages.x86_64-linux.default` derivation reads
// `dep.system` for its `system` field. This is the end-to-end seam — inputs →
// outputs → derivation → drvPath — in one fixture: `report` must instantiate the
// derivation (proving the wired input flowed into it; an unwired input would
// error and surface `Unresolved`), and `lock` must pin both declared inputs.
const DRV_CONSUMES_INPUT_FLAKE: &str = r#"{
  inputs = {
    self = { url = "."; };
    dep = { url = "./dep"; };
  };
  outputs = { self, dep, ... }: {
    packages = {
      x86_64-linux = {
        default = builtins.derivationStrict {
          name = "hello";
          builder = "/bin/sh";
          system = dep.system;
        };
      };
    };
  };
}"#;
const DEP_SYSTEM_FLAKE: &str = r#"{
  outputs = inputs: { system = "x86_64-linux"; };
}"#;

#[test]
fn report_instantiates_a_derivation_that_consumes_an_input_and_lock_pins_it() {
    let dir = TempDir::new();
    dir.write("flake.nix", DRV_CONSUMES_INPUT_FLAKE);
    std::fs::create_dir_all(dir.path.join("dep")).expect("mkdir dep");
    dir.write("dep/flake.nix", DEP_SYSTEM_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");

    // `show` enumerates the one derivation output path.
    let out = flake.show().expect("show");
    let names: Vec<&str> = out.paths().iter().map(|s| s.as_ref()).collect();
    assert_eq!(names, vec!["packages.x86_64-linux.default"]);

    // `report` resolves it: the derivation reads `dep.system` (a wired input),
    // so it instantiates to a drvPath — and the report is `ok` (check exits 0).
    let report = flake.report(&store_in(&dir)).expect("report");
    let kind = report
        .entries()
        .iter()
        .find(|(p, _)| p.as_ref() == "packages.x86_64-linux.default")
        .map(|(_, k)| k)
        .expect("derivation output present");
    match kind {
        OutputKind::Derivation { drv_path } => assert!(
            drv_path.name().ends_with(".drv"),
            "a derivation consuming a wired input instantiates to a .drv, got {drv_path}"
        ),
        other => panic!("expected a Derivation output, got {other:?}"),
    }
    assert!(
        report.ok(),
        "the derivation resolved, so the report is ok (check exits zero)"
    );

    // `lock` pins both declared inputs by content hash.
    let lock = flake.lock().expect("lock");
    let pinned: Vec<&str> = lock.entries().iter().map(|e| e.name()).collect();
    assert_eq!(
        pinned,
        vec!["dep", "self"],
        "lock pins every declared input, sorted"
    );
    lock.verify(&dir.path).expect("freshly built lock verifies");
}

// Our `inputs` schema (NOT cppNix flake-URL grammar): each `inputs.<name>` is an
// attribute set with a `url` that is a plain local path string. `inputs` is the
// bridge a `flake.lock` is built from (each input pinned by content hash).
const INPUTS_FLAKE: &str = r#"{
  inputs = {
    dep = { url = "./vendor/dep"; };
    other = { url = "../sibling"; };
  };
  outputs = inputs: { answer = 1; };
}"#;

#[test]
fn inputs_enumerates_local_path_inputs_sorted() {
    let dir = TempDir::new();
    dir.write("flake.nix", INPUTS_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    let inputs = flake.inputs().expect("inputs");
    let pairs: Vec<(&str, &str)> = inputs
        .entries()
        .iter()
        .map(|i| (i.name(), i.url()))
        .collect();
    assert_eq!(
        pairs,
        vec![("dep", "./vendor/dep"), ("other", "../sibling")],
        "inputs lists each declared input's name and local-path url, sorted by name"
    );
}

// `dnx flake metadata` surfaces a flake's declared `description` (a plain
// top-level string). The minimal flake declares one; it is read by the same
// evaluation-free surface walk as `inputs`/`show`.
#[test]
fn description_returns_the_declared_description() {
    let dir = TempDir::new();
    dir.write("flake.nix", MINIMAL_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    assert_eq!(
        flake.description().expect("description").as_deref(),
        Some("a minimal dnx flake"),
        "description reads the top-level `description` string"
    );
}

// A flake with no `description` attribute has none — `None`, not an error or a
// fabricated empty string (mirrors `inputs_absent_is_empty`).
#[test]
fn description_absent_is_none() {
    let dir = TempDir::new();
    dir.write("flake.nix", SHALLOW_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    assert!(
        flake.description().expect("description").is_none(),
        "a flake with no `description` attr has no description"
    );
}

// `lock_status` is the `dnx flake metadata` lock line: with no `flake.lock`
// beside the flake, the status is `Absent` (nothing pinned yet).
#[test]
fn lock_status_absent_when_no_lock_file() {
    let dir = TempDir::new();
    dir.write("flake.nix", CONSUMER_FLAKE);
    std::fs::create_dir_all(dir.path.join("dep")).expect("mkdir dep");
    dir.write("dep/flake.nix", DEP_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    assert_eq!(
        flake.lock_status().expect("lock_status"),
        LockStatus::Absent,
        "no flake.lock beside the flake is an Absent lock status"
    );
}

// After `lock` writes `flake.lock`, the status is `UpToDate`: every declared
// input is pinned and each pinned content still hashes to its record.
#[test]
fn lock_status_up_to_date_after_lock() {
    let dir = TempDir::new();
    dir.write("flake.nix", CONSUMER_FLAKE);
    std::fs::create_dir_all(dir.path.join("dep")).expect("mkdir dep");
    dir.write("dep/flake.nix", DEP_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    std::fs::write(
        dir.path.join("flake.lock"),
        flake.lock().expect("lock").to_text(),
    )
    .expect("write flake.lock");
    assert_eq!(
        flake.lock_status().expect("lock_status"),
        LockStatus::UpToDate,
        "a freshly written lock matching every declared input is UpToDate"
    );
}

// A lock that pins a different set of inputs than the flake now declares is
// `Stale`: here the lock is written, then the flake gains a second input, so the
// declared set no longer matches the pinned set.
#[test]
fn lock_status_stale_when_declared_inputs_change() {
    let dir = TempDir::new();
    // First: a flake with a single `dep` input; lock it.
    dir.write("flake.nix", CONSUMER_ONE_INPUT_FLAKE);
    std::fs::create_dir_all(dir.path.join("dep")).expect("mkdir dep");
    dir.write("dep/flake.nix", DEP_FLAKE);
    let locked = Flake::load(&dir.path).expect("load one-input");
    std::fs::write(
        dir.path.join("flake.lock"),
        locked.lock().expect("lock").to_text(),
    )
    .expect("write flake.lock");
    // Then: redeclare with an extra `self` input — the lock is now stale.
    dir.write("flake.nix", CONSUMER_FLAKE);
    let flake = Flake::load(&dir.path).expect("load two-input");
    assert_eq!(
        flake.lock_status().expect("lock_status"),
        LockStatus::Stale,
        "a lock whose pinned inputs differ from the declared inputs is Stale"
    );
}

// A `flake.lock` whose pinned content no longer hashes to its record is `Stale`:
// the input flake's `flake.nix` changed after locking.
#[test]
fn lock_status_stale_when_pinned_content_changes() {
    let dir = TempDir::new();
    dir.write("flake.nix", CONSUMER_ONE_INPUT_FLAKE);
    std::fs::create_dir_all(dir.path.join("dep")).expect("mkdir dep");
    dir.write("dep/flake.nix", DEP_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    std::fs::write(
        dir.path.join("flake.lock"),
        flake.lock().expect("lock").to_text(),
    )
    .expect("write flake.lock");
    // Tamper with the pinned input's content: same name set, hash no longer matches.
    dir.write("dep/flake.nix", "{ outputs = inputs: { answer = 99; }; }");
    assert_eq!(
        flake.lock_status().expect("lock_status"),
        LockStatus::Stale,
        "a lock whose pinned content changed is Stale"
    );
}

// A single-input flake (the `lock_status` stale fixtures redeclare it with more
// inputs to drive the declared-set mismatch).
const CONSUMER_ONE_INPUT_FLAKE: &str = r#"{
  inputs = { dep = { url = "./dep"; }; };
  outputs = { dep, ... }: { consumes = dep.answer; };
}"#;

// A flake with no `inputs` attribute declares no inputs (an empty set), not an
// error: `outputs`-only flakes are well-formed.
#[test]
fn inputs_absent_is_empty() {
    let dir = TempDir::new();
    dir.write("flake.nix", SHALLOW_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    let inputs = flake.inputs().expect("inputs");
    assert!(
        inputs.entries().is_empty(),
        "a flake with no `inputs` attr declares no inputs"
    );
    let _: &FlakeInputs = &inputs;
}

// A non-local url scheme (`github:`, `path:`, …) is rejected: our flakes resolve
// only local paths (lib.rs:5), so a remote/registry ref is out of design, not a
// silently accepted input.
const REMOTE_INPUT_FLAKE: &str = r#"{
  inputs = { nixpkgs = { url = "github:NixOS/nixpkgs"; }; };
  outputs = inputs: { answer = 1; };
}"#;

#[test]
fn inputs_rejects_a_non_local_url() {
    let dir = TempDir::new();
    dir.write("flake.nix", REMOTE_INPUT_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    match flake.inputs() {
        Err(FlakeError::NotAFlake(_)) => {}
        other => panic!("expected NotAFlake for a non-local input url, got {other:?}"),
    }
}

// A dynamic (`${...}`) url cannot be enumerated statically and must never be
// fabricated into a partial string (mirrors the dynamic-output-key guard).
const DYNAMIC_URL_FLAKE: &str = r#"{
  inputs = { dep = { url = "./${sys}"; }; };
  outputs = inputs: { answer = 1; };
}"#;

#[test]
fn inputs_rejects_a_dynamic_url() {
    let dir = TempDir::new();
    dir.write("flake.nix", DYNAMIC_URL_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    match flake.inputs() {
        Err(FlakeError::Parse(_)) => {}
        other => panic!("expected Parse for a dynamic input url, got {other:?}"),
    }
}

// An input entry without a `url` is malformed: report it rather than drop the
// input or fabricate a path.
const NO_URL_FLAKE: &str = r#"{
  inputs = { dep = { rev = "abc"; }; };
  outputs = inputs: { answer = 1; };
}"#;

#[test]
fn inputs_rejects_an_entry_without_a_url() {
    let dir = TempDir::new();
    dir.write("flake.nix", NO_URL_FLAKE);
    let flake = Flake::load(&dir.path).expect("load");
    match flake.inputs() {
        Err(FlakeError::NotAFlake(_)) => {}
        other => panic!("expected NotAFlake for an input without a url, got {other:?}"),
    }
}
