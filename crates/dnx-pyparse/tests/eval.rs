//! Oracle: the minimal Python surface evaluates on the same Dnx core as Nix.
//! The headline test (`py_derivation_equals_nix_derivation`) shows a Python
//! `derivation(...)` and a Nix `derivationStrict {...}` reduce to the identical
//! derivation attrset — one substrate, two languages.

use dnx_lang::runtime::{NixEvalError, NixEvalResult, NixRuntime};
use dnx_pyparse::PyRuntime;

fn py(src: &str) -> NixEvalResult {
    PyRuntime::pure().eval(src)
}

fn nix(src: &str) -> NixEvalResult {
    NixRuntime::pure().eval(src)
}

fn expect_int(r: NixEvalResult, n: i64) {
    match r {
        NixEvalResult::Int(got) => assert_eq!(got, n, "expected Int({n})"),
        other => panic!("expected Int({n}), got {}", tag(&other)),
    }
}

fn tag(r: &NixEvalResult) -> String {
    match r {
        NixEvalResult::Int(n) => format!("Int({n})"),
        NixEvalResult::Float(f) => format!("Float({f})"),
        NixEvalResult::Str(s) => format!("Str({s:?})"),
        NixEvalResult::Bool(b) => format!("Bool({b})"),
        NixEvalResult::Null => "Null".into(),
        NixEvalResult::List(_) => "List".into(),
        NixEvalResult::AttrSet(_) => "AttrSet".into(),
        NixEvalResult::Lambda(_) => "Lambda".into(),
        NixEvalResult::Error(e) => format!("Error({e:?})"),
    }
}

#[test]
fn arithmetic_precedence() {
    // 1 + 2 * 3 == 7 (multiplication binds tighter).
    expect_int(py("1 + 2 * 3"), 7);
}

#[test]
fn lambda_applied() {
    expect_int(py("(lambda x: x + 1)(41)"), 42);
}

#[test]
fn def_then_call() {
    expect_int(py("def double(x): return x * 2\ndouble(21)"), 42);
}

#[test]
fn ternary_true_branch() {
    // Python ternary: `<then> if <cond> else <else>`.
    expect_int(py("10 if 1 < 2 else 0"), 10);
}

#[test]
fn ternary_false_branch() {
    expect_int(py("99 if 1 > 2 else 42"), 42);
}

#[test]
fn comparison_chain_matches_nix_conjunction() {
    // Python chains comparisons: `a < b < c` means `(a < b) and (b < c)`, NOT
    // the left-folded `(a < b) < c`. Nix has no chaining, so the oracle is the
    // explicit conjunction `(a < b) && (b < c)` — both lower to the same core.
    match (py("1 < 2 < 3"), nix("(1 < 2) && (2 < 3)")) {
        (NixEvalResult::Bool(p), NixEvalResult::Bool(n)) => {
            assert!(p && n, "1 < 2 < 3 must be true on both frontends")
        }
        (p, n) => panic!("chain true: py {} vs nix {}", tag(&p), tag(&n)),
    }
    // A broken middle link makes the whole chain false (left-fold would wrongly
    // compare a Bool to 2 and not model Python at all).
    match (py("1 < 3 < 2"), nix("(1 < 3) && (3 < 2)")) {
        (NixEvalResult::Bool(p), NixEvalResult::Bool(n)) => {
            assert!(!p && !n, "1 < 3 < 2 must be false on both frontends")
        }
        (p, n) => panic!("chain false: py {} vs nix {}", tag(&p), tag(&n)),
    }
}

#[test]
fn comparison_is_bool() {
    match py("1 == 1") {
        NixEvalResult::Bool(true) => {}
        other => panic!("expected Bool(true), got {}", tag(&other)),
    }
}

#[test]
fn boolean_and_or_not() {
    match py("not (1 == 2)") {
        NixEvalResult::Bool(true) => {}
        other => panic!("expected Bool(true), got {}", tag(&other)),
    }
    match py("(1 == 1) and (2 == 2)") {
        NixEvalResult::Bool(true) => {}
        other => panic!("expected Bool(true) for and, got {}", tag(&other)),
    }
}

#[test]
fn string_concat() {
    match py(r#""foo" + "bar""#) {
        NixEvalResult::Str(s) if s.as_ref() == "foobar" => {}
        other => panic!("expected Str(foobar), got {}", tag(&other)),
    }
}

#[test]
fn list_evaluates_like_nix() {
    // A list is a Scott-encoded term; the same `dnx-read::read_value` recognizer
    // reconstructs it structurally on both frontends, so `[1, 2, 3]` reads back as
    // the identical `List` value either way — one substrate, two languages.
    match (py("[1, 2, 3]"), nix("[1 2 3]")) {
        (NixEvalResult::List(p), NixEvalResult::List(n)) => assert_eq!(p, n, "same list"),
        (p, n) => panic!("py list {} vs nix list {}", tag(&p), tag(&n)),
    }
}

#[test]
fn list_concat_matches_nix_plusplus() {
    // Python overloads `+`: two list literals concatenate. It lowers to the SAME
    // prelude `concat` that Nix `++` uses (lower.rs `lower_binop`, literals.rs:142),
    // so `[1,2]+[3]` and `[1 2]++[3]` take the identical path on the shared core —
    // one substrate, two surfaces. Both currently terminate in the SAME
    // `ReadbackIncomplete`: the shared Scott-recursion driver gate that blocks
    // every `fix`-based prelude op (`map`/`length`/`concat`) on BOTH frontends —
    // see MEMORY recursion-applied-fix-diverge; that driver is out of this crate.
    // The oracle pins frontend AGREEMENT (same lowering, same gate), independent of
    // the driver. When the driver lands, this becomes a `List([1,2,3])` equality.
    match (py("[1,2]+[3]"), nix("[1 2]++[3]")) {
        (
            NixEvalResult::Error(NixEvalError::Elaborate(a)),
            NixEvalResult::Error(NixEvalError::Elaborate(b)),
        ) => assert_eq!(
            a.to_string(),
            b.to_string(),
            "py `+` and nix `++` must hit the identical core path"
        ),
        (p, n) => panic!("py `[1,2]+[3]` {} vs nix `[1 2]++[3]` {}", tag(&p), tag(&n)),
    }
}

#[test]
fn scalar_plus_still_adds() {
    // The list dispatch must not regress scalar `+`: int adds, string concatenates.
    expect_int(py("1 + 2"), 3);
    match py(r#""foo" + "bar""#) {
        NixEvalResult::Str(s) if s.as_ref() == "foobar" => {}
        other => panic!("expected Str(foobar), got {}", tag(&other)),
    }
}

#[test]
fn fstring_matches_nix_interpolation() {
    // A Python f-string `f"a{e}b"` desugars to the SAME core a Nix interpolated
    // string `"a${e}b"` does: `Add(Add("a", toString e), "b")` (mirrors
    // dnx-lang literals.rs:24-54). Both frontends take the identical path, so the
    // produced string is byte-identical — one substrate, two surfaces.
    match (
        py(r#"x = 5
f"n={x}!""#),
        nix(r#"let x = 5; in "n=${x}!""#),
    ) {
        (NixEvalResult::Str(p), NixEvalResult::Str(n)) => {
            assert_eq!(p.as_ref(), "n=5!", "py f-string value");
            assert_eq!(p, n, "py f-string must equal nix interpolation");
        }
        (p, n) => panic!("py {} vs nix {}", tag(&p), tag(&n)),
    }
}

#[test]
fn fstring_coerces_and_concats_literals() {
    // Leading/trailing literals around a hole, and a non-string hole coerced via
    // toString — exactly Nix interpolation semantics.
    match py("f\"{1 + 2} apples\"") {
        NixEvalResult::Str(s) if s.as_ref() == "3 apples" => {}
        other => panic!("expected Str(\"3 apples\"), got {}", tag(&other)),
    }
}

#[test]
fn fstring_no_holes_is_plain_string() {
    match (py(r#"f"plain""#), nix(r#""plain""#)) {
        (NixEvalResult::Str(p), NixEvalResult::Str(n)) => assert_eq!(p, n),
        (p, n) => panic!("py {} vs nix {}", tag(&p), tag(&n)),
    }
}

#[test]
fn dict_attr_access() {
    // Dict access via subscript and attribute both lower to `Select`.
    expect_int(py(r#"{"a": 1, "b": 2}["b"]"#), 2);
}

#[test]
fn membership_in_matches_nix_has_attr() {
    // Python `k in d` is membership; it lowers to the same `hasAttr` primop as
    // Nix `d ? k`, so both frontends agree on present and absent keys.
    let present = (py(r#""a" in {"a": 1}"#), nix(r#"{ a = 1; } ? a"#));
    match present {
        (NixEvalResult::Bool(true), NixEvalResult::Bool(true)) => {}
        (p, n) => panic!("present: py {} vs nix {}", tag(&p), tag(&n)),
    }
    let absent = (py(r#""z" in {"a": 1}"#), nix(r#"{ a = 1; } ? z"#));
    match absent {
        (NixEvalResult::Bool(false), NixEvalResult::Bool(false)) => {}
        (p, n) => panic!("absent: py {} vs nix {}", tag(&p), tag(&n)),
    }
}

#[test]
fn assignment_then_use() {
    expect_int(py("x = 5\nx + x"), 10);
}

#[test]
fn float_literal() {
    match py("typeOf(1.5)") {
        NixEvalResult::Str(s) if s.as_ref() == "float" => {}
        other => panic!("expected Str(float), got {}", tag(&other)),
    }
}

/// Headline demo: a Python `derivation(...)` and the equivalent Nix
/// `derivationStrict {...}` produce the SAME derivation attrset, because both
/// frontends lower to the same core and apply the same `derivationStrict`
/// primop. `conv_eq` on the normal-form values witnesses the equality.
#[test]
fn py_derivation_equals_nix_derivation() {
    let p = py(r#"derivation(name="hi", builder="/bin/sh", system="x86_64-linux")"#);
    let n =
        nix(r#"derivationStrict { name = "hi"; builder = "/bin/sh"; system = "x86_64-linux"; }"#);
    // Both are attrsets with the same keys/values (type/name/builder/system).
    match (&p, &n) {
        (NixEvalResult::AttrSet(_), NixEvalResult::AttrSet(_)) => {}
        _ => panic!("py {} vs nix {}", tag(&p), tag(&n)),
    }
    assert!(
        p.conv_eq(&n),
        "python derivation must equal nix derivation (same core, same drv)"
    );
}

#[test]
fn py_derivation_is_marked_derivation() {
    match py(r#"derivation(name="hi", builder="/bin/sh").type"#) {
        NixEvalResult::Str(s) if s.as_ref() == "derivation" => {}
        other => panic!("expected type=\"derivation\", got {}", tag(&other)),
    }
}

#[test]
fn py_derivation_field_select() {
    match py(r#"derivation(name="hi", builder="/bin/sh")["name"]"#) {
        NixEvalResult::Str(s) if s.as_ref() == "hi" => {}
        other => panic!("expected Str(hi), got {}", tag(&other)),
    }
}

/// Lift an evaluated derivation attrset to its drvPath in an isolated store.
/// `instantiate` is pure (no builder runs) and content-addressed, so the path
/// depends only on the `Derivation` value — never on the source language.
fn drv_path(r: &NixEvalResult, store: &dnx_store::Store) -> String {
    let attrs = match r {
        NixEvalResult::AttrSet(kvs) => kvs,
        other => panic!("expected a derivation attrset, got {}", tag(other)),
    };
    dnx_drv::from_attrs(attrs)
        .expect("attrset is a derivation")
        .instantiate(store)
        .expect("instantiate")
        .to_string()
}

/// The same-store-hash beat, end to end: a Python `derivation(...)` and the
/// equivalent Nix `derivationStrict {...}` instantiate to the byte-identical
/// drvPath. This extends `py_derivation_equals_nix_derivation` past attrset
/// `conv_eq` (eval.rs above) down to the store hash the demo advertises.
#[test]
fn py_drv_path_equals_nix_drv_path() {
    let tmp = std::env::temp_dir().join(format!("pyparse-drv-eq-{}", std::process::id()));
    let store = dnx_store::Store::open_at(&tmp).expect("open store");

    let p = py(r#"derivation(name="hi", builder="/bin/sh", system="x86_64-linux")"#);
    let n =
        nix(r#"derivationStrict { name = "hi"; builder = "/bin/sh"; system = "x86_64-linux"; }"#);
    let pp = drv_path(&p, &store);
    let np = drv_path(&n, &store);

    let _ = std::fs::remove_dir_all(&tmp);
    assert_eq!(
        pp, np,
        "python and nix derivations must instantiate to the same drvPath"
    );
}
