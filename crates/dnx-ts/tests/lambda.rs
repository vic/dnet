//! Oracle for the hand-grammar lambda surface: a micro lambda-calculus
//! (`\x. body`, juxtaposition application, `+`, parens, ints, idents) parsed by
//! a hand lexer/parser, lowered to the shared core `Ast`, and evaluated on the
//! Dnx engine. This is the binder/variable-multiplicity path the JSON spike
//! sidesteps (JSON has no binders): a bound variable used N times must be
//! `Rep`-split (N>1) or `Era`-dropped (N=0) to stay linearity-legal
//! (dnx-lang helpers.rs:11 `wrap_uses`, replicated for the shared `Ast`).
//!
//! The decisive oracle (design §6.5, the same one the JSON spike uses) is
//! *parity with the nix front-end*: an equivalent nix lambda must lower to the
//! byte-identical `Ast` AND evaluate to the identical `NixEvalResult`. Lambda is
//! the smallest construct that forces the multiplicity machinery, so identity
//! (1 use), duplication (`x + x`, 2 uses → `Rep`) and erasure (`\x. 1`, 0 uses
//! → `Era`) each get checked against their nix equivalent.
//!
//! The whole crate is behind the `tree-sitter` feature.
#![cfg(feature = "tree-sitter")]

use dnx_lang::nix_to_expr;
use dnx_lang::runtime::{NixEvalResult, NixRuntime};
use dnx_ts::{lower_lambda_surface, TsRuntime};

fn surf(src: &str) -> NixEvalResult {
    TsRuntime::pure().eval_lambda(src)
}

fn nix(src: &str) -> NixEvalResult {
    NixRuntime::pure().eval(src)
}

/// `NixEvalResult` has no `Debug`/`PartialEq`; name the variant for assertions
/// (mirrors `tests/roundtrip.rs` `tag`).
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

fn int(r: NixEvalResult) -> i64 {
    match r {
        NixEvalResult::Int(n) => n,
        other => panic!("expected Int, got {}", tag(&other)),
    }
}

/// LOWERING PARITY (the strongest oracle): the hand-grammar lambda lowers to the
/// *byte-identical* shared `Ast` the nix front-end produces for the equivalent
/// `x: …` lambda — including the `Rep`-split variable renaming. If the two IRs
/// are equal, every downstream pass is identical by construction.
#[test]
fn lowering_matches_nix_identity() {
    let s = lower_lambda_surface(r"\x. x").expect("surface lowers");
    let n = nix_to_expr("x: x").expect("nix lowers");
    assert_eq!(s, n, "identity lambda lowers identically");
}

#[test]
fn lowering_matches_nix_duplication() {
    // `x` used twice → `Rep`-chain split (helpers.rs:19). The split-name scheme
    // (`x__0`, `x__1`) is replicated exactly, so the IRs must be equal.
    let s = lower_lambda_surface(r"\x. x + x").expect("surface lowers");
    let n = nix_to_expr("x: x + x").expect("nix lowers");
    assert_eq!(s, n, "duplicating lambda lowers identically (Rep)");
}

#[test]
fn lowering_matches_nix_erasure() {
    // `x` unused → `Era` (helpers.rs:13).
    let s = lower_lambda_surface(r"\x. 1").expect("surface lowers");
    let n = nix_to_expr("x: 1").expect("nix lowers");
    assert_eq!(s, n, "erasing lambda lowers identically (Era)");
}

/// EVAL PARITY (the mission oracle, `surface(x) == nix(equiv)`): applying each
/// lambda to an argument reduces on the shared engine to the identical scalar
/// the equivalent nix expression does.
#[test]
fn identity_applied_matches_nix() {
    assert_eq!(int(surf(r"(\x. x) 5")), int(nix("(x: x) 5")));
    assert_eq!(int(surf(r"(\x. x) 5")), 5);
}

#[test]
fn duplication_applied_matches_nix() {
    // Exercises the `Rep` path end-to-end: `5 + 5 == 10`.
    assert_eq!(int(surf(r"(\x. x + x) 5")), int(nix("(x: x + x) 5")));
    assert_eq!(int(surf(r"(\x. x + x) 5")), 10);
}

#[test]
fn erasure_applied_matches_nix() {
    // Exercises the `Era` path end-to-end: the argument is dropped.
    assert_eq!(int(surf(r"(\x. 1) 5")), int(nix("(x: 1) 5")));
    assert_eq!(int(surf(r"(\x. 1) 5")), 1);
}

/// Nested binders + shadowing: the inner `\x` shadows the outer, and both the
/// surface and nix front-ends resolve the reference to the innermost binder.
#[test]
fn nested_lambda_matches_nix() {
    assert_eq!(
        int(surf(r"(\x. (\y. x + y) 3) 4")),
        int(nix("(x: (y: x + y) 3) 4")),
    );
    assert_eq!(int(surf(r"(\x. (\y. x + y) 3) 4")), 7);
}

/// A higher-arity application chains left-associatively, exactly like nix
/// juxtaposition: `(\f. \x. f x) (\y. y + y) 6 == 12`.
#[test]
fn application_chain_matches_nix() {
    assert_eq!(
        int(surf(r"(\f. \x. f x) (\y. y + y) 6")),
        int(nix("(f: x: f x) (y: y + y) 6")),
    );
}

/// `let x = v; in body` lowers to the byte-identical `Ast` the nix front-end
/// produces for a single binding — `App(Abs(x, wrap_uses…), v)` (dnx-lang
/// binding.rs:65-71) — so the `Rep`-split body is identical too.
#[test]
fn lowering_let_matches_nix() {
    let s = lower_lambda_surface("let x = 5; in x + x").expect("surface lowers");
    let n = nix_to_expr("let x = 5; in x + x").expect("nix lowers");
    assert_eq!(s, n, "let lowers identically to nix single binding");
}

/// EVAL PARITY (mission oracle): `let x = 5; in x + x` reduces to the identical
/// scalar the equivalent nix `let` does (and to `10`, exercising the `Rep`
/// path through the let binder).
#[test]
fn let_applied_matches_nix() {
    assert_eq!(
        int(surf("let x = 5; in x + x")),
        int(nix("let x = 5; in x + x")),
    );
    assert_eq!(int(surf("let x = 5; in x + x")), 10);
}

/// A let value is itself an expression: `let y = (\z. z + z) 3; in y + 1`
/// matches nix, confirming the value position reuses the full `expr` parser.
#[test]
fn let_value_is_expr_matches_nix() {
    assert_eq!(
        int(surf(r"let y = (\z. z + z) 3; in y + 1")),
        int(nix("let y = (z: z + z) 3; in y + 1")),
    );
}

/// Malformed surface input is a typed error, not a panic.
#[test]
fn malformed_is_error() {
    assert!(lower_lambda_surface(r"\x.").is_err(), "lambda missing body");
    assert!(lower_lambda_surface(r"(1").is_err(), "unbalanced paren");
    assert!(matches!(surf(r"\x."), NixEvalResult::Error(_)));
}

/// LOWERING PARITY for the attrset literal `{ k = v; }`: the hand-grammar lowers
/// to the byte-identical `Insert`-fold over `EmptyAttrSet` the nix front-end
/// produces (dnx-lang collections.rs:38-44), so the resulting attrset value is
/// identical given identical keys/values.
#[test]
fn lowering_attrset_matches_nix() {
    let s = lower_lambda_surface("{ a = 1; b = 2; }").expect("surface lowers");
    let n = nix_to_expr("{ a = 1; b = 2; }").expect("nix lowers");
    assert_eq!(
        s, n,
        "attrset literal lowers identically to nix Insert fold"
    );
}

/// LOWERING PARITY for select `set.k`: lowers to the byte-identical
/// `App(App(Select, set), Str("k"))` the nix front-end produces
/// (dnx-lang collections.rs:202).
#[test]
fn lowering_select_matches_nix() {
    let s = lower_lambda_surface("{ a = 1; }.a").expect("surface lowers");
    let n = nix_to_expr("{ a = 1; }.a").expect("nix lowers");
    assert_eq!(s, n, "select lowers identically to nix Select prim");
}

/// EVAL PARITY (mission oracle): selecting a field of an attrset literal reduces
/// on the shared engine to the identical scalar the equivalent nix does.
#[test]
fn attrset_select_applied_matches_nix() {
    assert_eq!(
        int(surf("{ a = 1; b = 2; }.b")),
        int(nix("{ a = 1; b = 2; }.b"))
    );
    assert_eq!(int(surf("{ a = 1; b = 2; }.b")), 2);
}

/// A select's value position is itself a full expression: a field whose value is
/// an applied lambda reduces to the identical scalar nix does.
#[test]
fn attrset_field_in_expr_matches_nix() {
    assert_eq!(
        int(surf(r"{ v = (\z. z + z) 4; }.v")),
        int(nix("{ v = (z: z + z) 4; }.v"))
    );
    assert_eq!(int(surf(r"{ v = (\z. z + z) 4; }.v")), 8);
}

/// Selecting a *lambda-valued* field and applying it is identical to nix —
/// including where the shared engine cannot read the result back: the surface's
/// lowered IR is byte-identical, so it errors (or succeeds) in lockstep. This is
/// the parity oracle stated directly, independent of engine completeness.
#[test]
fn attrset_lambda_field_matches_nix() {
    assert_eq!(
        tag(&surf(r"{ f = \x. x + x; }.f 3")),
        tag(&nix("{ f = x: x + x; }.f 3")),
        "surface select-and-apply matches nix in lockstep",
    );
}

/// Select binds tighter than application and `+`, exactly like nix, so
/// `{a=1;}.a + {b=2;}.b` is `1 + 2`.
#[test]
fn select_precedence_matches_nix() {
    assert_eq!(
        int(surf("{ a = 1; }.a + { b = 2; }.b")),
        int(nix("{ a = 1; }.a + { b = 2; }.b")),
    );
}

/// Malformed attrset / select input is a typed error, not a panic.
#[test]
fn malformed_attrset_is_error() {
    assert!(
        lower_lambda_surface("{ a = 1 }").is_err(),
        "entry missing ;"
    );
    assert!(
        lower_lambda_surface("{ a = 1;").is_err(),
        "attrset missing close"
    );
    assert!(lower_lambda_surface("x.").is_err(), "select missing key");
}
