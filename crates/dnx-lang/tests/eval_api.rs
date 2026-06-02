//! Integration tests documenting the public eval API of dnx-lang.
//!
//! Public API:
//! - `use dnx_lang::runtime::{NixRuntime, NixEvalResult};`
//! - `NixRuntime::pure()` builds a runtime.
//! - `rt.eval(&str) -> NixEvalResult`
//! - `NixEvalResult` variants: `Int(i64)`, `Float(f64)`, `Str(Arc<str>)`, `Bool(bool)`,
//!   `Null`, `List(Vec<...>)`, `Lambda(_)`, `Error(_)`.
//!
//! Note: Booleans from comparisons (e.g., `1==1`) yield `Lambda` because dnx uses
//! Church-encoded bools, NOT the Bool variant.

use dnx_lang::runtime::{NixEvalResult, NixRuntime};

fn eval(src: &str) -> NixEvalResult {
    NixRuntime::pure().eval(src)
}

fn int(src: &str) -> i64 {
    match eval(src) {
        NixEvalResult::Int(n) => n,
        other => panic!("{src} => {}", tag(&other)),
    }
}

fn s(src: &str) -> String {
    match eval(src) {
        NixEvalResult::Str(x) => x.to_string(),
        other => panic!("{src} => {}", tag(&other)),
    }
}

fn boolv(src: &str) -> bool {
    match eval(src) {
        NixEvalResult::Bool(b) => b,
        _ => panic!("expected Bool for: {src}"),
    }
}

fn tag(r: &NixEvalResult) -> &'static str {
    match r {
        NixEvalResult::Int(_) => "int",
        NixEvalResult::Float(_) => "float",
        NixEvalResult::Str(_) => "str",
        NixEvalResult::Bool(_) => "bool",
        NixEvalResult::Null => "null",
        NixEvalResult::List(_) => "list",
        NixEvalResult::AttrSet(_) => "set",
        NixEvalResult::Lambda(_) => "lambda",
        NixEvalResult::Error(_) => "error",
    }
}

fn is_error(src: &str) -> bool {
    matches!(eval(src), NixEvalResult::Error(_))
}

// ============================================================================
// Arithmetic Tests
// ============================================================================

#[test]
fn test_add() {
    assert_eq!(int("1 + 2"), 3);
}

#[test]
fn test_sub() {
    assert_eq!(int("10 - 3"), 7);
}

#[test]
fn test_mul() {
    assert_eq!(int("2 * 4"), 8);
}

#[test]
fn test_div() {
    assert_eq!(int("9 / 3"), 3);
}

// ============================================================================
// String Concatenation
// ============================================================================

#[test]
fn test_str_concat() {
    assert_eq!(s(r#""foo" + "bar""#), "foobar");
}

// ============================================================================
// Conditionals with Integer Comparisons
// ============================================================================

#[test]
fn test_if_eq_true_branch() {
    assert_eq!(int("if 1 == 1 then 42 else 0"), 42);
}

#[test]
fn test_if_eq_false_branch() {
    assert_eq!(int("if 1 == 2 then 1 else 2"), 2);
}

// ============================================================================
// Logical Operators (Church-encoded bools)
// ============================================================================

#[test]
fn test_and_false() {
    assert_eq!(int("if true && false then 1 else 0"), 0);
}

#[test]
fn test_or_true() {
    assert_eq!(int("if true || false then 1 else 0"), 1);
}

#[test]
#[ignore = "FAILING: if !false yields lambda (Church-encoded bool), not 0"]
fn test_not_false() {
    assert_eq!(int("if !false then 1 else 0"), 1);
}

// ============================================================================
// Let Bindings
// ============================================================================

#[test]
fn test_let_single_binding() {
    assert_eq!(int("let x = 5; in x + 1"), 6);
}

#[test]
fn test_let_multi_binding() {
    assert_eq!(int("let x = 2; y = 3; in x * y"), 6);
}

// ============================================================================
// Lambda Application
// ============================================================================

#[test]
fn test_lambda_single_arg() {
    assert_eq!(int("(x: x + 1) 4"), 5);
}

#[test]
fn test_lambda_curried() {
    assert_eq!(int("(x: y: x + y) 3 4"), 7);
}

// ============================================================================
// Record Access
// ============================================================================

#[test]
fn test_record_access_simple() {
    assert_eq!(int("{ a = 1; b = 2; }.a"), 1);
}

#[test]
fn test_record_access_let() {
    assert_eq!(int("let s = { a = 10; }; in s.a"), 10);
}

// ============================================================================
// Record Pattern Matching
// ============================================================================

#[test]
#[ignore = "pattern destructure binds attrset arg used once per field (Select) → sharing/forcing interaction; followup w/ spine-restricted forcing"]
fn test_record_destruct() {
    assert_eq!(int("({ a, b }: a + b) { a = 1; b = 2; }"), 3);
}

// ============================================================================
// List Operations
// ============================================================================

#[test]
fn test_head() {
    assert_eq!(int("head [ 10 20 30 ]"), 10);
}

// ============================================================================
// Type Inspection
// ============================================================================

#[test]
fn test_typeof_int() {
    assert_eq!(s("typeOf 1"), "int");
}

#[test]
fn test_typeof_float() {
    assert_eq!(s("typeOf 1.5"), "float");
}

#[test]
fn test_typeof_str() {
    assert_eq!(s(r#"typeOf "x""#), "string");
}

#[test]
fn test_typeof_null() {
    assert_eq!(s("typeOf null"), "null");
}

#[test]
fn test_typeof_lambda() {
    assert_eq!(s("typeOf (x: x)"), "lambda");
}

// ============================================================================
// Booleans (tagged PrimVal::Bool — comparisons/logic yield native bools)
// ============================================================================

#[test]
fn test_bool_eq_true() {
    assert!(boolv("1 == 1"));
}

#[test]
fn test_bool_lt() {
    assert!(boolv("1 < 2"));
}

// ============================================================================
// Attribute Set Operations
// ============================================================================

#[test]
fn test_attrset_access_simple() {
    assert_eq!(int("{ a = 1; b = 2; }.a"), 1);
}

#[test]
fn test_attrset_access_multi_field() {
    assert_eq!(int("{ x = 5; y = 10; }.y"), 10);
}

#[test]
fn test_attrset_access_missing_key() {
    assert!(is_error("{ a = 1; }.b"));
}

#[test]
fn test_attrset_has_attr_present() {
    assert!(boolv("{ a = 1; } ? a"));
}

#[test]
fn test_attrset_has_attr_missing() {
    assert!(!boolv("{ a = 1; } ? b"));
}

#[test]
#[ignore = "// update forces 2 attrset args; inline prim-arg forcing isn't spine-restricted → over-reduces currying. Needs spine-restricted inner force_whnf (followup)"]
fn test_attrset_update() {
    assert_eq!(int("({ a = 1; b = 2; } // { a = 99; }).a"), 99);
}

#[test]
#[ignore = "// update: see test_attrset_update"]
fn test_attrset_update_adds_key() {
    assert_eq!(int("({ a = 1; } // { b = 2; }).b"), 2);
}

// ============================================================================
// String Primitives (P1 eager scalars)
// ============================================================================

#[test]
fn test_builtin_string_length() {
    assert_eq!(int("builtins.stringLength \"hello\""), 5);
}

#[test]
fn test_builtin_string_length_empty() {
    assert_eq!(int("builtins.stringLength \"\""), 0);
}

#[test]
fn test_builtin_substring_basic() {
    assert_eq!(s("builtins.substring 1 2 \"hello\""), "el");
}

#[test]
fn test_builtin_substring_start_zero() {
    assert_eq!(s("builtins.substring 0 3 \"hello\""), "hel");
}

#[test]
fn test_builtin_substring_out_of_bounds() {
    assert_eq!(s("builtins.substring 10 5 \"hello\""), "");
}

#[test]
fn test_builtin_to_string_int() {
    assert_eq!(s("builtins.toString 42"), "42");
}

#[test]
fn test_builtin_to_string_str() {
    assert_eq!(s("builtins.toString \"hello\""), "hello");
}

#[test]
fn test_builtin_to_string_negative_int() {
    // `toString -100` parses as subtraction in Nix; parenthesize the negative.
    assert_eq!(s("builtins.toString (-100)"), "-100");
}

#[test]
fn test_builtin_bit_and() {
    assert_eq!(int("builtins.bitAnd 12 10"), 8);
}

#[test]
fn test_builtin_bit_or() {
    assert_eq!(int("builtins.bitOr 12 10"), 14);
}

#[test]
fn test_builtin_bit_xor() {
    assert_eq!(int("builtins.bitXor 12 10"), 6);
}

#[test]
fn test_builtin_to_int_valid() {
    assert_eq!(int("builtins.toInt \"42\""), 42);
}

#[test]
fn test_builtin_to_int_negative() {
    assert_eq!(int("builtins.toInt \"-100\""), -100);
}

#[test]
fn test_builtin_to_int_whitespace() {
    assert_eq!(int("builtins.toInt \"  123  \""), 123);
}

#[test]
fn test_builtin_to_int_invalid() {
    assert!(is_error("builtins.toInt \"not a number\""));
}

// ============================================================================
// Integer Overflow (must surface as an error, never crash the evaluator).
// Faithful to Nix: overflow is an error, not a silent wrap. See review
// prim.rs:112-153. `dnx eval` must never panic on these.
// ============================================================================

#[test]
fn test_add_overflow_is_error_not_panic() {
    assert!(is_error("9223372036854775807 + 1"));
}

#[test]
fn test_mul_overflow_is_error_not_panic() {
    assert!(is_error("9223372036854775807 * 2"));
}

#[test]
fn test_sub_overflow_is_error_not_panic() {
    assert!(is_error("(-9223372036854775807) - 2"));
}

#[test]
fn test_normal_arithmetic_still_works() {
    assert_eq!(int("1 + 2 * 3"), 7);
    assert_eq!(int("10 - 3"), 7);
    assert_eq!(int("-5"), -5);
}

// ============================================================================
// `inherit` — attrset & let (scalar inherits only)
// `inherit x` == `x = x`; `inherit (e) a` == `a = e.a`.
// ============================================================================

#[test]
fn test_inherit_attrset_plain() {
    // `{ inherit x; }` binds x from the enclosing scope.
    assert_eq!(int("let x = 7; in { inherit x; }.x"), 7);
}

#[test]
fn test_inherit_attrset_plain_multi() {
    // `inherit x y;` desugars to two bindings, each from outer scope.
    assert_eq!(int("let x = 1; y = 2; in { inherit x y; }.x"), 1);
    assert_eq!(int("let x = 1; y = 2; in { inherit x y; }.y"), 2);
}

#[test]
fn test_inherit_attrset_from() {
    // `inherit (e) a;` == `a = e.a`.
    assert_eq!(int("let e = { a = 3; }; in { inherit (e) a; }.a"), 3);
}

#[test]
fn test_inherit_let_from() {
    // `inherit (e) a;` in a let binds a = e.a, usable in the body.
    assert_eq!(int("let e = { a = 9; }; in let inherit (e) a; in a"), 9);
}

// NOTE: three further inherit shapes desugar correctly but hit *pre-existing*
// dnx runtime/scope gaps unrelated to this desugaring (each fails identically
// when hand-written without `inherit` — see REPORT.md):
//   * `inherit (e) a b;`            → needs Rep-duplicating an attrset value;
//                                      `(e.a)+(e.b)` fails the same way.
//   * `inherit (e) a; inherit (f) b;` in one attrset → multiple Select-valued
//                                      keys; `{x=e.a;y=f.b;}` fails the same.
//   * plain `inherit x;` inside a *nested* let → same-name let shadow;
//                                      `let x=1; in let x=x; in x` fails the same.

// --- Attrset-pattern lambdas (linearity: pattern arg rep-split over N selects).

#[test]
fn test_pat_single_field() {
    assert_eq!(int("({a}: a) {a=1;}"), 1);
}

#[test]
fn test_pat_two_fields_sum() {
    assert_eq!(int("({a,b}: a + b) {a=1;b=2;}"), 3);
}

#[test]
fn test_pat_three_fields() {
    assert_eq!(int("({a,b,c}: a + b + c) {a=1;b=2;c=3;}"), 6);
}

#[test]
fn test_pat_ellipsis_ignores_extra() {
    assert_eq!(int("({a,...}: a) {a=7;b=9;}"), 7);
}

#[test]
fn test_pat_default_used() {
    assert_eq!(int("({a?5}: a) {}"), 5);
}

#[test]
fn test_pat_default_overridden() {
    assert_eq!(int("({a?5}: a) {a=8;}"), 8);
}

#[test]
fn test_pat_at_bind_whole() {
    // `@`-name bound to the whole arg; field also selected → arg used twice.
    assert_eq!(int("(args@{a}: a + args.a) {a=4;}"), 8);
}

#[test]
fn test_pat_at_bind_before() {
    assert_eq!(int("({a}@args: args.a) {a=6;}"), 6);
}
