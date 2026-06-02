//! Attrset with a non-scalar value at a NON-first attr — the LOPath
//! frontier-collision class.
//!
//! Was: `{ a = 1; b = [ 2 3 ]; }` → `error: insert: first arg must be attrset`.
//! ROOT CAUSE: the App FUNCTION side was assigned the parent's bare `lo` at
//! elaboration (pass2 `Ast::App`), so two distinct live active pairs landed on one
//! `frontier1: BTreeMap<LOPath, _>` key and the inner `insert` pair was silently
//! evicted — the accumulator reified to `Lambda`.
//! FIX (Option A): App fn-side `lo.extend_left()` (mirrors arg-side
//! `extend_right`), so every elaborated sub-term gets a collision-free LOPath.
//! See vic/notes/frontier-collision-root.md + vic/settled/lopath.md.

use dnx_lang::runtime::{NixEvalResult, NixRuntime};

fn eval(src: &str) -> NixEvalResult {
    NixRuntime::pure().eval(src)
}

#[test]
fn attrset_list_value_after_scalar_is_set() {
    assert!(
        matches!(eval("{ a = 1; b = [ 2 3 ]; }"), NixEvalResult::AttrSet(_)),
        "list value at a non-first attr must yield an AttrSet, not error/Lambda"
    );
}

#[test]
fn attrset_nested_value_after_scalar_is_set() {
    assert!(
        matches!(
            eval("{ a = 1; b = { c = 2; }; }"),
            NixEvalResult::AttrSet(_)
        ),
        "nested-attrset value at a non-first attr must yield an AttrSet"
    );
}

#[test]
fn attrset_two_compound_values_is_set() {
    // Two non-scalar values in one attrset — the original mission repro.
    assert!(matches!(
        eval("{ x = { a = 1; }; y = { b = 2; }; }"),
        NixEvalResult::AttrSet(_)
    ));
}

#[test]
fn inherit_from_set_resolves_field() {
    // `inherit (s) a b;` builds a 2-compound-field attrset; `.a` must resolve.
    assert!(matches!(
        eval("let s = { a = 1; b = 2; }; in { inherit (s) a b; }.a"),
        NixEvalResult::Int(1)
    ));
}

#[test]
fn attrset_list_first_then_scalar_is_set() {
    // Control: a non-scalar value FIRST does not collide and already works.
    assert!(matches!(
        eval("{ b = [ 2 3 ]; a = 1; }"),
        NixEvalResult::AttrSet(_)
    ));
}
