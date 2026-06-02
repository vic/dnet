//! RECURSION ORACLE — the objective judge for the fix-recursion work.
//!
//! Δ-Nets reduces λ-Y recursion natively (main.tex: 3 agents fan/eraser/replicator,
//! no Book). Normal-order reduction does NOT reduce discarded args (main.tex:252);
//! garbage under an eraser is ignored by readback, never fired. The bug being fixed:
//! `normalize_demand`'s blind frontier drain fires the OFF-SPINE discarded
//! recursive-unfold replicators (r7 distinct-level replicate → level climb →
//! `LO path depth exceeded`). Fix = reachable-from-root normalization only.
//!
//! These assert the CORRECT (paper) result. Cases marked RED currently fail
//! (climb → Error) and must go green WITHOUT regressing the converging cases.

use dnx_lang::runtime::{NixEvalResult, NixRuntime};

fn int(src: &str) -> i64 {
    match NixRuntime::pure().eval(src) {
        NixEvalResult::Int(n) => n,
        NixEvalResult::Error(_) => panic!("{src} => Error (expected Int)"),
        _ => panic!("{src} => non-Int (expected Int)"),
    }
}

// --- ROOT (non-recursive!): applying a function used 2+ times. Recursion fails
// because it shares the recursive function via a Rep and applies it; this is the
// SAME bug with no fix/recursion. After r5 replicates the shared λ, its bound var
// sits behind a REP_OUT the demand walker can't force through. Fix this → recursion
// follows. main.tex:957 (fan-rep commutation) + :954 (canonical reps = fan-ins). ---
#[test]
fn apply_function_used_once() {
    assert_eq!(int("(g: g 0) (x: x + 1)"), 1); // control: used once, works today
}
#[test]
fn apply_shared_function_nested() {
    assert_eq!(int("(g: g (g 0)) (x: x + 1)"), 2); // used 2x + applied — RED
}
#[test]
fn apply_shared_function_twice() {
    assert_eq!(int("(g: (g 0) + (g 1)) (x: x + 1)"), 3); // used 2x, applied 2x — RED
}

// --- baseline: already green (no fix wrapper, or fix body self-contained) ---
#[test]
fn baseline_no_fix_prim() {
    assert_eq!(int("(n: n + 1) 3"), 4);
}
#[test]
fn fix_const_body() {
    assert_eq!(int("fix (self: 0)"), 0); // self unused → Era
    assert_eq!(int("fix (self: 0 + 1)"), 1); // prim on consts
    assert_eq!(int("fix (self: (y: 1) 2)"), 1); // discard, no prim-on-bound-var
}
#[test]
fn fix_identity_applied() {
    assert_eq!(int("(fix (self: n: n)) 3"), 3); // bound var returned direct
}
#[test]
fn fix_const_condition() {
    assert_eq!(int("(fix (self: n: if true then 9 else 8)) 3"), 9);
}

// --- RED: prim forces a fix-bound var → off-spine unfold climbs today ---
#[test]
fn fix_prim_on_bound_var_succ() {
    // self UNUSED; semantically (λn.n+1) 3 = 4. Today: LO path depth exceeded.
    assert_eq!(int("(fix (self: n: n + 1)) 3"), 4);
}
#[test]
fn fix_prim_on_bound_var_add_left() {
    assert_eq!(int("(fix (self: n: 0 + n)) 3"), 3);
}
#[test]
fn fix_if_forces_bound_var_then() {
    assert_eq!(int("(fix (self: n: if n == 0 then 9 else 8)) 0"), 9);
}
#[test]
fn fix_if_forces_bound_var_else() {
    assert_eq!(int("(fix (self: n: if n == 0 then 9 else 8)) 3"), 8);
}

// --- RED: GENUINE recursion (self USED) — the real goal ---
#[test]
fn countdown_terminates() {
    // self used in the recursive call; base case returns 0; if erases the dead branch.
    assert_eq!(
        int("(fix (self: n: if n == 0 then 0 else self (n - 1))) 3"),
        0
    );
    assert_eq!(
        int("(fix (self: n: if n == 0 then 0 else self (n - 1))) 10"),
        0
    );
}
#[test]
fn sum_to_n() {
    // accumulating recursion: sum 0..n. tests the recursive value actually flows.
    assert_eq!(
        int("(fix (self: n: if n == 0 then 0 else n + self (n - 1))) 3"),
        6,
    );
}
