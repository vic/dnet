//! Boolean-algebra laws on the dnx-proof kernel, proved by `Bool.rec` CASE-ANALYSIS (Bool is the
//! finite two-element inductive `false | true`, so every law below is a CASE-SPLIT — an `Elim Bool`
//! per free variable — NOT an induction; there is no recursive ctor, hence no inductive hypothesis).
//!
//! Bool and its eliminator are spelled EXACTLY as the four-colour proofs spell them
//! (fourcolor_coloring.rs:88-107 the inductive, ctor 0 = `false`, ctor 1 = `true`;
//! fourcolor_coloring.rs:139-147 `not`; fourcolor_demo.rs:119-128 `and`). The three connectives are
//! `Bool`-valued, so each is a SMALL elimination into the constant motive `λ_:Bool. Bool` (the closed
//! Bool analogue of thm_filter.rs:177-181 `ite`, which is the same `Elim Bool` into a `List A` motive):
//!   not := λb.       Elim Bool (λ_.Bool) true  false b      -- minor_false=true , minor_true=false
//!   and := λa.λb.    Elim Bool (λ_.Bool) false b     a      -- if a then b    else false  (scrut a)
//!   or  := λa.λb.    Elim Bool (λ_.Bool) b     true  a      -- if a then true else b      (scrut a)
//! Spine order is ctor order (driver.rs §5): motive · minor_false · minor_true · scrutinee, so
//!   not true ι→ false , not false ι→ true ;  and true b ι→ b , and false b ι→ false ;
//!   or  true b ι→ true , or  false b ι→ b .
//!
//! THEOREMS (machine-checked by the trusted kernel `check`; the kernel is the oracle). Each is proved
//! by `Elim Bool` over the GOAL — the motive abstracts a free var to `b:Bool`; every leaf is a CLOSED
//! Bool, so both connectives ι-reduce to a ctor and the leaf closes by `refl` (DEFINITIONAL):
//!   • not_involutive : ∀b.   not (not b) = b
//!   • and_comm       : ∀a b. and a b = and b a
//!   • or_comm        : ∀a b. or  a b = or  b a
//!   • not_and        : ∀a b. not (and a b) = or (not a) (not b)   (a de Morgan law)
//!
//! NO new axioms; the only inductives are Bool and Id (propositional equality, thm_filter.rs:150-169).
//! NO-FALSE-GREEN: the WRONG law `not (not b) = not b` is REJECTED by `check`, pinned by a positive
//! control (the SAME shape against the TRUE involutive goal DOES check) so the rejection is a genuine
//! semantic mismatch, not a vacuous ill-typing. Closed-compute sanity (`not true = false`,
//! `and true false = false`) exercises the ι-driver on concrete ctors.

use dnx_proof::conv::conv;
use dnx_proof::driver::nf_tm;
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::{check, TypeError};
use dnx_proof::symbol::{ConstId, IndId};
use dnx_proof::tm::Tm;

// ── term helpers (same idioms as thm_filter.rs:44-56) ──
fn lam(dom: Tm, b: Tm) -> Tm {
    Tm::Lam(Box::new(dom), Box::new(b))
}
fn pi(dom: Tm, b: Tm) -> Tm {
    Tm::Pi(Box::new(dom), Box::new(b))
}
fn app(f: Tm, x: Tm) -> Tm {
    Tm::App(Box::new(f), Box::new(x))
}
fn apps(head: Tm, xs: &[Tm]) -> Tm {
    xs.iter().fold(head, |f, a| app(f, a.clone()))
}

const BOOL: IndId = IndId(0);
const ID: IndId = IndId(1);
const NOT: ConstId = ConstId(0);
const AND: ConstId = ConstId(1);
const OR: ConstId = ConstId(2);

// Bool = false | true   (ctor 0 = false, ctor 1 = true; fourcolor_coloring.rs:88-107).
fn bool_ind() -> Inductive {
    Inductive {
        id: BOOL,
        params: vec![],
        indices: vec![],
        sort: 0,
        ctors: vec![
            CtorDecl {
                ctor_ix: 0,
                args: vec![],
                ret_indices: vec![],
            }, // false
            CtorDecl {
                ctor_ix: 1,
                args: vec![],
                ret_indices: vec![],
            }, // true
        ],
    }
}
fn bool_ty() -> Tm {
    Tm::Ind(BOOL)
}
fn fls() -> Tm {
    Tm::Ctor(BOOL, 0)
}
fn tru() -> Tm {
    Tm::Ctor(BOOL, 1)
}

// Id : Π(A:Type₀)(a:A). A → Type₀ ; refl A a : Id A a a.   (thm_filter.rs:150-169.)
fn id_ind() -> Inductive {
    Inductive {
        id: ID,
        params: vec![Tm::Sort(0), Tm::Var(0)],
        indices: vec![Tm::Var(1)],
        sort: 0,
        ctors: vec![CtorDecl {
            ctor_ix: 0,
            args: vec![],
            ret_indices: vec![Tm::Var(0)],
        }],
    }
}
fn id_ty(a_ty: Tm, a: Tm, b: Tm) -> Tm {
    apps(Tm::Ind(ID), &[a_ty, a, b])
}
fn refl(a_ty: Tm, a: Tm) -> Tm {
    apps(Tm::Ctor(ID, 0), &[a_ty, a])
}

// ── the three connectives, each a SMALL Elim Bool into the constant `λ_:Bool. Bool` motive ──

/// not := λb. Elim Bool (λ_:Bool.Bool) true false b   (fourcolor_coloring.rs:142-147; ¬ swaps ctors).
fn not_body() -> Tm {
    let motive = lam(bool_ty(), bool_ty());
    lam(
        bool_ty(),
        apps(Tm::Elim(BOOL), &[motive, tru(), fls(), Tm::Var(0)]),
    )
}
fn not_ty() -> Tm {
    pi(bool_ty(), bool_ty()) // Bool → Bool
}
fn not_(b: Tm) -> Tm {
    app(Tm::Const(NOT), b)
}

/// and := λa.λb. Elim Bool (λ_:Bool.Bool) false b a   (fourcolor_demo.rs:121-128; if a then b else false).
fn and_body() -> Tm {
    let motive = lam(bool_ty(), bool_ty());
    let elim = apps(
        Tm::Elim(BOOL),
        &[motive, fls(), Tm::Var(0), Tm::Var(1)], // minor_false=false, minor_true=b, scrut=a
    );
    lam(bool_ty(), lam(bool_ty(), elim))
}
fn and_ty() -> Tm {
    pi(bool_ty(), pi(bool_ty(), bool_ty())) // Bool → Bool → Bool
}
fn and_(a: Tm, b: Tm) -> Tm {
    apps(Tm::Const(AND), &[a, b])
}

/// or := λa.λb. Elim Bool (λ_:Bool.Bool) b true a   (dual of `and`; if a then true else b).
fn or_body() -> Tm {
    let motive = lam(bool_ty(), bool_ty());
    let elim = apps(
        Tm::Elim(BOOL),
        &[motive, Tm::Var(0), tru(), Tm::Var(1)], // minor_false=b, minor_true=true, scrut=a
    );
    lam(bool_ty(), lam(bool_ty(), elim))
}
fn or_ty() -> Tm {
    pi(bool_ty(), pi(bool_ty(), bool_ty())) // Bool → Bool → Bool
}
fn or_(a: Tm, b: Tm) -> Tm {
    apps(Tm::Const(OR), &[a, b])
}

fn env() -> dnx_proof::env::GlobalEnv {
    let mut e = dnx_proof::env::GlobalEnv::default();
    e.add_inductive(bool_ind()).expect("Bool admits");
    e.add_inductive(id_ind()).expect("Id admits");
    e.add_const(NOT, not_ty(), not_body())
        .expect("not admits (δ-acyclic)");
    e.add_const(AND, and_ty(), and_body())
        .expect("and admits (δ-acyclic)");
    e.add_const(OR, or_ty(), or_body())
        .expect("or admits (δ-acyclic)");
    e
}

#[test]
fn connectives_well_typed() {
    // ADMISSION GATE: `add_const` only checks δ-acyclicity (env.rs), NOT the body's type — so we
    // check HERE that each connective genuinely inhabits its declared `Bool[→Bool]→Bool` type
    // (the `Elim Bool` into the constant `λ_:Bool. Bool` motive is well-formed small elimination).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &not_body(), &not_ty()).is_ok(),
        "not_body : Bool → Bool"
    );
    assert!(
        check(&env, &Vec::new(), &and_body(), &and_ty()).is_ok(),
        "and_body : Bool → Bool → Bool"
    );
    assert!(
        check(&env, &Vec::new(), &or_body(), &or_ty()).is_ok(),
        "or_body : Bool → Bool → Bool"
    );
}

#[test]
fn connectives_compute_closed() {
    // Closed-compute sanity: the ι-driver fires on concrete ctors.
    let env = env();
    let ctx = Vec::new();
    // not true ι→ false ; not false ι→ true.
    assert_eq!(nf_tm(&env, &ctx, &not_(tru())), nf_tm(&env, &ctx, &fls()));
    assert_eq!(nf_tm(&env, &ctx, &not_(fls())), nf_tm(&env, &ctx, &tru()));
    // and true false ι→ false ; and true true ι→ true.
    assert_eq!(
        nf_tm(&env, &ctx, &and_(tru(), fls())),
        nf_tm(&env, &ctx, &fls())
    );
    assert_eq!(
        nf_tm(&env, &ctx, &and_(tru(), tru())),
        nf_tm(&env, &ctx, &tru())
    );
    // or false false ι→ false ; or false true ι→ true.
    assert_eq!(
        nf_tm(&env, &ctx, &or_(fls(), fls())),
        nf_tm(&env, &ctx, &fls())
    );
    assert_eq!(
        nf_tm(&env, &ctx, &or_(fls(), tru())),
        nf_tm(&env, &ctx, &tru())
    );
    // conv cross-check on one closed case (driver + conv agree).
    assert!(
        conv(&env, &ctx, &and_(tru(), fls()), &fls()).unwrap(),
        "and true false ≡ false"
    );
    // no-false-green at the compute level: and true false is NOT true.
    assert!(
        !conv(&env, &ctx, &and_(tru(), fls()), &tru()).unwrap(),
        "and true false ≢ true"
    );
}

// ════════════════════════ not_involutive — ∀b. not (not b) = b ════════════════════════

/// not_involutive := λb. Elim Bool (λb'. Id Bool (not (not b')) b') (refl Bool false)(refl Bool true) b
/// Case-split on b. b=false: not(not false) ι→ not true ι→ false ⇒ refl Bool false.
///                b=true : not(not true ) ι→ not false ι→ true  ⇒ refl Bool true.
fn not_involutive() -> Tm {
    // motive λb'. Id Bool (not (not b')) b'   (ctx [b,b']: b'=Var0).
    let motive = lam(
        bool_ty(),
        id_ty(bool_ty(), not_(not_(Tm::Var(0))), Tm::Var(0)),
    );
    lam(
        bool_ty(), // b : Bool
        apps(
            Tm::Elim(BOOL),
            &[
                motive,
                refl(bool_ty(), fls()), // minor_false : Id Bool (not(not false)) false ≡ Id Bool false false
                refl(bool_ty(), tru()), // minor_true  : Id Bool (not(not true )) true  ≡ Id Bool true  true
                Tm::Var(0),             // scrutinee b
            ],
        ),
    )
}
fn not_involutive_ty() -> Tm {
    // Π(b:Bool). Id Bool (not (not b)) b.
    pi(
        bool_ty(),
        id_ty(bool_ty(), not_(not_(Tm::Var(0))), Tm::Var(0)),
    )
}

#[test]
fn not_involutive_typechecks() {
    // ∀b. not (not b) = b — case-split on b; each leaf DEFINITIONAL (ι on closed Bool).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &not_involutive(), &not_involutive_ty()).is_ok(),
        "not_involutive : Π(b). Id Bool (not (not b)) b"
    );
}

#[test]
fn false_not_involutive_rejected() {
    // NO-FALSE-GREEN: the involutive witness does NOT inhabit the WRONG goal
    // `∀b. not (not b) = not b` — at b=true that demands `Id Bool true false`, uninhabited, so the
    // `refl Bool true` minor no longer fits the (wrong) motive and `check` rejects.
    let env = env();
    let bad_ty = pi(
        bool_ty(),
        id_ty(bool_ty(), not_(not_(Tm::Var(0))), not_(Tm::Var(0))), // not (not b) = not b  — WRONG
    );
    // POSITIVE CONTROL (non-vacuity): the SAME witness DOES check against the TRUE involutive goal —
    // so the rejection below is a genuine semantic mismatch, not a vacuous ill-typed term.
    assert!(
        check(&env, &Vec::new(), &not_involutive(), &not_involutive_ty()).is_ok(),
        "positive control: not_involutive DOES prove the true law"
    );
    assert_eq!(
        check(&env, &Vec::new(), &not_involutive(), &bad_ty),
        Err(TypeError::Mismatch),
        "not_involutive does NOT prove not (not b) = not b  (no false-green)"
    );
}

// ════════════════════════ and_comm — ∀a b. and a b = and b a ════════════════════════

/// and_comm := λa b. Elim Bool (λa'. Id Bool (and a' b) (and b a'))
///                     (inner-split on b at a'=false)(inner-split on b at a'=true) a
/// NESTED case-split: outer on a, inner on b. All 4 leaves are CLOSED Bool ⇒ `and` ι-reduces both
/// sides to the SAME ctor, so each leaf is `refl`.
fn and_comm() -> Tm {
    // Inner split on b, with a' FIXED to a concrete ctor `a_val`. Built in ctx [a,b] (b=Var0).
    // motive_b λb'. Id Bool (and a_val b') (and b' a_val).
    let inner = |a_val: Tm| -> Tm {
        let motive_b = lam(
            bool_ty(),
            id_ty(
                bool_ty(),
                and_(a_val.clone(), Tm::Var(0)),
                and_(Tm::Var(0), a_val.clone()),
            ),
        );
        // leaf b'=false: Id Bool (and a_val false)(and false a_val); leaf b'=true: …(and a_val true)(and true a_val).
        let leaf = |b_val: Tm| -> Tm { refl(bool_ty(), and_(a_val.clone(), b_val)) };
        apps(
            Tm::Elim(BOOL),
            &[
                motive_b,
                leaf(fls()), // minor b'=false
                leaf(tru()), // minor b'=true
                Tm::Var(0),  // scrutinee b
            ],
        )
    };
    // outer motive λa'. Id Bool (and a' b) (and b a')   (ctx [a,b,a']: b=Var1, a'=Var0).
    let motive_a = lam(
        bool_ty(),
        id_ty(
            bool_ty(),
            and_(Tm::Var(0), Tm::Var(1)),
            and_(Tm::Var(1), Tm::Var(0)),
        ),
    );
    lam(
        bool_ty(), // a
        lam(
            bool_ty(), // b
            apps(
                Tm::Elim(BOOL),
                &[
                    motive_a,
                    inner(fls()), // a'=false : Π-instantiated inner split on b
                    inner(tru()), // a'=true
                    Tm::Var(1),   // scrutinee a
                ],
            ),
        ),
    )
}
fn and_comm_ty() -> Tm {
    // Π(a b:Bool). Id Bool (and a b) (and b a).   (ctx [a,b]: a=Var1, b=Var0.)
    pi(
        bool_ty(),
        pi(
            bool_ty(),
            id_ty(
                bool_ty(),
                and_(Tm::Var(1), Tm::Var(0)),
                and_(Tm::Var(0), Tm::Var(1)),
            ),
        ),
    )
}

#[test]
fn and_comm_typechecks() {
    // ∀a b. and a b = and b a — nested case-split; all 4 leaves DEFINITIONAL.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &and_comm(), &and_comm_ty()).is_ok(),
        "and_comm : Π(a b). Id Bool (and a b) (and b a)"
    );
}

// ════════════════════════ or_comm — ∀a b. or a b = or b a ════════════════════════

/// or_comm := λa b. Elim Bool (λa'. Id Bool (or a' b) (or b a')) (inner b @ false)(inner b @ true) a.
/// Same nested case-split as `and_comm`; all 4 leaves CLOSED ⇒ `refl`.
fn or_comm() -> Tm {
    let inner = |a_val: Tm| -> Tm {
        let motive_b = lam(
            bool_ty(),
            id_ty(
                bool_ty(),
                or_(a_val.clone(), Tm::Var(0)),
                or_(Tm::Var(0), a_val.clone()),
            ),
        );
        let leaf = |b_val: Tm| -> Tm { refl(bool_ty(), or_(a_val.clone(), b_val)) };
        apps(
            Tm::Elim(BOOL),
            &[motive_b, leaf(fls()), leaf(tru()), Tm::Var(0)],
        )
    };
    let motive_a = lam(
        bool_ty(),
        id_ty(
            bool_ty(),
            or_(Tm::Var(0), Tm::Var(1)),
            or_(Tm::Var(1), Tm::Var(0)),
        ),
    );
    lam(
        bool_ty(),
        lam(
            bool_ty(),
            apps(
                Tm::Elim(BOOL),
                &[motive_a, inner(fls()), inner(tru()), Tm::Var(1)],
            ),
        ),
    )
}
fn or_comm_ty() -> Tm {
    pi(
        bool_ty(),
        pi(
            bool_ty(),
            id_ty(
                bool_ty(),
                or_(Tm::Var(1), Tm::Var(0)),
                or_(Tm::Var(0), Tm::Var(1)),
            ),
        ),
    )
}

#[test]
fn or_comm_typechecks() {
    // ∀a b. or a b = or b a — nested case-split; all 4 leaves DEFINITIONAL.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &or_comm(), &or_comm_ty()).is_ok(),
        "or_comm : Π(a b). Id Bool (or a b) (or b a)"
    );
}

// ════════════════════════ not_and (de Morgan) — ∀a b. not (and a b) = or (not a) (not b) ════════════════════════

/// not_and := λa b. Elim Bool (λa'. Id Bool (not (and a' b)) (or (not a') (not b)))
///                    (inner b @ false)(inner b @ true) a.
/// NESTED case-split; all 4 leaves CLOSED ⇒ both sides ι-reduce to the SAME ctor, leaf = `refl`.
///   a=false: LHS not(and false b) ι→ not false ι→ true ; RHS or (not false) (not b) ι→ or true (not b) ι→ true.
///   a=true : LHS not(and true  b) ι→ not b              ; RHS or (not true)  (not b) ι→ or false(not b) ι→ not b.
fn not_and() -> Tm {
    // inner split on b at fixed a_val. motive_b λb'. Id Bool (not (and a_val b')) (or (not a_val) (not b')).
    let inner = |a_val: Tm| -> Tm {
        let motive_b = lam(
            bool_ty(),
            id_ty(
                bool_ty(),
                not_(and_(a_val.clone(), Tm::Var(0))),
                or_(not_(a_val.clone()), not_(Tm::Var(0))),
            ),
        );
        let leaf = |b_val: Tm| -> Tm { refl(bool_ty(), not_(and_(a_val.clone(), b_val))) };
        apps(
            Tm::Elim(BOOL),
            &[motive_b, leaf(fls()), leaf(tru()), Tm::Var(0)],
        )
    };
    // outer motive λa'. Id Bool (not (and a' b)) (or (not a') (not b))   (ctx [a,b,a']: b=Var1, a'=Var0).
    let motive_a = lam(
        bool_ty(),
        id_ty(
            bool_ty(),
            not_(and_(Tm::Var(0), Tm::Var(1))),
            or_(not_(Tm::Var(0)), not_(Tm::Var(1))),
        ),
    );
    lam(
        bool_ty(),
        lam(
            bool_ty(),
            apps(
                Tm::Elim(BOOL),
                &[motive_a, inner(fls()), inner(tru()), Tm::Var(1)],
            ),
        ),
    )
}
fn not_and_ty() -> Tm {
    // Π(a b:Bool). Id Bool (not (and a b)) (or (not a) (not b)).   (ctx [a,b]: a=Var1, b=Var0.)
    pi(
        bool_ty(),
        pi(
            bool_ty(),
            id_ty(
                bool_ty(),
                not_(and_(Tm::Var(1), Tm::Var(0))),
                or_(not_(Tm::Var(1)), not_(Tm::Var(0))),
            ),
        ),
    )
}

#[test]
fn not_and_typechecks() {
    // de Morgan: ∀a b. not (and a b) = or (not a) (not b) — nested case-split; all 4 leaves DEFINITIONAL.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &not_and(), &not_and_ty()).is_ok(),
        "not_and : Π(a b). Id Bool (not (and a b)) (or (not a) (not b))"
    );
}

#[test]
fn false_not_and_rejected() {
    // NO-FALSE-GREEN: de Morgan does NOT hold with `or` swapped to `and` on the RHS —
    // `not (and a b) = and (not a) (not b)` FAILS at a=false (LHS true, RHS and true (not b) ι→ not b),
    // so `check` rejects. Positive control pins it to the connective swap (not a vacuous ill-typing).
    let env = env();
    let bad_ty = pi(
        bool_ty(),
        pi(
            bool_ty(),
            id_ty(
                bool_ty(),
                not_(and_(Tm::Var(1), Tm::Var(0))),
                and_(not_(Tm::Var(1)), not_(Tm::Var(0))), // and (not a)(not b)  — WRONG (should be or)
            ),
        ),
    );
    assert!(
        check(&env, &Vec::new(), &not_and(), &not_and_ty()).is_ok(),
        "positive control: not_and DOES prove the true de Morgan law"
    );
    assert_eq!(
        check(&env, &Vec::new(), &not_and(), &bad_ty),
        Err(TypeError::Mismatch),
        "not_and does NOT prove not (and a b) = and (not a)(not b)  (no false-green)"
    );
}
