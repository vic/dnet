//! Verified `Option`/`Maybe` FUNCTOR laws on the dnx-proof kernel:
//!   • omap_id   : ∀A (o:Option A). omap (λx.x) o = o                       (functor IDENTITY)
//!   • omap_comp : ∀A B C (f:B→C)(g:A→B)(o:Option A).
//!                   omap f (omap g o) = omap (λx. f (g x)) o               (functor COMPOSITION)
//!
//! `Option A = none | some (a:A)` is the parametric NON-recursive inductive (param `A`, NO indices ⇒
//! `nidx == 0`, like `List` thm_map_append.rs:76-96, but `some`'s single field `a:A` is NON-recursive
//! ⇒ the minor carries NO induction hypothesis — `minor_type` recursor.rs:73-134 only binds an `ih`
//! per field whose head IS the family, recorder.rs:78 `recs = fields filter head_is_ind`). So `omap`
//! is a CASE-ANALYSIS recursor — the `Option` analogue of `map` with the recursion erased:
//!
//!   omap := λA B f o. Option.rec A (λ_:Option A. Option B) (none B) (λa:A. some B (f a)) o
//!     ⇒  omap A B f (none A)   ι→ none B ,
//!        omap A B f (some A a) ι→ some B (f a).
//!
//! Both proofs are pure CASE-SPLITs via `Option.rec` over the GOAL (one `Elim Option`, NO `ap_cons`,
//! NO inductive hypothesis — `Option` has no recursive ctor, exactly like `Bool` thm_bool_logic.rs):
//!   • none-leaf: both sides ι→ `none B`/`none C` ⇒ `refl` (DEFINITIONAL).
//!   • some-leaf: the head collapses by β just as in `map`'s identity/composition steps
//!     (thm_map_append.rs:645-650 `id a ≡ a`; thm_map_map.rs:352-356 `(f∘g) a ≡ f (g a)`,
//!      whnf β driver.rs:46-47) so the leaf is again `refl`. The composed function `f ∘ g` is the
//!     inline closed lambda `λx:A. f (g x)` (no separate `compose` δ-const; thm_map_map.rs:185-190).
//! `Option` is non-indexed (`nidx == 0`) so the ι-driver fires on the OPEN scrutinee `o`
//! (driver.rs:104-119 fast-path); the driver:106 empty-ctx infer (INDEXED families only) never bites.
//!
//! Closed-compute over `Nat` (the recursive `zero | succ n`): `omap (λx. succ x) (some 2) = some 3`
//! and `omap f (none) = none` (ι on concrete ctors; nf/conv). NO new axioms.
//! NO-FALSE-GREEN: the f/g-SWAPPED composition companion is REJECTED by `check`, and a positive
//! control pins each rejection to the swap (not a vacuous ill-typing).

use dnx_proof::conv::conv;
use dnx_proof::driver::nf_tm;
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::{check, TypeError};
use dnx_proof::symbol::{ConstId, IndId};
use dnx_proof::tm::Tm;

// ── term helpers (same idioms as thm_map_append.rs:36-47) ──
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

const NAT: IndId = IndId(0); // element type for closed-compute (zero | succ n)
const OPTION: IndId = IndId(1);
const ID: IndId = IndId(2);
const OMAP: ConstId = ConstId(0);

// Nat = zero | succ (n:Nat)   (recorder.rs:158-177 the canonical recursive inductive).
fn nat_ind() -> Inductive {
    Inductive {
        id: NAT,
        params: vec![],
        indices: vec![],
        sort: 0,
        ctors: vec![
            CtorDecl {
                ctor_ix: 0,
                args: vec![],
                ret_indices: vec![],
            }, // zero
            CtorDecl {
                ctor_ix: 1,
                args: vec![Tm::Ind(NAT)], // n : Nat
                ret_indices: vec![],
            }, // succ
        ],
    }
}
fn nat_ty() -> Tm {
    Tm::Ind(NAT)
}
fn zero() -> Tm {
    Tm::Ctor(NAT, 0)
}
fn succ(n: Tm) -> Tm {
    app(Tm::Ctor(NAT, 1), n)
}
/// Church-style numeral `n` over `Nat` (`succ^n zero`).
fn nat_lit(n: u32) -> Tm {
    (0..n).fold(zero(), |acc, _| succ(acc))
}
/// `succ_fun := λx:Nat. succ x` — the (non-identity) function for the closed-compute witness.
fn succ_fun() -> Tm {
    lam(nat_ty(), succ(Tm::Var(0)))
}

// Option : Π(A:Type₀). Type₀   (param A, NO indices ⇒ nidx==0; like List thm_map_append.rs:76-96, but
// `some`'s field a:A is NON-recursive ⇒ no IH in the minor, recorder.rs:78).
fn option_ind() -> Inductive {
    Inductive {
        id: OPTION,
        params: vec![Tm::Sort(0)],
        indices: vec![],
        sort: 0,
        ctors: vec![
            CtorDecl {
                ctor_ix: 0,
                args: vec![],
                ret_indices: vec![],
            }, // none
            CtorDecl {
                ctor_ix: 1,
                args: vec![Tm::Var(0)], // a : A   (NON-recursive ⇒ minor has NO ih)
                ret_indices: vec![],
            }, // some
        ],
    }
}
fn option_ty(a: Tm) -> Tm {
    app(Tm::Ind(OPTION), a)
}
fn none(a: Tm) -> Tm {
    app(Tm::Ctor(OPTION, 0), a)
}
fn some(a_ty: Tm, x: Tm) -> Tm {
    apps(Tm::Ctor(OPTION, 1), &[a_ty, x])
}

// Id : Π(A:Type₀)(a:A). A → Type₀ ; refl A a : Id A a a.   (thm_map_append.rs:108-126.)
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

// omap := λA B f o. Option.rec A (λ_:Option A. Option B) (none B) (λa:A. some B (f a)) o
//   (CASE-ANALYSIS on o; constant `Option B` motive ⇒ non-indexed result). `Option.rec` spine
//   (recorder.rs:35-69): param A · motive · minor_none · minor_some · scrutinee (ctor order: none,some).
fn omap_body() -> Tm {
    // ctx [A,B,f,o]: A=Var3, B=Var2, f=Var1, o=Var0.
    // minor_some : λa:A. some B (f a).   ctx [A,B,f,o,a]: B=Var3, f=Var2, a=Var0.
    let minor_some = lam(
        Tm::Var(3), // a : A   (A = Var3 in ctx [A,B,f,o])
        some(
            Tm::Var(3),                  // B   (B = Var3 in ctx [A,B,f,o,a])
            app(Tm::Var(2), Tm::Var(0)), // f a   (f = Var2, a = Var0)
        ),
    );
    let elim = apps(
        Tm::Elim(OPTION),
        &[
            Tm::Var(3),                                        // param A
            lam(option_ty(Tm::Var(3)), option_ty(Tm::Var(3))), // motive λ_:Option A. Option B
            none(Tm::Var(2)),                                  // minor_none = none B
            minor_some,
            Tm::Var(0), // scrutinee = o
        ],
    );
    lam(
        Tm::Sort(0),
        lam(
            Tm::Sort(0),
            lam(
                pi(Tm::Var(1), Tm::Var(1)),       // f : A → B
                lam(option_ty(Tm::Var(2)), elim), // o : Option A
            ),
        ),
    )
}
fn omap_ty() -> Tm {
    // Π(A B:Type₀)(f:A→B)(o:Option A). Option B.
    pi(
        Tm::Sort(0),
        pi(
            Tm::Sort(0),
            pi(
                pi(Tm::Var(1), Tm::Var(1)),                       // f : A → B
                pi(option_ty(Tm::Var(2)), option_ty(Tm::Var(2))), // o : Option A ⊢ Option B
            ),
        ),
    )
}
fn omap_(a_ty: Tm, b_ty: Tm, f: Tm, o: Tm) -> Tm {
    apps(Tm::Const(OMAP), &[a_ty, b_ty, f, o])
}

/// `idfun A := λx:A. x`   (thm_map_append.rs:231-233).
fn idfun(a_ty: Tm) -> Tm {
    lam(a_ty, Tm::Var(0))
}

/// `comp A f g := λx:A. f (g x)`, the diagrammatic composition `f ∘ g : A → C` for `g:A→B`,`f:B→C`
/// (thm_map_map.rs:185-190). `f`/`g` are passed already SHIFTED for the lambda's own `x` binder.
fn comp(a_ty: Tm, f: Tm, g: Tm) -> Tm {
    lam(a_ty, app(f, app(g, Tm::Var(0))))
}

fn env() -> dnx_proof::env::GlobalEnv {
    let mut e = dnx_proof::env::GlobalEnv::default();
    e.add_inductive(nat_ind()).expect("Nat admits");
    e.add_inductive(option_ind())
        .expect("Option admits (parametric inductive, positivity R3 ok)");
    e.add_inductive(id_ind()).expect("Id admits");
    e.add_const(OMAP, omap_ty(), omap_body())
        .expect("omap admits (δ-acyclic, case-analysis recursor)");
    e
}

#[test]
fn omap_body_well_typed() {
    // ADMISSION GATE: `add_const` only checks δ-acyclicity (env.rs), NOT the body's type — so check
    // HERE that `omap`'s body genuinely inhabits `Π(A B)(f:A→B)(o:Option A). Option B`: the
    // minor_none `none B : Option B` and minor_some `λa. some B (f a) : Π(a:A). Option B` both fit the
    // constant `Option B` motive (case-analysis Option-elim is well-formed small elimination).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &omap_body(), &omap_ty()).is_ok(),
        "omap_body : Π(A B)(f:A→B)(o:Option A). Option B"
    );
}

#[test]
fn omap_computes_closed() {
    // omap (λx. succ x) (some 2) ι→ some 3 ; omap f (none Nat) ι→ none Nat.
    let env = env();
    let ctx = Vec::new();
    // some-branch: omap succ (some 2) = some 3.
    let lhs = omap_(nat_ty(), nat_ty(), succ_fun(), some(nat_ty(), nat_lit(2)));
    let want = some(nat_ty(), nat_lit(3));
    assert_eq!(
        nf_tm(&env, &ctx, &lhs),
        nf_tm(&env, &ctx, &want),
        "omap (λx. succ x) (some 2) ι→ some 3"
    );
    assert!(
        conv(&env, &ctx, &lhs, &want).unwrap(),
        "omap (λx. succ x) (some 2) ≡ some 3"
    );
    // no-false-green: the mapped result is NOT `some 2` (the head genuinely advanced by `succ`).
    assert!(
        !conv(&env, &ctx, &lhs, &some(nat_ty(), nat_lit(2))).unwrap(),
        "omap (λx. succ x) (some 2) ≢ some 2"
    );
    // none-branch: omap f none ι→ none, for ANY closed f (here succ).
    let lhs_none = omap_(nat_ty(), nat_ty(), succ_fun(), none(nat_ty()));
    assert_eq!(
        nf_tm(&env, &ctx, &lhs_none),
        nf_tm(&env, &ctx, &none(nat_ty())),
        "omap f none ι→ none"
    );
    assert!(
        conv(&env, &ctx, &lhs_none, &none(nat_ty())).unwrap(),
        "omap f none ≡ none"
    );
}

// ════════════════════════ omap_id — ∀A (o:Option A). omap (λx.x) o = o  (functor IDENTITY) ════════════════════════

/// omap_id := λA o. Option.rec A
///     (λo'. Id (Option A) (omap A A id o') o')          -- motive
///     (refl (Option A) (none A))                        -- none-leaf
///     (λa. refl (Option A) (some A a))                  -- some-leaf  (id a ≡ a by β)
///     o                                            (id := λx:A. x)
///
/// CASE-SPLIT on `o` (Option.rec — NO induction hypothesis; Option has no recursive ctor).
///   none: `omap A A id (none A)` ι→ `none A`, goal `Id (Option A) (none A) (none A)` ⇒ `refl` (DEFN).
///   some a: `omap A A id (some A a)` ι→ `some A (id a)`, and `id a = (λx.x) a` β→ `a`
///     (whnf β driver.rs:46-47), so the LHS ≡ `some A a` = the target ⇒ `refl (Option A) (some A a)`.
fn omap_id() -> Tm {
    // ctx [A,o]: A=Var1, o=Var0.
    // motive λo'. Id (Option A) (omap A A id o') o'.   dom A=Var1 (pre-binder); body under o' ⇒ A=Var2.
    let motive = lam(
        option_ty(Tm::Var(1)), // o' : Option A   (A = Var1 in ctx [A,o])
        id_ty(
            option_ty(Tm::Var(2)), // Option A   (A = Var2 under o')
            omap_(Tm::Var(2), Tm::Var(2), idfun(Tm::Var(2)), Tm::Var(0)), // omap A A id o'
            Tm::Var(0),            // o'
        ),
    );
    // none-leaf : refl (Option A) (none A)   (ctx [A,o]: A=Var1).
    let leaf_none = refl(option_ty(Tm::Var(1)), none(Tm::Var(1)));
    // some-leaf : λa. refl (Option A) (some A a)   (ctx [A,o,a]: A=Var2, a=Var0).
    let leaf_some = lam(
        Tm::Var(1), // a : A   (A = Var1 in ctx [A,o])
        refl(
            option_ty(Tm::Var(2)),        // Option A  (A = Var2 in ctx [A,o,a])
            some(Tm::Var(2), Tm::Var(0)), // some A a
        ),
    );
    let rec = apps(
        Tm::Elim(OPTION),
        &[Tm::Var(1), motive, leaf_none, leaf_some, Tm::Var(0)],
    ); // param A, scrut o
    lam(Tm::Sort(0), lam(option_ty(Tm::Var(0)), rec))
}
fn omap_id_ty() -> Tm {
    // Π(A:Type₀)(o:Option A). Id (Option A) (omap A A id o) o.   (ctx [A,o]: A=Var1, o=Var0.)
    pi(
        Tm::Sort(0),
        pi(
            option_ty(Tm::Var(0)), // o : Option A
            id_ty(
                option_ty(Tm::Var(1)),                                        // Option A
                omap_(Tm::Var(1), Tm::Var(1), idfun(Tm::Var(1)), Tm::Var(0)), // omap A A id o
                Tm::Var(0),                                                   // o
            ),
        ),
    )
}

#[test]
fn omap_id_typechecks() {
    // THE theorem: ∀A (o:Option A). omap (λx.x) o = o  (functor IDENTITY) — GENERAL, machine-checked.
    // Case-split on o (Option.rec); none-leaf definitional; some-leaf `refl` after the head `id a ≡ a`
    // collapses by β (driver.rs:46-47). Goes through on the OPEN scrutinee because Option is
    // non-indexed (nidx==0) — never hits the driver:106 empty-ctx infer (INDEXED families only).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &omap_id(), &omap_id_ty()).is_ok(),
        "omap_id : Π(A)(o:Option A). Id (Option A) (omap A A id o) o"
    );
}

#[test]
fn false_omap_id_rejected() {
    // NO-FALSE-GREEN: the identity witness does NOT inhabit the WRONG goal
    // `∀A (o:Option A). omap id o = some A ???` — we use the cleanest false sibling at A:=Nat:
    // `∀(o:Option Nat). omap id o = some Nat zero`. At o = none this demands `Id (Option Nat)(none)
    // (some 0)`, uninhabited, so the `none`-leaf `refl (Option Nat)(none)` no longer fits ⇒ `check`
    // rejects. Specialised to Nat so both endpoints are well-typed (a genuine VALUE mismatch).
    let env = env();
    // bad goal at A:=Nat: Π(o:Option Nat). Id (Option Nat) (omap id o) (some Nat zero).  ctx [o]: o=Var0.
    let bad_ty = pi(
        option_ty(nat_ty()), // o : Option Nat
        id_ty(
            option_ty(nat_ty()),
            omap_(nat_ty(), nat_ty(), idfun(nat_ty()), Tm::Var(0)), // omap id o
            some(nat_ty(), zero()), // some Nat zero  — WRONG (not o)
        ),
    );
    // `omap_id` instantiated at A:=Nat — the well-typed witness whose stated type is the TRUE id law.
    let witness = app(omap_id(), nat_ty());
    // POSITIVE CONTROL (non-vacuity): the SAME specialised witness DOES check against the TRUE id law
    // at A:=Nat — so the rejection below is a genuine VALUE mismatch, not a vacuous ill-typed term.
    let good_ty = pi(
        option_ty(nat_ty()), // o : Option Nat
        id_ty(
            option_ty(nat_ty()),
            omap_(nat_ty(), nat_ty(), idfun(nat_ty()), Tm::Var(0)), // omap id o
            Tm::Var(0),                                             // o   — correct
        ),
    );
    assert!(
        check(&env, &Vec::new(), &witness, &good_ty).is_ok(),
        "positive control: specialised omap_id DOES prove the true identity law at A:=Nat"
    );
    assert_eq!(
        check(&env, &Vec::new(), &witness, &bad_ty),
        Err(TypeError::Mismatch),
        "omap_id does NOT prove omap id o = some Nat zero  (no false-green)"
    );
}

// ════════════════════════ omap_comp — ∀A B C f g o. omap f (omap g o) = omap (λx. f (g x)) o ════════════════════════

/// omap_comp := λA B C f g o. Option.rec A
///     (λo'. Id (Option C) (omap B C f (omap A B g o')) (omap A C (f∘g) o'))    -- motive
///     (refl (Option C) (none C))                                              -- none-leaf
///     (λa. refl (Option C) (some C (f (g a))))                                -- some-leaf
///     o                                                  (f∘g := λx:A. f (g x))
///
/// CASE-SPLIT on `o` (Option.rec — NO induction hypothesis; the COMPOSITION law `omap f ∘ omap g =
/// omap (f ∘ g)`, the `Option` analogue of thm_map_map.rs:359-445 with the recursion erased).
///   none: `omap f (omap g (none A))` ι→ `omap f (none B)` ι→ `none C`; `omap (f∘g)(none A)` ι→
///     `none C` ⇒ `refl (Option C)(none C)` (DEFINITIONAL).
///   some a: LHS `omap f (omap g (some A a))` ι→ `omap f (some B (g a))` ι→ `some C (f (g a))`;
///     RHS `omap (f∘g)(some A a)` ι→ `some C ((f∘g) a)`, and `(f∘g) a = (λx.f(g x)) a` β→ `f (g a)`
///     (whnf β driver.rs:46-47), so RHS ≡ `some C (f (g a))` = LHS ⇒ `refl (Option C)(some C (f(g a)))`.
fn omap_comp() -> Tm {
    // ctx [A,B,C,f,g,o]: A=Var5, B=Var4, C=Var3, f=Var2, g=Var1, o=Var0.
    // motive λo'. Id (Option C) (omap B C f (omap A B g o')) (omap A C (f∘g) o').
    //   dom Option A uses pre-binder A=Var5; body under o' ⇒ A=Var6,B=Var5,C=Var4,f=Var3,g=Var2,o'=Var0.
    let motive = lam(
        option_ty(Tm::Var(5)), // o' : Option A   (A = Var5 in ctx [A,B,C,f,g,o])
        id_ty(
            option_ty(Tm::Var(4)), // Option C
            omap_(
                Tm::Var(5),                                            // B
                Tm::Var(4),                                            // C
                Tm::Var(3),                                            // f
                omap_(Tm::Var(6), Tm::Var(5), Tm::Var(2), Tm::Var(0)), // omap A B g o'
            ), // omap B C f (omap A B g o')
            omap_(
                Tm::Var(6),                                       // A
                Tm::Var(4),                                       // C
                comp(Tm::Var(6), Tm::Var(3 + 1), Tm::Var(2 + 1)), // f∘g (f,g shifted for comp's binder)
                Tm::Var(0),                                       // o'
            ), // omap A C (f∘g) o'
        ),
    );
    // none-leaf : refl (Option C) (none C)   (ctx [A,B,C,f,g,o]: C=Var3).
    let leaf_none = refl(option_ty(Tm::Var(3)), none(Tm::Var(3)));
    // some-leaf : λa. refl (Option C) (some C (f (g a))).
    //   ctx [A,B,C,f,g,o,a]: A=Var6, B=Var5, C=Var4, f=Var3, g=Var2, a=Var0.
    let leaf_some = lam(
        Tm::Var(5), // a : A   (A = Var5 in ctx [A,B,C,f,g,o])
        refl(
            option_ty(Tm::Var(4)), // Option C   (C = Var4 in ctx [A,B,C,f,g,o,a])
            some(
                Tm::Var(4),                                   // C
                app(Tm::Var(3), app(Tm::Var(2), Tm::Var(0))), // f (g a)
            ), // some C (f (g a))
        ),
    );
    let rec = apps(
        Tm::Elim(OPTION),
        &[Tm::Var(5), motive, leaf_none, leaf_some, Tm::Var(0)],
    ); // param A, scrut o
    lam(
        Tm::Sort(0),
        lam(
            Tm::Sort(0),
            lam(
                Tm::Sort(0),
                lam(
                    pi(Tm::Var(1), Tm::Var(1)), // f : B → C   (B=Var1, C=Var0)
                    lam(
                        pi(Tm::Var(3), Tm::Var(3)),      // g : A → B   (A=Var3, B=Var2)
                        lam(option_ty(Tm::Var(4)), rec), // o : Option A  (A=Var4 in ctx [A,B,C,f,g])
                    ),
                ),
            ),
        ),
    )
}
fn omap_comp_ty() -> Tm {
    // Π(A B C:Type₀)(f:B→C)(g:A→B)(o:Option A).
    //   Id (Option C) (omap f (omap g o)) (omap (λx. f (g x)) o).
    // ctx [A,B,C,f,g,o]: A=Var5, B=Var4, C=Var3, f=Var2, g=Var1, o=Var0.
    pi(
        Tm::Sort(0),
        pi(
            Tm::Sort(0),
            pi(
                Tm::Sort(0),
                pi(
                    pi(Tm::Var(1), Tm::Var(1)), // f : B → C
                    pi(
                        pi(Tm::Var(3), Tm::Var(3)), // g : A → B
                        pi(
                            option_ty(Tm::Var(4)), // o : Option A
                            id_ty(
                                option_ty(Tm::Var(3)), // Option C
                                omap_(
                                    Tm::Var(4),
                                    Tm::Var(3),
                                    Tm::Var(2),
                                    omap_(Tm::Var(5), Tm::Var(4), Tm::Var(1), Tm::Var(0)),
                                ), // omap B C f (omap A B g o)
                                omap_(
                                    Tm::Var(5),
                                    Tm::Var(3),
                                    comp(Tm::Var(5), Tm::Var(2 + 1), Tm::Var(1 + 1)),
                                    Tm::Var(0),
                                ), // omap A C (f∘g) o
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
}

#[test]
fn omap_comp_typechecks() {
    // THE theorem: ∀A B C f g o. omap f (omap g o) = omap (λx. f (g x)) o  (functor COMPOSITION) —
    // GENERAL, machine-checked. Case-split on o (Option.rec); none-leaf definitional; some-leaf `refl`
    // after the composed head `(f∘g) a ≡ f (g a)` collapses by β (driver.rs:46-47), exactly as in the
    // `map` composition law. Non-indexed ⇒ goes through on the OPEN scrutinee (driver:106 never bites).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &omap_comp(), &omap_comp_ty()).is_ok(),
        "omap_comp : Π(A B C)(f:B→C)(g:A→B)(o). Id (Option C) (omap f (omap g o)) (omap (λx. f (g x)) o)"
    );
}

#[test]
fn false_omap_comp_swap_rejected() {
    // NO-FALSE-GREEN: `omap_comp` does NOT inhabit the f/g-SWAPPED goal
    // `omap f (omap g o) = omap (λx. g (f x)) o`. Pin A=B=C=Nat (both composites well-typed) so the
    // rejection is a genuine ORDER check: the witness builds the `f∘g` some-leaf, NOT convertible to
    // the `g∘f` target ⇒ `check` rejects.
    let env = env();
    // bad goal at A=B=C=Nat: Π(f g:Nat→Nat)(o:Option Nat).
    //   Id (Option Nat) (omap f (omap g o)) (omap (λx. g (f x)) o).   ctx [f,g,o]: f=Var2, g=Var1, o=Var0.
    let bad_ty = pi(
        pi(nat_ty(), nat_ty()), // f : Nat → Nat
        pi(
            pi(nat_ty(), nat_ty()), // g : Nat → Nat
            pi(
                option_ty(nat_ty()), // o : Option Nat
                id_ty(
                    option_ty(nat_ty()),
                    omap_(
                        nat_ty(),
                        nat_ty(),
                        Tm::Var(2),                                        // f
                        omap_(nat_ty(), nat_ty(), Tm::Var(1), Tm::Var(0)), // omap g o
                    ), // omap f (omap g o)
                    omap_(
                        nat_ty(),
                        nat_ty(),
                        // λx. g (f x)  — SWAPPED order (g∘f instead of f∘g).
                        lam(
                            nat_ty(),
                            app(Tm::Var(1 + 1), app(Tm::Var(2 + 1), Tm::Var(0))),
                        ),
                        Tm::Var(0),
                    ), // omap (λx. g (f x)) o
                ),
            ),
        ),
    );
    // `omap_comp` instantiated at A=B=C=Nat — the well-typed witness whose stated type is the TRUE law.
    let witness = apps(omap_comp(), &[nat_ty(), nat_ty(), nat_ty()]);
    // POSITIVE CONTROL (non-vacuity): the SAME specialised witness DOES check against the TRUE (f∘g)
    // law at A=B=C=Nat — so the rejection below is a genuine f/g-ORDER mismatch, not vacuous ill-typing.
    let good_ty = pi(
        pi(nat_ty(), nat_ty()), // f : Nat → Nat
        pi(
            pi(nat_ty(), nat_ty()), // g : Nat → Nat
            pi(
                option_ty(nat_ty()), // o : Option Nat
                id_ty(
                    option_ty(nat_ty()),
                    omap_(
                        nat_ty(),
                        nat_ty(),
                        Tm::Var(2),                                        // f
                        omap_(nat_ty(), nat_ty(), Tm::Var(1), Tm::Var(0)), // omap g o
                    ), // omap f (omap g o)
                    omap_(
                        nat_ty(),
                        nat_ty(),
                        // λx. f (g x)  — correct (f∘g) order.
                        lam(
                            nat_ty(),
                            app(Tm::Var(2 + 1), app(Tm::Var(1 + 1), Tm::Var(0))),
                        ),
                        Tm::Var(0),
                    ), // omap (λx. f (g x)) o
                ),
            ),
        ),
    );
    assert!(
        check(&env, &Vec::new(), &witness, &good_ty).is_ok(),
        "positive control: specialised omap_comp DOES prove the true (f∘g) law at A=B=C=Nat"
    );
    assert_eq!(
        check(&env, &Vec::new(), &witness, &bad_ty),
        Err(TypeError::Mismatch),
        "omap_comp does NOT prove omap f (omap g o) = omap (λx. g (f x)) o  (no false-green)"
    );
}
