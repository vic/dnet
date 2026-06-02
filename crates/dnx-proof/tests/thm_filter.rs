//! Verified list `filter` (the predicate-driven sublist selector `List A → List A` keeping exactly
//! the heads on which a decidable predicate `p : A → Bool` returns `true`) on the dnx-proof kernel,
//! culminating in the GENERAL distributivity / homomorphism law
//! `∀A (p:A→Bool) l1 l2. filter p (l1 ++ l2) = (filter p l1) ++ (filter p l2)`.
//!
//! `filter` is the first list operation here whose recursive step is GUARDED by a `Bool`-valued
//! decision: the cons-minor branches on `p a` via `Elim Bool` (the kernel's large-eliminator into a
//! `List A` motive, infer.rs:130 "large elimination"; the closed analogue of fourcolor's reflected
//! `not`/`eqc`, fourcolor_coloring.rs:139-146). The conditional is spelled exactly as those proofs
//! spell it:
//!   ite c X Y := Elim Bool (λ_:Bool. List A) Y X c      -- minor order is ctor order: false, then true
//!     ⇒  ite true X Y ι→ X ,  ite false X Y ι→ Y      (Bool: ctor 0 = false, ctor 1 = true).
//!
//! `filter` recurses on its list argument, keeping the head iff `p a`:
//!   filter := λA p l. List.rec A (λ_:List A. List A) (nil A)
//!               (λa tl ih. ite (p a) (cons A a ih) ih) l
//!   ⇒  filter p nil ι→ nil A ,
//!      filter p (cons a tl) ι→ ite (p a) (cons A a (filter p tl)) (filter p tl).
//! Because both `List A` and `Bool` are non-indexed (`nidx == 0`), the ι-driver fires on OPEN
//! scrutinees (driver.rs:104-119 fast-path) — so `filter` reduces under binders. The head `ite (p a)`
//! is STUCK under a free `p` (the Bool scrutinee `p a` is neutral), which is the whole reason the
//! inductive step below must CASE-SPLIT on `p a` (an `Elim Bool` over the GOAL) rather than collapse
//! to a single `cons` the way `map`'s step does (thm_map_append.rs:457-543).
//!
//! THEOREMS (machine-checked by the trusted kernel `check`; the kernel is the oracle):
//!   • closed computation: filter (λx. x==e0) [e0,e1,e0] = [e0,e0]   (ι on a CONCRETE predicate;
//!     nf/conv — exercises BOTH ite branches: e0 kept, e1 dropped).
//!   • filter_nil_l : ∀A p l. filter p (nil ++ l) = filter p l       (definitional: nil++l ι→ l).
//!   • filter_append : ∀A p l1 l2. filter p (l1++l2) = (filter p l1) ++ (filter p l2)
//!     (GENERAL; induction on l1; the cons-step CASE-SPLITS on `p a` via `Elim Bool` into a dependent
//!      `Id`-motive — the `true` branch consumes the IH through `ap_cons` over List A, the `false`
//!      branch consumes the IH directly. The IH is genuinely CONSUMED in BOTH branches.)
//!
//! NO new axioms. NO-FALSE-GREEN: the l1/l2-swapped companion is REJECTED by `check`; a positive
//! control pins the rejection to the swap (not a vacuous ill-typing).

use dnx_proof::conv::conv;
use dnx_proof::driver::nf_tm;
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::{check, TypeError};
use dnx_proof::symbol::{ConstId, IndId};
use dnx_proof::tm::Tm;

// ── term helpers (same idioms as thm_map_append.rs) ──
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

const ATOM: IndId = IndId(0); // closed element type {e0,e1,e2} to populate the closed-compute lists
const BOOL: IndId = IndId(1);
const LIST: IndId = IndId(2);
const ID: IndId = IndId(3);
const APPEND: ConstId = ConstId(0);
const FILTER: ConstId = ConstId(1);

// Atom = e0 | e1 | e2.   (thm_map_append.rs:53-74.)
fn atom() -> Inductive {
    Inductive {
        id: ATOM,
        params: vec![],
        indices: vec![],
        sort: 0,
        ctors: (0..3)
            .map(|k| CtorDecl {
                ctor_ix: k,
                args: vec![],
                ret_indices: vec![],
            })
            .collect(),
    }
}
fn atom_ty() -> Tm {
    Tm::Ind(ATOM)
}
fn e(k: u32) -> Tm {
    Tm::Ctor(ATOM, k)
}

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

// List : Π(A:Type₀). Type₀  (param A, NO indices ⇒ nidx==0).   (thm_map_append.rs:76-96.)
fn list_ind() -> Inductive {
    Inductive {
        id: LIST,
        params: vec![Tm::Sort(0)],
        indices: vec![],
        sort: 0,
        ctors: vec![
            CtorDecl {
                ctor_ix: 0,
                args: vec![],
                ret_indices: vec![],
            }, // nil
            CtorDecl {
                ctor_ix: 1,
                args: vec![Tm::Var(0), app(Tm::Ind(LIST), Tm::Var(1))], // a:A, xs:List A
                ret_indices: vec![],
            },
        ],
    }
}
fn list_ty(a: Tm) -> Tm {
    app(Tm::Ind(LIST), a)
}
fn nil(a: Tm) -> Tm {
    app(Tm::Ctor(LIST, 0), a)
}
fn cons(a_ty: Tm, hd: Tm, tl: Tm) -> Tm {
    apps(Tm::Ctor(LIST, 1), &[a_ty, hd, tl])
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

/// `ite A c X Y := Elim Bool (λ_:Bool. List A) Y X c`, the `List A`-valued conditional. Spine
/// (driver.rs §5): motive · minor_false · minor_true · scrutinee. minor_false = Y (else), minor_true
/// = X (then) — matching `not`'s spelling (fourcolor_coloring.rs:142-147) ⇒ ite true X Y ι→ X,
/// ite false X Y ι→ Y. All four arguments are supplied in the AMBIENT context; `a_ty` is used under
/// the motive's own `λ_:Bool` binder, so the helper de-Bruijn-SHIFTS it by 1 there (the only binder
/// it introduces). `c`/`X`/`Y` sit at the ambient level (no shift). Correct at any context.
fn ite(a_ty: Tm, c: Tm, x: Tm, y: Tm) -> Tm {
    let a_ty_under_b = dnx_proof::tm::shift(&a_ty, 1, 0); // A shifted for the motive's λ_:Bool binder
    let motive = lam(bool_ty(), list_ty(a_ty_under_b)); // λ_:Bool. List A
    apps(Tm::Elim(BOOL), &[motive, y, x, c])
}

// append := λA l1 l2. List.rec A (λ_:List A. List A) l2 (λa xs ih. cons A a ih) l1
//   (recursion on l1; thm_map_append.rs:128-167).
fn append_body() -> Tm {
    let minor_cons = lam(
        Tm::Var(2), // a : A
        lam(
            list_ty(Tm::Var(3)), // xs : List A
            lam(
                list_ty(Tm::Var(4)),                      // ih : List A
                cons(Tm::Var(5), Tm::Var(2), Tm::Var(0)), // cons A a ih
            ),
        ),
    );
    let elim = apps(
        Tm::Elim(LIST),
        &[
            Tm::Var(2),                                    // param A
            lam(list_ty(Tm::Var(2)), list_ty(Tm::Var(3))), // motive λ_:List A. List A
            Tm::Var(0),                                    // minor_nil = l2
            minor_cons,
            Tm::Var(1), // scrutinee = l1
        ],
    );
    lam(
        Tm::Sort(0),
        lam(list_ty(Tm::Var(0)), lam(list_ty(Tm::Var(1)), elim)),
    )
}
fn append_ty() -> Tm {
    pi(
        Tm::Sort(0),
        pi(
            list_ty(Tm::Var(0)),
            pi(list_ty(Tm::Var(1)), list_ty(Tm::Var(2))),
        ),
    )
}
fn append(a_ty: Tm, l1: Tm, l2: Tm) -> Tm {
    apps(Tm::Const(APPEND), &[a_ty, l1, l2])
}

// filter := λA p l. List.rec A (λ_:List A. List A) (nil A)
//             (λa tl ih. ite A (p a) (cons A a ih) ih) l
//   (recursion on l; constant `List A` motive). The cons-minor guards on `p a` via `ite` (Elim Bool).
fn filter_body() -> Tm {
    // ctx [A,p,l]: A=Var2, p=Var1, l=Var0.
    // minor_cons : λa.λtl.λih. ite A (p a) (cons A a ih) ih
    //   ctx [A,p,l,a,tl,ih]: A=Var5, p=Var4, a=Var2, ih=Var0.
    let minor_cons = lam(
        Tm::Var(2), // a : A   (A = Var2 in ctx [A,p,l])
        lam(
            list_ty(Tm::Var(3)), // tl : List A  (A = Var3 in ctx [A,p,l,a])
            lam(
                list_ty(Tm::Var(4)), // ih : List A  (A = Var4 in ctx [A,p,l,a,tl])
                // ctx [A,p,l,a,tl,ih]: A=Var5, p=Var4, a=Var2, ih=Var0.
                ite(
                    Tm::Var(5),                               // A
                    app(Tm::Var(4), Tm::Var(2)),              // p a
                    cons(Tm::Var(5), Tm::Var(2), Tm::Var(0)), // cons A a ih  (keep the head)
                    Tm::Var(0),                               // ih           (drop the head)
                ),
            ),
        ),
    );
    let elim = apps(
        Tm::Elim(LIST),
        &[
            Tm::Var(2),                                    // param A
            lam(list_ty(Tm::Var(2)), list_ty(Tm::Var(3))), // motive λ_:List A. List A
            nil(Tm::Var(2)), // minor_nil = nil A   (A = Var2 in ctx [A,p,l])
            minor_cons,
            Tm::Var(0), // scrutinee = l
        ],
    );
    // λA:Type₀.λp:A→Bool.λl:List A. elim
    lam(
        Tm::Sort(0),
        lam(
            pi(Tm::Var(0), bool_ty()),      // p : A → Bool   (A = Var0; Bool closed)
            lam(list_ty(Tm::Var(1)), elim), // l : List A  (A = Var1 in ctx [A,p])
        ),
    )
}
fn filter_ty() -> Tm {
    // Π(A:Type₀)(p:A→Bool)(l:List A). List A.
    pi(
        Tm::Sort(0),
        pi(
            pi(Tm::Var(0), bool_ty()),                    // p : A → Bool
            pi(list_ty(Tm::Var(1)), list_ty(Tm::Var(2))), // l : List A ⊢ List A
        ),
    )
}
fn filter_(a_ty: Tm, p: Tm, l: Tm) -> Tm {
    apps(Tm::Const(FILTER), &[a_ty, p, l])
}

fn env() -> dnx_proof::env::GlobalEnv {
    let mut e = dnx_proof::env::GlobalEnv::default();
    e.add_inductive(atom()).expect("Atom admits");
    e.add_inductive(bool_ind()).expect("Bool admits");
    e.add_inductive(list_ind())
        .expect("List admits (parametric inductive, positivity R3 ok)");
    e.add_inductive(id_ind()).expect("Id admits");
    e.add_const(APPEND, append_ty(), append_body())
        .expect("append admits (δ-acyclic)");
    e.add_const(FILTER, filter_ty(), filter_body())
        .expect("filter admits (δ-acyclic, Bool-guarded recursor)");
    e
}

/// `[x0;x1;…]` over Atom.
fn list_lit(xs: &[Tm]) -> Tm {
    xs.iter()
        .rev()
        .fold(nil(atom_ty()), |tl, hd| cons(atom_ty(), hd.clone(), tl))
}

/// The CONCRETE predicate `is_e0 := λx:Atom. Elim Atom (λ_.Bool) true false false x` — returns
/// `true` exactly at `e0`, `false` at `e1`/`e2`. A genuine decision procedure (the closed-predicate
/// analogue of fourcolor's `eqc`) that exercises BOTH `ite` branches in the closed-compute test.
fn is_e0() -> Tm {
    let motive = lam(atom_ty(), bool_ty()); // λ_:Atom. Bool
    lam(
        atom_ty(),
        apps(Tm::Elim(ATOM), &[motive, tru(), fls(), fls(), Tm::Var(0)]),
    )
}

#[test]
fn filter_body_well_typed() {
    // ADMISSION GATE: `filter`'s defining body genuinely inhabits its declared type
    // `Π(A)(p:A→Bool)(l:List A). List A`. `add_const` only checks δ-acyclicity (env.rs:22-31) — it
    // does NOT type-check the body — so we check it HERE: the cons-minor's `ite (p a) … : List A`
    // (Bool large-elim into `List A`) and the nil-minor `nil A : List A` must both fit the constant
    // `List A` motive. (Likewise `append`, the other δ-const this file relies on.)
    let env = env();
    assert!(
        check(&env, &Vec::new(), &append_body(), &append_ty()).is_ok(),
        "append_body : Π(A)(l1 l2:List A). List A"
    );
    assert!(
        check(&env, &Vec::new(), &filter_body(), &filter_ty()).is_ok(),
        "filter_body : Π(A)(p:A→Bool)(l:List A). List A  (Bool-guarded recursor is well-typed)"
    );
}

#[test]
fn filter_admits_and_computes_closed() {
    // filter is_e0 [e0,e1,e0] ι-normalizes to [e0,e0] — the recursor KEEPS e0 (p e0 ι→ true ⇒ then)
    // and DROPS e1 (p e1 ι→ false ⇒ else), exercising both ite branches.
    let env = env();
    let input = list_lit(&[e(0), e(1), e(0)]); // [e0,e1,e0]
    let want = list_lit(&[e(0), e(0)]); // [e0,e0]
    assert_eq!(
        nf_tm(
            &env,
            &Vec::new(),
            &filter_(atom_ty(), is_e0(), input.clone())
        ),
        nf_tm(&env, &Vec::new(), &want),
        "filter is_e0 [e0,e1,e0] ι→ [e0,e0]"
    );
    assert!(
        conv(
            &env,
            &Vec::new(),
            &filter_(atom_ty(), is_e0(), input.clone()),
            &want
        )
        .unwrap(),
        "filter is_e0 [e0,e1,e0] ≡ [e0,e0]"
    );
    // no-false-green: NOT convertible to the unfiltered input (e1 was genuinely dropped).
    assert!(
        !conv(
            &env,
            &Vec::new(),
            &filter_(atom_ty(), is_e0(), input),
            &input_unfiltered()
        )
        .unwrap(),
        "filter is_e0 [e0,e1,e0] ≢ [e0,e1,e0]"
    );
}
fn input_unfiltered() -> Tm {
    list_lit(&[e(0), e(1), e(0)])
}

// ════════════════════════ filter_nil_l — ∀A p l. filter p (nil ++ l) = filter p l ════════════════════════

/// filter_nil_l := λA p l. refl (List A) (filter p l).
/// `nil ++ l` ι→ `l` (the append nil-minor), so `filter p (nil ++ l) ≡ filter p l` definitionally.
fn filter_nil_l() -> Tm {
    // ctx [A,p,l]: A=Var2, p=Var1, l=Var0.
    lam(
        Tm::Sort(0),
        lam(
            pi(Tm::Var(0), bool_ty()), // p : A → Bool
            lam(
                list_ty(Tm::Var(1)), // l : List A
                refl(
                    list_ty(Tm::Var(2)),                         // List A  (A = Var2 in ctx [A,p,l])
                    filter_(Tm::Var(2), Tm::Var(1), Tm::Var(0)), // filter p l
                ),
            ),
        ),
    )
}
fn filter_nil_l_ty() -> Tm {
    // Π(A:Type₀)(p:A→Bool)(l:List A). Id (List A) (filter p (nil ++ l)) (filter p l).
    pi(
        Tm::Sort(0),
        pi(
            pi(Tm::Var(0), bool_ty()),
            pi(
                list_ty(Tm::Var(1)), // l : List A
                id_ty(
                    list_ty(Tm::Var(2)), // List A
                    filter_(
                        Tm::Var(2),
                        Tm::Var(1),
                        append(Tm::Var(2), nil(Tm::Var(2)), Tm::Var(0)),
                    ), // filter p (nil ++ l)
                    filter_(Tm::Var(2), Tm::Var(1), Tm::Var(0)), // filter p l
                ),
            ),
        ),
    )
}

#[test]
fn filter_nil_l_typechecks() {
    // ∀A p l. filter p (nil ++ l) = filter p l — GENERAL, definitional (ι on the append nil-minor).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &filter_nil_l(), &filter_nil_l_ty()).is_ok(),
        "filter_nil_l : Π(A)(p:A→Bool)(l). Id (List A) (filter p (nil ++ l)) (filter p l)  (definitional)"
    );
}

// ════════════════════════ ap_cons — congruence of `cons a` from J (over List A) ════════════════════════
// Reproduced from thm_map_append.rs:362-428 (the `true` branch's only tool).

/// ap_cons : Π(A:Type₀)(a:A)(xs ys:List A)(p:Id (List A) xs ys). Id (List A) (cons A a xs)(cons A a ys)
fn ap_cons() -> Tm {
    // ctx [A,a,xs,ys,p]: A=Var4, a=Var3, xs=Var2, ys=Var1, p=Var0.
    let motive = lam(
        list_ty(Tm::Var(4)), // ys' : List A
        lam(
            id_ty(list_ty(Tm::Var(5)), Tm::Var(3), Tm::Var(0)), // q : Id (List A) xs ys'
            id_ty(
                list_ty(Tm::Var(6)),
                cons(Tm::Var(6), Tm::Var(5), Tm::Var(4)), // cons A a xs
                cons(Tm::Var(6), Tm::Var(5), Tm::Var(1)), // cons A a ys'
            ),
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            list_ty(Tm::Var(4)), // A_id = List A
            Tm::Var(2),          // xs
            motive,
            refl(
                list_ty(Tm::Var(4)),
                cons(Tm::Var(4), Tm::Var(3), Tm::Var(2)),
            ), // refl (List A)(cons A a xs)
            Tm::Var(1), // index ys
            Tm::Var(0), // scrutinee p
        ],
    );
    lam(
        Tm::Sort(0),
        lam(
            Tm::Var(0), // a : A
            lam(
                list_ty(Tm::Var(1)), // xs
                lam(
                    list_ty(Tm::Var(2)),                                           // ys
                    lam(id_ty(list_ty(Tm::Var(3)), Tm::Var(1), Tm::Var(0)), body), // p
                ),
            ),
        ),
    )
}
fn ap_cons_ty() -> Tm {
    pi(
        Tm::Sort(0),
        pi(
            Tm::Var(0),
            pi(
                list_ty(Tm::Var(1)),
                pi(
                    list_ty(Tm::Var(2)),
                    pi(
                        id_ty(list_ty(Tm::Var(3)), Tm::Var(1), Tm::Var(0)),
                        id_ty(
                            list_ty(Tm::Var(4)),
                            cons(Tm::Var(4), Tm::Var(3), Tm::Var(2)),
                            cons(Tm::Var(4), Tm::Var(3), Tm::Var(1)),
                        ),
                    ),
                ),
            ),
        ),
    )
}
/// `ap_cons A a xs ys p : Id (List A) (cons A a xs) (cons A a ys)`  (concrete instance).
fn ap_cons_at(a_ty: Tm, a: Tm, xs: Tm, ys: Tm, p: Tm) -> Tm {
    apps(ap_cons(), &[a_ty, a, xs, ys, p])
}

#[test]
fn ap_cons_typechecks() {
    let env = env();
    assert!(
        check(&env, &Vec::new(), &ap_cons(), &ap_cons_ty()).is_ok(),
        "ap_cons : Π(A)(a:A)(xs ys:List A)(p:Id (List A) xs ys). Id (List A) (cons a xs)(cons a ys)"
    );
}

// ════════════════════════ filter_append — ∀A p l1 l2. filter p (l1++l2) = (filter p l1)++(filter p l2) ════════════════════════

/// filter_append := λA p l1 l2. List.rec A
///     (λl1'. Id (List A) (filter p (l1'++l2)) ((filter p l1') ++ (filter p l2)))      -- motive
///     (refl (List A) (filter p l2))                                                   -- base l1=nil
///     (λa xs ih. CASESPLIT(p a))                                                       -- step
///     l1
///
/// Induction on l1 (the list `append`/`filter` recurse on).
///   Base l1=nil: `filter p (nil ++ l2)` ι→ `filter p l2`; `(filter p nil) ++ (filter p l2)`
///     ι→ `nil ++ (filter p l2)` ι→ `filter p l2` — both sides ι to `filter p l2`, so the goal is
///     `refl (List A) (filter p l2)` (DEFINITIONAL).
///   Step l1=cons a xs (with IH `ih : Id (List A) (filter p (xs++l2)) ((filter p xs)++(filter p l2))`):
///     LHS `filter p ((cons a xs) ++ l2)` ι→ `filter p (cons a (xs ++ l2))`
///                                         ι→ `ite (p a) (cons a (filter p (xs++l2))) (filter p (xs++l2))`,
///     RHS `(filter p (cons a xs)) ++ (filter p l2)`
///                                ι→ `(ite (p a) (cons a (filter p xs)) (filter p xs)) ++ (filter p l2)`.
///     Both heads are STUCK on the neutral `p a`, so we CASE-SPLIT it with an `Elim Bool` whose
///     motive `M` is the goal with `p a` abstracted to a fresh `b:Bool`:
///       M b := Id (List A) (ite b (cons a (filter p (xs++l2))) (filter p (xs++l2)))
///                          ((ite b (cons a (filter p xs)) (filter p xs)) ++ (filter p l2)).
///     • b = true:  ite true … ι→ the `cons`; RHS `(cons a (filter p xs)) ++ (filter p l2)`
///         ι→ `cons a ((filter p xs) ++ (filter p l2))`, so the goal is
///         `Id (List A) (cons a (filter p (xs++l2))) (cons a ((filter p xs)++(filter p l2)))`
///         = `ap_cons A a (filter p (xs++l2)) ((filter p xs)++(filter p l2)) ih`  (IH CONSUMED).
///     • b = false: ite false … ι→ the tail; the goal is
///         `Id (List A) (filter p (xs++l2)) ((filter p xs) ++ (filter p l2))` = `ih`  (IH CONSUMED).
///     Applying `Elim Bool M minor_false minor_true (p a)` at the neutral `p a` reconstructs the
///     stuck goal exactly (M (p a) ≡ goal), closing the step. All recursive ι's fire on the OPEN tail
///     `xs` because List/Bool are non-indexed (driver.rs:104-119 fast-path).
fn filter_append() -> Tm {
    // ctx [A,p,l1,l2]: A=Var3, p=Var2, l1=Var1, l2=Var0.
    // motive λl1'. Id (List A) (filter p (l1'++l2)) ((filter p l1')++(filter p l2)).
    //   ctx [A,p,l1,l2,l1']: A=Var4, p=Var3, l2=Var1, l1'=Var0.
    let motive = lam(
        list_ty(Tm::Var(3)), // l1' : List A
        id_ty(
            list_ty(Tm::Var(4)), // List A
            filter_(
                Tm::Var(4),
                Tm::Var(3),
                append(Tm::Var(4), Tm::Var(0), Tm::Var(1)),
            ), // filter p (l1' ++ l2)
            append(
                Tm::Var(4),
                filter_(Tm::Var(4), Tm::Var(3), Tm::Var(0)), // filter p l1'
                filter_(Tm::Var(4), Tm::Var(3), Tm::Var(1)), // filter p l2
            ), // (filter p l1') ++ (filter p l2)
        ),
    );
    // base : refl (List A) (filter p l2)   (ctx [A,p,l1,l2]: A=Var3, p=Var2, l2=Var0).
    let base = refl(
        list_ty(Tm::Var(3)),
        filter_(Tm::Var(3), Tm::Var(2), Tm::Var(0)),
    );
    // step λa.λxs.λih. (Elim Bool M minor_false minor_true (p a)).
    //   ctx [A,p,l1,l2,a,xs,ih]: A=Var6, p=Var5, l2=Var3, a=Var2, xs=Var1, ih=Var0.
    let step = lam(
        Tm::Var(3), // a : A   (A = Var3 in ctx [A,p,l1,l2])
        lam(
            list_ty(Tm::Var(4)), // xs : List A  (A = Var4 in ctx [A,p,l1,l2,a])
            lam(
                // ih : motive xs = Id (List A) (filter p (xs++l2)) ((filter p xs)++(filter p l2))
                //   ctx [A,p,l1,l2,a,xs]: A=Var5, p=Var4, l2=Var2, xs=Var0.
                id_ty(
                    list_ty(Tm::Var(5)),
                    filter_(
                        Tm::Var(5),
                        Tm::Var(4),
                        append(Tm::Var(5), Tm::Var(0), Tm::Var(2)),
                    ), // filter p (xs ++ l2)
                    append(
                        Tm::Var(5),
                        filter_(Tm::Var(5), Tm::Var(4), Tm::Var(0)), // filter p xs
                        filter_(Tm::Var(5), Tm::Var(4), Tm::Var(2)), // filter p l2
                    ),
                ),
                // ── the Bool case-split on `p a` ──
                // ctx [A,p,l1,l2,a,xs,ih]: A=Var6, p=Var5, l2=Var3, a=Var2, xs=Var1, ih=Var0.
                filter_step_casesplit(),
            ),
        ),
    );
    let rec = apps(
        Tm::Elim(LIST),
        &[Tm::Var(3), motive, base, step, Tm::Var(1)],
    ); // param A, scrut l1
    lam(
        Tm::Sort(0),
        lam(
            pi(Tm::Var(0), bool_ty()), // p : A → Bool
            lam(
                list_ty(Tm::Var(1)),           // l1 : List A
                lam(list_ty(Tm::Var(2)), rec), // l2 : List A
            ),
        ),
    )
}

/// The cons-step body: `Elim Bool M minor_false minor_true (p a)`, written in the context
/// `[A,p,l1,l2,a,xs,ih]` (A=Var6, p=Var5, l2=Var3, a=Var2, xs=Var1, ih=Var0).
///
/// Bool-elim spine: motive · minor_false · minor_true · scrutinee (ctor order false, then true).
/// The motive abstracts the stuck `p a` to `b:Bool`:
///   M := λb:Bool. Id (List A) (ite b (cons a (filter p (xs++l2))) (filter p (xs++l2)))
///                            ((ite b (cons a (filter p xs)) (filter p xs)) ++ (filter p l2)).
fn filter_step_casesplit() -> Tm {
    // ── motive M (one extra binder `b` over the step ctx) ──
    // ctx [A,p,l1,l2,a,xs,ih,b]: A=Var7, p=Var6, l2=Var4, a=Var3, xs=Var2, ih=Var1, b=Var0.
    let motive = lam(
        bool_ty(), // b : Bool
        id_ty(
            list_ty(Tm::Var(7)), // List A
            // LHS endpoint: ite b (cons A a (filter p (xs++l2))) (filter p (xs++l2)).
            ite(
                Tm::Var(7), // A
                Tm::Var(0), // b
                cons(
                    Tm::Var(7),
                    Tm::Var(3), // a
                    filter_(
                        Tm::Var(7),
                        Tm::Var(6),
                        append(Tm::Var(7), Tm::Var(2), Tm::Var(4)),
                    ), // filter p (xs++l2)
                ), // cons A a (filter p (xs++l2))
                filter_(
                    Tm::Var(7),
                    Tm::Var(6),
                    append(Tm::Var(7), Tm::Var(2), Tm::Var(4)),
                ), // filter p (xs++l2)
            ),
            // RHS endpoint: (ite b (cons A a (filter p xs)) (filter p xs)) ++ (filter p l2).
            append(
                Tm::Var(7),
                ite(
                    Tm::Var(7), // A
                    Tm::Var(0), // b
                    cons(
                        Tm::Var(7),
                        Tm::Var(3),                                  // a
                        filter_(Tm::Var(7), Tm::Var(6), Tm::Var(2)), // filter p xs
                    ), // cons A a (filter p xs)
                    filter_(Tm::Var(7), Tm::Var(6), Tm::Var(2)), // filter p xs
                ), // ite b (cons a (filter p xs)) (filter p xs)
                filter_(Tm::Var(7), Tm::Var(6), Tm::Var(4)), // filter p l2
            ),
        ),
    );

    // ── minor_false : M false  (b dropped) ──
    // Goal at b=false: Id (List A) (filter p (xs++l2)) ((filter p xs) ++ (filter p l2)) = ih.
    // ctx [A,p,l1,l2,a,xs,ih]: A=Var6, p=Var5, l2=Var3, a=Var2, xs=Var1, ih=Var0.
    let minor_false = Tm::Var(0); // ih  (CONSUMED)

    // ── minor_true : M true  (b kept) ──
    // Goal at b=true: Id (List A) (cons A a (filter p (xs++l2))) (cons A a ((filter p xs)++(filter p l2)))
    //   = ap_cons A a (filter p (xs++l2)) ((filter p xs)++(filter p l2)) ih.
    // (RHS `(cons a (filter p xs)) ++ (filter p l2)` ι→ `cons a ((filter p xs) ++ (filter p l2))`.)
    let minor_true = ap_cons_at(
        Tm::Var(6), // A
        Tm::Var(2), // a
        filter_(
            Tm::Var(6),
            Tm::Var(5),
            append(Tm::Var(6), Tm::Var(1), Tm::Var(3)),
        ), // filter p (xs++l2)
        append(
            Tm::Var(6),
            filter_(Tm::Var(6), Tm::Var(5), Tm::Var(1)), // filter p xs
            filter_(Tm::Var(6), Tm::Var(5), Tm::Var(3)), // filter p l2
        ), // (filter p xs) ++ (filter p l2)
        Tm::Var(0), // ih  (CONSUMED)
    );

    apps(
        Tm::Elim(BOOL),
        &[
            motive,
            minor_false,
            minor_true,
            app(Tm::Var(5), Tm::Var(2)), // scrutinee = p a
        ],
    )
}

fn filter_append_ty() -> Tm {
    // Π(A:Type₀)(p:A→Bool)(l1 l2:List A). Id (List A) (filter p (l1++l2)) ((filter p l1)++(filter p l2)).
    // ctx [A,p,l1,l2]: A=Var3, p=Var2, l1=Var1, l2=Var0.
    pi(
        Tm::Sort(0),
        pi(
            pi(Tm::Var(0), bool_ty()),
            pi(
                list_ty(Tm::Var(1)), // l1
                pi(
                    list_ty(Tm::Var(2)), // l2
                    id_ty(
                        list_ty(Tm::Var(3)), // List A
                        filter_(
                            Tm::Var(3),
                            Tm::Var(2),
                            append(Tm::Var(3), Tm::Var(1), Tm::Var(0)),
                        ), // filter p (l1 ++ l2)
                        append(
                            Tm::Var(3),
                            filter_(Tm::Var(3), Tm::Var(2), Tm::Var(1)), // filter p l1
                            filter_(Tm::Var(3), Tm::Var(2), Tm::Var(0)), // filter p l2
                        ), // (filter p l1) ++ (filter p l2)
                    ),
                ),
            ),
        ),
    )
}

#[test]
fn filter_append_typechecks() {
    // THE theorem: ∀A p l1 l2. filter p (l1++l2) = (filter p l1) ++ (filter p l2) — GENERAL, checked.
    // Induction on l1 (List.rec); base definitional; the cons-step CASE-SPLITS on the neutral `p a`
    // via Elim Bool into a dependent Id-motive: the `true` branch closes with `ap_cons` (fed the IH),
    // the `false` branch IS the IH. The IH is genuinely CONSUMED in BOTH branches. Goes through on the
    // OPEN tail because List/Bool are non-indexed (nidx==0) — the open recursive field `xs` never hits
    // the driver:106 empty-ctx infer (that gate only bites INDEXED families).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &filter_append(), &filter_append_ty()).is_ok(),
        "filter_append : Π(A)(p:A→Bool)(l1 l2). Id (List A) (filter p (l1++l2)) ((filter p l1)++(filter p l2))"
    );
}

#[test]
fn false_filter_append_swap_rejected() {
    // NO-FALSE-GREEN: `filter_append` does NOT inhabit the l1/l2-SWAPPED (false) goal
    // `filter p (l1++l2) = (filter p l2) ++ (filter p l1)` — append is not commutative, so the
    // base/step witnesses no longer fit and `check` rejects.
    let env = env();
    let bad_ty = pi(
        Tm::Sort(0),
        pi(
            pi(Tm::Var(0), bool_ty()),
            pi(
                list_ty(Tm::Var(1)),
                pi(
                    list_ty(Tm::Var(2)),
                    id_ty(
                        list_ty(Tm::Var(3)),
                        filter_(
                            Tm::Var(3),
                            Tm::Var(2),
                            append(Tm::Var(3), Tm::Var(1), Tm::Var(0)),
                        ), // filter p (l1 ++ l2)
                        append(
                            Tm::Var(3),
                            filter_(Tm::Var(3), Tm::Var(2), Tm::Var(0)), // filter p l2
                            filter_(Tm::Var(3), Tm::Var(2), Tm::Var(1)), // filter p l1
                        ), // (filter p l2) ++ (filter p l1)  — SWAPPED
                    ),
                ),
            ),
        ),
    );
    // POSITIVE CONTROL (non-vacuity): the SAME witness DOES check against the TRUE goal — so the
    // rejection below is a genuine l1/l2-ORDER mismatch, not a vacuous ill-typed term.
    assert!(
        check(&env, &Vec::new(), &filter_append(), &filter_append_ty()).is_ok(),
        "positive control: filter_append DOES prove the true law"
    );
    assert_eq!(
        check(&env, &Vec::new(), &filter_append(), &bad_ty),
        Err(TypeError::Mismatch),
        "filter_append does NOT prove filter p (l1++l2) = (filter p l2)++(filter p l1)  (no false-green)"
    );
}
