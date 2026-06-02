//! Verified `length` bridging List → Nat on the dnx-proof kernel, culminating in the GENERAL
//! homomorphism law `∀A xs ys. length (xs ++ ys) = length xs + length ys`.
//!
//! This file joins the two non-indexed worlds: `List A` (parametric, `nidx == 0`) and `Nat`
//! (`nidx == 0`). `length` is one `Elim List` whose motive is the CONSTANT `Nat`, so its result
//! is non-indexed:
//!   length := λA xs. List.rec A (λ_:List A. Nat) 0 (λa tl ih. succ ih) xs
//!   ⇒  length A nil ι→ 0 ,  length A (cons a tl) ι→ succ (length A tl).
//! Because both `List` and `Nat` are non-indexed, the ι-driver fires on OPEN scrutinees
//! (driver.rs:104-119 fast-path) — so the inductive step below reduces under binders and the
//! `driver.rs:106` empty-ctx infer (which only bites INDEXED families) never engages.
//!
//! THEOREMS (all GENERAL, ∀-quantified, machine-checked by the kernel `check`):
//!   • length_append : ∀A xs ys. length (xs ++ ys) = length xs + length ys
//!     (induction on xs; base definitional; step CONSUMES the IH via the J-derived `ap_succ`).
//!
//! NO new axioms. NO-FALSE-GREEN: the off-by-one / swapped companions are REJECTED by `check`.

use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::{check, TypeError};
use dnx_proof::symbol::{ConstId, IndId};
use dnx_proof::tm::Tm;

// ── term helpers ──
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

const ATOM: IndId = IndId(0);
const LIST: IndId = IndId(1);
const NAT: IndId = IndId(2);
const ID: IndId = IndId(3);
const APPEND: ConstId = ConstId(0);
const PLUS: ConstId = ConstId(1);
const LENGTH: ConstId = ConstId(2);

// Atom = e0 | e1 | e2   (a closed payload type, like thm_list_append.rs:50-71).
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

// List : Π(A:Type₀). Type₀  (param A, NO indices ⇒ nidx==0).   (thm_list_append.rs:76-96.)
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
            },
            CtorDecl {
                ctor_ix: 1,
                args: vec![Tm::Var(0), app(Tm::Ind(LIST), Tm::Var(1))],
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

// Nat = zero | succ Nat   (non-indexed; thm_nat_algebra.rs:55-74).
fn nat() -> Inductive {
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
            },
            CtorDecl {
                ctor_ix: 1,
                args: vec![Tm::Ind(NAT)],
                ret_indices: vec![],
            },
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

// Id : Π(A:Type₀)(a:A). A → Type₀ ; refl A a : Id A a a   (polymorphic — serves both Id (List A)
// and Id Nat).   (thm_list_append.rs:108-126.)
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
fn id_nat(a: Tm, b: Tm) -> Tm {
    apps(Tm::Ind(ID), &[nat_ty(), a, b])
}
fn refl_nat(a: Tm) -> Tm {
    apps(Tm::Ctor(ID, 0), &[nat_ty(), a])
}

// append := λA l1 l2. List.rec A (λ_:List A. List A) l2 (λa xs ih. cons A a ih) l1
//   (recursion on l1; thm_list_append.rs:128-157).
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

// plus := λa b. Elim Nat (λ_.Nat) b (λk ih. succ ih) a   (recursion on FIRST arg; thm_nat_algebra.rs:100-110).
fn plus_body() -> Tm {
    let elim = apps(
        Tm::Elim(NAT),
        &[
            lam(nat_ty(), nat_ty()),
            Tm::Var(0),
            lam(nat_ty(), lam(nat_ty(), succ(Tm::Var(0)))),
            Tm::Var(1),
        ],
    );
    lam(nat_ty(), lam(nat_ty(), elim))
}
fn plus_ty() -> Tm {
    pi(nat_ty(), pi(nat_ty(), nat_ty()))
}
fn plus(a: Tm, b: Tm) -> Tm {
    apps(Tm::Const(PLUS), &[a, b])
}

// length := λA xs. List.rec A (λ_:List A. Nat) 0 (λa tl ih. succ ih) xs   (constant Nat motive
// ⇒ non-indexed result).  length A nil ι→ 0 ;  length A (cons a tl) ι→ succ (length A tl).
fn length_body() -> Tm {
    // ctx [A,xs]: A=Var1, xs=Var0.  minor_cons λa.λtl.λih. succ ih   (ctx [A,xs,a,tl,ih]: ih=Var0).
    let minor_cons = lam(
        Tm::Var(1), // a : A   (A = Var1 in ctx [A,xs])
        lam(
            list_ty(Tm::Var(2)), // tl : List A  (A = Var2 in ctx [A,xs,a])
            lam(
                nat_ty(),         // ih : Nat
                succ(Tm::Var(0)), // succ ih
            ),
        ),
    );
    let elim = apps(
        Tm::Elim(LIST),
        &[
            Tm::Var(1),                         // param A
            lam(list_ty(Tm::Var(1)), nat_ty()), // motive λ_:List A. Nat
            zero(),                             // minor_nil = 0
            minor_cons,
            Tm::Var(0), // scrutinee = xs
        ],
    );
    lam(Tm::Sort(0), lam(list_ty(Tm::Var(0)), elim))
}
fn length_ty() -> Tm {
    pi(Tm::Sort(0), pi(list_ty(Tm::Var(0)), nat_ty()))
}
fn length(a_ty: Tm, xs: Tm) -> Tm {
    apps(Tm::Const(LENGTH), &[a_ty, xs])
}

fn env() -> dnx_proof::env::GlobalEnv {
    let mut e = dnx_proof::env::GlobalEnv::default();
    e.add_inductive(atom()).expect("Atom admits");
    e.add_inductive(list_ind())
        .expect("List admits (parametric inductive)");
    e.add_inductive(nat()).expect("Nat admits");
    e.add_inductive(id_ind()).expect("Id admits");
    e.add_const(APPEND, append_ty(), append_body())
        .expect("append admits (δ-acyclic)");
    e.add_const(PLUS, plus_ty(), plus_body())
        .expect("plus admits (δ-acyclic)");
    e.add_const(LENGTH, length_ty(), length_body())
        .expect("length admits (δ-acyclic)");
    e
}

// ════════════════════════ ap_succ — congruence of `succ` from J ════════════════════════
// Reproduced verbatim from thm_nat_algebra.rs:135-174 (the step's only tool).

/// ap_succ : Π(a b:Nat)(p:Id Nat a b). Id Nat (succ a) (succ b)
fn ap_succ() -> Tm {
    let motive = lam(
        nat_ty(),
        lam(
            id_nat(Tm::Var(3), Tm::Var(0)),
            id_nat(succ(Tm::Var(4)), succ(Tm::Var(1))),
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            nat_ty(),
            Tm::Var(2),
            motive,
            refl_nat(succ(Tm::Var(2))),
            Tm::Var(1),
            Tm::Var(0),
        ],
    );
    lam(
        nat_ty(),
        lam(nat_ty(), lam(id_nat(Tm::Var(1), Tm::Var(0)), body)),
    )
}
fn ap_succ_ty() -> Tm {
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            pi(
                id_nat(Tm::Var(1), Tm::Var(0)),
                id_nat(succ(Tm::Var(2)), succ(Tm::Var(1))),
            ),
        ),
    )
}
fn ap_succ_at(a: Tm, b: Tm, p: Tm) -> Tm {
    apps(ap_succ(), &[a, b, p])
}

#[test]
fn building_blocks_typecheck() {
    // length is admitted (δ-acyclic) and ap_succ (the step's only tool) typechecks.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &ap_succ(), &ap_succ_ty()).is_ok(),
        "ap_succ : Π(a b:Nat)(p:Id Nat a b). Id Nat (succ a)(succ b)  (J / Elim Id)"
    );
}

#[test]
fn length_admits_and_computes() {
    // length does real work on CLOSED lists: length [e0,e1,e2] ≡ 3.
    use dnx_proof::conv::conv;
    let atom_ty = Tm::Ind(ATOM);
    let e = |k: u32| Tm::Ctor(ATOM, k);
    let env = env();
    let l3 = cons(
        atom_ty.clone(),
        e(0),
        cons(
            atom_ty.clone(),
            e(1),
            cons(atom_ty.clone(), e(2), nil(atom_ty.clone())),
        ),
    );
    assert!(
        conv(
            &env,
            &Vec::new(),
            &length(atom_ty.clone(), l3.clone()),
            &succ(succ(succ(zero())))
        )
        .unwrap(),
        "length [e0,e1,e2] ≡ 3"
    );
    // no-false-green: NOT 2.
    assert!(
        !conv(&env, &Vec::new(), &length(atom_ty, l3), &succ(succ(zero()))).unwrap(),
        "length [e0,e1,e2] ≢ 2"
    );
}

// ════════════════════════ length_append — ∀A xs ys. length (xs++ys) = length xs + length ys ════════════════════════

/// length_append := λA xs ys. List.rec A
///     (λxs'. Id Nat (length (append xs' ys)) (plus (length xs') (length ys)))   -- motive
///     (refl Nat (length ys))                                                    -- base xs=nil
///     (λa tl ih. ap_succ (length (append tl ys)) (plus (length tl)(length ys)) ih) -- step
///     xs
///
/// Induction on xs (the list `append`/`length` recurse on).
///   Base xs=nil: `append A nil ys ι→ ys` so LHS `length ys`; `plus (length nil)(length ys) ≡
///     plus 0 (length ys) ι→ length ys`. Goal `Id Nat (length ys)(length ys)` = refl (DEFINITIONAL).
///   Step xs=cons a tl:
///     LHS `length (cons a tl ++ ys)` ι→ `length (cons a (tl++ys))` ι→ `succ (length (tl++ys))`,
///     RHS `plus (length (cons a tl))(length ys)` ι→ `plus (succ (length tl))(length ys)`
///         ι→ `succ (plus (length tl)(length ys))`,
///     IH `ih : Id Nat (length (tl++ys)) (plus (length tl)(length ys))`,
///     so `ap_succ … ih` closes the goal. The IH is genuinely CONSUMED. The recursive ι's fire on
///     the OPEN tail `tl` because List/Nat are non-indexed (nidx==0) — driver:106 does NOT bite.
fn length_append() -> Tm {
    // ctx [A,xs,ys]: A=Var2, xs=Var1, ys=Var0.
    // motive λxs'. Id Nat (length (append xs' ys)) (plus (length xs')(length ys)).
    //   ctx [A,xs,ys,xs']: A=Var3, ys=Var1, xs'=Var0.
    let motive = lam(
        list_ty(Tm::Var(2)), // xs' : List A
        id_nat(
            length(Tm::Var(3), append(Tm::Var(3), Tm::Var(0), Tm::Var(1))), // length (xs'++ys)
            plus(
                length(Tm::Var(3), Tm::Var(0)), // length xs'
                length(Tm::Var(3), Tm::Var(1)), // length ys
            ),
        ),
    );
    // base : refl Nat (length ys)   (ctx [A,xs,ys]: A=Var2, ys=Var0).
    let base = refl_nat(length(Tm::Var(2), Tm::Var(0)));
    // step λa.λtl.λih. ap_succ (length (tl++ys)) (plus (length tl)(length ys)) ih.
    //   ctx [A,xs,ys,a,tl,ih]: A=Var5, ys=Var3, a=Var2, tl=Var1, ih=Var0.
    let step = lam(
        Tm::Var(2), // a : A   (A = Var2 in ctx [A,xs,ys])
        lam(
            list_ty(Tm::Var(3)), // tl : List A  (A = Var3 in ctx [A,xs,ys,a])
            lam(
                // ih : motive tl = Id Nat (length (tl++ys)) (plus (length tl)(length ys)).
                //   ctx [A,xs,ys,a,tl]: A=Var4, ys=Var2, tl=Var0.
                id_nat(
                    length(Tm::Var(4), append(Tm::Var(4), Tm::Var(0), Tm::Var(2))),
                    plus(
                        length(Tm::Var(4), Tm::Var(0)),
                        length(Tm::Var(4), Tm::Var(2)),
                    ),
                ),
                // ctx [A,xs,ys,a,tl,ih]: A=Var5, ys=Var3, tl=Var1, ih=Var0.
                ap_succ_at(
                    length(Tm::Var(5), append(Tm::Var(5), Tm::Var(1), Tm::Var(3))), // length (tl++ys)
                    plus(
                        length(Tm::Var(5), Tm::Var(1)),
                        length(Tm::Var(5), Tm::Var(3)),
                    ), // plus (length tl)(length ys)
                    Tm::Var(0), // ih  (CONSUMED)
                ),
            ),
        ),
    );
    let rec = apps(
        Tm::Elim(LIST),
        &[Tm::Var(2), motive, base, step, Tm::Var(1)],
    ); // param A, scrut xs
    lam(
        Tm::Sort(0),
        lam(list_ty(Tm::Var(0)), lam(list_ty(Tm::Var(1)), rec)),
    )
}
fn length_append_ty() -> Tm {
    // Π(A)(xs ys:List A). Id Nat (length (xs++ys)) (plus (length xs)(length ys)).
    // ctx [A,xs,ys]: A=Var2, xs=Var1, ys=Var0.
    pi(
        Tm::Sort(0),
        pi(
            list_ty(Tm::Var(0)),
            pi(
                list_ty(Tm::Var(1)),
                id_nat(
                    length(Tm::Var(2), append(Tm::Var(2), Tm::Var(1), Tm::Var(0))),
                    plus(
                        length(Tm::Var(2), Tm::Var(1)),
                        length(Tm::Var(2), Tm::Var(0)),
                    ),
                ),
            ),
        ),
    )
}

#[test]
fn length_append_typechecks() {
    // THE theorem: ∀A xs ys. length (xs++ys) = length xs + length ys — GENERAL, machine-checked.
    // Induction on xs (List.rec); base definitional; step CONSUMES the IH via ap_succ. Goes
    // through on the OPEN tail because List/Nat are non-indexed (nidx==0) — driver:106 does not bite.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &length_append(), &length_append_ty()).is_ok(),
        "length_append : Π(A)(xs ys:List A). Id Nat (length (xs++ys)) (plus (length xs)(length ys))"
    );
}

#[test]
fn false_length_append_succ_rejected() {
    // NO-FALSE-GREEN (off by one): `length (xs++ys) = succ (plus (length xs)(length ys))` is FALSE.
    let env = env();
    let bad_ty = pi(
        Tm::Sort(0),
        pi(
            list_ty(Tm::Var(0)),
            pi(
                list_ty(Tm::Var(1)),
                id_nat(
                    length(Tm::Var(2), append(Tm::Var(2), Tm::Var(1), Tm::Var(0))),
                    succ(plus(
                        length(Tm::Var(2), Tm::Var(1)),
                        length(Tm::Var(2), Tm::Var(0)),
                    )),
                ),
            ),
        ),
    );
    assert_eq!(
        check(&env, &Vec::new(), &length_append(), &bad_ty),
        Err(TypeError::Mismatch),
        "length_append does NOT prove length(xs++ys) = succ(len xs + len ys)  (no false-green)"
    );
}
