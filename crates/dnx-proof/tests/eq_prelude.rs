//! Propositional-equality prelude (`Id`/`refl`) exercising the indexed recursor-ι
//! (proofs.md §4-5:131-188; recursor.rs/driver.rs). `Id` is an indexed inductive in the
//! Vec mould (params [A,a], index [b], ctor `refl` with `ret_indices=[a]`), and its `Elim`
//! IS the J / based-path-induction eliminator: the single minor's result is
//! `motive (ret_indices=a) (refl A a)` (proofs.md:177-180). From `Elim Id` we derive and
//! TYPECHECK `transport`, `eq_sym`, `eq_trans`, then prove `eq_sym (refl) ≡ refl` and
//! `transport _ refl = id` by ι-reduction (proofs.md:183-188).

use dnx_proof::conv::conv;
use dnx_proof::driver::nf_tm;
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::{check, infer};
use dnx_proof::recursor::recursor_type;
use dnx_proof::symbol::IndId;
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

const NAT: IndId = IndId(0);
const ID: IndId = IndId(1);

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

// Id : Π(A:Type₀)(a:A). A → Type₀   (params [A, a], index [b:A]; sort 0).
//   refl : Π(A:Type₀)(a:A). Id A a a     (ctor 0, no fields, ret index b := a).
fn id_ind() -> Inductive {
    Inductive {
        id: ID,
        params: vec![Tm::Sort(0), Tm::Var(0)], // A:Type₀ ; a:A  (a's type A = Var0 in ctx [A])
        indices: vec![Tm::Var(1)],             // b:A  (A = Var1 in ctx [A,a])
        sort: 0,
        ctors: vec![CtorDecl {
            ctor_ix: 0,
            args: vec![],
            ret_indices: vec![Tm::Var(0)], // refl A a : Id A a a  (index b := a = Var0 in ctx [A,a])
        }],
    }
}

fn id_env() -> dnx_proof::env::GlobalEnv {
    let mut e = dnx_proof::env::GlobalEnv::default();
    e.add_inductive(nat()).expect("Nat admits");
    e.add_inductive(id_ind())
        .expect("Id admits (indexed inductive, Vec mould)");
    e
}

// Id A a b  and  refl A a   (closed builders given concrete A,a,b terms).
fn id_ty(a_ty: Tm, a: Tm, b: Tm) -> Tm {
    apps(Tm::Ind(ID), &[a_ty, a, b])
}
fn refl(a_ty: Tm, a: Tm) -> Tm {
    apps(Tm::Ctor(ID, 0), &[a_ty, a])
}

#[test]
fn id_and_refl_typecheck() {
    let env = id_env();
    // (1) Id : Π(A:Type₀)(a:A). A → Type₀  — the inductive's arity (infer on the head `Ind Id`).
    let id_arity = pi(Tm::Sort(0), pi(Tm::Var(0), pi(Tm::Var(1), Tm::Sort(0))));
    assert_eq!(
        infer(&env, &Vec::new(), &Tm::Ind(ID)).expect("Ind Id infers its arity"),
        id_arity,
        "Id : Π(A:Type₀)(a:A). A → Type₀"
    );

    // (2) refl : Π(A:Type₀)(a:A). Id A a a  — the constructor type (ret head `Id` @ params + ret idx).
    let refl_ty = pi(
        Tm::Sort(0),
        pi(Tm::Var(0), id_ty(Tm::Var(1), Tm::Var(0), Tm::Var(0))),
    );
    assert_eq!(
        infer(&env, &Vec::new(), &Tm::Ctor(ID, 0)).expect("Ctor refl infers its type"),
        refl_ty,
        "refl : Π(A:Type₀)(a:A). Id A a a"
    );

    // (3) a concrete proof: refl Nat zero : Id Nat zero zero.
    let zero = Tm::Ctor(NAT, 0);
    let refl_nz = refl(Tm::Ind(NAT), zero.clone());
    let goal = id_ty(Tm::Ind(NAT), zero.clone(), zero.clone());
    assert!(
        check(&env, &Vec::new(), &refl_nz, &goal).is_ok(),
        "refl Nat zero : Id Nat zero zero"
    );
}

#[test]
fn elim_id_is_j() {
    // The recursor of `Id` IS based path induction (J / `Eq.rec`): the single (refl) minor's
    // result is `motive a (refl A a)` — i.e. proving `motive` at the diagonal suffices
    // (proofs.md:177-180). Pin the synthesized recursor type structurally.
    let env = id_env();
    let id = env.inds.get(&ID).expect("Id present");
    let rt = recursor_type(id, 0).expect("Id recursor type (J) synthesized");

    // Π(A:Type₀) Π(a:A) Π(motive: Π(b:A)Π(x:Id A a b).Sort0) Π(minor_refl) Π(b:A) Π(x:Id A a b). motive b x
    // Peel: A, a, then read the motive binder.
    let after_a = match rt {
        Tm::Pi(d, b) if *d == Tm::Sort(0) => match *b {
            Tm::Pi(da, ba) if *da == Tm::Var(0) => *ba, // a : A (=Var0)
            _ => panic!("second binder a : A"),
        },
        _ => panic!("first binder A : Type₀"),
    };
    let (motive_ty, after_motive) = match after_a {
        Tm::Pi(d, b) => (*d, *b),
        _ => panic!("third binder = motive"),
    };
    // motive : Π(b:A) Π(x:Id A a b). Sort 0   (A=Var1 under b, a=Var2 under b; under x: A=Var2,a=Var3,b=Var1)
    let expect_motive = pi(
        Tm::Var(1), // b : A  (A = Var1 in ctx [A,a])
        pi(
            id_ty(Tm::Var(2), Tm::Var(1), Tm::Var(0)), // x : Id A a b  (A=Var2,a=Var1,b=Var0)
            Tm::Sort(0),
        ),
    );
    assert_eq!(
        motive_ty, expect_motive,
        "motive : Π(b:A)Π(x:Id A a b).Sort ℓ"
    );

    // minor_refl : motive a (refl A a)   (ctx [A,a,motive]: motive=Var0, A=Var2, a=Var1).
    let minor_ty = match after_motive {
        Tm::Pi(d, _) => *d,
        _ => panic!("fourth binder = minor_refl"),
    };
    let expect_minor = app(
        app(Tm::Var(0), Tm::Var(1)),  // motive a
        refl(Tm::Var(2), Tm::Var(1)), // (refl A a)
    );
    assert_eq!(
        minor_ty, expect_minor,
        "minor_refl : motive a (refl A a) — the J base case (proofs.md:177-180)"
    );
}

// ── derived combinators (closed `Elim Id` terms), checked at their stated Π-types ──
// All written in the outer binder context shown; the `Elim Id` arg order is
// params(A,a) · motive · minor · index(b) · scrutinee  (proofs.md:171-181).

/// eq_sym : Π(A:Type₀)(a b:A)(p:Id A a b). Id A b a
///   = λA a b p. Elim Id A a (λb' x. Id A b' a) (refl A a) b p
fn eq_sym() -> Tm {
    // ctx [A,a,b,p]: A=Var3,a=Var2,b=Var1,p=Var0.
    let motive = lam(
        Tm::Var(3), // b' : A   (A = Var3 in ctx [A,a,b,p])
        lam(
            id_ty(Tm::Var(4), Tm::Var(3), Tm::Var(0)), // x : Id A a b'  (A=Var4,a=Var3,b'=Var0)
            id_ty(Tm::Var(5), Tm::Var(1), Tm::Var(4)), // Id A b' a  (A=Var5,b'=Var1,a=Var4)
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            Tm::Var(3),                   // A
            Tm::Var(2),                   // a
            motive,                       // motive
            refl(Tm::Var(3), Tm::Var(2)), // minor_refl = refl A a
            Tm::Var(1),                   // index b
            Tm::Var(0),                   // scrutinee p
        ],
    );
    lam(
        Tm::Sort(0),
        lam(
            Tm::Var(0),
            lam(
                Tm::Var(1),
                lam(id_ty(Tm::Var(2), Tm::Var(1), Tm::Var(0)), body),
            ),
        ),
    )
}
fn eq_sym_ty() -> Tm {
    pi(
        Tm::Sort(0),
        pi(
            Tm::Var(0), // a : A
            pi(
                Tm::Var(1), // b : A
                pi(
                    id_ty(Tm::Var(2), Tm::Var(1), Tm::Var(0)), // p : Id A a b
                    id_ty(Tm::Var(3), Tm::Var(1), Tm::Var(2)), // Id A b a
                ),
            ),
        ),
    )
}

/// transport : Π(A:Type₀)(P:A→Type₀)(a b:A)(p:Id A a b). P a → P b
///   = λA P a b p. Elim Id A a (λb' x. P a → P b') (λh. h) b p
fn transport() -> Tm {
    // ctx [A,P,a,b,p]: A=Var4,P=Var3,a=Var2,b=Var1,p=Var0.
    let motive = lam(
        Tm::Var(4), // b' : A   (A = Var4 in ctx [A,P,a,b,p])
        lam(
            id_ty(Tm::Var(5), Tm::Var(3), Tm::Var(0)), // x : Id A a b'  (A=Var5,a=Var3,b'=Var0)
            pi(app(Tm::Var(5), Tm::Var(4)), app(Tm::Var(6), Tm::Var(2))), // P a → P b'  (P=Var5,a=Var4 ; cod P=Var6,b'=Var2)
        ),
    );
    let minor = lam(app(Tm::Var(3), Tm::Var(2)), Tm::Var(0)); // λh:P a. h
    let body = apps(
        Tm::Elim(ID),
        &[
            Tm::Var(4),
            Tm::Var(2),
            motive,
            minor,
            Tm::Var(1),
            Tm::Var(0),
        ],
    );
    lam(
        Tm::Sort(0),
        lam(
            pi(Tm::Var(0), Tm::Sort(0)), // P : A → Type₀
            lam(
                Tm::Var(1), // a : A
                lam(
                    Tm::Var(2),                                           // b : A
                    lam(id_ty(Tm::Var(3), Tm::Var(1), Tm::Var(0)), body), // p : Id A a b  (ctx [A,P,a,b]: A=Var3,a=Var1,b=Var0)
                ),
            ),
        ),
    )
}
fn transport_ty() -> Tm {
    pi(
        Tm::Sort(0),
        pi(
            pi(Tm::Var(0), Tm::Sort(0)), // P : A → Type₀
            pi(
                Tm::Var(1), // a : A
                pi(
                    Tm::Var(2), // b : A
                    pi(
                        id_ty(Tm::Var(3), Tm::Var(1), Tm::Var(0)), // p : Id A a b  (ctx [A,P,a,b]: A=Var3,a=Var1,b=Var0)
                        pi(app(Tm::Var(3), Tm::Var(2)), app(Tm::Var(4), Tm::Var(2))), // P a → P b
                    ),
                ),
            ),
        ),
    )
}

/// eq_trans : Π(A:Type₀)(a b c:A)(p:Id A a b)(q:Id A b c). Id A a c
///   = λA a b c p q. Elim Id A b (λc' x. Id A a c') p c q   (J on q, based at b)
fn eq_trans() -> Tm {
    // ctx [A,a,b,c,p,q]: A=Var5,a=Var4,b=Var3,c=Var2,p=Var1,q=Var0.
    let motive = lam(
        Tm::Var(5), // c' : A
        lam(
            id_ty(Tm::Var(6), Tm::Var(4), Tm::Var(0)), // x : Id A b c'  (A=Var6,b=Var4,c'=Var0)
            id_ty(Tm::Var(7), Tm::Var(6), Tm::Var(1)), // Id A a c'  (A=Var7,a=Var6,c'=Var1)
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            Tm::Var(5), // A
            Tm::Var(3), // b  (recursor based at b)
            motive,
            Tm::Var(1), // minor_refl = p : Id A a b  (= motive b (refl A b))
            Tm::Var(2), // index c
            Tm::Var(0), // scrutinee q
        ],
    );
    lam(
        Tm::Sort(0),
        lam(
            Tm::Var(0), // a
            lam(
                Tm::Var(1), // b
                lam(
                    Tm::Var(2), // c
                    lam(
                        id_ty(Tm::Var(3), Tm::Var(2), Tm::Var(1)), // p : Id A a b
                        lam(id_ty(Tm::Var(4), Tm::Var(2), Tm::Var(1)), body), // q : Id A b c
                    ),
                ),
            ),
        ),
    )
}
fn eq_trans_ty() -> Tm {
    pi(
        Tm::Sort(0),
        pi(
            Tm::Var(0), // a
            pi(
                Tm::Var(1), // b
                pi(
                    Tm::Var(2), // c
                    pi(
                        id_ty(Tm::Var(3), Tm::Var(2), Tm::Var(1)), // p : Id A a b
                        pi(
                            id_ty(Tm::Var(4), Tm::Var(2), Tm::Var(1)), // q : Id A b c
                            id_ty(Tm::Var(5), Tm::Var(4), Tm::Var(2)), // Id A a c
                        ),
                    ),
                ),
            ),
        ),
    )
}

#[test]
fn transport_typechecks() {
    let env = id_env();
    assert!(
        check(&env, &Vec::new(), &transport(), &transport_ty()).is_ok(),
        "transport : Π(A)(P:A→Type₀)(a b:A)(p:Id A a b). P a → P b"
    );
}

#[test]
fn eq_sym_typechecks() {
    let env = id_env();
    assert!(
        check(&env, &Vec::new(), &eq_sym(), &eq_sym_ty()).is_ok(),
        "eq_sym : Π(A)(a b:A)(p:Id A a b). Id A b a"
    );
}

#[test]
fn eq_trans_typechecks() {
    let env = id_env();
    assert!(
        check(&env, &Vec::new(), &eq_trans(), &eq_trans_ty()).is_ok(),
        "eq_trans : Π(A)(a b c:A)(p:Id A a b)(q:Id A b c). Id A a c"
    );
}

#[test]
fn thm_eq_sym_refl_reduces_to_refl() {
    // THE theorem (end-to-end ι): eq_sym A a (refl A a) ≡ refl A a.
    // J's single minor fires on the `refl` scrutinee (proofs.md:183-188), yielding `refl A a`.
    let env = id_env();
    let zero = Tm::Ctor(NAT, 0);
    let a_ty = Tm::Ind(NAT);
    let refl_az = refl(a_ty.clone(), zero.clone());
    // eq_sym Nat zero zero (refl Nat zero)
    let lhs = apps(
        eq_sym(),
        &[a_ty.clone(), zero.clone(), zero.clone(), refl_az.clone()],
    );
    assert_eq!(
        nf_tm(&env, &Vec::new(), &lhs),
        refl_az,
        "eq_sym (refl) ι-reduces to refl (the J base case is the identity at the diagonal)"
    );
    assert!(
        conv(&env, &Vec::new(), &lhs, &refl_az).unwrap(),
        "eq_sym (refl) ≡ refl"
    );
    // no false-green: it is NOT convertible to a different proof object (refl Nat (succ zero)).
    let refl_s = refl(a_ty, Tm::App(Box::new(Tm::Ctor(NAT, 1)), Box::new(zero)));
    assert!(
        !conv(&env, &Vec::new(), &lhs, &refl_s).unwrap(),
        "eq_sym (refl Nat 0) ≢ refl Nat 1"
    );
}

#[test]
fn thm_transport_refl_is_identity() {
    // transport over `refl` is the identity function: transport A P a a (refl A a) ≡ λh. h
    // (J base minor = `λh. h`; proofs.md:183-188).
    let env = id_env();
    let zero = Tm::Ctor(NAT, 0);
    let a_ty = Tm::Ind(NAT);
    let p = lam(a_ty.clone(), Tm::Ind(NAT)); // P := λ_:Nat. Nat
    let refl_az = refl(a_ty.clone(), zero.clone());
    let lhs = apps(transport(), &[a_ty, p, zero.clone(), zero, refl_az]);
    // λh:P a. h  — P a = (λ_.Nat) zero ; nf both sides for a verbatim identity-function match.
    let id_fn = lam(Tm::Ind(NAT), Tm::Var(0));
    assert_eq!(
        nf_tm(&env, &Vec::new(), &lhs),
        nf_tm(&env, &Vec::new(), &id_fn),
        "transport _ (refl) normalizes to the identity λh.h (proofs.md:183-188)"
    );
}
