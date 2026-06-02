//! `plus_n_O` — the classic Coq first proof — proven end-to-end on the kernel.
//!
//! HUMAN-READABLE THEOREM:  ∀ n : Nat,  n + 0 = n   (`Id Nat (plus n 0) n`),
//! where `plus` recurses on its FIRST argument (`plus 0 b = b`, `plus (succ k) b = succ (plus k b)`).
//! Hence `plus n 0` is STUCK on the neutral `n` (ι cannot fire on a variable) — the equation is
//! NOT definitional; it demands genuine induction over the `Nat` constructor tree.
//!
//! The proof is `Nat.rec` (the recursor synthesized in TCB; proofs.md:163-188) at the dependent
//! motive `P := λn. Id Nat (plus n 0) n` (large-elim into Sort 0, A5):
//!   • base    `P 0`        = `Id Nat (plus 0 0) 0` ≡ `Id Nat 0 0`  ⊳  `refl Nat 0`   (ι: plus 0 0 → 0)
//!   • step    `P (succ k)` = `Id Nat (plus (succ k) 0) (succ k)` ≡ `Id Nat (succ (plus k 0)) (succ k)`
//!                ⊳  `ap succ ih`   where `ih : Id Nat (plus k 0) k`   (ι: plus (succ k) 0 → succ (plus k 0))
//! `ap` (congruence `Id A x y → Id B (f x) (f y)`) is derived from `Elim Id` / J exactly as
//! `eq_sym`/`transport` are derived in `eq_prelude.rs:166-233` (proofs.md:177-188).
//!
//! NO-FALSE-GREEN: the FALSE companion `∀ n. Id Nat (plus n 0) (succ n)` is rejected by `check`
//! (its base case `refl Nat 0 : Id Nat 0 0` cannot inhabit `Id Nat 0 (succ 0)`), and the bare
//! false equation `Id Nat 0 (succ 0)` has no `refl` inhabitant.

use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::{check, TypeError};
use dnx_proof::symbol::{ConstId, IndId};
use dnx_proof::tm::Tm;

// ── term helpers (same idioms as eq_prelude.rs:18-29) ──
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
const PLUS: ConstId = ConstId(0);

fn nat_ty() -> Tm {
    Tm::Ind(NAT)
}
fn zero() -> Tm {
    Tm::Ctor(NAT, 0)
}
fn succ(n: Tm) -> Tm {
    app(Tm::Ctor(NAT, 1), n)
}

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

// Id : Π(A:Type₀)(a:A). A → Type₀ ; refl : Π(A:Type₀)(a:A). Id A a a   (eq_prelude.rs:49-61).
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

// plus := λa:Nat.λb:Nat. Elim Nat (λ_:Nat.Nat) b (λk.λih. succ ih) a   — recursion on the FIRST arg.
//   plus 0 b = b ;  plus (succ k) b = succ (plus k b).   (a3-style `add` but on arg 1; soundness.rs:189.)
fn plus_body() -> Tm {
    // ctx [a,b]: a=Var1, b=Var0.
    let elim = apps(
        Tm::Elim(NAT),
        &[
            lam(nat_ty(), nat_ty()),                        // motive λ_:Nat. Nat
            Tm::Var(0),                                     // minor_zero = b
            lam(nat_ty(), lam(nat_ty(), succ(Tm::Var(0)))), // minor_succ = λk.λih. succ ih
            Tm::Var(1),                                     // scrutinee = a
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

// ap : Π(A B:Type₀)(f:A→B)(x y:A)(p:Id A x y). Id B (f x) (f y)
//   = λA B f x y p. Elim Id A x (λy'.λq. Id B (f x) (f y')) (refl B (f x)) y p   (J; eq_prelude.rs:166-186).
fn ap() -> Tm {
    // ctx [A,B,f,x,y,p]: A=Var5,B=Var4,f=Var3,x=Var2,y=Var1,p=Var0.
    let motive = lam(
        Tm::Var(5), // y' : A   (A = Var5 in ctx [A,B,f,x,y,p])
        lam(
            id_ty(Tm::Var(6), Tm::Var(3), Tm::Var(0)), // q : Id A x y'  (A=Var6,x=Var3,y'=Var0)
            id_ty(
                Tm::Var(6),                  // B  (=Var6 under y',q)
                app(Tm::Var(5), Tm::Var(4)), // f x  (f=Var5,x=Var4)
                app(Tm::Var(5), Tm::Var(1)), // f y' (f=Var5,y'=Var1)
            ),
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            Tm::Var(5), // A
            Tm::Var(2), // x  (J based at x)
            motive,
            refl(Tm::Var(4), app(Tm::Var(3), Tm::Var(2))), // minor_refl = refl B (f x)
            Tm::Var(1),                                    // index y
            Tm::Var(0),                                    // scrutinee p
        ],
    );
    // λA:Type₀.λB:Type₀.λf:A→B.λx:A.λy:A.λp:Id A x y. body
    lam(
        Tm::Sort(0),
        lam(
            Tm::Sort(0),
            lam(
                pi(Tm::Var(1), Tm::Var(1)), // f : A → B  (ctx [A,B]: A=Var1; cod B=Var1 under the dom)
                lam(
                    Tm::Var(2), // x : A  (ctx [A,B,f]: A=Var2)
                    lam(
                        Tm::Var(3),                                           // y : A
                        lam(id_ty(Tm::Var(4), Tm::Var(1), Tm::Var(0)), body), // p : Id A x y
                    ),
                ),
            ),
        ),
    )
}
fn ap_ty() -> Tm {
    pi(
        Tm::Sort(0), // A
        pi(
            Tm::Sort(0), // B
            pi(
                pi(Tm::Var(1), Tm::Var(1)), // f : A → B
                pi(
                    Tm::Var(2), // x : A
                    pi(
                        Tm::Var(3), // y : A
                        pi(
                            id_ty(Tm::Var(4), Tm::Var(1), Tm::Var(0)), // p : Id A x y
                            id_ty(
                                Tm::Var(4),                  // B  (ctx [A,B,f,x,y,p]: B=Var4)
                                app(Tm::Var(3), Tm::Var(2)), // f x  (f=Var3, x=Var2)
                                app(Tm::Var(3), Tm::Var(1)), // f y  (f=Var3, y=Var1)
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
}

fn env() -> dnx_proof::env::GlobalEnv {
    let mut e = dnx_proof::env::GlobalEnv::default();
    e.add_inductive(nat()).expect("Nat admits");
    e.add_inductive(id_ind())
        .expect("Id admits (indexed inductive, Vec mould)");
    e.add_const(PLUS, plus_ty(), plus_body())
        .expect("plus admits (δ-acyclic)");
    e
}

// plus_n_O := λn:Nat. Elim Nat (λm. Id Nat (plus m 0) m) (refl Nat 0) (λk.λih. ap Nat Nat succ (plus k 0) k ih) n
fn motive_p() -> Tm {
    // λm:Nat. Id Nat (plus m 0) m   (ctx [n,m]: m=Var0).
    lam(
        nat_ty(),
        id_ty(nat_ty(), plus(Tm::Var(0), zero()), Tm::Var(0)),
    )
}
fn succ_fn() -> Tm {
    lam(nat_ty(), succ(Tm::Var(0))) // λx:Nat. succ x
}
fn plus_n_o() -> Tm {
    // minor_succ : λk.λih. ap Nat Nat succ (plus k 0) k ih   (ctx [n,k,ih]: k=Var1, ih=Var0).
    let minor_succ = lam(
        nat_ty(), // k
        lam(
            id_ty(nat_ty(), plus(Tm::Var(0), zero()), Tm::Var(0)), // ih : Id Nat (plus k 0) k  (ctx [n,k]: k=Var0)
            apps(
                ap(),
                &[
                    nat_ty(),
                    nat_ty(),
                    succ_fn(),
                    plus(Tm::Var(1), zero()),
                    Tm::Var(1),
                    Tm::Var(0),
                ],
            ),
        ),
    );
    let elim = apps(
        Tm::Elim(NAT),
        &[
            motive_p(),
            refl(nat_ty(), zero()), // minor_zero : Id Nat (plus 0 0) 0 ≡ Id Nat 0 0
            minor_succ,
            Tm::Var(0), // scrutinee n
        ],
    );
    lam(nat_ty(), elim)
}
fn plus_n_o_ty() -> Tm {
    // Π(n:Nat). Id Nat (plus n 0) n
    pi(
        nat_ty(),
        id_ty(nat_ty(), plus(Tm::Var(0), zero()), Tm::Var(0)),
    )
}

#[test]
fn ap_typechecks() {
    // congruence derived from J (the step's only extra tool) — pin it before the theorem.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &ap(), &ap_ty()).is_ok(),
        "ap : Π(A B)(f:A→B)(x y:A)(p:Id A x y). Id B (f x) (f y)  (eq_prelude.rs:166; proofs.md:177-188)"
    );
}

#[test]
fn plus_n_o_typechecks() {
    // THE theorem: ∀ n. Id Nat (plus n 0) n — by Nat.rec induction + ap (congruence) on the
    // inductive hypothesis. `plus n 0` is stuck on neutral n, so this is NOT definitional —
    // it is the genuine recursive-data theorem (proofs.md:163-188, A5/A6 machinery).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &plus_n_o(), &plus_n_o_ty()).is_ok(),
        "plus_n_O : Π(n:Nat). Id Nat (plus n 0) n  (Nat.rec + ap; the classic Coq first proof)"
    );
}

#[test]
fn false_equation_has_no_refl() {
    // NO-FALSE-GREEN (1): the bare FALSE equation `0 = succ 0` has no `refl` inhabitant.
    // `refl Nat 0 : Id Nat 0 0`, never `Id Nat 0 (succ 0)` (distinct ctor spines, ι cannot bridge).
    let env = env();
    let false_goal = id_ty(nat_ty(), zero(), succ(zero())); // Id Nat 0 (succ 0)
    assert_eq!(
        check(&env, &Vec::new(), &refl(nat_ty(), zero()), &false_goal),
        Err(TypeError::Mismatch),
        "refl Nat 0 does NOT inhabit Id Nat 0 (succ 0)"
    );
}

#[test]
fn false_plus_n_succ_n_rejected() {
    // NO-FALSE-GREEN (2): the FALSE companion `∀ n. Id Nat (plus n 0) (succ n)` is NOT provable
    // by the same induction skeleton. Its base case demands `refl Nat 0 : Id Nat (plus 0 0) (succ 0)`
    // ≡ `Id Nat 0 (succ 0)`, which `check` rejects — so the whole term fails to typecheck.
    let env = env();
    // motive_bad := λm. Id Nat (plus m 0) (succ m)
    let motive_bad = lam(
        nat_ty(),
        id_ty(nat_ty(), plus(Tm::Var(0), zero()), succ(Tm::Var(0))),
    );
    // Same skeleton as the true proof (refl base + ap step) — but at the FALSE motive.
    let minor_succ_bad = lam(
        nat_ty(),
        lam(
            id_ty(nat_ty(), plus(Tm::Var(0), zero()), succ(Tm::Var(0))),
            apps(
                ap(),
                &[
                    nat_ty(),
                    nat_ty(),
                    succ_fn(),
                    plus(Tm::Var(1), zero()),
                    succ(Tm::Var(1)),
                    Tm::Var(0),
                ],
            ),
        ),
    );
    let bad_term = lam(
        nat_ty(),
        apps(
            Tm::Elim(NAT),
            &[
                motive_bad,
                refl(nat_ty(), zero()),
                minor_succ_bad,
                Tm::Var(0),
            ],
        ),
    );
    let bad_ty = pi(
        nat_ty(),
        id_ty(nat_ty(), plus(Tm::Var(0), zero()), succ(Tm::Var(0))),
    );
    assert_eq!(
        check(&env, &Vec::new(), &bad_term, &bad_ty),
        Err(TypeError::Mismatch),
        "∀ n. Id Nat (plus n 0) (succ n) is FALSE — the refl base case is rejected (no false-green)"
    );
}
