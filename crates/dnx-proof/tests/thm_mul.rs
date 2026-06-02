//! Verified multiplication on the dnx-proof kernel: the two zero laws of `*`.
//!
//! `mul` recurses on its FIRST argument over `plus`:
//!   mul := λm n. Nat.rec (λ_:Nat.Nat) 0 (λk ih. plus n ih) m
//!   ⇒  mul 0 n ι→ 0 ,  mul (succ k) n ι→ plus n (mul k n).
//! `Nat` is non-indexed (`nidx == 0`), so the ι-driver fires on OPEN scrutinees
//! (driver.rs:104-119) — the genuine inductive step below goes through.
//!
//! THEOREMS (both GENERAL, ∀-quantified, machine-checked by the kernel `check`):
//!   • mul_0_n : ∀n.  0 * n = 0     (definitional: mul 0 n ι→ 0)
//!   • mul_n_O : ∀n.  n * 0 = 0     (induction on n; `mul n 0` is stuck on neutral n)
//!
//! For `mul_n_O` the step is the cleanest possible induction: at `n = succ k`,
//!   mul (succ k) 0 ι→ plus 0 (mul k 0) ι→ mul k 0    (plus 0 x ι→ x),
//! so the goal `mul (succ k) 0 = 0` is DEFINITIONALLY the IH `mul k 0 = 0` — the inductive
//! hypothesis `ih` is returned directly (no congruence needed). NO new axioms.
//!
//! NO-FALSE-GREEN: `∀n. n*0 = succ 0` and `∀n. 0*n = succ 0` are REJECTED by `check`.

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

const NAT: IndId = IndId(0);
const ID: IndId = IndId(1);
const PLUS: ConstId = ConstId(0);
const MUL: ConstId = ConstId(1);

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

// plus := λa b. Elim Nat (λ_.Nat) b (λk ih. succ ih) a   (recursion on FIRST arg; thm_plus_n_o.rs).
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

// mul := λm n. Elim Nat (λ_.Nat) 0 (λk ih. plus n ih) m   (recursion on FIRST arg).
//   mul 0 n ι→ 0 ;  mul (succ k) n ι→ plus n (mul k n).
fn mul_body() -> Tm {
    // ctx [m,n]: m=Var1, n=Var0.  Under the succ-minor λk.λih: ctx [m,n,k,ih]: n=Var2, ih=Var0.
    let elim = apps(
        Tm::Elim(NAT),
        &[
            lam(nat_ty(), nat_ty()), // motive λ_:Nat.Nat
            zero(),                  // minor_zero = 0
            lam(nat_ty(), lam(nat_ty(), plus(Tm::Var(2), Tm::Var(0)))), // minor_succ = λk ih. plus n ih
            Tm::Var(1),                                                 // scrutinee = m
        ],
    );
    lam(nat_ty(), lam(nat_ty(), elim))
}
fn mul_ty() -> Tm {
    pi(nat_ty(), pi(nat_ty(), nat_ty()))
}
fn mul(a: Tm, b: Tm) -> Tm {
    apps(Tm::Const(MUL), &[a, b])
}

// ════════════════════════ derived equality combinators (J / Elim Id) ════════════════════════
// ap_succ / eq_trans / eq_sym reproduced verbatim from thm_nat_algebra.rs:135-241,465-517;
// ap_plus_l is the new left-congruence of `plus` (same J shape as ap_succ).

/// ap_succ : Π(a b:Nat)(p:Id Nat a b). Id Nat (succ a) (succ b)   (thm_nat_algebra.rs:135-159).
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

/// ap_plus_l : Π(c a b:Nat)(p:Id Nat a b). Id Nat (plus c a) (plus c b)
///   = λc a b p. Elim Id Nat a (λb' x. Id Nat (plus c a)(plus c b')) (refl Nat (plus c a)) b p
/// J / Elim Id, the SAME shape as ap_succ (thm_nat_algebra.rs:135-159) — left-congruence of plus.
fn ap_plus_l() -> Tm {
    // ctx [c,a,b,p]: c=Var3, a=Var2, b=Var1, p=Var0.
    let motive = lam(
        nat_ty(), // b' : Nat
        lam(
            id_nat(Tm::Var(3), Tm::Var(0)), // x : Id Nat a b'   (a=Var3, b'=Var0)
            id_nat(
                plus(Tm::Var(5), Tm::Var(4)), // plus c a   (c=Var5, a=Var4)
                plus(Tm::Var(5), Tm::Var(1)), // plus c b'  (b'=Var1)
            ),
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            nat_ty(),
            Tm::Var(2), // a  (J based at a)
            motive,
            refl_nat(plus(Tm::Var(3), Tm::Var(2))), // minor_refl = refl Nat (plus c a)
            Tm::Var(1),                             // index b
            Tm::Var(0),                             // scrutinee p
        ],
    );
    lam(
        nat_ty(),
        lam(
            nat_ty(),
            lam(nat_ty(), lam(id_nat(Tm::Var(1), Tm::Var(0)), body)),
        ),
    )
}
fn ap_plus_l_ty() -> Tm {
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            pi(
                nat_ty(),
                pi(
                    id_nat(Tm::Var(1), Tm::Var(0)),
                    id_nat(plus(Tm::Var(3), Tm::Var(2)), plus(Tm::Var(3), Tm::Var(1))),
                ),
            ),
        ),
    )
}
fn ap_plus_l_at(c: Tm, a: Tm, b: Tm, p: Tm) -> Tm {
    apps(ap_plus_l(), &[c, a, b, p])
}

/// eq_trans : Π(A)(a b c:A)(p:Id A a b)(q:Id A b c). Id A a c   (thm_nat_algebra.rs:177-216).
fn eq_trans() -> Tm {
    let motive = lam(
        Tm::Var(5),
        lam(
            apps(Tm::Ind(ID), &[Tm::Var(6), Tm::Var(4), Tm::Var(0)]),
            apps(Tm::Ind(ID), &[Tm::Var(7), Tm::Var(6), Tm::Var(1)]),
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            Tm::Var(5),
            Tm::Var(3),
            motive,
            Tm::Var(1),
            Tm::Var(2),
            Tm::Var(0),
        ],
    );
    lam(
        Tm::Sort(0),
        lam(
            Tm::Var(0),
            lam(
                Tm::Var(1),
                lam(
                    Tm::Var(2),
                    lam(
                        apps(Tm::Ind(ID), &[Tm::Var(3), Tm::Var(2), Tm::Var(1)]),
                        lam(
                            apps(Tm::Ind(ID), &[Tm::Var(4), Tm::Var(2), Tm::Var(1)]),
                            body,
                        ),
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
            Tm::Var(0),
            pi(
                Tm::Var(1),
                pi(
                    Tm::Var(2),
                    pi(
                        apps(Tm::Ind(ID), &[Tm::Var(3), Tm::Var(2), Tm::Var(1)]),
                        pi(
                            apps(Tm::Ind(ID), &[Tm::Var(4), Tm::Var(2), Tm::Var(1)]),
                            apps(Tm::Ind(ID), &[Tm::Var(5), Tm::Var(4), Tm::Var(2)]),
                        ),
                    ),
                ),
            ),
        ),
    )
}
/// `eq_trans Nat a b c p q : Id Nat a c`.
fn trans_nat(a: Tm, b: Tm, c: Tm, p: Tm, q: Tm) -> Tm {
    apps(eq_trans(), &[nat_ty(), a, b, c, p, q])
}

/// eq_sym : Π(A)(a b:A)(p:Id A a b). Id A b a   (thm_nat_algebra.rs:465-498).
fn eq_sym() -> Tm {
    let motive = lam(
        Tm::Var(3),
        lam(
            apps(Tm::Ind(ID), &[Tm::Var(4), Tm::Var(3), Tm::Var(0)]),
            apps(Tm::Ind(ID), &[Tm::Var(5), Tm::Var(1), Tm::Var(4)]),
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            Tm::Var(3),
            Tm::Var(2),
            motive,
            apps(Tm::Ctor(ID, 0), &[Tm::Var(3), Tm::Var(2)]),
            Tm::Var(1),
            Tm::Var(0),
        ],
    );
    lam(
        Tm::Sort(0),
        lam(
            Tm::Var(0),
            lam(
                Tm::Var(1),
                lam(
                    apps(Tm::Ind(ID), &[Tm::Var(2), Tm::Var(1), Tm::Var(0)]),
                    body,
                ),
            ),
        ),
    )
}
fn eq_sym_ty() -> Tm {
    pi(
        Tm::Sort(0),
        pi(
            Tm::Var(0),
            pi(
                Tm::Var(1),
                pi(
                    apps(Tm::Ind(ID), &[Tm::Var(2), Tm::Var(1), Tm::Var(0)]),
                    apps(Tm::Ind(ID), &[Tm::Var(3), Tm::Var(1), Tm::Var(2)]),
                ),
            ),
        ),
    )
}
/// `eq_sym Nat a b p : Id Nat b a`.
fn eq_sym_nat(a: Tm, b: Tm, p: Tm) -> Tm {
    apps(eq_sym(), &[nat_ty(), a, b, p])
}

// ════════════════════════ proven plus lemmas (reused as terms; thm_nat_algebra.rs) ════════════════════════

/// plus_n_O : Π(n:Nat). Id Nat (plus n 0) n   (thm_nat_algebra.rs:441-456).
fn plus_n_o() -> Tm {
    let motive = lam(nat_ty(), id_nat(plus(Tm::Var(0), zero()), Tm::Var(0)));
    let base = refl_nat(zero());
    let step = lam(
        nat_ty(),
        lam(
            id_nat(plus(Tm::Var(0), zero()), Tm::Var(0)),
            ap_succ_at(plus(Tm::Var(1), zero()), Tm::Var(1), Tm::Var(0)),
        ),
    );
    lam(
        nat_ty(),
        apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(0)]),
    )
}

/// plus_n_Sm : Π(m n:Nat). Id Nat (succ (plus m n)) (plus m (succ n))   (thm_nat_algebra.rs:308-336).
fn plus_n_sm() -> Tm {
    let motive = lam(
        nat_ty(),
        id_nat(
            succ(plus(Tm::Var(0), Tm::Var(1))),
            plus(Tm::Var(0), succ(Tm::Var(1))),
        ),
    );
    let base = refl_nat(succ(Tm::Var(0)));
    let step = lam(
        nat_ty(),
        lam(
            id_nat(
                succ(plus(Tm::Var(0), Tm::Var(1))),
                plus(Tm::Var(0), succ(Tm::Var(1))),
            ),
            ap_succ_at(
                succ(plus(Tm::Var(1), Tm::Var(2))),
                plus(Tm::Var(1), succ(Tm::Var(2))),
                Tm::Var(0),
            ),
        ),
    );
    let rec = apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(1)]);
    lam(nat_ty(), lam(nat_ty(), rec))
}
fn plus_n_sm_at(m: Tm, n: Tm) -> Tm {
    apps(plus_n_sm(), &[m, n])
}

/// add_comm : Π(m n:Nat). Id Nat (plus m n) (plus n m)   (thm_nat_algebra.rs:519-559).
fn add_comm() -> Tm {
    let motive = lam(
        nat_ty(),
        id_nat(plus(Tm::Var(0), Tm::Var(1)), plus(Tm::Var(1), Tm::Var(0))),
    );
    let base = eq_sym_nat(
        plus(Tm::Var(0), zero()),
        Tm::Var(0),
        app(plus_n_o(), Tm::Var(0)),
    );
    let step = lam(
        nat_ty(),
        lam(
            id_nat(plus(Tm::Var(0), Tm::Var(1)), plus(Tm::Var(1), Tm::Var(0))),
            trans_nat(
                succ(plus(Tm::Var(1), Tm::Var(2))),
                succ(plus(Tm::Var(2), Tm::Var(1))),
                plus(Tm::Var(2), succ(Tm::Var(1))),
                ap_succ_at(
                    plus(Tm::Var(1), Tm::Var(2)),
                    plus(Tm::Var(2), Tm::Var(1)),
                    Tm::Var(0),
                ),
                plus_n_sm_at(Tm::Var(2), Tm::Var(1)),
            ),
        ),
    );
    let rec = apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(1)]);
    lam(nat_ty(), lam(nat_ty(), rec))
}
fn add_comm_at(m: Tm, n: Tm) -> Tm {
    apps(add_comm(), &[m, n])
}

/// add_assoc_l : Π(x y z:Nat). Id Nat (plus (plus x y) z) (plus x (plus y z))
///   — induction on the FIRST arg x (next-theorems-design.md §2.1a). The last-arg orientation
///   (induction on z) is `add_assoc` in thm_induction.rs and also checks: `plus` recurses on a
///   NON-indexed `Nat`, so the ι-driver fires on open recursive fields (driver.rs:109-112).
/// Motive λx'. Id Nat (plus (plus x' y) z) (plus x' (plus y z)).
///   base x=0: `plus (plus 0 y) z ι→ plus y z`, `plus 0 (plus y z) ι→ plus y z` ⇒ refl.
///   step x=succ k: both sides ι→ succ(...) through the first-arg succ-minor, close with ap_succ ih.
fn add_assoc_l() -> Tm {
    // ctx [x,y,z,x']: y=Var2, z=Var1, x'=Var0.
    let motive = lam(
        nat_ty(),
        id_nat(
            plus(plus(Tm::Var(0), Tm::Var(2)), Tm::Var(1)), // (x'+y)+z
            plus(Tm::Var(0), plus(Tm::Var(2), Tm::Var(1))), // x'+(y+z)
        ),
    );
    // base : refl Nat (plus y z)   (ctx [x,y,z]: y=Var1, z=Var0).
    let base = refl_nat(plus(Tm::Var(1), Tm::Var(0)));
    // step λk.λih. ap_succ ((k+y)+z) (k+(y+z)) ih.
    let step = lam(
        nat_ty(), // k
        lam(
            // ih : motive k   (ctx [x,y,z,k]: y=Var2, z=Var1, k=Var0).
            id_nat(
                plus(plus(Tm::Var(0), Tm::Var(2)), Tm::Var(1)),
                plus(Tm::Var(0), plus(Tm::Var(2), Tm::Var(1))),
            ),
            // ctx [x,y,z,k,ih]: y=Var3, z=Var2, k=Var1, ih=Var0.
            ap_succ_at(
                plus(plus(Tm::Var(1), Tm::Var(3)), Tm::Var(2)), // (k+y)+z
                plus(Tm::Var(1), plus(Tm::Var(3), Tm::Var(2))), // k+(y+z)
                Tm::Var(0),                                     // ih  (CONSUMED)
            ),
        ),
    );
    let rec = apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(2)]); // scrut x
    lam(nat_ty(), lam(nat_ty(), lam(nat_ty(), rec)))
}
fn add_assoc_l_ty() -> Tm {
    // Π(x y z:Nat). Id Nat ((x+y)+z) (x+(y+z))   (ctx [x,y,z]: x=Var2, y=Var1, z=Var0).
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            pi(
                nat_ty(),
                id_nat(
                    plus(plus(Tm::Var(2), Tm::Var(1)), Tm::Var(0)),
                    plus(Tm::Var(2), plus(Tm::Var(1), Tm::Var(0))),
                ),
            ),
        ),
    )
}
fn add_assoc_l_at(x: Tm, y: Tm, z: Tm) -> Tm {
    apps(add_assoc_l(), &[x, y, z])
}

fn env() -> dnx_proof::env::GlobalEnv {
    let mut e = dnx_proof::env::GlobalEnv::default();
    e.add_inductive(nat()).expect("Nat admits");
    e.add_inductive(id_ind()).expect("Id admits");
    e.add_const(PLUS, plus_ty(), plus_body())
        .expect("plus admits (δ-acyclic)");
    e.add_const(MUL, mul_ty(), mul_body())
        .expect("mul admits (δ-acyclic; mul calls plus, plus does not call mul)");
    e
}

#[test]
fn mul_admits_and_computes() {
    // mul is admitted (δ-acyclic over plus) and its two computation rules hold by ι.
    use dnx_proof::conv::conv;
    let env = env();
    let lit = |n: u32| (0..n).fold(zero(), |a, _| succ(a));
    // mul 0 n ≡ 0  (n=3).
    assert!(
        conv(&env, &Vec::new(), &mul(zero(), lit(3)), &zero()).unwrap(),
        "mul 0 3 ≡ 0"
    );
    // mul (succ k) n ≡ plus n (mul k n): mul 2 3 ≡ 6.
    assert!(
        conv(&env, &Vec::new(), &mul(lit(2), lit(3)), &lit(6)).unwrap(),
        "mul 2 3 ≡ 6"
    );
    // mul 3 0 ≡ 0  (the n*0 law at a closed instance).
    assert!(
        conv(&env, &Vec::new(), &mul(lit(3), zero()), &zero()).unwrap(),
        "mul 3 0 ≡ 0"
    );
}

// ════════════════════════ mul_0_n — ∀n. 0 * n = 0 ════════════════════════

/// mul_0_n := λn:Nat. refl Nat 0   :   Π(n:Nat). Id Nat (mul 0 n) 0.
/// `mul 0 n` ι-reduces to `0` (the zero-minor), so this law is DEFINITIONAL.
fn mul_0_n() -> Tm {
    lam(nat_ty(), refl_nat(zero()))
}
fn mul_0_n_ty() -> Tm {
    pi(nat_ty(), id_nat(mul(zero(), Tm::Var(0)), zero()))
}

#[test]
fn mul_0_n_typechecks() {
    // ∀n. 0 * n = 0 — GENERAL, definitional (ι on the first-arg zero-minor).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &mul_0_n(), &mul_0_n_ty()).is_ok(),
        "mul_0_n : Π(n:Nat). Id Nat (mul 0 n) 0  (definitional, mul 0 n ι→ 0)"
    );
}

#[test]
fn false_mul_0_n_rejected() {
    // NO-FALSE-GREEN: `∀n. 0*n = succ 0` is FALSE (0 ≠ 1).
    let env = env();
    let bad_ty = pi(nat_ty(), id_nat(mul(zero(), Tm::Var(0)), succ(zero())));
    assert_eq!(
        check(&env, &Vec::new(), &mul_0_n(), &bad_ty),
        Err(TypeError::Mismatch),
        "∀n. 0*n = 1 is FALSE — refl Nat 0 rejected"
    );
}

// ════════════════════════ mul_n_O — ∀n. n * 0 = 0 ════════════════════════

/// mul_n_O := λn:Nat. Nat.rec (λn'. Id Nat (mul n' 0) 0)
///                            (refl Nat 0)                 -- base n=0:  mul 0 0 ≡ 0
///                            (λk ih. ih)                  -- step n=succ k: goal ≡ IH
///                            n
/// `mul n 0` is STUCK on the neutral n, so this needs genuine induction. Step n=succ k:
///   mul (succ k) 0 ι→ plus 0 (mul k 0) ι→ mul k 0   (plus 0 x ι→ x),
/// so `motive (succ k) = Id Nat (mul (succ k) 0) 0` is DEFINITIONALLY `Id Nat (mul k 0) 0 = motive k`,
/// and the inductive hypothesis `ih : motive k` is returned DIRECTLY — the IH is genuinely the
/// whole step. (The kernel accepts `λk ih. ih` only because the two motives are conv-equal.)
fn mul_n_o() -> Tm {
    // motive λn'. Id Nat (mul n' 0) 0   (ctx [n,n']: n'=Var0).
    let motive = lam(nat_ty(), id_nat(mul(Tm::Var(0), zero()), zero()));
    let base = refl_nat(zero()); // Id Nat (mul 0 0) 0 ≡ Id Nat 0 0
                                 // step λk.λih. ih   (ctx [n,k,ih]: ih=Var0).  ih : motive k, returned as motive (succ k).
    let step = lam(
        nat_ty(),                                                 // k
        lam(id_nat(mul(Tm::Var(0), zero()), zero()), Tm::Var(0)), // λih. ih
    );
    lam(
        nat_ty(),
        apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(0)]),
    )
}
fn mul_n_o_ty() -> Tm {
    pi(nat_ty(), id_nat(mul(Tm::Var(0), zero()), zero()))
}

#[test]
fn mul_n_o_typechecks() {
    // ∀n. n * 0 = 0 — GENERAL, by Nat.rec induction on n. `mul n 0` is stuck on neutral n
    // (NOT definitional), so this is a genuine inductive proof; the step returns the IH directly
    // because `mul (succ k) 0 ≡ mul k 0` (via plus 0 x ι→ x). Goes through on the open scrutinee
    // because Nat is non-indexed (driver:106 indexed-field gate does not bite).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &mul_n_o(), &mul_n_o_ty()).is_ok(),
        "mul_n_O : Π(n:Nat). Id Nat (mul n 0) 0  (induction on n)"
    );
}

#[test]
fn false_mul_n_o_rejected() {
    // NO-FALSE-GREEN: `∀n. n*0 = succ 0` is FALSE. The SAME skeleton at the false motive fails:
    // its base needs `refl Nat 0 : Id Nat (mul 0 0) (succ 0) ≡ Id Nat 0 (succ 0)`, rejected.
    let env = env();
    let bad_motive = lam(nat_ty(), id_nat(mul(Tm::Var(0), zero()), succ(zero())));
    let bad_step = lam(
        nat_ty(),
        lam(id_nat(mul(Tm::Var(0), zero()), succ(zero())), Tm::Var(0)),
    );
    let bad = lam(
        nat_ty(),
        apps(
            Tm::Elim(NAT),
            &[bad_motive, refl_nat(zero()), bad_step, Tm::Var(0)],
        ),
    );
    let bad_ty = pi(nat_ty(), id_nat(mul(Tm::Var(0), zero()), succ(zero())));
    assert_eq!(
        check(&env, &Vec::new(), &bad, &bad_ty),
        Err(TypeError::Mismatch),
        "∀n. n*0 = 1 is FALSE — base case rejected (no false-green)"
    );
}

#[test]
fn building_blocks_typecheck() {
    // The derived combinators (the proofs' tools beyond Nat.rec) before the theorems.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &ap_succ(), &ap_succ_ty()).is_ok(),
        "ap_succ : Π(a b:Nat)(p:Id Nat a b). Id Nat (succ a)(succ b)"
    );
    assert!(
        check(&env, &Vec::new(), &ap_plus_l(), &ap_plus_l_ty()).is_ok(),
        "ap_plus_l : Π(c a b:Nat)(p:Id Nat a b). Id Nat (plus c a)(plus c b)  (J / Elim Id)"
    );
    assert!(
        check(&env, &Vec::new(), &eq_trans(), &eq_trans_ty()).is_ok(),
        "eq_trans : Π(A)(a b c:A)(p:Id A a b)(q:Id A b c). Id A a c"
    );
    assert!(
        check(&env, &Vec::new(), &eq_sym(), &eq_sym_ty()).is_ok(),
        "eq_sym : Π(A)(a b:A)(p:Id A a b). Id A b a"
    );
    assert!(
        check(&env, &Vec::new(), &add_comm(), &add_comm_ty()).is_ok(),
        "add_comm : Π(m n:Nat). Id Nat (plus m n)(plus n m)"
    );
    assert!(
        check(&env, &Vec::new(), &add_assoc_l(), &add_assoc_l_ty()).is_ok(),
        "add_assoc_l : Π(x y z:Nat). Id Nat ((x+y)+z) (x+(y+z))  (FIRST-arg induction)"
    );
}
fn add_comm_ty() -> Tm {
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            id_nat(plus(Tm::Var(1), Tm::Var(0)), plus(Tm::Var(0), Tm::Var(1))),
        ),
    )
}

// ════════════════════════ mul_succ_r — ∀m n. m * (succ n) = m*n + m ════════════════════════

/// mul_succ_r := λm n. Nat.rec
///     (λm'. Id Nat (mul m' (succ n)) (plus (mul m' n) m'))                       -- motive
///     (refl Nat 0)                                                               -- base m=0
///     (λk ih. <chain>)                                                           -- step m=succ k
///     m
///
/// Induction on m (the arg `mul` recurses on).
///   Base m=0: `mul 0 (succ n) ι→ 0`; `plus (mul 0 n) 0 ≡ plus 0 0 ι→ 0`. Goal `Id Nat 0 0` = refl.
///   Step m=succ k, ih : Id Nat (mul k (succ n)) (plus (mul k n) k):
///     LHS `mul (succ k)(succ n)` ι→ `succ (plus n (mul k (succ n)))`.
///     RHS `plus (mul (succ k) n)(succ k)` ι→ `plus (plus n (mul k n))(succ k)`.
///     chain (eq_trans, left→right), goal `Id Nat (succ (plus n (mul k(succ n)))) (plus (plus n (mul k n))(succ k))`:
///       p1 = ap_succ (ap_plus_l n (mul k(succ n)) (plus (mul k n) k) ih)  -- IH CONSUMED
///            : succ(plus n (mul k(succ n))) = succ(plus n (plus (mul k n) k))
///       p2 = ap_succ (eq_sym (add_assoc_l n (mul k n) k))
///            : succ(plus n (plus (mul k n) k)) = succ(plus (plus n (mul k n)) k)
///       p3 = plus_n_Sm (plus n (mul k n)) k
///            : succ(plus (plus n (mul k n)) k) = plus (plus n (mul k n))(succ k)
fn mul_succ_r() -> Tm {
    // motive λm'. Id Nat (mul m' (succ n)) (plus (mul m' n) m')   (ctx [m,n,m']: n=Var1, m'=Var0).
    let motive = lam(
        nat_ty(),
        id_nat(
            mul(Tm::Var(0), succ(Tm::Var(1))),             // mul m' (succ n)
            plus(mul(Tm::Var(0), Tm::Var(1)), Tm::Var(0)), // plus (mul m' n) m'
        ),
    );
    let base = refl_nat(zero()); // Id Nat 0 0
                                 // step λk.λih. <chain>   (ctx [m,n,k,ih]: n=Var2, k=Var1, ih=Var0).
    let step = lam(
        nat_ty(), // k
        lam(
            // ih : motive k   (ctx [m,n,k]: n=Var1, k=Var0).
            id_nat(
                mul(Tm::Var(0), succ(Tm::Var(1))),
                plus(mul(Tm::Var(0), Tm::Var(1)), Tm::Var(0)),
            ),
            // ctx [m,n,k,ih]: n=Var2, k=Var1, ih=Var0.
            {
                let mksn = mul(Tm::Var(1), succ(Tm::Var(2))); // mul k (succ n)
                let mkn = mul(Tm::Var(1), Tm::Var(2)); // mul k n
                let n = Tm::Var(2);
                let k = Tm::Var(1);
                // p1 : succ(plus n mksn) = succ(plus n (plus mkn k))
                let p1 = ap_succ_at(
                    plus(n.clone(), mksn.clone()),
                    plus(n.clone(), plus(mkn.clone(), k.clone())),
                    ap_plus_l_at(
                        n.clone(),
                        mksn.clone(),
                        plus(mkn.clone(), k.clone()),
                        Tm::Var(0), // ih  (CONSUMED)
                    ),
                );
                // p2 : succ(plus n (plus mkn k)) = succ(plus (plus n mkn) k)
                let p2 = ap_succ_at(
                    plus(n.clone(), plus(mkn.clone(), k.clone())),
                    plus(plus(n.clone(), mkn.clone()), k.clone()),
                    eq_sym_nat(
                        plus(plus(n.clone(), mkn.clone()), k.clone()),
                        plus(n.clone(), plus(mkn.clone(), k.clone())),
                        add_assoc_l_at(n.clone(), mkn.clone(), k.clone()),
                    ),
                );
                // p3 : succ(plus (plus n mkn) k) = plus (plus n mkn)(succ k)
                let p3 = plus_n_sm_at(plus(n.clone(), mkn.clone()), k.clone());
                let inner = trans_nat(
                    succ(plus(n.clone(), mksn.clone())),
                    succ(plus(n.clone(), plus(mkn.clone(), k.clone()))),
                    succ(plus(plus(n.clone(), mkn.clone()), k.clone())),
                    p1,
                    p2,
                );
                trans_nat(
                    succ(plus(n.clone(), mksn)),
                    succ(plus(plus(n.clone(), mkn.clone()), k.clone())),
                    plus(plus(n, mkn), succ(k)),
                    inner,
                    p3,
                )
            },
        ),
    );
    let rec = apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(1)]); // scrut m
    lam(nat_ty(), lam(nat_ty(), rec))
}
fn mul_succ_r_ty() -> Tm {
    // Π(m n:Nat). Id Nat (mul m (succ n)) (plus (mul m n) m)   (ctx [m,n]: m=Var1, n=Var0).
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            id_nat(
                mul(Tm::Var(1), succ(Tm::Var(0))),
                plus(mul(Tm::Var(1), Tm::Var(0)), Tm::Var(1)),
            ),
        ),
    )
}
fn mul_succ_r_at(m: Tm, n: Tm) -> Tm {
    apps(mul_succ_r(), &[m, n])
}

#[test]
fn mul_succ_r_typechecks() {
    // ∀m n. m*(succ n) = m*n + m — GENERAL, induction on m. The one fiddly plus-shuffle lemma:
    // IH consumed via ap_plus_l, re-associated with add_assoc_l (first-arg), closed with plus_n_Sm.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &mul_succ_r(), &mul_succ_r_ty()).is_ok(),
        "mul_succ_r : Π(m n:Nat). Id Nat (mul m (succ n)) (plus (mul m n) m)  (induction on m)"
    );
}

// ════════════════════════ mul_comm — ∀m n. m * n = n * m ════════════════════════

/// mul_comm := λm n. Nat.rec
///     (λm'. Id Nat (mul m' n) (mul n m'))                                        -- motive
///     (eq_sym (mul_n_O n))                                                       -- base m=0
///     (λk ih. <chain>)                                                           -- step m=succ k
///     m
///
/// Induction on m.  Base m=0: goal `Id Nat (mul 0 n)(mul n 0)` ≡ `Id Nat 0 (mul n 0)`;
///   `mul_n_O n : Id Nat (mul n 0) 0`, eq_sym ⟹ `Id Nat 0 (mul n 0)`.
/// Step m=succ k, ih : Id Nat (mul k n)(mul n k):
///   goal `Id Nat (mul (succ k) n)(mul n (succ k))`; LHS ι→ `plus n (mul k n)`.
///   s1 = ap_plus_l n (mul k n)(mul n k) ih : plus n (mul k n) = plus n (mul n k)   -- IH CONSUMED
///   s2 = add_comm n (mul n k)             : plus n (mul n k) = plus (mul n k) n
///   s3 = eq_sym (mul_succ_r n k)          : plus (mul n k) n = mul n (succ k)
///   eq_trans chains them ⟹ plus n (mul k n) = mul n (succ k) ≡ goal (LHS ι-eq).
fn mul_comm() -> Tm {
    // motive λm'. Id Nat (mul m' n) (mul n m')   (ctx [m,n,m']: n=Var1, m'=Var0).
    let motive = lam(
        nat_ty(),
        id_nat(mul(Tm::Var(0), Tm::Var(1)), mul(Tm::Var(1), Tm::Var(0))),
    );
    // base m=0: eq_sym (mul_n_O n)   (ctx [m,n]: n=Var0).
    let base = eq_sym_nat(mul(Tm::Var(0), zero()), zero(), app(mul_n_o(), Tm::Var(0)));
    // step λk.λih. <chain>   (ctx [m,n,k,ih]: n=Var2, k=Var1, ih=Var0).
    let step = lam(
        nat_ty(), // k
        lam(
            // ih : motive k   (ctx [m,n,k]: n=Var1, k=Var0).
            id_nat(mul(Tm::Var(0), Tm::Var(1)), mul(Tm::Var(1), Tm::Var(0))),
            {
                let n = Tm::Var(2);
                let k = Tm::Var(1);
                let mkn = mul(Tm::Var(1), Tm::Var(2)); // mul k n
                let mnk = mul(Tm::Var(2), Tm::Var(1)); // mul n k
                                                       // s1 : plus n (mul k n) = plus n (mul n k)
                let s1 = ap_plus_l_at(n.clone(), mkn.clone(), mnk.clone(), Tm::Var(0));
                // s2 : plus n (mul n k) = plus (mul n k) n
                let s2 = add_comm_at(n.clone(), mnk.clone());
                // s3 : plus (mul n k) n = mul n (succ k)
                let s3 = eq_sym_nat(
                    mul(n.clone(), succ(k.clone())),
                    plus(mnk.clone(), n.clone()),
                    mul_succ_r_at(n.clone(), k.clone()),
                );
                let inner = trans_nat(
                    plus(n.clone(), mkn.clone()),
                    plus(n.clone(), mnk.clone()),
                    plus(mnk.clone(), n.clone()),
                    s1,
                    s2,
                );
                trans_nat(
                    plus(n.clone(), mkn),
                    plus(mnk, n.clone()),
                    mul(n, succ(k)),
                    inner,
                    s3,
                )
            },
        ),
    );
    let rec = apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(1)]); // scrut m
    lam(nat_ty(), lam(nat_ty(), rec))
}
fn mul_comm_ty() -> Tm {
    // Π(m n:Nat). Id Nat (mul m n) (mul n m)   (ctx [m,n]: m=Var1, n=Var0).
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            id_nat(mul(Tm::Var(1), Tm::Var(0)), mul(Tm::Var(0), Tm::Var(1))),
        ),
    )
}

#[test]
fn mul_comm_typechecks() {
    // THE marquee arithmetic theorem: ∀m n. m * n = n * m — GENERAL, machine-checked.
    // Induction on m; base via mul_n_O+eq_sym; step CONSUMES the IH via ap_plus_l and chains with
    // add_comm + mul_succ_r through eq_trans. Nat non-indexed (nidx==0) ⇒ driver:106 does not bite.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &mul_comm(), &mul_comm_ty()).is_ok(),
        "mul_comm : Π(m n:Nat). Id Nat (mul m n) (mul n m)  (induction on m; IH consumed)"
    );
}

#[test]
fn false_mul_comm_rejected() {
    // NO-FALSE-GREEN: `mul_comm` does NOT inhabit the off-by-one `∀m n. m*n = succ (n*m)`.
    let env = env();
    let bad_ty = pi(
        nat_ty(),
        pi(
            nat_ty(),
            id_nat(
                mul(Tm::Var(1), Tm::Var(0)),
                succ(mul(Tm::Var(0), Tm::Var(1))),
            ),
        ),
    );
    assert!(
        check(&env, &Vec::new(), &mul_comm(), &bad_ty).is_err(),
        "mul_comm does NOT inhabit ∀m n. m*n = succ(n*m) (off by one)"
    );
}

// ════════════════════════ mul_add_distrib_r — ∀a b c. (a+b)*c = a*c + b*c ════════════════════════

/// mul_add_distrib_r := λa b c. Nat.rec
///     (λa'. Id Nat (mul (plus a' b) c) (plus (mul a' c) (mul b c)))              -- motive
///     (refl Nat (mul b c))                                                       -- base a=0
///     (λk ih. <chain>)                                                           -- step a=succ k
///     a
///
/// Right-distributivity, induction on a (lines up with both `plus`/`mul` first-arg recursion).
///   Base a=0: `plus 0 b ι→ b` ⇒ LHS `mul b c`; RHS `plus 0 (mul b c) ι→ mul b c`. refl (DEFINITIONAL).
///   Step a=succ k, ih : Id Nat (mul (plus k b) c) (plus (mul k c)(mul b c)):
///     LHS `mul (plus (succ k) b) c` ι→ `plus c (mul (plus k b) c)`,
///     RHS `plus (mul (succ k) c)(mul b c)` ι→ `plus (plus c (mul k c))(mul b c)`,
///     s1 = ap_plus_l c (mul (plus k b) c) (plus (mul k c)(mul b c)) ih   -- IH CONSUMED
///        : plus c (mul (plus k b) c) = plus c (plus (mul k c)(mul b c))
///     s2 = eq_sym (add_assoc_l c (mul k c)(mul b c))
///        : plus c (plus (mul k c)(mul b c)) = plus (plus c (mul k c))(mul b c)
///     eq_trans chains them ⟹ goal (both sides ι-eq).
fn mul_add_distrib_r() -> Tm {
    // motive λa'. Id Nat (mul (plus a' b) c) (plus (mul a' c)(mul b c))   (ctx [a,b,c,a']: b=Var2, c=Var1, a'=Var0).
    let motive = lam(
        nat_ty(),
        id_nat(
            mul(plus(Tm::Var(0), Tm::Var(2)), Tm::Var(1)), // mul (plus a' b) c
            plus(
                mul(Tm::Var(0), Tm::Var(1)), // mul a' c
                mul(Tm::Var(2), Tm::Var(1)), // mul b c
            ),
        ),
    );
    // base : refl Nat (mul b c)   (ctx [a,b,c]: b=Var1, c=Var0).
    let base = refl_nat(mul(Tm::Var(1), Tm::Var(0)));
    // step λk.λih. <chain>   (ctx [a,b,c,k,ih]: b=Var3, c=Var2, k=Var1, ih=Var0).
    let step = lam(
        nat_ty(), // k
        lam(
            // ih : motive k   (ctx [a,b,c,k]: b=Var2, c=Var1, k=Var0).
            id_nat(
                mul(plus(Tm::Var(0), Tm::Var(2)), Tm::Var(1)),
                plus(mul(Tm::Var(0), Tm::Var(1)), mul(Tm::Var(2), Tm::Var(1))),
            ),
            // ctx [a,b,c,k,ih]: b=Var3, c=Var2, k=Var1, ih=Var0.
            {
                let c = Tm::Var(2);
                let mkbc = mul(plus(Tm::Var(1), Tm::Var(3)), Tm::Var(2)); // mul (plus k b) c
                let mkc = mul(Tm::Var(1), Tm::Var(2)); // mul k c
                let mbc = mul(Tm::Var(3), Tm::Var(2)); // mul b c
                                                       // s1 : plus c (mul (plus k b) c) = plus c (plus (mul k c)(mul b c))
                let s1 = ap_plus_l_at(
                    c.clone(),
                    mkbc.clone(),
                    plus(mkc.clone(), mbc.clone()),
                    Tm::Var(0), // ih  (CONSUMED)
                );
                // s2 : plus c (plus (mul k c)(mul b c)) = plus (plus c (mul k c))(mul b c)
                let s2 = eq_sym_nat(
                    plus(plus(c.clone(), mkc.clone()), mbc.clone()),
                    plus(c.clone(), plus(mkc.clone(), mbc.clone())),
                    add_assoc_l_at(c.clone(), mkc.clone(), mbc.clone()),
                );
                trans_nat(
                    plus(c.clone(), mkbc),
                    plus(c.clone(), plus(mkc.clone(), mbc.clone())),
                    plus(plus(c, mkc), mbc),
                    s1,
                    s2,
                )
            },
        ),
    );
    let rec = apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(2)]); // scrut a
    lam(nat_ty(), lam(nat_ty(), lam(nat_ty(), rec)))
}
fn mul_add_distrib_r_ty() -> Tm {
    // Π(a b c:Nat). Id Nat (mul (plus a b) c) (plus (mul a c)(mul b c))   (ctx [a,b,c]: a=Var2, b=Var1, c=Var0).
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            pi(
                nat_ty(),
                id_nat(
                    mul(plus(Tm::Var(2), Tm::Var(1)), Tm::Var(0)),
                    plus(mul(Tm::Var(2), Tm::Var(0)), mul(Tm::Var(1), Tm::Var(0))),
                ),
            ),
        ),
    )
}

#[test]
fn mul_add_distrib_r_typechecks() {
    // THE theorem: ∀a b c. (a+b)*c = a*c + b*c — GENERAL, machine-checked. Induction on a; base
    // definitional; step CONSUMES the IH via ap_plus_l and re-associates with add_assoc_l (the
    // FIRST-arg orientation — next-theorems-design.md §2.1a — which keeps the open recursive field
    // off the empty-ctx re-infer path, so the driver:106 indexed-field gate never bites).
    let env = env();
    assert!(
        check(
            &env,
            &Vec::new(),
            &mul_add_distrib_r(),
            &mul_add_distrib_r_ty()
        )
        .is_ok(),
        "mul_add_distrib_r : Π(a b c:Nat). Id Nat (mul (plus a b) c) (plus (mul a c)(mul b c))"
    );
}

#[test]
fn false_mul_add_distrib_r_rejected() {
    // NO-FALSE-GREEN: `(a+b)*c = a*c + a*c` (b→a on the rhs second factor) is FALSE.
    let env = env();
    let bad_ty = pi(
        nat_ty(),
        pi(
            nat_ty(),
            pi(
                nat_ty(),
                id_nat(
                    mul(plus(Tm::Var(2), Tm::Var(1)), Tm::Var(0)),
                    plus(
                        mul(Tm::Var(2), Tm::Var(0)),
                        mul(Tm::Var(2), Tm::Var(0)), // a*c (should be b*c)
                    ),
                ),
            ),
        ),
    );
    assert_eq!(
        check(&env, &Vec::new(), &mul_add_distrib_r(), &bad_ty),
        Err(TypeError::Mismatch),
        "mul_add_distrib_r does NOT prove (a+b)*c = a*c + a*c  (no false-green)"
    );
}
