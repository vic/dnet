//! Verified Nat algebra on the dnx-proof kernel — the unit/shuffle laws around the proven
//! `∀n. n+0 = n` (thm_plus_n_o.rs), culminating in COMMUTATIVITY `∀m n. m+n = n+m`.
//!
//! All proofs are `Nat.rec` inductions (proofs.md:163-188) closed with the `Id`/`refl`
//! prelude and the J-derived congruence `ap_succ` + transitivity `eq_trans`
//! (eq_prelude.rs:166-312). NO new axioms: every term is `check`ed at its ∀-type by the
//! trusted kernel, so the kernel itself is the oracle.
//!
//! `plus` recurses on its FIRST argument (`plus 0 b = b`, `plus (succ k) b = succ (plus k b)`;
//! same as thm_plus_n_o.rs), and `Nat` is non-indexed (`nidx == 0`), so the ι-driver fires on
//! OPEN scrutinees (driver.rs:104-119 `field_indices` fast-path) — this is exactly why the
//! genuine inductive steps below go through without hitting the `driver.rs:106` open-INDEXED-
//! field limitation (that gate only bites indexed families like `Vec`; thm_induction.rs:404).
//!
//! THEOREMS (all GENERAL, ∀-quantified, machine-checked):
//!   • zero_plus_n : ∀n.        0 + n = n                (definitional: plus 0 n ι→ n)
//!   • plus_n_Sm   : ∀m n.      succ(m+n) = m + succ n   (induction on m; IH via ap_succ)
//!   • add_comm    : ∀m n.      m + n = n + m            (induction on m; uses both lemmas)
//!
//! NO-FALSE-GREEN: the off-by-one companions are REJECTED by `check` (asserted per theorem).

use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::{check, TypeError};
use dnx_proof::symbol::{ConstId, IndId};
use dnx_proof::tm::Tm;

// ── term helpers (same idioms as eq_prelude.rs / thm_plus_n_o.rs) ──
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

// Id : Π(A:Type₀)(a:A). A → Type₀ ; refl A a : Id A a a   (eq_prelude.rs:49-61).
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
// Id Nat a b  and  refl Nat a   (closed builders, the only equality we need here).
fn id_nat(a: Tm, b: Tm) -> Tm {
    apps(Tm::Ind(ID), &[nat_ty(), a, b])
}
fn refl_nat(a: Tm) -> Tm {
    apps(Tm::Ctor(ID, 0), &[nat_ty(), a])
}

// plus := λa:Nat.λb:Nat. Elim Nat (λ_:Nat.Nat) b (λk.λih. succ ih) a   — recursion on the FIRST arg.
//   plus 0 b ι→ b ;  plus (succ k) b ι→ succ (plus k b).   (thm_plus_n_o.rs:83-97.)
fn plus_body() -> Tm {
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

fn env() -> dnx_proof::env::GlobalEnv {
    let mut e = dnx_proof::env::GlobalEnv::default();
    e.add_inductive(nat()).expect("Nat admits");
    e.add_inductive(id_ind())
        .expect("Id admits (indexed inductive, Vec mould)");
    e.add_const(PLUS, plus_ty(), plus_body())
        .expect("plus admits (δ-acyclic)");
    e
}

// ════════════════════════ derived equality combinators (from J / Elim Id) ════════════════════════
// ap_succ and eq_trans are derived EXACTLY as in eq_prelude.rs / thm_induction.rs (proofs.md:177-188);
// reproduced here closed at Nat so each theorem file is self-contained.

/// ap_succ : Π(a b:Nat)(p:Id Nat a b). Id Nat (succ a) (succ b)
///   = λa b p. Elim Id Nat a (λb' x. Id Nat (succ a) (succ b')) (refl Nat (succ a)) b p
fn ap_succ() -> Tm {
    // ctx [a,b,p]: a=Var2, b=Var1, p=Var0.
    let motive = lam(
        nat_ty(), // b' : Nat
        lam(
            id_nat(Tm::Var(3), Tm::Var(0)), // x : Id Nat a b'   (a=Var3, b'=Var0)
            id_nat(succ(Tm::Var(4)), succ(Tm::Var(1))), // Id Nat (succ a)(succ b')  (a=Var4, b'=Var1)
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            nat_ty(),
            Tm::Var(2), // a
            motive,
            refl_nat(succ(Tm::Var(2))), // minor_refl = refl Nat (succ a)
            Tm::Var(1),                 // index b
            Tm::Var(0),                 // scrutinee p
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

/// eq_trans : Π(A:Type₀)(a b c:A)(p:Id A a b)(q:Id A b c). Id A a c   (eq_prelude.rs:255-291).
fn eq_trans() -> Tm {
    // ctx [A,a,b,c,p,q]: A=Var5,a=Var4,b=Var3,c=Var2,p=Var1,q=Var0.
    let motive = lam(
        Tm::Var(5), // c' : A
        lam(
            apps(Tm::Ind(ID), &[Tm::Var(6), Tm::Var(4), Tm::Var(0)]), // x : Id A b c'
            apps(Tm::Ind(ID), &[Tm::Var(7), Tm::Var(6), Tm::Var(1)]), // Id A a c'
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            Tm::Var(5), // A
            Tm::Var(3), // b  (recursor based at b)
            motive,
            Tm::Var(1), // minor_refl = p : Id A a b
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
                        apps(Tm::Ind(ID), &[Tm::Var(3), Tm::Var(2), Tm::Var(1)]), // p:Id A a b
                        lam(
                            apps(Tm::Ind(ID), &[Tm::Var(4), Tm::Var(2), Tm::Var(1)]),
                            body,
                        ), // q:Id A b c
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
/// `eq_trans Nat a b c p q : Id Nat a c`  (concrete, the only instantiation used below).
fn trans_nat(a: Tm, b: Tm, c: Tm, p: Tm, q: Tm) -> Tm {
    apps(eq_trans(), &[nat_ty(), a, b, c, p, q])
}

#[test]
fn building_blocks_typecheck() {
    // Pin the two derived combinators (the proof's only tools beyond Nat.rec) before the theorems.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &ap_succ(), &ap_succ_ty()).is_ok(),
        "ap_succ : Π(a b:Nat)(p:Id Nat a b). Id Nat (succ a)(succ b)  (J / Elim Id)"
    );
    assert!(
        check(&env, &Vec::new(), &eq_trans(), &eq_trans_ty()).is_ok(),
        "eq_trans : Π(A)(a b c:A)(p:Id A a b)(q:Id A b c). Id A a c  (J / Elim Id)"
    );
    assert!(
        check(&env, &Vec::new(), &eq_sym(), &eq_sym_ty()).is_ok(),
        "eq_sym : Π(A)(a b:A)(p:Id A a b). Id A b a  (J / Elim Id; the add_comm base-case tool)"
    );
}

// ════════════════════════ A1 — ∀n. 0 + n = n  (the OTHER unit law) ════════════════════════

/// zero_plus_n := λn:Nat. refl Nat n   :   Π(n:Nat). Id Nat (plus 0 n) n.
/// `plus 0 n` ι-reduces to `n` (the zero-minor of the first-arg recursion), so this unit law
/// is DEFINITIONAL — `refl Nat n` inhabits it under conv. (Contrast `plus n 0`, stuck on the
/// neutral `n`, which needs genuine induction — thm_plus_n_o.rs.)
fn zero_plus_n() -> Tm {
    lam(nat_ty(), refl_nat(Tm::Var(0)))
}
fn zero_plus_n_ty() -> Tm {
    pi(nat_ty(), id_nat(plus(zero(), Tm::Var(0)), Tm::Var(0)))
}

#[test]
fn zero_plus_n_typechecks() {
    // ∀n. 0 + n = n — GENERAL. Holds definitionally (ι on the first-arg zero-minor).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &zero_plus_n(), &zero_plus_n_ty()).is_ok(),
        "zero_plus_n : Π(n:Nat). Id Nat (plus 0 n) n  (definitional, plus 0 n ι→ n)"
    );
}

#[test]
fn false_zero_plus_n_rejected() {
    // NO-FALSE-GREEN: `∀n. 0 + n = succ n` is FALSE; `refl Nat n : Id Nat n n` cannot inhabit
    // `Id Nat (plus 0 n) (succ n) ≡ Id Nat n (succ n)`.
    let env = env();
    let bad_ty = pi(nat_ty(), id_nat(plus(zero(), Tm::Var(0)), succ(Tm::Var(0))));
    assert_eq!(
        check(&env, &Vec::new(), &zero_plus_n(), &bad_ty),
        Err(TypeError::Mismatch),
        "∀n. 0+n = succ n is FALSE — refl rejected"
    );
}

// ════════════════════════ A2 — ∀m n. succ(m+n) = m + succ n  (the shuffle lemma) ════════════════════════

/// plus_n_Sm := λm n. Nat.rec (λm'. Id Nat (succ (plus m' n)) (plus m' (succ n)))
///                            (refl Nat (succ n))                                   -- base m=0
///                            (λk ih. ap_succ (succ (plus k n)) (plus k (succ n)) ih) -- step
///                            m
/// Induction on m (the arg `plus` recurses on). Base m=0: `succ(plus 0 n) ≡ succ n` and
/// `plus 0 (succ n) ≡ succ n` — both ι-reduce, goal is `refl Nat (succ n)`. Step m=succ k:
///   goal `succ(plus (succ k) n) = plus (succ k)(succ n)` ≡ `succ(succ(plus k n)) = succ(plus k (succ n))`
///   (both sides ι through the first-arg succ-minor), so `ap_succ … ih` closes it — the IH is
///   CONSUMED. Same shape as plus_n_O (IH used only through congruence; no open-INDEXED-field ι).
fn plus_n_sm() -> Tm {
    // motive λm'. Id Nat (succ (plus m' n)) (plus m' (succ n))   (ctx [m,n,m']: n=Var1, m'=Var0).
    let motive = lam(
        nat_ty(),
        id_nat(
            succ(plus(Tm::Var(0), Tm::Var(1))), // succ (plus m' n)
            plus(Tm::Var(0), succ(Tm::Var(1))), // plus m' (succ n)
        ),
    );
    let base = refl_nat(succ(Tm::Var(0))); // refl Nat (succ n)   (ctx [m,n]: n=Var0)
                                           // step λk.λih. ap_succ (succ (plus k n)) (plus k (succ n)) ih   (ctx [m,n,k,ih]: n=Var2,k=Var1,ih=Var0).
    let step = lam(
        nat_ty(), // k
        lam(
            // ih : motive k = Id Nat (succ (plus k n)) (plus k (succ n))   (ctx [m,n,k]: n=Var1,k=Var0)
            id_nat(
                succ(plus(Tm::Var(0), Tm::Var(1))),
                plus(Tm::Var(0), succ(Tm::Var(1))),
            ),
            ap_succ_at(
                succ(plus(Tm::Var(1), Tm::Var(2))), // succ (plus k n)
                plus(Tm::Var(1), succ(Tm::Var(2))), // plus k (succ n)
                Tm::Var(0),                         // ih  (CONSUMED)
            ),
        ),
    );
    let rec = apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(1)]); // scrutinee m
    lam(nat_ty(), lam(nat_ty(), rec))
}
fn plus_n_sm_ty() -> Tm {
    // Π(m n:Nat). Id Nat (succ (plus m n)) (plus m (succ n))   (ctx [m,n]: m=Var1,n=Var0).
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            id_nat(
                succ(plus(Tm::Var(1), Tm::Var(0))),
                plus(Tm::Var(1), succ(Tm::Var(0))),
            ),
        ),
    )
}
/// `plus_n_Sm m n : Id Nat (succ (plus m n)) (plus m (succ n))`  (concrete instance).
fn plus_n_sm_at(m: Tm, n: Tm) -> Tm {
    apps(plus_n_sm(), &[m, n])
}

#[test]
fn plus_n_sm_typechecks() {
    // ∀m n. succ(m+n) = m + succ n — GENERAL, by Nat.rec induction on m; IH consumed via ap_succ.
    // plus_n_O-shaped (no open-INDEXED-field ι), so the driver:106 gate does NOT bite.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &plus_n_sm(), &plus_n_sm_ty()).is_ok(),
        "plus_n_Sm : Π(m n:Nat). Id Nat (succ (plus m n)) (plus m (succ n))  (induction on m)"
    );
}

#[test]
fn false_plus_n_sm_rejected() {
    // NO-FALSE-GREEN: `∀m n. succ(m+n) = m + n` (drop the succ on the rhs) is FALSE — the base
    // case would need `refl Nat (succ n) : Id Nat (succ n) n`, which `check` rejects.
    let env = env();
    let bad_motive = lam(
        nat_ty(),
        id_nat(
            succ(plus(Tm::Var(0), Tm::Var(1))),
            plus(Tm::Var(0), Tm::Var(1)),
        ),
    );
    let bad_base = refl_nat(succ(Tm::Var(0)));
    let bad_step = lam(
        nat_ty(),
        lam(
            id_nat(
                succ(plus(Tm::Var(0), Tm::Var(1))),
                plus(Tm::Var(0), Tm::Var(1)),
            ),
            ap_succ_at(
                succ(plus(Tm::Var(1), Tm::Var(2))),
                plus(Tm::Var(1), Tm::Var(2)),
                Tm::Var(0),
            ),
        ),
    );
    let bad = lam(
        nat_ty(),
        lam(
            nat_ty(),
            apps(Tm::Elim(NAT), &[bad_motive, bad_base, bad_step, Tm::Var(1)]),
        ),
    );
    let bad_ty = pi(
        nat_ty(),
        pi(
            nat_ty(),
            id_nat(
                succ(plus(Tm::Var(1), Tm::Var(0))),
                plus(Tm::Var(1), Tm::Var(0)),
            ),
        ),
    );
    assert_eq!(
        check(&env, &Vec::new(), &bad, &bad_ty),
        Err(TypeError::Mismatch),
        "∀m n. succ(m+n) = m+n is FALSE — base case rejected (no false-green)"
    );
}

// ════════════════════════ add_comm — ∀m n. m + n = n + m ════════════════════════

/// add_comm := λm n. Nat.rec
///     (λm'. Id Nat (plus m' n) (plus n m'))                        -- motive
///     (zero_plus_n_sym n)                                          -- base m=0:  n = plus n 0
///     (λk ih. step)                                                -- step m=succ k
///     m
///
/// Base m=0: goal `Id Nat (plus 0 n) (plus n 0)` ≡ `Id Nat n (plus n 0)`. We supply
///   eq_sym (plus_n_O n) — but to stay self-contained we instead use the proven `plus n 0 = n`
///   route via eq_trans; concretely the base witness is `eq_sym Nat (plus n 0) n (plus_n_O n)`.
///   To avoid re-deriving eq_sym here we phrase the base as a transitivity that needs only
///   plus_n_O and refl (see `base` below).
///
/// Step m=succ k: goal `Id Nat (plus (succ k) n) (plus n (succ k))`.
///   LHS `plus (succ k) n` ι→ `succ (plus k n)`.
///   IH `ih : Id Nat (plus k n) (plus n k)`.
///   `ap_succ … ih : Id Nat (succ (plus k n)) (succ (plus n k))`.
///   `plus_n_Sm n k : Id Nat (succ (plus n k)) (plus n (succ k))`.
///   eq_trans chains them: `Id Nat (succ (plus k n)) (plus n (succ k))` ≡ the goal (LHS ι-eq).
///   The IH is genuinely CONSUMED (inside `ap_succ`).
///
/// The base needs `plus n 0 = n` (plus_n_O, recursion-on-first-arg STUCK on neutral n). We take
/// it as a hypothesis-free derived term: `plus_n_o n` below (a local copy of thm_plus_n_o.rs).
fn plus_n_o() -> Tm {
    // λn. Nat.rec (λm. Id Nat (plus m 0) m) (refl Nat 0) (λk ih. ap_succ (plus k 0) k ih) n
    let motive = lam(nat_ty(), id_nat(plus(Tm::Var(0), zero()), Tm::Var(0)));
    let base = refl_nat(zero()); // Id Nat (plus 0 0) 0 ≡ Id Nat 0 0
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
/// `plus_n_O n : Id Nat (plus n 0) n`.
fn plus_n_o_at(n: Tm) -> Tm {
    app(plus_n_o(), n)
}

/// eq_sym : Π(A:Type₀)(a b:A)(p:Id A a b). Id A b a   — the CLOSED J-derived combinator
/// (eq_prelude.rs:166-202), reproduced here. We apply it (no manual de Bruijn shifting of the
/// captured args — substitution does that), then specialise at A:=Nat in `eq_sym_nat`.
fn eq_sym() -> Tm {
    // ctx [A,a,b,p]: A=Var3,a=Var2,b=Var1,p=Var0.
    let motive = lam(
        Tm::Var(3), // b' : A
        lam(
            apps(Tm::Ind(ID), &[Tm::Var(4), Tm::Var(3), Tm::Var(0)]), // x : Id A a b'
            apps(Tm::Ind(ID), &[Tm::Var(5), Tm::Var(1), Tm::Var(4)]), // Id A b' a
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            Tm::Var(3), // A
            Tm::Var(2), // a
            motive,
            apps(Tm::Ctor(ID, 0), &[Tm::Var(3), Tm::Var(2)]), // minor_refl = refl A a
            Tm::Var(1),                                       // index b
            Tm::Var(0),                                       // scrutinee p
        ],
    );
    lam(
        Tm::Sort(0),
        lam(
            Tm::Var(0), // a : A
            lam(
                Tm::Var(1), // b : A
                lam(
                    apps(Tm::Ind(ID), &[Tm::Var(2), Tm::Var(1), Tm::Var(0)]),
                    body,
                ), // p : Id A a b
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
/// `eq_sym Nat a b p : Id Nat b a`  (concrete instantiation at A:=Nat).
fn eq_sym_nat(a: Tm, b: Tm, p: Tm) -> Tm {
    apps(eq_sym(), &[nat_ty(), a, b, p])
}

fn add_comm() -> Tm {
    // motive λm'. Id Nat (plus m' n) (plus n m')   (ctx [m,n,m']: n=Var1, m'=Var0).
    let motive = lam(
        nat_ty(),
        id_nat(plus(Tm::Var(0), Tm::Var(1)), plus(Tm::Var(1), Tm::Var(0))),
    );
    // base m=0: goal Id Nat (plus 0 n) (plus n 0) ≡ Id Nat n (plus n 0).
    //   plus_n_O n : Id Nat (plus n 0) n  ⟹  eq_sym : Id Nat n (plus n 0).   (ctx [m,n]: n=Var0)
    let base = eq_sym_nat(
        plus(Tm::Var(0), zero()),
        Tm::Var(0),
        plus_n_o_at(Tm::Var(0)),
    );
    // step λk.λih. ...   (ctx [m,n,k,ih]: n=Var2, k=Var1, ih=Var0).
    let step = lam(
        nat_ty(), // k
        lam(
            // ih : motive k = Id Nat (plus k n) (plus n k)   (ctx [m,n,k]: n=Var1, k=Var0)
            id_nat(plus(Tm::Var(0), Tm::Var(1)), plus(Tm::Var(1), Tm::Var(0))),
            // ctx [m,n,k,ih]: n=Var2, k=Var1, ih=Var0.
            // s1 = ap_succ (plus k n) (plus n k) ih : Id Nat (succ (plus k n)) (succ (plus n k)).
            // s2 = plus_n_Sm n k          : Id Nat (succ (plus n k)) (plus n (succ k)).
            // goal Id Nat (plus (succ k) n) (plus n (succ k)) ≡ Id Nat (succ (plus k n)) (plus n (succ k))
            //   (LHS ι: plus (succ k) n → succ (plus k n)).
            // eq_trans Nat (succ (plus k n)) (succ (plus n k)) (plus n (succ k)) s1 s2.
            trans_nat(
                succ(plus(Tm::Var(1), Tm::Var(2))), // succ (plus k n)
                succ(plus(Tm::Var(2), Tm::Var(1))), // succ (plus n k)
                plus(Tm::Var(2), succ(Tm::Var(1))), // plus n (succ k)
                ap_succ_at(
                    plus(Tm::Var(1), Tm::Var(2)), // plus k n
                    plus(Tm::Var(2), Tm::Var(1)), // plus n k
                    Tm::Var(0),                   // ih  (CONSUMED)
                ),
                plus_n_sm_at(Tm::Var(2), Tm::Var(1)), // plus_n_Sm n k
            ),
        ),
    );
    let rec = apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(1)]); // scrutinee m
    lam(nat_ty(), lam(nat_ty(), rec))
}
fn add_comm_ty() -> Tm {
    // Π(m n:Nat). Id Nat (plus m n) (plus n m)   (ctx [m,n]: m=Var1, n=Var0).
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            id_nat(plus(Tm::Var(1), Tm::Var(0)), plus(Tm::Var(0), Tm::Var(1))),
        ),
    )
}

#[test]
fn plus_n_o_helper_typechecks() {
    // The base-case lemma (a local copy of thm_plus_n_o.rs's headline) at its ∀-type.
    let env = env();
    let ty = pi(nat_ty(), id_nat(plus(Tm::Var(0), zero()), Tm::Var(0)));
    assert!(
        check(&env, &Vec::new(), &plus_n_o(), &ty).is_ok(),
        "plus_n_O : Π(n:Nat). Id Nat (plus n 0) n  (base-case lemma for add_comm)"
    );
}

#[test]
fn add_comm_typechecks() {
    // THE marquee theorem: ∀m n. m + n = n + m — GENERAL, machine-checked.
    // Induction on m (Nat.rec): base via plus_n_O+eq_sym; step CONSUMES the IH via ap_succ and
    // chains with plus_n_Sm through eq_trans. Goes through because Nat is non-indexed (nidx==0):
    // the ι-driver fires on the open scrutinee/fields, so the driver:106 INDEXED-field gate
    // (thm_induction.rs:404) never bites — the IH is used only through congruence + transitivity.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &add_comm(), &add_comm_ty()).is_ok(),
        "add_comm : Π(m n:Nat). Id Nat (plus m n) (plus n m)  (induction on m; IH consumed)"
    );
}

#[test]
fn false_add_comm_rejected() {
    // NO-FALSE-GREEN: the SAME proof skeleton at the FALSE goal `∀m n. plus m n = succ (plus n m)`
    // fails to typecheck (the base/step no longer fit). We assert the off-by-one ∀-type is NOT
    // inhabited by `add_comm` (a sanity check that the type is load-bearing).
    let env = env();
    let bad_ty = pi(
        nat_ty(),
        pi(
            nat_ty(),
            id_nat(
                plus(Tm::Var(1), Tm::Var(0)),
                succ(plus(Tm::Var(0), Tm::Var(1))),
            ),
        ),
    );
    assert!(
        check(&env, &Vec::new(), &add_comm(), &bad_ty).is_err(),
        "add_comm does NOT inhabit ∀m n. m+n = succ(n+m) (off by one)"
    );
}
