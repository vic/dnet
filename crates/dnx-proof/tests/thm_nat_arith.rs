//! Nat arithmetic laws — `add_zero_r`, `add_succ_r`, `add_comm`, `add_assoc` — proven
//! end-to-end on the dnx-proof kernel by genuine `Nat.rec` induction.
//!
//! `Nat`/`zero`/`succ`, `Id`/`refl`, and the J-derived congruence/equality combinators
//! (`ap_succ`, `eq_sym`, `eq_trans`) are reproduced CLOSED here so the file is self-contained,
//! using the exact idioms of `thm_plus_n_o.rs` / `thm_nat_algebra.rs` / `thm_mul.rs`
//! (eq_prelude.rs:166-312; proofs.md:163-188). NO new axioms: every term is `check`ed at its
//! ∀-type by the trusted kernel, so the kernel itself is the oracle.
//!
//! `add` recurses on its FIRST argument (`add 0 b ι→ b`, `add (succ k) b ι→ succ (add k b)`;
//! the convention of thm_plus_n_o.rs:95-115). Hence:
//!   • `add n 0` is STUCK on the neutral `n` ⇒ `add_zero_r` demands induction (NOT definitional),
//!   • `add n (succ m)` is STUCK on the neutral `n` ⇒ `add_succ_r` demands induction,
//!   • `add_comm` then CONSUMES both lemmas + its IH.
//! `Nat` is non-indexed (`nidx == 0`), so the ι-driver fires on OPEN scrutinees/recursive fields
//! (driver.rs:109-112), which is why the inductive steps go through (thm_nat_algebra.rs:9-13).
//!
//! THEOREMS (all GENERAL, ∀-quantified, machine-checked at their type):
//!   • add_zero_r : ∀n.     add n 0 = n               (induction on n; IH via ap_succ)
//!   • add_succ_r : ∀n m.   add n (succ m) = succ (add n m)   (induction on n; IH via ap_succ)
//!   • add_comm   : ∀n m.   add n m = add m n         (induction on n; uses both lemmas + IH)
//!   • add_assoc  : ∀n m k. add (add n m) k = add n (add m k)  (induction on n; IH via ap_succ)
//!
//! NON-VACUITY: a CLOSED instance (`add 2 3`) ι-normalizes to the literal `5`, and the off-by-one
//! companions are REJECTED by `check` while the TRUE goals pass (positive control alongside every
//! negative) — so the green is not a vacuous-type artifact.

use dnx_proof::conv::conv;
use dnx_proof::driver::nf_tm;
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::{check, TypeError};
use dnx_proof::symbol::{ConstId, IndId};
use dnx_proof::tm::Tm;

// ── term helpers (same idioms as eq_prelude.rs / thm_plus_n_o.rs / thm_induction.rs) ──
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
const ADD: ConstId = ConstId(0);

fn nat_ty() -> Tm {
    Tm::Ind(NAT)
}
fn zero() -> Tm {
    Tm::Ctor(NAT, 0)
}
fn succ(n: Tm) -> Tm {
    app(Tm::Ctor(NAT, 1), n)
}
fn lit(n: u32) -> Tm {
    (0..n).fold(zero(), |acc, _| succ(acc))
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
// Id Nat a b   and   refl Nat a   (closed builders, the only equality we need here).
fn id_nat(a: Tm, b: Tm) -> Tm {
    apps(Tm::Ind(ID), &[nat_ty(), a, b])
}
fn refl_nat(a: Tm) -> Tm {
    apps(Tm::Ctor(ID, 0), &[nat_ty(), a])
}

// add := λa:Nat.λb:Nat. Elim Nat (λ_:Nat.Nat) b (λk.λih. succ ih) a   — recursion on the FIRST arg.
//   add 0 b ι→ b ;  add (succ k) b ι→ succ (add k b).   (thm_plus_n_o.rs:95-115.)
fn add_body() -> Tm {
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
fn add_ty() -> Tm {
    pi(nat_ty(), pi(nat_ty(), nat_ty()))
}
fn add(a: Tm, b: Tm) -> Tm {
    apps(Tm::Const(ADD), &[a, b])
}

fn env() -> dnx_proof::env::GlobalEnv {
    let mut e = dnx_proof::env::GlobalEnv::default();
    e.add_inductive(nat()).expect("Nat admits");
    e.add_inductive(id_ind())
        .expect("Id admits (indexed inductive, Vec mould)");
    e.add_const(ADD, add_ty(), add_body())
        .expect("add admits (δ-acyclic)");
    e
}

// ════════════════ derived equality combinators (from J / Elim Id) ════════════════
// ap_succ / eq_sym / eq_trans are derived EXACTLY as in eq_prelude.rs (proofs.md:177-188);
// reproduced here closed so the file is self-contained.

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

/// eq_sym : Π(A:Type₀)(a b:A)(p:Id A a b). Id A b a   (eq_prelude.rs:166-202).
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
    // Pin the three J-derived combinators (the proofs' only tools beyond Nat.rec) before the theorems.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &ap_succ(), &ap_succ_ty()).is_ok(),
        "ap_succ : Π(a b:Nat)(p:Id Nat a b). Id Nat (succ a)(succ b)  (J / Elim Id)"
    );
    assert!(
        check(&env, &Vec::new(), &eq_sym(), &eq_sym_ty()).is_ok(),
        "eq_sym : Π(A)(a b:A)(p:Id A a b). Id A b a  (J / Elim Id)"
    );
    assert!(
        check(&env, &Vec::new(), &eq_trans(), &eq_trans_ty()).is_ok(),
        "eq_trans : Π(A)(a b c:A)(p:Id A a b)(q:Id A b c). Id A a c  (J / Elim Id)"
    );
}

// ════════════════════════ add_zero_r — ∀n. add n 0 = n ════════════════════════

/// add_zero_r := λn:Nat. Nat.rec (λm. Id Nat (add m 0) m)
///                               (refl Nat 0)                              -- base n=0
///                               (λk ih. ap_succ (add k 0) k ih)          -- step n=succ k
///                               n
/// `add n 0` is STUCK on the neutral `n` (ι cannot fire on a variable, recursion is on arg 1),
/// so this is NOT definitional — it is the genuine recursive-data law (the classic Coq `plus_n_O`).
fn add_zero_r() -> Tm {
    let motive = lam(nat_ty(), id_nat(add(Tm::Var(0), zero()), Tm::Var(0)));
    let base = refl_nat(zero()); // Id Nat (add 0 0) 0 ≡ Id Nat 0 0
    let step = lam(
        nat_ty(), // k
        lam(
            // ih : Id Nat (add k 0) k   (ctx [n,k]: k=Var0)
            id_nat(add(Tm::Var(0), zero()), Tm::Var(0)),
            // ctx [n,k,ih]: k=Var1, ih=Var0.
            ap_succ_at(add(Tm::Var(1), zero()), Tm::Var(1), Tm::Var(0)),
        ),
    );
    lam(
        nat_ty(),
        apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(0)]),
    )
}
fn add_zero_r_ty() -> Tm {
    pi(nat_ty(), id_nat(add(Tm::Var(0), zero()), Tm::Var(0)))
}
/// `add_zero_r n : Id Nat (add n 0) n`.
fn add_zero_r_at(n: Tm) -> Tm {
    app(add_zero_r(), n)
}

#[test]
fn add_zero_r_typechecks() {
    // ∀n. add n 0 = n — GENERAL, by Nat.rec induction on n (IH consumed via ap_succ).
    // `add n 0` is stuck on neutral n ⇒ genuine induction, NOT definitional.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &add_zero_r(), &add_zero_r_ty()).is_ok(),
        "add_zero_r : Π(n:Nat). Id Nat (add n 0) n  (Nat.rec + ap_succ)"
    );
}

#[test]
fn false_add_zero_r_rejected() {
    // NO-FALSE-GREEN + positive control: the SAME induction skeleton at the FALSE motive
    // `∀n. add n 0 = succ n` fails (base would need `refl Nat 0 : Id Nat 0 (succ 0)`), while the
    // TRUE goal passes (asserted above) — so the type is load-bearing, not vacuous.
    let env = env();
    let bad_motive = lam(nat_ty(), id_nat(add(Tm::Var(0), zero()), succ(Tm::Var(0))));
    let bad_step = lam(
        nat_ty(),
        lam(
            id_nat(add(Tm::Var(0), zero()), succ(Tm::Var(0))),
            ap_succ_at(add(Tm::Var(1), zero()), succ(Tm::Var(1)), Tm::Var(0)),
        ),
    );
    let bad = lam(
        nat_ty(),
        apps(
            Tm::Elim(NAT),
            &[bad_motive, refl_nat(zero()), bad_step, Tm::Var(0)],
        ),
    );
    let bad_ty = pi(nat_ty(), id_nat(add(Tm::Var(0), zero()), succ(Tm::Var(0))));
    assert_eq!(
        check(&env, &Vec::new(), &bad, &bad_ty),
        Err(TypeError::Mismatch),
        "∀n. add n 0 = succ n is FALSE — base case rejected (no false-green)"
    );
}

// ════════════════════════ add_succ_r — ∀n m. add n (succ m) = succ (add n m) ════════════════════════

/// add_succ_r := λn m. Nat.rec (λn'. Id Nat (add n' (succ m)) (succ (add n' m)))
///                             (refl Nat (succ m))                                      -- base n=0
///                             (λk ih. ap_succ (add k (succ m)) (succ (add k m)) ih)    -- step
///                             n
/// Induction on n (the arg `add` recurses on). `add n (succ m)` is stuck on the neutral `n`.
///   base n=0: `add 0 (succ m) ι→ succ m` and `succ (add 0 m) ι→ succ m` ⇒ `refl Nat (succ m)`.
///   step n=succ k: LHS `add (succ k)(succ m) ι→ succ(add k (succ m))`, RHS
///     `succ(add (succ k) m) ι→ succ(succ(add k m))`; IH `ih : Id Nat (add k (succ m)) (succ(add k m))`,
///     so `ap_succ … ih` closes the goal (IH CONSUMED).
fn add_succ_r() -> Tm {
    // motive λn'. Id Nat (add n' (succ m)) (succ (add n' m))   (ctx [n,m,n']: m=Var1, n'=Var0).
    let motive = lam(
        nat_ty(),
        id_nat(
            add(Tm::Var(0), succ(Tm::Var(1))), // add n' (succ m)
            succ(add(Tm::Var(0), Tm::Var(1))), // succ (add n' m)
        ),
    );
    // base : refl Nat (succ m)   (ctx [n,m]: m=Var0).
    let base = refl_nat(succ(Tm::Var(0)));
    // step λk.λih. ap_succ (add k (succ m)) (succ (add k m)) ih   (ctx [n,m,k,ih]: m=Var2,k=Var1,ih=Var0).
    let step = lam(
        nat_ty(), // k
        lam(
            // ih : motive k = Id Nat (add k (succ m)) (succ (add k m))   (ctx [n,m,k]: m=Var1,k=Var0)
            id_nat(
                add(Tm::Var(0), succ(Tm::Var(1))),
                succ(add(Tm::Var(0), Tm::Var(1))),
            ),
            ap_succ_at(
                add(Tm::Var(1), succ(Tm::Var(2))), // add k (succ m)
                succ(add(Tm::Var(1), Tm::Var(2))), // succ (add k m)
                Tm::Var(0),                        // ih  (CONSUMED)
            ),
        ),
    );
    let rec = apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(1)]); // scrutinee n
    lam(nat_ty(), lam(nat_ty(), rec))
}
fn add_succ_r_ty() -> Tm {
    // Π(n m:Nat). Id Nat (add n (succ m)) (succ (add n m))   (ctx [n,m]: n=Var1,m=Var0).
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            id_nat(
                add(Tm::Var(1), succ(Tm::Var(0))),
                succ(add(Tm::Var(1), Tm::Var(0))),
            ),
        ),
    )
}
/// `add_succ_r n m : Id Nat (add n (succ m)) (succ (add n m))`  (concrete instance).
fn add_succ_r_at(n: Tm, m: Tm) -> Tm {
    apps(add_succ_r(), &[n, m])
}

#[test]
fn add_succ_r_typechecks() {
    // ∀n m. add n (succ m) = succ (add n m) — GENERAL, by Nat.rec induction on n; IH via ap_succ.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &add_succ_r(), &add_succ_r_ty()).is_ok(),
        "add_succ_r : Π(n m:Nat). Id Nat (add n (succ m)) (succ (add n m))  (induction on n)"
    );
}

#[test]
fn false_add_succ_r_rejected() {
    // NO-FALSE-GREEN + positive control: drop the `succ` on the rhs ⇒ `∀n m. add n (succ m) = add n m`
    // is FALSE; its base needs `refl Nat (succ m) : Id Nat (succ m) m`, rejected by `check`.
    let env = env();
    let bad_motive = lam(
        nat_ty(),
        id_nat(
            add(Tm::Var(0), succ(Tm::Var(1))),
            add(Tm::Var(0), Tm::Var(1)),
        ),
    );
    let bad_base = refl_nat(succ(Tm::Var(0)));
    let bad_step = lam(
        nat_ty(),
        lam(
            id_nat(
                add(Tm::Var(0), succ(Tm::Var(1))),
                add(Tm::Var(0), Tm::Var(1)),
            ),
            ap_succ_at(
                add(Tm::Var(1), succ(Tm::Var(2))),
                add(Tm::Var(1), Tm::Var(2)),
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
                add(Tm::Var(1), succ(Tm::Var(0))),
                add(Tm::Var(1), Tm::Var(0)),
            ),
        ),
    );
    assert_eq!(
        check(&env, &Vec::new(), &bad, &bad_ty),
        Err(TypeError::Mismatch),
        "∀n m. add n (succ m) = add n m is FALSE — base case rejected (no false-green)"
    );
}

// ════════════════════════ add_comm — ∀n m. add n m = add m n ════════════════════════

/// add_comm := λn m. Nat.rec
///     (λn'. Id Nat (add n' m) (add m n'))                            -- motive
///     (eq_sym Nat (add m 0) m (add_zero_r m))                        -- base n=0:  m = add m 0
///     (λk ih. eq_trans … (ap_succ … ih) (eq_sym … (add_succ_r m k))) -- step n=succ k
///     n
/// Induction on n.
///   base n=0: goal `Id Nat (add 0 m) (add m 0)` ≡ `Id Nat m (add m 0)`. `add_zero_r m :
///     Id Nat (add m 0) m`, so `eq_sym` flips it to `Id Nat m (add m 0)`.
///   step n=succ k: goal `Id Nat (add (succ k) m) (add m (succ k))`. LHS `add (succ k) m ι→
///     succ (add k m)`. IH `ih : Id Nat (add k m) (add m k)`.
///       s1 = ap_succ (add k m) (add m k) ih   : Id Nat (succ (add k m)) (succ (add m k)).
///       s2 = eq_sym (add_succ_r m k)          : Id Nat (succ (add m k)) (add m (succ k)).
///     eq_trans chains s1,s2 to `Id Nat (succ (add k m)) (add m (succ k))` ≡ goal (LHS ι-eq).
///     The IH is genuinely CONSUMED (inside `ap_succ`).
fn add_comm() -> Tm {
    // motive λn'. Id Nat (add n' m) (add m n')   (ctx [n,m,n']: m=Var1, n'=Var0).
    let motive = lam(
        nat_ty(),
        id_nat(add(Tm::Var(0), Tm::Var(1)), add(Tm::Var(1), Tm::Var(0))),
    );
    // base n=0: goal Id Nat (add 0 m) (add m 0) ≡ Id Nat m (add m 0).   (ctx [n,m]: m=Var0)
    //   add_zero_r m : Id Nat (add m 0) m  ⟹  eq_sym : Id Nat m (add m 0).
    let base = eq_sym_nat(
        add(Tm::Var(0), zero()),
        Tm::Var(0),
        add_zero_r_at(Tm::Var(0)),
    );
    // step λk.λih. ...   (ctx [n,m,k,ih]: m=Var2, k=Var1, ih=Var0).
    let step = lam(
        nat_ty(), // k
        lam(
            // ih : motive k = Id Nat (add k m) (add m k)   (ctx [n,m,k]: m=Var1, k=Var0)
            id_nat(add(Tm::Var(0), Tm::Var(1)), add(Tm::Var(1), Tm::Var(0))),
            // ctx [n,m,k,ih]: m=Var2, k=Var1, ih=Var0.
            // goal Id Nat (add (succ k) m) (add m (succ k)) ≡ Id Nat (succ (add k m)) (add m (succ k))
            //   (LHS ι: add (succ k) m → succ (add k m)).
            trans_nat(
                succ(add(Tm::Var(1), Tm::Var(2))), // succ (add k m)
                succ(add(Tm::Var(2), Tm::Var(1))), // succ (add m k)
                add(Tm::Var(2), succ(Tm::Var(1))), // add m (succ k)
                ap_succ_at(
                    add(Tm::Var(1), Tm::Var(2)), // add k m
                    add(Tm::Var(2), Tm::Var(1)), // add m k
                    Tm::Var(0),                  // ih  (CONSUMED)
                ),
                // eq_sym (add_succ_r m k) : Id Nat (succ (add m k)) (add m (succ k)).
                eq_sym_nat(
                    add(Tm::Var(2), succ(Tm::Var(1))),     // add m (succ k)
                    succ(add(Tm::Var(2), Tm::Var(1))),     // succ (add m k)
                    add_succ_r_at(Tm::Var(2), Tm::Var(1)), // add_succ_r m k
                ),
            ),
        ),
    );
    let rec = apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(1)]); // scrutinee n
    lam(nat_ty(), lam(nat_ty(), rec))
}
fn add_comm_ty() -> Tm {
    // Π(n m:Nat). Id Nat (add n m) (add m n)   (ctx [n,m]: n=Var1, m=Var0).
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            id_nat(add(Tm::Var(1), Tm::Var(0)), add(Tm::Var(0), Tm::Var(1))),
        ),
    )
}

#[test]
fn add_comm_typechecks() {
    // THE marquee theorem: ∀n m. add n m = add m n — GENERAL, machine-checked.
    // Induction on n (Nat.rec): base via add_zero_r + eq_sym; step CONSUMES the IH via ap_succ and
    // chains with eq_sym(add_succ_r) through eq_trans. Nat non-indexed ⇒ ι fires on open fields.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &add_comm(), &add_comm_ty()).is_ok(),
        "add_comm : Π(n m:Nat). Id Nat (add n m) (add m n)  (induction on n; IH consumed)"
    );
}

#[test]
fn false_add_comm_rejected() {
    // NO-FALSE-GREEN + positive control: `add_comm` does NOT inhabit the off-by-one
    // `∀n m. add n m = succ (add m n)`, while it DOES inhabit the true type (asserted above).
    let env = env();
    let bad_ty = pi(
        nat_ty(),
        pi(
            nat_ty(),
            id_nat(
                add(Tm::Var(1), Tm::Var(0)),
                succ(add(Tm::Var(0), Tm::Var(1))),
            ),
        ),
    );
    assert!(
        check(&env, &Vec::new(), &add_comm(), &bad_ty).is_err(),
        "add_comm does NOT inhabit ∀n m. add n m = succ (add m n) (off by one)"
    );
}

// ════════════════════════ add_assoc — ∀n m k. add (add n m) k = add n (add m k) ════════════════════════

/// add_assoc := λn m k. Nat.rec
///     (λn'. Id Nat (add (add n' m) k) (add n' (add m k)))                  -- motive
///     (refl Nat (add m k))                                                 -- base n=0
///     (λj ih. ap_succ (add (add j m) k) (add j (add m k)) ih)              -- step n=succ j
///     n
/// Induction on the FIRST arg n (thm_mul.rs:439-475's `add_assoc_l`).
///   base n=0: `add (add 0 m) k ι→ add m k` and `add 0 (add m k) ι→ add m k` ⇒ `refl Nat (add m k)`.
///   step n=succ j: both sides ι→ `succ(...)` through the first-arg succ-minor, so `ap_succ … ih`
///     closes it (IH CONSUMED).
fn add_assoc() -> Tm {
    // ctx [n,m,k,n']: m=Var2, k=Var1, n'=Var0.
    let motive = lam(
        nat_ty(),
        id_nat(
            add(add(Tm::Var(0), Tm::Var(2)), Tm::Var(1)), // (n'+m)+k
            add(Tm::Var(0), add(Tm::Var(2), Tm::Var(1))), // n'+(m+k)
        ),
    );
    // base : refl Nat (add m k)   (ctx [n,m,k]: m=Var1, k=Var0).
    let base = refl_nat(add(Tm::Var(1), Tm::Var(0)));
    // step λj.λih. ap_succ ((j+m)+k) (j+(m+k)) ih.
    let step = lam(
        nat_ty(), // j
        lam(
            // ih : motive j   (ctx [n,m,k,j]: m=Var2, k=Var1, j=Var0).
            id_nat(
                add(add(Tm::Var(0), Tm::Var(2)), Tm::Var(1)),
                add(Tm::Var(0), add(Tm::Var(2), Tm::Var(1))),
            ),
            // ctx [n,m,k,j,ih]: m=Var3, k=Var2, j=Var1, ih=Var0.
            ap_succ_at(
                add(add(Tm::Var(1), Tm::Var(3)), Tm::Var(2)), // (j+m)+k
                add(Tm::Var(1), add(Tm::Var(3), Tm::Var(2))), // j+(m+k)
                Tm::Var(0),                                   // ih  (CONSUMED)
            ),
        ),
    );
    let rec = apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(2)]); // scrutinee n
    lam(nat_ty(), lam(nat_ty(), lam(nat_ty(), rec)))
}
fn add_assoc_ty() -> Tm {
    // Π(n m k:Nat). Id Nat ((n+m)+k) (n+(m+k))   (ctx [n,m,k]: n=Var2, m=Var1, k=Var0).
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            pi(
                nat_ty(),
                id_nat(
                    add(add(Tm::Var(2), Tm::Var(1)), Tm::Var(0)),
                    add(Tm::Var(2), add(Tm::Var(1), Tm::Var(0))),
                ),
            ),
        ),
    )
}
/// The inductive proof SPECIALISED to closed literals n,m,k (outer λs pre-applied ⇒ CLOSED term).
fn add_assoc_at(n: u32, m: u32, k: u32) -> Tm {
    apps(add_assoc(), &[lit(n), lit(m), lit(k)])
}

#[test]
fn add_assoc_typechecks() {
    // ∀n m k. (n+m)+k = n+(m+k) — GENERAL, by Nat.rec induction on n; IH consumed via ap_succ.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &add_assoc(), &add_assoc_ty()).is_ok(),
        "add_assoc : Π(n m k:Nat). Id Nat ((n+m)+k) (n+(m+k))  (induction on n)"
    );
}

#[test]
fn false_add_assoc_rejected() {
    // NO-FALSE-GREEN + positive control: the SAME proof term does NOT inhabit the off-by-one
    // `∀n m k. (n+m)+k = succ (n+(m+k))`, while it DOES inhabit the true type (asserted above).
    let env = env();
    let false_ty = pi(
        nat_ty(),
        pi(
            nat_ty(),
            pi(
                nat_ty(),
                id_nat(
                    add(add(Tm::Var(2), Tm::Var(1)), Tm::Var(0)),
                    succ(add(Tm::Var(2), add(Tm::Var(1), Tm::Var(0)))),
                ),
            ),
        ),
    );
    assert!(
        check(&env, &Vec::new(), &add_assoc(), &false_ty).is_err(),
        "add_assoc does NOT inhabit ∀n m k. (n+m)+k = succ (n+(m+k)) (off by one)"
    );
}

// ════════════════════════ closed-compute sanity + non-vacuity ════════════════════════

#[test]
fn add_two_three_nf_is_five() {
    // Closed-compute sanity: `add 2 3` ι-normalizes to the literal `5` (the recursor fires through
    // every closed succ-field), and is convertible to `5` but NOT to `4` or `6`.
    let env = env();
    let nf = nf_tm(&env, &Vec::new(), &add(lit(2), lit(3)));
    assert_eq!(nf, lit(5), "add 2 3 ι-normalizes to 5");
    assert!(
        conv(&env, &Vec::new(), &add(lit(2), lit(3)), &lit(5)).unwrap(),
        "add 2 3 ≡ 5"
    );
    assert!(
        !conv(&env, &Vec::new(), &add(lit(2), lit(3)), &lit(4)).unwrap(),
        "add 2 3 ≢ 4"
    );
    assert!(
        !conv(&env, &Vec::new(), &add(lit(2), lit(3)), &lit(6)).unwrap(),
        "add 2 3 ≢ 6"
    );
}

#[test]
fn add_assoc_instance_normalizes_to_refl() {
    // End-to-end ι evidence: the closed proof `add_assoc 1 2 3 : Id Nat 6 6` NORMALIZES to the
    // canonical witness `refl Nat 6` (both (n+m)+k and n+(m+k) compute to 6 through the recursor),
    // convertible to it but NOT to a wrong witness `refl Nat 5` — the proof is non-vacuous.
    let env = env();
    let inst = add_assoc_at(1, 2, 3);
    let refl6 = refl_nat(lit(6));
    assert_eq!(
        nf_tm(&env, &Vec::new(), &inst),
        refl6,
        "add_assoc 1 2 3 ι-normalizes to refl Nat 6"
    );
    assert!(
        conv(&env, &Vec::new(), &inst, &refl6).unwrap(),
        "add_assoc 1 2 3 ≡ refl Nat 6"
    );
    assert!(
        !conv(&env, &Vec::new(), &inst, &refl_nat(lit(5))).unwrap(),
        "add_assoc 1 2 3 ≢ refl Nat 5 (off by one)"
    );
}

#[test]
fn add_comm_closed_instance_is_refl() {
    // NEGATIVE / non-vacuity for add_comm at closed args: `add_comm 2 3 : Id Nat (add 2 3) (add 3 2)`
    // ≡ `Id Nat 5 5`, normalizing to `refl Nat 5` — convertible to it, NOT to `refl Nat 6`.
    let env = env();
    let inst = apps(add_comm(), &[lit(2), lit(3)]);
    let refl5 = refl_nat(lit(5));
    assert_eq!(
        nf_tm(&env, &Vec::new(), &inst),
        refl5,
        "add_comm 2 3 ι-normalizes to refl Nat 5"
    );
    assert!(
        !conv(&env, &Vec::new(), &inst, &refl_nat(lit(6))).unwrap(),
        "add_comm 2 3 ≢ refl Nat 6"
    );
}
