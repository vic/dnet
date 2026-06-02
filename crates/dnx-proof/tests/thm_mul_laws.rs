//! Verified Nat MULTIPLICATION laws on the dnx-proof kernel, proven end-to-end by genuine
//! `Nat.rec` induction. Companion to `thm_mul.rs`, but every multiplicative law here is stated in
//! its **task-canonical orientation** — the `succ`/distrib laws are oriented so the recursing
//! variable leads (`mul n (succ m) = add n (mul n m)`, `mul (add n m) k = add (mul n k)(mul m k)`),
//! which is a DIFFERENT (and strictly harder) orientation than `thm_mul.rs`'s
//! `mul m (succ n) = plus (mul m n) m`. The two are inter-derivable only through `add` commutativity,
//! so this is not a re-statement: the `add`-shuffle plumbing (assoc + comm + BOTH plus congruences,
//! including the left-argument congruence `ap_plus_r` absent from thm_mul.rs) is genuinely exercised.
//!
//! `Nat`/`zero`/`succ`, `Id`/`refl`, the J-derived `ap_succ`/`eq_sym`/`eq_trans`, and the two `add`
//! lemmas `add_zero_r`/`add_succ_r` are reproduced CLOSED here (the exact idioms of
//! thm_nat_arith.rs / thm_nat_algebra.rs / thm_mul.rs; eq_prelude.rs:166-312, proofs.md:163-188) so
//! the file is self-contained. NO new axioms: every term is `check`ed at its ∀-type by the trusted
//! kernel, so the kernel is the oracle.
//!
//! `add` and `mul` both recurse on their FIRST argument:
//!   add 0 b ι→ b ,  add (succ k) b ι→ succ (add k b)         (thm_plus_n_o.rs:95-115)
//!   mul 0 n ι→ 0 ,  mul (succ k) n ι→ add n (mul k n)         (thm_mul.rs:114-128)
//! `Nat` is non-indexed (`nidx == 0`), so the ι-driver fires on OPEN scrutinees / recursive fields
//! (driver.rs:109-112) — which is why the inductive steps below go through.
//!
//! THEOREMS (all GENERAL, ∀-quantified, machine-checked at their type):
//!   • mul_zero_r   : ∀n.     mul n 0 = 0                        (induction on n; step returns IH)
//!   • mul_succ_r   : ∀n m.   mul n (succ m) = add n (mul n m)   (induction on n; add-swap interchange)
//!   • mul_comm     : ∀n m.   mul n m = mul m n                  (induction on n; uses both above)
//!   • mul_distrib_r: ∀n m k. mul (add n m) k = add (mul n k)(mul m k)  (induction on n)
//!
//! NON-VACUITY: a CLOSED instance (`mul 2 3`) ι-normalizes to the literal `6`, the closed proof
//! `mul_comm 2 3 : Id Nat 6 6` normalizes to `refl Nat 6`, and the off-by-one companions are
//! REJECTED by `check` alongside the TRUE goals — so the green is not a vacuous-type artifact.

use dnx_proof::conv::conv;
use dnx_proof::driver::nf_tm;
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::{check, TypeError};
use dnx_proof::symbol::{ConstId, IndId};
use dnx_proof::tm::Tm;

// ── term helpers (same idioms as eq_prelude.rs / thm_mul.rs / thm_nat_arith.rs) ──
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
fn id_nat(a: Tm, b: Tm) -> Tm {
    apps(Tm::Ind(ID), &[nat_ty(), a, b])
}
fn refl_nat(a: Tm) -> Tm {
    apps(Tm::Ctor(ID, 0), &[nat_ty(), a])
}

// add := λa b. Elim Nat (λ_.Nat) b (λk ih. succ ih) a   (recursion on FIRST arg; thm_nat_arith.rs).
//   add 0 b ι→ b ;  add (succ k) b ι→ succ (add k b).
fn add_body() -> Tm {
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
fn add_ty() -> Tm {
    pi(nat_ty(), pi(nat_ty(), nat_ty()))
}
fn add(a: Tm, b: Tm) -> Tm {
    apps(Tm::Const(ADD), &[a, b])
}

// mul := λm n. Elim Nat (λ_.Nat) 0 (λk ih. add n ih) m   (recursion on FIRST arg; thm_mul.rs:114).
//   mul 0 n ι→ 0 ;  mul (succ k) n ι→ add n (mul k n).
fn mul_body() -> Tm {
    // ctx [m,n]: m=Var1, n=Var0.  Under succ-minor λk.λih: ctx [m,n,k,ih]: n=Var2, ih=Var0.
    let elim = apps(
        Tm::Elim(NAT),
        &[
            lam(nat_ty(), nat_ty()),                                   // motive λ_.Nat
            zero(),                                                    // minor_zero = 0
            lam(nat_ty(), lam(nat_ty(), add(Tm::Var(2), Tm::Var(0)))), // minor_succ = λk ih. add n ih
            Tm::Var(1),                                                // scrutinee = m
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

fn env() -> dnx_proof::env::GlobalEnv {
    let mut e = dnx_proof::env::GlobalEnv::default();
    e.add_inductive(nat()).expect("Nat admits");
    e.add_inductive(id_ind())
        .expect("Id admits (indexed inductive, Vec mould)");
    e.add_const(ADD, add_ty(), add_body())
        .expect("add admits (δ-acyclic)");
    e.add_const(MUL, mul_ty(), mul_body())
        .expect("mul admits (δ-acyclic; mul calls add, add does not call mul)");
    e
}

// ════════════════ derived equality combinators (J / Elim Id) ════════════════
// ap_succ / eq_sym / eq_trans are derived EXACTLY as in eq_prelude.rs (proofs.md:177-188);
// ap_plus_l / ap_plus_r are the two one-sided congruences of `add` (same J shape as ap_succ).

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

/// ap_plus_l : Π(c a b:Nat)(p:Id Nat a b). Id Nat (add c a) (add c b)  (right-arg congruence of add).
///   = λc a b p. Elim Id Nat a (λb' x. Id Nat (add c a)(add c b')) (refl Nat (add c a)) b p
fn ap_plus_l() -> Tm {
    // ctx [c,a,b,p]: c=Var3, a=Var2, b=Var1, p=Var0.
    let motive = lam(
        nat_ty(), // b'
        lam(
            id_nat(Tm::Var(3), Tm::Var(0)), // x : Id Nat a b'  (a=Var3, b'=Var0)
            id_nat(
                add(Tm::Var(5), Tm::Var(4)), // add c a   (c=Var5, a=Var4)
                add(Tm::Var(5), Tm::Var(1)), // add c b'  (b'=Var1)
            ),
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            nat_ty(),
            Tm::Var(2), // a
            motive,
            refl_nat(add(Tm::Var(3), Tm::Var(2))), // refl Nat (add c a)
            Tm::Var(1),                            // index b
            Tm::Var(0),                            // scrutinee p
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
                    id_nat(add(Tm::Var(3), Tm::Var(2)), add(Tm::Var(3), Tm::Var(1))),
                ),
            ),
        ),
    )
}
fn ap_plus_l_at(c: Tm, a: Tm, b: Tm, p: Tm) -> Tm {
    apps(ap_plus_l(), &[c, a, b, p])
}

/// ap_plus_r : Π(c a b:Nat)(p:Id Nat a b). Id Nat (add a c) (add b c)  (LEFT-arg congruence of add).
///   = λc a b p. Elim Id Nat a (λb' x. Id Nat (add a c)(add b' c)) (refl Nat (add a c)) b p
/// This left-congruence is NOT present in thm_mul.rs and is what the task `add`-orientation forces.
fn ap_plus_r() -> Tm {
    // ctx [c,a,b,p]: c=Var3, a=Var2, b=Var1, p=Var0.
    let motive = lam(
        nat_ty(), // b'
        lam(
            id_nat(Tm::Var(3), Tm::Var(0)), // x : Id Nat a b'  (a=Var3, b'=Var0)
            id_nat(
                add(Tm::Var(4), Tm::Var(5)), // add a c   (a=Var4, c=Var5)
                add(Tm::Var(1), Tm::Var(5)), // add b' c  (b'=Var1, c=Var5)
            ),
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            nat_ty(),
            Tm::Var(2), // a
            motive,
            refl_nat(add(Tm::Var(2), Tm::Var(3))), // refl Nat (add a c)
            Tm::Var(1),                            // index b
            Tm::Var(0),                            // scrutinee p
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
fn ap_plus_r_ty() -> Tm {
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            pi(
                nat_ty(),
                pi(
                    id_nat(Tm::Var(1), Tm::Var(0)),
                    id_nat(add(Tm::Var(2), Tm::Var(3)), add(Tm::Var(1), Tm::Var(3))),
                ),
            ),
        ),
    )
}
fn ap_plus_r_at(c: Tm, a: Tm, b: Tm, p: Tm) -> Tm {
    apps(ap_plus_r(), &[c, a, b, p])
}

/// eq_sym : Π(A:Type₀)(a b:A)(p:Id A a b). Id A b a   (eq_prelude.rs:166-202).
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
fn eq_sym_nat(a: Tm, b: Tm, p: Tm) -> Tm {
    apps(eq_sym(), &[nat_ty(), a, b, p])
}

/// eq_trans : Π(A)(a b c:A)(p:Id A a b)(q:Id A b c). Id A a c   (eq_prelude.rs:255-291).
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
fn trans_nat(a: Tm, b: Tm, c: Tm, p: Tm, q: Tm) -> Tm {
    apps(eq_trans(), &[nat_ty(), a, b, c, p, q])
}

// ════════════════ add lemmas (reproduced from thm_nat_arith.rs, used as terms) ════════════════

/// add_zero_r : Π(n:Nat). Id Nat (add n 0) n   (thm_nat_arith.rs:336-355).
fn add_zero_r() -> Tm {
    let motive = lam(nat_ty(), id_nat(add(Tm::Var(0), zero()), Tm::Var(0)));
    let base = refl_nat(zero());
    let step = lam(
        nat_ty(),
        lam(
            id_nat(add(Tm::Var(0), zero()), Tm::Var(0)),
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
fn add_zero_r_at(n: Tm) -> Tm {
    app(add_zero_r(), n)
}

/// add_succ_r : Π(n m:Nat). Id Nat (add n (succ m)) (succ (add n m))   (thm_nat_arith.rs:412-441).
fn add_succ_r() -> Tm {
    let motive = lam(
        nat_ty(),
        id_nat(
            add(Tm::Var(0), succ(Tm::Var(1))),
            succ(add(Tm::Var(0), Tm::Var(1))),
        ),
    );
    let base = refl_nat(succ(Tm::Var(0)));
    let step = lam(
        nat_ty(),
        lam(
            id_nat(
                add(Tm::Var(0), succ(Tm::Var(1))),
                succ(add(Tm::Var(0), Tm::Var(1))),
            ),
            ap_succ_at(
                add(Tm::Var(1), succ(Tm::Var(2))),
                succ(add(Tm::Var(1), Tm::Var(2))),
                Tm::Var(0),
            ),
        ),
    );
    let rec = apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(1)]);
    lam(nat_ty(), lam(nat_ty(), rec))
}
fn add_succ_r_ty() -> Tm {
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
fn add_succ_r_at(n: Tm, m: Tm) -> Tm {
    apps(add_succ_r(), &[n, m])
}

/// add_comm : Π(n m:Nat). Id Nat (add n m) (add m n)   (thm_nat_arith.rs:528-566).
fn add_comm() -> Tm {
    let motive = lam(
        nat_ty(),
        id_nat(add(Tm::Var(0), Tm::Var(1)), add(Tm::Var(1), Tm::Var(0))),
    );
    let base = eq_sym_nat(
        add(Tm::Var(0), zero()),
        Tm::Var(0),
        add_zero_r_at(Tm::Var(0)),
    );
    let step = lam(
        nat_ty(),
        lam(
            id_nat(add(Tm::Var(0), Tm::Var(1)), add(Tm::Var(1), Tm::Var(0))),
            trans_nat(
                succ(add(Tm::Var(1), Tm::Var(2))),
                succ(add(Tm::Var(2), Tm::Var(1))),
                add(Tm::Var(2), succ(Tm::Var(1))),
                ap_succ_at(
                    add(Tm::Var(1), Tm::Var(2)),
                    add(Tm::Var(2), Tm::Var(1)),
                    Tm::Var(0),
                ),
                eq_sym_nat(
                    add(Tm::Var(2), succ(Tm::Var(1))),
                    succ(add(Tm::Var(2), Tm::Var(1))),
                    add_succ_r_at(Tm::Var(2), Tm::Var(1)),
                ),
            ),
        ),
    );
    let rec = apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(1)]);
    lam(nat_ty(), lam(nat_ty(), rec))
}
fn add_comm_ty() -> Tm {
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            id_nat(add(Tm::Var(1), Tm::Var(0)), add(Tm::Var(0), Tm::Var(1))),
        ),
    )
}
fn add_comm_at(n: Tm, m: Tm) -> Tm {
    apps(add_comm(), &[n, m])
}

/// add_assoc : Π(n m k:Nat). Id Nat (add (add n m) k) (add n (add m k))   (thm_nat_arith.rs:622-652).
fn add_assoc() -> Tm {
    let motive = lam(
        nat_ty(),
        id_nat(
            add(add(Tm::Var(0), Tm::Var(2)), Tm::Var(1)),
            add(Tm::Var(0), add(Tm::Var(2), Tm::Var(1))),
        ),
    );
    let base = refl_nat(add(Tm::Var(1), Tm::Var(0)));
    let step = lam(
        nat_ty(),
        lam(
            id_nat(
                add(add(Tm::Var(0), Tm::Var(2)), Tm::Var(1)),
                add(Tm::Var(0), add(Tm::Var(2), Tm::Var(1))),
            ),
            ap_succ_at(
                add(add(Tm::Var(1), Tm::Var(3)), Tm::Var(2)),
                add(Tm::Var(1), add(Tm::Var(3), Tm::Var(2))),
                Tm::Var(0),
            ),
        ),
    );
    let rec = apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(2)]);
    lam(nat_ty(), lam(nat_ty(), lam(nat_ty(), rec)))
}
fn add_assoc_ty() -> Tm {
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
fn add_assoc_at(n: Tm, m: Tm, k: Tm) -> Tm {
    apps(add_assoc(), &[n, m, k])
}

/// add_swap : Π(a b c:Nat). Id Nat (add a (add b c)) (add b (add a c))   (the interchange law).
///   a+(b+c) =⟨sym assoc⟩= (a+b)+c =⟨ap_plus_r (add_comm a b)⟩= (b+a)+c =⟨assoc⟩= b+(a+c).
/// This is the one shuffle `mul_succ_r` (task orientation) needs, and the reason `ap_plus_r` exists.
fn add_swap() -> Tm {
    // ctx [a,b,c]: a=Var2, b=Var1, c=Var0.
    let a = Tm::Var(2);
    let b = Tm::Var(1);
    let c = Tm::Var(0);
    // p1 : add a (add b c) = add (add a b) c     (sym of assoc a b c)
    let p1 = eq_sym_nat(
        add(add(a.clone(), b.clone()), c.clone()),
        add(a.clone(), add(b.clone(), c.clone())),
        add_assoc_at(a.clone(), b.clone(), c.clone()),
    );
    // p2 : add (add a b) c = add (add b a) c     (ap_plus_r c (add a b) (add b a) (add_comm a b))
    let p2 = ap_plus_r_at(
        c.clone(),
        add(a.clone(), b.clone()),
        add(b.clone(), a.clone()),
        add_comm_at(a.clone(), b.clone()),
    );
    // p3 : add (add b a) c = add b (add a c)      (assoc b a c)
    let p3 = add_assoc_at(b.clone(), a.clone(), c.clone());
    let inner = trans_nat(
        add(a.clone(), add(b.clone(), c.clone())),
        add(add(a.clone(), b.clone()), c.clone()),
        add(add(b.clone(), a.clone()), c.clone()),
        p1,
        p2,
    );
    let body = trans_nat(
        add(a.clone(), add(b.clone(), c.clone())),
        add(add(b.clone(), a.clone()), c.clone()),
        add(b.clone(), add(a, c)),
        inner,
        p3,
    );
    lam(nat_ty(), lam(nat_ty(), lam(nat_ty(), body)))
}
fn add_swap_ty() -> Tm {
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            pi(
                nat_ty(),
                id_nat(
                    add(Tm::Var(2), add(Tm::Var(1), Tm::Var(0))),
                    add(Tm::Var(1), add(Tm::Var(2), Tm::Var(0))),
                ),
            ),
        ),
    )
}
fn add_swap_at(a: Tm, b: Tm, c: Tm) -> Tm {
    apps(add_swap(), &[a, b, c])
}

#[test]
fn building_blocks_typecheck() {
    // Pin every tool (the proofs' only weapons beyond Nat.rec) before the multiplicative theorems.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &ap_succ(), &ap_succ_ty()).is_ok(),
        "ap_succ : Π(a b:Nat)(p:Id Nat a b). Id Nat (succ a)(succ b)"
    );
    assert!(
        check(&env, &Vec::new(), &ap_plus_l(), &ap_plus_l_ty()).is_ok(),
        "ap_plus_l : Π(c a b:Nat)(p:Id Nat a b). Id Nat (add c a)(add c b)  (right-arg congruence)"
    );
    assert!(
        check(&env, &Vec::new(), &ap_plus_r(), &ap_plus_r_ty()).is_ok(),
        "ap_plus_r : Π(c a b:Nat)(p:Id Nat a b). Id Nat (add a c)(add b c)  (LEFT-arg congruence)"
    );
    assert!(
        check(&env, &Vec::new(), &eq_sym(), &eq_sym_ty()).is_ok(),
        "eq_sym : Π(A)(a b:A)(p:Id A a b). Id A b a"
    );
    assert!(
        check(&env, &Vec::new(), &eq_trans(), &eq_trans_ty()).is_ok(),
        "eq_trans : Π(A)(a b c:A)(p:Id A a b)(q:Id A b c). Id A a c"
    );
    assert!(
        check(&env, &Vec::new(), &add_zero_r(), &add_zero_r_ty()).is_ok(),
        "add_zero_r : Π(n:Nat). Id Nat (add n 0) n"
    );
    assert!(
        check(&env, &Vec::new(), &add_succ_r(), &add_succ_r_ty()).is_ok(),
        "add_succ_r : Π(n m:Nat). Id Nat (add n (succ m)) (succ (add n m))"
    );
    assert!(
        check(&env, &Vec::new(), &add_comm(), &add_comm_ty()).is_ok(),
        "add_comm : Π(n m:Nat). Id Nat (add n m) (add m n)"
    );
    assert!(
        check(&env, &Vec::new(), &add_assoc(), &add_assoc_ty()).is_ok(),
        "add_assoc : Π(n m k:Nat). Id Nat ((n+m)+k) (n+(m+k))"
    );
    assert!(
        check(&env, &Vec::new(), &add_swap(), &add_swap_ty()).is_ok(),
        "add_swap : Π(a b c:Nat). Id Nat (a+(b+c)) (b+(a+c))  (interchange; uses ap_plus_r)"
    );
}

#[test]
fn mul_admits_and_computes() {
    // mul is admitted (δ-acyclic over add) and its two computation rules hold by ι.
    let env = env();
    assert!(
        conv(&env, &Vec::new(), &mul(zero(), lit(3)), &zero()).unwrap(),
        "mul 0 3 ≡ 0  (zero-minor)"
    );
    assert!(
        conv(&env, &Vec::new(), &mul(lit(2), lit(3)), &lit(6)).unwrap(),
        "mul 2 3 ≡ 6  (succ-minor: add n (mul k n))"
    );
    assert!(
        conv(&env, &Vec::new(), &mul(lit(3), zero()), &zero()).unwrap(),
        "mul 3 0 ≡ 0  (the n*0 law at a closed instance)"
    );
}

// ════════════════════════ mul_zero_r — ∀n. mul n 0 = 0 ════════════════════════

/// mul_zero_r := λn. Nat.rec (λn'. Id Nat (mul n' 0) 0)
///                           (refl Nat 0)              -- base n=0:  mul 0 0 ι→ 0
///                           (λk ih. ih)               -- step n=succ k: goal ≡ IH
///                           n
/// `mul n 0` is STUCK on neutral n ⇒ genuine induction. Step n=succ k:
///   mul (succ k) 0 ι→ add 0 (mul k 0) ι→ mul k 0   (add 0 x ι→ x),
/// so `motive (succ k)` is DEFINITIONALLY `motive k`, and `ih` is returned directly.
fn mul_zero_r() -> Tm {
    let motive = lam(nat_ty(), id_nat(mul(Tm::Var(0), zero()), zero()));
    let base = refl_nat(zero());
    let step = lam(
        nat_ty(),                                                 // k
        lam(id_nat(mul(Tm::Var(0), zero()), zero()), Tm::Var(0)), // λih. ih
    );
    lam(
        nat_ty(),
        apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(0)]),
    )
}
fn mul_zero_r_ty() -> Tm {
    pi(nat_ty(), id_nat(mul(Tm::Var(0), zero()), zero()))
}
fn mul_zero_r_at(n: Tm) -> Tm {
    app(mul_zero_r(), n)
}

#[test]
fn mul_zero_r_typechecks() {
    // ∀n. mul n 0 = 0 — GENERAL, by Nat.rec induction on n. `mul n 0` stuck on neutral n
    // (NOT definitional); step returns the IH directly because mul (succ k) 0 ≡ mul k 0.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &mul_zero_r(), &mul_zero_r_ty()).is_ok(),
        "mul_zero_r : Π(n:Nat). Id Nat (mul n 0) 0  (induction on n)"
    );
}

#[test]
fn false_mul_zero_r_rejected() {
    // NO-FALSE-GREEN + positive control: the SAME skeleton at the FALSE motive `∀n. mul n 0 = succ 0`
    // fails (base needs `refl Nat 0 : Id Nat 0 (succ 0)`), while the TRUE goal passes (above).
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
        "∀n. mul n 0 = 1 is FALSE — base case rejected (no false-green)"
    );
}

// ════════════════════════ mul_succ_r — ∀n m. mul n (succ m) = add n (mul n m) ════════════════════════

/// mul_succ_r := λn m. Nat.rec
///     (λn'. Id Nat (mul n' (succ m)) (add n' (mul n' m)))                  -- motive
///     (refl Nat 0)                                                         -- base n=0
///     (λk ih. <chain>)                                                     -- step n=succ k
///     n
/// Induction on n (the arg `mul` recurses on). TASK ORIENTATION: rhs is `add n' (mul n' m)`
/// (recursing var leads), NOT thm_mul.rs's `add (mul n' m) n'`.
///   Base n=0: `mul 0 (succ m) ι→ 0`; `add 0 (mul 0 m) ι→ add 0 0 ι→ 0`. Goal `Id Nat 0 0` = refl.
///   Step n=succ k, ih : Id Nat (mul k (succ m)) (add k (mul k m)):
///     LHS `mul (succ k)(succ m)` ι→ `add (succ m) (mul k (succ m))` ι→ `succ (add m (mul k (succ m)))`.
///     RHS `add (succ k) (mul (succ k) m)` ι→ `succ (add k (mul (succ k) m))`
///                                          ι→ `succ (add k (add m (mul k m)))`.
///     So (modulo ι) the goal is `succ (add m (mul k (succ m))) = succ (add k (add m (mul k m)))`.
///       p1 = ap_succ (ap_plus_l m (mul k(succ m)) (add k (mul k m)) ih)        -- IH CONSUMED
///            : succ(add m (mul k(succ m))) = succ(add m (add k (mul k m)))
///       p2 = ap_succ (add_swap m k (mul k m))
///            : succ(add m (add k (mul k m))) = succ(add k (add m (mul k m)))
///     eq_trans chains p1,p2 ⟹ goal (both sides ι-eq to the motive at succ k / k).
fn mul_succ_r() -> Tm {
    // motive λn'. Id Nat (mul n' (succ m)) (add n' (mul n' m))   (ctx [n,m,n']: m=Var1, n'=Var0).
    let motive = lam(
        nat_ty(),
        id_nat(
            mul(Tm::Var(0), succ(Tm::Var(1))),            // mul n' (succ m)
            add(Tm::Var(0), mul(Tm::Var(0), Tm::Var(1))), // add n' (mul n' m)
        ),
    );
    let base = refl_nat(zero()); // Id Nat 0 0
                                 // step λk.λih. <chain>   (ctx [n,m,k,ih]: m=Var2, k=Var1, ih=Var0).
    let step = lam(
        nat_ty(), // k
        lam(
            // ih : motive k   (ctx [n,m,k]: m=Var1, k=Var0).
            id_nat(
                mul(Tm::Var(0), succ(Tm::Var(1))),
                add(Tm::Var(0), mul(Tm::Var(0), Tm::Var(1))),
            ),
            // ctx [n,m,k,ih]: m=Var2, k=Var1, ih=Var0.
            {
                let m = Tm::Var(2);
                let k = Tm::Var(1);
                let mksm = mul(Tm::Var(1), succ(Tm::Var(2))); // mul k (succ m)
                let mkm = mul(Tm::Var(1), Tm::Var(2)); // mul k m
                                                       // p1 : succ(add m (mul k(succ m))) = succ(add m (add k (mul k m)))
                let p1 = ap_succ_at(
                    add(m.clone(), mksm.clone()),
                    add(m.clone(), add(k.clone(), mkm.clone())),
                    ap_plus_l_at(
                        m.clone(),
                        mksm.clone(),
                        add(k.clone(), mkm.clone()),
                        Tm::Var(0), // ih  (CONSUMED)
                    ),
                );
                // p2 : succ(add m (add k (mul k m))) = succ(add k (add m (mul k m)))
                let p2 = ap_succ_at(
                    add(m.clone(), add(k.clone(), mkm.clone())),
                    add(k.clone(), add(m.clone(), mkm.clone())),
                    add_swap_at(m.clone(), k.clone(), mkm.clone()),
                );
                trans_nat(
                    succ(add(m.clone(), mksm)),
                    succ(add(m.clone(), add(k.clone(), mkm.clone()))),
                    succ(add(k.clone(), add(m, mkm))),
                    p1,
                    p2,
                )
            },
        ),
    );
    let rec = apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(1)]); // scrut n
    lam(nat_ty(), lam(nat_ty(), rec))
}
fn mul_succ_r_ty() -> Tm {
    // Π(n m:Nat). Id Nat (mul n (succ m)) (add n (mul n m))   (ctx [n,m]: n=Var1, m=Var0).
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            id_nat(
                mul(Tm::Var(1), succ(Tm::Var(0))),
                add(Tm::Var(1), mul(Tm::Var(1), Tm::Var(0))),
            ),
        ),
    )
}
fn mul_succ_r_at(n: Tm, m: Tm) -> Tm {
    apps(mul_succ_r(), &[n, m])
}

#[test]
fn mul_succ_r_typechecks() {
    // ∀n m. mul n (succ m) = add n (mul n m) — GENERAL, induction on n. The task orientation:
    // IH consumed via ap_plus_l, then the add-interchange (add_swap, built from assoc+comm+ap_plus_r)
    // re-orders `m + (k + x)` into `k + (m + x)` to match the rhs ι-normal form.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &mul_succ_r(), &mul_succ_r_ty()).is_ok(),
        "mul_succ_r : Π(n m:Nat). Id Nat (mul n (succ m)) (add n (mul n m))  (induction on n)"
    );
}

#[test]
fn false_mul_succ_r_rejected() {
    // NO-FALSE-GREEN: `∀n m. mul n (succ m) = add n (mul n n)` (second factor m→n on the rhs) is FALSE.
    let env = env();
    let bad_ty = pi(
        nat_ty(),
        pi(
            nat_ty(),
            id_nat(
                mul(Tm::Var(1), succ(Tm::Var(0))),
                add(Tm::Var(1), mul(Tm::Var(1), Tm::Var(1))), // mul n n (should be mul n m)
            ),
        ),
    );
    assert!(
        check(&env, &Vec::new(), &mul_succ_r(), &bad_ty).is_err(),
        "mul_succ_r does NOT inhabit ∀n m. mul n (succ m) = add n (mul n n)  (no false-green)"
    );
}

// ════════════════════════ mul_comm — ∀n m. mul n m = mul m n ════════════════════════

/// mul_comm := λn m. Nat.rec
///     (λn'. Id Nat (mul n' m) (mul m n'))                                  -- motive
///     (eq_sym (mul_zero_r m))                                              -- base n=0
///     (λk ih. <chain>)                                                     -- step n=succ k
///     n
/// Induction on n. Base n=0: goal `Id Nat (mul 0 m)(mul m 0)` ≡ `Id Nat 0 (mul m 0)`;
///   `mul_zero_r m : Id Nat (mul m 0) 0`, eq_sym ⟹ `Id Nat 0 (mul m 0)`.
/// Step n=succ k, ih : Id Nat (mul k m)(mul m k):
///   goal `Id Nat (mul (succ k) m)(mul m (succ k))`; LHS ι→ `add m (mul k m)`.
///   s1 = ap_plus_l m (mul k m)(mul m k) ih : add m (mul k m) = add m (mul m k)   -- IH CONSUMED
///   s2 = eq_sym (mul_succ_r m k)           : add m (mul m k) = mul m (succ k)
///   eq_trans chains them ⟹ add m (mul k m) = mul m (succ k) ≡ goal (LHS ι-eq).
/// NOTE this consumes the TASK-oriented `mul_succ_r m k : mul m (succ k) = add m (mul m k)` directly —
/// no add_comm fix-up is needed (that is the whole point of the task orientation).
fn mul_comm() -> Tm {
    // motive λn'. Id Nat (mul n' m) (mul m n')   (ctx [n,m,n']: m=Var1, n'=Var0).
    let motive = lam(
        nat_ty(),
        id_nat(mul(Tm::Var(0), Tm::Var(1)), mul(Tm::Var(1), Tm::Var(0))),
    );
    // base n=0: eq_sym (mul_zero_r m)   (ctx [n,m]: m=Var0).
    let base = eq_sym_nat(mul(Tm::Var(0), zero()), zero(), mul_zero_r_at(Tm::Var(0)));
    // step λk.λih. <chain>   (ctx [n,m,k,ih]: m=Var2, k=Var1, ih=Var0).
    let step = lam(
        nat_ty(), // k
        lam(
            // ih : motive k   (ctx [n,m,k]: m=Var1, k=Var0).
            id_nat(mul(Tm::Var(0), Tm::Var(1)), mul(Tm::Var(1), Tm::Var(0))),
            {
                let m = Tm::Var(2);
                let k = Tm::Var(1);
                let mkm = mul(Tm::Var(1), Tm::Var(2)); // mul k m
                let mmk = mul(Tm::Var(2), Tm::Var(1)); // mul m k
                                                       // s1 : add m (mul k m) = add m (mul m k)
                let s1 = ap_plus_l_at(m.clone(), mkm.clone(), mmk.clone(), Tm::Var(0));
                // s2 : add m (mul m k) = mul m (succ k)
                let s2 = eq_sym_nat(
                    mul(m.clone(), succ(k.clone())),
                    add(m.clone(), mmk.clone()),
                    mul_succ_r_at(m.clone(), k.clone()),
                );
                trans_nat(
                    add(m.clone(), mkm),
                    add(m.clone(), mmk),
                    mul(m, succ(k)),
                    s1,
                    s2,
                )
            },
        ),
    );
    let rec = apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(1)]); // scrut n
    lam(nat_ty(), lam(nat_ty(), rec))
}
fn mul_comm_ty() -> Tm {
    // Π(n m:Nat). Id Nat (mul n m) (mul m n)   (ctx [n,m]: n=Var1, m=Var0).
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
    // THE marquee theorem: ∀n m. mul n m = mul m n — GENERAL, machine-checked.
    // Induction on n; base via mul_zero_r+eq_sym; step CONSUMES the IH via ap_plus_l and closes with
    // eq_sym(mul_succ_r) — the task orientation makes the step a clean 2-link chain (no add_comm fix).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &mul_comm(), &mul_comm_ty()).is_ok(),
        "mul_comm : Π(n m:Nat). Id Nat (mul n m) (mul m n)  (induction on n; IH consumed)"
    );
}

#[test]
fn false_mul_comm_rejected() {
    // NO-FALSE-GREEN + positive control: `mul_comm` does NOT inhabit the off-by-one
    // `∀n m. mul n m = succ (mul m n)`, while it DOES inhabit the true type (above).
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
        "mul_comm does NOT inhabit ∀n m. mul n m = succ(mul m n)  (off by one)"
    );
}

// ════════════════════════ mul_distrib_r — ∀n m k. mul (add n m) k = add (mul n k)(mul m k) ════════════════════════

/// mul_distrib_r := λn m k. Nat.rec
///     (λn'. Id Nat (mul (add n' m) k) (add (mul n' k)(mul m k)))           -- motive
///     (refl Nat (mul m k))                                                 -- base n=0
///     (λj ih. <chain>)                                                     -- step n=succ j
///     n
/// Right-distributivity, induction on n (aligns with both add/mul first-arg recursion).
///   Base n=0: `add 0 m ι→ m` ⇒ LHS `mul m k`; RHS `add (mul 0 k)(mul m k) ι→ add 0 (mul m k) ι→ mul m k`.
///     refl (DEFINITIONAL).
///   Step n=succ j, ih : Id Nat (mul (add j m) k) (add (mul j k)(mul m k)):
///     LHS `mul (add (succ j) m) k` ι→ `mul (succ (add j m)) k` ι→ `add k (mul (add j m) k)`,
///     RHS `add (mul (succ j) k)(mul m k)` ι→ `add (add k (mul j k))(mul m k)`,
///     s1 = ap_plus_l k (mul (add j m) k) (add (mul j k)(mul m k)) ih       -- IH CONSUMED
///        : add k (mul (add j m) k) = add k (add (mul j k)(mul m k))
///     s2 = eq_sym (add_assoc k (mul j k)(mul m k))
///        : add k (add (mul j k)(mul m k)) = add (add k (mul j k))(mul m k)
///     eq_trans chains them ⟹ goal (both sides ι-eq).
fn mul_distrib_r() -> Tm {
    // motive λn'. Id Nat (mul (add n' m) k) (add (mul n' k)(mul m k))   (ctx [n,m,k,n']: m=Var2, k=Var1, n'=Var0).
    let motive = lam(
        nat_ty(),
        id_nat(
            mul(add(Tm::Var(0), Tm::Var(2)), Tm::Var(1)), // mul (add n' m) k
            add(
                mul(Tm::Var(0), Tm::Var(1)), // mul n' k
                mul(Tm::Var(2), Tm::Var(1)), // mul m k
            ),
        ),
    );
    // base : refl Nat (mul m k)   (ctx [n,m,k]: m=Var1, k=Var0).
    let base = refl_nat(mul(Tm::Var(1), Tm::Var(0)));
    // step λj.λih. <chain>   (ctx [n,m,k,j,ih]: m=Var3, k=Var2, j=Var1, ih=Var0).
    let step = lam(
        nat_ty(), // j
        lam(
            // ih : motive j   (ctx [n,m,k,j]: m=Var2, k=Var1, j=Var0).
            id_nat(
                mul(add(Tm::Var(0), Tm::Var(2)), Tm::Var(1)),
                add(mul(Tm::Var(0), Tm::Var(1)), mul(Tm::Var(2), Tm::Var(1))),
            ),
            // ctx [n,m,k,j,ih]: m=Var3, k=Var2, j=Var1, ih=Var0.
            {
                let k = Tm::Var(2);
                let mjmk = mul(add(Tm::Var(1), Tm::Var(3)), Tm::Var(2)); // mul (add j m) k
                let mjk = mul(Tm::Var(1), Tm::Var(2)); // mul j k
                let mmk = mul(Tm::Var(3), Tm::Var(2)); // mul m k
                                                       // s1 : add k (mul (add j m) k) = add k (add (mul j k)(mul m k))
                let s1 = ap_plus_l_at(
                    k.clone(),
                    mjmk.clone(),
                    add(mjk.clone(), mmk.clone()),
                    Tm::Var(0), // ih  (CONSUMED)
                );
                // s2 : add k (add (mul j k)(mul m k)) = add (add k (mul j k))(mul m k)
                let s2 = eq_sym_nat(
                    add(add(k.clone(), mjk.clone()), mmk.clone()),
                    add(k.clone(), add(mjk.clone(), mmk.clone())),
                    add_assoc_at(k.clone(), mjk.clone(), mmk.clone()),
                );
                trans_nat(
                    add(k.clone(), mjmk),
                    add(k.clone(), add(mjk.clone(), mmk.clone())),
                    add(add(k, mjk), mmk),
                    s1,
                    s2,
                )
            },
        ),
    );
    let rec = apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(2)]); // scrut n
    lam(nat_ty(), lam(nat_ty(), lam(nat_ty(), rec)))
}
fn mul_distrib_r_ty() -> Tm {
    // Π(n m k:Nat). Id Nat (mul (add n m) k) (add (mul n k)(mul m k))   (ctx [n,m,k]: n=Var2, m=Var1, k=Var0).
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            pi(
                nat_ty(),
                id_nat(
                    mul(add(Tm::Var(2), Tm::Var(1)), Tm::Var(0)),
                    add(mul(Tm::Var(2), Tm::Var(0)), mul(Tm::Var(1), Tm::Var(0))),
                ),
            ),
        ),
    )
}
fn mul_distrib_r_at(n: Tm, m: Tm, k: Tm) -> Tm {
    apps(mul_distrib_r(), &[n, m, k])
}

#[test]
fn mul_distrib_r_typechecks() {
    // ∀n m k. mul (add n m) k = add (mul n k)(mul m k) — GENERAL, machine-checked. Induction on n;
    // base definitional; step CONSUMES the IH via ap_plus_l and re-associates with add_assoc. Nat
    // non-indexed ⇒ the ι-driver fires on the open recursive field (driver.rs:109-112).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &mul_distrib_r(), &mul_distrib_r_ty()).is_ok(),
        "mul_distrib_r : Π(n m k:Nat). Id Nat (mul (add n m) k) (add (mul n k)(mul m k))"
    );
}

#[test]
fn false_mul_distrib_r_rejected() {
    // NO-FALSE-GREEN: `mul (add n m) k = add (mul n k)(mul n k)` (m→n on the rhs second term) is FALSE.
    let env = env();
    let bad_ty = pi(
        nat_ty(),
        pi(
            nat_ty(),
            pi(
                nat_ty(),
                id_nat(
                    mul(add(Tm::Var(2), Tm::Var(1)), Tm::Var(0)),
                    add(
                        mul(Tm::Var(2), Tm::Var(0)),
                        mul(Tm::Var(2), Tm::Var(0)), // mul n k (should be mul m k)
                    ),
                ),
            ),
        ),
    );
    assert_eq!(
        check(&env, &Vec::new(), &mul_distrib_r(), &bad_ty),
        Err(TypeError::Mismatch),
        "mul_distrib_r does NOT prove (n+m)*k = n*k + n*k  (no false-green)"
    );
}

// ════════════════════════ closed-compute sanity + non-vacuity ════════════════════════

#[test]
fn mul_two_three_nf_is_six() {
    // Closed-compute sanity: `mul 2 3` ι-normalizes to the literal `6`, convertible to `6` but
    // NOT to `5` or `7`.
    let env = env();
    let nf = nf_tm(&env, &Vec::new(), &mul(lit(2), lit(3)));
    assert_eq!(nf, lit(6), "mul 2 3 ι-normalizes to 6");
    assert!(
        conv(&env, &Vec::new(), &mul(lit(2), lit(3)), &lit(6)).unwrap(),
        "mul 2 3 ≡ 6"
    );
    assert!(
        !conv(&env, &Vec::new(), &mul(lit(2), lit(3)), &lit(5)).unwrap(),
        "mul 2 3 ≢ 5"
    );
    assert!(
        !conv(&env, &Vec::new(), &mul(lit(2), lit(3)), &lit(7)).unwrap(),
        "mul 2 3 ≢ 7"
    );
}

#[test]
fn mul_comm_closed_instance_is_refl() {
    // End-to-end ι evidence: the closed proof `mul_comm 2 3 : Id Nat (mul 2 3)(mul 3 2)` ≡
    // `Id Nat 6 6` NORMALIZES to the canonical witness `refl Nat 6`, convertible to it but NOT to a
    // wrong witness `refl Nat 5` — the proof is non-vacuous.
    let env = env();
    let inst = apps(mul_comm(), &[lit(2), lit(3)]);
    let refl6 = refl_nat(lit(6));
    assert_eq!(
        nf_tm(&env, &Vec::new(), &inst),
        refl6,
        "mul_comm 2 3 ι-normalizes to refl Nat 6"
    );
    assert!(
        conv(&env, &Vec::new(), &inst, &refl6).unwrap(),
        "mul_comm 2 3 ≡ refl Nat 6"
    );
    assert!(
        !conv(&env, &Vec::new(), &inst, &refl_nat(lit(5))).unwrap(),
        "mul_comm 2 3 ≢ refl Nat 5 (off by one)"
    );
}

#[test]
fn mul_distrib_r_closed_instance_is_refl() {
    // Non-vacuity for distributivity at closed args: `mul_distrib_r 2 3 4 :
    // Id Nat (mul (add 2 3) 4) (add (mul 2 4)(mul 3 4))` ≡ `Id Nat 20 20`, normalizing to `refl Nat 20`.
    let env = env();
    let inst = mul_distrib_r_at(lit(2), lit(3), lit(4));
    let refl20 = refl_nat(lit(20));
    assert_eq!(
        nf_tm(&env, &Vec::new(), &inst),
        refl20,
        "mul_distrib_r 2 3 4 ι-normalizes to refl Nat 20"
    );
    assert!(
        !conv(&env, &Vec::new(), &inst, &refl_nat(lit(19))).unwrap(),
        "mul_distrib_r 2 3 4 ≢ refl Nat 19 (off by one)"
    );
}

#[test]
fn mul_succ_r_closed_instance_is_refl() {
    // Non-vacuity for the succ law at closed args: `mul_succ_r 3 2 :
    // Id Nat (mul 3 (succ 2)) (add 3 (mul 3 2))` ≡ `Id Nat 9 9`, normalizing to `refl Nat 9`.
    let env = env();
    let inst = mul_succ_r_at(lit(3), lit(2));
    let refl9 = refl_nat(lit(9));
    assert_eq!(
        nf_tm(&env, &Vec::new(), &inst),
        refl9,
        "mul_succ_r 3 2 ι-normalizes to refl Nat 9"
    );
    assert!(
        !conv(&env, &Vec::new(), &inst, &refl_nat(lit(8))).unwrap(),
        "mul_succ_r 3 2 ≢ refl Nat 8 (off by one)"
    );
}
