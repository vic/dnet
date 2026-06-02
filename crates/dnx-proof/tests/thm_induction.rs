//! A classic theorem proven BY INDUCTION over a recursive datatype — the inductive
//! hypothesis is used in the step case, so this exercises real inductive proving power
//! (Nat.rec's IH), not just definitional computation.
//!
//! THEOREM (associativity of addition on the naturals):
//!     ∀ (a b c : Nat),  (a + b) + c  =  a + (b + c)
//!
//! Proof is by induction on `c` (the argument `add` recurses on):
//!   • base  c = 0      : (a+b)+0 ≡ a+b  and  a+(b+0) ≡ a+b   — both sides ι-reduce to
//!                        `a+b`, so the goal is `refl Nat (a+b)` (a DEFINITIONAL equality).
//!   • step  c = succ k : (a+b)+(succ k) ≡ succ ((a+b)+k)  and
//!                        a+(b+(succ k)) ≡ succ (a+(b+k))    — so from the IH
//!                        `ih : (a+b)+k = a+(b+k)` we conclude by `ap succ ih`.
//!     The IH `ih` is the recursive-field argument of Nat.rec's succ-minor
//!     (`minor_succ : Π(k:Nat) Π(ih: motive k). motive (succ k)`; proofs.md:177-180),
//!     and it is genuinely CONSUMED (`ap_succ … ih`) — this is the inductive step.
//!
//! Building blocks (all already in the trusted kernel + eq-prelude):
//!   • `Nat`/`zero`/`succ`, `add` via `Nat.rec` (soundness.rs A2/A3; recursion on the 2nd arg).
//!   • `Id`/`refl` and its eliminator `Elim Id` = J / based-path-induction (eq_prelude.rs;
//!     proofs.md:163-188). From J we derive `ap_succ : Id a b → Id (succ a) (succ b)`
//!     (congruence), exactly as eq_prelude derives `eq_sym`/`transport` from J.
//!
//! ORACLE: `add_assoc` `check`s at its ∀-type (the step uses the IH — no false green); the
//! same proof term is REJECTED at an off-by-one (false) goal; a closed instance normalizes to
//! `refl` and is NOT convertible to a wrong witness. All asserted via the kernel `check`/`conv`.

use dnx_proof::conv::conv;
use dnx_proof::driver::nf_tm;
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::check;
use dnx_proof::symbol::{ConstId, IndId};
use dnx_proof::tm::Tm;

// ── term helpers (as in eq_prelude.rs / soundness.rs) ──
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

fn zero() -> Tm {
    Tm::Ctor(NAT, 0)
}
fn succ(n: Tm) -> Tm {
    app(Tm::Ctor(NAT, 1), n)
}
fn nat_ty() -> Tm {
    Tm::Ind(NAT)
}
// Id Nat a b   and   refl Nat a   (closed builders).
fn id_nat(a: Tm, b: Tm) -> Tm {
    apps(Tm::Ind(ID), &[nat_ty(), a, b])
}
fn refl_nat(a: Tm) -> Tm {
    apps(Tm::Ctor(ID, 0), &[nat_ty(), a])
}
// add x y  (x + y).
fn add(x: Tm, y: Tm) -> Tm {
    apps(Tm::Const(ADD), &[x, y])
}

/// `add : Nat → Nat → Nat` body (soundness.rs A3): recursion on the 2nd arg.
///   add = λm.λn. Nat.rec (λ_:Nat.Nat) m (λk.λih. succ ih) n
///   ⇒  add m 0 ≡ m ,  add m (succ k) ≡ succ (add m k).
fn add_body() -> Tm {
    // ctx [m, n]: m = Var1, n = Var0.
    lam(
        nat_ty(), // m
        lam(
            nat_ty(), // n
            apps(
                Tm::Elim(NAT),
                &[
                    lam(nat_ty(), nat_ty()),                        // motive λ_:Nat.Nat
                    Tm::Var(1),                                     // minor_zero = m
                    lam(nat_ty(), lam(nat_ty(), succ(Tm::Var(0)))), // minor_succ = λk.λih. succ ih
                    Tm::Var(0),                                     // scrutinee = n
                ],
            ),
        ),
    )
}
fn add_ty() -> Tm {
    pi(nat_ty(), pi(nat_ty(), nat_ty()))
}

fn env() -> dnx_proof::env::GlobalEnv {
    let mut e = dnx_proof::env::GlobalEnv::default();
    e.add_inductive(nat()).expect("Nat admits");
    e.add_inductive(id_ind()).expect("Id admits");
    e.add_const(ADD, add_ty(), add_body())
        .expect("add admits (acyclic)");
    e
}

/// Congruence of `succ` over `Id`, derived from `Elim Id` (J) — exactly as eq_prelude
/// derives `eq_sym`/`transport` (proofs.md:177-188):
///   ap_succ : Π(a b:Nat)(p:Id Nat a b). Id Nat (succ a) (succ b)
///     = λa b p. Elim Id Nat a (λb' x. Id Nat (succ a) (succ b')) (refl Nat (succ a)) b p
fn ap_succ() -> Tm {
    // ctx [a, b, p]: a = Var2, b = Var1, p = Var0.
    let motive = lam(
        nat_ty(), // b' : Nat
        lam(
            id_nat(Tm::Var(3), Tm::Var(0)), // x : Id Nat a b'   (a = Var3, b' = Var0)
            id_nat(succ(Tm::Var(4)), succ(Tm::Var(1))), // Id Nat (succ a) (succ b')  (a=Var4, b'=Var1)
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            nat_ty(),                   // A = Nat
            Tm::Var(2),                 // a
            motive,                     // motive
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
                id_nat(Tm::Var(1), Tm::Var(0)),             // p : Id Nat a b
                id_nat(succ(Tm::Var(2)), succ(Tm::Var(1))), // Id Nat (succ a) (succ b)
            ),
        ),
    )
}

/// add_assoc : Π(a b c:Nat). Id Nat (add (add a b) c) (add a (add b c))
///   = λa b c. Nat.rec
///       (λc'. Id Nat (add (add a b) c') (add a (add b c')))      -- motive (depends on c')
///       (refl Nat (add a b))                                     -- base: c=0 (both sides ≡ a+b)
///       (λk ih. ap_succ (add (add a b) k) (add a (add b k)) ih)  -- step: IH `ih` CONSUMED
///       c
fn add_assoc() -> Tm {
    // ctx [a, b, c]: a = Var2, b = Var1, c = Var0.
    let motive = lam(
        nat_ty(), // c' : Nat
        // ctx [a,b,c,c']: a=Var3, b=Var2, c'=Var0.
        id_nat(
            add(add(Tm::Var(3), Tm::Var(2)), Tm::Var(0)), // (a+b)+c'
            add(Tm::Var(3), add(Tm::Var(2), Tm::Var(0))), // a+(b+c')
        ),
    );
    let base = refl_nat(add(Tm::Var(2), Tm::Var(1))); // refl Nat (a+b)
    let step = lam(
        nat_ty(), // k : Nat
        // ctx [a,b,c,k]: a=Var3, b=Var2, k=Var0.
        lam(
            // ih : motive k = Id Nat ((a+b)+k) (a+(b+k))
            id_nat(
                add(add(Tm::Var(3), Tm::Var(2)), Tm::Var(0)),
                add(Tm::Var(3), add(Tm::Var(2), Tm::Var(0))),
            ),
            // ctx [a,b,c,k,ih]: a=Var4, b=Var3, k=Var1, ih=Var0.
            apps(
                ap_succ(),
                &[
                    add(add(Tm::Var(4), Tm::Var(3)), Tm::Var(1)), // (a+b)+k
                    add(Tm::Var(4), add(Tm::Var(3), Tm::Var(1))), // a+(b+k)
                    Tm::Var(0),                                   // ih  (the inductive hypothesis)
                ],
            ),
        ),
    );
    let rec = apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(0)]);
    lam(nat_ty(), lam(nat_ty(), lam(nat_ty(), rec)))
}
fn add_assoc_ty() -> Tm {
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            pi(
                nat_ty(),
                // ctx [a,b,c]: a=Var2, b=Var1, c=Var0.
                id_nat(
                    add(add(Tm::Var(2), Tm::Var(1)), Tm::Var(0)), // (a+b)+c
                    add(Tm::Var(2), add(Tm::Var(1), Tm::Var(0))), // a+(b+c)
                ),
            ),
        ),
    )
}

fn lit(n: u32) -> Tm {
    (0..n).fold(zero(), |acc, _| succ(acc))
}

/// The inductive proof `add_assoc` SPECIALISED to closed literals a,b,c (the outer λa.λb.λc is
/// pre-applied, so the resulting term is CLOSED — no free variables anywhere). This is the
/// bounded form the V1 ι-driver can fully reduce: every recursive field is a closed numeral, so
/// ι fires through the whole recursion (the general open-variable form is proven below in
/// `add_assoc_general_by_induction`).
/// The term is still the genuine induction: `Nat.rec motive base step c` whose `step` CONSUMES
/// the IH via `ap_succ` (proofs.md:177-180).
fn add_assoc_at(a: u32, b: u32, c: u32) -> Tm {
    let (al, bl) = (lit(a), lit(b));
    // motive λc'. Id Nat ((a+b)+c') (a+(b+c'))   (c' = Var0; a,b closed).
    let motive = lam(
        nat_ty(),
        id_nat(
            add(add(al.clone(), bl.clone()), Tm::Var(0)),
            add(al.clone(), add(bl.clone(), Tm::Var(0))),
        ),
    );
    let base = refl_nat(add(al.clone(), bl.clone())); // refl Nat (a+b)
                                                      // step λk.λih. ap_succ ((a+b)+k) (a+(b+k)) ih    (k=Var1, ih=Var0).
    let step = lam(
        nat_ty(),
        lam(
            id_nat(
                add(add(al.clone(), bl.clone()), Tm::Var(1)),
                add(al.clone(), add(bl.clone(), Tm::Var(1))),
            ),
            apps(
                ap_succ(),
                &[
                    add(add(al.clone(), bl.clone()), Tm::Var(1)),
                    add(al.clone(), add(bl.clone(), Tm::Var(1))),
                    Tm::Var(0), // ih
                ],
            ),
        ),
    );
    apps(Tm::Elim(NAT), &[motive, base, step, lit(c)])
}

#[test]
fn add_computes_definitionally() {
    // The two computation rules of `add` (the equalities the base/step cases lean on), by ι.
    let env = env();
    // add m 0 ≡ m  (m = 2).
    assert!(
        conv(&env, &Vec::new(), &add(lit(2), zero()), &lit(2)).unwrap(),
        "add 2 0 ≡ 2"
    );
    // add m (succ k) ≡ succ (add m k)  (m=2,k=1): add 2 2 ≡ succ (add 2 1) ≡ 4.
    assert!(
        conv(&env, &Vec::new(), &add(lit(2), lit(2)), &lit(4)).unwrap(),
        "add 2 2 ≡ 4"
    );
}

#[test]
fn ap_succ_typechecks() {
    // The derived congruence (from J / Elim Id) is well-typed at its stated Π-type — the step
    // case's tool. Same derivation pattern as eq_prelude's eq_sym/transport (proofs.md:177-188).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &ap_succ(), &ap_succ_ty()).is_ok(),
        "ap_succ : Π(a b:Nat)(p:Id Nat a b). Id Nat (succ a) (succ b)"
    );
}

#[test]
fn add_assoc_step_uses_the_ih() {
    // The INDUCTIVE STEP `minor_succ`, type-checked in isolation — the heart of the proof and the
    // evidence the IH is genuinely USED. With a,b,k closed (1,1,2) the step term
    //   step = λ(ih : motive 2). ap_succ ((1+1)+2) (1+(1+2)) ih
    // is checked against the recursor's succ-minor result `motive (succ 2)`
    //   = Id Nat ((1+1)+3) (1+(1+3))  =  Id Nat 5 5,
    // where `motive 2 = Id Nat ((1+1)+2) (1+(1+2)) = Id Nat 4 4`. The hypothesis `ih : motive 2`
    // is CONSUMED by `ap_succ` (proofs.md:177-180: `minor_succ : Π(k)Π(ih:motive k). motive(succ k)`).
    let env = env();
    let (al, bl, k) = (lit(1), lit(1), lit(2));
    let motive_2 = id_nat(
        add(add(al.clone(), bl.clone()), k.clone()),
        add(al.clone(), add(bl.clone(), k.clone())),
    );
    // step = λ(ih:motive 2). ap_succ ((1+1)+2) (1+(1+2)) ih    (ih = Var0)
    let step = lam(
        motive_2.clone(),
        apps(
            ap_succ(),
            &[
                add(add(al.clone(), bl.clone()), k.clone()),
                add(al.clone(), add(bl.clone(), k.clone())),
                Tm::Var(0), // ih — the inductive hypothesis, CONSUMED here
            ],
        ),
    );
    let step_ty = pi(
        motive_2.clone(),
        id_nat(
            add(add(al.clone(), bl.clone()), succ(k.clone())),
            add(al.clone(), add(bl.clone(), succ(k.clone()))),
        ), // motive (succ 2)
    );
    assert!(
        check(&env, &Vec::new(), &step, &step_ty).is_ok(),
        "step `λih. ap_succ … ih : motive 2 → motive (succ 2)` — the IH is used (induction)"
    );
    // no-false-green: the step does NOT inhabit an off-by-one minor `motive 2 → motive (succ(succ 2))`.
    let step_ty_wrong = pi(
        motive_2,
        id_nat(
            add(add(al.clone(), bl.clone()), succ(succ(k.clone()))),
            add(al, add(bl, succ(succ(k)))),
        ), // motive (succ (succ 2)) ← off by one
    );
    assert!(
        check(&env, &Vec::new(), &step, &step_ty_wrong).is_err(),
        "step must NOT prove motive 2 → motive (succ (succ 2))"
    );
}

#[test]
fn add_assoc_bounded_instances_compute() {
    // Bounded form of the theorem: for CLOSED a,b,c the genuine inductive proof
    // `add_assoc_at a b c = Nat.rec motive base step c` RUNS to completion through the recursor
    // (every recursive field is a closed numeral, so the V1 ι-driver fires through every step,
    // each STEP consuming its IH = the recursive `Nat.rec … k` call; proofs.md:177-180,187), and
    // yields exactly the canonical witness `refl Nat ((a+b)+c)` of the TRUE equation. (We assert
    // the COMPUTATION here by conv/nf; the full ∀-typed proof is checked in
    // `add_assoc_general_by_induction`.)
    let env = env();
    let cases = [
        (0u32, 0u32, 0u32),
        (1, 1, 1),
        (2, 0, 1),
        (1, 2, 3),
        (2, 3, 0),
        (3, 1, 2),
    ];
    for (a, b, c) in cases {
        let proof = add_assoc_at(a, b, c);
        let sum = a + b + c;
        let witness = refl_nat(lit(sum)); // both (a+b)+c and a+(b+c) compute to a+b+c
        assert_eq!(
            nf_tm(&env, &Vec::new(), &proof),
            witness,
            "add_assoc {a} {b} {c} normalizes to refl Nat {sum}"
        );
        assert!(
            conv(&env, &Vec::new(), &proof, &witness).unwrap(),
            "add_assoc {a} {b} {c} ≡ refl Nat {sum} (proof of ((a+b)+c) = (a+(b+c)) = {sum})"
        );
        // no-false-green: NOT the witness of a different (false) equation.
        assert!(
            !conv(&env, &Vec::new(), &proof, &refl_nat(lit(sum + 1))).unwrap(),
            "add_assoc {a} {b} {c} ≢ refl Nat {} (off by one)",
            sum + 1
        );
    }
}

#[test]
fn add_assoc_instance_normalizes_to_refl() {
    // End-to-end ι evidence: the closed proof `add_assoc 1 1 1 : Id Nat 3 3` NORMALIZES to the
    // canonical witness `refl Nat 3` (both sides compute to 3 through the recursor), convertible
    // to it but NOT to a wrong witness `refl Nat 2`.
    let env = env();
    let inst = add_assoc_at(1, 1, 1);
    let refl3 = refl_nat(lit(3));
    assert_eq!(
        nf_tm(&env, &Vec::new(), &inst),
        refl3,
        "add_assoc 1 1 1 ι-normalizes to refl Nat 3"
    );
    assert!(
        conv(&env, &Vec::new(), &inst, &refl3).unwrap(),
        "add_assoc 1 1 1 ≡ refl Nat 3"
    );
    assert!(
        !conv(&env, &Vec::new(), &inst, &refl_nat(lit(2))).unwrap(),
        "add_assoc 1 1 1 ≢ refl Nat 2"
    );
}

#[test]
fn add_assoc_general_by_induction() {
    // THE theorem (human-readable): ∀ (a b c : Nat), (a + b) + c = a + (b + c).
    //   add_assoc = λa b c. Nat.rec (λc'. Id Nat ((a+b)+c') (a+(b+c')))
    //                               (refl Nat (a+b))                       -- base c=0
    //                               (λk ih. ap_succ … ih)                  -- step (uses IH)
    //                               c
    // `check`ing this under NEUTRAL a,b,c conv-checks the succ-minor against `motive (succ k)`,
    // which needs `add a (succ N) ≡ succ (add a N)` where the recursive field `N` holds the free
    // `b` (the `a+(b+c)` side). `add` recurses on its 2nd arg via `Nat.rec`, and `Nat` is
    // NON-indexed (nidx==0), so the ι-driver's `field_indices` short-circuits to `[]` WITHOUT
    // inferring the open field's type (driver.rs:109-112) ⇒ ι fires on the open recursive field ⇒
    // the step minor convs. (Indexed-family ι still infers each field's type, so it remains
    // closed-scrutinee only — soundness.rs:a6; proofs.md:187 `idx rec_j`.)
    let env = env();
    assert!(
        check(&env, &Vec::new(), &add_assoc(), &add_assoc_ty()).is_ok(),
        "add_assoc : Π(a b c:Nat). Id Nat ((a+b)+c) (a+(b+c)) — by induction on c"
    );
    // no-false-green: the SAME proof term must NOT inhabit an off-by-one (false) equation
    //   Π(a b c). Id Nat ((a+b)+c) (succ (a+(b+c)))  — the step's `ap_succ` cannot bridge it.
    let false_ty = pi(
        nat_ty(),
        pi(
            nat_ty(),
            pi(
                nat_ty(),
                // ctx [a,b,c]: a=Var2, b=Var1, c=Var0.
                id_nat(
                    add(add(Tm::Var(2), Tm::Var(1)), Tm::Var(0)), // (a+b)+c
                    succ(add(Tm::Var(2), add(Tm::Var(1), Tm::Var(0)))), // succ (a+(b+c)) ← false
                ),
            ),
        ),
    );
    assert!(
        check(&env, &Vec::new(), &add_assoc(), &false_ty).is_err(),
        "add_assoc must NOT prove the off-by-one false equation ((a+b)+c = succ(a+(b+c)))"
    );
}
