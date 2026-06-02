//! Four-colour-CLASS dependent-type proof of a genuine LOWER BOUND — "the triangle K3 needs ≥3
//! colours" — by FINITE EXHAUSTION, typechecked by the dnx-proof kernel TODAY via the Tm-level
//! recursor-ι path (driver.rs `try_iota`) + `Id`/`refl` reflection (proofs.md §4-5; eq_prelude.rs).
//! HONEST SCOPE: this is NOT the four-colour theorem. It is a concrete, demo-sized result about ONE
//! named graph, closed by COMPUTING over a FINITE colour space and inhabiting `Id Bool checker true`
//! with `refl`. The "∀ 2-colouring" quantifier is ELIMINATED into a finite OR-fold that ι computes —
//! exactly the fourcolor-CLASS move (decidable + finite + reflected), scoped to one tiny graph.
//! Mirrors fourcolor_coloring.rs in structure, adding the dual `or` combinator and an 8-way fold.
//!
//! ── THE GRAPH (human-readable) ────────────────────────────────────────────────────────────
//!   K3 = the complete triangle on vertices {0,1,2}, edge set { (0,1), (1,2), (2,0) }. It is the
//!        minimal graph with chromatic number 3 (every pair of vertices is adjacent, so no two may
//!        share a colour ⇒ 3 colours are required and suffice).
//!   Four colours available: Color = { c0, c1, c2, c3 }; the lower-bound argument uses only {c0,c1}.
//!
//! ── THE PREDICATES ────────────────────────────────────────────────────────────────────────
//!   proper_k3(x0,x1,x2) := neqc x0 x1 ∧ neqc x1 x2 ∧ neqc x2 x0    (the 3 edges of K3).
//!   any_2col_k3 : Bool   := OR over all 8 colourings with each vertex ∈ {c0,c1} of proper_k3(…).
//!                          "Does ANY 2-colouring (over the two fixed colours c0,c1) of K3 work?"
//!   Both are closed `Bool`-valued decision procedures (`Elim`-folds, no recursion ⇒ ι-computable).
//!
//! ── THE THEOREM (human-readable) ──────────────────────────────────────────────────────────
//!   THEOREM ("K3 needs ≥3 colours"):  is_true (not any_2col_k3)
//!     ≡ "no 2-colouring of K3 over {c0,c1} is proper"  ≡  K3 is NOT 2-colourable.
//!   any_2col_k3 ι-reduces: every one of the 8 disjuncts ⟶ false (3 vertices from 2 colours force
//!   a repeated adjacent pair, pigeonhole), so the OR ⟶ false and `not false` ⟶ true.
//!   PROOF TERM:  refl Bool true : Id Bool (not any_2col_k3) true.
//!   COMPANION (upper bound): proper_k3 c0 c1 c2 ⟶ true, refl Bool true : Id Bool (proper_k3 c0 c1
//!   c2) true — "3 colours suffice". Together: needs 3, and 3 suffice.
//!
//! ── NEGATIVE (no-false-green) ─────────────────────────────────────────────────────────────
//!   The bogus claim "K3 IS 2-colourable", is_true any_2col_k3 (i.e. refl Bool true : Id Bool
//!   any_2col_k3 true), is REJECTED because any_2col_k3 ≡ false. THIS IS THE LOAD-BEARING NEGATIVE:
//!   it proves the exhaustion is real, not vacuous. `refl Bool false` against the good goal is
//!   rejected too (wrong index).
//!
//! ── SCOPE CAPTION ─────────────────────────────────────────────────────────────────────────
//!   "≥3 colours" here means "not 2-colourable over the two fixed colours c0,c1, checked by
//!   exhausting all 8 assignments". We rely on 2-colourability being invariant under colour
//!   renaming (any two colours are interchangeable for "is there a proper 2-colouring") — immediate,
//!   stated so the claim is not overread. We do NOT claim a universal theorem over all graphs.
//!
//! Inductives:  Color = c0|c1|c2|c3 (IndId 0); Bool = false|true (IndId 1);
//!              Id = Π(A:Sort0)(a:A). A → Sort0 := refl (IndId 2; the `=` of is_true).
//! Consts:      not, eqc, neqc, proper_k3, any_2col_k3 (Elim-folds → Bool; ι-computable, no recursion).

use dnx_proof::conv::conv;
use dnx_proof::driver::nf_tm;
use dnx_proof::env::GlobalEnv;
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::check;
use dnx_proof::symbol::{ConstId, IndId};
use dnx_proof::tm::Tm;

// ── tiny builders (de Bruijn, as in eq_prelude.rs / fourcolor_coloring.rs) ──
fn lam(dom: Tm, b: Tm) -> Tm {
    Tm::Lam(Box::new(dom), Box::new(b))
}
fn app(f: Tm, x: Tm) -> Tm {
    Tm::App(Box::new(f), Box::new(x))
}
fn apps(head: Tm, args: &[Tm]) -> Tm {
    args.iter().fold(head, |f, a| app(f, a.clone()))
}
fn pi(dom: Tm, b: Tm) -> Tm {
    Tm::Pi(Box::new(dom), Box::new(b))
}

const COLOR: IndId = IndId(0);
const BOOL: IndId = IndId(1);
const ID: IndId = IndId(2);
const NOT: ConstId = ConstId(0);
const EQC: ConstId = ConstId(1);
const NEQC: ConstId = ConstId(2);
const PROPER_K3: ConstId = ConstId(3);
const ANY_2COL_K3: ConstId = ConstId(4);

// ── Color = c0 | c1 | c2 | c3 ──
fn color_ind() -> Inductive {
    Inductive {
        id: COLOR,
        params: vec![],
        indices: vec![],
        sort: 0,
        ctors: (0..4)
            .map(|k| CtorDecl {
                ctor_ix: k,
                args: vec![],
                ret_indices: vec![],
            })
            .collect(),
    }
}
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
/// Id : Π(A:Sort0)(a:A). A → Sort0 := refl  (indexed; the `=` of `is_true`).
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

fn col(k: u32) -> Tm {
    Tm::Ctor(COLOR, k)
}
fn fls() -> Tm {
    Tm::Ctor(BOOL, 0)
}
fn tru() -> Tm {
    Tm::Ctor(BOOL, 1)
}
fn id_ty(a_ty: Tm, a: Tm, b: Tm) -> Tm {
    apps(Tm::Ind(ID), &[a_ty, a, b])
}
fn refl(a_ty: Tm, a: Tm) -> Tm {
    apps(Tm::Ctor(ID, 0), &[a_ty, a])
}

/// not := λb:Bool. Elim Bool (λ_:Bool.Bool) true false b   (¬: swaps the two ctors).
fn not_body() -> Tm {
    let motive = lam(Tm::Ind(BOOL), Tm::Ind(BOOL));
    lam(
        Tm::Ind(BOOL),
        apps(Tm::Elim(BOOL), &[motive, tru(), fls(), Tm::Var(0)]),
    )
}

/// eqc := λa:Color.λb:Color. Elim Color (λ_.Bool) M0 M1 M2 M3 a  — decidable colour equality.
fn eqc_body() -> Tm {
    let is_k = |row: u32| -> Tm {
        let motive = lam(Tm::Ind(COLOR), Tm::Ind(BOOL));
        let minors: Vec<Tm> = (0..4)
            .map(|c| if c == row { tru() } else { fls() })
            .collect();
        let mut spine = vec![motive];
        spine.extend(minors);
        spine.push(Tm::Var(0)); // scrutinee b
        apps(Tm::Elim(COLOR), &spine)
    };
    let outer_motive = lam(Tm::Ind(COLOR), Tm::Ind(BOOL));
    let mut spine = vec![outer_motive];
    for row in 0..4 {
        spine.push(is_k(row));
    }
    spine.push(Tm::Var(1)); // scrutinee a
    lam(
        Tm::Ind(COLOR),
        lam(Tm::Ind(COLOR), apps(Tm::Elim(COLOR), &spine)),
    )
}

/// neqc := λa:Color.λb:Color. not (eqc a b).
fn neqc_body() -> Tm {
    lam(
        Tm::Ind(COLOR),
        lam(
            Tm::Ind(COLOR),
            app(
                Tm::Const(NOT),
                apps(Tm::Const(EQC), &[Tm::Var(1), Tm::Var(0)]),
            ),
        ),
    )
}

/// and := λa.λb. Elim Bool (λ_.Bool) false b a   (short-circuit AND).
fn and(a: Tm, b: Tm) -> Tm {
    let motive = lam(Tm::Ind(BOOL), Tm::Ind(BOOL));
    apps(Tm::Elim(BOOL), &[motive, fls(), b, a])
}

/// or := λa.λb. Elim Bool (λ_.Bool) b true a   (short-circuit OR; the DUAL of `and`).
/// Spine: motive · minor_false · minor_true · scrutinee. a=false ⟶ b (the other operand);
/// a=true ⟶ true. So `or false b ⟶ b`, `or true b ⟶ true`. (plan §4:303.)
fn or(a: Tm, b: Tm) -> Tm {
    let motive = lam(Tm::Ind(BOOL), Tm::Ind(BOOL));
    apps(Tm::Elim(BOOL), &[motive, b, tru(), a])
}

/// proper_k3 := λx0 x1 x2 : Color. neqc x0 x1 ∧ neqc x1 x2 ∧ neqc x2 x0.
/// The three conjuncts ARE the three edges of K3 = {(0,1),(1,2),(2,0)}. After the three binders:
/// ctx [x0,x1,x2] ⇒ x0=Var2, x1=Var1, x2=Var0.
fn proper_k3_body() -> Tm {
    let edge = |u: u32, v: u32| apps(Tm::Const(NEQC), &[Tm::Var(u), Tm::Var(v)]);
    let e01 = edge(2, 1); // (0,1)
    let e12 = edge(1, 0); // (1,2)
    let e20 = edge(0, 2); // (2,0)
    let body = and(e01, and(e12, e20));
    lam(
        Tm::Ind(COLOR),
        lam(Tm::Ind(COLOR), lam(Tm::Ind(COLOR), body)),
    )
}

/// any_2col_k3 : Bool  (a 0-ary const naming the finite exhaustion).
/// = OR over the 8 colourings with each of the 3 vertices ∈ {c0,c1} of `proper_k3 a b c`.
/// Built programmatically (plan §1 DEMO C builder loop), so the term is generated not hand-spelled.
fn any_2col_k3_body() -> Tm {
    let cols = [col(0), col(1)];
    let mut acc = fls();
    for a in 0..2 {
        for b in 0..2 {
            for c in 0..2 {
                let disj = apps(
                    Tm::Const(PROPER_K3),
                    &[cols[a].clone(), cols[b].clone(), cols[c].clone()],
                );
                acc = or(acc, disj);
            }
        }
    }
    acc
}

/// is_true b := Id Bool b true.
fn is_true(b: Tm) -> Tm {
    id_ty(Tm::Ind(BOOL), b, tru())
}

/// proper_k3 x0 x1 x2  for concrete colours.
fn proper_of3(x0: Tm, x1: Tm, x2: Tm) -> Tm {
    apps(Tm::Const(PROPER_K3), &[x0, x1, x2])
}

/// not_ c  — apply the `not` const to a closed Bool.
fn not_(c: Tm) -> Tm {
    app(Tm::Const(NOT), c)
}

/// Build the demo environment; surfaces any admission gap as the `Result` of `add_*`.
fn demo_env() -> Result<GlobalEnv, dnx_proof::env::AdmitError> {
    let mut e = GlobalEnv::default();
    e.add_inductive(color_ind())?;
    e.add_inductive(bool_ind())?;
    e.add_inductive(id_ind())?;
    let bool_to_bool = pi(Tm::Ind(BOOL), Tm::Ind(BOOL));
    let cc_to_bool = pi(Tm::Ind(COLOR), pi(Tm::Ind(COLOR), Tm::Ind(BOOL)));
    let ccc_to_bool = pi(
        Tm::Ind(COLOR),
        pi(Tm::Ind(COLOR), pi(Tm::Ind(COLOR), Tm::Ind(BOOL))),
    );
    e.add_const(NOT, bool_to_bool, not_body())?;
    e.add_const(EQC, cc_to_bool.clone(), eqc_body())?;
    e.add_const(NEQC, cc_to_bool, neqc_body())?;
    e.add_const(PROPER_K3, ccc_to_bool, proper_k3_body())?;
    // any_2col_k3 references PROPER_K3, so it must be admitted AFTER it (δ-acyclicity R7).
    e.add_const(ANY_2COL_K3, Tm::Ind(BOOL), any_2col_k3_body())?;
    Ok(e)
}

// ════════════════════════ ADMISSION (kernel-have check) ════════════════════════

#[test]
fn admits_color_bool_id_and_consts() {
    // Color/Bool/Id + not/eqc/neqc/proper_k3/any_2col_k3 must all pass the SOUNDNESS gates
    // (positivity R3, field-universe R11, δ-acyclicity R7). any_2col_k3 is a closed Bool const
    // referencing proper_k3 — admitting it exercises δ-acyclicity on the dependency.
    let env = demo_env().expect("Color/Bool/Id + not/eqc/neqc/proper_k3/any_2col_k3 admitted");
    assert!(env.inds.contains_key(&COLOR), "4-colour inductive admitted");
    assert!(
        env.const_body(ANY_2COL_K3).is_some(),
        "any_2col_k3 finite-exhaustion const stored"
    );
}

// ════════════════════════ ι CHAIN (the decision procedures compute) ════════════════════════

#[test]
fn proper_k3_computes_true_on_3_coloring() {
    // K3 IS 3-colourable: the all-distinct colouring [c0,c1,c2] makes every edge bichromatic.
    let env = demo_env().expect("demo env");
    assert_eq!(
        nf_tm(&env, &Vec::new(), &proper_of3(col(0), col(1), col(2))),
        tru(),
        "proper_k3 c0 c1 c2 ι-reduces to Bool.true (3 colours suffice for K3)"
    );
}

#[test]
fn proper_k3_computes_false_on_2_coloring() {
    // Any colouring of K3 reusing a colour fails: [c0,c0,c1] clashes on edge (0,1).
    let env = demo_env().expect("demo env");
    assert_eq!(
        nf_tm(&env, &Vec::new(), &proper_of3(col(0), col(0), col(1))),
        fls(),
        "proper_k3 c0 c0 c1 ι-reduces to Bool.false (edge (0,1) monochromatic)"
    );
}

#[test]
fn any_2col_k3_computes_false_by_exhaustion() {
    // The HEART of the lower bound: the OR over ALL 8 two-colourings of K3 ι-reduces to false —
    // every assignment of {c0,c1} to 3 mutually-adjacent vertices repeats a colour on some edge.
    let env = demo_env().expect("demo env");
    assert_eq!(
        nf_tm(&env, &Vec::new(), &Tm::Const(ANY_2COL_K3)),
        fls(),
        "any_2col_k3 ι-reduces to Bool.false (no 2-colouring of K3 over c0,c1 is proper)"
    );
}

#[test]
fn not_any_2col_k3_computes_true() {
    // Therefore `not any_2col_k3` ι-reduces to true — "K3 is NOT 2-colourable".
    let env = demo_env().expect("demo env");
    assert_eq!(
        nf_tm(&env, &Vec::new(), &not_(Tm::Const(ANY_2COL_K3))),
        tru(),
        "not any_2col_k3 ι-reduces to Bool.true (K3 needs ≥3 colours)"
    );
}

// ════════════════════════ THE THEOREM: K3 needs ≥3 colours, by finite exhaustion ════════════

#[test]
fn thm_k3_needs_three_colours_typechecks() {
    // THEOREM:  is_true (not any_2col_k3)  — no 2-colouring of K3 over {c0,c1} is proper, i.e.
    // K3 is not 2-colourable ⇒ needs ≥3 colours. PROOF: refl Bool true : Id Bool (not any_2col_k3)
    // true. The kernel ι-reduces the 8-way OR to false then `not` to true; the diagonal `refl`
    // inhabits the equality. This is a genuine machine-checked LOWER BOUND via finite exhaustion.
    let env = demo_env().expect("demo env");
    let goal = is_true(not_(Tm::Const(ANY_2COL_K3)));
    let proof = refl(Tm::Ind(BOOL), tru());
    assert!(
        check(&env, &Vec::new(), &proof, &goal).is_ok(),
        "refl Bool true : Id Bool (not any_2col_k3) true — the kernel proves K3 needs ≥3 colours"
    );
    assert!(
        conv(&env, &Vec::new(), &goal, &is_true(tru())).expect("conv on closed kernel terms"),
        "is_true (not any_2col_k3) ≡ is_true true"
    );
}

#[test]
fn thm_k3_three_colours_suffice_typechecks() {
    // COMPANION (upper bound): K3 IS 3-colourable — refl Bool true : Id Bool (proper_k3 c0 c1 c2)
    // true. Together with the theorem above: K3 needs 3, and 3 suffice ⇒ χ(K3) = 3 (for this graph).
    let env = demo_env().expect("demo env");
    let goal = is_true(proper_of3(col(0), col(1), col(2)));
    let proof = refl(Tm::Ind(BOOL), tru());
    assert!(
        check(&env, &Vec::new(), &proof, &goal).is_ok(),
        "refl Bool true : Id Bool (proper_k3 c0 c1 c2) true — 3 colours suffice for K3"
    );
}

// ════════════════════════ NEGATIVE CONTROL (no-false-green) ════════════════════════

#[test]
fn neg_k3_is_2colourable_claim_rejected_by_check() {
    // THE LOAD-BEARING NEGATIVE: the bogus claim "K3 IS 2-colourable", is_true any_2col_k3, MUST
    // be rejected — any_2col_k3 ≡ false, so refl Bool true : Id Bool false true fails under conv.
    // This proves the finite exhaustion is REAL (not vacuously satisfied).
    let env = demo_env().expect("demo env");
    let bogus_goal = is_true(Tm::Const(ANY_2COL_K3));
    let proof = refl(Tm::Ind(BOOL), tru());
    assert!(
        check(&env, &Vec::new(), &proof, &bogus_goal).is_err(),
        "refl Bool true MUST NOT prove is_true any_2col_k3 — K3 is NOT 2-colourable"
    );
    assert!(
        !conv(&env, &Vec::new(), &bogus_goal, &is_true(tru()))
            .expect("conv on closed kernel terms"),
        "is_true any_2col_k3 must NOT ≡ is_true true (false ≠ true)"
    );
}

#[test]
fn neg_false_is_uninhabited_by_diagonal_refl() {
    // Extra no-false-green: `refl Bool false` does NOT prove the good goal is_true(not any_2col_k3)
    // (its type is Id Bool false false, wrong index). Confirms `check` discriminates on the INDEX.
    let env = demo_env().expect("demo env");
    let goal = is_true(not_(Tm::Const(ANY_2COL_K3)));
    let proof_false = refl(Tm::Ind(BOOL), fls());
    assert!(
        check(&env, &Vec::new(), &proof_false, &goal).is_err(),
        "refl Bool false : Id Bool false false ≠ Id Bool (not any_2col_k3) true"
    );
}
