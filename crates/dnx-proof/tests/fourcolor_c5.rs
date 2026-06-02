//! Four-colour-CLASS dependent-type proof about the ODD CYCLE C5 — a proper 3-colouring AND a
//! machine-checked "two colours are not enough" via finite exhaustion — typechecked by the dnx-proof
//! kernel TODAY via the Tm-level recursor-ι path (driver.rs `try_iota`) + `Id`/`refl` reflection
//! (proofs.md §4-5; eq_prelude.rs). HONEST SCOPE: NOT the four-colour theorem. Concrete, demo-sized
//! facts about ONE named graph, each closed by COMPUTING a decidable checker to `true` and inhabiting
//! `Id Bool checker true` with `refl`. Mirrors fourcolor_coloring.rs in structure, adding the dual
//! `or` combinator and a Rust-built 32-way OR-fold.
//!
//! ── THE GRAPH (human-readable) ────────────────────────────────────────────────────────────
//!   C5 = the 5-cycle on vertices {0,1,2,3,4}, edge set { (0,1),(1,2),(2,3),(3,4),(4,0) }. It is
//!        the canonical ODD cycle, chromatic number 3 (an odd cycle cannot be 2-coloured: the
//!        alternation c0,c1,c0,c1,… wraps around and clashes at the closing edge).
//!   Four colours available: Color = { c0, c1, c2, c3 }; the lower-bound argument uses only {c0,c1}.
//!
//! ── THE PREDICATES ────────────────────────────────────────────────────────────────────────
//!   proper_c5(x0,x1,x2,x3,x4) := neqc x0 x1 ∧ neqc x1 x2 ∧ neqc x2 x3 ∧ neqc x3 x4 ∧ neqc x4 x0.
//!   no2_c5 : Bool := OR over all 32 colourings with each vertex ∈ {c0,c1} of proper_c5(…).
//!                    "Does ANY 2-colouring (over the two fixed colours c0,c1) of C5 work?"
//!   Both are closed `Bool`-valued decision procedures (`Elim`-folds, no recursion ⇒ ι-computable).
//!
//! ── THE THEOREMS (human-readable) ─────────────────────────────────────────────────────────
//!   PART 1 (3-colouring exists):  is_true (proper_c5 c0 c1 c0 c1 c2)
//!     — the forced "extra" colour c2 at the odd closing vertex. PROOF: refl Bool true.
//!   PART 2(a) (named 2-colour attempt fails):  the canonical alternation [c0,c1,c0,c1,c0] is NOT
//!     proper (edge (4,0) is c0 vs c0); refl Bool true : is_true(proper_c5 c0 c1 c0 c1 c0) is
//!     REJECTED by the kernel.
//!   PART 2(b) (no 2-colouring at all):  is_true (not no2_c5)  ≡ "no colouring of C5 over {c0,c1} is
//!     proper". no2_c5 ι-reduces (all 32 disjuncts ⟶ false) to false, `not` to true. PROOF: refl.
//!
//! ── NEGATIVE (no-false-green) ─────────────────────────────────────────────────────────────
//!   PART 1: a defective 3-colouring [c0,c0,c0,c1,c2] ⟶ false; refl Bool true rejected.
//!   PART 2(b) load-bearing: the bogus "C5 IS 2-colourable" claim is_true no2_c5 is REJECTED
//!   (no2_c5 ≡ false). `refl Bool false` against a good goal rejected (wrong index).
//!
//! ── SCOPE CAPTION ─────────────────────────────────────────────────────────────────────────
//!   We verify (i) a concrete 3-colouring of C5 and (ii) that no colouring of C5 using only two
//!   fixed colours is proper (finite exhaustion of all 32 assignments over {c0,c1}, relying on
//!   2-colourability being invariant under colour renaming). We do NOT claim χ(C5) ≥ 3 as a
//!   universal theorem over all 2-colourings up to symmetry — only the explicit finite checks above.
//!
//! Inductives:  Color = c0|c1|c2|c3 (IndId 0); Bool = false|true (IndId 1);
//!              Id = Π(A:Sort0)(a:A). A → Sort0 := refl (IndId 2; the `=` of is_true).
//! Consts:      not, eqc, neqc, proper_c5, no2_c5 (Elim-folds → Bool; ι-computable, no recursion).

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
const PROPER_C5: ConstId = ConstId(3);
const NO2_C5: ConstId = ConstId(4);

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

/// not := λb:Bool. Elim Bool (λ_:Bool.Bool) true false b.
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
fn or(a: Tm, b: Tm) -> Tm {
    let motive = lam(Tm::Ind(BOOL), Tm::Ind(BOOL));
    apps(Tm::Elim(BOOL), &[motive, b, tru(), a])
}

/// proper_c5 := λx0 x1 x2 x3 x4 : Color. neqc x0 x1 ∧ neqc x1 x2 ∧ neqc x2 x3 ∧ neqc x3 x4 ∧ neqc x4 x0.
/// The five conjuncts ARE the five edges of C5. After the five binders:
/// ctx [x0,x1,x2,x3,x4] ⇒ x0=Var4, x1=Var3, x2=Var2, x3=Var1, x4=Var0.
fn proper_c5_body() -> Tm {
    let edge = |u: u32, v: u32| apps(Tm::Const(NEQC), &[Tm::Var(u), Tm::Var(v)]);
    let e01 = edge(4, 3); // (0,1)
    let e12 = edge(3, 2); // (1,2)
    let e23 = edge(2, 1); // (2,3)
    let e34 = edge(1, 0); // (3,4)
    let e40 = edge(0, 4); // (4,0)
    let body = and(e01, and(e12, and(e23, and(e34, e40))));
    lam(
        Tm::Ind(COLOR),
        lam(
            Tm::Ind(COLOR),
            lam(
                Tm::Ind(COLOR),
                lam(Tm::Ind(COLOR), lam(Tm::Ind(COLOR), body)),
            ),
        ),
    )
}

/// no2_c5 : Bool  (0-ary const naming the finite exhaustion).
/// = OR over the 32 colourings with each of the 5 vertices ∈ {c0,c1} of `proper_c5 …`.
/// Built programmatically (plan §1 DEMO B part 2(b) builder loop).
fn no2_c5_body() -> Tm {
    let cols = [col(0), col(1)];
    let mut acc = fls();
    for v in 0..32u32 {
        let pick = |bit: u32| cols[((v >> bit) & 1) as usize].clone();
        let disj = apps(
            Tm::Const(PROPER_C5),
            &[pick(0), pick(1), pick(2), pick(3), pick(4)],
        );
        acc = or(acc, disj);
    }
    acc
}

/// is_true b := Id Bool b true.
fn is_true(b: Tm) -> Tm {
    id_ty(Tm::Ind(BOOL), b, tru())
}

/// proper_c5 x0 x1 x2 x3 x4  for concrete colours.
fn proper_of5(x0: Tm, x1: Tm, x2: Tm, x3: Tm, x4: Tm) -> Tm {
    apps(Tm::Const(PROPER_C5), &[x0, x1, x2, x3, x4])
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
    let c5_to_bool = pi(
        Tm::Ind(COLOR),
        pi(
            Tm::Ind(COLOR),
            pi(
                Tm::Ind(COLOR),
                pi(Tm::Ind(COLOR), pi(Tm::Ind(COLOR), Tm::Ind(BOOL))),
            ),
        ),
    );
    e.add_const(NOT, bool_to_bool, not_body())?;
    e.add_const(EQC, cc_to_bool.clone(), eqc_body())?;
    e.add_const(NEQC, cc_to_bool, neqc_body())?;
    e.add_const(PROPER_C5, c5_to_bool, proper_c5_body())?;
    // no2_c5 references PROPER_C5, so admit it AFTER (δ-acyclicity R7).
    e.add_const(NO2_C5, Tm::Ind(BOOL), no2_c5_body())?;
    Ok(e)
}

// ════════════════════════ ADMISSION (kernel-have check) ════════════════════════

#[test]
fn admits_color_bool_id_and_consts() {
    // Color/Bool/Id + not/eqc/neqc/proper_c5/no2_c5 must all pass the SOUNDNESS gates
    // (positivity R3, field-universe R11, δ-acyclicity R7). no2_c5 references proper_c5.
    let env = demo_env().expect("Color/Bool/Id + not/eqc/neqc/proper_c5/no2_c5 admitted");
    assert!(env.inds.contains_key(&COLOR), "4-colour inductive admitted");
    assert!(
        env.const_body(NO2_C5).is_some(),
        "no2_c5 finite-exhaustion const stored"
    );
}

// ════════════════════════ ι CHAIN (the decision procedures compute) ════════════════════════

#[test]
fn proper_c5_computes_true_on_good_3_coloring() {
    // PART 1 ι-chain: [c0,c1,c0,c1,c2] — alternate c0/c1 around, force c2 at the odd close ⇒ proper.
    let env = demo_env().expect("demo env");
    assert_eq!(
        nf_tm(
            &env,
            &Vec::new(),
            &proper_of5(col(0), col(1), col(0), col(1), col(2))
        ),
        tru(),
        "proper_c5 c0 c1 c0 c1 c2 ι-reduces to Bool.true (a proper 3-colouring of C5)"
    );
}

#[test]
fn proper_c5_computes_false_on_canonical_2_coloring() {
    // PART 2(a) ι-chain: the canonical alternation [c0,c1,c0,c1,c0] clashes at the closing edge
    // (4,0) = c0 vs c0 ⇒ proper_c5 ⟶ false. (The only alternating 2-colouring of an odd cycle.)
    let env = demo_env().expect("demo env");
    assert_eq!(
        nf_tm(
            &env,
            &Vec::new(),
            &proper_of5(col(0), col(1), col(0), col(1), col(0))
        ),
        fls(),
        "proper_c5 c0 c1 c0 c1 c0 ι-reduces to Bool.false (edge (4,0) monochromatic)"
    );
}

#[test]
fn proper_c5_computes_false_on_defective_3_coloring() {
    // PART 1 negative ι-chain: [c0,c0,c0,c1,c2] — edge (0,1) = c0 vs c0 ⇒ proper_c5 ⟶ false.
    let env = demo_env().expect("demo env");
    assert_eq!(
        nf_tm(
            &env,
            &Vec::new(),
            &proper_of5(col(0), col(0), col(0), col(1), col(2))
        ),
        fls(),
        "proper_c5 c0 c0 c0 c1 c2 ι-reduces to Bool.false (edge (0,1) monochromatic)"
    );
}

#[test]
fn no2_c5_computes_false_by_exhaustion() {
    // PART 2(b) HEART: the OR over ALL 32 two-colourings of C5 ι-reduces to false — no assignment
    // of {c0,c1} to the 5 vertices of the odd cycle avoids a monochromatic edge.
    let env = demo_env().expect("demo env");
    assert_eq!(
        nf_tm(&env, &Vec::new(), &Tm::Const(NO2_C5)),
        fls(),
        "no2_c5 ι-reduces to Bool.false (no 2-colouring of C5 over c0,c1 is proper)"
    );
}

#[test]
fn not_no2_c5_computes_true() {
    // Therefore `not no2_c5` ι-reduces to true — "C5 has no proper 2-colouring".
    let env = demo_env().expect("demo env");
    assert_eq!(
        nf_tm(&env, &Vec::new(), &not_(Tm::Const(NO2_C5))),
        tru(),
        "not no2_c5 ι-reduces to Bool.true (C5 is not 2-colourable over c0,c1)"
    );
}

// ════════════════════════ THE THEOREMS ════════════════════════

#[test]
fn thm_c5_proper_3coloring_typechecks() {
    // PART 1 THEOREM:  is_true (proper_c5 c0 c1 c0 c1 c2). PROOF: refl Bool true. The kernel
    // ι-reduces the checker to true; the diagonal refl inhabits the equality (T-Conv → conv → nf).
    let env = demo_env().expect("demo env");
    let goal = is_true(proper_of5(col(0), col(1), col(0), col(1), col(2)));
    let proof = refl(Tm::Ind(BOOL), tru());
    assert!(
        check(&env, &Vec::new(), &proof, &goal).is_ok(),
        "refl Bool true : Id Bool (proper_c5 c0 c1 c0 c1 c2) true — C5 is properly 3-coloured"
    );
    assert!(
        conv(&env, &Vec::new(), &goal, &is_true(tru())).expect("conv on closed kernel terms"),
        "is_true (proper_c5 c0 c1 c0 c1 c2) ≡ is_true true"
    );
}

#[test]
fn thm_c5_no_2coloring_typechecks() {
    // PART 2(b) THEOREM:  is_true (not no2_c5)  — no 2-colouring of C5 over {c0,c1} is proper.
    // PROOF: refl Bool true : Id Bool (not no2_c5) true. The kernel ι-reduces the 32-way OR to
    // false then `not` to true. A machine-checked "two colours don't suffice" via finite exhaustion.
    let env = demo_env().expect("demo env");
    let goal = is_true(not_(Tm::Const(NO2_C5)));
    let proof = refl(Tm::Ind(BOOL), tru());
    assert!(
        check(&env, &Vec::new(), &proof, &goal).is_ok(),
        "refl Bool true : Id Bool (not no2_c5) true — C5 has no proper 2-colouring"
    );
    assert!(
        conv(&env, &Vec::new(), &goal, &is_true(tru())).expect("conv on closed kernel terms"),
        "is_true (not no2_c5) ≡ is_true true"
    );
}

// ════════════════════════ NEGATIVE CONTROL (no-false-green) ════════════════════════

#[test]
fn neg_canonical_2coloring_proof_rejected_by_check() {
    // PART 2(a) NEGATIVE: refl Bool true : is_true (proper_c5 c0 c1 c0 c1 c0) MUST be rejected —
    // the canonical 2-colouring of C5 is not proper (proper_c5 … ≡ false). "The kernel rejects the
    // bogus proof that the alternating 2-colouring of C5 works."
    let env = demo_env().expect("demo env");
    let bad_goal = is_true(proper_of5(col(0), col(1), col(0), col(1), col(0)));
    let proof = refl(Tm::Ind(BOOL), tru());
    assert!(
        check(&env, &Vec::new(), &proof, &bad_goal).is_err(),
        "refl Bool true MUST NOT prove is_true (proper_c5 c0 c1 c0 c1 c0) — edge (4,0) clashes"
    );
    assert!(
        !conv(&env, &Vec::new(), &bad_goal, &is_true(tru())).expect("conv on closed kernel terms"),
        "is_true (proper_c5 c0 c1 c0 c1 c0) must NOT ≡ is_true true (false ≠ true)"
    );
}

#[test]
fn neg_c5_is_2colourable_claim_rejected_by_check() {
    // PART 2(b) LOAD-BEARING NEGATIVE: the bogus claim "C5 IS 2-colourable", is_true no2_c5, MUST
    // be rejected — no2_c5 ≡ false. Proves the 32-way finite exhaustion is REAL, not vacuous.
    let env = demo_env().expect("demo env");
    let bogus_goal = is_true(Tm::Const(NO2_C5));
    let proof = refl(Tm::Ind(BOOL), tru());
    assert!(
        check(&env, &Vec::new(), &proof, &bogus_goal).is_err(),
        "refl Bool true MUST NOT prove is_true no2_c5 — C5 is NOT 2-colourable"
    );
}

#[test]
fn neg_defective_3coloring_proof_rejected_by_check() {
    // PART 1 NEGATIVE: the defective 3-colouring [c0,c0,c0,c1,c2] is rejected — proper_c5 ≡ false.
    let env = demo_env().expect("demo env");
    let bad_goal = is_true(proper_of5(col(0), col(0), col(0), col(1), col(2)));
    let proof = refl(Tm::Ind(BOOL), tru());
    assert!(
        check(&env, &Vec::new(), &proof, &bad_goal).is_err(),
        "refl Bool true MUST NOT prove is_true (proper_c5 c0 c0 c0 c1 c2) — edge (0,1) clashes"
    );
}

#[test]
fn neg_false_is_uninhabited_by_diagonal_refl() {
    // Extra no-false-green: `refl Bool false` does NOT prove is_true(not no2_c5) (type Id Bool
    // false false, wrong index). Confirms `check` discriminates on the INDEX, not any refl.
    let env = demo_env().expect("demo env");
    let goal = is_true(not_(Tm::Const(NO2_C5)));
    let proof_false = refl(Tm::Ind(BOOL), fls());
    assert!(
        check(&env, &Vec::new(), &proof_false, &goal).is_err(),
        "refl Bool false : Id Bool false false ≠ Id Bool (not no2_c5) true"
    );
}
