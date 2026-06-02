//! Four-colour-CLASS dependent-type proof on a CONCRETE planar graph, typechecked by the
//! dnx-proof kernel TODAY via the Tm-level recursor-ι path (driver.rs `try_iota`) + `Id`/`refl`
//! reflection (proofs.md §4-5:131-188; eq_prelude.rs). HONEST SCOPE: this is NOT the full
//! four-colour theorem (that is Gonthier's 60k-line Coq development) — it is a concrete,
//! demo-sized graph-colouring theorem that shows the kernel proves real dependent-type math
//! by COMPUTING a decidable colouring predicate and closing it by definitional equality.
//!
//! ── THE GRAPH (human-readable) ────────────────────────────────────────────────────────────
//!   C4 = the 4-cycle, a planar graph on vertices {0,1,2,3} with edge set
//!        E = { (0,1), (1,2), (2,3), (3,0) }   (a square).
//!   Four colours available: Color = { c0, c1, c2, c3 }.
//!
//! ── THE PREDICATE ─────────────────────────────────────────────────────────────────────────
//!   A colouring of C4 is a 4-tuple of colours (one per vertex). It is *proper* iff every edge
//!   joins two DIFFERENTLY-coloured vertices:
//!       proper(x0,x1,x2,x3) := neqc x0 x1 ∧ neqc x1 x2 ∧ neqc x2 x3 ∧ neqc x3 x0
//!   where  neqc a b := ¬ (eqc a b)  and  eqc : Color → Color → Bool  is decidable colour
//!   equality (a nested `Elim Color`). `proper` is a closed `Bool`-valued decision procedure —
//!   the exact analogue of fourcolor's reflected boolean predicates (`is_true`, proofs.md:644).
//!
//! ── THE THEOREM (human-readable) ──────────────────────────────────────────────────────────
//!   THEOREM (proper 2-colouring of C4 exists, with witness [c0,c1,c0,c1]):
//!       is_true (proper c0 c1 c0 c1)
//!   i.e. the colouring v0↦c0, v1↦c1, v2↦c0, v3↦c1 is a proper 4-colouring of C4.
//!   PROOF TERM:  refl Bool true  :  Id Bool (proper c0 c1 c0 c1) true.
//!   It typechecks because the kernel ι-reduces `proper c0 c1 c0 c1` to `Bool.true`, so the
//!   index `(proper c0 c1 c0 c1)` is definitionally equal to `true` and the diagonal `refl`
//!   inhabits the equality (T-Conv → conv → nf; mirror of fourcolor_demo.rs:258-270 reducibility
//!   closing, but the workload is a concrete graph-colouring decision rather than a tree fold).
//!
//! ── NEGATIVE (no-false-green) ─────────────────────────────────────────────────────────────
//!   The colouring [c0,c0,c0,c1] is NOT proper (vertices 0,1 are adjacent but share colour c0),
//!   so `proper c0 c0 c0 c1` ι-reduces to `Bool.false`. The kernel REJECTS the bogus proof
//!   `refl Bool true : Id Bool (proper c0 c0 c0 c1) true` — `false ≠ true` under conv — proving
//!   the theorem is not vacuously/trivially true.
//!
//! Inductives:  Color = c0|c1|c2|c3 (IndId 0; 4-ctor, sort 0, no fields — admits like Bool).
//!              Bool  = false|true   (IndId 1; 2-ctor, sort 0).
//!              Id    = Π(A:Sort0)(a:A). A → Sort0 := refl  (IndId 2; indexed, the `=` of is_true).
//! Consts:      not, eqc, neqc, proper  (Elim-folds → Bool; all ι-computable, no recursion).

use dnx_proof::conv::conv;
use dnx_proof::driver::nf_tm;
use dnx_proof::env::GlobalEnv;
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::check;
use dnx_proof::symbol::{ConstId, IndId};
use dnx_proof::tm::Tm;

// ── tiny builders (de Bruijn, as in eq_prelude.rs / fourcolor_demo.rs) ──
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
const PROPER: ConstId = ConstId(3);

// ── Color = c0 | c1 | c2 | c3  (the four colours; 4-ctor enum, sort 0, no fields) ──
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
/// Id : Π(A:Sort0)(a:A). A → Sort0 := refl  (indexed; the `=` of `is_true`, eq_prelude.rs:49-61).
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
/// Spine (driver.rs §5): motive · minor_false · minor_true · scrutinee. minor_false=true,
/// minor_true=false, so not false ⟶ true, not true ⟶ false.
fn not_body() -> Tm {
    let motive = lam(Tm::Ind(BOOL), Tm::Ind(BOOL));
    lam(
        Tm::Ind(BOOL),
        apps(Tm::Elim(BOOL), &[motive, tru(), fls(), Tm::Var(0)]),
    )
}

/// eqc := λa:Color.λb:Color. Elim Color (λ_.Bool) M0 M1 M2 M3 a
/// where Mk = the comparison branch when a = ck: it `Elim Color`s on b and returns `true`
/// exactly at b = ck, else `false`. Decidable colour equality — a nested `Elim Color`
/// (the 4-colour analogue of fourcolor_demo.rs `and`'s short-circuit `Elim Bool`).
fn eqc_body() -> Tm {
    // After `λa.λb.`: ctx [a,b] ⇒ a=Var1, b=Var0. The inner Elim scrutinises b (Var0),
    // building 4 minors that are constant Bool per the row index `row`.
    let is_k = |row: u32| -> Tm {
        // Elim Color (λ_.Bool) [k==0] [k==1] [k==2] [k==3] b   — returns true iff b's ctor == row.
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

/// neqc := λa:Color.λb:Color. not (eqc a b)   — "adjacent vertices must differ".
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

/// and := λa.λb. Elim Bool (λ_.Bool) false b a   (short-circuit AND; fourcolor_demo.rs:121-128).
/// Inlined here (no separate const) — used only inside `proper`.
fn and(a: Tm, b: Tm) -> Tm {
    let motive = lam(Tm::Ind(BOOL), Tm::Ind(BOOL));
    apps(Tm::Elim(BOOL), &[motive, fls(), b, a])
}

/// proper := λx0 x1 x2 x3 : Color. neqc x0 x1 ∧ neqc x1 x2 ∧ neqc x2 x3 ∧ neqc x3 x0.
/// The four conjuncts ARE the four edges of C4 = {(0,1),(1,2),(2,3),(3,0)}. After the four
/// binders: ctx [x0,x1,x2,x3] ⇒ x0=Var3, x1=Var2, x2=Var1, x3=Var0.
fn proper_body() -> Tm {
    let edge = |u: u32, v: u32| apps(Tm::Const(NEQC), &[Tm::Var(u), Tm::Var(v)]);
    // de Bruijn: x0=3,x1=2,x2=1,x3=0. Edges (0,1)(1,2)(2,3)(3,0).
    let e01 = edge(3, 2);
    let e12 = edge(2, 1);
    let e23 = edge(1, 0);
    let e30 = edge(0, 3);
    let body = and(e01, and(e12, and(e23, e30)));
    lam(
        Tm::Ind(COLOR),
        lam(
            Tm::Ind(COLOR),
            lam(Tm::Ind(COLOR), lam(Tm::Ind(COLOR), body)),
        ),
    )
}

/// is_true b := Id Bool b true   (mathcomp `is_true`; written inline as the goal type).
fn is_true(b: Tm) -> Tm {
    id_ty(Tm::Ind(BOOL), b, tru())
}

/// proper x0 x1 x2 x3  for concrete colours.
fn proper_of(x0: Tm, x1: Tm, x2: Tm, x3: Tm) -> Tm {
    apps(Tm::Const(PROPER), &[x0, x1, x2, x3])
}

/// Build the demo environment; surfaces any admission gap as the `Result` of `add_*`.
fn demo_env() -> Result<GlobalEnv, dnx_proof::env::AdmitError> {
    let mut e = GlobalEnv::default();
    e.add_inductive(color_ind())?;
    e.add_inductive(bool_ind())?;
    e.add_inductive(id_ind())?;
    let bool_to_bool = pi(Tm::Ind(BOOL), Tm::Ind(BOOL));
    let cc_to_bool = pi(Tm::Ind(COLOR), pi(Tm::Ind(COLOR), Tm::Ind(BOOL)));
    let cccc_to_bool = pi(
        Tm::Ind(COLOR),
        pi(
            Tm::Ind(COLOR),
            pi(Tm::Ind(COLOR), pi(Tm::Ind(COLOR), Tm::Ind(BOOL))),
        ),
    );
    e.add_const(NOT, bool_to_bool, not_body())?;
    e.add_const(EQC, cc_to_bool.clone(), eqc_body())?;
    e.add_const(NEQC, cc_to_bool, neqc_body())?;
    e.add_const(PROPER, cccc_to_bool, proper_body())?;
    Ok(e)
}

// ════════════════════════ ADMISSION (kernel-have check) ════════════════════════

#[test]
fn admits_color_bool_id_and_consts() {
    // Color/Bool/Id + not/eqc/neqc/proper must all pass the SOUNDNESS gates (positivity R3,
    // field-universe R11, δ-acyclicity R7). A gap here pinpoints the missing kernel feature.
    let env = demo_env().expect("Color/Bool/Id + not/eqc/neqc/proper admitted by the kernel");
    assert!(env.inds.contains_key(&COLOR), "4-colour inductive admitted");
    assert!(env.const_body(PROPER).is_some(), "proper predicate stored");
}

// ════════════════════════ ι CHAIN (the decision procedure computes) ════════════════════════

#[test]
fn eqc_decides_color_equality_by_iota() {
    // The decidable colour-equality `eqc` ι-reduces to the right Bool on concrete colours:
    // reflexive pairs ⟶ true, distinct pairs ⟶ false (all four diagonal + a few off-diagonal).
    let env = demo_env().expect("demo env");
    for k in 0..4 {
        assert_eq!(
            nf_tm(&env, &Vec::new(), &apps(Tm::Const(EQC), &[col(k), col(k)])),
            tru(),
            "eqc ck ck ι-reduces to true (reflexive)"
        );
    }
    assert_eq!(
        nf_tm(&env, &Vec::new(), &apps(Tm::Const(EQC), &[col(0), col(1)])),
        fls()
    );
    assert_eq!(
        nf_tm(&env, &Vec::new(), &apps(Tm::Const(EQC), &[col(2), col(3)])),
        fls()
    );
    assert_eq!(
        nf_tm(&env, &Vec::new(), &apps(Tm::Const(EQC), &[col(3), col(0)])),
        fls()
    );
}

#[test]
fn proper_computes_true_on_good_coloring() {
    // The good 2-colouring [c0,c1,c0,c1]: every C4 edge joins differing colours ⇒ proper ⟶ true.
    let env = demo_env().expect("demo env");
    assert_eq!(
        nf_tm(
            &env,
            &Vec::new(),
            &proper_of(col(0), col(1), col(0), col(1))
        ),
        tru(),
        "proper [c0,c1,c0,c1] ι-reduces to Bool.true (a proper 4-colouring of C4)"
    );
    // A genuine 4-colour use also works: [c0,c1,c2,c3] colours every vertex distinctly.
    assert_eq!(
        nf_tm(
            &env,
            &Vec::new(),
            &proper_of(col(0), col(1), col(2), col(3))
        ),
        tru(),
        "proper [c0,c1,c2,c3] ι-reduces to Bool.true (all four colours distinct)"
    );
}

#[test]
fn proper_computes_false_on_bad_coloring() {
    // The bad colouring [c0,c0,c0,c1]: vertices 0,1 adjacent but share c0 ⇒ proper ⟶ false.
    let env = demo_env().expect("demo env");
    assert_eq!(
        nf_tm(
            &env,
            &Vec::new(),
            &proper_of(col(0), col(0), col(0), col(1))
        ),
        fls(),
        "proper [c0,c0,c0,c1] ι-reduces to Bool.false (edge (0,1) monochromatic)"
    );
}

// ════════════════════════ THE THEOREM: a proper colouring exists, by reflection ═════════════

#[test]
fn thm_proper_coloring_of_c4_typechecks() {
    // THEOREM:  is_true (proper c0 c1 c0 c1)   — the 2-colouring [c0,c1,c0,c1] properly
    // 4-colours C4. PROOF:  refl Bool true : Id Bool (proper c0 c1 c0 c1) true. The kernel
    // ι-reduces `proper c0 c1 c0 c1 ≡ true`, so the diagonal `refl` inhabits the equality
    // (T-Conv → conv → nf; fourcolor_demo.rs:258-270 reducibility-closing on a graph workload).
    let env = demo_env().expect("demo env");
    let goal = is_true(proper_of(col(0), col(1), col(0), col(1)));
    let proof = refl(Tm::Ind(BOOL), tru());
    assert!(
        check(&env, &Vec::new(), &proof, &goal).is_ok(),
        "refl Bool true : Id Bool (proper c0 c1 c0 c1) true — the kernel proves C4 is properly 4-coloured"
    );
    // Cross-check the reflection equation directly: is_true(proper good) ≡ is_true true.
    assert!(
        conv(&env, &Vec::new(), &goal, &is_true(tru())).expect("conv on closed kernel terms"),
        "is_true (proper c0 c1 c0 c1) ≡ is_true true"
    );
}

#[test]
fn thm_four_color_witness_typechecks() {
    // Companion: the all-distinct 4-colouring [c0,c1,c2,c3] is also a proper colouring —
    // refl Bool true : Id Bool (proper c0 c1 c2 c3) true. Demonstrates the proof goes through
    // for a genuine use of all FOUR colours, not only the 2-colouring.
    let env = demo_env().expect("demo env");
    let goal = is_true(proper_of(col(0), col(1), col(2), col(3)));
    let proof = refl(Tm::Ind(BOOL), tru());
    assert!(
        check(&env, &Vec::new(), &proof, &goal).is_ok(),
        "refl Bool true : Id Bool (proper c0 c1 c2 c3) true"
    );
}

// ════════════════════════ NEGATIVE CONTROL (no-false-green) ════════════════════════

#[test]
fn neg_bad_coloring_proof_rejected_by_check() {
    // NEGATIVE: the bogus proof that the IMPROPER colouring [c0,c0,c0,c1] is proper MUST be
    // rejected. `proper c0 c0 c0 c1 ≡ false`, so `refl Bool true : Id Bool false true` fails
    // — `false ≠ true` under conv. Guards the theorem against being vacuously true.
    let env = demo_env().expect("demo env");
    let bad_goal = is_true(proper_of(col(0), col(0), col(0), col(1)));
    let proof = refl(Tm::Ind(BOOL), tru());
    assert!(
        check(&env, &Vec::new(), &proof, &bad_goal).is_err(),
        "refl Bool true MUST NOT prove is_true (proper c0 c0 c0 c1) — the colouring is improper"
    );
    // And the reflection equation does NOT hold: is_true(proper bad) ≢ is_true true.
    assert!(
        !conv(&env, &Vec::new(), &bad_goal, &is_true(tru())).expect("conv on closed kernel terms"),
        "is_true (proper c0 c0 c0 c1) must NOT ≡ is_true true (false ≠ true)"
    );
}

#[test]
fn neg_false_is_uninhabited_by_diagonal_refl() {
    // Extra no-false-green: even the `false`-side diagonal `refl Bool false` does NOT prove the
    // bad colouring is_true (its type is `Id Bool false false`, not `Id Bool (proper bad) true`).
    // Confirms `check` is discriminating on the INDEX, not merely accepting any refl.
    let env = demo_env().expect("demo env");
    let bad_goal = is_true(proper_of(col(0), col(0), col(0), col(1)));
    let proof_false = refl(Tm::Ind(BOOL), fls());
    assert!(
        check(&env, &Vec::new(), &proof_false, &bad_goal).is_err(),
        "refl Bool false : Id Bool false false ≠ Id Bool (proper bad) true"
    );
}
