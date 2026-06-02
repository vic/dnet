//! Four-colour-CLASS dependent-type proof on a CONCRETE PLANAR MAP — the 5-wheel W4 — typechecked
//! by the dnx-proof kernel TODAY via the Tm-level recursor-ι path (driver.rs `try_iota`) + `Id`/`refl`
//! reflection (proofs.md §4-5:131-188; eq_prelude.rs). HONEST SCOPE: this is NOT the four-colour
//! theorem (Gonthier's 60k-line Coq development) — it is a concrete, demo-sized graph-colouring
//! theorem about ONE named planar map, closed by COMPUTING a decidable colouring predicate and
//! inhabiting `Id Bool checker true` with `refl`. Mirrors fourcolor_coloring.rs (C4) exactly,
//! scaled to 5 vertices / 8 edges.
//!
//! ── THE GRAPH (human-readable) ────────────────────────────────────────────────────────────
//!   W4 = the 5-WHEEL: a central hub `h` joined to every vertex of a 4-cycle rim {0,1,2,3}.
//!        It is a genuinely 2-D planar MAP (a square region quartered by a central point).
//!        Vertices {h,0,1,2,3}.  Edge set (8 edges):
//!            rim   C4 = { (0,1), (1,2), (2,3), (3,0) }      (the outer square)
//!            spokes   = { (h,0), (h,1), (h,2), (h,3) }      (hub to each rim vertex)
//!   Four colours available: Color = { c0, c1, c2, c3 }.  W4 has chromatic number 3 (even rim ⇒
//!   3 colours suffice: hub one colour, rim alternates the other two) — so this is a "4 available,
//!   3 used" beat.
//!
//! ── THE PREDICATE ─────────────────────────────────────────────────────────────────────────
//!   A colouring of W4 is a 5-tuple (h,x0,x1,x2,x3). It is *proper* iff every edge joins two
//!   DIFFERENTLY-coloured vertices:
//!       proper_w4(h,x0,x1,x2,x3) := neqc x0 x1 ∧ neqc x1 x2 ∧ neqc x2 x3 ∧ neqc x3 x0   (rim)
//!                                 ∧ neqc h x0 ∧ neqc h x1 ∧ neqc h x2 ∧ neqc h x3        (spokes)
//!   where neqc a b := ¬(eqc a b) and eqc : Color→Color→Bool is decidable colour equality (a
//!   nested `Elim Color`). `proper_w4` is a closed `Bool`-valued decision procedure — the exact
//!   analogue of fourcolor's reflected boolean predicates (`is_true`, proofs.md:644).
//!
//! ── THE THEOREM (human-readable) ──────────────────────────────────────────────────────────
//!   THEOREM (proper 3-colouring of W4, witness hub=c2, rim=[c0,c1,c0,c1]):
//!       is_true (proper_w4 c2 c0 c1 c0 c1)
//!   i.e. h↦c2, v0↦c0, v1↦c1, v2↦c0, v3↦c1 is a proper colouring of W4 using only 3 colours.
//!   PROOF TERM:  refl Bool true : Id Bool (proper_w4 c2 c0 c1 c0 c1) true.
//!   It typechecks because the kernel ι-reduces `proper_w4 c2 c0 c1 c0 c1` to `Bool.true`, so the
//!   index is definitionally equal to `true` and the diagonal `refl` inhabits the equality
//!   (T-Conv → conv → nf; mirror of fourcolor_coloring.rs:313-331 on a richer 8-edge map).
//!
//! ── NEGATIVE (no-false-green) ─────────────────────────────────────────────────────────────
//!   The colouring hub=c0, rim=[c0,c1,c0,c1] is NOT proper (spoke (h,0) is monochromatic c0),
//!   so `proper_w4 c0 c0 c1 c0 c1` ι-reduces to `Bool.false`. The kernel REJECTS the bogus proof
//!   `refl Bool true : Id Bool (proper_w4 c0 c0 c1 c0 c1) true` — proving the theorem is not
//!   vacuously true. A rim defect (hub=c2, rim=[c0,c0,c0,c1]) is rejected too.
//!
//! Inductives:  Color = c0|c1|c2|c3 (IndId 0; 4-ctor, sort 0, no fields — admits like Bool).
//!              Bool  = false|true   (IndId 1; 2-ctor, sort 0).
//!              Id    = Π(A:Sort0)(a:A). A → Sort0 := refl  (IndId 2; indexed, the `=` of is_true).
//! Consts:      not, eqc, neqc, proper_w4  (Elim-folds → Bool; all ι-computable, no recursion).

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
const PROPER_W4: ConstId = ConstId(3);

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
fn not_body() -> Tm {
    let motive = lam(Tm::Ind(BOOL), Tm::Ind(BOOL));
    lam(
        Tm::Ind(BOOL),
        apps(Tm::Elim(BOOL), &[motive, tru(), fls(), Tm::Var(0)]),
    )
}

/// eqc := λa:Color.λb:Color. Elim Color (λ_.Bool) M0 M1 M2 M3 a  — decidable colour equality,
/// a nested `Elim Color` (true only on the diagonal). Identical to fourcolor_coloring.rs:154-178.
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

/// and := λa.λb. Elim Bool (λ_.Bool) false b a   (short-circuit AND; fourcolor_coloring.rs:194-199).
fn and(a: Tm, b: Tm) -> Tm {
    let motive = lam(Tm::Ind(BOOL), Tm::Ind(BOOL));
    apps(Tm::Elim(BOOL), &[motive, fls(), b, a])
}

/// proper_w4 := λh x0 x1 x2 x3 : Color. (8 edge-conjuncts of W4).
/// The 8 conjuncts ARE the 8 edges of W4: rim C4 {(0,1),(1,2),(2,3),(3,0)} + spokes {(h,i)}.
/// After the five binders: ctx [h,x0,x1,x2,x3] ⇒ h=Var4, x0=Var3, x1=Var2, x2=Var1, x3=Var0.
fn proper_w4_body() -> Tm {
    let edge = |u: u32, v: u32| apps(Tm::Const(NEQC), &[Tm::Var(u), Tm::Var(v)]);
    // de Bruijn: h=4, x0=3, x1=2, x2=1, x3=0.
    let e01 = edge(3, 2); // rim (0,1)
    let e12 = edge(2, 1); // rim (1,2)
    let e23 = edge(1, 0); // rim (2,3)
    let e30 = edge(0, 3); // rim (3,0)
    let sh0 = edge(4, 3); // spoke (h,0)
    let sh1 = edge(4, 2); // spoke (h,1)
    let sh2 = edge(4, 1); // spoke (h,2)
    let sh3 = edge(4, 0); // spoke (h,3)
                          // Right-associated AND chain over all 8 edges.
    let body = and(
        e01,
        and(e12, and(e23, and(e30, and(sh0, and(sh1, and(sh2, sh3)))))),
    );
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

/// is_true b := Id Bool b true   (mathcomp `is_true`; written inline as the goal type).
fn is_true(b: Tm) -> Tm {
    id_ty(Tm::Ind(BOOL), b, tru())
}

/// proper_w4 h x0 x1 x2 x3  for concrete colours.
fn proper_of(h: Tm, x0: Tm, x1: Tm, x2: Tm, x3: Tm) -> Tm {
    apps(Tm::Const(PROPER_W4), &[h, x0, x1, x2, x3])
}

/// Build the demo environment; surfaces any admission gap as the `Result` of `add_*`.
fn demo_env() -> Result<GlobalEnv, dnx_proof::env::AdmitError> {
    let mut e = GlobalEnv::default();
    e.add_inductive(color_ind())?;
    e.add_inductive(bool_ind())?;
    e.add_inductive(id_ind())?;
    let bool_to_bool = pi(Tm::Ind(BOOL), Tm::Ind(BOOL));
    let cc_to_bool = pi(Tm::Ind(COLOR), pi(Tm::Ind(COLOR), Tm::Ind(BOOL)));
    // Color → Color → Color → Color → Color → Bool   (5 args: h,x0,x1,x2,x3).
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
    e.add_const(PROPER_W4, c5_to_bool, proper_w4_body())?;
    Ok(e)
}

// ════════════════════════ ADMISSION (kernel-have check) ════════════════════════

#[test]
fn admits_color_bool_id_and_consts() {
    // Color/Bool/Id + not/eqc/neqc/proper_w4 must all pass the SOUNDNESS gates (positivity R3,
    // field-universe R11, δ-acyclicity R7). A gap here pinpoints the missing kernel feature.
    let env = demo_env().expect("Color/Bool/Id + not/eqc/neqc/proper_w4 admitted by the kernel");
    assert!(env.inds.contains_key(&COLOR), "4-colour inductive admitted");
    assert!(
        env.const_body(PROPER_W4).is_some(),
        "proper_w4 predicate stored"
    );
}

// ════════════════════════ ι CHAIN (the decision procedure computes) ════════════════════════

#[test]
fn proper_w4_computes_true_on_good_3_coloring() {
    // The good 3-colouring hub=c2, rim=[c0,c1,c0,c1]: every rim edge joins c0 vs c1, every spoke
    // joins c2 vs {c0,c1} ⇒ all 8 edges bichromatic ⇒ proper_w4 ⟶ true. Only 3 colours used.
    let env = demo_env().expect("demo env");
    assert_eq!(
        nf_tm(
            &env,
            &Vec::new(),
            &proper_of(col(2), col(0), col(1), col(0), col(1))
        ),
        tru(),
        "proper_w4 c2 c0 c1 c0 c1 ι-reduces to Bool.true (a proper 3-colouring of W4)"
    );
}

#[test]
fn proper_w4_computes_true_on_four_color_witness() {
    // A genuine all-FOUR-colour use: hub=c3, rim=[c0,c1,c0,c2]. Rim edges (0,1)=c0,c1 (1,2)=c1,c0
    // (2,3)=c0,c2 (3,0)=c2,c0 all differ; spokes c3 vs each of {c0,c1,c0,c2} all differ ⇒ all 8
    // edges bichromatic ⇒ proper, and the colouring uses all four colours c0,c1,c2,c3.
    let env = demo_env().expect("demo env");
    assert_eq!(
        nf_tm(
            &env,
            &Vec::new(),
            &proper_of(col(3), col(0), col(1), col(0), col(2))
        ),
        tru(),
        "proper_w4 c3 c0 c1 c0 c2 ι-reduces to Bool.true (all four colours used, proper)"
    );
}

#[test]
fn proper_w4_computes_false_on_spoke_defect() {
    // Bad: hub=c0 equals rim vertex 0=c0 ⇒ spoke (h,0) is monochromatic ⇒ proper_w4 ⟶ false.
    let env = demo_env().expect("demo env");
    assert_eq!(
        nf_tm(
            &env,
            &Vec::new(),
            &proper_of(col(0), col(0), col(1), col(0), col(1))
        ),
        fls(),
        "proper_w4 c0 c0 c1 c0 c1 ι-reduces to Bool.false (spoke (h,0) monochromatic)"
    );
}

#[test]
fn proper_w4_computes_false_on_rim_defect() {
    // Bad: rim vertices 1,2 both c0 ⇒ rim edge (1,2) monochromatic ⇒ proper_w4 ⟶ false.
    let env = demo_env().expect("demo env");
    assert_eq!(
        nf_tm(
            &env,
            &Vec::new(),
            &proper_of(col(2), col(0), col(0), col(0), col(1))
        ),
        fls(),
        "proper_w4 c2 c0 c0 c0 c1 ι-reduces to Bool.false (rim edge (1,2) monochromatic)"
    );
}

// ════════════════════════ THE THEOREM: a proper 3-colouring of W4, by reflection ════════════

#[test]
fn thm_proper_3coloring_of_w4_typechecks() {
    // THEOREM:  is_true (proper_w4 c2 c0 c1 c0 c1)  — hub=c2, rim=[c0,c1,c0,c1] is a proper
    // colouring of the 5-wheel map W4 using only 3 colours. PROOF: refl Bool true :
    // Id Bool (proper_w4 c2 c0 c1 c0 c1) true. The kernel ι-reduces the checker to `true`, so the
    // diagonal `refl` inhabits the equality (T-Conv → conv → nf; fourcolor_coloring.rs:313-331).
    let env = demo_env().expect("demo env");
    let goal = is_true(proper_of(col(2), col(0), col(1), col(0), col(1)));
    let proof = refl(Tm::Ind(BOOL), tru());
    assert!(
        check(&env, &Vec::new(), &proof, &goal).is_ok(),
        "refl Bool true : Id Bool (proper_w4 c2 c0 c1 c0 c1) true — the kernel proves W4 is properly 3-coloured"
    );
    // Cross-check the reflection equation directly: is_true(proper good) ≡ is_true true.
    assert!(
        conv(&env, &Vec::new(), &goal, &is_true(tru())).expect("conv on closed kernel terms"),
        "is_true (proper_w4 c2 c0 c1 c0 c1) ≡ is_true true"
    );
}

#[test]
fn thm_four_color_witness_of_w4_typechecks() {
    // Companion: the all-distinct use hub=c3, rim=[c0,c1,c0,c2] is also a proper colouring —
    // refl Bool true : Id Bool (proper_w4 c3 c0 c1 c0 c2) true. Shows the proof goes through for
    // a genuine use of all FOUR colours on the map, not only the 3-colouring.
    let env = demo_env().expect("demo env");
    let goal = is_true(proper_of(col(3), col(0), col(1), col(0), col(2)));
    let proof = refl(Tm::Ind(BOOL), tru());
    assert!(
        check(&env, &Vec::new(), &proof, &goal).is_ok(),
        "refl Bool true : Id Bool (proper_w4 c3 c0 c1 c0 c2) true"
    );
}

// ════════════════════════ NEGATIVE CONTROL (no-false-green) ════════════════════════

#[test]
fn neg_spoke_defect_proof_rejected_by_check() {
    // NEGATIVE: the bogus proof that the IMPROPER colouring hub=c0, rim=[c0,c1,c0,c1] is proper
    // MUST be rejected. `proper_w4 c0 c0 c1 c0 c1 ≡ false`, so `refl Bool true : Id Bool false
    // true` fails — `false ≠ true` under conv. Guards the theorem against being vacuously true.
    let env = demo_env().expect("demo env");
    let bad_goal = is_true(proper_of(col(0), col(0), col(1), col(0), col(1)));
    let proof = refl(Tm::Ind(BOOL), tru());
    assert!(
        check(&env, &Vec::new(), &proof, &bad_goal).is_err(),
        "refl Bool true MUST NOT prove is_true (proper_w4 c0 c0 c1 c0 c1) — spoke (h,0) is monochromatic"
    );
    assert!(
        !conv(&env, &Vec::new(), &bad_goal, &is_true(tru())).expect("conv on closed kernel terms"),
        "is_true (proper_w4 c0 c0 c1 c0 c1) must NOT ≡ is_true true (false ≠ true)"
    );
}

#[test]
fn neg_rim_defect_proof_rejected_by_check() {
    // NEGATIVE: a rim defect (hub=c2, rim=[c0,c0,c0,c1]) is also rejected — proper_w4 ≡ false.
    let env = demo_env().expect("demo env");
    let bad_goal = is_true(proper_of(col(2), col(0), col(0), col(0), col(1)));
    let proof = refl(Tm::Ind(BOOL), tru());
    assert!(
        check(&env, &Vec::new(), &proof, &bad_goal).is_err(),
        "refl Bool true MUST NOT prove is_true (proper_w4 c2 c0 c0 c0 c1) — rim edge (1,2) monochromatic"
    );
}

#[test]
fn neg_false_is_uninhabited_by_diagonal_refl() {
    // Extra no-false-green: even the `false`-side diagonal `refl Bool false` does NOT prove the
    // bad colouring is_true (its type is `Id Bool false false`, not `Id Bool (proper bad) true`).
    // Confirms `check` is discriminating on the INDEX, not merely accepting any refl.
    let env = demo_env().expect("demo env");
    let bad_goal = is_true(proper_of(col(0), col(0), col(1), col(0), col(1)));
    let proof_false = refl(Tm::Ind(BOOL), fls());
    assert!(
        check(&env, &Vec::new(), &proof_false, &bad_goal).is_err(),
        "refl Bool false : Id Bool false false ≠ Id Bool (proper_w4 bad) true"
    );
}
