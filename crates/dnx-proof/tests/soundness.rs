//! Soundness + completeness gate (proofs.md Part III). MUST-ACCEPT (A*) pass,
//! MUST-REJECT (R*) error. Deferred items are `#[ignore]` with the reason.
//!
//! v1 scope notes:
//! - η (A4): implemented (nf-time η-contraction); A4 green.
//! - Elim type synthesis (A5/A6): recursor type + ι cover the full P/X telescope incl. indexed
//!   families (`Vec A n`); A5 large-elim + A6 indexed recursor green (proofs.md:163-188).
//! - R10 N/A — no Prop in v1 (settled C2).
//! - D2 differential fuzz — OPEN-15 (needs an independent reference normalizer).

use dnx_proof::conv::conv;
use dnx_proof::driver::{nf_tm, whnf_tm};
use dnx_proof::env::{AdmitError, GlobalEnv};
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::{check, infer, TypeError};
use dnx_proof::positivity::strictly_positive;
use dnx_proof::symbol::{ConstId, IndId};
use dnx_proof::tm::Tm;

// ── helpers ──
fn lam(dom: Tm, b: Tm) -> Tm {
    Tm::Lam(Box::new(dom), Box::new(b))
}
fn app(f: Tm, x: Tm) -> Tm {
    Tm::App(Box::new(f), Box::new(x))
}
fn nat() -> Inductive {
    Inductive {
        id: IndId(0),
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
                args: vec![Tm::Ind(IndId(0))],
                ret_indices: vec![],
            },
        ],
    }
}
fn nat_env() -> GlobalEnv {
    let mut e = GlobalEnv::default();
    e.add_inductive(nat()).unwrap();
    e
}
fn zero() -> Tm {
    Tm::Ctor(IndId(0), 0)
}
fn succ(n: Tm) -> Tm {
    app(Tm::Ctor(IndId(0), 1), n)
}

// ── φ_K → Ω_K → φ_K⁻¹ net pipeline (the trusted roundtrip of proofs.md:283-285), used by
//    A1's erasure-roundtrip clause and A8's α-rename roundtrip. Readback (`psi_native`) emits
//    gensym binder names, so equality is decided by α (de Bruijn binding depth), not by name.
use dnx_ast::{Ast, Name, NoFun, NoVal};
use dnx_proof::erase::phi_k;
use dnx_read::{psi_native, ReadbackResult};
use dnx_sched::{Scheduler, SequentialScheduler};

type A = Ast<NoVal, NoFun>;

/// Drive a Tm through φ_K (erase+build net) → Ω_K (normalize) → φ_K⁻¹ (readback).
fn net_roundtrip(t: &Tm) -> ReadbackResult<NoVal, NoFun> {
    let (net, _root) = phi_k(t).expect("φ_K builds a net");
    let (canon, _) = SequentialScheduler::normalize(net).expect("Ω_K normalizes");
    psi_native::<_, NoVal, NoFun>(&canon)
}

/// `Era(d, body)` is a weakening marker (erase.rs:40: dropped binder `d`, value `body`);
/// it carries no value, so α-comparison sees through it to `body`.
fn peel_era(a: &A) -> &A {
    match a {
        Ast::Era(_d, body) => peel_era(body),
        other => other,
    }
}

/// α-equality on readback ASTs: bound vars by binding depth, free vars by name; `Era`
/// weakening nodes are transparent.
fn alpha_eq(a: &A, b: &A, sa: &mut Vec<Name>, sb: &mut Vec<Name>) -> bool {
    match (peel_era(a), peel_era(b)) {
        (Ast::Name(x), Ast::Name(y)) => match (
            sa.iter().rposition(|n| n == x),
            sb.iter().rposition(|n| n == y),
        ) {
            (Some(i), Some(j)) => i == j, // both bound: same de Bruijn level
            (None, None) => x == y,       // both free
            _ => false,
        },
        (Ast::Abs(x, bx), Ast::Abs(y, by)) => {
            sa.push(x.clone());
            sb.push(y.clone());
            let r = alpha_eq(bx, by, sa, sb);
            sa.pop();
            sb.pop();
            r
        }
        (Ast::App(f1, x1), Ast::App(f2, x2)) => {
            alpha_eq(f1, f2, sa, sb) && alpha_eq(x1, x2, sa, sb)
        }
        _ => false,
    }
}

/// Two Tms roundtrip through the net to α-equal readbacks (both must be closed Lambdas).
fn net_roundtrip_alpha_eq(t: &Tm, u: &Tm) -> bool {
    match (net_roundtrip(t), net_roundtrip(u)) {
        (ReadbackResult::Lambda(a), ReadbackResult::Lambda(b)) => {
            alpha_eq(&a, &b, &mut Vec::new(), &mut Vec::new())
        }
        _ => false,
    }
}

// ═══ MUST-ACCEPT ═══

#[test]
fn a1_polymorphic_identity_typechecks() {
    // proofs.md:297 "A1 | `id : Π(A:Type₀)(x:A), A` applied + `refl` typechecks |
    //                 φ_K erasure + readback roundtrip".
    let env = nat_env(); // Nat available as a closed type to instantiate the polymorphic id
    let id = lam(Tm::Sort(0), lam(Tm::Var(0), Tm::Var(0)));
    let ty = Tm::Pi(
        Box::new(Tm::Sort(0)),
        Box::new(Tm::Pi(Box::new(Tm::Var(0)), Box::new(Tm::Var(1)))),
    );
    // (1) id has the polymorphic Π type.
    assert!(
        check(&env, &Vec::new(), &id, &ty).is_ok(),
        "id : Π(A)(x:A).A"
    );

    // (2) APPLIED + refl-style: `id Nat zero : Nat`. The dependent result type instantiates to
    //     the instantiating type (proofs.md:297 "applied"). Instantiated at the *closed* type
    //     `Nat` (an `Ind`) so the T-Conv check rides the typed layer (conv.rs:49 needs_typed_conv).
    let nat = Tm::Ind(IndId(0));
    let id_nat_zero = app(app(id.clone(), nat.clone()), zero()); // id Nat zero
    assert_eq!(
        infer(&env, &Vec::new(), &id_nat_zero).expect("id Nat zero infers"),
        nat,
        "id Nat zero : Nat (dependent result instantiates to Nat)"
    );
    // …and it actually checks at the instantiated type (the `refl`-style use site).
    assert!(
        check(&env, &Vec::new(), &id_nat_zero, &nat).is_ok(),
        "id Nat zero : Nat checks"
    );

    // (3) φ_K erasure + readback roundtrip (proofs.md:297, TCB φ_K→Ω_K→φ_K⁻¹, proofs.md:283-285):
    //     the applied identity (λx.x)(λw.w) erases its λ-domain type annotations, β-reduces in the
    //     net, and reads back α-equal to the type-free identity λw.w. Driven on the net directly
    //     because `conv` routes Sort-annotated λs to the typed layer (conv.rs:25,47). NOTE: a
    //     *type* argument (`Sort`) cannot ride φ_K — it erases to a free `§ty` token the net
    //     cannot drain (ReadbackIncomplete); the runtime/erased identity is the value-level use.
    let val_id = lam(Tm::Sort(0), Tm::Var(0)); // λw. w  (domain erased by φ_K)
    let applied_id = app(val_id.clone(), val_id.clone()); // (λx.x)(λw.w)
    assert!(
        net_roundtrip_alpha_eq(&applied_id, &val_id),
        "(λx.x)(λw.w) →φ_K→Ω_K→φ_K⁻¹ reads back α≡ λw.w"
    );
}

#[test]
fn a2_nat_rec_iota_reduces() {
    // Elim Nat motive zero (λpred.λih. succ ih) (succ (succ zero)) → succ (succ zero)
    let env = nat_env();
    let ms = lam(Tm::Ind(IndId(0)), lam(Tm::Ind(IndId(0)), succ(Tm::Var(0))));
    let two = succ(succ(zero()));
    let rec = app(
        app(app(app(Tm::Elim(IndId(0)), Tm::Sort(0)), zero()), ms),
        two.clone(),
    );
    assert_eq!(nf_tm(&env, &Vec::new(), &rec), two);
}

#[test]
fn a3_add_delta_iota_to_literal() {
    // proofs.md:299 "A3 | `add 2 3 = 5` via δ-unfold | δ-unfold + Ω_K confluence".
    // add := λm.λn. Nat.rec (λ_:Nat.Nat) m (λk.λih. succ ih) n   (recursion on n).
    //   add m zero = m ; add m (succ k) = succ (add m k).
    // `conv` routes through nf_tm (kernel symbols present): δ unfolds `add`, β substitutes
    // 2/3, ι fires on each `succ` of the scrutinee, leaving the literal `5`.
    let mut env = nat_env();
    let nat_ty = Tm::Ind(IndId(0));
    let add_body = lam(
        nat_ty.clone(), // m
        lam(
            nat_ty.clone(), // n
            // Elim Nat (λ_.Nat) m (λk.λih. succ ih) n
            app(
                app(
                    app(
                        app(Tm::Elim(IndId(0)), lam(nat_ty.clone(), nat_ty.clone())), // motive λ_.Nat
                        Tm::Var(1), // minor_zero = m
                    ),
                    lam(nat_ty.clone(), lam(nat_ty.clone(), succ(Tm::Var(0)))), // minor_succ = λk.λih. succ ih
                ),
                Tm::Var(0), // scrutinee = n
            ),
        ),
    );
    // add : Nat → Nat → Nat (acyclicity only; conv supplies the computation).
    let add_ty = Tm::Pi(
        Box::new(nat_ty.clone()),
        Box::new(Tm::Pi(Box::new(nat_ty.clone()), Box::new(nat_ty.clone()))),
    );
    env.add_const(ConstId(0), add_ty, add_body).unwrap();

    let lit = |n: u32| (0..n).fold(zero(), |acc, _| succ(acc));
    let add_2_3 = app(app(Tm::Const(ConstId(0)), lit(2)), lit(3));
    // add 2 3 ≡ 5, and (no false green) NOT ≡ 4.
    assert!(
        conv(&env, &Vec::new(), &add_2_3, &lit(5)).unwrap(),
        "add 2 3 ≡ 5 (δ+ι)"
    );
    assert!(
        !conv(&env, &Vec::new(), &add_2_3, &lit(4)).unwrap(),
        "add 2 3 ≢ 4"
    );
    // the normal form is the literal 5 verbatim (δ-unfold + ι reach a ctor spine).
    assert_eq!(
        nf_tm(&env, &Vec::new(), &add_2_3),
        lit(5),
        "add 2 3 normalizes to literal 5"
    );
}

#[test]
fn a7_beta_equal_terms_convertible() {
    // (λx.x)(λy.y) ≡ λy.y  — closed β-conv
    let env = GlobalEnv::default();
    let id = lam(Tm::Sort(0), Tm::Var(0));
    let redex = app(lam(Tm::Sort(0), Tm::Var(0)), id.clone());
    assert!(conv(&env, &Vec::new(), &redex, &id).unwrap());
}

#[test]
fn a8_alpha_rename_roundtrip() {
    // proofs.md:304 "A8 | α-rename roundtrip: `λx.λy.x` survives φ_K → Ω_K → φ_K⁻¹ intact |
    //                 de Bruijn scoping in readback".
    // K = λx.λy.x  (outer binder used, inner dropped ⇒ Era inserted in the net, gone on readback).
    let k = lam(Tm::Sort(0), lam(Tm::Sort(0), Tm::Var(1)));
    // K2 = λx.λy.y  (the other projection) — must stay distinct after the roundtrip (R9 at the
    // net level: no de Bruijn capture/collapse during readback).
    let k2 = lam(Tm::Sort(0), lam(Tm::Sort(0), Tm::Var(0)));

    // (a) roundtrip is intact: K reads back α-equal to K (binder identity & scope preserved).
    assert!(
        net_roundtrip_alpha_eq(&k, &k),
        "λx.λy.x survives φ_K→Ω_K→φ_K⁻¹ α-intact"
    );
    // (b) the two projections do NOT collapse: readback distinguishes which binder x refers to.
    assert!(
        !net_roundtrip_alpha_eq(&k, &k2),
        "λx.λy.x ≢ λx.λy.y after roundtrip (de Bruijn scope, no capture)"
    );
    // (c) the readback shape is a genuine 2-binder λ (not Partial/collapsed) whose body refers
    //     to the OUTER binder — pins scoping is correct, not merely self-consistent. The inner
    //     binder y is unused ⇒ readback wraps the body in an Era weakening (erase.rs:40).
    match net_roundtrip(&k) {
        ReadbackResult::Lambda(Ast::Abs(x, body)) => match *body {
            Ast::Abs(_y, inner) => assert!(
                matches!(peel_era(&inner), Ast::Name(n) if *n == x),
                "inner body (mod weakening) is the OUTER binder x (λx.λy.x), got {inner:?}"
            ),
            other => panic!("expected nested λ (λx.λy. …), got {other:?}"),
        },
        ReadbackResult::Lambda(other) => panic!("expected outer λ, got {other:?}"),
        ReadbackResult::Partial(n) => panic!("expected a 2-binder λ readback, got Partial({n})"),
    }
}

#[test]
fn a4_eta_pi() {
    // opaque f (free Var) ;  f ≡ λx. f x   — η-contraction (Var 0 ∉ FV(f)).
    let env = GlobalEnv::default();
    let f = Tm::Var(5);
    // under the λ, f is shifted: λx. (Var 6) x
    let eta = lam(Tm::Sort(0), app(Tm::Var(6), Tm::Var(0)));
    assert!(
        conv(&env, &Vec::new(), &f, &eta).unwrap(),
        "f ≡ λx. f x (η-Π)"
    );
}

#[test]
fn a5_large_elim_typing() {
    // motive : Nat → Type0  (large elimination — motive lands in a universe).
    // Typing `Elim Nat motive` must succeed with the motive's result sort free (predicativity).
    let env = nat_env();
    let motive = lam(Tm::Ind(IndId(0)), Tm::Sort(0));
    let elim_m = app(Tm::Elim(IndId(0)), motive);
    let ty = infer(&env, &Vec::new(), &elim_m).expect("large-elim motive into Type accepted (A5)");
    assert!(
        matches!(ty, Tm::Pi(..)),
        "yields the remaining recursor telescope"
    );
}

// Vec A n  (params [A:Type], indices [n:Nat]); Nat = IndId(0), Vec = IndId(1).
//   nil  : Vec A 0
//   cons : Π(a:A)(k:Nat)(xs:Vec A k). Vec A (succ k)
fn vec_env() -> GlobalEnv {
    let mut e = nat_env();
    let vec = Inductive {
        id: IndId(1),
        params: vec![Tm::Sort(0)],        // A : Type0
        indices: vec![Tm::Ind(IndId(0))], // n : Nat
        sort: 0,
        ctors: vec![
            CtorDecl {
                ctor_ix: 0,
                args: vec![],
                ret_indices: vec![zero()], // Vec A 0
            },
            CtorDecl {
                ctor_ix: 1,
                // [a:A, k:Nat, xs:Vec A k] in ctx [A]: A=Var0; then [A,a]; then [A,a,k]: A=Var2,k=Var0
                args: vec![
                    Tm::Var(0),
                    Tm::Ind(IndId(0)),
                    app(app(Tm::Ind(IndId(1)), Tm::Var(2)), Tm::Var(0)),
                ],
                // ret index `succ k`: ctx [A,a,k,xs] ⇒ k=Var(1)
                ret_indices: vec![succ(Tm::Var(1))],
            },
        ],
    };
    e.add_inductive(vec).unwrap();
    e
}
fn vnil(a: Tm) -> Tm {
    app(Tm::Ctor(IndId(1), 0), a)
}
fn vcons(a: Tm, x: Tm, k: Tm, xs: Tm) -> Tm {
    app(app(app(app(Tm::Ctor(IndId(1), 1), a), x), k), xs)
}

#[test]
fn a6_indexed_recursor() {
    use dnx_proof::recursor::recursor_type;
    let env = vec_env();
    let vec = env.inds.get(&IndId(1)).unwrap();

    // (a) recursor_type handles the full P+X telescope (proofs.md:163-181). The cons-minor
    // result must be `motive (succ k_field) (cons A fields…)`; nil-minor `motive 0 (nil A)`.
    let rt = recursor_type(vec, 1).expect("indexed recursor type synthesized (A6)");
    // Structurally: outermost Π is the param A:Sort0, then the motive Π(n:Nat)Π(x:Vec A n).Sort1.
    let (p_dom, after_p) = match rt {
        Tm::Pi(d, b) => (*d, *b),
        _ => panic!("recursor starts with a param Π"),
    };
    assert_eq!(p_dom, Tm::Sort(0), "first binder = param A : Type0");
    let motive_ty = match &after_p {
        Tm::Pi(d, _) => (**d).clone(),
        _ => panic!("second binder = motive"),
    };
    // motive : Π(n:Nat) Π(x: Vec A n). Sort 1
    let expect_motive = Tm::Pi(
        Box::new(Tm::Ind(IndId(0))), // n : Nat
        Box::new(Tm::Pi(
            // x : Vec A n  ⇒ Vec applied to param A (Var(1) under n) and n (Var(0))
            Box::new(app(app(Tm::Ind(IndId(1)), Tm::Var(1)), Tm::Var(0))),
            Box::new(Tm::Sort(1)),
        )),
    );
    assert_eq!(
        motive_ty, expect_motive,
        "indexed motive Π(X)(x:I P X).Sort ℓ"
    );

    // The cons-minor (4th Π: after A, motive, minor_nil) exercises ret_indices + IH index
    // relocation (proofs.md:177-180). In its body ctx [A,motive,minor_nil,a,k,xs,ih] (depth 4):
    //   result = motive (succ k) (cons A a k xs) ;  ih : motive k xs.
    // Layout: motive=Var5, A=Var6, a=Var3, k=Var2, xs=Var1, ih@motive=Var4, ih_k=Var1, ih_xs=Var0.
    let nat = Tm::Ind(IndId(0));
    let vec_at = |t: Tm, n: Tm| app(app(Tm::Ind(IndId(1)), t), n);
    let cons_minor = {
        // skip motive (after_p = Π motive. rest) then minor_nil to reach minor_cons.
        let after_motive = match after_p {
            Tm::Pi(_, b) => *b,
            _ => panic!(),
        };
        match after_motive {
            Tm::Pi(_minor_nil, b) => match *b {
                Tm::Pi(d, _) => *d, // minor_cons domain
                _ => panic!("minor_cons present"),
            },
            _ => panic!("minor_nil present"),
        }
    };
    let expect_cons_minor = Tm::Pi(
        Box::new(Tm::Var(2)), // a : A
        Box::new(Tm::Pi(
            Box::new(nat.clone()), // k : Nat
            Box::new(Tm::Pi(
                Box::new(vec_at(Tm::Var(4), Tm::Var(0))), // xs : Vec A k
                Box::new(Tm::Pi(
                    // ih : motive k xs
                    Box::new(app(app(Tm::Var(4), Tm::Var(1)), Tm::Var(0))),
                    Box::new(app(
                        app(Tm::Var(5), succ(Tm::Var(2))), // motive (succ k)
                        app(
                            app(
                                app(app(Tm::Ctor(IndId(1), 1), Tm::Var(6)), Tm::Var(3)),
                                Tm::Var(2),
                            ),
                            Tm::Var(1),
                        ), // cons A a k xs
                    )),
                )),
            )),
        )),
    );
    assert_eq!(
        cons_minor, expect_cons_minor,
        "cons-minor: result motive(ret_idx=succ k)(cons…) + IH motive(idx xs = k) xs (A6)"
    );

    // (b) ι threads `idx rec_j`: length via Vec.rec. minor_nil = zero;
    //     minor_cons = λa.λk.λxs.λih. succ ih  ⇒  len(cons _ _ _ nil) = succ zero.
    // element-type witness = Nat (`Ind Nat : Type0`); the driver infers each rec field's type
    // to read its indices (proofs.md:187), so the scrutinee must be well-typed (D1 precondition).
    let a = Tm::Ind(IndId(0)); // A := Nat : Type0
    let motive = lam(
        Tm::Ind(IndId(0)),
        lam(
            app(app(Tm::Ind(IndId(1)), a.clone()), Tm::Var(0)),
            Tm::Ind(IndId(0)),
        ),
    );
    let m_cons = lam(
        a.clone(),
        lam(
            Tm::Ind(IndId(0)),
            lam(
                app(app(Tm::Ind(IndId(1)), a.clone()), Tm::Var(0)),
                lam(Tm::Ind(IndId(0)), succ(Tm::Var(0))),
            ),
        ),
    );
    let one = succ(zero());
    // Elim Vec  A  motive  minor_nil  minor_cons  (succ 0)  (cons A 0 0 (nil A))
    let rec = app(
        app(
            app(
                app(app(app(Tm::Elim(IndId(1)), a.clone()), motive), zero()),
                m_cons,
            ),
            one.clone(),
        ),
        vcons(a.clone(), zero(), zero(), vnil(a)),
    );
    assert_eq!(
        nf_tm(&env, &Vec::new(), &rec),
        one,
        "Vec.rec computes length 1 of (cons _ _ _ nil); IH threaded at idx 0 (A6, proofs.md:187)"
    );
}

#[test]
fn a6_indexed_recursor_guards() {
    // no-false-green: the indexed recursor still obeys R4/R5 (proofs.md:193).
    let env = vec_env();
    let a = Tm::Ind(IndId(0));
    let motive = lam(
        Tm::Ind(IndId(0)),
        lam(
            app(app(Tm::Ind(IndId(1)), a.clone()), Tm::Var(0)),
            Tm::Ind(IndId(0)),
        ),
    );
    // R5: missing the index + scrutinee (arity = np+1+nctors+nidx+1 = 6) ⇒ stuck.
    let under = app(
        app(app(Tm::Elim(IndId(1)), a.clone()), motive.clone()),
        zero(),
    );
    assert_eq!(
        whnf_tm(&env, &Vec::new(), &under),
        under,
        "underapplied Vec.rec stuck (R5)"
    );
    // R4: full arity but neutral scrutinee (Var) ⇒ ι never fires.
    let neutral = app(
        app(
            app(
                app(app(app(Tm::Elim(IndId(1)), a.clone()), motive), zero()),
                zero(),
            ),
            zero(),
        ),
        Tm::Var(0),
    );
    assert_eq!(
        whnf_tm(&env, &Vec::new(), &neutral),
        neutral,
        "ι on neutral Vec scrutinee stuck (R4)"
    );
}

// ═══ MUST-REJECT ═══

#[test]
fn r1_type_in_type_rejected() {
    // T-Sort gives `Sort 0 : Sort 1`, never `Sort 0` ⇒ checking at goal `Sort 0` mismatches.
    let env = GlobalEnv::default();
    assert_eq!(
        check(&env, &Vec::new(), &Tm::Sort(0), &Tm::Sort(0)),
        Err(TypeError::Mismatch)
    );
}

#[test]
fn r2_pi_universe_is_max() {
    let env = GlobalEnv::default();
    let pi = Tm::Pi(Box::new(Tm::Sort(1)), Box::new(Tm::Sort(0)));
    assert_eq!(infer(&env, &Vec::new(), &pi).unwrap(), Tm::Sort(2));
}

#[test]
fn r2_pi_placed_too_low_rejected() {
    // proofs.md:309 R2 row "`Π(A:Typeᵤ).A : Typeᵤ` (Π placed too low) | Hurkens via Π
    // universe-max miscompute"; proofs.md:84 T-Pi `max i j`. The impredicative claim
    // `Π(A:Type₀). A : Type₀` would re-enable Hurkens' paradox.
    // Real type: dom Type₀:Sort1 (i=1), cod A:Sort0 (j=0) ⇒ max(1,0)=Sort1 ≠ claimed Sort0.
    let env = GlobalEnv::default();
    let pi = Tm::Pi(Box::new(Tm::Sort(0)), Box::new(Tm::Var(0)));
    assert_eq!(infer(&env, &Vec::new(), &pi).unwrap(), Tm::Sort(1)); // computed at max, not low
    assert_eq!(
        check(&env, &Vec::new(), &pi, &Tm::Sort(0)),
        Err(TypeError::Mismatch) // claiming the too-low `Type₀` fails
    );
}

#[test]
fn r3_non_positive_inductive_rejected() {
    // Bad := mk : (Bad → Bad) → Bad
    let arg = Tm::Pi(
        Box::new(Tm::Pi(
            Box::new(Tm::Ind(IndId(0))),
            Box::new(Tm::Ind(IndId(0))),
        )),
        Box::new(Tm::Ind(IndId(0))),
    );
    assert!(!strictly_positive(&GlobalEnv::default(), IndId(0), &arg));

    let mut env = GlobalEnv::default();
    let bad = Inductive {
        id: IndId(0),
        params: vec![],
        indices: vec![],
        sort: 0,
        ctors: vec![CtorDecl {
            ctor_ix: 0,
            args: vec![arg],
            ret_indices: vec![],
        }],
    };
    // rejected for the RIGHT reason: positivity, not some unrelated decl error.
    assert_eq!(
        env.add_inductive(bad),
        Err(AdmitError::BadDecl("non-positive"))
    );
}

#[test]
fn r3_buried_occurrence_rejected() {
    // proofs.md:154 "`Ind` ... never under non-spos"; Lean `inductive.cpp:404-407`.
    // Bad2 := mk : (f Bad2) → Bad2 — `Bad2` buried as an App arg under `Const f`.
    // F Bad2 with `F X = X → Void` is a NEGATIVE occurrence ⇒ proves False. MUST reject.
    let field = Tm::App(Box::new(Tm::Const(ConstId(0))), Box::new(Tm::Ind(IndId(0))));
    let mut env = GlobalEnv::default();
    let bad2 = Inductive {
        id: IndId(0),
        params: vec![],
        indices: vec![],
        sort: 0,
        ctors: vec![CtorDecl {
            ctor_ix: 0,
            args: vec![field],
            ret_indices: vec![],
        }],
    };
    assert_eq!(
        env.add_inductive(bad2),
        Err(AdmitError::BadDecl("non-positive"))
    );
    assert!(!env.inds.contains_key(&IndId(0))); // nothing leaks on rejection
}

#[test]
fn r3_direct_recursive_field_accepted() {
    // no-false-green: a DIRECT recursive arg `Ind self` (Nat.succ) is strictly positive
    // ⇒ admitted. Confirms r3 is the occurrence-classifier, not a blanket reject.
    let mut env = GlobalEnv::default();
    assert!(env.add_inductive(nat()).is_ok());
    assert!(env.inds.contains_key(&IndId(0)));
}

#[test]
fn r3_negative_behind_delta_const_rejected() {
    // proofs.md:155 "Lean `inductive.cpp:393-409` … **whnf arg**; `Ind` in ANY Pi-domain → reject".
    // The positivity check MUST whnf each ctor-field type before the occurrence walk. A NEGATIVE
    // occurrence hidden behind a δ-unfoldable `Const` is invisible to a raw (un-whnf'd) occurs-check.
    //
    //   Unit : Type0                            (a base type, ≠ Bad, to feed `g`)
    //   g    := λ_:Type0. (Bad → Type0)         (ignores its arg; δ-unfolds to `Bad → Type`)
    //   Bad  : Type1 := mk : (g Unit) → Bad
    //
    // `g Unit` δ→ `Bad → Type0` = `Pi(Ind Bad, Sort0)` ⇒ `Bad` stands LEFT of `→` = a NEGATIVE
    // (non-strictly-positive) occurrence ⇒ `Bad` is genuinely non-positive ⇒ admits ⊥ ⇒ MUST reject.
    // Raw occurs sees only `App(Const g, Ind Unit)` (no `Ind Bad` token) ⇒ would wrongly accept.
    const UNIT: IndId = IndId(0);
    const BAD: IndId = IndId(1);
    let mut env = GlobalEnv::default();
    // Unit : Type0 (one nullary ctor; only needed as a Sort0 inhabitant to apply `g`).
    env.add_inductive(Inductive {
        id: UNIT,
        params: vec![],
        indices: vec![],
        sort: 0,
        ctors: vec![CtorDecl {
            ctor_ix: 0,
            args: vec![],
            ret_indices: vec![],
        }],
    })
    .unwrap();
    // g := λ_:Type0. (Bad → Type0)   :   Π(_:Type0). Sort1   (acyclicity only; refs `Ind Bad`).
    let g_body = lam(
        Tm::Sort(0),
        Tm::Pi(Box::new(Tm::Ind(BAD)), Box::new(Tm::Sort(0))),
    );
    let g_ty = Tm::Pi(Box::new(Tm::Sort(0)), Box::new(Tm::Sort(1)));
    env.add_const(ConstId(0), g_ty, g_body).unwrap();
    // Bad : Type1 := mk : (g Unit) → Bad   — the field `g Unit` is the δ-hidden negative.
    let field = app(Tm::Const(ConstId(0)), Tm::Ind(UNIT)); // g Unit  (δ→ Bad → Type0)
    let bad = Inductive {
        id: BAD,
        params: vec![],
        indices: vec![],
        sort: 1, // ≥ field sort (g Unit : Sort1) so R11 (field-universe) cannot pre-empt positivity
        ctors: vec![CtorDecl {
            ctor_ix: 0,
            args: vec![field],
            ret_indices: vec![],
        }],
    };
    assert_eq!(
        env.add_inductive(bad),
        Err(AdmitError::BadDecl("non-positive")),
        "a NEGATIVE occurrence hidden behind a δ-Const (g Unit ≡ Bad → Type) must be REJECTED \
         (proofs.md:155 'whnf arg')"
    );
    assert!(
        !env.inds.contains_key(&BAD),
        "rejection rolls back — the non-positive Bad must not leak into the env"
    );
}

#[test]
fn r3_positive_behind_delta_const_accepted() {
    // No-false-green (the ACCEPT half of the whnf fix): a δ-`Const` field that unfolds to a
    // NON-recursive type must STILL be admitted — the fix whnf's to *classify* the occurrence,
    // it is not a blanket "reject any Const-headed field".
    //   Unit : Type0 ;  h := λ_:Type0. Type0   (h X ≡ Type0, no `Good` occurrence)
    //   Good : Type1 := mk : (h Unit) → Good   — `h Unit` δ→ `Type0` ⇒ nonrecursive arg ⇒ OK.
    const UNIT: IndId = IndId(0);
    const GOOD: IndId = IndId(1);
    let mut env = GlobalEnv::default();
    env.add_inductive(Inductive {
        id: UNIT,
        params: vec![],
        indices: vec![],
        sort: 0,
        ctors: vec![CtorDecl {
            ctor_ix: 0,
            args: vec![],
            ret_indices: vec![],
        }],
    })
    .unwrap();
    // h := λ_:Type0. Type0  :  Π(_:Type0). Sort1  (h Unit : Sort1; no recursive occ of Good).
    let h_body = lam(Tm::Sort(0), Tm::Sort(0));
    let h_ty = Tm::Pi(Box::new(Tm::Sort(0)), Box::new(Tm::Sort(1)));
    env.add_const(ConstId(0), h_ty, h_body).unwrap();
    let field = app(Tm::Const(ConstId(0)), Tm::Ind(UNIT)); // h Unit  (δ→ Type0)
    let good = Inductive {
        id: GOOD,
        params: vec![],
        indices: vec![],
        sort: 1, // field `h Unit : Sort1` ⇒ decl sort 1 satisfies R11
        ctors: vec![CtorDecl {
            ctor_ix: 0,
            args: vec![field],
            ret_indices: vec![],
        }],
    };
    assert!(
        env.add_inductive(good).is_ok(),
        "a δ-Const field unfolding to a NON-recursive type (h Unit ≡ Type0) must be ACCEPTED"
    );
    assert!(env.inds.contains_key(&GOOD));
}

#[test]
fn r4_iota_on_neutral_does_not_fire() {
    let env = nat_env();
    let stuck = app(
        app(app(app(Tm::Elim(IndId(0)), Tm::Sort(0)), zero()), zero()),
        Tm::Var(0), // neutral scrutinee
    );
    assert_eq!(whnf_tm(&env, &Vec::new(), &stuck), stuck);
}

#[test]
fn r5_underapplied_recursor_stays_stuck() {
    let env = nat_env();
    let t = app(Tm::Elim(IndId(0)), Tm::Sort(0)); // missing minors + scrutinee
    assert_eq!(whnf_tm(&env, &Vec::new(), &t), t);
}

#[test]
fn r7_delta_cycle_rejected() {
    let mut env = GlobalEnv::default();
    // A := A  (self-reference, not yet admitted) ⇒ rejected
    assert!(env
        .add_const(ConstId(0), Tm::Sort(0), Tm::Const(ConstId(0)))
        .is_err());
}

#[test]
fn r9_distinct_projections_differ() {
    let env = GlobalEnv::default();
    let k = lam(Tm::Sort(0), lam(Tm::Sort(0), Tm::Var(1)));
    let k2 = lam(Tm::Sort(0), lam(Tm::Sort(0), Tm::Var(0)));
    assert!(!conv(&env, &Vec::new(), &k, &k2).unwrap());
    assert!(conv(&env, &Vec::new(), &k, &k.clone()).unwrap());
}

#[test]
fn r11_ctor_field_universe_too_big_rejected() {
    // proofs.md §4:319 — `Inductive Big : Type₀ := mk : Type₀ → Big`.
    // The field `Type₀` lives in `Sort 1` > decl `sort 0` ⇒ predicativity break ⇒ reject.
    // (Lean `inductive.cpp:435-442`; dnx drops the `is_zero`/Prop escape — STRICT.)
    let mut env = GlobalEnv::default();
    let big = Inductive {
        id: IndId(0),
        params: vec![],
        indices: vec![],
        sort: 0,
        ctors: vec![CtorDecl {
            ctor_ix: 0,
            args: vec![Tm::Sort(0)], // field type Type₀ : Sort 1
            ret_indices: vec![],
        }],
    };
    assert_eq!(
        env.add_inductive(big),
        Err(AdmitError::BadDecl("field universe too big"))
    );
    // rejection rolls back the provisional registration — nothing leaks into the env.
    assert!(!env.inds.contains_key(&IndId(0)));
}

#[test]
fn r11_field_at_decl_level_accepted() {
    // Same shape, but declared in `Type₁`: field `Type₀ : Sort 1` ≤ decl `sort 1` ⇒ OK.
    // Confirms R11 is the level-compare gate, not a blanket reject (no false-green).
    let mut env = GlobalEnv::default();
    let big1 = Inductive {
        id: IndId(0),
        params: vec![],
        indices: vec![],
        sort: 1,
        ctors: vec![CtorDecl {
            ctor_ix: 0,
            args: vec![Tm::Sort(0)],
            ret_indices: vec![],
        }],
    };
    assert!(env.add_inductive(big1).is_ok());
}

// ── Indexed-family ret_index well-formedness (proofs.md §4:131-159; the indexed-family analogue
//    of the R11 gate). `add_inductive` must reject a ctor whose `ret_indices` skew the declared
//    index telescope (wrong arity) or are ill-typed at the index types — otherwise `infer(Ctor)`
//    builds a malformed `I P ret_indices` head ⇒ `recursor_type` emits a motive-application with
//    arity skew ⇒ an ill-typed recursor whose minors inhabit a bogus motive instance = UNSOUND.

#[test]
fn ret_index_arity_skew_rejected() {
    // Malformed `Vec`: `cons` returns `Vec A` with NO length index (ret_indices = []) while the
    // family declares one index (n:Nat). The arity skew must be REJECTED at admission.
    let mut env = nat_env(); // Nat = IndId(0)
    let bad_vec = Inductive {
        id: IndId(1),
        params: vec![Tm::Sort(0)],        // A : Type0
        indices: vec![Tm::Ind(IndId(0))], // n : Nat  (ONE index)
        sort: 0,
        ctors: vec![
            CtorDecl {
                ctor_ix: 0,
                args: vec![],
                ret_indices: vec![zero()], // nil : Vec A 0  (well-formed)
            },
            CtorDecl {
                ctor_ix: 1,
                args: vec![
                    Tm::Var(0),
                    Tm::Ind(IndId(0)),
                    app(app(Tm::Ind(IndId(1)), Tm::Var(2)), Tm::Var(0)),
                ],
                ret_indices: vec![], // BUG: returns `Vec A` — missing the length index
            },
        ],
    };
    assert_eq!(
        env.add_inductive(bad_vec),
        Err(AdmitError::BadDecl("ret_indices arity mismatch")),
        "a ctor returning `Vec A` (no length index) for a 1-index family must be rejected"
    );
    assert!(
        !env.inds.contains_key(&IndId(1)),
        "rejection leaks nothing into the env"
    );
}

#[test]
fn ret_index_ill_typed_rejected() {
    // Malformed `Vec`: `nil` returns `Vec A Type₀` — the index value `Sort 0` is a TYPE, not the
    // declared `n : Nat`. An ill-typed ret_index must be REJECTED (no bogus index admitted).
    let mut env = nat_env();
    let bad_vec = Inductive {
        id: IndId(1),
        params: vec![Tm::Sort(0)],        // A : Type0
        indices: vec![Tm::Ind(IndId(0))], // n : Nat
        sort: 0,
        ctors: vec![CtorDecl {
            ctor_ix: 0,
            args: vec![],
            ret_indices: vec![Tm::Sort(0)], // BUG: `Type₀ : Sort 1` is not a `Nat`
        }],
    };
    assert_eq!(
        env.add_inductive(bad_vec),
        Err(AdmitError::BadDecl("ill-typed ret_index")),
        "a ret_index of the wrong type (Sort where Nat is declared) must be rejected"
    );
    assert!(
        !env.inds.contains_key(&IndId(1)),
        "rejection leaks nothing into the env"
    );
}

#[test]
fn ret_index_wellformed_vec_accepted() {
    // No-false-green (the ACCEPT half): the genuine `Vec A n` — `nil : Vec A 0`,
    // `cons : … Vec A (succ k)` — has arity-correct, well-typed ret_indices ⇒ STAYS admitted.
    // (The `Id` family in tests/eq_prelude.rs covers the other valid indexed inductive.)
    let env = vec_env();
    assert!(
        env.inds.contains_key(&IndId(1)),
        "the well-formed Vec is admitted"
    );
    // And its constructors still infer their indexed types (the gate did not corrupt admission).
    let cons_ty = infer(&env, &Vec::new(), &Tm::Ctor(IndId(1), 1));
    assert!(
        cons_ty.is_ok(),
        "cons : Π(A)(a:A)(k:Nat)(xs:Vec A k). Vec A (succ k) still infers"
    );
}

#[test]
fn r6_wrong_minor_count_rejected() {
    // proofs.md:315 (R6) "Recursor with wrong minor-premise count | Elim arity-table mismatch";
    // §2:89 "wrong minor count rejected by arity-table". `Nat` has TWO ctors ⇒ the recursor type
    // (recursor.rs:55) binds TWO minors (mz, ms). Supplying ONE minor then the scrutinee makes the
    // scrutinee `two : Nat` land at the `ms` binder, whose domain is the Π-type
    // `Π(n:Nat). motive n → motive (succ n)` (NOT `Nat`) ⇒ T-App `check` calls `conv(Nat, Π…)`
    // which fails ⇒ the malformed recursor application is REJECTED. A wrong arg-slicing here would
    // otherwise feed `minor_k` the wrong number of fields (G2:243 "wrong arg slicing → proves False").
    let env = nat_env();
    let motive = lam(Tm::Ind(IndId(0)), Tm::Ind(IndId(0))); // λ_:Nat. Nat  (motive : Nat→Type0)
    let mz = zero(); // minor_zero : motive zero ≡ Nat  ⇒  zero : Nat
                     // minor_succ : Π(n:Nat). motive n → motive (succ n)  ≡  Π(_:Nat)(_:Nat). Nat
    let ms = lam(Tm::Ind(IndId(0)), lam(Tm::Ind(IndId(0)), succ(Tm::Var(0))));
    let two = succ(succ(zero()));

    // ACCEPT (no-false-green): the FULL, arity-correct application infers a type.
    let ok = app(
        app(app(app(Tm::Elim(IndId(0)), motive.clone()), mz.clone()), ms),
        two.clone(),
    );
    assert!(
        infer(&env, &Vec::new(), &ok).is_ok(),
        "the arity-correct Nat recursor application must typecheck"
    );

    // REJECT: drop `minor_succ` — only ONE minor, so `two` is checked at the `ms` binder's Π domain.
    let bad = app(app(app(Tm::Elim(IndId(0)), motive), mz), two);
    assert_eq!(
        infer(&env, &Vec::new(), &bad),
        Err(TypeError::Mismatch),
        "a recursor missing a minor premise (wrong minor count) must be rejected (R6)"
    );
}

// Bool := false | true  (a second, distinct inductive for the R8 domain-mismatch trap).
fn bool_env() -> GlobalEnv {
    let mut e = nat_env(); // Nat = IndId(0)
    let b = Inductive {
        id: IndId(1),
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
                args: vec![],
                ret_indices: vec![],
            },
        ],
    };
    e.add_inductive(b).unwrap();
    e
}

#[test]
fn r8_eta_pi_mismatched_domains_rejected() {
    // proofs.md:317 (R8) "η-Π with mismatched domains: `λx:A.f x` ≠ `f` when `f:B→C`, `A≠B`".
    // η is sound ONLY because of the §0 invariant (proofs.md:42): conv is reached ONLY after both
    // sides `check` at the SAME type. A wrong-domain η-expansion `λx:A. f x` (with `f : B→C`, A≠B)
    // is rejected by typing BEFORE conv — exactly the D1/§0 guard (proofs.md:326). Here `f : Nat→Nat`
    // and the η-expansion binds `x:Bool`, feeding `Bool` into `f`'s `Nat` domain.
    let mut env = bool_env(); // Nat = IndId(0), Bool = IndId(1)
    let nat = Tm::Ind(IndId(0));
    let nat2nat = Tm::Pi(Box::new(nat.clone()), Box::new(nat.clone())); // Nat → Nat
    env.add_const(ConstId(0), nat2nat.clone(), lam(nat.clone(), Tm::Var(0)))
        .unwrap(); // f := λx:Nat. x  :  Nat → Nat
    let f = Tm::Const(ConstId(0));

    // ACCEPT (no-false-green): η-expansion at the CORRECT domain typechecks, and is convertible to f.
    let eta_ok = lam(nat.clone(), app(f.clone(), Tm::Var(0))); // λx:Nat. f x
    assert!(
        check(&env, &Vec::new(), &eta_ok, &nat2nat).is_ok(),
        "the correctly-domained η-expansion λx:Nat. f x : Nat→Nat typechecks"
    );
    assert!(
        conv(&env, &Vec::new(), &f, &eta_ok).unwrap(),
        "f ≡ λx:Nat. f x  (η-Π, matching domains)"
    );

    // REJECT: η-expansion at the WRONG domain — `λx:Bool. f x` feeds `Bool` to `f : Nat→Nat`.
    let eta_bad = lam(Tm::Ind(IndId(1)), app(f, Tm::Var(0))); // λx:Bool. f x
    assert_eq!(
        infer(&env, &Vec::new(), &eta_bad),
        Err(TypeError::Mismatch),
        "η-expansion binding a mismatched domain (Bool ≠ Nat) must be rejected (R8)"
    );
}

#[test]
#[ignore = "R10 N/A — no Prop sort in v1 (settled C2)"]
fn r10_prop_large_elim() {}

#[test]
#[ignore = "D2 differential fuzz — OPEN-15, needs independent reference normalizer"]
fn d2_differential_fuzz() {}

// ═══ conv-engine audit (ws-conv): δ-compute + open-term routing (proofs.md:328 D3) ═══

#[test]
fn a3_delta_unfold_computes() {
    // c := λx.x ; conv (c applied to id) ≡ id  via δ
    let mut env = GlobalEnv::default();
    let id = lam(Tm::Sort(0), Tm::Var(0));
    env.add_const(ConstId(0), Tm::Sort(0), id.clone()).unwrap();
    let lhs = app(Tm::Const(ConstId(0)), id.clone());
    assert!(conv(&env, &Vec::new(), &lhs, &id).unwrap());
}

#[test]
fn d3_open_neutral_conv_uses_congruence() {
    // The `id A x` T-Conv case: comparing two bare context Vars. An OPEN term (free Var)
    // must take the structural-congruence path, NOT the net fast path (proofs.md:328 D3:
    // "open term with free vars must NOT take ArtifactId LOCAL fast path"). Same free head
    // ⇒ conv-YES, with NO panic in erase (the bug: to_ast(Var,depth=0) underflowed).
    let env = GlobalEnv::default();
    assert!(
        conv(&env, &Vec::new(), &Tm::Var(0), &Tm::Var(0)).unwrap(),
        "open neutral Var(0) ≡ Var(0) via congruence (D3), no panic"
    );
    // Neutral applied to a neutral arg: same head + congruent args ⇒ conv-YES.
    let neu = app(Tm::Var(1), Tm::Var(0));
    assert!(
        conv(&env, &Vec::new(), &neu, &neu.clone()).unwrap(),
        "open neutral (Var 1) (Var 0) ≡ itself via congruence (D3)"
    );
}

#[test]
fn d3_id_applied_typechecks_open() {
    // End-to-end trigger of the bug: typecheck `id A x` in an OPEN context [A:Type, x:A].
    // T-App on the last arg makes `check` call `conv` on two bare context Vars (got=A vs A);
    // before the D3 routing fix this panicked in erase (`to_ast(Var, depth=0)` underflow).
    let env = GlobalEnv::default();
    // id := λ(A:Type).λ(x:A). x   :   Π(A:Type).Π(x:A). A
    let id = lam(Tm::Sort(0), lam(Tm::Var(0), Tm::Var(0)));
    let ctx = vec![Tm::Sort(0), Tm::Var(0)]; // A:Type (idx 1), x:A (idx 0)
    let expr = app(app(id, Tm::Var(1)), Tm::Var(0)); // id A x
                                                     // result type is `A` = Var(1) in this context.
    assert!(
        check(&env, &ctx, &expr, &Tm::Var(1)).is_ok(),
        "`id A x` typechecks at `A` in an open context (D3 path, no panic)"
    );
}

#[test]
fn d3_distinct_neutrals_do_not_convert() {
    // Negative: two DISTINCT open neutrals must NOT be equal (no false-merge on the
    // congruence path). Different free heads ⇒ conv-NO.
    let env = GlobalEnv::default();
    assert!(
        !conv(&env, &Vec::new(), &Tm::Var(0), &Tm::Var(1)).unwrap(),
        "distinct free vars Var(0) ≠ Var(1)"
    );
    // Same head, distinct args ⇒ conv-NO.
    let a = app(Tm::Var(2), Tm::Var(0));
    let b = app(Tm::Var(2), Tm::Var(1));
    assert!(
        !conv(&env, &Vec::new(), &a, &b).unwrap(),
        "(Var 2)(Var 0) ≠ (Var 2)(Var 1) — congruence is structural on args"
    );
}

// ═══ A6 indexed-ι UNDER A BINDER (the &Ctx-threading fix) ═══
// Before threading, `field_indices` typed each recursive field in the EMPTY ctx, so an indexed
// recursor whose rec-field is a bound variable could not read `idx rec_j` (proofs.md:187) and ι
// stayed stuck. With `ctx` threaded through nf_tm→whnf_tm→try_iota→field_indices, the field is
// typed in its real context and indexed-ι fires under the binder.
#[test]
fn a6_indexed_iota_fires_under_binder() {
    let env = vec_env();
    let a = Tm::Ind(IndId(0)); // A := Nat : Type0
                               // motive λ(n:Nat)(_:Vec A n). Nat   (length)
    let motive = lam(
        Tm::Ind(IndId(0)),
        lam(
            app(app(Tm::Ind(IndId(1)), a.clone()), Tm::Var(0)),
            Tm::Ind(IndId(0)),
        ),
    );
    // minor_cons = λa.λk.λxs.λih. succ ih
    let m_cons = lam(
        a.clone(),
        lam(
            Tm::Ind(IndId(0)),
            lam(
                app(app(Tm::Ind(IndId(1)), a.clone()), Tm::Var(0)),
                lam(Tm::Ind(IndId(0)), succ(Tm::Var(0))),
            ),
        ),
    );
    // body (under `λ xs : Vec A 0`, so xs = Var 0):
    //   Elim Vec A motive 0 m_cons (succ 0) (cons A 0 0 xs)
    // scrutinee head = cons (a ctor) whose recursive field `xs` is a BOUND var; ι must infer
    // `xs : Vec A 0` in the binder ctx to thread `idx = 0` into the IH (proofs.md:187).
    let scrut = vcons(a.clone(), zero(), zero(), Tm::Var(0));
    let body = app(
        app(
            app(
                app(app(app(Tm::Elim(IndId(1)), a.clone()), motive), zero()),
                m_cons,
            ),
            succ(zero()),
        ),
        scrut,
    );
    let term = lam(app(app(Tm::Ind(IndId(1)), a.clone()), zero()), body); // λ xs:Vec A 0. body
    let nf = nf_tm(&env, &Vec::new(), &term);

    // ι fired ⇒ result is NOT the un-reduced input (would be the proof of regression).
    assert_ne!(
        nf, term,
        "indexed ι under a binder must reduce (was stuck with empty-ctx field typing)"
    );
    // …and it fired to the cons branch: body head is `succ (…)` (the IH applied through m_cons).
    let fired = matches!(&nf, Tm::Lam(_, b) if matches!(&**b, Tm::App(f, _) if **f == Tm::Ctor(IndId(0), 1)));
    assert!(
        fired,
        "Vec.rec on (cons … xs) under λ ι-reduces to `succ <ih>` (A6 idx threaded in ctx)"
    );
}

// MUST-REJECT: an indexed eliminator whose scrutinee index disagrees with the index supplied to
// the recursor is ill-typed and must be rejected (index-checking in infer_elim, not ι).
#[test]
fn a6_indexed_elim_wrong_index_rejected() {
    let env = vec_env();
    let a = Tm::Ind(IndId(0));
    let motive = lam(
        Tm::Ind(IndId(0)),
        lam(
            app(app(Tm::Ind(IndId(1)), a.clone()), Tm::Var(0)),
            Tm::Ind(IndId(0)),
        ),
    );
    // index arg = `succ 0` but scrutinee `nil A : Vec A 0` ⇒ scrutinee dom `Vec A (succ 0)` ≠ `Vec A 0`.
    let bad = app(
        app(
            app(
                app(app(app(Tm::Elim(IndId(1)), a.clone()), motive), zero()),
                lam(
                    a.clone(),
                    lam(
                        Tm::Ind(IndId(0)),
                        lam(
                            app(app(Tm::Ind(IndId(1)), a.clone()), Tm::Var(0)),
                            lam(Tm::Ind(IndId(0)), succ(Tm::Var(0))),
                        ),
                    ),
                ),
            ),
            succ(zero()), // claimed index 1
        ),
        vnil(a.clone()), // but nil : Vec A 0
    );
    assert_eq!(
        infer(&env, &Vec::new(), &bad),
        Err(TypeError::Mismatch),
        "indexed elim with mismatched scrutinee index must REJECT"
    );
}
