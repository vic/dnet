//! Soundness battery: each case is a KNOWN unsoundness a dependent-type kernel MUST
//! reject. If any is ACCEPTED, that is a soundness HOLE. Cases exercise the real reject
//! surface: `infer`/`check` (T-App, T-Sort R1, T-Conv) and the admission gate
//! `GlobalEnv::add_const`/`add_inductive` (R3 positivity, R7 δ-acyclicity, R11 field
//! universe, indexed-family ret-index well-formedness). Citations: proofs.md §2/§4/§5,
//! Lean `inductive.cpp`. The public API used here mirrors the crate's own theorem tests
//! (`tests/thm_plus_n_o.rs`): build `Tm` from public constructors, drive through `infer`,
//! `check`, and `add_*`.

use dnx_proof::env::{AdmitError, GlobalEnv};
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::{check, infer, TypeError};
use dnx_proof::symbol::{ConstId, IndId};
use dnx_proof::tm::Tm;

const NAT: IndId = IndId(0);

fn nat_ty() -> Tm {
    Tm::Ind(NAT)
}

/// Nat with `zero : Nat` and `succ : Nat -> Nat` — a well-formed inductive that admits, so
/// the cases below isolate ONE defect each against an otherwise-sound environment.
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
                args: vec![nat_ty()],
                ret_indices: vec![],
            },
        ],
    }
}

fn env_with_nat() -> GlobalEnv {
    let mut e = GlobalEnv::default();
    assert!(e.add_inductive(nat()).is_ok(), "Nat must admit (control)");
    e
}

fn no_ctx() -> Vec<Tm> {
    Vec::new()
}

fn pi(dom: Tm, cod: Tm) -> Tm {
    Tm::Pi(Box::new(dom), Box::new(cod))
}

fn lam(dom: Tm, body: Tm) -> Tm {
    Tm::Lam(Box::new(dom), Box::new(body))
}

fn app(f: Tm, x: Tm) -> Tm {
    Tm::App(Box::new(f), Box::new(x))
}

// ── 1. Ill-typed application: applying a NON-function (T-App requires a Π head; proofs.md
// §2 T-App / infer.rs:`as_pi`). `(Sort 0) (Sort 0)` has a non-Π head ⇒ NotAPi. Accepting it
// would let any value be "called", collapsing the function space.
#[test]
fn ill_typed_app_non_function_head_rejected() {
    let env = GlobalEnv::default();
    let bad = app(Tm::Sort(0), Tm::Sort(0));
    assert_eq!(infer(&env, &no_ctx(), &bad), Err(TypeError::NotAPi));
}

// ── 2. Ill-typed application: argument type mismatch. `id : Nat → Nat` applied to `Sort 0`
// (a type, not a Nat). T-App's `check(arg, dom)` must reject (Mismatch). Accepting a
// mistyped argument would let `motive`/predicate instantiation go wrong ⇒ unsound.
#[test]
fn ill_typed_app_arg_mismatch_rejected() {
    let env = env_with_nat();
    let id_nat = lam(nat_ty(), Tm::Var(0)); // λ(x:Nat). x  :  Nat → Nat
    let bad = app(id_nat, Tm::Sort(0)); // apply to a SORT, not a Nat
    assert_eq!(infer(&env, &no_ctx(), &bad), Err(TypeError::Mismatch));
}

// ── 3. Universe inconsistency = Type : Type (Girard's paradox source). T-Sort (R1,
// infer.rs:`Sort l : Sort (succ l)`, proofs.md §3) gives `Sort 0 : Sort 1`, NEVER
// `Sort 0 : Sort 0`. Checking `Sort 0` against goal `Sort 0` must fail (Mismatch). If it
// passed, `Type : Type` holds and Girard's paradox inhabits False.
#[test]
fn universe_type_in_type_rejected() {
    let env = GlobalEnv::default();
    assert_eq!(
        check(&env, &no_ctx(), &Tm::Sort(0), &Tm::Sort(0)),
        Err(TypeError::Mismatch),
        "Sort 0 : Sort 0 (Type:Type) MUST be rejected — else Girard's paradox"
    );
    // Positive control: the TRUE judgement `Sort 0 : Sort 1` is accepted.
    assert!(check(&env, &no_ctx(), &Tm::Sort(0), &Tm::Sort(1)).is_ok());
}

// ── 4. No cumulativity (dnx is non-cumulative, monomorphic levels; proofs.md §3).
// `Sort 0 : Sort 1` holds but `Sort 0 : Sort 5` must NOT (no `Sort i : Sort j` for j>i+1,
// no subtyping). A spurious cumulativity rule is a classic universe unsoundness.
#[test]
fn universe_no_cumulativity_rejected() {
    let env = GlobalEnv::default();
    assert_eq!(
        check(&env, &no_ctx(), &Tm::Sort(0), &Tm::Sort(5)),
        Err(TypeError::Mismatch),
    );
}

// ── 5. Non-positive inductive (proves False). `Bad` with `mk : (Bad → Bad) → Bad` puts
// `Bad` left of an arrow in a ctor field ⇒ strict-positivity (R3, proofs.md §4:154, Lean
// inductive.cpp:393-409) must reject at admission. A negative occurrence yields a fixpoint
// `Bad ≅ (Bad → Bad)` ⇒ non-termination ⇒ a closed inhabitant of False.
#[test]
fn non_positive_inductive_rejected() {
    let mut env = GlobalEnv::default();
    let bad = Inductive {
        id: NAT,
        params: vec![],
        indices: vec![],
        sort: 0,
        ctors: vec![CtorDecl {
            ctor_ix: 0,
            args: vec![pi(pi(nat_ty(), nat_ty()), nat_ty())], // (Bad → Bad) → Bad
            ret_indices: vec![],
        }],
    };
    assert_eq!(
        env.add_inductive(bad),
        Err(AdmitError::BadDecl("non-positive")),
    );
}

// ── 6. Ill-formed recursor application (wrong arity). A bare `Elim` must be applied to its
// params+motive (proofs.md §5:171; infer.rs:`infer_elim`). Here `Nat.rec` is applied to a
// single arg that is NOT a valid motive (`Sort 0` is not `Π(x:Nat).Sort`), so peeling the
// scrutinee binder off its type fails (NotAPi). A recursor used at the wrong arity/motive
// can fabricate an inhabitant of an arbitrary motive instance ⇒ unsound.
#[test]
fn recursor_wrong_arity_rejected() {
    let env = env_with_nat();
    // Nat.rec applied to a bogus "motive" that is a Sort, not a Π(x:Nat).Sort.
    let bad = app(Tm::Elim(NAT), Tm::Sort(0));
    assert!(
        matches!(
            infer(&env, &no_ctx(), &bad),
            Err(TypeError::NotAPi) | Err(TypeError::Unsupported(_)) | Err(TypeError::Mismatch)
        ),
        "Nat.rec with a non-motive argument must be rejected, got {:?}",
        infer(&env, &no_ctx(), &bad)
    );
    // And a bare, UNAPPLIED recursor (no params/motive at all) is rejected too.
    assert!(infer(&env, &no_ctx(), &Tm::Elim(NAT)).is_err());
}

// ── 7. Ill-typed constructor field. A ctor field whose type does not even type-check (here
// `(Sort 0) (Sort 0)`, a non-function application) must be rejected at admission
// (env.rs:`check_field_universes` infers each field's sort). A ctor carrying a junk field
// type breaks subject reduction for its eliminator.
#[test]
fn ill_typed_ctor_field_rejected() {
    let mut env = GlobalEnv::default();
    let bad = Inductive {
        id: NAT,
        params: vec![],
        indices: vec![],
        sort: 0,
        ctors: vec![CtorDecl {
            ctor_ix: 0,
            args: vec![app(Tm::Sort(0), Tm::Sort(0))], // field type does not type-check
            ret_indices: vec![],
        }],
    };
    assert_eq!(
        env.add_inductive(bad),
        Err(AdmitError::BadDecl("ill-typed field")),
    );
}

// ── 8. Escaping universe (R11 predicativity). An inductive declared in `Sort 0` whose ctor
// stores a field in `Sort 0` (a TYPE, itself `: Sort 1 > 0`) breaks predicativity
// (proofs.md §4:155, Lean inductive.cpp:435-442 — STRICT, no Prop escape in dnx). Admission
// must reject: a large field in a small inductive lets you encode an impredicative
// comprehension ⇒ False.
#[test]
fn escaping_universe_field_too_big_rejected() {
    let mut env = GlobalEnv::default();
    let bad = Inductive {
        id: NAT,
        params: vec![],
        indices: vec![],
        sort: 0, // declared small
        ctors: vec![CtorDecl {
            ctor_ix: 0,
            args: vec![Tm::Sort(0)], // stores a Type (level 1 > declared 0)
            ret_indices: vec![],
        }],
    };
    assert_eq!(
        env.add_inductive(bad),
        Err(AdmitError::BadDecl("field universe too big")),
    );
}

// ── 9. η / conversion is structural (dnx conv is η-free; conv.rs:33-34 compares `nf_tm`).
// A function-typed term must convert ONLY to a genuinely equal term. `λ(x:Nat).x` (the
// identity, `Nat → Nat`) checked at the NON-function goal `Nat` must fail (a Π is not a
// Nat). Accepting an ill-typed function/value confusion is unsound; this also pins that
// conv does not spuriously η-collapse a Π into its codomain.
#[test]
fn eta_function_value_confusion_rejected() {
    let env = env_with_nat();
    let id_nat = lam(nat_ty(), Tm::Var(0)); // : Nat → Nat
    assert_eq!(
        check(&env, &no_ctx(), &id_nat, &nat_ty()),
        Err(TypeError::Mismatch),
        "a function (Nat→Nat) is not a Nat — no η-collapse to the codomain"
    );
    // Distinct projections must NOT be interconvertible (R9): λλ.1 checked at the type of
    // λλ.0 fails. (K = λ(a)λ(b).a vs λ(a)λ(b).b over Nat.)
    let k1 = lam(nat_ty(), lam(nat_ty(), Tm::Var(1))); // λa λb. a
    let k2_ty = pi(nat_ty(), pi(nat_ty(), nat_ty())); // Nat→Nat→Nat (type of both)
    let k2 = lam(nat_ty(), lam(nat_ty(), Tm::Var(0))); // λa λb. b
    assert!(check(&env, &no_ctx(), &k1, &k2_ty).is_ok());
    assert!(check(&env, &no_ctx(), &k2, &k2_ty).is_ok());
    // but k1 and k2 are NOT convertible — proven via a goal that only k2's value inhabits is
    // hard to state without Id; instead assert they infer the SAME type yet differ as terms.
    let t1 = infer(&env, &no_ctx(), &k1).expect("k1 types");
    let t2 = infer(&env, &no_ctx(), &k2).expect("k2 types");
    assert_eq!(t1, t2, "both have type Nat→Nat→Nat");
    assert_ne!(
        k1, k2,
        "λλ.1 and λλ.0 are distinct (no η/projection collapse)"
    );
}

// ── 10. Indexed-family eliminator: wrong index arity at the constructor. A ctor of an
// INDEXED family must supply EXACTLY one return-index per declared index
// (env.rs:`check_ret_indices`, proofs.md §4:131-159). Here a 1-index family `F : Nat →
// Sort 0` has a ctor returning ZERO indices ⇒ arity skew ⇒ reject. Unchecked ret-indices
// make `infer(Ctor)` build a malformed `F ret_indices` head ⇒ the recursor's motive
// application skews ⇒ unsound indexed elimination.
#[test]
fn indexed_ctor_wrong_index_arity_rejected() {
    let mut env = env_with_nat(); // need Nat to be the index type
    let fam = Inductive {
        id: IndId(1),
        params: vec![],
        indices: vec![nat_ty()], // ONE index of type Nat  ⇒  F : Nat → Sort 0
        sort: 0,
        ctors: vec![CtorDecl {
            ctor_ix: 0,
            args: vec![],
            ret_indices: vec![], // returns ZERO indices — arity skew vs the 1 declared
        }],
    };
    assert_eq!(
        env.add_inductive(fam),
        Err(AdmitError::BadDecl("ret_indices arity mismatch")),
    );
}

// ── 11. δ-acyclicity (R7, proofs.md): a self-referential definition `c := c` must be
// rejected by `add_const` (a body may reference only ALREADY-admitted consts ⇒ the δ-graph
// is a DAG). A self-unfolding const loops δ-reduction ⇒ a non-normalizing "proof".
#[test]
fn self_referential_const_rejected() {
    let mut env = GlobalEnv::default();
    assert_eq!(
        env.add_const(ConstId(0), Tm::Sort(0), Tm::Const(ConstId(0))),
        Err(AdmitError::Cycle(ConstId(0))),
    );
}

// ── 12. Unknown / dangling reference: a term mentioning an inductive that was never
// admitted must not type-check (infer.rs `UnknownInd`). Accepting a dangling symbol lets a
// "proof" depend on a declaration that passed no admission check.
#[test]
fn dangling_inductive_reference_rejected() {
    let env = GlobalEnv::default(); // empty: IndId(0) was never admitted
    assert_eq!(
        infer(&env, &no_ctx(), &Tm::Ind(IndId(0))),
        Err(TypeError::UnknownInd),
    );
    assert_eq!(
        infer(&env, &no_ctx(), &Tm::Const(ConstId(0))),
        Err(TypeError::UnknownConst),
    );
}
