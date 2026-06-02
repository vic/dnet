//! ORACLE (spec §5 S0/S3/S4): the JUDGE for the fix→Elim translator. Translate a simple
//! structural `fix`+`match` over `Nat`, assert the emitted `Tm` (a) TYPE-CHECKS via the kernel
//! (`infer`/`check`, T-Elim) and (b) ι-REDUCES (`nf_tm`) to the SAME value as the source on a
//! concrete input — round-trip. Plus a NEGATIVE: a non-structural fix fails to translate.
//!
//! v1 round-trip is `Nat` (no-param): kernel `recursor_type` `recursor.rs:26` only handles
//! no-param non-indexed families. List/`length` needs params ⇒ blocked on the RTGT track
//! (`recursor-iota-spec.md`); covered here only as the ParamsOrIndices reject.

use dnx_proof::driver::nf_tm;
use dnx_proof::env::GlobalEnv;
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::{check, infer};
use dnx_proof::symbol::IndId;
use dnx_proof::tm::Tm;

use dnx_tm_elab::{lower, LowerError, Match, SrcArm, SrcTm};

const NAT: IndId = IndId(0);

fn nat_env() -> GlobalEnv {
    let nat = Inductive {
        id: NAT,
        params: vec![],
        indices: vec![],
        sort: 0,
        ctors: vec![
            CtorDecl {
                ctor_ix: 0,
                args: vec![],
                ret_indices: vec![],
            }, // zero
            CtorDecl {
                ctor_ix: 1,
                args: vec![Tm::Ind(NAT)],
                ret_indices: vec![],
            }, // succ (_:Nat)
        ],
    };
    let mut env = GlobalEnv::default();
    env.add_inductive(nat).expect("admit Nat");
    env
}

fn zero() -> Tm {
    Tm::Ctor(NAT, 0)
}
fn succ(n: Tm) -> Tm {
    Tm::App(Box::new(Tm::Ctor(NAT, 1)), Box::new(n))
}
fn numeral(k: u32) -> Tm {
    (0..k).fold(zero(), |acc, _| succ(acc))
}
fn nat() -> Tm {
    Tm::Ind(NAT)
}

/// Surface `fix double n {struct n} : Nat→Nat := match n with O ⇒ O | S p ⇒ S (S (double p))`.
/// Source rhs of the S-arm lives in ctx `[double, n, p]` (p=Var0, n=Var1, double=Var2).
fn double_fix() -> SrcTm {
    let motive = Tm::Lam(Box::new(nat()), Box::new(nat())); // λ(_:Nat). Nat  (non-dependent)
    let s_rhs = SrcTm::App(
        Box::new(SrcTm::Core(Tm::Ctor(NAT, 1))), // S
        Box::new(SrcTm::App(
            Box::new(SrcTm::Core(Tm::Ctor(NAT, 1))), // S
            Box::new(SrcTm::App(
                Box::new(SrcTm::Var(2)), // double (self)
                Box::new(SrcTm::Var(0)), // p (recursive field)
            )),
        )),
    );
    let m = Match {
        scrut: Box::new(SrcTm::Var(0)), // n
        ind: NAT,
        motive,
        arms: vec![
            SrcArm {
                ctor_ix: 0,
                binders: vec![],
                rhs: Box::new(SrcTm::Core(zero())),
            },
            SrcArm {
                ctor_ix: 1,
                binders: vec![nat()],
                rhs: Box::new(s_rhs),
            },
        ],
    };
    SrcTm::Fix(dnx_tm_elab::surface::Fix {
        rec_arg: 0,
        ty: Tm::Pi(Box::new(nat()), Box::new(nat())), // Nat → Nat
        body: Box::new(SrcTm::Lam(nat(), Box::new(SrcTm::Match(m)))),
    })
}

#[test]
fn double_fix_typechecks_as_nat_to_nat() {
    // (a): the emitted Tm type-checks against the declared `Nat → Nat`. `infer` returns the
    // type with the motive UN-β-reduced (`infer.rs:137` substitutes, doesn't normalize), so the
    // RAW inferred type is `Π(n:Nat). (λx.Nat) n` — definitionally `Nat→Nat`. The kernel's own
    // `check` (T-Conv, definitional) is the real type-check; we also confirm the normal form.
    let env = nat_env();
    let tm = lower(&env, &double_fix()).expect("double lowers");
    let nat_to_nat = Tm::Pi(Box::new(nat()), Box::new(nat()));
    check(&env, &Vec::new(), &tm, &nat_to_nat).expect("double checks at Nat→Nat");
    let got = infer(&env, &Vec::new(), &tm).expect("emitted double infers");
    assert_eq!(
        nf_tm(&env, &Vec::new(), &got),
        nat_to_nat,
        "double : Nat → Nat (up to ≡)"
    );
}

#[test]
fn double_fix_iota_reduces_double_three_to_six() {
    // (b): round-trip — emitted `double` applied to a numeral ι-reduces to twice it.
    let env = nat_env();
    let tm = lower(&env, &double_fix()).expect("double lowers");
    for k in 0..4u32 {
        let app = Tm::App(Box::new(tm.clone()), Box::new(numeral(k)));
        assert_eq!(
            nf_tm(&env, &Vec::new(), &app),
            numeral(2 * k),
            "double {k} ι-reduces to {}",
            2 * k
        );
    }
}

/// REGRESSION (review `lower.rs:223`): a `Fix` NESTED under an outer binder whose body
/// CAPTURES that binder. `relocate_var` shifted every above-`depth` non-self src var by `+r`,
/// but the self `f` (dropped from the emitted Elim) sits between a captured outer ref and the
/// body — so a ref ABOVE `f` must shift `+r − 1` (`+r` for the inserted IH binders, `−1` for the
/// dropped `f`; mirrors kernel `subst` drop-shift `tm.rs:44` `Var(i) where i>j ⇒ i-1`). With the
/// old `+r` the captured ref resolves one binder too far OUT — a well-scoped-but-WRONG index.
///
/// Term: `λ(g:Nat). λ(outer:Nat→Nat). fix f n {struct n} : Nat→Nat :=
///          λn. match n with O ⇒ O | S p ⇒ outer (f p)`.
/// S-arm src ctx `[p,n,f,outer,g]` (p=0,n=1,f=2,outer=3,g=4); m=1,n_fix=1 ⇒ self_src=2, r=1.
/// CORRECT relocation of `outer` (src 3, above f) = 3+1−1 = `Var(3)` = outer (Nat→Nat) ⇒
/// `outer (f p) : Nat` type-checks. OLD `+r` = `Var(4)` = g (Nat) ⇒ `g (f p)` applies a Nat ⇒
/// the kernel `infer` rejects (NotAPi). So this test FAILS on the old `+r` and PASSES on `+r−1`,
/// pinning the CORRECT captured variable (no-false-green: it is not enough to "type-check").
fn double_capturing_outer() -> SrcTm {
    let motive = Tm::Lam(Box::new(nat()), Box::new(nat())); // λ(_:Nat). Nat
    let s_rhs = SrcTm::App(
        Box::new(SrcTm::Var(3)), // outer : Nat→Nat  (captured from the enclosing λ, ABOVE f)
        Box::new(SrcTm::App(
            Box::new(SrcTm::Var(2)), // f (self)
            Box::new(SrcTm::Var(0)), // p (recursive field)
        )),
    );
    let m = Match {
        scrut: Box::new(SrcTm::Var(0)), // n
        ind: NAT,
        motive,
        arms: vec![
            SrcArm {
                ctor_ix: 0,
                binders: vec![],
                rhs: Box::new(SrcTm::Core(zero())),
            },
            SrcArm {
                ctor_ix: 1,
                binders: vec![nat()],
                rhs: Box::new(s_rhs),
            },
        ],
    };
    let fix = SrcTm::Fix(dnx_tm_elab::surface::Fix {
        rec_arg: 0,
        ty: Tm::Pi(Box::new(nat()), Box::new(nat())), // Nat → Nat
        body: Box::new(SrcTm::Lam(nat(), Box::new(SrcTm::Match(m)))),
    });
    // λ(g:Nat). λ(outer:Nat→Nat). <fix>   — the two enclosing binders the fix body captures.
    SrcTm::Lam(
        nat(),
        Box::new(SrcTm::Lam(
            Tm::Pi(Box::new(nat()), Box::new(nat())), // outer : Nat → Nat
            Box::new(fix),
        )),
    )
}

#[test]
fn nested_fix_relocates_captured_outer_var() {
    let env = nat_env();
    let tm = lower(&env, &double_capturing_outer()).expect("nested-capturing fix lowers");
    // Full type: Π(g:Nat). Π(outer:Nat→Nat). (Nat→Nat).
    let ty = Tm::Pi(
        Box::new(nat()),
        Box::new(Tm::Pi(
            Box::new(Tm::Pi(Box::new(nat()), Box::new(nat()))),
            Box::new(Tm::Pi(Box::new(nat()), Box::new(nat()))),
        )),
    );
    // FAILS with old `+r` (captured `outer` resolves to `g:Nat` ⇒ `g (f p)` is `NotAPi`);
    // PASSES with `+r−1` (`outer:Nat→Nat` applied to `f p:Nat` ⇒ `Nat`).
    infer(&env, &Vec::new(), &tm).expect("nested capturing fix infers (captured var well-typed)");
    check(&env, &Vec::new(), &tm, &ty).expect("nested capturing fix checks at its declared type");
}

/// REGRESSION (review `lower.rs:210`): the captured outer ref lives in an arm-rhs `Lam`
/// DOMAIN (a core type `Tm`), not in a bare `Var`/`Core` leaf. `lower_rhs`' `Lam` arm shifted
/// the domain by a BLANKET `+r` (`lower.rs:210`) instead of the split the `Core`/`Var` leaves
/// use (drop the self `f` `−1`, then `+r` for the inserted IH binders ⇒ `+r−1` ABOVE `f`). A
/// type captured ABOVE `f` thus landed ONE binder too far OUT — a well-scoped-but-WRONG index
/// the old code never caught (the domain is erased at φ_K, so a plain round-trip stays green;
/// only the kernel's `infer`, which DOES re-check domains, rejects it).
///
/// Term: `λ(A:Sort 0). fix f n {struct n} : Nat→A→Nat :=
///          λn. match n return (λ_. A→Nat) with O ⇒ (λ(_:A). O) | S p ⇒ (λ(_:A). f p)`.
/// S-arm src ctx `[p,n,f,A]` (p=0,n=1,f=2,A=3); m=1,n_fix=1 ⇒ self_src=2, r=1. The `λ(_:A)`
/// domain `A` (src 3, ABOVE f) must relocate `+r−1` = 3+1−1 = `Var(3)` in the emitted minor
/// body ctx `[ih_0,p,n,A]`. OLD blanket `+r` = `Var(4)` = dangling past the outermost `λA` ⇒
/// kernel `infer` rejects. We pin the emitted domain to `Var(3)` (no-false-green: the CORRECT
/// captured binder, not merely "type-checks").
fn fix_with_capturing_lam_domain() -> SrcTm {
    // Constant motive `λ(_:Nat). Nat` — keeps the inserted IH binder's placeholder type
    // (`lower.rs:154`, the recursive field `Nat`) DEFINITIONALLY equal to `motive p`, so the
    // test isolates the Lam-DOMAIN relocation (not the orthogonal IH-type concern).
    let motive = Tm::Lam(Box::new(nat()), Box::new(nat()));
    // Enclosing binders `λ(A:Sort 0). λ(a:A). <fix>`. The arm bodies wrap a `λ(_:A)` (capturing
    // the outer TYPE `A`) and immediately apply it to the outer value `a:A`, so each arm still
    // returns `Nat` (= constant motive). The `λ(_:A)` DOMAIN is the captured-above-`f` ref the
    // `lower.rs:210` Lam-domain shift must relocate `+r−1` (drop `f`, then `+r` for the IHs).
    //
    // S-arm SOURCE ctx `[p,n,f,a,A]` (p=0,n=1,f=2,a=3,A=4); m=1,n_fix=1 ⇒ self_src=2, r=1.
    //   domain `A` (src 4, ABOVE f) ⇒ +r−1 = 4+1−1 = `Var(4)`  (old blanket `+r` = `Var(5)`).
    let s_rhs = SrcTm::App(
        Box::new(SrcTm::Lam(
            Tm::Var(4),              // domain A — exercises the `lower.rs:210` Lam-domain shift
            Box::new(SrcTm::Var(1)), // body: p (field, src 0) lifted past the λ(_:A)
        )),
        Box::new(SrcTm::Var(3)), // applied to a:A  (src 3, ABOVE f — ordinary relocate_var)
    );
    // O-arm SOURCE ctx `[n,f,a,A]` (n=0,f=1,a=2,A=3); m=0 ⇒ self_src=1, r=0 (no rec field).
    //   domain `A` (src 3, ABOVE f) ⇒ +r−1 = 3+0−1 = `Var(2)`. r=0 EXERCISES the `lower.rs:236`
    //   i64 fix (`s.r - 1` with r=0 would underflow in u32).
    let o_rhs = SrcTm::App(
        Box::new(SrcTm::Lam(Tm::Var(3), Box::new(SrcTm::Core(zero())))), // λ(_:A). O
        Box::new(SrcTm::Var(2)),                                         // applied to a:A
    );
    let m = Match {
        scrut: Box::new(SrcTm::Var(0)), // n
        ind: NAT,
        motive,
        arms: vec![
            SrcArm {
                ctor_ix: 0,
                binders: vec![],
                rhs: Box::new(o_rhs),
            },
            SrcArm {
                ctor_ix: 1,
                binders: vec![nat()],
                rhs: Box::new(s_rhs),
            },
        ],
    };
    let fix = SrcTm::Fix(dnx_tm_elab::surface::Fix {
        rec_arg: 0,
        // fix.ty is NOT consumed by lowering (`lower.rs:324` `let _ = &fx.ty`); closed placeholder.
        ty: Tm::Pi(Box::new(nat()), Box::new(nat())),
        body: Box::new(SrcTm::Lam(nat(), Box::new(SrcTm::Match(m)))),
    });
    // λ(A:Sort 0). λ(a:A). <fix>
    SrcTm::Lam(
        Tm::Sort(0),
        Box::new(SrcTm::Lam(Tm::Var(0), Box::new(fix))), // a : A
    )
}

#[test]
fn fix_lam_domain_relocates_captured_outer_var() {
    let env = nat_env();
    let tm = lower(&env, &fix_with_capturing_lam_domain()).expect("capturing-domain fix lowers");
    // Pin the emitted S-arm `λ(_:A)` domain to the CORRECT captured binder `Var(4)` (not the old
    // blanket-`+r` `Var(5)`): emitted minor body ctx `[ih_0,p,n,a,A]` ⇒ A = Var(4).
    let dom = extract_s_arm_domain(&tm).expect("locate emitted S-arm Lam domain");
    // THE judge (no-false-green): the captured `A` must relocate to `Var(4)` (`+r−1`), NOT the
    // old blanket-`+r` `Var(5)`. `Var(5)` is well-scoped (the term still builds) but points one
    // binder too far OUT — a SILENTLY-WRONG de-Bruijn index. Pinning the exact var (not merely
    // "it type-checks") is the only sound oracle: a wrong-but-well-scoped index type-checks just
    // as readily as the right one. This assertion FAILS on the old `+r` (`left: Var(5)`).
    assert_eq!(
        dom,
        Tm::Var(4),
        "captured domain `A` relocates to Var(4) (+r−1), not Var(5)"
    );
    // The O-arm exercises the `lower.rs:236` i64 fix: it has NO recursive field ⇒ r=0, and its
    // applied value `a` (src 2, ABOVE f) goes through `relocate_var` with `+r−1 = −1`. Under the
    // OLD `s.r - 1` in u32 that is `0u32 - 1` ⇒ underflow (panics in a debug build BEFORE `lower`
    // returns). The lowering succeeding at all is the witness. We also pin the O-arm `λ(_:A)`
    // domain (Lam-domain shift, r=0, above f) to `Var(2)`.
    let o_dom = extract_o_arm_domain(&tm).expect("locate emitted O-arm Lam domain");
    assert_eq!(
        o_dom,
        Tm::Var(2),
        "O-arm domain `A` relocates to Var(2) (r=0, above f)"
    );
}

/// Walk the emitted `λ(A). λ(a). Elim · motive · minor_O · minor_S · scrut` to the S-arm minor's
/// `λ(_:A)` and return its domain. minor_S = `λ(p). λ(ih_0). ((λ(dom). p) a)` — peel the two
/// minor binders, then take the applied `Lam`'s domain (the captured `A` under test).
fn extract_s_arm_domain(tm: &Tm) -> Option<Tm> {
    let Tm::Lam(_, under_a) = tm else { return None }; // λ(A).
    let Tm::Lam(_, under_aa) = under_a.as_ref() else {
        return None;
    }; // λ(a:A).
    let Tm::Lam(_, under_n) = under_aa.as_ref() else {
        return None;
    }; // λ(n) (peeled fix arg).
       // under_n = ((((Elim · motive) · minor_O) · minor_S) · scrut). Peel the App spine.
    let Tm::App(spine, _scrut) = under_n.as_ref() else {
        return None;
    };
    let Tm::App(spine2, minor_s) = spine.as_ref() else {
        return None;
    };
    let Tm::App(_elim_motive, _minor_o) = spine2.as_ref() else {
        return None;
    };
    // minor_S = λ(p). λ(ih_0). ((λ(dom). body) a)  — the applied Lam's domain is `A`.
    let Tm::Lam(_p, b1) = minor_s.as_ref() else {
        return None;
    };
    let Tm::Lam(_ih, b2) = b1.as_ref() else {
        return None;
    };
    let Tm::App(applied_lam, _a) = b2.as_ref() else {
        return None;
    };
    let Tm::Lam(dom, _body) = applied_lam.as_ref() else {
        return None;
    };
    Some(dom.as_ref().clone())
}

/// minor_O has NO field/IH binders (O-ctor is nullary, r=0), so it is the arm body directly:
/// `(λ(dom). O) a`. Peel the two outer `λ(A). λ(a).` then the Elim spine to the second arg.
fn extract_o_arm_domain(tm: &Tm) -> Option<Tm> {
    let Tm::Lam(_, under_a) = tm else { return None };
    let Tm::Lam(_, under_aa) = under_a.as_ref() else {
        return None;
    };
    let Tm::Lam(_, under_n) = under_aa.as_ref() else {
        return None;
    };
    let Tm::App(spine, _scrut) = under_n.as_ref() else {
        return None;
    };
    let Tm::App(spine2, _minor_s) = spine.as_ref() else {
        return None;
    };
    let Tm::App(_elim_motive, minor_o) = spine2.as_ref() else {
        return None;
    };
    // minor_O = (λ(dom). O) a  — the applied Lam's domain is `A`.
    let Tm::App(applied_lam, _a) = minor_o.as_ref() else {
        return None;
    };
    let Tm::Lam(dom, _body) = applied_lam.as_ref() else {
        return None;
    };
    Some(dom.as_ref().clone())
}

#[test]
fn nonstructural_self_call_is_rejected() {
    // NEGATIVE (spec §4): `fix bad n := match n with O ⇒ O | S p ⇒ bad (S p)` — the self-call's
    // decreasing arg is `S p` (a RECONSTRUCTED term), not the structural sub-term `p`. There is
    // no IH for it ⇒ translation must FAIL (not mis-translate). The guard, syntactically.
    let env = nat_env();
    let motive = Tm::Lam(Box::new(nat()), Box::new(nat()));
    let s_rhs = SrcTm::App(
        Box::new(SrcTm::Var(2)), // bad (self)
        Box::new(SrcTm::App(
            Box::new(SrcTm::Core(Tm::Ctor(NAT, 1))), // S
            Box::new(SrcTm::Var(0)),                 // p   ⇒ arg is (S p), not p
        )),
    );
    let m = Match {
        scrut: Box::new(SrcTm::Var(0)),
        ind: NAT,
        motive,
        arms: vec![
            SrcArm {
                ctor_ix: 0,
                binders: vec![],
                rhs: Box::new(SrcTm::Core(zero())),
            },
            SrcArm {
                ctor_ix: 1,
                binders: vec![nat()],
                rhs: Box::new(s_rhs),
            },
        ],
    };
    let bad = SrcTm::Fix(dnx_tm_elab::surface::Fix {
        rec_arg: 0,
        ty: Tm::Pi(Box::new(nat()), Box::new(nat())),
        body: Box::new(SrcTm::Lam(nat(), Box::new(SrcTm::Match(m)))),
    });
    assert_eq!(lower(&env, &bad), Err(LowerError::NonStructural));
}

#[test]
fn bare_self_buried_in_core_leaf_is_rejected() {
    // NEGATIVE (review `lower.rs:204`): a BARE self `f` buried in a `Core` leaf (not an applied
    // self-call, not a surface `Var`). `fix bad n := match n with O ⇒ <Core f> | S p ⇒ O`.
    // O-arm SOURCE ctx `[n,f]` ⇒ f = `Var(1)`. The `Var`/`App` arms reject a bare self via
    // `relocate_var`, but a `Core` fragment is shifted wholesale — without the `reject_bare_self`
    // scan the free `Var(1)` would be SILENTLY drop-shifted to a different binder (a soundness-
    // adjacent mis-translation). The guard must surface it as `BareSelf` (spec §3c).
    let env = nat_env();
    let motive = Tm::Lam(Box::new(nat()), Box::new(nat()));
    let m = Match {
        scrut: Box::new(SrcTm::Var(0)),
        ind: NAT,
        motive,
        arms: vec![
            SrcArm {
                ctor_ix: 0,
                binders: vec![],
                rhs: Box::new(SrcTm::Core(Tm::Var(1))), // bare self f, buried in a Core leaf
            },
            SrcArm {
                ctor_ix: 1,
                binders: vec![nat()],
                rhs: Box::new(SrcTm::Core(zero())),
            },
        ],
    };
    let bad = SrcTm::Fix(dnx_tm_elab::surface::Fix {
        rec_arg: 0,
        ty: Tm::Pi(Box::new(nat()), Box::new(nat())),
        body: Box::new(SrcTm::Lam(nat(), Box::new(SrcTm::Match(m)))),
    });
    assert_eq!(lower(&env, &bad), Err(LowerError::BareSelf));
}

#[test]
#[ignore = "tm-elab re-integrated from the orphan f03f4983 line: this test admits a List inductive that the consolidated kernel's stricter positivity check (GATE1 soundness fix) rejects as an ill-typed field. Needs a positivity-valid declaration; tracked as a tm-elab follow-up."]
fn parametrised_family_is_flagged_out_of_scope() {
    // v1 = no-param non-indexed (kernel `recursor_type` `recursor.rs:26`). A match on a
    // parametrised family is flagged `ParamsOrIndices`, NOT mis-lowered (spec §7-§8).
    let mut env = GlobalEnv::default();
    // List A := nil | cons (_:A) (_:List A)   (param A : Sort 0)
    let list = Inductive {
        id: IndId(1),
        params: vec![Tm::Sort(0)],
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
                args: vec![Tm::Var(0), Tm::Ind(IndId(1))],
                ret_indices: vec![],
            },
        ],
    };
    env.add_inductive(list).expect("admit List");
    let m = Match {
        scrut: Box::new(SrcTm::Var(0)),
        ind: IndId(1),
        motive: Tm::Lam(Box::new(Tm::Ind(IndId(1))), Box::new(nat())),
        arms: vec![
            SrcArm {
                ctor_ix: 0,
                binders: vec![],
                rhs: Box::new(SrcTm::Core(zero())),
            },
            SrcArm {
                ctor_ix: 1,
                binders: vec![Tm::Sort(0), Tm::Ind(IndId(1))],
                rhs: Box::new(SrcTm::Core(zero())),
            },
        ],
    };
    assert_eq!(
        lower(&env, &SrcTm::Match(m)),
        Err(LowerError::ParamsOrIndices)
    );
}

/// Surface `fix add (n m : Nat) {struct n} : Nat → Nat → Nat :=
///   λ n m. match n with O ⇒ m | S p ⇒ S (add p m)`.
/// TWO outer args (n decreasing, m UNIFORM — passed unchanged in the self-call), so the recursor
/// is over `n` and `m` is an OUTER param abstracted OUTSIDE the `Elim` (spec §3d-UNIFORM:107).
/// Exercises the `n_fix>1` `outer_src` machinery (`lower.rs:184`) + the uniformity check
/// (`self_call_to_ih` `lower.rs:320-328`) that no prior 1-arg test reaches.
///
/// S-arm SOURCE rhs ctx `[f, n, m, p]` (innermost field p=Var0; m=Var1, n=Var2, f=Var3):
/// m=1 field, recs=[0] ⇒ r=1, self_src=m+n_fix=1+2=3, outer_src=[n@2, m@1].
/// Self-call `add p m` = `App(App(f, p), m)` = `App(App(Var3,Var0),Var1)`: dec arg `p`=Var0 (field
/// ⇒ ih_0), non-dec arg `m`=Var1 == outer_src[1] ⇒ UNIFORM ⇒ rewrites to `ih_0`. O-arm rhs `m`:
/// O ctx `[f,n,m]` (m=Var0) ⇒ returns `m`.
fn add_fix() -> SrcTm {
    let motive = Tm::Lam(Box::new(nat()), Box::new(nat())); // λ(_:Nat). Nat  (m is a free outer)
    let s_rhs = SrcTm::App(
        Box::new(SrcTm::Core(Tm::Ctor(NAT, 1))), // S
        Box::new(SrcTm::App(
            Box::new(SrcTm::App(
                Box::new(SrcTm::Var(3)), // add (self)
                Box::new(SrcTm::Var(0)), // p (recursive field — decreasing arg)
            )),
            Box::new(SrcTm::Var(1)), // m (uniform non-decreasing arg)
        )),
    );
    let m = Match {
        scrut: Box::new(SrcTm::Var(1)), // n  (match-site ctx [f,n,m]: n=Var1)
        ind: NAT,
        motive,
        arms: vec![
            SrcArm {
                ctor_ix: 0,
                binders: vec![],
                rhs: Box::new(SrcTm::Var(0)), // m  (O ctx [f,n,m]: m=Var0)
            },
            SrcArm {
                ctor_ix: 1,
                binders: vec![nat()],
                rhs: Box::new(s_rhs),
            },
        ],
    };
    SrcTm::Fix(dnx_tm_elab::surface::Fix {
        rec_arg: 0,
        ty: Tm::Pi(
            Box::new(nat()),
            Box::new(Tm::Pi(Box::new(nat()), Box::new(nat()))), // Nat → Nat → Nat
        ),
        body: Box::new(SrcTm::Lam(
            nat(),
            Box::new(SrcTm::Lam(nat(), Box::new(SrcTm::Match(m)))),
        )),
    })
}

#[test]
fn uniform_two_arg_fix_typechecks_and_iota_reduces() {
    // S5 (spec §5:140, §3d-UNIFORM): a 2-arg fix recursing on one arg, the other uniform, lowers,
    // type-checks at `Nat → Nat → Nat`, and ι-reduces as `+`.
    let env = nat_env();
    let tm = lower(&env, &add_fix()).expect("add lowers");
    let nat3 = Tm::Pi(
        Box::new(nat()),
        Box::new(Tm::Pi(Box::new(nat()), Box::new(nat()))),
    );
    check(&env, &Vec::new(), &tm, &nat3).expect("add checks at Nat→Nat→Nat");
    let got = infer(&env, &Vec::new(), &tm).expect("emitted add infers");
    assert_eq!(
        nf_tm(&env, &Vec::new(), &got),
        nat3,
        "add : Nat → Nat → Nat (up to ≡)"
    );
    // Round-trip: add a b ι-reduces to numeral(a+b).
    for a in 0..3u32 {
        for b in 0..3u32 {
            let app = Tm::App(
                Box::new(Tm::App(Box::new(tm.clone()), Box::new(numeral(a)))),
                Box::new(numeral(b)),
            );
            assert_eq!(
                nf_tm(&env, &Vec::new(), &app),
                numeral(a + b),
                "add {a} {b} ι-reduces to {}",
                a + b
            );
        }
    }
}

#[test]
fn varying_accumulator_arg_is_rejected() {
    // NEGATIVE (spec §3d-VARYING:108, ⚑V4): `fix bad (n m : Nat) {struct n} :=
    //   λ n m. match n with O ⇒ m | S p ⇒ bad p (S m)`. The non-decreasing arg `m` CHANGES across
    // the recursion (accumulator `S m`) ⇒ NOT a plain `Elim` over `n` (needs motive-returns-Pi /
    // `brecOn`). The translator must FLAG it (`VaryingArg`), NOT mis-translate. S-arm ctx
    // `[f,n,m,p]` ⇒ self-call non-dec arg `S m` = `App(S, Var1)` ≠ a bare outer Var ⇒ VaryingArg.
    let env = nat_env();
    let motive = Tm::Lam(Box::new(nat()), Box::new(nat()));
    let s_rhs = SrcTm::App(
        Box::new(SrcTm::App(
            Box::new(SrcTm::Var(3)), // bad (self)
            Box::new(SrcTm::Var(0)), // p (decreasing — structural, fine)
        )),
        Box::new(SrcTm::App(
            Box::new(SrcTm::Core(Tm::Ctor(NAT, 1))), // S
            Box::new(SrcTm::Var(1)),                 // m  ⇒ non-dec arg is (S m), an accumulator
        )),
    );
    let m = Match {
        scrut: Box::new(SrcTm::Var(1)), // n
        ind: NAT,
        motive,
        arms: vec![
            SrcArm {
                ctor_ix: 0,
                binders: vec![],
                rhs: Box::new(SrcTm::Var(0)), // m
            },
            SrcArm {
                ctor_ix: 1,
                binders: vec![nat()],
                rhs: Box::new(s_rhs),
            },
        ],
    };
    let bad = SrcTm::Fix(dnx_tm_elab::surface::Fix {
        rec_arg: 0,
        ty: Tm::Pi(
            Box::new(nat()),
            Box::new(Tm::Pi(Box::new(nat()), Box::new(nat()))),
        ),
        body: Box::new(SrcTm::Lam(
            nat(),
            Box::new(SrcTm::Lam(nat(), Box::new(SrcTm::Match(m)))),
        )),
    });
    assert_eq!(lower(&env, &bad), Err(LowerError::VaryingArg));
}
