//! Levitation `Desc₀` prototype — a universe of CODES for (a slice of) inductive shapes,
//! a single generic `decode`/`El₀ : Desc₀ → Type → Type → Type` realized by the EXISTING
//! recursor (`Elim Desc₀`, large-elim A5 — soundness.rs:275) + the EXISTING ι rule
//! (`try_iota` — driver.rs:62), and the pattern functors of Nat and List encoded as `Desc₀`
//! VALUES whose decode ι-reduces to the expected polynomial.
//!
//! SCOPE (the achievable Slice 0 of the Gentle Art of Levitation, Chapman/Dagand/McBride/
//! Morris ICFP 2010; see vic/plans/levitation-prototype.md §3 SLICE 0). This is a CLOSED
//! code-enum with a TYPE-valued generic interpreter — "levitation in spirit": ONE `El₀`
//! definition computes the payload Type for EVERY code, via one ι rule. It DELIBERATELY has
//!   - NO `'σ`/`'π` storing an arbitrary `Set` (that field would be `Sort 1 > Sort 0` ⇒ R11
//!     forces `Desc : Type₁`, then the self-`iso` needs `Lift`/level-poly we lack — GAP A);
//!   - NO `μ` fixpoint tying codes to a recursive datatype (needs W-types / induction-recursion
//!     — GAP B); the recursive datatype here is the kernel's NATIVE inductive, and `El₀`
//!     computes its one-step pattern functor.
//!
//! So this is the levitation FLAVOUR at toy scale, on admitted machinery only (no kernel change,
//! no soundness impact). The faithful self-describing `Desc ≅ μ DescD` stays 🔭 (levitation-gap.md).
//!
//! `Desc₀ : Type₀` (all codes nullary or recursive-in-`Desc₀` ⇒ no field exceeds `Sort 0`, R11
//! OK — soundness.rs:636; non-indexed ⇒ ι fires via the `nidx==0` fast-path driver.rs:110):
//!   d_one  : Desc₀                    -- '1'  unit shape
//!   d_X    : Desc₀                    -- 'X'  the recursive carrier slot
//!   d_A    : Desc₀                    -- 'A'  a fixed parameter slot (List's element type)
//!   d_prod : Desc₀ → Desc₀ → Desc₀    -- '×'  product of two shapes  (recursive fields, +pos)
//!   d_sum  : Desc₀ → Desc₀ → Desc₀    -- '+'  choice                  (recursive fields, +pos)
//!
//! decode (`El₀ d A X`), large-elim with motive `λ_:Desc₀. Type→Type→Type` (A5):
//!   El₀ d_one        A X = Unit            El₀ d_A          A X = A
//!   El₀ d_X          A X = X               El₀ (d_prod a b) A X = Prod (El₀ a A X) (El₀ b A X)
//!                                          El₀ (d_sum  a b) A X = Sum  (El₀ a A X) (El₀ b A X)
//!
//! Pattern functors as codes:  NatF := d_sum d_one d_X            ⟦NatF⟧  A X = 1 + X
//!                             ListF := d_sum d_one (d_prod d_A d_X) ⟦ListF⟧ A X = 1 + A×X

use dnx_proof::driver::nf_tm;
use dnx_proof::env::GlobalEnv;
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::{check, infer};
use dnx_proof::symbol::IndId;
use dnx_proof::tm::Tm;

// ── term helpers (same idiom as eq_prelude.rs:17-29) ──
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
const UNIT: IndId = IndId(1);
const PROD: IndId = IndId(2);
const SUM: IndId = IndId(3);
const DESC: IndId = IndId(4);

// ── the support inductives (all admit at Type₀; the Σ/× mould = Corr.1, eq_prelude.rs:49) ──

// Nat := zero | succ Nat   (the native recursive datatype whose pattern functor `1 + X` we decode).
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

// Unit := tt   (0-field inductive — the '1' payload).
fn unit() -> Inductive {
    Inductive {
        id: UNIT,
        params: vec![],
        indices: vec![],
        sort: 0,
        ctors: vec![CtorDecl {
            ctor_ix: 0,
            args: vec![],
            ret_indices: vec![],
        }],
    }
}

// Prod (A B : Type₀) := pair : A → B → Prod A B   (the non-dependent × ; params [A,B]).
fn prod() -> Inductive {
    Inductive {
        id: PROD,
        params: vec![Tm::Sort(0), Tm::Sort(0)], // A:Type₀ ; B:Type₀
        indices: vec![],
        sort: 0,
        // field 0 (type A): ctx [A,B] ⇒ A=Var1. field 1 (type B): ctx [A,B,f0] ⇒ B=Var1
        // (the param B shifts +1 past the pushed first field — cf. Vec cons, soundness.rs:307).
        ctors: vec![CtorDecl {
            ctor_ix: 0,
            args: vec![Tm::Var(1), Tm::Var(1)],
            ret_indices: vec![],
        }],
    }
}

// Sum (A B : Type₀) := inl : A → Sum A B | inr : B → Sum A B   (the choice payload; params [A,B]).
fn sum() -> Inductive {
    Inductive {
        id: SUM,
        params: vec![Tm::Sort(0), Tm::Sort(0)],
        indices: vec![],
        sort: 0,
        ctors: vec![
            CtorDecl {
                ctor_ix: 0,
                args: vec![Tm::Var(1)],
                ret_indices: vec![],
            }, // inl : A → Sum A B
            CtorDecl {
                ctor_ix: 1,
                args: vec![Tm::Var(0)],
                ret_indices: vec![],
            }, // inr : B → Sum A B
        ],
    }
}

// Desc₀ — the universe of codes (5 ctors; d_prod/d_sum recursive ⇒ strictly positive, Type₀).
fn desc0() -> Inductive {
    Inductive {
        id: DESC,
        params: vec![],
        indices: vec![],
        sort: 0,
        ctors: vec![
            CtorDecl {
                ctor_ix: 0,
                args: vec![],
                ret_indices: vec![],
            }, // d_one
            CtorDecl {
                ctor_ix: 1,
                args: vec![],
                ret_indices: vec![],
            }, // d_X
            CtorDecl {
                ctor_ix: 2,
                args: vec![],
                ret_indices: vec![],
            }, // d_A
            CtorDecl {
                ctor_ix: 3, // d_prod : Desc₀ → Desc₀ → Desc₀
                args: vec![Tm::Ind(DESC), Tm::Ind(DESC)],
                ret_indices: vec![],
            },
            CtorDecl {
                ctor_ix: 4, // d_sum : Desc₀ → Desc₀ → Desc₀
                args: vec![Tm::Ind(DESC), Tm::Ind(DESC)],
                ret_indices: vec![],
            },
        ],
    }
}

fn desc_env() -> GlobalEnv {
    let mut e = GlobalEnv::default();
    e.add_inductive(nat()).expect("Nat admits");
    e.add_inductive(unit()).expect("Unit admits");
    e.add_inductive(prod()).expect("Prod admits (× mould)");
    e.add_inductive(sum()).expect("Sum admits");
    e.add_inductive(desc0())
        .expect("Desc₀ admits (Type₀, strictly positive)");
    e
}

// ── code builders ──
fn d_one() -> Tm {
    Tm::Ctor(DESC, 0)
}
fn d_x() -> Tm {
    Tm::Ctor(DESC, 1)
}
fn d_a() -> Tm {
    Tm::Ctor(DESC, 2)
}
fn d_prod(a: Tm, b: Tm) -> Tm {
    apps(Tm::Ctor(DESC, 3), &[a, b])
}
fn d_sum(a: Tm, b: Tm) -> Tm {
    apps(Tm::Ctor(DESC, 4), &[a, b])
}

/// The type-former `Type → Type → Type` = `Π(_:Type₀)(_:Type₀). Type₀`  (: `Sort 1`).
fn tyformer() -> Tm {
    pi(Tm::Sort(0), pi(Tm::Sort(0), Tm::Sort(0)))
}

/// `El₀` = the single generic decoder, realized by `Elim Desc₀` (one large-elim, one ι rule).
/// `El₀ d A X` decodes code `d` against parameter type `A` and recursive carrier `X`.
///
/// motive = `λ_:Desc₀. Type→Type→Type` (ignores the code; large-elim into Sort 1, A5).
/// Each minor binds the ctor fields then the IHs (recursor.rs:73 field-then-ih order), then `A X`:
///   minor_one  = λA λX. Unit                 minor_A    = λA λX. A
///   minor_X    = λA λX. X
///   minor_prod = λa λb λiha λihb λA λX. Prod (iha A X) (ihb A X)   -- iha=Var3 ihb=Var2 A=Var1 X=Var0
///   minor_sum  = λa λb λiha λihb λA λX. Sum  (iha A X) (ihb A X)
fn el0() -> Tm {
    let motive = lam(Tm::Ind(DESC), tyformer());
    let minor_one = lam(Tm::Sort(0), lam(Tm::Sort(0), Tm::Ind(UNIT)));
    let minor_x = lam(Tm::Sort(0), lam(Tm::Sort(0), Tm::Var(0))); // X
    let minor_a = lam(Tm::Sort(0), lam(Tm::Sort(0), Tm::Var(1))); // A
                                                                  // body under [a,b,iha,ihb,A,X]: iha=Var3, ihb=Var2, A=Var1, X=Var0.
    let bin_body = |ind: IndId| {
        let iha_ax = app(app(Tm::Var(3), Tm::Var(1)), Tm::Var(0));
        let ihb_ax = app(app(Tm::Var(2), Tm::Var(1)), Tm::Var(0));
        apps(Tm::Ind(ind), &[iha_ax, ihb_ax])
    };
    let bin_minor = |ind: IndId| {
        lam(
            Tm::Ind(DESC), // a
            lam(
                Tm::Ind(DESC), // b
                lam(
                    tyformer(), // iha : Type→Type→Type
                    lam(
                        tyformer(), // ihb : Type→Type→Type
                        lam(Tm::Sort(0), lam(Tm::Sort(0), bin_body(ind))),
                    ),
                ),
            ),
        )
    };
    apps(
        Tm::Elim(DESC),
        &[
            motive,
            minor_one,
            minor_x,
            minor_a,
            bin_minor(PROD),
            bin_minor(SUM),
        ],
    )
}

/// `El₀ d A X` fully applied.
fn el0_at(d: Tm, a: Tm, x: Tm) -> Tm {
    apps(el0(), &[d, a, x])
}

// ── tests ──

#[test]
fn desc0_universe_and_supports_admit_at_type0() {
    // The whole levitation slice lives in Type₀ on admitted machinery (no kernel change).
    let env = desc_env();
    for id in [NAT, UNIT, PROD, SUM, DESC] {
        assert!(env.inds.contains_key(&id), "{id:?} admitted");
        assert!(env.recursors.contains_key(&id), "{id:?} has a recursor");
    }
    // Desc₀ : Type₀  (the universe of codes is small — it stores no `Set`, so no R11 lift).
    assert_eq!(
        infer(&env, &Vec::new(), &Tm::Ind(DESC)).unwrap(),
        Tm::Sort(0),
        "Desc₀ : Type₀ (GAP A dodged by construction — no `'σ` Set-field)"
    );
}

#[test]
fn el0_typechecks_as_decode() {
    // El₀ : Desc₀ → Type → Type → Type  — the generic decoder typechecks (large elim, A5).
    let env = desc_env();
    let want = pi(Tm::Ind(DESC), pi(Tm::Sort(0), pi(Tm::Sort(0), Tm::Sort(0))));
    let got = infer(&env, &Vec::new(), &el0()).expect("El₀ (Elim Desc₀ …) typechecks");
    // `infer` returns the recursor result `Π(d). motive d` with the motive application un-reduced;
    // definitional equality (T-Conv) is the kernel's notion, so compare normal forms (the `check`
    // below is the actual T-Conv gate; this assert documents the decoder's type).
    assert_eq!(
        nf_tm(&env, &Vec::new(), &got),
        want,
        "El₀ : Desc₀ → Type → Type → Type (up to definitional equality)"
    );
    // and it checks AT that type via the real T-Conv path (β-normalizes the motive application).
    assert!(check(&env, &Vec::new(), &el0(), &want).is_ok());
}

#[test]
fn el0_base_codes_reduce() {
    // The three nullary codes decode by one ι step each (closed scrutinee — try_iota fires).
    let env = desc_env();
    let nat = || Tm::Ind(NAT);
    // El₀ d_one Nat Nat  ⟶  Unit
    assert_eq!(
        nf_tm(&env, &Vec::new(), &el0_at(d_one(), nat(), nat())),
        Tm::Ind(UNIT),
        "⟦'1'⟧ = Unit"
    );
    // El₀ d_X A X  ⟶  X   (use distinct A=Unit, X=Nat to prove it picks the carrier, not the param)
    assert_eq!(
        nf_tm(&env, &Vec::new(), &el0_at(d_x(), Tm::Ind(UNIT), nat())),
        nat(),
        "⟦'X'⟧ = X (the recursive carrier)"
    );
    // El₀ d_A A X  ⟶  A
    assert_eq!(
        nf_tm(&env, &Vec::new(), &el0_at(d_a(), Tm::Ind(UNIT), nat())),
        Tm::Ind(UNIT),
        "⟦'A'⟧ = A (the parameter slot)"
    );
}

#[test]
fn el0_nat_pattern_functor_computes() {
    // NatF := d_sum d_one d_X     ⟦NatF⟧ A X = Sum Unit X  =  1 + X  (Nat's pattern functor).
    // The TINY COMPUTATION: decode the code against the kernel's NATIVE Nat as carrier ⇒ the
    // one-step unfolding `Sum Unit Nat`. ONE `El₀` definition + one ι rule does the whole thing.
    let env = desc_env();
    let nat = || Tm::Ind(NAT);
    let nat_f = d_sum(d_one(), d_x());

    // typechecks at Type (the decoder is total over codes).
    assert_eq!(
        infer(&env, &Vec::new(), &el0_at(nat_f.clone(), nat(), nat())).unwrap(),
        Tm::Sort(0),
        "⟦NatF⟧ Nat Nat : Type₀"
    );

    // reduces to Sum Unit Nat = 1 + Nat.
    let want = apps(Tm::Ind(SUM), &[Tm::Ind(UNIT), nat()]);
    assert_eq!(
        nf_tm(&env, &Vec::new(), &el0_at(nat_f, nat(), nat())),
        want,
        "⟦NatF⟧ A Nat ι-reduces to `Sum Unit Nat` (1 + X with X := Nat) — Nat encoded via Desc"
    );
}

#[test]
fn el0_list_pattern_functor_computes() {
    // ListF := d_sum d_one (d_prod d_A d_X)   ⟦ListF⟧ A X = Sum Unit (Prod A X) = 1 + A×X.
    // Decode List-of-Nat's pattern functor with element A:=Nat, recursive carrier X:=Nat.
    // Exercises the IH threading on the NESTED d_prod (the recursor hands `iha,ihb` for the
    // product's children — the generic fold genuinely recurses).
    let env = desc_env();
    let nat = || Tm::Ind(NAT);
    let list_f = d_sum(d_one(), d_prod(d_a(), d_x()));

    assert_eq!(
        infer(&env, &Vec::new(), &el0_at(list_f.clone(), nat(), nat())).unwrap(),
        Tm::Sort(0),
        "⟦ListF⟧ Nat Nat : Type₀"
    );

    // Sum Unit (Prod Nat Nat) = 1 + Nat×Nat.
    let want = apps(
        Tm::Ind(SUM),
        &[Tm::Ind(UNIT), apps(Tm::Ind(PROD), &[nat(), nat()])],
    );
    assert_eq!(
        nf_tm(&env, &Vec::new(), &el0_at(list_f, nat(), nat())),
        want,
        "⟦ListF⟧ Nat Nat ι-reduces to `Sum Unit (Prod Nat Nat)` (1 + A×X) — List encoded via Desc"
    );
}

#[test]
fn el0_carrier_substitution_is_generic() {
    // Genericity check: the SAME ListF code, decoded at a DIFFERENT carrier, tracks the carrier.
    // ⟦ListF⟧ Nat Unit = Sum Unit (Prod Nat Unit)  (X flows to the right factor only).
    let env = desc_env();
    let list_f = d_sum(d_one(), d_prod(d_a(), d_x()));
    let want = apps(
        Tm::Ind(SUM),
        &[
            Tm::Ind(UNIT),
            apps(Tm::Ind(PROD), &[Tm::Ind(NAT), Tm::Ind(UNIT)]),
        ],
    );
    assert_eq!(
        nf_tm(
            &env,
            &Vec::new(),
            &el0_at(list_f, Tm::Ind(NAT), Tm::Ind(UNIT))
        ),
        want,
        "one El₀ definition decodes the same code at any carrier (A:=Nat, X:=Unit)"
    );
}

#[test]
fn el0_on_neutral_code_is_stuck() {
    // No-false-green: ι must NOT fire on an OPEN code (a free Var scrutinee) — R4 (driver.rs:76).
    // `El₀ (Var 0) A X` under a binder stays a neutral `Elim` application (does not invent a
    // reduction). This pins that the generic decoder reduces ONLY on closed codes (Slice-0 honesty).
    let env = desc_env();
    let open = lam(
        Tm::Ind(DESC),
        el0_at(Tm::Var(0), Tm::Ind(NAT), Tm::Ind(NAT)),
    );
    let nf = nf_tm(&env, &Vec::new(), &open);
    // the body must still contain an Elim DESC head (stuck), not a Sum/Prod/Unit.
    fn mentions_elim(t: &Tm, id: IndId) -> bool {
        match t {
            Tm::Elim(j) => *j == id,
            Tm::Pi(a, b) | Tm::Lam(a, b) | Tm::App(a, b) => {
                mentions_elim(a, id) || mentions_elim(b, id)
            }
            _ => false,
        }
    }
    assert!(
        mentions_elim(&nf, DESC),
        "ι is stuck on an open code (R4) — generic decode reduces on CLOSED codes only"
    );
}
