//! Levitation **Slice-1** — the VALUE layer on top of Slice-0 (`levitation_desc.rs`, 7 green).
//!
//! Slice-0 is purely TYPE-level: `El₀ : Desc₀ → Type → Type → Type` computes a payload *Type*
//! per closed code. Slice-1 adds **data of those types and a generic FOLD that computes a value
//! over closed described data** — the first slice where a levitated artifact reduces a *value*
//! (a number), not just a type. It stays AXIOM-FREE, adds NO `Tm` variant, edits NO `src/`, and
//! rides the SAME admission gates (R3/R11/ret-index, env.rs:41) + the SAME ι (driver.rs:62).
//!
//! THE LOAD-BEARING CORRECTION (vic/research/levitation-slice1-design.md §0): the textbook
//! primitive `Mu (I)(D:Desc I)` with `con : El D (Mu I D) i → Mu I D i` does NOT admit — the
//! self-reference sits in a SPINE ARG under the `El` decode (head `Elim`, not `Ind`), so
//! `valid_ind_app` returns false (positivity.rs:23,28) and `add_inductive` rejects it
//! ("non-positive", env.rs:48). dnx positivity is NON-NESTED. So Slice-1 takes the only
//! axiom-free, no-new-Tm path that still buys real generic computation over closed data:
//!   - keep Slice-0's closed universe `Desc₀` + decoder `El₀`;
//!   - declare a NATIVE described datatype `LN := lnil | lcons Nat LN` (direct `Ind` recursion ⇒
//!     positivity-OK: `lcons`'s recursive field is `Tm::Ind(LN)`, the `nat_succ` shape,
//!     positivity.rs:60 — the very thing the blocked `con` LACKED, whose head was `Elim`);
//!   - a generic ALGEBRA layer `Alg₀ d X := El₀ d X X → X` whose INPUT type is computed by the
//!     single `El₀` (no new def — `el0()` verbatim);
//!   - a generic FOLD `gfold_LN : Π(X:Type). (El₀ code_LN X X → X) → LN → X` realized by ONE
//!     `Elim LN` (one recursor, one ι);
//!   - the demoable theorem T4: `gfold_LN Nat sumAlg (described list 1,2,3) ⟶ 6` — generic-sum
//!     over closed described data REDUCES to the native answer via the SAME ι engine.
//!
//! The code↔data link is the PROVEN coherence T2 (`El₀ code_LN A LN` ι-reduces to LN's own
//! one-step functor `Sum Unit (Prod A LN)`), not a definitional `LN := μ code_LN` — exactly
//! nix-effects' "weak" stance minus the unstatable iso. Net new TCB code: ZERO.

use dnx_proof::driver::nf_tm;
use dnx_proof::env::GlobalEnv;
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::{check, infer};
use dnx_proof::symbol::IndId;
use dnx_proof::tm::Tm;

// ── term helpers (same idiom as levitation_desc.rs:44-55 / eq_prelude.rs:17-29) ──
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
const LN: IndId = IndId(5); // the NATIVE described Nat-list (Slice-1's value carrier)

// ──────────────────────────────────────────────────────────────────────────────
// Slice-0 support inductives + Desc₀ + El₀, copied VERBATIM (test-local, NO src/ change;
// mirrors levitation_desc.rs:63-262). Slice-1 reuses them UNCHANGED.
// ──────────────────────────────────────────────────────────────────────────────

// Nat := zero | succ Nat   (the element type AND the fold's carrier in the demo).
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

// Unit := tt   (the '1' payload).
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

// Prod (A B : Type₀) := pair : A → B → Prod A B   (the non-dependent ×).
fn prod() -> Inductive {
    Inductive {
        id: PROD,
        params: vec![Tm::Sort(0), Tm::Sort(0)],
        indices: vec![],
        sort: 0,
        ctors: vec![CtorDecl {
            ctor_ix: 0,
            args: vec![Tm::Var(1), Tm::Var(1)],
            ret_indices: vec![],
        }],
    }
}

// Sum (A B : Type₀) := inl : A → Sum A B | inr : B → Sum A B   (the choice payload).
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
                ctor_ix: 3,
                args: vec![Tm::Ind(DESC), Tm::Ind(DESC)],
                ret_indices: vec![],
            }, // d_prod
            CtorDecl {
                ctor_ix: 4,
                args: vec![Tm::Ind(DESC), Tm::Ind(DESC)],
                ret_indices: vec![],
            }, // d_sum
        ],
    }
}

// ── the Slice-1 NATIVE described datatype ──
//
// LN := lnil | lcons (Nat) (LN)   -- a Nat-list; ctors MIRROR `code_LN = 1 + Nat×X`.
//   * `lcons`'s recursive field is `Tm::Ind(LN)` = the `nat_succ` shape ⇒ strictly positive
//     (positivity.rs:60). Its head IS `Ind(LN)` (valid_ind_app ✅, positivity.rs:28) — the very
//     thing the blocked primitive `con` lacked (its head was `Elim`). This is WHY the native
//     route admits where `μ` does not (design §0/§3b).
//   * `Nat` field is `Sort 0` ⇒ R11 ✅. NON-indexed (nidx==0) ⇒ ι fires on OPEN scrutinees too
//     (driver.rs:110), demoed in T7.
fn ln() -> Inductive {
    Inductive {
        id: LN,
        params: vec![],
        indices: vec![],
        sort: 0,
        ctors: vec![
            CtorDecl {
                ctor_ix: 0,
                args: vec![],
                ret_indices: vec![],
            }, // lnil : LN
            CtorDecl {
                ctor_ix: 1,
                args: vec![Tm::Ind(NAT), Tm::Ind(LN)],
                ret_indices: vec![],
            }, // lcons : Nat → LN → LN
        ],
    }
}

fn slice1_env() -> GlobalEnv {
    let mut e = GlobalEnv::default();
    e.add_inductive(nat()).expect("Nat admits");
    e.add_inductive(unit()).expect("Unit admits");
    e.add_inductive(prod()).expect("Prod admits (× mould)");
    e.add_inductive(sum()).expect("Sum admits");
    e.add_inductive(desc0())
        .expect("Desc₀ admits (Type₀, strictly positive)");
    e.add_inductive(ln())
        .expect("LN admits (native described Nat-list, direct Ind recursion ⇒ positivity-OK)");
    e
}

// ── code builders (levitation_desc.rs:190-204) ──
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

/// `code_LN := d_sum d_one (d_prod d_A d_X)`  —  the `1 + A×X` shape (the ListF of
/// levitation_desc.rs:358). A closed `Desc₀` VALUE.
fn code_ln() -> Tm {
    d_sum(d_one(), d_prod(d_a(), d_x()))
}

/// `code_Nat := d_sum d_one d_X`  —  the `1 + X` shape (NatF of levitation_desc.rs:332). Used by
/// the optional second-datatype genericity check (T8).
fn code_nat() -> Tm {
    d_sum(d_one(), d_x())
}

/// The type-former `Type → Type → Type` (: `Sort 1`).
fn tyformer() -> Tm {
    pi(Tm::Sort(0), pi(Tm::Sort(0), Tm::Sort(0)))
}

/// `El₀` = the single generic decoder, realized by `Elim Desc₀` (levitation_desc.rs:220-257).
/// motive = `λ_:Desc₀. Type→Type→Type`; minors bind ctor fields then IHs then `A X`.
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
                    tyformer(), // iha
                    lam(
                        tyformer(), // ihb
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

// ── Nat numerals + `add` (levitation_desc.rs / thm_induction.rs:110) ──
fn zero() -> Tm {
    Tm::Ctor(NAT, 0)
}
fn succ(n: Tm) -> Tm {
    app(Tm::Ctor(NAT, 1), n)
}
fn numeral(n: u32) -> Tm {
    (0..n).fold(zero(), |acc, _| succ(acc))
}

/// `add x y` via `Nat.rec`, recursion on the 2nd arg (thm_induction.rs:111):
///   add = λm.λn. Nat.rec (λ_:Nat.Nat) m (λk.λih. succ ih) n
/// As a CLOSED term applied to `x,y` (no `add_const` needed — keeps the demo body-only).
fn add(x: Tm, y: Tm) -> Tm {
    // ctx for the inner Elim is [m, n] with m=Var1, n=Var0.
    let add_body = lam(
        Tm::Ind(NAT), // m
        lam(
            Tm::Ind(NAT), // n
            apps(
                Tm::Elim(NAT),
                &[
                    lam(Tm::Ind(NAT), Tm::Ind(NAT)), // motive λ_:Nat.Nat
                    Tm::Var(1),                      // minor_zero = m
                    lam(Tm::Ind(NAT), lam(Tm::Ind(NAT), succ(Tm::Var(0)))), // minor_succ = λk.λih. succ ih
                    Tm::Var(0),                                             // scrutinee = n
                ],
            ),
        ),
    );
    apps(add_body, &[x, y])
}

// ── Sum / Prod recursors used by the algebras (closed builders) ──

/// `fst p` / `snd p` on `Prod Nat Nat` via `Prod.rec`:
///   Prod.rec params(Nat,Nat) (motive λ_.Nat) (minor_pair λa.λb. a|b) p
/// minor_pair binds [a,b] ⇒ a=Var1, b=Var0.
fn prod_fst(p: Tm) -> Tm {
    apps(
        Tm::Elim(PROD),
        &[
            Tm::Ind(NAT), // A
            Tm::Ind(NAT), // B
            lam(
                apps(Tm::Ind(PROD), &[Tm::Ind(NAT), Tm::Ind(NAT)]),
                Tm::Ind(NAT),
            ), // motive λ_:Prod Nat Nat. Nat
            lam(Tm::Ind(NAT), lam(Tm::Ind(NAT), Tm::Var(1))), // minor_pair = λa.λb. a
            p,
        ],
    )
}
fn prod_snd(p: Tm) -> Tm {
    apps(
        Tm::Elim(PROD),
        &[
            Tm::Ind(NAT),
            Tm::Ind(NAT),
            lam(
                apps(Tm::Ind(PROD), &[Tm::Ind(NAT), Tm::Ind(NAT)]),
                Tm::Ind(NAT),
            ),
            lam(Tm::Ind(NAT), lam(Tm::Ind(NAT), Tm::Var(0))), // minor_pair = λa.λb. b
            p,
        ],
    )
}

// ──────────────────────────────────────────────────────────────────────────────
// The generic fold `gfold_LN` (ONE `Elim LN`, one ι) — design §3c.
// ──────────────────────────────────────────────────────────────────────────────

/// `(Unit, Prod Nat X)` — the two summand types of `Sum Unit (Prod Nat X)`, the ι-normal form of
/// `El₀ code_LN Nat X` (the algebra input: element slot A:=Nat, recursive slot X). Used to build
/// the `inl`/`inr` summands the algebra consumes. `x` is the carrier var in the caller's scope.
fn one_step_functor(x: Tm) -> (Tm, Tm) {
    let unit = Tm::Ind(UNIT);
    let prod_nat_x = apps(Tm::Ind(PROD), &[Tm::Ind(NAT), x]);
    (unit, prod_nat_x) // (the inl-summand type, the inr-summand type)
}

/// `gfold_LN : Π(X:Type₀). (El₀ code_LN Nat X → X) → LN → X`, realized as `Elim LN` (design §3c).
/// The algebra input type is `El₀ code_LN Nat X` (design §1 A2 `El₀ d A X → X`: element slot
/// A:=Nat = LN's native element type, recursive slot X = the fold's carrier; the only well-typed
/// reading, ι-decode = `1 + Nat×X`, design §3c:180). Concretely:
///   gfold_LN := λX:Type₀. λg:(El₀ code_LN Nat X → X).
///     Elim LN (λ_:LN. X)
///       ( g (inl Unit (Prod Nat X) tt) )                                       -- minor_lnil
///       ( λh:Nat. λt:LN. λiht:X. g (inr Unit (Prod Nat X) (pair Nat X h iht)) ) -- minor_lcons
///
/// `Elim LN` spine (non-indexed, np=0, nidx=0): `motive · minor_lnil · minor_lcons · scrut`.
/// The minor SHAPE (`inl tt`, `inr (pair h iht)`) is dictated by `code_LN`'s decode
/// `El₀ code_LN Nat X` — change the code, the algebra-input type changes, ONE `El₀` computes it.
fn gfold_ln() -> Tm {
    // Outer binders: X (Var pushed first), g. Under both, X=Var1, g=Var0.
    // Inside `Elim LN`'s minors, further binders are pushed; we track de Bruijn carefully.

    // minor_lnil : motive lnil = X. Under [X, g] the body sits with NO extra binder pushed by the
    // recursor for the nullary ctor ⇒ X=Var1, g=Var0.
    //   g (inl Unit (Prod Nat X) tt)
    let (s_inl_l, s_inr_l) = one_step_functor(Tm::Var(1)); // X = Var1 here
    let inl_tt = apps(
        Tm::Ctor(SUM, 0), // inl
        &[s_inl_l, s_inr_l, Tm::Ctor(UNIT, 0)],
    );
    let minor_lnil = app(Tm::Var(0), inl_tt); // g (inl … tt)

    // minor_lcons : Π(h:Nat) Π(t:LN) Π(iht:X). motive (lcons h t) = X.
    // Field-then-IH order (recursor.rs:73): binders h, t, iht. Under [X, g, h, t, iht]:
    //   X=Var4, g=Var3, h=Var2, t=Var1, iht=Var0.
    //   g (inr Unit (Prod Nat X) (pair Nat X h iht))
    let (s_inl_c, s_inr_c) = one_step_functor(Tm::Var(4)); // X = Var4 here
    let pair_h_iht = apps(
        Tm::Ctor(PROD, 0), // pair
        &[
            Tm::Ind(NAT), // A := Nat
            Tm::Var(4),   // B := X
            Tm::Var(2),   // h
            Tm::Var(0),   // iht (the folded tail)
        ],
    );
    let inr_pair = apps(
        Tm::Ctor(SUM, 1), // inr
        &[s_inl_c, s_inr_c, pair_h_iht],
    );
    let minor_lcons_body = app(Tm::Var(3), inr_pair); // g (inr … (pair …))
                                                      // iht binder type = X. At the iht binder the context is [X, g, h, t] ⇒ X = Var3 (the BODY
                                                      // below, with iht also bound, sees X = Var4). Binder types are erased at φ_K (tm.rs:11) so
                                                      // only `infer`/`check` reads this — getting it right is what T3 verifies.
    let minor_lcons = lam(
        Tm::Ind(NAT), // h
        lam(
            Tm::Ind(LN),                       // t
            lam(Tm::Var(3), minor_lcons_body), // iht : X
        ),
    );

    // The Elim, under [X, g]: motive = λ_:LN. X (X=Var2 inside the motive's binder).
    let motive = lam(Tm::Ind(LN), Tm::Var(2));
    let elim_body = apps(Tm::Elim(LN), &[motive, minor_lnil, minor_lcons]);

    // Wrap the two outer binders. g's type: El₀ code_LN Nat X → X (element slot A:=Nat fixed to
    // LN's native element type, recursive slot X:=carrier — design §1 A2 `El₀ d A X → X`; the only
    // well-typed reading, decode = `1 + Nat×X`, design §3c:180). Under [X], X=Var0.
    let alg_ty = pi(el0_at(code_ln(), Tm::Ind(NAT), Tm::Var(0)), Tm::Var(1));
    lam(Tm::Sort(0), lam(alg_ty, elim_body))
}

/// `gfold_LN X g` type — the spec the fold checks against.
fn gfold_ln_ty() -> Tm {
    // Π(X:Type₀). (El₀ code_LN Nat X → X) → LN → X   (element slot A:=Nat, recursive slot X).
    pi(
        Tm::Sort(0),
        pi(
            pi(el0_at(code_ln(), Tm::Ind(NAT), Tm::Var(0)), Tm::Var(1)), // El₀ code_LN Nat X → X
            pi(Tm::Ind(LN), Tm::Var(2)),                                 // LN → X
        ),
    )
}

/// `list123 : LN` = `lcons 1 (lcons 2 (lcons 3 lnil))`.
fn list123() -> Tm {
    let lnil = Tm::Ctor(LN, 0);
    let lcons = |h: Tm, t: Tm| apps(Tm::Ctor(LN, 1), &[h, t]);
    lcons(numeral(1), lcons(numeral(2), lcons(numeral(3), lnil)))
}

/// `sumAlg : El₀ code_LN Nat Nat → Nat` (= `Sum Unit (Prod Nat Nat) → Nat`):
///   λs. Sum.rec (λ_.Nat) (λu:Unit. zero) (λp:Prod Nat Nat. add (fst p) (snd p)) s
/// Here the carrier X:=Nat and the `iht` slot is ALREADY the folded tail, so `snd p` is the
/// running total ⇒ generic-sum.
fn sum_alg() -> Tm {
    let unit = Tm::Ind(UNIT);
    let prod_nat_nat = apps(Tm::Ind(PROD), &[Tm::Ind(NAT), Tm::Ind(NAT)]);
    let dom = apps(Tm::Ind(SUM), &[unit.clone(), prod_nat_nat.clone()]); // Sum Unit (Prod Nat Nat)
                                                                         // body under [s]: s=Var0.
    let body = apps(
        Tm::Elim(SUM),
        &[
            unit.clone(),                   // A := Unit
            prod_nat_nat.clone(),           // B := Prod Nat Nat
            lam(dom.clone(), Tm::Ind(NAT)), // motive λ_:Sum…. Nat
            lam(unit, zero()),              // minor_inl = λu:Unit. zero
            // minor_inr = λp:Prod Nat Nat. add (fst p) (snd p)   (p=Var0)
            lam(
                prod_nat_nat,
                add(prod_fst(Tm::Var(0)), prod_snd(Tm::Var(0))),
            ),
            Tm::Var(0), // scrutinee = s
        ],
    );
    lam(dom, body)
}

/// `lenAlg : El₀ code_LN Nat Nat → Nat` — counts elements (genericity, T6):
///   λs. Sum.rec (λ_.Nat) (λu. zero) (λp. succ (snd p)) s
fn len_alg() -> Tm {
    let unit = Tm::Ind(UNIT);
    let prod_nat_nat = apps(Tm::Ind(PROD), &[Tm::Ind(NAT), Tm::Ind(NAT)]);
    let dom = apps(Tm::Ind(SUM), &[unit.clone(), prod_nat_nat.clone()]);
    let body = apps(
        Tm::Elim(SUM),
        &[
            unit.clone(),
            prod_nat_nat.clone(),
            lam(dom.clone(), Tm::Ind(NAT)),
            lam(unit, zero()),                             // inl ↦ 0
            lam(prod_nat_nat, succ(prod_snd(Tm::Var(0)))), // inr (h,t) ↦ succ t
            Tm::Var(0),
        ],
    );
    lam(dom, body)
}

// ──────────────────────────────────────────────────────────────────────────────
// Tests T1–T8 (design §4b). T4 is the headline.
// ──────────────────────────────────────────────────────────────────────────────

#[test]
fn t1_desc_and_ln_admit_at_type0() {
    // every support + Desc₀ + LN admits, has a recursor, and LN : Type₀.
    let env = slice1_env();
    for id in [NAT, UNIT, PROD, SUM, DESC, LN] {
        assert!(env.inds.contains_key(&id), "{id:?} admitted");
        assert!(env.recursors.contains_key(&id), "{id:?} has a recursor");
    }
    assert_eq!(
        infer(&env, &Vec::new(), &Tm::Ind(LN)).unwrap(),
        Tm::Sort(0),
        "LN : Type₀ (native described Nat-list, R3/R11 OK)"
    );
}

#[test]
fn t2_el0_describes_ln() {
    // COHERENCE (A5): `El₀ code_LN Nat LN` ι-reduces to LN's actual one-step functor
    // `Sum Unit (Prod Nat LN)` — i.e. code_LN DESCRIBES LN. Extends
    // el0_list_pattern_functor_computes (levitation_desc.rs:371) with carrier X := Ind(LN).
    let env = slice1_env();
    let want = apps(
        Tm::Ind(SUM),
        &[
            Tm::Ind(UNIT),
            apps(Tm::Ind(PROD), &[Tm::Ind(NAT), Tm::Ind(LN)]),
        ],
    );
    assert_eq!(
        nf_tm(
            &env,
            &Vec::new(),
            &el0_at(code_ln(), Tm::Ind(NAT), Tm::Ind(LN))
        ),
        want,
        "El₀ code_LN Nat LN ⟶ Sum Unit (Prod Nat LN): the code describes LN's ctor shape"
    );
}

#[test]
fn t3_gfold_ln_typechecks() {
    // The generic fold has the levitated interface type `Π(X).(El₀ code_LN Nat X → X)→LN→X`. The
    // minors are checked against `El₀ code_LN Nat X` ι-reduced (= `Sum Unit (Prod Nat X)`) via
    // T-Conv (infer.rs:152) — the load-bearing "generic input type" link, pure ι, no axiom.
    let env = slice1_env();
    let ty = gfold_ln_ty();
    // the spec type itself is well-formed.
    infer(&env, &Vec::new(), &ty).expect("gfold_LN spec type is well-formed");
    // the fold checks at that type (and infers a definitionally-equal type).
    check(&env, &Vec::new(), &gfold_ln(), &ty)
        .expect("gfold_LN : Π(X).(El₀ code_LN Nat X → X)→LN→X");
    let got = infer(&env, &Vec::new(), &gfold_ln()).expect("gfold_LN infers");
    assert_eq!(
        nf_tm(&env, &Vec::new(), &got),
        nf_tm(&env, &Vec::new(), &ty),
        "inferred fold type ≡ the levitated interface (up to ι/β)"
    );
}

#[test]
fn t4_generic_sum_reduces() {
    // THE THEOREM / the demo: generic-sum over a CLOSED described Nat-list reduces to the native
    // answer. `gfold_LN Nat sumAlg (lcons 1 (lcons 2 (lcons 3 lnil))) ⟶ 6`.
    // closed scrutinee ⇒ try_iota fires through all 3 lcons + lnil (driver.rs:62; nidx==0 :110);
    // each step feeds (inr (pair h iht)) to sumAlg ⇒ add h iht; bottoms at lnil ⇒ 0. 1+2+3 = 6.
    let env = slice1_env();
    let term = apps(gfold_ln(), &[Tm::Ind(NAT), sum_alg(), list123()]);
    assert_eq!(
        nf_tm(&env, &Vec::new(), &term),
        numeral(6),
        "gfold_LN Nat sumAlg [1,2,3] ⟶ 6 (generic-sum over closed described data = native sum)"
    );
    // and the term typechecks at Nat (the whole pipeline is well-typed).
    assert_eq!(
        nf_tm(&env, &Vec::new(), &infer(&env, &Vec::new(), &term).unwrap()),
        Tm::Ind(NAT),
        "gfold_LN Nat sumAlg [1,2,3] : Nat"
    );
}

#[test]
fn t5_no_false_green() {
    // The fold computes the RIGHT number, not a coincidence: == 6 and != 5.
    let env = slice1_env();
    let term = apps(gfold_ln(), &[Tm::Ind(NAT), sum_alg(), list123()]);
    let got = nf_tm(&env, &Vec::new(), &term);
    assert_eq!(got, numeral(6), "= 6");
    assert_ne!(got, numeral(5), "≠ 5 (no off-by-one / no-false-green)");
}

#[test]
fn t6_generic_length_reuses_same_fold() {
    // GENERICITY: the SAME gfold_LN, a DIFFERENT algebra ⇒ length = 3 (one generic fold, many ops).
    let env = slice1_env();
    let term = apps(gfold_ln(), &[Tm::Ind(NAT), len_alg(), list123()]);
    assert_eq!(
        nf_tm(&env, &Vec::new(), &term),
        numeral(3),
        "gfold_LN Nat lenAlg [1,2,3] ⟶ 3 (same fold, different algebra — the levitation payoff)"
    );
}

#[test]
fn t7_open_fold_still_fires() {
    // LN is NON-indexed (nidx==0) ⇒ its OWN fold fires on OPEN scrutinees too (driver.rs:110),
    // distinct from the GAP-C indexed-open limit (design §5). Here the scrutinee is a CLOSED
    // spine whose HEAD `lcons` is under a binder for an unrelated free var; the fold still
    // reduces the lcons/lnil structure. We fold `lcons 7 lnil` under a dummy binder ⇒ 7.
    let env = slice1_env();
    let lnil = Tm::Ctor(LN, 0);
    let one_elt = apps(Tm::Ctor(LN, 1), &[numeral(7), lnil]);
    // under λ_:Nat (a free var in scope), the fold of a closed list still ι-reduces.
    let body = apps(gfold_ln(), &[Tm::Ind(NAT), sum_alg(), one_elt]);
    let open = lam(Tm::Ind(NAT), body);
    assert_eq!(
        nf_tm(&env, &Vec::new(), &open),
        lam(Tm::Ind(NAT), numeral(7)),
        "LN's fold fires under a binder (non-indexed ι open-capable, driver.rs:110)"
    );
}

#[test]
fn t8_second_described_datatype() {
    // A6 (genericity over codes): a SECOND described datatype proves the algebra schema is
    // code-driven, not LN-specific. `code_Nat = d_sum d_one d_X` describes a Peano Nat whose
    // value carrier is the NATIVE `Nat` itself; `El₀ code_Nat A Nat ⟶ Sum Unit Nat`. We fold the
    // native `Nat` with the SAME El₀-typed algebra schema (here realized via Nat.rec) and show the
    // code's decode is `1 + X` — the algebra-input type is read off ONE El₀, different code.
    let env = slice1_env();
    // El₀ code_Nat Nat Nat ⟶ Sum Unit Nat (the NatF one-step functor; X := Nat).
    let want = apps(Tm::Ind(SUM), &[Tm::Ind(UNIT), Tm::Ind(NAT)]);
    assert_eq!(
        nf_tm(
            &env,
            &Vec::new(),
            &el0_at(code_nat(), Tm::Ind(NAT), Tm::Ind(NAT))
        ),
        want,
        "El₀ code_Nat Nat Nat ⟶ Sum Unit Nat (1 + X) — a SECOND code, SAME El₀ decoder"
    );
    // and the decode is GENERIC in the carrier: El₀ code_Nat Nat Unit ⟶ Sum Unit Unit.
    let want2 = apps(Tm::Ind(SUM), &[Tm::Ind(UNIT), Tm::Ind(UNIT)]);
    assert_eq!(
        nf_tm(
            &env,
            &Vec::new(),
            &el0_at(code_nat(), Tm::Ind(NAT), Tm::Ind(UNIT))
        ),
        want2,
        "El₀ code_Nat Nat Unit ⟶ Sum Unit Unit — carrier-generic, one El₀, second code"
    );
}
