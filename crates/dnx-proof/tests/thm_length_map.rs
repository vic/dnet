//! Verified composition of the two cross-type recursors `map : List A → List B` and
//! `length : List A → Nat` on the dnx-proof kernel, culminating in the GENERAL law
//! `∀A B f l. length (map f l) = length l` — "`map` preserves length".
//!
//! This is the first theorem here to chain BOTH cross-type recursors in one goal
//! (`length ∘ map`): `map` (List A → List B, thm_map_append.rs:13) feeds its result into
//! `length` (List B → Nat, thm_length_append.rs:7). Every family involved is non-indexed
//! (`List` and `Nat` have `nidx == 0`), so the ι-driver fires on OPEN scrutinees
//! (driver.rs:104-119 fast-path) and the inductive step reduces under binders — the
//! `driver.rs:106` empty-ctx infer (which only bites INDEXED families) never engages.
//!
//!   map    := λA B f l. List.rec A (λ_:List A. List B) (nil B) (λa tl ih. cons B (f a) ih) l
//!   length := λA xs.    List.rec A (λ_:List A. Nat)     0       (λa tl ih. succ ih)        xs
//!
//! THEOREM (GENERAL, ∀-quantified, machine-checked by the trusted kernel `check`):
//!   • length_map : ∀A B f l. length (map f l) = length l
//!     (induction on l; base definitional; step CONSUMES the IH via the J-derived `ap_succ`).
//!
//! NO new axioms. NO-FALSE-GREEN: the off-by-one companion is REJECTED by `check`.

use dnx_proof::conv::conv;
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::{check, TypeError};
use dnx_proof::symbol::{ConstId, IndId};
use dnx_proof::tm::Tm;

// ── term helpers (same idioms as thm_length_append.rs / thm_map_append.rs) ──
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

const ATOM: IndId = IndId(0); // closed payload type {e0,e1,e2} for the closed-compute check
const LIST: IndId = IndId(1);
const NAT: IndId = IndId(2);
const ID: IndId = IndId(3);
const MAP: ConstId = ConstId(0);
const LENGTH: ConstId = ConstId(1);

// Atom = e0 | e1 | e2.   (thm_length_append.rs:47-61.)
fn atom() -> Inductive {
    Inductive {
        id: ATOM,
        params: vec![],
        indices: vec![],
        sort: 0,
        ctors: (0..3)
            .map(|k| CtorDecl {
                ctor_ix: k,
                args: vec![],
                ret_indices: vec![],
            })
            .collect(),
    }
}
fn atom_ty() -> Tm {
    Tm::Ind(ATOM)
}
fn e(k: u32) -> Tm {
    Tm::Ctor(ATOM, k)
}

// List : Π(A:Type₀). Type₀  (param A, NO indices ⇒ nidx==0).   (thm_list_append.rs:76-96.)
fn list_ind() -> Inductive {
    Inductive {
        id: LIST,
        params: vec![Tm::Sort(0)],
        indices: vec![],
        sort: 0,
        ctors: vec![
            CtorDecl {
                ctor_ix: 0,
                args: vec![],
                ret_indices: vec![],
            }, // nil
            CtorDecl {
                ctor_ix: 1,
                args: vec![Tm::Var(0), app(Tm::Ind(LIST), Tm::Var(1))], // a:A, xs:List A
                ret_indices: vec![],
            },
        ],
    }
}
fn list_ty(a: Tm) -> Tm {
    app(Tm::Ind(LIST), a)
}
fn nil(a: Tm) -> Tm {
    app(Tm::Ctor(LIST, 0), a)
}
fn cons(a_ty: Tm, hd: Tm, tl: Tm) -> Tm {
    apps(Tm::Ctor(LIST, 1), &[a_ty, hd, tl])
}

// Nat = zero | succ Nat   (non-indexed; thm_length_append.rs:95-114).
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
fn nat_ty() -> Tm {
    Tm::Ind(NAT)
}
fn zero() -> Tm {
    Tm::Ctor(NAT, 0)
}
fn succ(n: Tm) -> Tm {
    app(Tm::Ctor(NAT, 1), n)
}

// Id : Π(A:Type₀)(a:A). A → Type₀ ; refl A a : Id A a a.   (thm_length_append.rs:127-139.)
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
fn id_nat(a: Tm, b: Tm) -> Tm {
    apps(Tm::Ind(ID), &[nat_ty(), a, b])
}
fn refl_nat(a: Tm) -> Tm {
    apps(Tm::Ctor(ID, 0), &[nat_ty(), a])
}

// map := λA B f l. List.rec A (λ_:List A. List B) (nil B) (λa tl ih. cons B (f a) ih) l
//   (recursion on l; thm_map_append.rs:173-211). Constant `List B` motive ⇒ non-indexed result.
fn map_body() -> Tm {
    // ctx [A,B,f,l]: A=Var3, B=Var2, f=Var1, l=Var0.
    let minor_cons = lam(
        Tm::Var(3), // a : A   (A = Var3 in ctx [A,B,f,l])
        lam(
            list_ty(Tm::Var(4)), // tl : List A  (A = Var4 in ctx [A,B,f,l,a])
            lam(
                list_ty(Tm::Var(4)), // ih : List B  (B = Var4 in ctx [A,B,f,l,a,tl])
                cons(
                    Tm::Var(5),                  // B   (B = Var5 in ctx [A,B,f,l,a,tl,ih])
                    app(Tm::Var(4), Tm::Var(2)), // f a   (f = Var4, a = Var2)
                    Tm::Var(0),                  // ih
                ),
            ),
        ),
    );
    let elim = apps(
        Tm::Elim(LIST),
        &[
            Tm::Var(3),                                    // param A
            lam(list_ty(Tm::Var(3)), list_ty(Tm::Var(3))), // motive λ_:List A. List B
            nil(Tm::Var(2)),                               // minor_nil = nil B
            minor_cons,
            Tm::Var(0), // scrutinee = l
        ],
    );
    lam(
        Tm::Sort(0),
        lam(
            Tm::Sort(0),
            lam(
                pi(Tm::Var(1), Tm::Var(1)),     // f : A → B
                lam(list_ty(Tm::Var(2)), elim), // l : List A
            ),
        ),
    )
}
fn map_ty() -> Tm {
    pi(
        Tm::Sort(0),
        pi(
            Tm::Sort(0),
            pi(
                pi(Tm::Var(1), Tm::Var(1)),                   // f : A → B
                pi(list_ty(Tm::Var(2)), list_ty(Tm::Var(2))), // l : List A ⊢ List B
            ),
        ),
    )
}
fn map_(a_ty: Tm, b_ty: Tm, f: Tm, l: Tm) -> Tm {
    apps(Tm::Const(MAP), &[a_ty, b_ty, f, l])
}

// length := λA xs. List.rec A (λ_:List A. Nat) 0 (λa tl ih. succ ih) xs   (thm_length_append.rs:210-233).
fn length_body() -> Tm {
    // ctx [A,xs]: A=Var1, xs=Var0.
    let minor_cons = lam(
        Tm::Var(1), // a : A   (A = Var1 in ctx [A,xs])
        lam(
            list_ty(Tm::Var(2)), // tl : List A  (A = Var2 in ctx [A,xs,a])
            lam(
                nat_ty(),         // ih : Nat
                succ(Tm::Var(0)), // succ ih
            ),
        ),
    );
    let elim = apps(
        Tm::Elim(LIST),
        &[
            Tm::Var(1),                         // param A
            lam(list_ty(Tm::Var(1)), nat_ty()), // motive λ_:List A. Nat
            zero(),                             // minor_nil = 0
            minor_cons,
            Tm::Var(0), // scrutinee = xs
        ],
    );
    lam(Tm::Sort(0), lam(list_ty(Tm::Var(0)), elim))
}
fn length_ty() -> Tm {
    pi(Tm::Sort(0), pi(list_ty(Tm::Var(0)), nat_ty()))
}
fn length(a_ty: Tm, xs: Tm) -> Tm {
    apps(Tm::Const(LENGTH), &[a_ty, xs])
}

fn env() -> dnx_proof::env::GlobalEnv {
    let mut e = dnx_proof::env::GlobalEnv::default();
    e.add_inductive(atom()).expect("Atom admits");
    e.add_inductive(list_ind())
        .expect("List admits (parametric inductive)");
    e.add_inductive(nat()).expect("Nat admits");
    e.add_inductive(id_ind()).expect("Id admits");
    e.add_const(MAP, map_ty(), map_body())
        .expect("map admits (δ-acyclic, cross-type recursor)");
    e.add_const(LENGTH, length_ty(), length_body())
        .expect("length admits (δ-acyclic)");
    e
}

/// `[x0;x1;…]` over Atom.
fn list_lit(xs: &[Tm]) -> Tm {
    xs.iter()
        .rev()
        .fold(nil(atom_ty()), |tl, hd| cons(atom_ty(), hd.clone(), tl))
}

#[test]
fn length_map_computes_closed() {
    // length (map (λ_.e1) [e0,e2]) ≡ 2 — the composite reduces on a CLOSED list, and equals
    // length [e0,e2] ≡ 2 (the witnessing endpoints of the general theorem at this instance).
    let env = env();
    let l2 = list_lit(&[e(0), e(2)]);
    let mapped = map_(atom_ty(), atom_ty(), lam(atom_ty(), e(1)), l2.clone());
    assert!(
        conv(
            &env,
            &Vec::new(),
            &length(atom_ty(), mapped.clone()),
            &succ(succ(zero()))
        )
        .unwrap(),
        "length (map (λ_.e1) [e0,e2]) ≡ 2"
    );
    assert!(
        conv(
            &env,
            &Vec::new(),
            &length(atom_ty(), mapped),
            &length(atom_ty(), l2)
        )
        .unwrap(),
        "length (map f [e0,e2]) ≡ length [e0,e2]"
    );
}

// ════════════════════════ ap_succ — congruence of `succ` from J ════════════════════════
// Reproduced verbatim from thm_length_append.rs:261-299 (the step's only tool).

/// ap_succ : Π(a b:Nat)(p:Id Nat a b). Id Nat (succ a) (succ b)
fn ap_succ() -> Tm {
    let motive = lam(
        nat_ty(),
        lam(
            id_nat(Tm::Var(3), Tm::Var(0)),
            id_nat(succ(Tm::Var(4)), succ(Tm::Var(1))),
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            nat_ty(),
            Tm::Var(2),
            motive,
            refl_nat(succ(Tm::Var(2))),
            Tm::Var(1),
            Tm::Var(0),
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
                id_nat(Tm::Var(1), Tm::Var(0)),
                id_nat(succ(Tm::Var(2)), succ(Tm::Var(1))),
            ),
        ),
    )
}
fn ap_succ_at(a: Tm, b: Tm, p: Tm) -> Tm {
    apps(ap_succ(), &[a, b, p])
}

#[test]
fn building_blocks_typecheck() {
    // map + length are admitted (δ-acyclic) and ap_succ (the step's only tool) typechecks.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &ap_succ(), &ap_succ_ty()).is_ok(),
        "ap_succ : Π(a b:Nat)(p:Id Nat a b). Id Nat (succ a)(succ b)  (J / Elim Id)"
    );
}

// ════════════════════════ length_map — ∀A B f l. length (map f l) = length l ════════════════════════

/// length_map := λA B f l. List.rec A
///     (λl'. Id Nat (length B (map A B f l')) (length A l'))                 -- motive
///     (refl Nat 0)                                                         -- base l'=nil
///     (λa tl ih. ap_succ (length B (map A B f tl)) (length A tl) ih)        -- step
///     l
///
/// Induction on l (the list both `map` and `length` recurse on).
///   Base l=nil: `map f nil` ι→ `nil B`, `length B (nil B)` ι→ `0`; `length A (nil A)` ι→ `0`.
///     Goal `Id Nat 0 0` = `refl Nat 0` (DEFINITIONAL).
///   Step l=cons a tl:
///     LHS `length B (map f (cons a tl))` ι→ `length B (cons (f a) (map f tl))`
///                                       ι→ `succ (length B (map f tl))`,
///     RHS `length A (cons a tl)` ι→ `succ (length A tl)`,
///     IH `ih : Id Nat (length B (map f tl)) (length A tl)`,
///     so `ap_succ (length B (map f tl)) (length A tl) ih` closes the goal. The IH is genuinely
///     CONSUMED. The recursive ι's fire on the OPEN tail `tl` because List/Nat are non-indexed
///     (nidx==0) — driver:106 does NOT bite.
fn length_map() -> Tm {
    // ctx [A,B,f,l]: A=Var3, B=Var2, f=Var1, l=Var0.
    // motive λl'. Id Nat (length B (map A B f l')) (length A l').
    //   ctx [A,B,f,l,l']: A=Var4, B=Var3, f=Var2, l'=Var0.
    let motive = lam(
        list_ty(Tm::Var(3)), // l' : List A   (A = Var3 in ctx [A,B,f,l])
        id_nat(
            length(
                Tm::Var(3),
                map_(Tm::Var(4), Tm::Var(3), Tm::Var(2), Tm::Var(0)),
            ), // length B (map f l')
            length(Tm::Var(4), Tm::Var(0)), // length A l'
        ),
    );
    // base : refl Nat 0   (both length-of-nil sides ι→ 0).
    let base = refl_nat(zero());
    // step λa.λtl.λih. ap_succ (length B (map f tl)) (length A tl) ih.
    let step = lam(
        Tm::Var(3), // a : A   (A = Var3 in ctx [A,B,f,l])
        lam(
            list_ty(Tm::Var(4)), // tl : List A  (A = Var4 in ctx [A,B,f,l,a])
            lam(
                // ih : motive tl = Id Nat (length B (map f tl)) (length A tl).
                //   ctx [A,B,f,l,a,tl]: A=Var5, B=Var4, f=Var3, tl=Var0.
                id_nat(
                    length(
                        Tm::Var(4),
                        map_(Tm::Var(5), Tm::Var(4), Tm::Var(3), Tm::Var(0)),
                    ),
                    length(Tm::Var(5), Tm::Var(0)),
                ),
                // ctx [A,B,f,l,a,tl,ih]: A=Var6, B=Var5, f=Var4, tl=Var1, ih=Var0.
                ap_succ_at(
                    length(
                        Tm::Var(5),
                        map_(Tm::Var(6), Tm::Var(5), Tm::Var(4), Tm::Var(1)),
                    ), // length B (map f tl)
                    length(Tm::Var(6), Tm::Var(1)), // length A tl
                    Tm::Var(0),                     // ih  (CONSUMED)
                ),
            ),
        ),
    );
    let rec = apps(
        Tm::Elim(LIST),
        &[Tm::Var(3), motive, base, step, Tm::Var(0)],
    ); // param A, scrut l
    lam(
        Tm::Sort(0),
        lam(
            Tm::Sort(0),
            lam(
                pi(Tm::Var(1), Tm::Var(1)),    // f : A → B
                lam(list_ty(Tm::Var(2)), rec), // l : List A
            ),
        ),
    )
}
fn length_map_ty() -> Tm {
    // Π(A B:Type₀)(f:A→B)(l:List A). Id Nat (length B (map f l)) (length A l).
    // ctx [A,B,f,l]: A=Var3, B=Var2, f=Var1, l=Var0.
    pi(
        Tm::Sort(0),
        pi(
            Tm::Sort(0),
            pi(
                pi(Tm::Var(1), Tm::Var(1)),
                pi(
                    list_ty(Tm::Var(2)), // l : List A
                    id_nat(
                        length(
                            Tm::Var(2),
                            map_(Tm::Var(3), Tm::Var(2), Tm::Var(1), Tm::Var(0)),
                        ), // length B (map f l)
                        length(Tm::Var(3), Tm::Var(0)), // length A l
                    ),
                ),
            ),
        ),
    )
}

#[test]
fn length_map_typechecks() {
    // THE theorem: ∀A B f l. length (map f l) = length l — GENERAL, machine-checked.
    // Induction on l (List.rec); base definitional; step CONSUMES the IH via ap_succ. Chains the
    // two cross-type recursors (length ∘ map). Goes through on the OPEN tail because List/Nat are
    // non-indexed (nidx==0) — the open recursive field `tl` never hits the driver:106 empty-ctx infer.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &length_map(), &length_map_ty()).is_ok(),
        "length_map : Π(A B)(f:A→B)(l:List A). Id Nat (length (map f l)) (length l)"
    );
}

#[test]
fn false_length_map_succ_rejected() {
    // NO-FALSE-GREEN (off by one): `length (map f l) = succ (length l)` is FALSE. The witness's
    // base `refl Nat 0` no longer fits the goal `Id Nat 0 (succ 0)`, so `check` rejects.
    let env = env();
    let bad_ty = pi(
        Tm::Sort(0),
        pi(
            Tm::Sort(0),
            pi(
                pi(Tm::Var(1), Tm::Var(1)),
                pi(
                    list_ty(Tm::Var(2)),
                    id_nat(
                        length(
                            Tm::Var(2),
                            map_(Tm::Var(3), Tm::Var(2), Tm::Var(1), Tm::Var(0)),
                        ), // length B (map f l)
                        succ(length(Tm::Var(3), Tm::Var(0))), // succ (length A l)  — off-by-one
                    ),
                ),
            ),
        ),
    );
    assert_eq!(
        check(&env, &Vec::new(), &length_map(), &bad_ty),
        Err(TypeError::Mismatch),
        "length_map does NOT prove length (map f l) = succ (length l)  (no false-green)"
    );
}
