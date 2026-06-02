//! Verified `map` FUSION / functor-composition law on the dnx-proof kernel:
//!   `∀A B C (f:B→C)(g:A→B)(l:List A). map f (map g l) = map (λx. f (g x)) l`.
//!
//! This is the second functor law for `map` (after the IDENTITY law `map id = id`,
//! thm_map_append.rs:633-719): the COMPOSITION law `map f ∘ map g = map (f ∘ g)`. It chains the
//! cross-type recursor `map` (List A → List B, thm_map_append.rs:13) with ITSELF at a second
//! instance (List B → List C), and compares against ONE `map` at the composed function. The
//! composition `f ∘ g` is expressed directly as the closed lambda `λx:A. f (g x)` (Type₀-clean;
//! no separate `compose` constant is needed — the kernel has first-class λ, so the inline
//! abstraction is the cleanest witness and avoids an extra δ-const in the TCB).
//!
//!   map := λA B f l. List.rec A (λ_:List A. List B) (nil B) (λa tl ih. cons B (f a) ih) l
//!     ⇒  map A B f nil ι→ nil B ,  map A B f (cons a tl) ι→ cons B (f a) (map A B f tl).
//!
//! Every family involved is non-indexed (`List` has `nidx == 0`), so the ι-driver fires on OPEN
//! scrutinees (driver.rs:104-119 fast-path) and the inductive step reduces under binders — the
//! `driver.rs:106` empty-ctx infer (which only bites INDEXED families) never engages.
//!
//! THEOREMS (machine-checked by the trusted kernel `check`; the kernel is the oracle):
//!   • closed computation: map f (map g [e0,e2]) = [f(g e0), f(g e2)]   (ι on closed lists; nf/conv).
//!   • map_map : ∀A B C f g l. map f (map g l) = map (λx. f (g x)) l
//!     (GENERAL; induction on l; base definitional; step CONSUMES the IH via `ap_cons` over List C;
//!      the composed head `(λx.f(g x)) a ≡ f (g a)` collapses by β, exactly as `id a ≡ a` does in
//!      the identity law).
//!
//! NO new axioms. NO-FALSE-GREEN: the f/g-swapped companion is REJECTED by `check`.

use dnx_proof::conv::conv;
use dnx_proof::driver::nf_tm;
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::{check, TypeError};
use dnx_proof::symbol::{ConstId, IndId};
use dnx_proof::tm::Tm;

// ── term helpers (same idioms as thm_map_append.rs) ──
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

const ATOM: IndId = IndId(0); // closed element type {e0,e1,e2} to populate the closed-compute lists
const LIST: IndId = IndId(1);
const ID: IndId = IndId(2);
const MAP: ConstId = ConstId(0);

// Atom = e0 | e1 | e2.   (thm_map_append.rs:53-74.)
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

// List : Π(A:Type₀). Type₀  (param A, NO indices ⇒ nidx==0).   (thm_map_append.rs:76-96.)
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

// Id : Π(A:Type₀)(a:A). A → Type₀ ; refl A a : Id A a a.   (thm_map_append.rs:108-126.)
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
fn id_ty(a_ty: Tm, a: Tm, b: Tm) -> Tm {
    apps(Tm::Ind(ID), &[a_ty, a, b])
}
fn refl(a_ty: Tm, a: Tm) -> Tm {
    apps(Tm::Ctor(ID, 0), &[a_ty, a])
}

// map := λA B f l. List.rec A (λ_:List A. List B) (nil B) (λa tl ih. cons B (f a) ih) l
//   (recursion on l; thm_map_append.rs:169-211). Constant `List B` motive ⇒ non-indexed result.
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
    // Π(A B:Type₀)(f:A→B)(l:List A). List B.
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

/// `comp A f g := λx:A. f (g x)`, the diagrammatic composition `f ∘ g : A → C` for
/// `g : A → B`, `f : B → C`. Body `Var(0)` is the lambda's own bound `x`; `f`/`g` are passed in
/// already shifted for ONE extra binder (the `x`), so the helper composes correctly at any context.
fn comp(a_ty: Tm, f: Tm, g: Tm) -> Tm {
    lam(a_ty, app(f, app(g, Tm::Var(0))))
}

fn env() -> dnx_proof::env::GlobalEnv {
    let mut e = dnx_proof::env::GlobalEnv::default();
    e.add_inductive(atom()).expect("Atom admits");
    e.add_inductive(list_ind())
        .expect("List admits (parametric inductive, positivity R3 ok)");
    e.add_inductive(id_ind()).expect("Id admits");
    e.add_const(MAP, map_ty(), map_body())
        .expect("map admits (δ-acyclic, cross-type recursor)");
    e
}

/// `[x0;x1;…]` over Atom.
fn list_lit(xs: &[Tm]) -> Tm {
    xs.iter()
        .rev()
        .fold(nil(atom_ty()), |tl, hd| cons(atom_ty(), hd.clone(), tl))
}

// Closed witnesses over Atom: g = (e0↦e1, _↦e2) crudely as a constant won't show fusion, so use two
// DISTINCT closed functions. g := λ_:Atom. e1 (sends every head to e1); f := λ_:Atom. e2 (every head
// to e2). Then map f (map g l) ι→ all-e2, and map (f∘g) l ι→ all-e2 — equal, and DISTINCT from the
// single passes (map g l is all-e1, map f l would be all-e2) so the closed case is non-degenerate.
fn g_fun() -> Tm {
    lam(atom_ty(), e(1))
}
fn f_fun() -> Tm {
    lam(atom_ty(), e(2))
}

#[test]
fn map_map_computes_closed() {
    // map f (map g [e0,e2]) ι→ [e2,e2], and map (λx. f (g x)) [e0,e2] ι→ [e2,e2] — equal.
    let env = env();
    let input = list_lit(&[e(0), e(2)]); // [e0,e2]
    let want = list_lit(&[e(2), e(2)]); // [e2,e2]  (f∘g sends everything to e2)
    let lhs = map_(
        atom_ty(),
        atom_ty(),
        f_fun(),
        map_(atom_ty(), atom_ty(), g_fun(), input.clone()),
    );
    let rhs = map_(
        atom_ty(),
        atom_ty(),
        comp(atom_ty(), f_fun(), g_fun()),
        input.clone(),
    );
    assert_eq!(
        nf_tm(&env, &Vec::new(), &lhs),
        nf_tm(&env, &Vec::new(), &want),
        "map f (map g [e0,e2]) ι→ [e2,e2]"
    );
    assert_eq!(
        nf_tm(&env, &Vec::new(), &rhs),
        nf_tm(&env, &Vec::new(), &want),
        "map (λx. f (g x)) [e0,e2] ι→ [e2,e2]"
    );
    assert!(
        conv(&env, &Vec::new(), &lhs, &rhs).unwrap(),
        "map f (map g [e0,e2]) ≡ map (λx. f (g x)) [e0,e2]"
    );
    // no-false-green: the fused side is NOT convertible to the SINGLE inner pass `map g [e0,e2]`
    // (= [e1,e1]) — the closed case genuinely exercises BOTH passes.
    let inner_only = list_lit(&[e(1), e(1)]);
    assert!(
        !conv(&env, &Vec::new(), &rhs, &inner_only).unwrap(),
        "map (λx. f (g x)) [e0,e2] ≢ [e1,e1]"
    );
}

// ════════════════════════ ap_cons — congruence of `cons a` from J (over List C) ════════════════════════
// Reproduced verbatim from thm_map_append.rs:358-428 (the step's only tool). Instantiated at A:=C below.

/// ap_cons : Π(A:Type₀)(a:A)(xs ys:List A)(p:Id (List A) xs ys). Id (List A) (cons A a xs)(cons A a ys)
fn ap_cons() -> Tm {
    // ctx [A,a,xs,ys,p]: A=Var4, a=Var3, xs=Var2, ys=Var1, p=Var0.
    let motive = lam(
        list_ty(Tm::Var(4)), // ys' : List A
        lam(
            id_ty(list_ty(Tm::Var(5)), Tm::Var(3), Tm::Var(0)), // q : Id (List A) xs ys'
            id_ty(
                list_ty(Tm::Var(6)),
                cons(Tm::Var(6), Tm::Var(5), Tm::Var(4)), // cons A a xs
                cons(Tm::Var(6), Tm::Var(5), Tm::Var(1)), // cons A a ys'
            ),
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            list_ty(Tm::Var(4)), // A_id = List A
            Tm::Var(2),          // xs
            motive,
            refl(
                list_ty(Tm::Var(4)),
                cons(Tm::Var(4), Tm::Var(3), Tm::Var(2)),
            ), // refl (List A)(cons A a xs)
            Tm::Var(1), // index ys
            Tm::Var(0), // scrutinee p
        ],
    );
    lam(
        Tm::Sort(0),
        lam(
            Tm::Var(0), // a : A
            lam(
                list_ty(Tm::Var(1)), // xs
                lam(
                    list_ty(Tm::Var(2)),                                           // ys
                    lam(id_ty(list_ty(Tm::Var(3)), Tm::Var(1), Tm::Var(0)), body), // p
                ),
            ),
        ),
    )
}
fn ap_cons_ty() -> Tm {
    pi(
        Tm::Sort(0),
        pi(
            Tm::Var(0),
            pi(
                list_ty(Tm::Var(1)),
                pi(
                    list_ty(Tm::Var(2)),
                    pi(
                        id_ty(list_ty(Tm::Var(3)), Tm::Var(1), Tm::Var(0)),
                        id_ty(
                            list_ty(Tm::Var(4)),
                            cons(Tm::Var(4), Tm::Var(3), Tm::Var(2)),
                            cons(Tm::Var(4), Tm::Var(3), Tm::Var(1)),
                        ),
                    ),
                ),
            ),
        ),
    )
}
/// `ap_cons A a xs ys p : Id (List A) (cons A a xs) (cons A a ys)`  (concrete instance).
fn ap_cons_at(a_ty: Tm, a: Tm, xs: Tm, ys: Tm, p: Tm) -> Tm {
    apps(ap_cons(), &[a_ty, a, xs, ys, p])
}

#[test]
fn ap_cons_typechecks() {
    let env = env();
    assert!(
        check(&env, &Vec::new(), &ap_cons(), &ap_cons_ty()).is_ok(),
        "ap_cons : Π(A)(a:A)(xs ys:List A)(p:Id (List A) xs ys). Id (List A) (cons a xs)(cons a ys)"
    );
}

// ════════════════════════ map_map — ∀A B C f g l. map f (map g l) = map (λx. f (g x)) l ════════════════════════

/// map_map := λA B C f g l. List.rec A
///     (λl'. Id (List C) (map B C f (map A B g l')) (map A C (f∘g) l'))               -- motive
///     (refl (List C) (nil C))                                                        -- base l'=nil
///     (λa xs ih. ap_cons C (f (g a)) (map B C f (map A B g xs)) (map A C (f∘g) xs) ih) -- step
///     l                                                       (f∘g := λx:A. f (g x))
///
/// Induction on l (the list every `map` recurses on).
///   Base l=nil: `map f (map g nil)` ι→ `map f (nil B)` ι→ `nil C`; `map (f∘g) nil` ι→ `nil C`.
///     Goal `Id (List C) (nil C) (nil C)` = `refl (List C) (nil C)` (DEFINITIONAL).
///   Step l=cons a xs:
///     LHS `map f (map g (cons a xs))` ι→ `map f (cons (g a) (map g xs))`
///                                     ι→ `cons (f (g a)) (map f (map g xs))`,
///     RHS `map (f∘g) (cons a xs)` ι→ `cons ((f∘g) a) (map (f∘g) xs)`, and
///       `(f∘g) a = (λx. f (g x)) a` β→ `f (g a)` (whnf_tm β, driver.rs:46-47), so RHS ≡
///       `cons (f (g a)) (map (f∘g) xs)`,
///     IH `ih : Id (List C) (map f (map g xs)) (map (f∘g) xs)`,
///     so `ap_cons C (f (g a)) … ih` closes the goal (the heads match up to the β-redex `(f∘g) a ≡
///       f (g a)`). The IH is genuinely CONSUMED. The recursive ι's fire on the OPEN tail `xs`
///       because List is non-indexed (driver.rs:104-119 fast-path).
fn map_map() -> Tm {
    // ctx [A,B,C,f,g,l]: A=Var5, B=Var4, C=Var3, f=Var2, g=Var1, l=Var0.
    // motive λl'. Id (List C) (map B C f (map A B g l')) (map A C (f∘g) l').
    //   ctx [A,B,C,f,g,l,l']: A=Var6, B=Var5, C=Var4, f=Var3, g=Var2, l'=Var0.
    let motive = lam(
        list_ty(Tm::Var(5)), // l' : List A   (A = Var5 in ctx [A,B,C,f,g,l])
        id_ty(
            list_ty(Tm::Var(4)), // List C
            map_(
                Tm::Var(5),                                           // B
                Tm::Var(4),                                           // C
                Tm::Var(3),                                           // f
                map_(Tm::Var(6), Tm::Var(5), Tm::Var(2), Tm::Var(0)), // map A B g l'
            ), // map B C f (map A B g l')
            map_(
                Tm::Var(6), // A
                Tm::Var(4), // C
                // f∘g : A → C ; f,g shifted for the comp's own binder.
                comp(Tm::Var(6), Tm::Var(3 + 1), Tm::Var(2 + 1)),
                Tm::Var(0), // l'
            ), // map A C (f∘g) l'
        ),
    );
    // base : refl (List C) (nil C)   (ctx [A,B,C,f,g,l]: C=Var3).
    let base = refl(list_ty(Tm::Var(3)), nil(Tm::Var(3)));
    // step λa.λxs.λih. ap_cons C (f (g a)) (map f (map g xs)) (map (f∘g) xs) ih.
    let step = lam(
        Tm::Var(5), // a : A   (A = Var5 in ctx [A,B,C,f,g,l])
        lam(
            list_ty(Tm::Var(6)), // xs : List A  (A = Var6 in ctx [A,B,C,f,g,l,a])
            lam(
                // ih : motive xs = Id (List C) (map f (map g xs)) (map (f∘g) xs).
                //   ctx [A,B,C,f,g,l,a,xs]: A=Var7, B=Var6, C=Var5, f=Var4, g=Var3, xs=Var0.
                id_ty(
                    list_ty(Tm::Var(5)), // List C
                    map_(
                        Tm::Var(6),
                        Tm::Var(5),
                        Tm::Var(4),
                        map_(Tm::Var(7), Tm::Var(6), Tm::Var(3), Tm::Var(0)),
                    ), // map B C f (map A B g xs)
                    map_(
                        Tm::Var(7),
                        Tm::Var(5),
                        comp(Tm::Var(7), Tm::Var(4 + 1), Tm::Var(3 + 1)),
                        Tm::Var(0),
                    ), // map A C (f∘g) xs
                ),
                // ctx [A,B,C,f,g,l,a,xs,ih]: A=Var8, B=Var7, C=Var6, f=Var5, g=Var4, a=Var2, xs=Var1, ih=Var0.
                ap_cons_at(
                    Tm::Var(6),                                   // C
                    app(Tm::Var(5), app(Tm::Var(4), Tm::Var(2))), // f (g a)
                    map_(
                        Tm::Var(7),
                        Tm::Var(6),
                        Tm::Var(5),
                        map_(Tm::Var(8), Tm::Var(7), Tm::Var(4), Tm::Var(1)),
                    ), // map B C f (map A B g xs)
                    map_(
                        Tm::Var(8),
                        Tm::Var(6),
                        comp(Tm::Var(8), Tm::Var(5 + 1), Tm::Var(4 + 1)),
                        Tm::Var(1),
                    ), // map A C (f∘g) xs
                    Tm::Var(0),                                   // ih  (CONSUMED)
                ),
            ),
        ),
    );
    let rec = apps(
        Tm::Elim(LIST),
        &[Tm::Var(5), motive, base, step, Tm::Var(0)],
    ); // param A, scrut l
    lam(
        Tm::Sort(0),
        lam(
            Tm::Sort(0),
            lam(
                Tm::Sort(0),
                lam(
                    pi(Tm::Var(1), Tm::Var(1)), // f : B → C   (B=Var1, C=Var0)
                    lam(
                        pi(Tm::Var(3), Tm::Var(3)), // g : A → B   (A=Var3, B=Var2 ⇒ Pi dom Var3, cod Var3 under dom)
                        lam(list_ty(Tm::Var(4)), rec), // l : List A  (A = Var4 in ctx [A,B,C,f,g])
                    ),
                ),
            ),
        ),
    )
}
fn map_map_ty() -> Tm {
    // Π(A B C:Type₀)(f:B→C)(g:A→B)(l:List A). Id (List C) (map f (map g l)) (map (λx. f (g x)) l).
    // ctx [A,B,C,f,g,l]: A=Var5, B=Var4, C=Var3, f=Var2, g=Var1, l=Var0.
    pi(
        Tm::Sort(0),
        pi(
            Tm::Sort(0),
            pi(
                Tm::Sort(0),
                pi(
                    pi(Tm::Var(1), Tm::Var(1)), // f : B → C
                    pi(
                        pi(Tm::Var(3), Tm::Var(3)), // g : A → B
                        pi(
                            list_ty(Tm::Var(4)), // l : List A
                            id_ty(
                                list_ty(Tm::Var(3)), // List C
                                map_(
                                    Tm::Var(4),
                                    Tm::Var(3),
                                    Tm::Var(2),
                                    map_(Tm::Var(5), Tm::Var(4), Tm::Var(1), Tm::Var(0)),
                                ), // map B C f (map A B g l)
                                map_(
                                    Tm::Var(5),
                                    Tm::Var(3),
                                    comp(Tm::Var(5), Tm::Var(2 + 1), Tm::Var(1 + 1)),
                                    Tm::Var(0),
                                ), // map A C (f∘g) l
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
}

#[test]
fn map_map_typechecks() {
    // THE theorem: ∀A B C f g l. map f (map g l) = map (λx. f (g x)) l — GENERAL, machine-checked.
    // The functor COMPOSITION law. Induction on l (List.rec); base definitional; step CONSUMES the IH
    // via ap_cons over List C. The composed head `(λx.f(g x)) a ≡ f (g a)` collapses by β
    // (driver.rs:46-47), exactly as `id a ≡ a` does in the identity law. Goes through on the OPEN tail
    // because List is non-indexed (nidx==0) — the open recursive field `xs` never hits driver:106.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &map_map(), &map_map_ty()).is_ok(),
        "map_map : Π(A B C)(f:B→C)(g:A→B)(l). Id (List C) (map f (map g l)) (map (λx. f (g x)) l)"
    );
}

#[test]
fn false_map_map_swap_rejected() {
    // NO-FALSE-GREEN: `map_map` does NOT inhabit the f/g-SWAPPED goal
    // `map f (map g l) = map (λx. g (f x)) l`. Even ignoring that `g (f x)` is ill-typed in general,
    // at A=B=C the order matters: the witness's base/step build the `f∘g` endpoints, which are NOT
    // convertible to the `g∘f` target, so `check` rejects. We pin A=B=C=Atom (where both composites
    // are well-typed) to make the rejection a genuine ORDER check, not a typing artifact.
    let env = env();
    // bad goal SPECIALISED to A=B=C=Atom: Π(f g:Atom→Atom)(l:List Atom).
    //   Id (List Atom) (map f (map g l)) (map (λx. g (f x)) l).   ctx [f,g,l]: f=Var2, g=Var1, l=Var0.
    let bad_ty = pi(
        pi(atom_ty(), atom_ty()), // f : Atom → Atom
        pi(
            pi(atom_ty(), atom_ty()), // g : Atom → Atom
            pi(
                list_ty(atom_ty()), // l : List Atom
                id_ty(
                    list_ty(atom_ty()),
                    map_(
                        atom_ty(),
                        atom_ty(),
                        Tm::Var(2),                                         // f
                        map_(atom_ty(), atom_ty(), Tm::Var(1), Tm::Var(0)), // map g l
                    ), // map f (map g l)
                    map_(
                        atom_ty(),
                        atom_ty(),
                        // λx. g (f x)  — SWAPPED order (g∘f instead of f∘g).
                        lam(
                            atom_ty(),
                            app(Tm::Var(1 + 1), app(Tm::Var(2 + 1), Tm::Var(0))),
                        ),
                        Tm::Var(0),
                    ), // map (λx. g (f x)) l
                ),
            ),
        ),
    );
    // `map_map` instantiated at A=B=C=Atom, f,g closed — the well-typed term whose stated type is the
    // TRUE (f∘g) law; here we ask `check` to accept it at the FALSE (g∘f) type.
    let witness = apps(map_map(), &[atom_ty(), atom_ty(), atom_ty()]);
    // POSITIVE CONTROL (non-vacuity): the SAME specialised witness DOES check against the TRUE
    // (f∘g) goal — so the rejection below is a genuine f/g-ORDER mismatch, not a vacuous ill-typed
    // term that would reject any type.
    let good_ty = pi(
        pi(atom_ty(), atom_ty()), // f : Atom → Atom
        pi(
            pi(atom_ty(), atom_ty()), // g : Atom → Atom
            pi(
                list_ty(atom_ty()), // l : List Atom
                id_ty(
                    list_ty(atom_ty()),
                    map_(
                        atom_ty(),
                        atom_ty(),
                        Tm::Var(2),                                         // f
                        map_(atom_ty(), atom_ty(), Tm::Var(1), Tm::Var(0)), // map g l
                    ), // map f (map g l)
                    map_(
                        atom_ty(),
                        atom_ty(),
                        // λx. f (g x)  — correct (f∘g) order.
                        lam(
                            atom_ty(),
                            app(Tm::Var(2 + 1), app(Tm::Var(1 + 1), Tm::Var(0))),
                        ),
                        Tm::Var(0),
                    ), // map (λx. f (g x)) l
                ),
            ),
        ),
    );
    assert!(
        check(&env, &Vec::new(), &witness, &good_ty).is_ok(),
        "positive control: specialised map_map DOES prove the true (f∘g) law at A=B=C=Atom"
    );
    assert_eq!(
        check(&env, &Vec::new(), &witness, &bad_ty),
        Err(TypeError::Mismatch),
        "map_map does NOT prove map f (map g l) = map (λx. g (f x)) l  (no false-green)"
    );
}
