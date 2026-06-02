//! Verified list `map` (the functorial action `List A → List B` of a function `f : A → B`) on
//! the dnx-proof kernel, culminating in the GENERAL naturality / fusion law
//! `∀A B f l1 l2. map f (l1 ++ l2) = (map f l1) ++ (map f l2)`.
//!
//! `map` is the first list operation here to take a FUNCTION argument (`f : A → B`) and to
//! recurse from one parametric inductive into ANOTHER (`List A → List B`); the cross-type
//! recursor precedent is `length` (`List A → Nat`, thm_length_append.rs:5-11). Because both
//! `List A` and `List B` are non-indexed (`nidx == 0`), the ι-driver fires on OPEN scrutinees
//! (driver.rs:104-119 fast-path), so `map` reduces under binders and the genuine inductive step
//! goes through — the `driver.rs:106` empty-ctx infer only bites INDEXED families (Vec).
//!
//! `map` recurses on its list argument, applying `f` to each head:
//!   map := λA B f l. List.rec A (λ_:List A. List B) (nil B) (λa tl ih. cons B (f a) ih) l
//!   ⇒  map A B f nil ι→ nil B ,  map A B f (cons a tl) ι→ cons B (f a) (map A B f tl).
//!
//! THEOREMS (machine-checked by the trusted kernel `check`; the kernel is the oracle):
//!   • closed computation: map (λx.e1) [e0,e2] = [e1,e1]      (ι on closed lists; nf/conv).
//!   • map_nil_l    : ∀A B f l. map f (nil ++ l) = map f l    (definitional: nil++l ι→ l).
//!   • map_append   : ∀A B f l1 l2. map f (l1++l2) = (map f l1) ++ (map f l2)
//!     (GENERAL; induction on l1, IH consumed via the J-derived congruence `ap_cons` over List B).
//!   • map_id       : ∀A l. map id l = l   (functor IDENTITY law; GENERAL; induction on l, IH
//!     consumed via `ap_cons`; the head `id a ≡ a` collapses by β).
//!
//! NO new axioms. NO-FALSE-GREEN: off-by-one / swapped companions are REJECTED by `check`.

use dnx_proof::conv::conv;
use dnx_proof::driver::nf_tm;
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::{check, TypeError};
use dnx_proof::symbol::{ConstId, IndId};
use dnx_proof::tm::Tm;

// ── term helpers (same idioms as thm_list_append.rs) ──
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
const APPEND: ConstId = ConstId(0);
const MAP: ConstId = ConstId(1);

// Atom = e0 | e1 | e2.
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

// Id : Π(A:Type₀)(a:A). A → Type₀ ; refl A a : Id A a a.   (thm_list_append.rs:108-126.)
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

// append := λA l1 l2. List.rec A (λ_:List A. List A) l2 (λa xs ih. cons A a ih) l1
//   (recursion on l1; thm_list_append.rs:128-157). Polymorphic — instantiated at A AND at B below.
fn append_body() -> Tm {
    let minor_cons = lam(
        Tm::Var(2), // a : A
        lam(
            list_ty(Tm::Var(3)), // xs : List A
            lam(
                list_ty(Tm::Var(4)),                      // ih : List A
                cons(Tm::Var(5), Tm::Var(2), Tm::Var(0)), // cons A a ih
            ),
        ),
    );
    let elim = apps(
        Tm::Elim(LIST),
        &[
            Tm::Var(2),                                    // param A
            lam(list_ty(Tm::Var(2)), list_ty(Tm::Var(3))), // motive λ_:List A. List A
            Tm::Var(0),                                    // minor_nil = l2
            minor_cons,
            Tm::Var(1), // scrutinee = l1
        ],
    );
    lam(
        Tm::Sort(0),
        lam(list_ty(Tm::Var(0)), lam(list_ty(Tm::Var(1)), elim)),
    )
}
fn append_ty() -> Tm {
    pi(
        Tm::Sort(0),
        pi(
            list_ty(Tm::Var(0)),
            pi(list_ty(Tm::Var(1)), list_ty(Tm::Var(2))),
        ),
    )
}
fn append(a_ty: Tm, l1: Tm, l2: Tm) -> Tm {
    apps(Tm::Const(APPEND), &[a_ty, l1, l2])
}

// map := λA B f l. List.rec A (λ_:List A. List B) (nil B) (λa tl ih. cons B (f a) ih) l
//   (recursion on l; spine for a 1-param inductive: param A · motive · minor_nil · minor_cons · scrut).
//   Motive is the CONSTANT `List B` (cross-type, like length's constant `Nat`), so the result is
//   non-indexed and ι fires on open scrutinees.
fn map_body() -> Tm {
    // ctx [A,B,f,l]: A=Var3, B=Var2, f=Var1, l=Var0.
    // minor_cons : λa.λtl.λih. cons B (f a) ih   (ctx [A,B,f,l,a,tl,ih]: B=Var5, f=Var4, a=Var2, ih=Var0).
    let minor_cons = lam(
        Tm::Var(3), // a : A   (A = Var3 in ctx [A,B,f,l])
        lam(
            list_ty(Tm::Var(4)), // tl : List A  (A = Var4 in ctx [A,B,f,l,a])
            lam(
                list_ty(Tm::Var(4)), // ih : List B  (B = Var4 in ctx [A,B,f,l,a,tl])
                cons(
                    Tm::Var(5),                  // B   (B = Var5 in ctx [A,B,f,l,a,tl,ih])
                    app(Tm::Var(4), Tm::Var(2)), // f a   (f = Var4, a = Var2)
                    Tm::Var(0),                  // ih  (B-list recursive result)
                ),
            ),
        ),
    );
    let elim = apps(
        Tm::Elim(LIST),
        &[
            Tm::Var(3),                                    // param A
            lam(list_ty(Tm::Var(3)), list_ty(Tm::Var(3))), // motive λ_:List A. List B  (A=Var3 under l'; B=Var3)
            nil(Tm::Var(2)), // minor_nil = nil B   (B = Var2 in ctx [A,B,f,l])
            minor_cons,
            Tm::Var(0), // scrutinee = l
        ],
    );
    // λA:Type₀.λB:Type₀.λf:A→B.λl:List A. elim
    lam(
        Tm::Sort(0),
        lam(
            Tm::Sort(0),
            lam(
                pi(Tm::Var(1), Tm::Var(1)), // f : A → B   (A=Var1, B=Var0 ⇒ Pi dom Var1, cod Var1 under the dom binder)
                lam(list_ty(Tm::Var(2)), elim), // l : List A  (A = Var2 in ctx [A,B,f])
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

/// `id_A := λx:A. x`. Body `Var(0)` is the lambda's own bound variable, so this is correct at ANY
/// binder context (no outer de-Bruijn shift needed).
fn idfun(a_ty: Tm) -> Tm {
    lam(a_ty, Tm::Var(0))
}

fn env() -> dnx_proof::env::GlobalEnv {
    let mut e = dnx_proof::env::GlobalEnv::default();
    e.add_inductive(atom()).expect("Atom admits");
    e.add_inductive(list_ind())
        .expect("List admits (parametric inductive, positivity R3 ok)");
    e.add_inductive(id_ind()).expect("Id admits");
    e.add_const(APPEND, append_ty(), append_body())
        .expect("append admits (δ-acyclic)");
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

/// The constant function `λ_:Atom. e1` — a non-trivial witness that `map` rewrites every element.
fn const_e1() -> Tm {
    lam(atom_ty(), e(1))
}

#[test]
fn map_admits_and_computes_closed() {
    // map (λ_.e1) [e0,e2] ι-normalizes to [e1,e1] — the recursor applies f to every head.
    let env = env();
    let input = list_lit(&[e(0), e(2)]); // [e0,e2]
    let want = list_lit(&[e(1), e(1)]); // [e1,e1]
    assert_eq!(
        nf_tm(
            &env,
            &Vec::new(),
            &map_(atom_ty(), atom_ty(), const_e1(), input.clone())
        ),
        nf_tm(&env, &Vec::new(), &want),
        "map (λ_.e1) [e0,e2] ι→ [e1,e1]"
    );
    assert!(
        conv(
            &env,
            &Vec::new(),
            &map_(atom_ty(), atom_ty(), const_e1(), input),
            &want
        )
        .unwrap(),
        "map (λ_.e1) [e0,e2] ≡ [e1,e1]"
    );
    // no-false-green: NOT convertible to a wrong-length / wrong-element result.
    let wrong = list_lit(&[e(1), e(1), e(1)]);
    assert!(
        !conv(
            &env,
            &Vec::new(),
            &map_(atom_ty(), atom_ty(), const_e1(), list_lit(&[e(0), e(2)])),
            &wrong
        )
        .unwrap(),
        "map (λ_.e1) [e0,e2] ≢ [e1,e1,e1]"
    );
}

// ════════════════════════ map_nil_l — ∀A B f l. map f (nil ++ l) = map f l ════════════════════════

/// map_nil_l := λA B f l. refl (List B) (map f l).
/// `nil ++ l` ι→ `l` (the append nil-minor), so `map f (nil ++ l) ≡ map f l` definitionally.
fn map_nil_l() -> Tm {
    // ctx [A,B,f,l]: A=Var3, B=Var2, f=Var1, l=Var0.
    lam(
        Tm::Sort(0),
        lam(
            Tm::Sort(0),
            lam(
                pi(Tm::Var(1), Tm::Var(1)), // f : A → B
                lam(
                    list_ty(Tm::Var(2)), // l : List A
                    refl(
                        list_ty(Tm::Var(2)), // List B  (B = Var2 in ctx [A,B,f,l])
                        map_(Tm::Var(3), Tm::Var(2), Tm::Var(1), Tm::Var(0)), // map f l
                    ),
                ),
            ),
        ),
    )
}
fn map_nil_l_ty() -> Tm {
    // Π(A B:Type₀)(f:A→B)(l:List A). Id (List B) (map f (append (nil A) l)) (map f l).
    pi(
        Tm::Sort(0),
        pi(
            Tm::Sort(0),
            pi(
                pi(Tm::Var(1), Tm::Var(1)),
                pi(
                    list_ty(Tm::Var(2)), // l : List A
                    id_ty(
                        list_ty(Tm::Var(2)), // List B
                        map_(
                            Tm::Var(3),
                            Tm::Var(2),
                            Tm::Var(1),
                            append(Tm::Var(3), nil(Tm::Var(3)), Tm::Var(0)),
                        ), // map f (nil ++ l)
                        map_(Tm::Var(3), Tm::Var(2), Tm::Var(1), Tm::Var(0)), // map f l
                    ),
                ),
            ),
        ),
    )
}

#[test]
fn map_nil_l_typechecks() {
    // ∀A B f l. map f (nil ++ l) = map f l — GENERAL, definitional (ι on the append nil-minor).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &map_nil_l(), &map_nil_l_ty()).is_ok(),
        "map_nil_l : Π(A B)(f:A→B)(l). Id (List B) (map f (nil ++ l)) (map f l)  (definitional)"
    );
}

// ════════════════════════ ap_cons — congruence of `cons a` from J (over List B) ════════════════════════

/// ap_cons : Π(A:Type₀)(a:A)(xs ys:List A)(p:Id (List A) xs ys). Id (List A) (cons A a xs) (cons A a ys)
///   (J / Elim Id; identical to thm_list_append.rs:261-302). Instantiated at A:=B below.
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

// ════════════════════════ map_append — ∀A B f l1 l2. map f (l1++l2) = (map f l1) ++ (map f l2) ════════════════════════

/// map_append := λA B f l1 l2. List.rec A
///     (λl1'. Id (List B) (map f (append l1' l2)) (append (map f l1') (map f l2)))   -- motive
///     (refl (List B) (map f l2))                                                    -- base l1=nil
///     (λa xs ih. ap_cons B (f a) (map f (append xs l2)) (append (map f xs) (map f l2)) ih) -- step
///     l1
///
/// Induction on l1 (the list `append`/`map` recurse on).
///   Base l1=nil: `map f (nil ++ l2)` ι→ `map f l2`; `(map f nil) ++ (map f l2)` ι→ `nil ++ (map f l2)`
///     ι→ `map f l2` — both sides ι to `map f l2`, so the goal is `refl (List B) (map f l2)`.
///   Step l1=cons a xs:
///     LHS `map f ((cons a xs) ++ l2)` ι→ `map f (cons a (xs ++ l2))` ι→ `cons (f a) (map f (xs++l2))`,
///     RHS `(map f (cons a xs)) ++ (map f l2)` ι→ `(cons (f a)(map f xs)) ++ (map f l2)`
///                                            ι→ `cons (f a) ((map f xs) ++ (map f l2))`,
///     IH `ih : Id (List B) (map f (xs++l2)) ((map f xs) ++ (map f l2))`,
///     so `ap_cons B (f a) … ih` closes the goal. The IH is genuinely CONSUMED. The recursive ι's
///     fire on the OPEN tail `xs` because List is non-indexed (driver.rs:104-119 fast-path).
fn map_append() -> Tm {
    // ctx [A,B,f,l1,l2]: A=Var4, B=Var3, f=Var2, l1=Var1, l2=Var0.
    // motive λl1'. Id (List B) (map f (append l1' l2)) (append (map f l1') (map f l2)).
    //   ctx [A,B,f,l1,l2,l1']: A=Var5, B=Var4, f=Var3, l2=Var1, l1'=Var0.
    let motive = lam(
        list_ty(Tm::Var(4)), // l1' : List A
        id_ty(
            list_ty(Tm::Var(4)), // List B
            map_(
                Tm::Var(5),
                Tm::Var(4),
                Tm::Var(3),
                append(Tm::Var(5), Tm::Var(0), Tm::Var(1)),
            ), // map f (l1' ++ l2)
            append(
                Tm::Var(4),
                map_(Tm::Var(5), Tm::Var(4), Tm::Var(3), Tm::Var(0)), // map f l1'
                map_(Tm::Var(5), Tm::Var(4), Tm::Var(3), Tm::Var(1)), // map f l2
            ), // (map f l1') ++ (map f l2)
        ),
    );
    // base : refl (List B) (map f l2)   (ctx [A,B,f,l1,l2]: A=Var4, B=Var3, f=Var2, l2=Var0).
    let base = refl(
        list_ty(Tm::Var(3)),
        map_(Tm::Var(4), Tm::Var(3), Tm::Var(2), Tm::Var(0)),
    );
    // step λa.λxs.λih. ap_cons B (f a) (map f (xs++l2)) ((map f xs)++(map f l2)) ih.
    //   ctx [A,B,f,l1,l2,a,xs,ih]: A=Var7, B=Var6, f=Var5, l2=Var3, a=Var2, xs=Var1, ih=Var0.
    let step = lam(
        Tm::Var(4), // a : A   (A = Var4 in ctx [A,B,f,l1,l2])
        lam(
            list_ty(Tm::Var(5)), // xs : List A  (A = Var5 in ctx [A,B,f,l1,l2,a])
            lam(
                // ih : motive xs = Id (List B) (map f (xs++l2)) ((map f xs)++(map f l2))
                //   ctx [A,B,f,l1,l2,a,xs]: A=Var6, B=Var5, f=Var4, l2=Var2, xs=Var0.
                id_ty(
                    list_ty(Tm::Var(5)),
                    map_(
                        Tm::Var(6),
                        Tm::Var(5),
                        Tm::Var(4),
                        append(Tm::Var(6), Tm::Var(0), Tm::Var(2)),
                    ), // map f (xs ++ l2)
                    append(
                        Tm::Var(5),
                        map_(Tm::Var(6), Tm::Var(5), Tm::Var(4), Tm::Var(0)), // map f xs
                        map_(Tm::Var(6), Tm::Var(5), Tm::Var(4), Tm::Var(2)), // map f l2
                    ),
                ),
                // ctx [A,B,f,l1,l2,a,xs,ih]: A=Var7, B=Var6, f=Var5, l2=Var3, a=Var2, xs=Var1, ih=Var0.
                ap_cons_at(
                    Tm::Var(6),                  // B
                    app(Tm::Var(5), Tm::Var(2)), // f a
                    map_(
                        Tm::Var(7),
                        Tm::Var(6),
                        Tm::Var(5),
                        append(Tm::Var(7), Tm::Var(1), Tm::Var(3)),
                    ), // map f (xs ++ l2)
                    append(
                        Tm::Var(6),
                        map_(Tm::Var(7), Tm::Var(6), Tm::Var(5), Tm::Var(1)), // map f xs
                        map_(Tm::Var(7), Tm::Var(6), Tm::Var(5), Tm::Var(3)), // map f l2
                    ), // (map f xs) ++ (map f l2)
                    Tm::Var(0),                  // ih  (CONSUMED)
                ),
            ),
        ),
    );
    let rec = apps(
        Tm::Elim(LIST),
        &[Tm::Var(4), motive, base, step, Tm::Var(1)],
    ); // param A, scrut l1
    lam(
        Tm::Sort(0),
        lam(
            Tm::Sort(0),
            lam(
                pi(Tm::Var(1), Tm::Var(1)), // f : A → B
                lam(
                    list_ty(Tm::Var(2)),           // l1 : List A
                    lam(list_ty(Tm::Var(3)), rec), // l2 : List A
                ),
            ),
        ),
    )
}
fn map_append_ty() -> Tm {
    // Π(A B:Type₀)(f:A→B)(l1 l2:List A). Id (List B) (map f (l1++l2)) ((map f l1) ++ (map f l2)).
    // ctx [A,B,f,l1,l2]: A=Var4, B=Var3, f=Var2, l1=Var1, l2=Var0.
    pi(
        Tm::Sort(0),
        pi(
            Tm::Sort(0),
            pi(
                pi(Tm::Var(1), Tm::Var(1)),
                pi(
                    list_ty(Tm::Var(2)), // l1
                    pi(
                        list_ty(Tm::Var(3)), // l2
                        id_ty(
                            list_ty(Tm::Var(3)), // List B
                            map_(
                                Tm::Var(4),
                                Tm::Var(3),
                                Tm::Var(2),
                                append(Tm::Var(4), Tm::Var(1), Tm::Var(0)),
                            ), // map f (l1 ++ l2)
                            append(
                                Tm::Var(3),
                                map_(Tm::Var(4), Tm::Var(3), Tm::Var(2), Tm::Var(1)), // map f l1
                                map_(Tm::Var(4), Tm::Var(3), Tm::Var(2), Tm::Var(0)), // map f l2
                            ), // (map f l1) ++ (map f l2)
                        ),
                    ),
                ),
            ),
        ),
    )
}

#[test]
fn map_append_typechecks() {
    // THE theorem: ∀A B f l1 l2. map f (l1++l2) = (map f l1) ++ (map f l2) — GENERAL, machine-checked.
    // Induction on l1 (List.rec); base definitional; step CONSUMES the IH via ap_cons over List B.
    // Goes through on the OPEN tail because List is non-indexed (nidx==0) — the open recursive field
    // `xs` never hits the driver:106 empty-ctx infer (that gate only bites INDEXED families).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &map_append(), &map_append_ty()).is_ok(),
        "map_append : Π(A B)(f:A→B)(l1 l2). Id (List B) (map f (l1++l2)) ((map f l1)++(map f l2))"
    );
}

#[test]
fn false_map_append_rejected() {
    // NO-FALSE-GREEN: `map_append` does NOT inhabit the SWAPPED (false) goal
    // `map f (l1++l2) = (map f l2) ++ (map f l1)` (l1,l2 swapped on the rhs) — append is not
    // commutative, so the base/step witnesses no longer fit and `check` rejects.
    let env = env();
    let bad_ty = pi(
        Tm::Sort(0),
        pi(
            Tm::Sort(0),
            pi(
                pi(Tm::Var(1), Tm::Var(1)),
                pi(
                    list_ty(Tm::Var(2)),
                    pi(
                        list_ty(Tm::Var(3)),
                        id_ty(
                            list_ty(Tm::Var(3)),
                            map_(
                                Tm::Var(4),
                                Tm::Var(3),
                                Tm::Var(2),
                                append(Tm::Var(4), Tm::Var(1), Tm::Var(0)),
                            ), // map f (l1 ++ l2)
                            append(
                                Tm::Var(3),
                                map_(Tm::Var(4), Tm::Var(3), Tm::Var(2), Tm::Var(0)), // map f l2
                                map_(Tm::Var(4), Tm::Var(3), Tm::Var(2), Tm::Var(1)), // map f l1
                            ), // (map f l2) ++ (map f l1)  — SWAPPED
                        ),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(
        check(&env, &Vec::new(), &map_append(), &bad_ty),
        Err(TypeError::Mismatch),
        "map_append does NOT prove map f (l1++l2) = (map f l2)++(map f l1)  (no false-green)"
    );
}

// ════════════════════════ map_id — ∀A l. map id l = l  (functor IDENTITY law) ════════════════════════

/// map_id := λA l. List.rec A
///     (λl'. Id (List A) (map A A id l') l')                              -- motive
///     (refl (List A) (nil A))                                           -- base l'=nil
///     (λa xs ih. ap_cons A a (map A A id xs) xs ih)                     -- step
///     l                                            (id := λx:A. x)
///
/// The functor identity law `map id = id`. Induction on `l` (the list `map` recurses on).
///   Base l=nil: `map A A id nil` ι→ `nil A`, so the goal `Id (List A) (nil A) (nil A)` is closed by
///     `refl (List A) (nil A)` (DEFINITIONAL).
///   Step l=cons a xs:
///     LHS `map A A id (cons a xs)` ι→ `cons A (id a) (map A A id xs)`, and `id a = (λx.x) a` β→ `a`
///       (whnf_tm β, driver.rs:46-47), so LHS ≡ `cons A a (map A A id xs)`,
///     RHS (goal target) `cons A a xs`,
///     IH `ih : Id (List A) (map A A id xs) xs`,
///     so `ap_cons A a (map A A id xs) xs ih : Id (List A) (cons A a (map A A id xs)) (cons A a xs)`
///       ≡ the goal (the LHS endpoints match up to the β-redex `id a ≡ a`).
///     The IH is genuinely CONSUMED. The recursive ι fires on the OPEN tail `xs` because List is
///     non-indexed (driver.rs:104-119 fast-path).
fn map_id() -> Tm {
    // ctx [A,l]: A=Var1, l=Var0.
    // motive λl'. Id (List A) (map A A id l') l'.
    //   dom uses the pre-binder index (A=Var1 at ctx [A,l]); the body is under l' (A=Var2).
    let motive = lam(
        list_ty(Tm::Var(1)), // l' : List A   (A = Var1 in ctx [A,l])
        id_ty(
            list_ty(Tm::Var(2)), // List A  (A = Var2 under l')
            map_(Tm::Var(2), Tm::Var(2), idfun(Tm::Var(2)), Tm::Var(0)), // map A A id l'
            Tm::Var(0),          // l'
        ),
    );
    // base : refl (List A) (nil A)   (ctx [A,l]: A=Var1).
    let base = refl(list_ty(Tm::Var(1)), nil(Tm::Var(1)));
    // step λa.λxs.λih. ap_cons A a (map A A id xs) xs ih.
    let step = lam(
        Tm::Var(1), // a : A   (A = Var1 in ctx [A,l])
        lam(
            list_ty(Tm::Var(2)), // xs : List A  (A = Var2 in ctx [A,l,a])
            lam(
                // ih : motive xs = Id (List A) (map A A id xs) xs   (ctx [A,l,a,xs]: A=Var3, xs=Var0).
                id_ty(
                    list_ty(Tm::Var(3)),
                    map_(Tm::Var(3), Tm::Var(3), idfun(Tm::Var(3)), Tm::Var(0)),
                    Tm::Var(0),
                ),
                // ctx [A,l,a,xs,ih]: A=Var4, a=Var2, xs=Var1, ih=Var0.
                ap_cons_at(
                    Tm::Var(4),                                                  // A
                    Tm::Var(2),                                                  // a
                    map_(Tm::Var(4), Tm::Var(4), idfun(Tm::Var(4)), Tm::Var(1)), // map A A id xs
                    Tm::Var(1),                                                  // xs
                    Tm::Var(0),                                                  // ih  (CONSUMED)
                ),
            ),
        ),
    );
    let rec = apps(
        Tm::Elim(LIST),
        &[Tm::Var(1), motive, base, step, Tm::Var(0)],
    ); // param A, scrut l
    lam(Tm::Sort(0), lam(list_ty(Tm::Var(0)), rec))
}
fn map_id_ty() -> Tm {
    // Π(A:Type₀)(l:List A). Id (List A) (map A A id l) l.   (ctx [A,l]: A=Var1, l=Var0.)
    pi(
        Tm::Sort(0),
        pi(
            list_ty(Tm::Var(0)), // l : List A
            id_ty(
                list_ty(Tm::Var(1)),                                         // List A
                map_(Tm::Var(1), Tm::Var(1), idfun(Tm::Var(1)), Tm::Var(0)), // map A A id l
                Tm::Var(0),                                                  // l
            ),
        ),
    )
}

#[test]
fn map_id_typechecks() {
    // THE theorem: ∀A l. map id l = l (functor IDENTITY law) — GENERAL, machine-checked.
    // Induction on l (List.rec); base definitional; step CONSUMES the IH via ap_cons. The head
    // `id a ≡ a` collapses by β (driver.rs:46-47). Goes through on the OPEN tail because List is
    // non-indexed (nidx==0) — the open recursive field `xs` never hits the driver:106 empty-ctx infer.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &map_id(), &map_id_ty()).is_ok(),
        "map_id : Π(A)(l:List A). Id (List A) (map A A id l) l"
    );
}

#[test]
fn false_map_id_rejected() {
    // NO-FALSE-GREEN: `map_id` does NOT inhabit the (false) goal `map id l = nil` — the witness's
    // step builds a `cons`, which is NOT convertible to `nil`, so `check` rejects.
    let env = env();
    let bad_ty = pi(
        Tm::Sort(0),
        pi(
            list_ty(Tm::Var(0)),
            id_ty(
                list_ty(Tm::Var(1)),
                map_(Tm::Var(1), Tm::Var(1), idfun(Tm::Var(1)), Tm::Var(0)), // map A A id l
                nil(Tm::Var(1)), // nil A  — FALSE target
            ),
        ),
    );
    assert_eq!(
        check(&env, &Vec::new(), &map_id(), &bad_ty),
        Err(TypeError::Mismatch),
        "map_id does NOT prove map id l = nil  (no false-green)"
    );
}
