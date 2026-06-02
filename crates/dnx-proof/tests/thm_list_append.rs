//! Verified list `append` (`++`) on the dnx-proof kernel: closed computation + the GENERAL
//! associativity theorem `∀ l1 l2 l3. (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)`.
//!
//! `List A` is a PARAMETRIC inductive (param `A:Type₀`, NO indices ⇒ `nidx == 0`):
//!   nil  : List A
//!   cons : Π(a:A)(xs:List A). List A
//! Because `nidx == 0`, the ι-driver fires on OPEN scrutinees (driver.rs:104-119 fast-path) —
//! so `append` reduces under binders and the genuine inductive step below goes through. The
//! `driver.rs:106` empty-ctx infer only bites INDEXED families (`Vec`); a plain parametric
//! `List` never reaches it (thm_induction.rs:404 names the indexed gate).
//!
//! `append` recurses on the FIRST list:
//!   append := λA l1 l2. List.rec A (λ_.List A) l2 (λa xs ih. cons A a ih) l1
//!   ⇒  append A nil l2 ι→ l2 ,  append A (cons a xs) l2 ι→ cons a (append A xs l2).
//!
//! THEOREMS:
//!   • closed computation: append [a,b] [c] = [a,b,c]   (ι on closed lists; nf/conv).
//!   • app_nil_l : ∀l. nil ++ l = l                      (definitional: append nil l ι→ l)
//!   • append_assoc : ∀ l1 l2 l3. (l1++l2)++l3 = l1++(l2++l3)   (GENERAL; induction on l1,
//!     IH consumed via the J-derived congruence `ap_cons`; machine-checked by the kernel).
//!
//! NO new axioms. NO-FALSE-GREEN: off-by-one / wrong-witness companions are REJECTED.

use dnx_proof::conv::conv;
use dnx_proof::driver::nf_tm;
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::{check, TypeError};
use dnx_proof::symbol::{ConstId, IndId};
use dnx_proof::tm::Tm;

// ── term helpers ──
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

const ATOM: IndId = IndId(0); // a tiny closed element type {e0,e1,e2} to populate lists
const LIST: IndId = IndId(1);
const ID: IndId = IndId(2);
const APPEND: ConstId = ConstId(0);

// Atom = e0 | e1 | e2   (a 3-element enum; the list payload, like Color in fourcolor).
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

// List : Π(A:Type₀). Type₀  (param A, NO indices ⇒ nidx==0).
//   nil  : Π(A). List A                 (ctor 0, no fields)
//   cons : Π(A)(a:A)(xs:List A). List A (ctor 1; recursive field xs : List A, head = Ind List @ A)
fn list_ind() -> Inductive {
    Inductive {
        id: LIST,
        params: vec![Tm::Sort(0)], // A : Type₀
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
                // ctx [A]: A=Var0; field a:A=Var0; then [A,a]; field xs : List A, head Ind(List) @ A=Var1.
                args: vec![Tm::Var(0), app(Tm::Ind(LIST), Tm::Var(1))],
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

// Id : Π(A:Type₀)(a:A). A → Type₀ ; refl A a : Id A a a.
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
//   (recursion on l1; spine for a 1-param inductive: param A · motive · minor_nil · minor_cons · scrut).
fn append_body() -> Tm {
    // ctx [A,l1,l2]: A=Var2, l1=Var1, l2=Var0.
    // minor_cons : λa.λxs.λih. cons A a ih   (ctx [A,l1,l2,a,xs,ih]: A=Var5, ih=Var0).
    let minor_cons = lam(
        Tm::Var(2), // a : A   (A = Var2 in ctx [A,l1,l2])
        lam(
            list_ty(Tm::Var(3)), // xs : List A  (A = Var3 in ctx [A,l1,l2,a])
            lam(
                list_ty(Tm::Var(4)), // ih : List A  (the recursive result; A = Var4 in ctx [A,l1,l2,a,xs])
                cons(Tm::Var(5), Tm::Var(2), Tm::Var(0)), // cons A a ih  (A=Var5, a=Var2, ih=Var0)
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
    // Π(A:Type₀)(l1 l2:List A). List A.
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

fn env() -> dnx_proof::env::GlobalEnv {
    let mut e = dnx_proof::env::GlobalEnv::default();
    e.add_inductive(atom()).expect("Atom admits");
    e.add_inductive(list_ind())
        .expect("List admits (parametric inductive, positivity R3 ok)");
    e.add_inductive(id_ind()).expect("Id admits");
    e.add_const(APPEND, append_ty(), append_body())
        .expect("append admits (δ-acyclic)");
    e
}

/// `[x0;x1;…]` over Atom: nil-terminated cons chain at A:=Atom.
fn list_lit(xs: &[Tm]) -> Tm {
    xs.iter()
        .rev()
        .fold(nil(atom_ty()), |tl, hd| cons(atom_ty(), hd.clone(), tl))
}

#[test]
fn append_admits_and_computes_closed() {
    // The recursor does real list work on CLOSED data (extends a6_indexed_recursor; plan A7/A8).
    let env = env();
    let l_ab = list_lit(&[e(0), e(1)]); // [e0,e1]
    let l_c = list_lit(&[e(2)]); // [e2]
    let l_abc = list_lit(&[e(0), e(1), e(2)]); // [e0,e1,e2]
                                               // append Atom [e0,e1] [e2] ≡ [e0,e1,e2].
    assert_eq!(
        nf_tm(
            &env,
            &Vec::new(),
            &append(atom_ty(), l_ab.clone(), l_c.clone())
        ),
        nf_tm(&env, &Vec::new(), &l_abc),
        "append [e0,e1] [e2] ι-normalizes to [e0,e1,e2]"
    );
    assert!(
        conv(&env, &Vec::new(), &append(atom_ty(), l_ab, l_c), &l_abc).unwrap(),
        "append [e0,e1] [e2] ≡ [e0,e1,e2]"
    );
    // no-false-green: NOT convertible to a wrong list.
    let wrong = list_lit(&[e(0), e(1), e(0)]);
    assert!(
        !conv(
            &env,
            &Vec::new(),
            &append(atom_ty(), list_lit(&[e(0), e(1)]), list_lit(&[e(2)])),
            &wrong
        )
        .unwrap(),
        "append [e0,e1] [e2] ≢ [e0,e1,e0]"
    );
}

// ════════════════════════ app_nil_l — ∀A l. nil ++ l = l ════════════════════════

/// app_nil_l := λA l. refl (List A) l   :   Π(A)(l:List A). Id (List A) (append A (nil A) l) l.
/// `append A (nil A) l` ι→ `l` (the nil-minor), so the left-unit law is DEFINITIONAL.
fn app_nil_l() -> Tm {
    lam(
        Tm::Sort(0),
        lam(list_ty(Tm::Var(0)), refl(list_ty(Tm::Var(1)), Tm::Var(0))),
    )
}
fn app_nil_l_ty() -> Tm {
    pi(
        Tm::Sort(0),
        pi(
            list_ty(Tm::Var(0)),
            id_ty(
                list_ty(Tm::Var(1)),
                append(Tm::Var(1), nil(Tm::Var(1)), Tm::Var(0)),
                Tm::Var(0),
            ),
        ),
    )
}

#[test]
fn app_nil_l_typechecks() {
    // ∀A l. nil ++ l = l — GENERAL, definitional (ι on the nil-minor).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &app_nil_l(), &app_nil_l_ty()).is_ok(),
        "app_nil_l : Π(A)(l:List A). Id (List A) (append A nil l) l  (definitional)"
    );
}

// ════════════════════════ ap_cons — congruence of `cons a` from J ════════════════════════

/// ap_cons : Π(A:Type₀)(a:A)(xs ys:List A)(p:Id (List A) xs ys). Id (List A) (cons A a xs) (cons A a ys)
///   = λA a xs ys p. Elim Id (List A) xs (λys' q. Id (List A) (cons A a xs) (cons A a ys'))
///                            (refl (List A) (cons A a xs)) ys p
/// Derived from `Elim Id` (J) exactly as `ap_succ` (thm_induction.rs:139) / eq_prelude's eq_sym.
fn ap_cons() -> Tm {
    // ctx [A,a,xs,ys,p]: A=Var4, a=Var3, xs=Var2, ys=Var1, p=Var0.
    let motive = lam(
        list_ty(Tm::Var(4)), // ys' : List A   (A = Var4 in ctx [A,a,xs,ys,p])
        lam(
            id_ty(list_ty(Tm::Var(5)), Tm::Var(3), Tm::Var(0)), // q : Id (List A) xs ys'  (A=Var5,xs=Var3,ys'=Var0)
            id_ty(
                list_ty(Tm::Var(6)),                      // List A   (A=Var6 under ys',q)
                cons(Tm::Var(6), Tm::Var(5), Tm::Var(4)), // cons A a xs   (A=Var6,a=Var5,xs=Var4)
                cons(Tm::Var(6), Tm::Var(5), Tm::Var(1)), // cons A a ys'  (ys'=Var1)
            ),
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            list_ty(Tm::Var(4)), // A_id = List A
            Tm::Var(2),          // xs   (J based at xs)
            motive,
            refl(
                list_ty(Tm::Var(4)),
                cons(Tm::Var(4), Tm::Var(3), Tm::Var(2)),
            ), // refl (List A)(cons A a xs)
            Tm::Var(1), // index ys
            Tm::Var(0), // scrutinee p
        ],
    );
    // λA:Type₀.λa:A.λxs:List A.λys:List A.λp:Id (List A) xs ys. body
    lam(
        Tm::Sort(0),
        lam(
            Tm::Var(0), // a : A
            lam(
                list_ty(Tm::Var(1)), // xs : List A
                lam(
                    list_ty(Tm::Var(2)),                                           // ys : List A
                    lam(id_ty(list_ty(Tm::Var(3)), Tm::Var(1), Tm::Var(0)), body), // p : Id (List A) xs ys
                ),
            ),
        ),
    )
}
fn ap_cons_ty() -> Tm {
    pi(
        Tm::Sort(0),
        pi(
            Tm::Var(0), // a : A
            pi(
                list_ty(Tm::Var(1)), // xs
                pi(
                    list_ty(Tm::Var(2)), // ys
                    pi(
                        id_ty(list_ty(Tm::Var(3)), Tm::Var(1), Tm::Var(0)), // p : Id (List A) xs ys
                        id_ty(
                            list_ty(Tm::Var(4)),                      // List A
                            cons(Tm::Var(4), Tm::Var(3), Tm::Var(2)), // cons A a xs
                            cons(Tm::Var(4), Tm::Var(3), Tm::Var(1)), // cons A a ys
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
    // The step's only tool (congruence of `cons a`), pinned before the theorem.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &ap_cons(), &ap_cons_ty()).is_ok(),
        "ap_cons : Π(A)(a:A)(xs ys:List A)(p:Id (List A) xs ys). Id (List A) (cons a xs)(cons a ys)"
    );
}

// ════════════════════════ append_assoc — ∀ l1 l2 l3. (l1++l2)++l3 = l1++(l2++l3) ════════════════════════

/// append_assoc := λA l1 l2 l3. List.rec A
///     (λl1'. Id (List A) (append (append l1' l2) l3) (append l1' (append l2 l3)))   -- motive
///     (refl (List A) (append l2 l3))                                                -- base l1=nil
///     (λa xs ih. ap_cons A a (append (append xs l2) l3) (append xs (append l2 l3)) ih) -- step
///     l1
///
/// Induction on l1 (the list `append` recurses on).
///   Base l1=nil: both sides ι-reduce: `(nil++l2)++l3 ≡ l2++l3` and `nil++(l2++l3) ≡ l2++l3`,
///     so the goal is `refl (List A) (append l2 l3)` (DEFINITIONAL).
///   Step l1=cons a xs:
///     LHS `(cons a xs ++ l2) ++ l3` ι→ `cons a ((xs++l2)++l3)`,
///     RHS `cons a xs ++ (l2++l3)`   ι→ `cons a (xs++(l2++l3))`,
///     IH `ih : Id (List A) ((xs++l2)++l3) (xs++(l2++l3))`,
///     so `ap_cons … ih : Id (List A) (cons a ((xs++l2)++l3)) (cons a (xs++(l2++l3)))` ≡ the goal.
///     The IH is genuinely CONSUMED (inside `ap_cons`). The recursive ι's fire on the OPEN tail
///     `xs` because List is non-indexed (nidx==0) — the driver:106 gate does NOT bite.
fn append_assoc() -> Tm {
    // ctx [A,l1,l2,l3]: A=Var3, l1=Var2, l2=Var1, l3=Var0.
    // motive λl1'. Id (List A) (append (append l1' l2) l3) (append l1' (append l2 l3)).
    //   ctx [A,l1,l2,l3,l1']: A=Var4, l2=Var2, l3=Var1, l1'=Var0.
    let motive = lam(
        list_ty(Tm::Var(3)), // l1' : List A
        id_ty(
            list_ty(Tm::Var(4)),
            append(
                Tm::Var(4),
                append(Tm::Var(4), Tm::Var(0), Tm::Var(2)),
                Tm::Var(1),
            ), // (l1'++l2)++l3
            append(
                Tm::Var(4),
                Tm::Var(0),
                append(Tm::Var(4), Tm::Var(2), Tm::Var(1)),
            ), // l1'++(l2++l3)
        ),
    );
    // base : refl (List A) (append l2 l3)   (ctx [A,l1,l2,l3]: A=Var3, l2=Var1, l3=Var0).
    let base = refl(
        list_ty(Tm::Var(3)),
        append(Tm::Var(3), Tm::Var(1), Tm::Var(0)),
    );
    // step λa.λxs.λih. ap_cons A a ((xs++l2)++l3) (xs++(l2++l3)) ih.
    //   ctx [A,l1,l2,l3,a,xs,ih]: A=Var6, l2=Var4, l3=Var3, a=Var2, xs=Var1, ih=Var0.
    let step = lam(
        Tm::Var(3), // a : A   (A = Var3 in ctx [A,l1,l2,l3])
        lam(
            list_ty(Tm::Var(4)), // xs : List A  (A = Var4 in ctx [A,l1,l2,l3,a])
            lam(
                // ih : motive xs = Id (List A) ((xs++l2)++l3) (xs++(l2++l3))
                //   ctx [A,l1,l2,l3,a,xs]: A=Var5, l2=Var3, l3=Var2, xs=Var0.
                id_ty(
                    list_ty(Tm::Var(5)),
                    append(
                        Tm::Var(5),
                        append(Tm::Var(5), Tm::Var(0), Tm::Var(3)),
                        Tm::Var(2),
                    ),
                    append(
                        Tm::Var(5),
                        Tm::Var(0),
                        append(Tm::Var(5), Tm::Var(3), Tm::Var(2)),
                    ),
                ),
                // ctx [A,l1,l2,l3,a,xs,ih]: A=Var6, l2=Var4, l3=Var3, a=Var2, xs=Var1, ih=Var0.
                ap_cons_at(
                    Tm::Var(6), // A
                    Tm::Var(2), // a
                    append(
                        Tm::Var(6),
                        append(Tm::Var(6), Tm::Var(1), Tm::Var(4)),
                        Tm::Var(3),
                    ), // (xs++l2)++l3
                    append(
                        Tm::Var(6),
                        Tm::Var(1),
                        append(Tm::Var(6), Tm::Var(4), Tm::Var(3)),
                    ), // xs++(l2++l3)
                    Tm::Var(0), // ih  (CONSUMED)
                ),
            ),
        ),
    );
    let rec = apps(
        Tm::Elim(LIST),
        &[Tm::Var(3), motive, base, step, Tm::Var(2)],
    ); // param A, scrut l1
    lam(
        Tm::Sort(0),
        lam(
            list_ty(Tm::Var(0)),
            lam(list_ty(Tm::Var(1)), lam(list_ty(Tm::Var(2)), rec)),
        ),
    )
}
fn append_assoc_ty() -> Tm {
    // Π(A)(l1 l2 l3:List A). Id (List A) ((l1++l2)++l3) (l1++(l2++l3)).
    // ctx [A,l1,l2,l3]: A=Var3, l1=Var2, l2=Var1, l3=Var0.
    pi(
        Tm::Sort(0),
        pi(
            list_ty(Tm::Var(0)),
            pi(
                list_ty(Tm::Var(1)),
                pi(
                    list_ty(Tm::Var(2)),
                    id_ty(
                        list_ty(Tm::Var(3)),
                        append(
                            Tm::Var(3),
                            append(Tm::Var(3), Tm::Var(2), Tm::Var(1)),
                            Tm::Var(0),
                        ), // (l1++l2)++l3
                        append(
                            Tm::Var(3),
                            Tm::Var(2),
                            append(Tm::Var(3), Tm::Var(1), Tm::Var(0)),
                        ), // l1++(l2++l3)
                    ),
                ),
            ),
        ),
    )
}

#[test]
fn append_assoc_typechecks() {
    // THE theorem: ∀ l1 l2 l3. (l1++l2)++l3 = l1++(l2++l3) — GENERAL, machine-checked.
    // Induction on l1 (List.rec); base definitional; step CONSUMES the IH via ap_cons. Goes
    // through on the OPEN tail because List is non-indexed (nidx==0) — the open recursive field
    // `xs` never hits the driver:106 empty-ctx infer (that gate only bites INDEXED families).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &append_assoc(), &append_assoc_ty()).is_ok(),
        "append_assoc : Π(A)(l1 l2 l3:List A). Id (List A) ((l1++l2)++l3) (l1++(l2++l3))"
    );
}

#[test]
fn false_append_assoc_rejected() {
    // NO-FALSE-GREEN: `append_assoc` does NOT inhabit a swapped (false) goal
    // `(l1++l2)++l3 = l1++(l3++l2)` (l2,l3 swapped on the rhs inner append).
    let env = env();
    let bad_ty = pi(
        Tm::Sort(0),
        pi(
            list_ty(Tm::Var(0)),
            pi(
                list_ty(Tm::Var(1)),
                pi(
                    list_ty(Tm::Var(2)),
                    id_ty(
                        list_ty(Tm::Var(3)),
                        append(
                            Tm::Var(3),
                            append(Tm::Var(3), Tm::Var(2), Tm::Var(1)),
                            Tm::Var(0),
                        ),
                        append(
                            Tm::Var(3),
                            Tm::Var(2),
                            append(Tm::Var(3), Tm::Var(0), Tm::Var(1)),
                        ), // l1++(l3++l2)
                    ),
                ),
            ),
        ),
    );
    assert_eq!(
        check(&env, &Vec::new(), &append_assoc(), &bad_ty),
        Err(TypeError::Mismatch),
        "append_assoc does NOT prove (l1++l2)++l3 = l1++(l3++l2)  (no false-green)"
    );
}
