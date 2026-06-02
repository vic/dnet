//! Verified list `reverse` and its INVOLUTION law `∀A (l:List A). reverse (reverse l) = l` on the
//! dnx-proof kernel. This is the deepest list theorem here: it needs a small equational toolkit
//! (`sym`, `trans`, congruences `ap_cons` / `ap_append_l`, all J-derived from `Elim Id`) plus three
//! sub-lemmas proved by induction in this same file:
//!   • append_nil_r   : ∀A l.        l ++ nil = l                                   (append right-id)
//!   • append_assoc   : ∀A l1 l2 l3. (l1++l2)++l3 = l1++(l2++l3)                     (append assoc)
//!   • reverse_append : ∀A l1 l2.    reverse (l1++l2) = (reverse l2) ++ (reverse l1) (anti-distrib)
//! and finally
//!   • reverse_involution : ∀A l. reverse (reverse l) = l.
//!
//! `reverse` is a SNOC-style left fold built from `append` (same `List.rec` cross-recursion idiom as
//! `map`/`length`, thm_map_append.rs:13 / thm_length_append.rs:13):
//!   reverse := λA l. List.rec A (λ_:List A. List A) (nil A) (λa tl ih. ih ++ (cons A a (nil A))) l
//!     ⇒  reverse nil ι→ nil A ,  reverse (cons a tl) ι→ (reverse tl) ++ (cons A a (nil A)).
//!
//! append := λA l1 l2. List.rec A (λ_:List A. List A) l2 (λa xs ih. cons A a ih) l1   (recursion on
//! l1; thm_map_append.rs:128-167), so  nil++l ι→ l  and  (cons a xs)++l ι→ cons a (xs++l).
//!
//! `List` and `Id` are non-indexed in their LIST-payload here (`List` has `nidx == 0`), so the
//! ι-driver fires on OPEN scrutinees (driver.rs:104-119 fast-path) and every inductive step reduces
//! under binders — the `driver.rs:106` empty-ctx infer (which only bites INDEXED families) never
//! engages on the `List`/`append`/`reverse` recursions.
//!
//! THEOREMS (machine-checked by the trusted kernel `check`; the kernel is the oracle):
//!   • closed computation: reverse [a,b,c] = [c,b,a]   and   reverse (reverse [a,b]) = [a,b]
//!     (ι on closed lists; nf/conv).
//!   • the four ∀-quantified laws above (induction; each step CONSUMES its IH via the J-congruences).
//!
//! NO new axioms — `sym`/`trans`/`ap_cons`/`ap_append_l` are all derived from `Elim Id` (J).
//! NO-FALSE-GREEN: a wrong involution rhs is REJECTED by `check`, with a POSITIVE control proving
//! the rejection is a genuine mismatch (non-vacuity), not a typo.

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
const APPEND: ConstId = ConstId(0);
const REVERSE: ConstId = ConstId(1);

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

// append := λA l1 l2. List.rec A (λ_:List A. List A) l2 (λa xs ih. cons A a ih) l1
//   (recursion on l1; thm_map_append.rs:128-167).
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

// reverse := λA l. List.rec A (λ_:List A. List A) (nil A) (λa tl ih. ih ++ (cons A a (nil A))) l
//   (recursion on l; SNOC-style left fold built from `append`). Motive is the CONSTANT `List A`, so
//   the result is non-indexed and ι fires on open scrutinees.
fn reverse_body() -> Tm {
    // ctx [A,l]: A=Var1, l=Var0.
    // minor_cons : λa.λtl.λih. ih ++ (cons A a (nil A))   (ctx [A,l,a,tl,ih]: A=Var4, a=Var2, ih=Var0).
    let minor_cons = lam(
        Tm::Var(1), // a : A   (A = Var1 in ctx [A,l])
        lam(
            list_ty(Tm::Var(2)), // tl : List A  (A = Var2 in ctx [A,l,a])
            lam(
                list_ty(Tm::Var(3)), // ih : List A  (A = Var3 in ctx [A,l,a,tl])
                append(
                    Tm::Var(4),                                    // A
                    Tm::Var(0),                                    // ih
                    cons(Tm::Var(4), Tm::Var(2), nil(Tm::Var(4))), // cons A a (nil A)
                ),
            ),
        ),
    );
    let elim = apps(
        Tm::Elim(LIST),
        &[
            Tm::Var(1),                                    // param A
            lam(list_ty(Tm::Var(1)), list_ty(Tm::Var(2))), // motive λ_:List A. List A
            nil(Tm::Var(1)),                               // minor_nil = nil A
            minor_cons,
            Tm::Var(0), // scrutinee = l
        ],
    );
    lam(Tm::Sort(0), lam(list_ty(Tm::Var(0)), elim))
}
fn reverse_ty() -> Tm {
    // Π(A:Type₀)(l:List A). List A.
    pi(Tm::Sort(0), pi(list_ty(Tm::Var(0)), list_ty(Tm::Var(1))))
}
fn reverse(a_ty: Tm, l: Tm) -> Tm {
    apps(Tm::Const(REVERSE), &[a_ty, l])
}

fn env() -> dnx_proof::env::GlobalEnv {
    let mut e = dnx_proof::env::GlobalEnv::default();
    e.add_inductive(atom()).expect("Atom admits");
    e.add_inductive(list_ind())
        .expect("List admits (parametric inductive, positivity R3 ok)");
    e.add_inductive(id_ind()).expect("Id admits");
    e.add_const(APPEND, append_ty(), append_body())
        .expect("append admits (δ-acyclic)");
    e.add_const(REVERSE, reverse_ty(), reverse_body())
        .expect("reverse admits (δ-acyclic, built on append)");
    e
}

/// `[x0;x1;…]` over Atom.
fn list_lit(xs: &[Tm]) -> Tm {
    xs.iter()
        .rev()
        .fold(nil(atom_ty()), |tl, hd| cons(atom_ty(), hd.clone(), tl))
}

#[test]
fn reverse_admits_and_computes_closed() {
    // reverse [e0,e1,e2] ι-normalizes to [e2,e1,e0] — the snoc fold flips the list.
    let env = env();
    let input = list_lit(&[e(0), e(1), e(2)]); // [e0,e1,e2]
    let want = list_lit(&[e(2), e(1), e(0)]); // [e2,e1,e0]
    assert_eq!(
        nf_tm(&env, &Vec::new(), &reverse(atom_ty(), input.clone())),
        nf_tm(&env, &Vec::new(), &want),
        "reverse [e0,e1,e2] ι→ [e2,e1,e0]"
    );
    assert!(
        conv(&env, &Vec::new(), &reverse(atom_ty(), input), &want).unwrap(),
        "reverse [e0,e1,e2] ≡ [e2,e1,e0]"
    );
    // closed involution sanity: reverse (reverse [e0,e1]) ≡ [e0,e1].
    let ab = list_lit(&[e(0), e(1)]);
    assert!(
        conv(
            &env,
            &Vec::new(),
            &reverse(atom_ty(), reverse(atom_ty(), ab.clone())),
            &ab
        )
        .unwrap(),
        "reverse (reverse [e0,e1]) ≡ [e0,e1]"
    );
    // no-false-green: reverse [e0,e1,e2] is NOT the identity (distinct heads ⇒ flip is observable).
    assert!(
        !conv(
            &env,
            &Vec::new(),
            &reverse(atom_ty(), list_lit(&[e(0), e(1), e(2)])),
            &list_lit(&[e(0), e(1), e(2)])
        )
        .unwrap(),
        "reverse [e0,e1,e2] ≢ [e0,e1,e2]"
    );
}

// ════════════════════════ J-derived equational toolkit (sym / trans / congruences) ════════════════════════

/// sym : Π(A:Type₀)(x y:A)(p:Id A x y). Id A y x.   (Elim Id; vary `y`, refl-case at y:=x.)
fn sym() -> Tm {
    // ctx [A,x,y,p]: A=Var3, x=Var2, y=Var1, p=Var0.
    // motive λy'.λq:Id A x y'. Id A y' x.   ctx [A,x,y,p,y']: A=Var4, x=Var3, y'=Var0.
    let motive = lam(
        Tm::Var(3), // y' : A
        lam(
            id_ty(Tm::Var(4), Tm::Var(3), Tm::Var(0)), // q : Id A x y'
            // ctx [A,x,y,p,y',q]: A=Var5, x=Var4, y'=Var1.
            id_ty(Tm::Var(5), Tm::Var(1), Tm::Var(4)), // Id A y' x
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            Tm::Var(3), // A_id = A
            Tm::Var(2), // base point x
            motive,
            refl(Tm::Var(3), Tm::Var(2)), // refl A x : motive x (refl A x) = Id A x x
            Tm::Var(1),                   // index y
            Tm::Var(0),                   // scrutinee p
        ],
    );
    lam(
        Tm::Sort(0),
        lam(
            Tm::Var(0), // x : A
            lam(
                Tm::Var(1),                                           // y : A
                lam(id_ty(Tm::Var(2), Tm::Var(1), Tm::Var(0)), body), // p : Id A x y
            ),
        ),
    )
}
fn sym_ty() -> Tm {
    pi(
        Tm::Sort(0),
        pi(
            Tm::Var(0),
            pi(
                Tm::Var(1),
                pi(
                    id_ty(Tm::Var(2), Tm::Var(1), Tm::Var(0)),
                    id_ty(Tm::Var(3), Tm::Var(1), Tm::Var(2)), // Id A y x
                ),
            ),
        ),
    )
}
fn sym_at(a_ty: Tm, x: Tm, y: Tm, p: Tm) -> Tm {
    apps(sym(), &[a_ty, x, y, p])
}

/// trans : Π(A:Type₀)(x y z:A)(p:Id A x y)(q:Id A y z). Id A x z.
///   (Elim Id on `q`; vary `z`, refl-case at z:=y returns `p`.)
fn trans() -> Tm {
    // ctx [A,x,y,z,p,q]: A=Var5, x=Var4, y=Var3, z=Var2, p=Var1, q=Var0.
    // motive λz'.λr:Id A y z'. Id A x z'.   ctx [A,x,y,z,p,q,z']: A=Var6, x=Var5, y=Var4, z'=Var0.
    let motive = lam(
        Tm::Var(5), // z' : A
        lam(
            id_ty(Tm::Var(6), Tm::Var(4), Tm::Var(0)), // r : Id A y z'
            // ctx [...,z',r]: A=Var7, x=Var6, z'=Var1.
            id_ty(Tm::Var(7), Tm::Var(6), Tm::Var(1)), // Id A x z'
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            Tm::Var(5), // A_id = A
            Tm::Var(3), // base point y
            motive,
            Tm::Var(1), // refl-case (motive y (refl A y) = Id A x y) := p
            Tm::Var(2), // index z
            Tm::Var(0), // scrutinee q
        ],
    );
    lam(
        Tm::Sort(0),
        lam(
            Tm::Var(0), // x : A
            lam(
                Tm::Var(1), // y : A
                lam(
                    Tm::Var(2), // z : A
                    lam(
                        id_ty(Tm::Var(3), Tm::Var(2), Tm::Var(1)), // p : Id A x y
                        lam(id_ty(Tm::Var(4), Tm::Var(2), Tm::Var(1)), body), // q : Id A y z
                    ),
                ),
            ),
        ),
    )
}
fn trans_ty() -> Tm {
    pi(
        Tm::Sort(0),
        pi(
            Tm::Var(0),
            pi(
                Tm::Var(1),
                pi(
                    Tm::Var(2),
                    pi(
                        id_ty(Tm::Var(3), Tm::Var(2), Tm::Var(1)), // Id A x y
                        pi(
                            id_ty(Tm::Var(4), Tm::Var(2), Tm::Var(1)), // Id A y z
                            id_ty(Tm::Var(5), Tm::Var(4), Tm::Var(2)), // Id A x z
                        ),
                    ),
                ),
            ),
        ),
    )
}
fn trans_at(a_ty: Tm, x: Tm, y: Tm, z: Tm, p: Tm, q: Tm) -> Tm {
    apps(trans(), &[a_ty, x, y, z, p, q])
}

/// ap_cons : Π(A:Type₀)(a:A)(xs ys:List A)(p:Id (List A) xs ys). Id (List A) (cons A a xs)(cons A a ys)
///   (J / Elim Id; identical to thm_map_append.rs:362-424).
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
fn ap_cons_at(a_ty: Tm, a: Tm, xs: Tm, ys: Tm, p: Tm) -> Tm {
    apps(ap_cons(), &[a_ty, a, xs, ys, p])
}

/// ap_append_l : Π(A:Type₀)(xs ys zs:List A)(p:Id (List A) xs ys).
///                  Id (List A) (xs ++ zs) (ys ++ zs).
///   Congruence of `(· ++ zs)` in its LEFT argument (J / Elim Id; vary `ys`, refl-case at ys:=xs).
fn ap_append_l() -> Tm {
    // ctx [A,xs,ys,zs,p]: A=Var4, xs=Var3, ys=Var2, zs=Var1, p=Var0.
    // motive λys'.λq:Id (List A) xs ys'. Id (List A) (xs++zs) (ys'++zs).
    //   ctx [A,xs,ys,zs,p,ys']: A=Var5, xs=Var4, zs=Var2, ys'=Var0.
    let motive = lam(
        list_ty(Tm::Var(4)), // ys' : List A
        lam(
            id_ty(list_ty(Tm::Var(5)), Tm::Var(4), Tm::Var(0)), // q : Id (List A) xs ys'
            // ctx [...,ys',q]: A=Var6, xs=Var5, zs=Var3, ys'=Var1.
            id_ty(
                list_ty(Tm::Var(6)),
                append(Tm::Var(6), Tm::Var(5), Tm::Var(3)), // xs ++ zs
                append(Tm::Var(6), Tm::Var(1), Tm::Var(3)), // ys' ++ zs
            ),
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            list_ty(Tm::Var(4)), // A_id = List A
            Tm::Var(3),          // base point xs
            motive,
            refl(
                list_ty(Tm::Var(4)),
                append(Tm::Var(4), Tm::Var(3), Tm::Var(1)), // refl (List A)(xs ++ zs)
            ),
            Tm::Var(2), // index ys
            Tm::Var(0), // scrutinee p
        ],
    );
    lam(
        Tm::Sort(0),
        lam(
            list_ty(Tm::Var(0)), // xs
            lam(
                list_ty(Tm::Var(1)), // ys
                lam(
                    list_ty(Tm::Var(2)),                                           // zs
                    lam(id_ty(list_ty(Tm::Var(3)), Tm::Var(2), Tm::Var(1)), body), // p
                ),
            ),
        ),
    )
}
fn ap_append_l_ty() -> Tm {
    pi(
        Tm::Sort(0),
        pi(
            list_ty(Tm::Var(0)), // xs
            pi(
                list_ty(Tm::Var(1)), // ys
                pi(
                    list_ty(Tm::Var(2)), // zs
                    pi(
                        id_ty(list_ty(Tm::Var(3)), Tm::Var(2), Tm::Var(1)), // p : Id (List A) xs ys
                        id_ty(
                            list_ty(Tm::Var(4)),
                            append(Tm::Var(4), Tm::Var(3), Tm::Var(1)), // xs ++ zs
                            append(Tm::Var(4), Tm::Var(2), Tm::Var(1)), // ys ++ zs
                        ),
                    ),
                ),
            ),
        ),
    )
}
fn ap_append_l_at(a_ty: Tm, xs: Tm, ys: Tm, zs: Tm, p: Tm) -> Tm {
    apps(ap_append_l(), &[a_ty, xs, ys, zs, p])
}

#[test]
fn toolkit_typechecks() {
    let env = env();
    assert!(
        check(&env, &Vec::new(), &sym(), &sym_ty()).is_ok(),
        "sym : Π(A)(x y:A)(p:Id A x y). Id A y x"
    );
    assert!(
        check(&env, &Vec::new(), &trans(), &trans_ty()).is_ok(),
        "trans : Π(A)(x y z:A)(p:Id A x y)(q:Id A y z). Id A x z"
    );
    assert!(
        check(&env, &Vec::new(), &ap_cons(), &ap_cons_ty()).is_ok(),
        "ap_cons : Π(A)(a:A)(xs ys:List A)(p:Id (List A) xs ys). Id (List A) (cons a xs)(cons a ys)"
    );
    assert!(
        check(&env, &Vec::new(), &ap_append_l(), &ap_append_l_ty()).is_ok(),
        "ap_append_l : Π(A)(xs ys zs:List A)(p:Id (List A) xs ys). Id (List A) (xs++zs)(ys++zs)"
    );
}

// ════════════════════════ append_nil_r — ∀A l. l ++ nil = l ════════════════════════

/// append_nil_r := λA l. List.rec A
///     (λl'. Id (List A) (l' ++ nil) l')                       -- motive
///     (refl (List A) (nil A))                                 -- base l'=nil  (nil++nil ι→ nil)
///     (λa xs ih. ap_cons A a (xs++nil) xs ih)                 -- step
///     l
///
/// Induction on l. Base: `nil ++ nil` ι→ `nil`, goal `Id (nil) (nil)` = refl. Step l=cons a xs:
///   `(cons a xs) ++ nil` ι→ `cons a (xs ++ nil)`; target `cons a xs`; IH `xs++nil = xs`; so
///   `ap_cons A a (xs++nil) xs ih` closes it. IH genuinely CONSUMED; ι fires on the open tail `xs`.
fn append_nil_r() -> Tm {
    // ctx [A,l]: A=Var1, l=Var0.
    // motive λl'. Id (List A) (l'++nil) l'.   ctx [A,l,l']: A=Var2, l'=Var0.
    let motive = lam(
        list_ty(Tm::Var(1)), // l' : List A  (A = Var1 in ctx [A,l])
        id_ty(
            list_ty(Tm::Var(2)),                             // List A  (A = Var2 under l')
            append(Tm::Var(2), Tm::Var(0), nil(Tm::Var(2))), // l' ++ nil
            Tm::Var(0),                                      // l'
        ),
    );
    // base : refl (List A) (nil A)   (ctx [A,l]: A=Var1).
    let base = refl(list_ty(Tm::Var(1)), nil(Tm::Var(1)));
    // step λa.λxs.λih. ap_cons A a (xs++nil) xs ih.
    let step = lam(
        Tm::Var(1), // a : A   (A = Var1 in ctx [A,l])
        lam(
            list_ty(Tm::Var(2)), // xs : List A  (A = Var2 in ctx [A,l,a])
            lam(
                // ih : motive xs = Id (List A) (xs++nil) xs.   ctx [A,l,a,xs]: A=Var3, xs=Var0.
                id_ty(
                    list_ty(Tm::Var(3)),
                    append(Tm::Var(3), Tm::Var(0), nil(Tm::Var(3))),
                    Tm::Var(0),
                ),
                // ctx [A,l,a,xs,ih]: A=Var4, a=Var2, xs=Var1, ih=Var0.
                ap_cons_at(
                    Tm::Var(4),                                      // A
                    Tm::Var(2),                                      // a
                    append(Tm::Var(4), Tm::Var(1), nil(Tm::Var(4))), // xs ++ nil
                    Tm::Var(1),                                      // xs
                    Tm::Var(0),                                      // ih  (CONSUMED)
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
fn append_nil_r_ty() -> Tm {
    // Π(A:Type₀)(l:List A). Id (List A) (l ++ nil) l.   ctx [A,l]: A=Var1, l=Var0.
    pi(
        Tm::Sort(0),
        pi(
            list_ty(Tm::Var(0)), // l : List A
            id_ty(
                list_ty(Tm::Var(1)),
                append(Tm::Var(1), Tm::Var(0), nil(Tm::Var(1))), // l ++ nil
                Tm::Var(0),                                      // l
            ),
        ),
    )
}
/// `append_nil_r A l : Id (List A) (l ++ nil) l`  (concrete instance).
fn append_nil_r_at(a_ty: Tm, l: Tm) -> Tm {
    apps(append_nil_r(), &[a_ty, l])
}

#[test]
fn append_nil_r_typechecks() {
    let env = env();
    assert!(
        check(&env, &Vec::new(), &append_nil_r(), &append_nil_r_ty()).is_ok(),
        "append_nil_r : Π(A)(l:List A). Id (List A) (l ++ nil) l"
    );
}

// ════════════════════════ append_assoc — ∀A l1 l2 l3. (l1++l2)++l3 = l1++(l2++l3) ════════════════════════

/// append_assoc := λA l1 l2 l3. List.rec A
///     (λl1'. Id (List A) ((l1'++l2)++l3) (l1'++(l2++l3)))                  -- motive
///     (refl (List A) (l2++l3))                                             -- base l1'=nil
///     (λa xs ih. ap_cons A a ((xs++l2)++l3) (xs++(l2++l3)) ih)             -- step
///     l1
///
/// Induction on l1. Base l1'=nil: `(nil++l2)++l3` ι→ `l2++l3`; `nil++(l2++l3)` ι→ `l2++l3` — both
///   ι to `l2++l3`, goal = refl. Step l1'=cons a xs:
///   LHS `((cons a xs)++l2)++l3` ι→ `(cons a (xs++l2))++l3` ι→ `cons a ((xs++l2)++l3)`,
///   RHS `(cons a xs)++(l2++l3)` ι→ `cons a (xs++(l2++l3))`,
///   IH `(xs++l2)++l3 = xs++(l2++l3)`; so `ap_cons A a … ih` closes it. IH CONSUMED; ι on open `xs`.
fn append_assoc() -> Tm {
    // ctx [A,l1,l2,l3]: A=Var3, l1=Var2, l2=Var1, l3=Var0.
    // motive λl1'. Id (List A) ((l1'++l2)++l3) (l1'++(l2++l3)).
    //   ctx [A,l1,l2,l3,l1']: A=Var4, l2=Var2, l3=Var1, l1'=Var0.
    let motive = lam(
        list_ty(Tm::Var(3)), // l1' : List A  (A = Var3 in ctx [A,l1,l2,l3])
        id_ty(
            list_ty(Tm::Var(4)), // List A
            append(
                Tm::Var(4),
                append(Tm::Var(4), Tm::Var(0), Tm::Var(2)), // l1' ++ l2
                Tm::Var(1),                                 // l3
            ), // (l1'++l2)++l3
            append(
                Tm::Var(4),
                Tm::Var(0),                                 // l1'
                append(Tm::Var(4), Tm::Var(2), Tm::Var(1)), // l2 ++ l3
            ), // l1'++(l2++l3)
        ),
    );
    // base : refl (List A) (l2++l3).   ctx [A,l1,l2,l3]: A=Var3, l2=Var1, l3=Var0.
    let base = refl(
        list_ty(Tm::Var(3)),
        append(Tm::Var(3), Tm::Var(1), Tm::Var(0)),
    );
    // step λa.λxs.λih. ap_cons A a ((xs++l2)++l3) (xs++(l2++l3)) ih.
    let step = lam(
        Tm::Var(3), // a : A   (A = Var3 in ctx [A,l1,l2,l3])
        lam(
            list_ty(Tm::Var(4)), // xs : List A  (A = Var4 in ctx [A,l1,l2,l3,a])
            lam(
                // ih : motive xs = Id (List A) ((xs++l2)++l3) (xs++(l2++l3)).
                //   ctx [A,l1,l2,l3,a,xs]: A=Var5, l2=Var3, l3=Var2, xs=Var0.
                id_ty(
                    list_ty(Tm::Var(5)),
                    append(
                        Tm::Var(5),
                        append(Tm::Var(5), Tm::Var(0), Tm::Var(3)), // xs ++ l2
                        Tm::Var(2),                                 // l3
                    ),
                    append(
                        Tm::Var(5),
                        Tm::Var(0),                                 // xs
                        append(Tm::Var(5), Tm::Var(3), Tm::Var(2)), // l2 ++ l3
                    ),
                ),
                // ctx [A,l1,l2,l3,a,xs,ih]: A=Var6, l2=Var4, l3=Var3, a=Var2, xs=Var1, ih=Var0.
                ap_cons_at(
                    Tm::Var(6), // A
                    Tm::Var(2), // a
                    append(
                        Tm::Var(6),
                        append(Tm::Var(6), Tm::Var(1), Tm::Var(4)), // xs ++ l2
                        Tm::Var(3),                                 // l3
                    ), // (xs++l2)++l3
                    append(
                        Tm::Var(6),
                        Tm::Var(1),                                 // xs
                        append(Tm::Var(6), Tm::Var(4), Tm::Var(3)), // l2 ++ l3
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
            list_ty(Tm::Var(0)), // l1 : List A
            lam(
                list_ty(Tm::Var(1)),           // l2 : List A
                lam(list_ty(Tm::Var(2)), rec), // l3 : List A
            ),
        ),
    )
}
fn append_assoc_ty() -> Tm {
    // Π(A:Type₀)(l1 l2 l3:List A). Id (List A) ((l1++l2)++l3) (l1++(l2++l3)).
    // ctx [A,l1,l2,l3]: A=Var3, l1=Var2, l2=Var1, l3=Var0.
    pi(
        Tm::Sort(0),
        pi(
            list_ty(Tm::Var(0)), // l1
            pi(
                list_ty(Tm::Var(1)), // l2
                pi(
                    list_ty(Tm::Var(2)), // l3
                    id_ty(
                        list_ty(Tm::Var(3)),
                        append(
                            Tm::Var(3),
                            append(Tm::Var(3), Tm::Var(2), Tm::Var(1)), // l1 ++ l2
                            Tm::Var(0),                                 // l3
                        ), // (l1++l2)++l3
                        append(
                            Tm::Var(3),
                            Tm::Var(2),                                 // l1
                            append(Tm::Var(3), Tm::Var(1), Tm::Var(0)), // l2 ++ l3
                        ), // l1++(l2++l3)
                    ),
                ),
            ),
        ),
    )
}
/// `append_assoc A l1 l2 l3 : Id (List A) ((l1++l2)++l3) (l1++(l2++l3))`  (concrete instance).
fn append_assoc_at(a_ty: Tm, l1: Tm, l2: Tm, l3: Tm) -> Tm {
    apps(append_assoc(), &[a_ty, l1, l2, l3])
}

#[test]
fn append_assoc_typechecks() {
    let env = env();
    assert!(
        check(&env, &Vec::new(), &append_assoc(), &append_assoc_ty()).is_ok(),
        "append_assoc : Π(A)(l1 l2 l3:List A). Id (List A) ((l1++l2)++l3) (l1++(l2++l3))"
    );
}

// ════════════════════════ reverse_append — ∀A l1 l2. reverse (l1++l2) = (reverse l2)++(reverse l1) ════════════════════════

/// reverse_append := λA l1 l2. List.rec A
///     (λl1'. Id (List A) (reverse (l1'++l2)) ((reverse l2) ++ (reverse l1')))     -- motive
///     base                                                                        -- l1'=nil
///     step                                                                        -- l1'=cons a xs
///     l1
///
/// Induction on l1.
///   Base l1'=nil: LHS `reverse (nil++l2)` ι→ `reverse l2`; RHS `(reverse l2)++(reverse nil)`
///     ι→ `(reverse l2) ++ nil`. These differ! `append_nil_r (reverse l2) : (reverse l2)++nil =
///     reverse l2`, so `sym (…)` : `reverse l2 = (reverse l2)++nil` is the base witness.
///   Step l1'=cons a xs:
///     LHS `reverse ((cons a xs)++l2)` ι→ `reverse (cons a (xs++l2))` ι→ `reverse(xs++l2) ++ (cons a nil)`,
///     RHS `(reverse l2) ++ (reverse (cons a xs))` ι→ `(reverse l2) ++ ((reverse xs) ++ (cons a nil))`,
///     IH `ih : reverse(xs++l2) = (reverse l2) ++ (reverse xs)`.
///     Chain (over List A, with `S := cons a nil`):
///       reverse(xs++l2) ++ S
///         =⟨ ap_append_l (reverse(xs++l2)) ((reverse l2)++(reverse xs)) S ih ⟩   -- congruence in left arg
///       ((reverse l2)++(reverse xs)) ++ S
///         =⟨ append_assoc (reverse l2) (reverse xs) S ⟩                          -- reassociate
///       (reverse l2) ++ ((reverse xs) ++ S)        ≡ RHS.
///     i.e. `trans (ap_append_l … ih) (append_assoc …)` closes the goal. IH genuinely CONSUMED; the
///     recursive ι's fire on the OPEN tail `xs` (List non-indexed, driver.rs:104-119 fast-path).
fn reverse_append() -> Tm {
    // ctx [A,l1,l2]: A=Var2, l1=Var1, l2=Var0.
    // motive λl1'. Id (List A) (reverse (l1'++l2)) ((reverse l2)++(reverse l1')).
    //   ctx [A,l1,l2,l1']: A=Var3, l2=Var1, l1'=Var0.
    let motive = lam(
        list_ty(Tm::Var(2)), // l1' : List A  (A = Var2 in ctx [A,l1,l2])
        id_ty(
            list_ty(Tm::Var(3)),                                             // List A
            reverse(Tm::Var(3), append(Tm::Var(3), Tm::Var(0), Tm::Var(1))), // reverse (l1' ++ l2)
            append(
                Tm::Var(3),
                reverse(Tm::Var(3), Tm::Var(1)), // reverse l2
                reverse(Tm::Var(3), Tm::Var(0)), // reverse l1'
            ), // (reverse l2) ++ (reverse l1')
        ),
    );
    // base : sym (List A) ((reverse l2)++nil) (reverse l2) (append_nil_r A (reverse l2))
    //   : Id (List A) (reverse l2) ((reverse l2)++nil).   ctx [A,l1,l2]: A=Var2, l2=Var0.
    let base = sym_at(
        list_ty(Tm::Var(2)),
        append(Tm::Var(2), reverse(Tm::Var(2), Tm::Var(0)), nil(Tm::Var(2))), // (reverse l2)++nil
        reverse(Tm::Var(2), Tm::Var(0)),                                      // reverse l2
        append_nil_r_at(Tm::Var(2), reverse(Tm::Var(2), Tm::Var(0))), // (reverse l2)++nil = reverse l2
    );
    // step λa.λxs.λih. trans (ap_append_l … ih) (append_assoc …).
    let step = lam(
        Tm::Var(2), // a : A   (A = Var2 in ctx [A,l1,l2])
        lam(
            list_ty(Tm::Var(3)), // xs : List A  (A = Var3 in ctx [A,l1,l2,a])
            lam(
                // ih : motive xs = Id (List A) (reverse(xs++l2)) ((reverse l2)++(reverse xs)).
                //   ctx [A,l1,l2,a,xs]: A=Var4, l2=Var2, xs=Var0.
                id_ty(
                    list_ty(Tm::Var(4)),
                    reverse(Tm::Var(4), append(Tm::Var(4), Tm::Var(0), Tm::Var(2))), // reverse (xs ++ l2)
                    append(
                        Tm::Var(4),
                        reverse(Tm::Var(4), Tm::Var(2)), // reverse l2
                        reverse(Tm::Var(4), Tm::Var(0)), // reverse xs
                    ),
                ),
                // ctx [A,l1,l2,a,xs,ih]: A=Var5, l2=Var3, a=Var2, xs=Var1, ih=Var0.
                // S := cons A a (nil A).
                // The three Id endpoints, all over List A:
                //   X := reverse(xs++l2) ++ S          (= LHS, after ι on reverse(cons a (xs++l2)))
                //   Y := ((reverse l2)++(reverse xs)) ++ S
                //   Z := (reverse l2) ++ ((reverse xs) ++ S)   (≡ RHS after ι on reverse(cons a xs))
                {
                    // helper sub-terms in ctx [A,l1,l2,a,xs,ih]: A=Var5, l2=Var3, a=Var2, xs=Var1.
                    let s_lit = cons(Tm::Var(5), Tm::Var(2), nil(Tm::Var(5))); // cons A a (nil A)
                    let rev_xs_l2 = reverse(Tm::Var(5), append(Tm::Var(5), Tm::Var(1), Tm::Var(3))); // reverse (xs ++ l2)
                    let rev_l2 = reverse(Tm::Var(5), Tm::Var(3)); // reverse l2
                    let rev_xs = reverse(Tm::Var(5), Tm::Var(1)); // reverse xs
                    let rl2_app_rxs = append(Tm::Var(5), rev_l2.clone(), rev_xs.clone()); // (reverse l2)++(reverse xs)
                    let x = append(Tm::Var(5), rev_xs_l2.clone(), s_lit.clone());
                    let y = append(Tm::Var(5), rl2_app_rxs.clone(), s_lit.clone());
                    let z = append(
                        Tm::Var(5),
                        rev_l2.clone(),
                        append(Tm::Var(5), rev_xs.clone(), s_lit.clone()),
                    );
                    // step1 : Id (List A) X Y   via ap_append_l in the left arg, fed the IH.
                    let step1 = ap_append_l_at(
                        Tm::Var(5),          // A
                        rev_xs_l2.clone(),   // xs-arg = reverse(xs++l2)
                        rl2_app_rxs.clone(), // ys-arg = (reverse l2)++(reverse xs)
                        s_lit.clone(),       // zs-arg = S
                        Tm::Var(0), // p = ih : reverse(xs++l2) = (reverse l2)++(reverse xs)
                    );
                    // step2 : Id (List A) Y Z   via append_assoc (reverse l2)(reverse xs) S.
                    let step2 =
                        append_assoc_at(Tm::Var(5), rev_l2.clone(), rev_xs.clone(), s_lit.clone());
                    trans_at(list_ty(Tm::Var(5)), x, y, z, step1, step2)
                },
            ),
        ),
    );
    let rec = apps(
        Tm::Elim(LIST),
        &[Tm::Var(2), motive, base, step, Tm::Var(1)],
    ); // param A, scrut l1
    lam(
        Tm::Sort(0),
        lam(
            list_ty(Tm::Var(0)),           // l1 : List A
            lam(list_ty(Tm::Var(1)), rec), // l2 : List A
        ),
    )
}
fn reverse_append_ty() -> Tm {
    // Π(A:Type₀)(l1 l2:List A). Id (List A) (reverse (l1++l2)) ((reverse l2)++(reverse l1)).
    // ctx [A,l1,l2]: A=Var2, l1=Var1, l2=Var0.
    pi(
        Tm::Sort(0),
        pi(
            list_ty(Tm::Var(0)), // l1
            pi(
                list_ty(Tm::Var(1)), // l2
                id_ty(
                    list_ty(Tm::Var(2)),
                    reverse(Tm::Var(2), append(Tm::Var(2), Tm::Var(1), Tm::Var(0))), // reverse (l1 ++ l2)
                    append(
                        Tm::Var(2),
                        reverse(Tm::Var(2), Tm::Var(0)), // reverse l2
                        reverse(Tm::Var(2), Tm::Var(1)), // reverse l1
                    ), // (reverse l2) ++ (reverse l1)
                ),
            ),
        ),
    )
}
/// `reverse_append A l1 l2 : Id (List A) (reverse (l1++l2)) ((reverse l2)++(reverse l1))`.
fn reverse_append_at(a_ty: Tm, l1: Tm, l2: Tm) -> Tm {
    apps(reverse_append(), &[a_ty, l1, l2])
}

#[test]
fn reverse_append_typechecks() {
    // Helper lemma: ∀A l1 l2. reverse (l1++l2) = (reverse l2) ++ (reverse l1) — GENERAL, machine-checked.
    // Induction on l1; base uses `sym (append_nil_r (reverse l2))`; step CHAINS `ap_append_l` (fed the
    // IH) with `append_assoc` via `trans`. Goes through on the OPEN tail because List is non-indexed.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &reverse_append(), &reverse_append_ty()).is_ok(),
        "reverse_append : Π(A)(l1 l2). Id (List A) (reverse (l1++l2)) ((reverse l2)++(reverse l1))"
    );
}

// ════════════════════════ reverse_involution — ∀A l. reverse (reverse l) = l ════════════════════════

/// reverse_involution := λA l. List.rec A
///     (λl'. Id (List A) (reverse (reverse l')) l')                                  -- motive
///     (refl (List A) (nil A))                                                       -- base l'=nil
///     (λa xs ih. trans (reverse_append A (reverse xs) (cons a nil))
///                      (ap_cons A a (reverse (reverse xs)) xs ih))                  -- step
///     l
///
/// Induction on l.
///   Base l'=nil: `reverse (reverse nil)` ι→ `reverse nil` ι→ `nil`. Goal `Id (nil) (nil)` = refl.
///   Step l'=cons a xs:
///     `reverse (reverse (cons a xs))` ι→ `reverse ((reverse xs) ++ (cons a nil))`.  Apply
///     `reverse_append A (reverse xs) (cons a nil)`:
///       reverse ((reverse xs) ++ (cons a nil))
///         = reverse (cons a nil) ++ reverse (reverse xs)
///         ≡ ((nil ++ (cons a nil)) ... ) ⇒ ι→ (cons a nil) ++ reverse(reverse xs)
///         ι→ cons a (nil ++ reverse(reverse xs)) ι→ cons a (reverse (reverse xs)).
///     So the FIRST hop's rhs `reverse(cons a nil) ++ reverse(reverse xs)` is DEFINITIONALLY equal to
///     `cons a (reverse(reverse xs))` (the convertibility the kernel collapses by ι). Then
///     `ap_cons A a (reverse(reverse xs)) xs ih : cons a (reverse(reverse xs)) = cons a xs`. Chain:
///       reverse(reverse(cons a xs))
///         =⟨ reverse_append A (reverse xs) (cons a nil) ⟩  reverse(cons a nil) ++ reverse(reverse xs)
///                                                          ≡  cons a (reverse(reverse xs))
///         =⟨ ap_cons A a (reverse(reverse xs)) xs ih ⟩     cons a xs.
///     `trans (reverse_append …) (ap_cons …)` closes the goal — the two trans endpoints meet at the
///     ι-convertible `cons a (reverse(reverse xs))`. IH genuinely CONSUMED; ι on the OPEN tail `xs`.
fn reverse_involution() -> Tm {
    // ctx [A,l]: A=Var1, l=Var0.
    // motive λl'. Id (List A) (reverse (reverse l')) l'.   ctx [A,l,l']: A=Var2, l'=Var0.
    let motive = lam(
        list_ty(Tm::Var(1)), // l' : List A  (A = Var1 in ctx [A,l])
        id_ty(
            list_ty(Tm::Var(2)),                                  // List A
            reverse(Tm::Var(2), reverse(Tm::Var(2), Tm::Var(0))), // reverse (reverse l')
            Tm::Var(0),                                           // l'
        ),
    );
    // base : refl (List A) (nil A).   ctx [A,l]: A=Var1.
    let base = refl(list_ty(Tm::Var(1)), nil(Tm::Var(1)));
    // step λa.λxs.λih. trans (reverse_append A (reverse xs)(cons a nil)) (ap_cons A a (reverse(reverse xs)) xs ih).
    let step = lam(
        Tm::Var(1), // a : A   (A = Var1 in ctx [A,l])
        lam(
            list_ty(Tm::Var(2)), // xs : List A  (A = Var2 in ctx [A,l,a])
            lam(
                // ih : motive xs = Id (List A) (reverse (reverse xs)) xs.
                //   ctx [A,l,a,xs]: A=Var3, xs=Var0.
                id_ty(
                    list_ty(Tm::Var(3)),
                    reverse(Tm::Var(3), reverse(Tm::Var(3), Tm::Var(0))),
                    Tm::Var(0),
                ),
                // ctx [A,l,a,xs,ih]: A=Var4, a=Var2, xs=Var1, ih=Var0.
                {
                    // S := cons A a (nil A); endpoints over List A:
                    //   P := reverse(reverse(cons a xs))  ≡  reverse ((reverse xs) ++ S)  (= LHS by ι)
                    //   M := reverse (cons a nil) ++ reverse(reverse xs)   ≡  cons a (reverse(reverse xs))
                    //   N := cons a xs                                     (= the goal target)
                    let s_lit = cons(Tm::Var(4), Tm::Var(2), nil(Tm::Var(4))); // cons A a (nil A)
                    let rev_xs = reverse(Tm::Var(4), Tm::Var(1)); // reverse xs
                    let rev_rev_xs = reverse(Tm::Var(4), rev_xs.clone()); // reverse (reverse xs)
                                                                          // P := reverse ((reverse xs) ++ S).  (Definitionally = reverse(reverse(cons a xs)).)
                    let p = reverse(
                        Tm::Var(4),
                        append(Tm::Var(4), rev_xs.clone(), s_lit.clone()),
                    );
                    // M := reverse_append's rhs = (reverse S) ++ reverse(reverse xs).
                    //   reverse S ι→ (cons a nil) (snoc of a onto reverse nil = nil), so M ι→
                    //   (cons a nil) ++ reverse(reverse xs) ι→ cons a (nil ++ reverse(reverse xs))
                    //   ι→ cons a (reverse(reverse xs)).
                    let m = append(
                        Tm::Var(4),
                        reverse(Tm::Var(4), s_lit.clone()), // reverse (cons a nil)
                        rev_rev_xs.clone(),
                    );
                    let n = cons(Tm::Var(4), Tm::Var(2), Tm::Var(1)); // cons A a xs
                                                                      // hop1 : Id (List A) P M   via reverse_append A (reverse xs) S.
                    let hop1 = reverse_append_at(Tm::Var(4), rev_xs.clone(), s_lit.clone());
                    // hop2 : Id (List A) (cons a (reverse(reverse xs))) (cons a xs)  via ap_cons + IH.
                    //   Its lhs `cons a (reverse(reverse xs))` is ι-convertible to M, so trans lines up.
                    let hop2 = ap_cons_at(
                        Tm::Var(4),         // A
                        Tm::Var(2),         // a
                        rev_rev_xs.clone(), // reverse (reverse xs)
                        Tm::Var(1),         // xs
                        Tm::Var(0),         // ih  (CONSUMED)
                    );
                    trans_at(list_ty(Tm::Var(4)), p, m, n, hop1, hop2)
                },
            ),
        ),
    );
    let rec = apps(
        Tm::Elim(LIST),
        &[Tm::Var(1), motive, base, step, Tm::Var(0)],
    ); // param A, scrut l
    lam(Tm::Sort(0), lam(list_ty(Tm::Var(0)), rec))
}
fn reverse_involution_ty() -> Tm {
    // Π(A:Type₀)(l:List A). Id (List A) (reverse (reverse l)) l.   ctx [A,l]: A=Var1, l=Var0.
    pi(
        Tm::Sort(0),
        pi(
            list_ty(Tm::Var(0)), // l : List A
            id_ty(
                list_ty(Tm::Var(1)),
                reverse(Tm::Var(1), reverse(Tm::Var(1), Tm::Var(0))), // reverse (reverse l)
                Tm::Var(0),                                           // l
            ),
        ),
    )
}

#[test]
fn reverse_involution_typechecks() {
    // THE theorem: ∀A l. reverse (reverse l) = l — GENERAL, machine-checked by the trusted kernel.
    // Induction on l (List.rec); base definitional; step CHAINS the helper lemma `reverse_append`
    // (anti-distributivity) with `ap_cons` (fed the IH) via `trans`. The middle endpoint
    // `reverse(cons a nil) ++ reverse(reverse xs)` collapses by ι to `cons a (reverse(reverse xs))`,
    // letting the two trans hops meet. Goes through on the OPEN tail because List is non-indexed
    // (nidx==0) — the open recursive field `xs` never hits the driver:106 empty-ctx infer.
    let env = env();
    assert!(
        check(
            &env,
            &Vec::new(),
            &reverse_involution(),
            &reverse_involution_ty()
        )
        .is_ok(),
        "reverse_involution : Π(A)(l:List A). Id (List A) (reverse (reverse l)) l"
    );
}

#[test]
fn false_reverse_involution_rejected() {
    // NO-FALSE-GREEN: `reverse_involution` does NOT inhabit the (false) goal
    // `reverse (reverse l) = reverse l` — i.e. claiming ONE reverse is already an involution. The
    // witness's step builds the `cons a xs` endpoint, which is NOT convertible to `reverse l`'s
    // (cons a xs ι→ reverse(reverse(cons a xs)) collapses, but the STATED target `reverse l` does
    // not), so `check` rejects.
    let env = env();
    let bad_ty = pi(
        Tm::Sort(0),
        pi(
            list_ty(Tm::Var(0)),
            id_ty(
                list_ty(Tm::Var(1)),
                reverse(Tm::Var(1), reverse(Tm::Var(1), Tm::Var(0))), // reverse (reverse l)
                reverse(Tm::Var(1), Tm::Var(0)),                      // reverse l  — FALSE target
            ),
        ),
    );
    // POSITIVE CONTROL (non-vacuity): the SAME witness DOES check against the TRUE goal — so the
    // rejection below is a genuine rhs mismatch, not a vacuously ill-typed term.
    assert!(
        check(
            &env,
            &Vec::new(),
            &reverse_involution(),
            &reverse_involution_ty()
        )
        .is_ok(),
        "positive control: reverse_involution proves the TRUE goal reverse(reverse l) = l"
    );
    assert_eq!(
        check(&env, &Vec::new(), &reverse_involution(), &bad_ty),
        Err(TypeError::Mismatch),
        "reverse_involution does NOT prove reverse (reverse l) = reverse l  (no false-green)"
    );
}
