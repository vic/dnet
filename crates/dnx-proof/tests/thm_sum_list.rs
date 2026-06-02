//! Verified list `sum : List Nat → Nat` (the fold `Σ` of a list of naturals) on the dnx-proof
//! kernel, culminating in the GENERAL monoid-homomorphism law
//! `∀l1 l2. sum (l1 ++ l2) = add (sum l1) (sum l2)` — `sum` carries `(++, nil)` to `(add, 0)`.
//!
//! This file joins the two non-indexed worlds `List Nat` (parametric `List` instantiated at the
//! CLOSED carrier `Nat`; `nidx == 0`) and `Nat` (`nidx == 0`). `sum` is one `Elim List` whose
//! motive is the CONSTANT `Nat`, so its result is non-indexed (the cross-type recursor precedent is
//! `length : List A → Nat`, thm_length_append.rs:5-8):
//!   sum := λl. List.rec Nat (λ_:List Nat. Nat) 0 (λa tl ih. add a ih) l
//!   ⇒  sum nil ι→ 0 ,  sum (cons a tl) ι→ add a (sum tl).
//! Because both `List` and `Nat` are non-indexed, the ι-driver fires on OPEN scrutinees / recursive
//! fields (driver.rs:104-119 fast-path), so `sum` reduces under binders and the genuine inductive
//! step below goes through — the `driver.rs:106` empty-ctx infer only bites INDEXED families.
//!
//! `Nat`/`zero`/`succ`, `add` (recursion on its FIRST arg, thm_nat_arith.rs:109-115), `Id`/`refl`,
//! `append` (++, recursion on l1, thm_map_append.rs:128-155), and the J-derived combinators
//! `ap_plus_l`/`eq_sym`/`eq_trans` plus the `add_assoc` lemma are reproduced CLOSED here so the file
//! is self-contained (the exact idioms of thm_nat_arith.rs / thm_mul_laws.rs / thm_map_append.rs;
//! eq_prelude.rs:166-312). NO new axioms: every term is `check`ed at its ∀-type by the trusted
//! kernel, so the kernel itself is the oracle.
//!
//! THEOREMS (all machine-checked at their type by the trusted kernel `check`):
//!   • closed computation: sum [1,2,3] = 6 ,  sum ([1,2] ++ [3]) = 6   (ι on closed lists; nf/conv).
//!   • sum_nil_l   : ∀l. sum (nil ++ l) = sum l        (definitional: nil++l ι→ l).
//!   • sum_append  : ∀l1 l2. sum (l1 ++ l2) = add (sum l1) (sum l2)
//!     (GENERAL; induction on l1, IH consumed via the right-arg congruence `ap_plus_l` over Nat,
//!      then re-associated with `add_assoc` — exactly the map_append/filter_append/mul_distrib shape).
//!
//! NON-VACUITY: a CLOSED instance (`sum_append [1,2] [3] : Id Nat 6 6`) ι-normalizes to `refl Nat 6`,
//! and off-by-one / swapped companions are REJECTED by `check` while the TRUE goal passes (a positive
//! control accompanies every negative) — so the green is not a vacuous-type artifact.

use dnx_proof::conv::conv;
use dnx_proof::driver::nf_tm;
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::infer::{check, TypeError};
use dnx_proof::symbol::{ConstId, IndId};
use dnx_proof::tm::Tm;

// ── term helpers (same idioms as eq_prelude.rs / thm_nat_arith.rs / thm_map_append.rs) ──
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
const LIST: IndId = IndId(1);
const ID: IndId = IndId(2);
const ADD: ConstId = ConstId(0);
const APPEND: ConstId = ConstId(1);
const SUM: ConstId = ConstId(2);

// ── Nat = zero | succ Nat ──   (thm_nat_arith.rs:66-85.)
fn nat_ty() -> Tm {
    Tm::Ind(NAT)
}
fn zero() -> Tm {
    Tm::Ctor(NAT, 0)
}
fn succ(n: Tm) -> Tm {
    app(Tm::Ctor(NAT, 1), n)
}
fn lit(n: u32) -> Tm {
    (0..n).fold(zero(), |acc, _| succ(acc))
}
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

// ── List : Π(A:Type₀). Type₀  (param A, NO indices ⇒ nidx==0).   (thm_map_append.rs:76-96.) ──
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
/// `List Nat` and its constructors — the only carrier `sum` operates on.
fn lnat() -> Tm {
    list_ty(nat_ty())
}
fn nil_nat() -> Tm {
    nil(nat_ty())
}
fn cons_nat(hd: Tm, tl: Tm) -> Tm {
    cons(nat_ty(), hd, tl)
}

// ── Id : Π(A:Type₀)(a:A). A → Type₀ ; refl A a : Id A a a.   (eq_prelude.rs:49-61.) ──
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

// ── add := λa b. Elim Nat (λ_.Nat) b (λk ih. succ ih) a   (recursion on FIRST arg; thm_nat_arith.rs:109).
//   add 0 b ι→ b ;  add (succ k) b ι→ succ (add k b). ──
fn add_body() -> Tm {
    let elim = apps(
        Tm::Elim(NAT),
        &[
            lam(nat_ty(), nat_ty()),                        // motive λ_:Nat. Nat
            Tm::Var(0),                                     // minor_zero = b
            lam(nat_ty(), lam(nat_ty(), succ(Tm::Var(0)))), // minor_succ = λk.λih. succ ih
            Tm::Var(1),                                     // scrutinee = a
        ],
    );
    lam(nat_ty(), lam(nat_ty(), elim))
}
fn add_ty() -> Tm {
    pi(nat_ty(), pi(nat_ty(), nat_ty()))
}
fn add(a: Tm, b: Tm) -> Tm {
    apps(Tm::Const(ADD), &[a, b])
}

// ── append := λA l1 l2. List.rec A (λ_:List A. List A) l2 (λa xs ih. cons A a ih) l1
//   (recursion on l1; thm_map_append.rs:128-155). Used only at A:=Nat below, but kept polymorphic. ──
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
/// `append Nat l1 l2 : List Nat`  (the only instantiation `sum_append` uses).
fn appn(l1: Tm, l2: Tm) -> Tm {
    apps(Tm::Const(APPEND), &[nat_ty(), l1, l2])
}

// ── sum := λl. List.rec Nat (λ_:List Nat. Nat) 0 (λa tl ih. add a ih) l   (recursion on l).
//   Motive is the CONSTANT `Nat` (cross-type, like length), so the result is non-indexed and ι fires
//   on open scrutinees.  sum nil ι→ 0 ;  sum (cons a tl) ι→ add a (sum tl). ──
fn sum_body() -> Tm {
    // ctx [l]: l=Var0.  Under minor λa.λtl.λih: ctx [l,a,tl,ih]: a=Var2, ih=Var0.
    let minor_cons = lam(
        nat_ty(), // a : Nat
        lam(
            lnat(), // tl : List Nat
            lam(
                nat_ty(),                    // ih : Nat  (the recursive Σ of the tail)
                add(Tm::Var(2), Tm::Var(0)), // add a ih
            ),
        ),
    );
    let elim = apps(
        Tm::Elim(LIST),
        &[
            nat_ty(),              // param A = Nat
            lam(lnat(), nat_ty()), // motive λ_:List Nat. Nat
            zero(),                // minor_nil = 0
            minor_cons,
            Tm::Var(0), // scrutinee = l
        ],
    );
    lam(lnat(), elim)
}
fn sum_ty() -> Tm {
    pi(lnat(), nat_ty()) // List Nat → Nat
}
fn sum_(l: Tm) -> Tm {
    app(Tm::Const(SUM), l)
}

fn env() -> dnx_proof::env::GlobalEnv {
    let mut e = dnx_proof::env::GlobalEnv::default();
    e.add_inductive(nat()).expect("Nat admits");
    e.add_inductive(list_ind())
        .expect("List admits (parametric inductive, positivity R3 ok)");
    e.add_inductive(id_ind())
        .expect("Id admits (indexed inductive, Vec mould)");
    e.add_const(ADD, add_ty(), add_body())
        .expect("add admits (δ-acyclic)");
    e.add_const(APPEND, append_ty(), append_body())
        .expect("append admits (δ-acyclic)");
    e.add_const(SUM, sum_ty(), sum_body()).expect(
        "sum admits (δ-acyclic, cross-type recursor; sum calls add, add does not call sum)",
    );
    e
}

/// `[x0;x1;…]` over Nat.
fn list_lit(xs: &[Tm]) -> Tm {
    xs.iter()
        .rev()
        .fold(nil_nat(), |tl, hd| cons_nat(hd.clone(), tl))
}

// ════════════════ derived equality combinators (J / Elim Id) ════════════════
// ap_plus_l / eq_sym / eq_trans are derived EXACTLY as in eq_prelude.rs / thm_mul_laws.rs
// (proofs.md:177-188); reproduced here closed so the file is self-contained.

/// ap_plus_l : Π(c a b:Nat)(p:Id Nat a b). Id Nat (add c a) (add c b)  (RIGHT-arg congruence of add).
///   = λc a b p. Elim Id Nat a (λb' x. Id Nat (add c a)(add c b')) (refl Nat (add c a)) b p
/// This is the congruence the step needs: it lifts the IH `sum(xs++l2)=add(sum xs)(sum l2)` under the
/// fixed head `add a (-)` (thm_mul_laws.rs:213-263).
fn ap_plus_l() -> Tm {
    // ctx [c,a,b,p]: c=Var3, a=Var2, b=Var1, p=Var0.
    let motive = lam(
        nat_ty(), // b'
        lam(
            id_nat(Tm::Var(3), Tm::Var(0)), // x : Id Nat a b'  (a=Var3, b'=Var0)
            id_nat(
                add(Tm::Var(5), Tm::Var(4)), // add c a   (c=Var5, a=Var4)
                add(Tm::Var(5), Tm::Var(1)), // add c b'  (b'=Var1)
            ),
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            nat_ty(),
            Tm::Var(2), // a
            motive,
            refl_nat(add(Tm::Var(3), Tm::Var(2))), // refl Nat (add c a)
            Tm::Var(1),                            // index b
            Tm::Var(0),                            // scrutinee p
        ],
    );
    lam(
        nat_ty(),
        lam(
            nat_ty(),
            lam(nat_ty(), lam(id_nat(Tm::Var(1), Tm::Var(0)), body)),
        ),
    )
}
fn ap_plus_l_ty() -> Tm {
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            pi(
                nat_ty(),
                pi(
                    id_nat(Tm::Var(1), Tm::Var(0)),
                    id_nat(add(Tm::Var(3), Tm::Var(2)), add(Tm::Var(3), Tm::Var(1))),
                ),
            ),
        ),
    )
}
fn ap_plus_l_at(c: Tm, a: Tm, b: Tm, p: Tm) -> Tm {
    apps(ap_plus_l(), &[c, a, b, p])
}

/// eq_sym : Π(A:Type₀)(a b:A)(p:Id A a b). Id A b a   (eq_prelude.rs:166-202).
fn eq_sym() -> Tm {
    let motive = lam(
        Tm::Var(3),
        lam(
            apps(Tm::Ind(ID), &[Tm::Var(4), Tm::Var(3), Tm::Var(0)]),
            apps(Tm::Ind(ID), &[Tm::Var(5), Tm::Var(1), Tm::Var(4)]),
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            Tm::Var(3),
            Tm::Var(2),
            motive,
            apps(Tm::Ctor(ID, 0), &[Tm::Var(3), Tm::Var(2)]),
            Tm::Var(1),
            Tm::Var(0),
        ],
    );
    lam(
        Tm::Sort(0),
        lam(
            Tm::Var(0),
            lam(
                Tm::Var(1),
                lam(
                    apps(Tm::Ind(ID), &[Tm::Var(2), Tm::Var(1), Tm::Var(0)]),
                    body,
                ),
            ),
        ),
    )
}
fn eq_sym_ty() -> Tm {
    pi(
        Tm::Sort(0),
        pi(
            Tm::Var(0),
            pi(
                Tm::Var(1),
                pi(
                    apps(Tm::Ind(ID), &[Tm::Var(2), Tm::Var(1), Tm::Var(0)]),
                    apps(Tm::Ind(ID), &[Tm::Var(3), Tm::Var(1), Tm::Var(2)]),
                ),
            ),
        ),
    )
}
/// `eq_sym Nat a b p : Id Nat b a`  (concrete instantiation at A:=Nat).
fn eq_sym_nat(a: Tm, b: Tm, p: Tm) -> Tm {
    apps(eq_sym(), &[nat_ty(), a, b, p])
}

/// eq_trans : Π(A)(a b c:A)(p:Id A a b)(q:Id A b c). Id A a c   (eq_prelude.rs:255-291).
fn eq_trans() -> Tm {
    let motive = lam(
        Tm::Var(5),
        lam(
            apps(Tm::Ind(ID), &[Tm::Var(6), Tm::Var(4), Tm::Var(0)]),
            apps(Tm::Ind(ID), &[Tm::Var(7), Tm::Var(6), Tm::Var(1)]),
        ),
    );
    let body = apps(
        Tm::Elim(ID),
        &[
            Tm::Var(5),
            Tm::Var(3),
            motive,
            Tm::Var(1),
            Tm::Var(2),
            Tm::Var(0),
        ],
    );
    lam(
        Tm::Sort(0),
        lam(
            Tm::Var(0),
            lam(
                Tm::Var(1),
                lam(
                    Tm::Var(2),
                    lam(
                        apps(Tm::Ind(ID), &[Tm::Var(3), Tm::Var(2), Tm::Var(1)]),
                        lam(
                            apps(Tm::Ind(ID), &[Tm::Var(4), Tm::Var(2), Tm::Var(1)]),
                            body,
                        ),
                    ),
                ),
            ),
        ),
    )
}
fn eq_trans_ty() -> Tm {
    pi(
        Tm::Sort(0),
        pi(
            Tm::Var(0),
            pi(
                Tm::Var(1),
                pi(
                    Tm::Var(2),
                    pi(
                        apps(Tm::Ind(ID), &[Tm::Var(3), Tm::Var(2), Tm::Var(1)]),
                        pi(
                            apps(Tm::Ind(ID), &[Tm::Var(4), Tm::Var(2), Tm::Var(1)]),
                            apps(Tm::Ind(ID), &[Tm::Var(5), Tm::Var(4), Tm::Var(2)]),
                        ),
                    ),
                ),
            ),
        ),
    )
}
/// `eq_trans Nat a b c p q : Id Nat a c`  (concrete, the only instantiation used below).
fn trans_nat(a: Tm, b: Tm, c: Tm, p: Tm, q: Tm) -> Tm {
    apps(eq_trans(), &[nat_ty(), a, b, c, p, q])
}

/// add_assoc : Π(n m k:Nat). Id Nat (add (add n m) k) (add n (add m k))   (thm_nat_arith.rs:622-652).
/// Induction on the FIRST arg n; base definitional; step lifts the IH via ap_succ (reproduced inline).
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
fn ap_succ_at(a: Tm, b: Tm, p: Tm) -> Tm {
    apps(ap_succ(), &[a, b, p])
}
fn add_assoc() -> Tm {
    let motive = lam(
        nat_ty(),
        id_nat(
            add(add(Tm::Var(0), Tm::Var(2)), Tm::Var(1)),
            add(Tm::Var(0), add(Tm::Var(2), Tm::Var(1))),
        ),
    );
    let base = refl_nat(add(Tm::Var(1), Tm::Var(0)));
    let step = lam(
        nat_ty(),
        lam(
            id_nat(
                add(add(Tm::Var(0), Tm::Var(2)), Tm::Var(1)),
                add(Tm::Var(0), add(Tm::Var(2), Tm::Var(1))),
            ),
            ap_succ_at(
                add(add(Tm::Var(1), Tm::Var(3)), Tm::Var(2)),
                add(Tm::Var(1), add(Tm::Var(3), Tm::Var(2))),
                Tm::Var(0),
            ),
        ),
    );
    let rec = apps(Tm::Elim(NAT), &[motive, base, step, Tm::Var(2)]);
    lam(nat_ty(), lam(nat_ty(), lam(nat_ty(), rec)))
}
fn add_assoc_ty() -> Tm {
    pi(
        nat_ty(),
        pi(
            nat_ty(),
            pi(
                nat_ty(),
                id_nat(
                    add(add(Tm::Var(2), Tm::Var(1)), Tm::Var(0)),
                    add(Tm::Var(2), add(Tm::Var(1), Tm::Var(0))),
                ),
            ),
        ),
    )
}
fn add_assoc_at(n: Tm, m: Tm, k: Tm) -> Tm {
    apps(add_assoc(), &[n, m, k])
}

#[test]
fn building_blocks_typecheck() {
    // Pin every tool (the proof's only weapons beyond List.rec) before the theorem.
    let env = env();
    assert!(
        check(&env, &Vec::new(), &ap_plus_l(), &ap_plus_l_ty()).is_ok(),
        "ap_plus_l : Π(c a b:Nat)(p:Id Nat a b). Id Nat (add c a)(add c b)  (right-arg congruence)"
    );
    assert!(
        check(&env, &Vec::new(), &eq_sym(), &eq_sym_ty()).is_ok(),
        "eq_sym : Π(A)(a b:A)(p:Id A a b). Id A b a"
    );
    assert!(
        check(&env, &Vec::new(), &eq_trans(), &eq_trans_ty()).is_ok(),
        "eq_trans : Π(A)(a b c:A)(p:Id A a b)(q:Id A b c). Id A a c"
    );
    assert!(
        check(&env, &Vec::new(), &add_assoc(), &add_assoc_ty()).is_ok(),
        "add_assoc : Π(n m k:Nat). Id Nat ((n+m)+k) (n+(m+k))"
    );
}

#[test]
fn sum_admits_and_computes_closed() {
    // sum is admitted (δ-acyclic over add) and computes by ι on closed lists:
    //   sum [1,2,3] ι→ add 1 (add 2 (add 3 0)) ι→ 6 ;  sum ([1,2]++[3]) ι→ sum [1,2,3] ι→ 6.
    let env = env();
    // sum [] = 0.
    assert!(
        conv(&env, &Vec::new(), &sum_(list_lit(&[])), &lit(0)).unwrap(),
        "sum [] ≡ 0  (nil-minor)"
    );
    // sum [1,2,3] = 6.
    let l123 = list_lit(&[lit(1), lit(2), lit(3)]);
    assert_eq!(
        nf_tm(&env, &Vec::new(), &sum_(l123.clone())),
        lit(6),
        "sum [1,2,3] ι-normalizes to 6"
    );
    assert!(
        conv(&env, &Vec::new(), &sum_(l123), &lit(6)).unwrap(),
        "sum [1,2,3] ≡ 6"
    );
    // sum ([1,2] ++ [3]) = 6  (append fires, then sum).
    let appended = appn(list_lit(&[lit(1), lit(2)]), list_lit(&[lit(3)]));
    assert_eq!(
        nf_tm(&env, &Vec::new(), &sum_(appended.clone())),
        lit(6),
        "sum ([1,2]++[3]) ι-normalizes to 6"
    );
    assert!(
        conv(&env, &Vec::new(), &sum_(appended.clone()), &lit(6)).unwrap(),
        "sum ([1,2]++[3]) ≡ 6"
    );
    // no-false-green: NOT convertible to a wrong total.
    assert!(
        !conv(&env, &Vec::new(), &sum_(appended), &lit(5)).unwrap(),
        "sum ([1,2]++[3]) ≢ 5"
    );
}

// ════════════════════════ sum_nil_l — ∀l. sum (nil ++ l) = sum l ════════════════════════

/// sum_nil_l := λl. refl Nat (sum l).
/// `nil ++ l` ι→ `l` (the append nil-minor), so `sum (nil ++ l) ≡ sum l` DEFINITIONALLY.
fn sum_nil_l() -> Tm {
    lam(lnat(), refl_nat(sum_(Tm::Var(0))))
}
fn sum_nil_l_ty() -> Tm {
    // Π(l:List Nat). Id Nat (sum (append Nat (nil Nat) l)) (sum l).
    pi(
        lnat(),
        id_nat(
            sum_(appn(nil_nat(), Tm::Var(0))), // sum (nil ++ l)
            sum_(Tm::Var(0)),                  // sum l
        ),
    )
}

#[test]
fn sum_nil_l_typechecks() {
    // ∀l. sum (nil ++ l) = sum l — GENERAL, definitional (ι on the append nil-minor).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &sum_nil_l(), &sum_nil_l_ty()).is_ok(),
        "sum_nil_l : Π(l:List Nat). Id Nat (sum (nil ++ l)) (sum l)  (definitional)"
    );
}

// ════════════════════════ sum_append — ∀l1 l2. sum (l1 ++ l2) = add (sum l1) (sum l2) ════════════════════════

/// sum_append := λl1 l2. List.rec Nat
///     (λl1'. Id Nat (sum (append Nat l1' l2)) (add (sum l1') (sum l2)))         -- motive
///     (refl Nat (sum l2))                                                       -- base l1=nil
///     (λa xs ih. <chain>)                                                       -- step l1=cons a xs
///     l1
///
/// Induction on l1 (the list `append`/`sum` recurse on).
///   Base l1=nil: `sum (nil ++ l2)` ι→ `sum l2`; `add (sum nil)(sum l2)` ι→ `add 0 (sum l2)` ι→
///     `sum l2` — both sides ι to `sum l2`, so the goal is `refl Nat (sum l2)`.
///   Step l1=cons a xs:
///     LHS `sum ((cons a xs) ++ l2)` ι→ `sum (cons a (xs ++ l2))` ι→ `add a (sum (xs ++ l2))`,
///     RHS `add (sum (cons a xs)) (sum l2)` ι→ `add (add a (sum xs)) (sum l2)`,
///     IH `ih : Id Nat (sum (xs++l2)) (add (sum xs)(sum l2))`.
///       s1 = ap_plus_l a (sum (xs++l2)) (add (sum xs)(sum l2)) ih        -- IH CONSUMED
///          : add a (sum (xs++l2)) = add a (add (sum xs)(sum l2))
///       s2 = eq_sym (add_assoc a (sum xs)(sum l2))
///          : add a (add (sum xs)(sum l2)) = add (add a (sum xs))(sum l2)
///     eq_trans chains s1,s2 ⟹ `add a (sum (xs++l2)) = add (add a (sum xs))(sum l2)` ≡ goal (both
///     sides ι-eq to the motive at cons a xs). The IH is genuinely CONSUMED, and the recursive ι's
///     fire on the OPEN tail `xs` because List is non-indexed (driver.rs:104-119 fast-path).
fn sum_append() -> Tm {
    // ctx [l1,l2]: l1=Var1, l2=Var0.
    // motive λl1'. Id Nat (sum (l1' ++ l2)) (add (sum l1') (sum l2)).
    //   ctx [l1,l2,l1']: l2=Var1, l1'=Var0.
    let motive = lam(
        lnat(), // l1' : List Nat
        id_nat(
            sum_(appn(Tm::Var(0), Tm::Var(1))),      // sum (l1' ++ l2)
            add(sum_(Tm::Var(0)), sum_(Tm::Var(1))), // add (sum l1') (sum l2)
        ),
    );
    // base : refl Nat (sum l2)   (ctx [l1,l2]: l2=Var0).
    let base = refl_nat(sum_(Tm::Var(0)));
    // step λa.λxs.λih. <chain>.
    //   ctx [l1,l2,a,xs,ih]: l2=Var3, a=Var2, xs=Var1, ih=Var0.
    let step = lam(
        nat_ty(), // a : Nat   (head element)
        lam(
            lnat(), // xs : List Nat
            lam(
                // ih : motive xs = Id Nat (sum (xs++l2)) (add (sum xs)(sum l2)).
                //   ctx [l1,l2,a,xs]: l2=Var2, xs=Var0.
                id_nat(
                    sum_(appn(Tm::Var(0), Tm::Var(2))),
                    add(sum_(Tm::Var(0)), sum_(Tm::Var(2))),
                ),
                // ctx [l1,l2,a,xs,ih]: l2=Var3, a=Var2, xs=Var1, ih=Var0.
                {
                    let a = Tm::Var(2);
                    let sxsl2 = sum_(appn(Tm::Var(1), Tm::Var(3))); // sum (xs ++ l2)
                    let sxs = sum_(Tm::Var(1)); // sum xs
                    let sl2 = sum_(Tm::Var(3)); // sum l2
                                                // s1 : add a (sum (xs++l2)) = add a (add (sum xs)(sum l2))
                    let s1 = ap_plus_l_at(
                        a.clone(),
                        sxsl2.clone(),
                        add(sxs.clone(), sl2.clone()),
                        Tm::Var(0), // ih  (CONSUMED)
                    );
                    // s2 : add a (add (sum xs)(sum l2)) = add (add a (sum xs))(sum l2)
                    let s2 = eq_sym_nat(
                        add(add(a.clone(), sxs.clone()), sl2.clone()),
                        add(a.clone(), add(sxs.clone(), sl2.clone())),
                        add_assoc_at(a.clone(), sxs.clone(), sl2.clone()),
                    );
                    trans_nat(
                        add(a.clone(), sxsl2),
                        add(a.clone(), add(sxs.clone(), sl2.clone())),
                        add(add(a, sxs), sl2),
                        s1,
                        s2,
                    )
                },
            ),
        ),
    );
    let rec = apps(Tm::Elim(LIST), &[nat_ty(), motive, base, step, Tm::Var(1)]); // param Nat, scrut l1
    lam(lnat(), lam(lnat(), rec))
}
fn sum_append_ty() -> Tm {
    // Π(l1 l2:List Nat). Id Nat (sum (l1 ++ l2)) (add (sum l1) (sum l2)).
    // ctx [l1,l2]: l1=Var1, l2=Var0.
    pi(
        lnat(),
        pi(
            lnat(),
            id_nat(
                sum_(appn(Tm::Var(1), Tm::Var(0))),      // sum (l1 ++ l2)
                add(sum_(Tm::Var(1)), sum_(Tm::Var(0))), // add (sum l1) (sum l2)
            ),
        ),
    )
}
/// `sum_append l1 l2 : Id Nat (sum (l1++l2)) (add (sum l1)(sum l2))`  (concrete instance).
fn sum_append_at(l1: Tm, l2: Tm) -> Tm {
    apps(sum_append(), &[l1, l2])
}

#[test]
fn sum_append_typechecks() {
    // THE theorem: ∀l1 l2. sum (l1++l2) = add (sum l1) (sum l2) — GENERAL, machine-checked.
    // `sum` is the monoid homomorphism (List Nat, ++, nil) → (Nat, add, 0). Induction on l1
    // (List.rec); base definitional; step CONSUMES the IH via ap_plus_l, then re-associates with
    // add_assoc (eq_sym + eq_trans) to match the rhs ι-normal form. Goes through on the OPEN tail
    // because List is non-indexed (nidx==0) — the open recursive field `xs` never hits the
    // driver:106 empty-ctx infer (that gate only bites INDEXED families).
    let env = env();
    assert!(
        check(&env, &Vec::new(), &sum_append(), &sum_append_ty()).is_ok(),
        "sum_append : Π(l1 l2:List Nat). Id Nat (sum (l1++l2)) (add (sum l1)(sum l2))"
    );
}

#[test]
fn false_sum_append_swapped_rejected() {
    // NO-FALSE-GREEN: `sum_append` does NOT inhabit the SWAPPED goal
    // `sum (l1++l2) = add (sum l2) (sum l1)`. Although `add` IS commutative, the WITNESS's base
    // `refl Nat (sum l2) : Id Nat (sum l2) (add (sum l2) (sum nil))` would need `add (sum l2) 0 ≡
    // sum l2`, but `add x 0` is STUCK on the neutral `sum l2` (add recurses on its first arg) — so
    // the base no longer typechecks and `check` rejects (it would demand its own induction).
    let env = env();
    let bad_ty = pi(
        lnat(),
        pi(
            lnat(),
            id_nat(
                sum_(appn(Tm::Var(1), Tm::Var(0))),      // sum (l1 ++ l2)
                add(sum_(Tm::Var(0)), sum_(Tm::Var(1))), // add (sum l2) (sum l1)  — SWAPPED
            ),
        ),
    );
    assert_eq!(
        check(&env, &Vec::new(), &sum_append(), &bad_ty),
        Err(TypeError::Mismatch),
        "sum_append does NOT prove sum (l1++l2) = add (sum l2)(sum l1)  (no false-green)"
    );
}

#[test]
fn false_sum_append_offbyone_rejected() {
    // NO-FALSE-GREEN + positive control: `sum_append` does NOT inhabit the off-by-one
    // `∀l1 l2. sum (l1++l2) = succ (add (sum l1)(sum l2))`, while it DOES inhabit the true type
    // (asserted above) — so the type is load-bearing, not vacuous.
    let env = env();
    let bad_ty = pi(
        lnat(),
        pi(
            lnat(),
            id_nat(
                sum_(appn(Tm::Var(1), Tm::Var(0))),
                succ(add(sum_(Tm::Var(1)), sum_(Tm::Var(0)))), // succ(...) — off by one
            ),
        ),
    );
    assert!(
        check(&env, &Vec::new(), &sum_append(), &bad_ty).is_err(),
        "sum_append does NOT inhabit ∀l1 l2. sum (l1++l2) = succ (add (sum l1)(sum l2))  (off by one)"
    );
}

#[test]
fn sum_append_closed_instance_is_refl() {
    // End-to-end ι evidence / non-vacuity: the closed proof
    // `sum_append [1,2] [3] : Id Nat (sum ([1,2]++[3])) (add (sum [1,2])(sum [3]))` ≡ `Id Nat 6 6`
    // NORMALIZES to the canonical witness `refl Nat 6` (both sides compute to 6 through the
    // recursors), convertible to it but NOT to a wrong witness `refl Nat 5`.
    let env = env();
    let inst = sum_append_at(list_lit(&[lit(1), lit(2)]), list_lit(&[lit(3)]));
    let refl6 = refl_nat(lit(6));
    assert_eq!(
        nf_tm(&env, &Vec::new(), &inst),
        refl6,
        "sum_append [1,2] [3] ι-normalizes to refl Nat 6"
    );
    assert!(
        conv(&env, &Vec::new(), &inst, &refl6).unwrap(),
        "sum_append [1,2] [3] ≡ refl Nat 6"
    );
    assert!(
        !conv(&env, &Vec::new(), &inst, &refl_nat(lit(5))).unwrap(),
        "sum_append [1,2] [3] ≢ refl Nat 5 (off by one)"
    );
}
