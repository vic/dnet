//! Fourcolor-class "verified proofs" demo (research-fourcolor.md §5). Drives the SAME
//! kernel features the four-colour proof stresses — ι-reduction over a recursive inductive
//! tree + boolean reflection — on TODAY's kernel, via the proven Tm-level recursor path
//! (driver.rs `try_iota`, the `a2` nat-rec template). No Y-net / Nix recursion involved.
//!
//! Mirror of fourcolor's reducibility-closing (`Eval vm_compute` at present.v:164,197): a
//! decision procedure (`all_leaf`) is run over a closed inductive value by ι, and its boolean
//! result is closed to `true` by conv — exactly `is_true b := (b = true)` (mathcomp ssrbool).
//!
//! Inductives:
//!   Bool  = false | true                              (IndId 0; 2-ctor, sort 0)
//!   Ctree = leaf (b: Bool) | node (l r: Ctree)        (IndId 1; recursive, strictly positive)
//!   eq    = Π(A:Sort0)(a:A). A → Sort0 := refl A a    (IndId 2; the `b = true` of `is_true`)
//! Consts:
//!   and      : Bool → Bool → Bool                     (Elim Bool — short-circuit fold)
//!   all_leaf : Ctree → Bool                           (Elim Ctree — structural recursor, IH/rec field)
//!   is_true  : Bool → Sort0                            (λb. eq Bool b true)

use dnx_proof::conv::conv;
use dnx_proof::driver::nf_tm;
use dnx_proof::env::GlobalEnv;
use dnx_proof::inductive::{CtorDecl, Inductive};
use dnx_proof::symbol::{ConstId, IndId};
use dnx_proof::tm::Tm;

// ── tiny builders (de Bruijn, as in soundness.rs) ──
fn lam(dom: Tm, b: Tm) -> Tm {
    Tm::Lam(Box::new(dom), Box::new(b))
}
fn app(f: Tm, x: Tm) -> Tm {
    Tm::App(Box::new(f), Box::new(x))
}
fn apps(head: Tm, args: &[Tm]) -> Tm {
    args.iter().fold(head, |f, a| app(f, a.clone()))
}

const BOOL: IndId = IndId(0);
const CTREE: IndId = IndId(1);
const EQ: IndId = IndId(2);
const AND: ConstId = ConstId(0);
const ALL_LEAF: ConstId = ConstId(1);
const IS_TRUE: ConstId = ConstId(2);

fn bool_ind() -> Inductive {
    Inductive {
        id: BOOL,
        params: vec![],
        indices: vec![],
        sort: 0,
        ctors: vec![
            CtorDecl {
                ctor_ix: 0, // false
                args: vec![],
                ret_indices: vec![],
            },
            CtorDecl {
                ctor_ix: 1, // true
                args: vec![],
                ret_indices: vec![],
            },
        ],
    }
}

/// Ctree = leaf (b:Bool) | node (l r:Ctree). `node` has two STRICTLY-POSITIVE recursive
/// fields ⇒ driver.rs threads one IH per field (the branching analogue of nat `succ`).
fn ctree_ind() -> Inductive {
    Inductive {
        id: CTREE,
        params: vec![],
        indices: vec![],
        sort: 0,
        ctors: vec![
            CtorDecl {
                ctor_ix: 0, // leaf : Bool → Ctree
                args: vec![Tm::Ind(BOOL)],
                ret_indices: vec![],
            },
            CtorDecl {
                ctor_ix: 1, // node : Ctree → Ctree → Ctree
                args: vec![Tm::Ind(CTREE), Tm::Ind(CTREE)],
                ret_indices: vec![],
            },
        ],
    }
}

/// eq (A:Sort0)(a:A) : A → Sort0 := refl : eq A a a. Indexed inductive — its `Elim` *type*
/// is not synthesised (recursor.rs rejects indexed families), but admission (positivity +
/// R11) and ι/conv work on any admitted inductive (driver.rs §3). `is_true` only needs the
/// type former + conv, never the recursor.
fn eq_ind() -> Inductive {
    Inductive {
        id: EQ,
        params: vec![Tm::Sort(0), Tm::Var(0)], // A : Sort0 ,  a : A(=Var 0)
        indices: vec![Tm::Var(1)],             // index : A  (A is Var 1 from inside the index ctx)
        sort: 0,
        ctors: vec![CtorDecl {
            ctor_ix: 0,                    // refl
            args: vec![],                  // no fields
            ret_indices: vec![Tm::Var(0)], // returns index = a (Var 0: params A,a in scope)
        }],
    }
}

fn fls() -> Tm {
    Tm::Ctor(BOOL, 0)
}
fn tru() -> Tm {
    Tm::Ctor(BOOL, 1)
}
fn leaf(b: Tm) -> Tm {
    app(Tm::Ctor(CTREE, 0), b)
}
fn node(l: Tm, r: Tm) -> Tm {
    apps(Tm::Ctor(CTREE, 1), &[l, r])
}

/// and := λa.λb. Elim Bool (λ_:Bool.Bool) false b a   — `if a then b else false` (short-circuit).
/// Spine (driver.rs §5): motive · minor_false · minor_true · scrutinee. a=Var 1, b=Var 0.
fn and_body() -> Tm {
    let motive = lam(Tm::Ind(BOOL), Tm::Ind(BOOL));
    let elim = apps(
        Tm::Elim(BOOL),
        &[motive, fls(), Tm::Var(0), Tm::Var(1)], // minor_false=false, minor_true=b, scrut=a
    );
    lam(Tm::Ind(BOOL), lam(Tm::Ind(BOOL), elim))
}

/// all_leaf := λt. Elim Ctree (λ_:Ctree.Bool) (λb. b) (λl.λr.λihl.λihr. and ihl ihr) t.
/// leaf-case returns the carried bool; node-case ANDs the two inductive hypotheses (ihl=Var 1,
/// ihr=Var 0) — the recursive `all_leaf` results threaded by ι.
fn all_leaf_body() -> Tm {
    let motive = lam(Tm::Ind(CTREE), Tm::Ind(BOOL));
    let minor_leaf = lam(Tm::Ind(BOOL), Tm::Var(0)); // λb. b
    let minor_node = lam(
        Tm::Ind(CTREE),
        lam(
            Tm::Ind(CTREE),
            lam(
                Tm::Ind(BOOL), // ih_l
                lam(
                    Tm::Ind(BOOL), // ih_r
                    apps(Tm::Const(AND), &[Tm::Var(1), Tm::Var(0)]),
                ),
            ),
        ),
    );
    let elim = apps(
        Tm::Elim(CTREE),
        &[motive, minor_leaf, minor_node, Tm::Var(0)],
    );
    lam(Tm::Ind(CTREE), elim)
}

/// is_true := λb:Bool. eq Bool b true   (mathcomp `is_true b := b = true`).
fn is_true_body() -> Tm {
    lam(
        Tm::Ind(BOOL),
        apps(Tm::Ind(EQ), &[Tm::Ind(BOOL), Tm::Var(0), tru()]),
    )
}

/// Build the demo environment; surfaces any admission gap as the `Result` of `add_*`.
fn demo_env() -> Result<GlobalEnv, dnx_proof::env::AdmitError> {
    let mut e = GlobalEnv::default();
    e.add_inductive(bool_ind())?;
    e.add_inductive(ctree_ind())?;
    e.add_inductive(eq_ind())?;
    e.add_const(
        AND,
        Tm::Pi(
            Box::new(Tm::Ind(BOOL)),
            Box::new(Tm::Pi(Box::new(Tm::Ind(BOOL)), Box::new(Tm::Ind(BOOL)))),
        ),
        and_body(),
    )?;
    e.add_const(
        ALL_LEAF,
        Tm::Pi(Box::new(Tm::Ind(CTREE)), Box::new(Tm::Ind(BOOL))),
        all_leaf_body(),
    )?;
    e.add_const(
        IS_TRUE,
        Tm::Pi(Box::new(Tm::Ind(BOOL)), Box::new(Tm::Sort(0))),
        is_true_body(),
    )?;
    Ok(e)
}

/// Balanced binary Ctree of the given depth; every leaf carries `b`. depth 0 = a single leaf.
fn balanced(depth: u32, b: &Tm) -> Tm {
    if depth == 0 {
        leaf(b.clone())
    } else {
        node(balanced(depth - 1, b), balanced(depth - 1, b))
    }
}

/// depth-4 all-`true` tree with ONE leaf flipped to `false` (left-most): all_leaf ⇒ false.
fn balanced_with_one_false(depth: u32) -> Tm {
    if depth == 0 {
        leaf(fls())
    } else {
        node(
            balanced_with_one_false(depth - 1),
            balanced(depth - 1, &tru()),
        )
    }
}

fn is_true_of(b: Tm) -> Tm {
    app(Tm::Const(IS_TRUE), b)
}
fn all_leaf_of(t: Tm) -> Tm {
    app(Tm::Const(ALL_LEAF), t)
}

// ════════════════════════ ADMISSION (kernel-have check) ════════════════════════

#[test]
fn admits_bool_ctree_eq_and_consts() {
    // Every inductive (incl. the indexed `eq`) and const must be admitted by the SOUNDNESS
    // gates (positivity R3 + field-universe R11 + δ-acyclicity R7). If `eq` cannot be admitted,
    // this fails and pinpoints the gap.
    let env = demo_env().expect("Bool/Ctree/eq + and/all_leaf/is_true admitted by the kernel");
    assert!(env.inds.contains_key(&EQ), "indexed eq is admitted");
    assert!(
        env.const_body(ALL_LEAF).is_some(),
        "all_leaf recursor const stored"
    );
}

// ════════════════════════ ι CHAIN (the compute) ════════════════════════

#[test]
fn iota_chains_all_leaf_true_tree_to_true() {
    // depth-4 balanced tree (16 leaves, 31 ctors). `all_leaf` ι-reduces the whole tree to a
    // single Bool — the recursor fires once per ctor, AND-folding 16 `true`s through 15 nodes.
    let env = demo_env().expect("demo env");
    let big = balanced(4, &tru());
    assert_eq!(
        nf_tm(&env, &Vec::new(), &all_leaf_of(big)),
        tru(),
        "all_leaf over an all-true depth-4 tree ι-reduces to Bool.true"
    );
}

#[test]
fn iota_chains_all_leaf_false_tree_to_false() {
    // Same shape, one leaf flipped: the `and` short-circuit propagates `false` up the spine.
    let env = demo_env().expect("demo env");
    let bad = balanced_with_one_false(4);
    assert_eq!(
        nf_tm(&env, &Vec::new(), &all_leaf_of(bad)),
        fls(),
        "all_leaf over a tree with a false leaf ι-reduces to Bool.false"
    );
}

// ════════════════════════ THE DEMO: reflection-closing by conv ════════════════════════

#[test]
fn demo_is_true_all_leaf_big_tree_closes_to_true() {
    // POSITIVE: `is_true (all_leaf BIG_TREE) ≡ is_true true`. conv (needs_typed_conv ⇒ nf path)
    // δ-unfolds is_true/all_leaf, ι-drives the tree to true, then `eq Bool true true` on both
    // sides α-match. This is fourcolor's `reducibility`-closing on a fourcolor-shaped workload.
    let env = demo_env().expect("demo env");
    let big = balanced(4, &tru());
    let goal = is_true_of(all_leaf_of(big)); // eq Bool (all_leaf BIG) true
    let closed = is_true_of(tru()); // eq Bool true true   (the refl-witness type)
    assert!(
        conv(&env, &Vec::new(), &goal, &closed).expect("conv on closed kernel terms"),
        "is_true (all_leaf BIG_TREE) ≡ is_true true (reflection closes by ι+conv)"
    );
}

#[test]
fn demo_negative_control_false_tree_does_not_close() {
    // NEGATIVE (no-false-green): a tree whose `all_leaf` is FALSE must NOT close to true —
    // `eq Bool false true` is NOT convertible to `eq Bool true true`. Guards against the demo
    // being trivially/vacuously true.
    let env = demo_env().expect("demo env");
    let bad = balanced_with_one_false(4);
    let goal = is_true_of(all_leaf_of(bad)); // eq Bool false true
    let closed = is_true_of(tru()); // eq Bool true true
    assert!(
        !conv(&env, &Vec::new(), &goal, &closed).expect("conv on closed kernel terms"),
        "is_true (all_leaf BAD_TREE) must NOT ≡ is_true true (false ≠ true under conv)"
    );
}
