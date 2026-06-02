//! Typed-layer reduction (δ/ι live OUTSIDE Ω_K, per settled §6). v1 does β+δ+ι at the Tm
//! level; the net engine remains the β-authority for pure-λ conv.

use crate::env::GlobalEnv;
use crate::infer::Ctx;
use crate::symbol::IndId;
use crate::tm::{shift, subst, Tm};

/// Flatten an application spine: returns the non-`App` head and its arguments left→right.
pub(crate) fn spine(t: &Tm) -> (Tm, Vec<Tm>) {
    let mut args = Vec::new();
    let mut cur = t;
    while let Tm::App(f, x) = cur {
        args.push((**x).clone());
        cur = f;
    }
    args.reverse();
    (cur.clone(), args)
}

/// Rebuild `head` applied to `args`.
fn apply(head: Tm, args: &[Tm]) -> Tm {
    args.iter()
        .fold(head, |f, a| Tm::App(Box::new(f), Box::new(a.clone())))
}

/// Head of a (possibly applied) type is the inductive `id` (walks Pi codomains / App spine).
pub(crate) fn head_is_ind(t: &Tm, id: IndId) -> bool {
    match t {
        Tm::Ind(j) => *j == id,
        Tm::App(f, _) => head_is_ind(f, id),
        Tm::Pi(_, b) => head_is_ind(b, id),
        _ => false,
    }
}

/// Weak-head normal form: β (App-Lam) + δ (Const unfold) + ι (Elim-of-Ctor).
/// Stuck heads (Var / neutral spine / underapplied Elim / Elim on neutral) are returned as-is.
/// `ctx` is the binder context of `t` (the scrutinee + ctor fields share it), so indexed-ι can
/// type a recursive field correctly even under binders (proofs.md:187 `idx rec_j`, A6).
pub fn whnf_tm(env: &GlobalEnv, ctx: &Ctx, t: &Tm) -> Tm {
    let mut cur = t.clone();
    loop {
        let (head, args) = spine(&cur);
        match head {
            Tm::Lam(_, body) if !args.is_empty() => {
                cur = apply(subst(&body, 0, &args[0]), &args[1..]); // β
            }
            Tm::Const(c) => match env.const_body(c) {
                Some(b) => cur = apply(b.clone(), &args), // δ
                None => return cur,
            },
            Tm::Elim(i) => match try_iota(env, ctx, i, &args) {
                Some(r) => cur = r, // ι
                None => return cur, // R4 (neutral scrutinee) / R5 (underapplied) ⇒ stuck
            },
            _ => return cur,
        }
    }
}

/// ι: `Elim I  P  motive  minor_0..  X  (Ctor I k P fields)`  ⟶  `minor_k fields (ih…)`
/// where each recursive field contributes `ih = Elim I P motive minors X' field`.
/// Spine layout (§5): nparams · motive · nctors minors · nindices · scrutinee.
fn try_iota(env: &GlobalEnv, ctx: &Ctx, i: IndId, args: &[Tm]) -> Option<Tm> {
    let ind = env.inds.get(&i)?;
    let np = ind.params.len();
    let nidx = ind.indices.len();
    let nctors = ind.ctors.len();
    let expected = np + 1 + nctors + nidx + 1;
    if args.len() < expected {
        return None; // R5: underapplied recursor stays stuck
    }
    // Scrutinee = last consumed arg; reduce to expose a constructor.
    let scrut = whnf_tm(env, ctx, &args[expected - 1]);
    let (chead, cargs) = spine(&scrut);
    let k = match chead {
        Tm::Ctor(j, k) if j == i => k as usize, // ctor of THIS inductive
        _ => return None,                       // R4: ι never fires on a neutral/non-ctor head
    };
    if k >= nctors {
        return None;
    }
    let fields = &cargs[np.min(cargs.len())..]; // drop the ctor's parameter prefix
    let minor = args[np + 1 + k].clone();

    // minor applied to the constructor fields…
    let mut res = apply(minor, fields);
    // …then one inductive hypothesis per recursive field:
    //   ih_j = Elim I params motive minors (idx rec_j) rec_j   (proofs.md:187, Lean:737).
    let elim_prefix = &args[..np + 1 + nctors]; // I-params · motive · minors  (shared by every IH)
    for (pos, arg_ty) in ind.ctors[k].args.iter().enumerate() {
        if head_is_ind(arg_ty, i) {
            let field = fields.get(pos)?.clone();
            let mut ih = apply(Tm::Elim(i), elim_prefix);
            // thread `idx rec_j`: the index args of the field's own type `I P idxs`.
            ih = apply(ih, &field_indices(env, ctx, i, np, nidx, &field)?);
            ih = Tm::App(Box::new(ih), Box::new(field));
            res = Tm::App(Box::new(res), Box::new(ih));
        }
    }
    // Re-apply any spine args beyond the recursor's own arity.
    Some(apply(res, &args[expected..]))
}

/// `idx rec_j`: the index arguments of a recursive field `rec_j`, read off its inferred type
/// `I P idxs` (proofs.md:187; Lean `inductive.cpp:737`). Returns the `nidx` index args after the
/// `np` params. A NON-indexed family (`nidx == 0`) has no indices to thread — return `[]` without
/// inferring. The field is a subterm of the scrutinee, which lives in `ctx`; typing it in that
/// SAME context (not the empty one) lets indexed ι fire under binders too (A6), e.g. an indexed
/// recursor in the inductive step of a proof where the field mentions outer bound vars.
fn field_indices(
    env: &GlobalEnv,
    ctx: &Ctx,
    i: IndId,
    np: usize,
    nidx: usize,
    field: &Tm,
) -> Option<Vec<Tm>> {
    if nidx == 0 {
        return Some(Vec::new());
    }
    let ty = whnf_tm(env, ctx, &crate::infer::infer(env, ctx, field).ok()?);
    let (head, args) = spine(&ty);
    if matches!(head, Tm::Ind(j) if j == i) && args.len() >= np {
        Some(args[np..].to_vec())
    } else {
        None
    }
}

/// Does `Var(k)` occur in `t` (k incremented under each binder)?
fn occurs_var(t: &Tm, k: u32) -> bool {
    match t {
        Tm::Var(i) => *i == k,
        Tm::Pi(a, b) | Tm::Lam(a, b) => occurs_var(a, k) || occurs_var(b, k + 1),
        Tm::App(a, b) => occurs_var(a, k) || occurs_var(b, k),
        _ => false,
    }
}

/// Full normal form: whnf the head, then normalize every subterm. Includes η-contraction
/// (`λx. f x` with `x ∉ FV(f)` ⟶ `f`) so η-equal terms share a normal form (A4). `ctx` is
/// extended with each binder's domain so ι under a λ/Π sees the right context (A6).
pub fn nf_tm(env: &GlobalEnv, ctx: &Ctx, t: &Tm) -> Tm {
    match whnf_tm(env, ctx, t) {
        Tm::Lam(d, b) => {
            let dom = nf_tm(env, ctx, &d);
            let mut inner = ctx.clone();
            inner.push((*d).clone());
            let body = nf_tm(env, &inner, &b);
            if let Tm::App(f, arg) = &body {
                if matches!(**arg, Tm::Var(0)) && !occurs_var(f, 0) {
                    return shift(f, -1, 0); // η-contract
                }
            }
            Tm::Lam(Box::new(dom), Box::new(body))
        }
        Tm::Pi(d, b) => {
            let dom = nf_tm(env, ctx, &d);
            let mut inner = ctx.clone();
            inner.push((*d).clone());
            Tm::Pi(Box::new(dom), Box::new(nf_tm(env, &inner, &b)))
        }
        Tm::App(f, x) => Tm::App(Box::new(nf_tm(env, ctx, &f)), Box::new(nf_tm(env, ctx, &x))),
        other => other,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::ConstId;
    use crate::tm::Tm;

    fn lam(b: Tm) -> Tm {
        Tm::Lam(Box::new(Tm::Sort(0)), Box::new(b))
    }

    #[test]
    fn beta_whnf() {
        // (λx.x) (λy.y)  →  λy.y
        let env = GlobalEnv::default();
        let id = lam(Tm::Var(0));
        let app = Tm::App(Box::new(lam(Tm::Var(0))), Box::new(id.clone()));
        assert_eq!(whnf_tm(&env, &Vec::new(), &app), id);
    }

    #[test]
    fn delta_unfold() {
        // c := λx.λy.x  (K) ; (c a) b  →  a
        let mut env = GlobalEnv::default();
        let k = lam(lam(Tm::Var(1)));
        env.add_const(ConstId(0), Tm::Sort(0), k).unwrap();
        // a, b modelled as distinct consts d, e (neutral atoms)
        env.add_const(ConstId(1), Tm::Sort(0), Tm::Sort(0)).unwrap(); // d (body irrelevant)
        env.add_const(ConstId(2), Tm::Sort(0), Tm::Sort(0)).unwrap(); // e
        let a = Tm::App(
            Box::new(Tm::App(
                Box::new(Tm::Const(ConstId(0))),
                Box::new(Tm::Var(7)),
            )),
            Box::new(Tm::Var(8)),
        );
        // whnf: c unfolds (δ), two β → Var(7)
        assert_eq!(whnf_tm(&env, &Vec::new(), &a), Tm::Var(7));
    }

    #[test]
    fn nf_recurses_under_lambda() {
        // λz. (λx.x) z   →  λz. z
        let env = GlobalEnv::default();
        let inner = Tm::App(Box::new(lam(Tm::Var(0))), Box::new(Tm::Var(0)));
        let outer = lam(inner);
        assert_eq!(nf_tm(&env, &Vec::new(), &outer), lam(Tm::Var(0)));
    }

    // ── ι / recursor ──
    use crate::inductive::{CtorDecl, Inductive};
    use crate::symbol::IndId;

    fn nat_env() -> GlobalEnv {
        // Nat := zero | succ (_:Nat)
        let nat = Inductive {
            id: IndId(0),
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
                    args: vec![Tm::Ind(IndId(0))],
                    ret_indices: vec![],
                },
            ],
        };
        let mut env = GlobalEnv::default();
        env.add_inductive(nat).unwrap();
        env
    }
    fn zero() -> Tm {
        Tm::Ctor(IndId(0), 0)
    }
    fn succ(n: Tm) -> Tm {
        Tm::App(Box::new(Tm::Ctor(IndId(0), 1)), Box::new(n))
    }
    /// Elim Nat motive minor_zero minor_succ scrut
    fn nat_rec(motive: Tm, mz: Tm, ms: Tm, scrut: Tm) -> Tm {
        apply(Tm::Elim(IndId(0)), &[motive, mz, ms, scrut])
    }

    #[test]
    fn a2_nat_rec_counts() {
        // rec with minor_succ = λpred.λih. succ ih  reconstructs the numeral: rec(2) = 2.
        let env = nat_env();
        let ms = Tm::Lam(
            Box::new(Tm::Ind(IndId(0))),
            Box::new(Tm::Lam(
                Box::new(Tm::Ind(IndId(0))),
                Box::new(succ(Tm::Var(0))),
            )),
        );
        let two = succ(succ(zero()));
        let r = nat_rec(Tm::Sort(0), zero(), ms, two.clone());
        assert_eq!(
            nf_tm(&env, &Vec::new(), &r),
            two,
            "Nat.rec on succ(succ zero) ι-reduces to 2 (A2)"
        );
    }

    #[test]
    fn r5_underapplied_recursor_stuck() {
        // Elim Nat motive minor_zero  (missing minor_succ + scrutinee) ⇒ stays stuck.
        let env = nat_env();
        let t = apply(Tm::Elim(IndId(0)), &[Tm::Sort(0), zero()]);
        assert_eq!(
            whnf_tm(&env, &Vec::new(), &t),
            t,
            "underapplied recursor must not fire (R5)"
        );
    }

    #[test]
    fn r4_iota_on_neutral_stuck() {
        // scrutinee = Var(0) (neutral, no ctor exposed) ⇒ ι must not fire.
        let env = nat_env();
        let t = nat_rec(Tm::Sort(0), zero(), zero(), Tm::Var(0));
        assert_eq!(
            whnf_tm(&env, &Vec::new(), &t),
            t,
            "ι on neutral head must not fire (R4)"
        );
    }
}
