//! infer / check — the TCB typing rules (§2). The ONLY caller of `conv` is T-Conv.
//! Universe side-conditions (T-Sort `ℓ+1`, T-Pi `max`) plug R1/R2. Predicative,
//! non-cumulative, monomorphic levels (§3).

use crate::conv::conv;
use crate::driver::whnf_tm;
use crate::env::GlobalEnv;
use crate::recursor::recursor_type;
use crate::tm::{shift, subst, Level, Tm};
use crate::universe::{max, succ};

#[derive(Debug, PartialEq, Eq)]
pub enum TypeError {
    UnboundVar,
    UnknownConst,
    UnknownInd,
    NotASort,
    NotAPi,
    Mismatch,
    Unsupported(&'static str),
}

/// Context: `ctx[ctx.len()-1-i]` is the binder type of `Var(i)` (innermost last).
pub(crate) type Ctx = Vec<Tm>;

/// Type of `Var(i)`: the stored binder type shifted into the current scope (`+ (i+1)`).
fn var_type(ctx: &Ctx, i: u32) -> Result<Tm, TypeError> {
    let n = ctx.len();
    let idx = (i as usize)
        .checked_add(1)
        .filter(|&k| k <= n)
        .ok_or(TypeError::UnboundVar)?;
    Ok(shift(&ctx[n - idx], (i + 1) as i64, 0))
}

pub fn infer(env: &GlobalEnv, ctx: &Ctx, t: &Tm) -> Result<Tm, TypeError> {
    // Applied recursors need their motive to synthesize a type — handle the whole spine.
    let (head, args) = spine(t);
    if let Tm::Elim(i) = head {
        return infer_elim(env, ctx, i, &args);
    }
    match t {
        Tm::Var(i) => var_type(ctx, *i),
        Tm::Sort(l) => Ok(Tm::Sort(succ(*l))), // R1: Sort l : Sort (l+1), never Sort l : Sort l
        Tm::Pi(a, b) => {
            let i = sort_of(env, ctx, a)?;
            let mut c2 = ctx.clone();
            c2.push((**a).clone());
            let j = sort_of(env, &c2, b)?;
            Ok(Tm::Sort(max(i, j))) // R2: codomain sort joined with domain, not placed too low
        }
        Tm::Lam(a, b) => {
            sort_of(env, ctx, a)?;
            let mut c2 = ctx.clone();
            c2.push((**a).clone());
            let bt = infer(env, &c2, b)?;
            Ok(Tm::Pi(a.clone(), Box::new(bt)))
        }
        Tm::App(f, x) => {
            let ft = infer(env, ctx, f)?;
            let (dom, cod) = as_pi(env, ctx, &ft)?;
            check(env, ctx, x, &dom)?;
            Ok(subst(&cod, 0, x)) // B[0:=a]
        }
        Tm::Const(c) => env
            .consts
            .get(c)
            .map(|(ty, _)| ty.clone())
            .ok_or(TypeError::UnknownConst),
        Tm::Ind(i) => {
            let ind = env.inds.get(i).ok_or(TypeError::UnknownInd)?;
            // arity = Π params. Π indices. Sort sort
            Ok(telescope(
                &ind.params,
                telescope(&ind.indices, Tm::Sort(ind.sort)),
            ))
        }
        Tm::Ctor(i, k) => {
            let ind = env.inds.get(i).ok_or(TypeError::UnknownInd)?;
            let cd = ind
                .ctors
                .iter()
                .find(|c| c.ctor_ix == *k)
                .ok_or(TypeError::Unsupported("ctor index"))?;
            // ctor type = Π(P) Π(A_k). I P ret_indices  (return head is `I` applied to the param
            // vars THEN the ret indices; proofs.md:177 `Ctor I k P A_k : I P ret_indices_k`).
            let np = ind.params.len();
            let m = cd.args.len();
            let pvars = (0..np).map(|a| Tm::Var((m + (np - 1 - a)) as u32));
            let head_args: Vec<Tm> = pvars.chain(cd.ret_indices.iter().cloned()).collect();
            let ret = apply(Tm::Ind(*i), &head_args);
            Ok(telescope(&ind.params, telescope(&cd.args, ret)))
        }
        // A bare `Elim` head is intercepted by the spine short-circuit above; reaching this
        // arm means an upstream slip, so fail with a TypeError rather than panic in the TCB.
        Tm::Elim(_) => Err(TypeError::Unsupported("Elim must be applied (spine head)")),
    }
}

/// Flatten an application spine: non-`App` head + args left→right.
fn spine(t: &Tm) -> (Tm, Vec<Tm>) {
    let mut args = Vec::new();
    let mut cur = t;
    while let Tm::App(f, x) = cur {
        args.push((**x).clone());
        cur = f;
    }
    args.reverse();
    (cur.clone(), args)
}

/// Type an (applied) recursor: synthesize its type from the motive's result level (§5),
/// then type-check the supplied arguments against it. Covers params + indices (the spine is
/// `params · motive · minors · indices · scrutinee`, proofs.md:171; driver.rs:61).
fn infer_elim(
    env: &GlobalEnv,
    ctx: &Ctx,
    i: crate::symbol::IndId,
    args: &[Tm],
) -> Result<Tm, TypeError> {
    let ind = env.inds.get(&i).ok_or(TypeError::UnknownInd)?;
    let nparams = ind.params.len();
    let nidx = ind.indices.len();
    // The motive follows the param telescope (proofs.md:171); only its result level is needed
    // here (the params themselves are checked by the application loop below).
    let motive = args.get(nparams).ok_or(TypeError::Unsupported(
        "recursor needs its params + motive (monomorphic levels)",
    ))?;
    // motive : Π(X)(x:I P X). Sort lm — peel the nidx index binders + the scrutinee, then the
    // result level is free (large elimination, A5; proofs.md:171).
    let mut mty = infer(env, ctx, motive)?;
    for _ in 0..nidx + 1 {
        let (_dom, cod) = as_pi(env, ctx, &mty)?;
        mty = cod;
    }
    let lm = match whnf_tm(env, ctx, &mty) {
        Tm::Sort(l) => l,
        _ => return Err(TypeError::Unsupported("motive must land in a sort")),
    };
    let rty = recursor_type(ind, lm).ok_or(TypeError::Unsupported(
        "recursor type for parametrised/indexed family (A6)",
    ))?;
    // Apply args to the recursor type via the ordinary T-App rule.
    let mut cur = rty;
    for a in args {
        let (dom, cod) = as_pi(env, ctx, &cur)?;
        check(env, ctx, a, &dom)?;
        cur = subst(&cod, 0, a);
    }
    Ok(cur)
}

/// T-Conv: `check` infers then converts at the goal type (the ONLY `conv` call site).
pub fn check(env: &GlobalEnv, ctx: &Ctx, t: &Tm, ty: &Tm) -> Result<(), TypeError> {
    let got = infer(env, ctx, t)?;
    match conv(env, ctx, &got, ty) {
        Ok(true) => Ok(()),
        Ok(false) => Err(TypeError::Mismatch),
        Err(_) => Err(TypeError::Mismatch),
    }
}

pub(crate) fn sort_of(env: &GlobalEnv, ctx: &Ctx, t: &Tm) -> Result<Level, TypeError> {
    match whnf_tm(env, ctx, &infer(env, ctx, t)?) {
        Tm::Sort(l) => Ok(l),
        _ => Err(TypeError::NotASort),
    }
}

fn as_pi(env: &GlobalEnv, ctx: &Ctx, t: &Tm) -> Result<(Tm, Tm), TypeError> {
    match whnf_tm(env, ctx, t) {
        Tm::Pi(a, b) => Ok((*a, *b)),
        _ => Err(TypeError::NotAPi),
    }
}

fn apply(head: Tm, args: &[Tm]) -> Tm {
    args.iter()
        .fold(head, |f, a| Tm::App(Box::new(f), Box::new(a.clone())))
}

/// Build `Π tele. body` from a left→right telescope (de Bruijn-correct: outer first).
fn telescope(tele: &[Tm], body: Tm) -> Tm {
    tele.iter()
        .rev()
        .fold(body, |acc, ty| Tm::Pi(Box::new(ty.clone()), Box::new(acc)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tm::Tm;

    #[test]
    fn sort_infers_successor() {
        let env = GlobalEnv::default();
        assert_eq!(infer(&env, &Vec::new(), &Tm::Sort(0)).unwrap(), Tm::Sort(1));
    }

    #[test]
    fn r1_type_in_type_rejected() {
        // Sort 0 : Sort 0 must FAIL — infer gives Sort 1, not Sort 0.
        let env = GlobalEnv::default();
        assert!(check(&env, &Vec::new(), &Tm::Sort(0), &Tm::Sort(0)).is_err());
    }

    #[test]
    fn r2_pi_takes_max_universe() {
        // Π(A:Sort1). Sort0  :  Sort (max 2 1) = Sort 2   (domain Sort1 : Sort2)
        let env = GlobalEnv::default();
        let pi = Tm::Pi(Box::new(Tm::Sort(1)), Box::new(Tm::Sort(0)));
        assert_eq!(infer(&env, &Vec::new(), &pi).unwrap(), Tm::Sort(2));
    }

    #[test]
    fn a1_polymorphic_identity_checks() {
        // id := λ(A:Sort0). λ(x:A). x   :   Π(A:Sort0). Π(x:A). A
        let env = GlobalEnv::default();
        let id = Tm::Lam(
            Box::new(Tm::Sort(0)),
            Box::new(Tm::Lam(Box::new(Tm::Var(0)), Box::new(Tm::Var(0)))),
        );
        let ty = Tm::Pi(
            Box::new(Tm::Sort(0)),
            Box::new(Tm::Pi(Box::new(Tm::Var(0)), Box::new(Tm::Var(1)))),
        );
        assert_eq!(infer(&env, &Vec::new(), &id).unwrap(), ty.clone());
        assert!(check(&env, &Vec::new(), &id, &ty).is_ok());
    }

    #[test]
    fn app_substitutes_codomain() {
        // (λ(x:Sort0). x) applied to Sort0 : Sort0  →  App : Sort0
        let env = GlobalEnv::default();
        let f = Tm::Lam(Box::new(Tm::Sort(1)), Box::new(Tm::Var(0)));
        // f : Π(_:Sort1).Sort1 ; apply Sort0 (: Sort1)
        let app = Tm::App(Box::new(f), Box::new(Tm::Sort(0)));
        assert_eq!(infer(&env, &Vec::new(), &app).unwrap(), Tm::Sort(1));
    }
}
