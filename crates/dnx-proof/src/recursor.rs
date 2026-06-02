//! Recursor (Elim) type synthesis (§5; proofs.md:163-181). Covers the full P (params) and
//! X (indices) telescopes, incl. indexed families (A6, e.g. `Vec A n`). The motive abstracts
//! the indices and the scrutinee; minors thread `ret_indices_k` at the result and `idx rec_j`
//! in each IH. ι REDUCTION (driver.rs) is the matching computation rule.

use crate::inductive::Inductive;
use crate::symbol::IndId;
use crate::tm::{shift, Level, Tm};

fn apply(head: Tm, args: &[Tm]) -> Tm {
    args.iter()
        .fold(head, |f, a| Tm::App(Box::new(f), Box::new(a.clone())))
}

fn head_is_ind(t: &Tm, id: IndId) -> bool {
    match t {
        Tm::Ind(j) => *j == id,
        Tm::App(f, _) => head_is_ind(f, id),
        Tm::Pi(_, b) => head_is_ind(b, id),
        _ => false,
    }
}

/// `I P X` applied to the `p` param vars + `nidx` index vars visible at de Bruijn `depth`
/// (the binder where this `I P X` sits). Param `a` is below the X band; index `t` is innermost.
/// proofs.md:171,177 `I P X`.
fn ind_app(i: IndId, p: usize, nidx: usize, depth_above_params: usize) -> Tm {
    let params = (0..p).map(|a| Tm::Var((nidx + depth_above_params + (p - 1 - a)) as u32));
    let indices = (0..nidx).map(|t| Tm::Var((nidx - 1 - t) as u32));
    apply(Tm::Ind(i), &params.chain(indices).collect::<Vec<_>>())
}

/// Recursor type (§5; proofs.md:163-181), motive result level `lm` free (large-elim, A5):
/// `Π(P) Π(motive: Π(X)(x:I P X).Sort lm) Π(minor_k: MINOR_k)… Π(X) Π(x:I P X). motive X x`.
pub fn recursor_type(ind: &Inductive, lm: Level) -> Option<Tm> {
    let i = ind.id;
    let p = ind.params.len();
    let c = ind.ctors.len();
    let nidx = ind.indices.len();

    // result `motive X x` at depth p+1+c+nidx+1: motive=Var(1+nidx+c); X_t=Var(nidx-t); x=Var0.
    let mut result_args: Vec<Tm> = (0..nidx).map(|t| Tm::Var((nidx - t) as u32)).collect();
    result_args.push(Tm::Var(0));
    let mut body = apply(Tm::Var((1 + nidx + c) as u32), &result_args);
    // scrutinee Π(x:I P X). … ; at the x-binder the P band sits above (motive=1, minors=c).
    let scrut = ind_app(i, p, nidx, 1 + c);
    body = Tm::Pi(Box::new(scrut), Box::new(body));
    // X-index binders (X_0 outermost). Index type lives in decl ctx [P,X_<t]; here the P band is
    // motive+minors = 1+c higher ⇒ shift param refs by 1+c above the t already-bound indices.
    for t in (0..nidx).rev() {
        let idx_ty = shift(&ind.indices[t], (1 + c) as i64, t as u32);
        body = Tm::Pi(Box::new(idx_ty), Box::new(body));
    }
    // minor binders (minor_0 outermost).
    for k in (0..c).rev() {
        body = Tm::Pi(Box::new(minor_type(ind, k)), Box::new(body));
    }
    // motive : Π(X)(x:I P X).Sort lm — built in ctx [P], so index types are used as-is.
    let mut motive_ty = Tm::Pi(Box::new(ind_app(i, p, nidx, 0)), Box::new(Tm::Sort(lm)));
    for t in (0..nidx).rev() {
        motive_ty = Tm::Pi(Box::new(ind.indices[t].clone()), Box::new(motive_ty));
    }
    body = Tm::Pi(Box::new(motive_ty), Box::new(body));
    // param binders (P_0 outermost); param types reference only earlier params (same outer band).
    for a in (0..p).rev() {
        body = Tm::Pi(Box::new(ind.params[a].clone()), Box::new(body));
    }
    Some(body)
}

/// `MINOR_k = Π(A_k) Π(ih_j: motive (idx rec_j) rec_j)… → motive (ret_indices_k) (Ctor I k P A_k)`
/// (proofs.md:177-180). de Bruijn indices target the FINAL nested term. `p` = #params.
fn minor_type(ind: &Inductive, k: usize) -> Tm {
    let i = ind.id;
    let p = ind.params.len();
    let fields = &ind.ctors[k].args;
    let m = fields.len();
    let recs: Vec<usize> = (0..m).filter(|&q| head_is_ind(&fields[q], i)).collect();
    let r = recs.len();
    let ret = &ind.ctors[k].ret_indices;

    // body context = [P, motive, minor_<k, field_0..field_{m-1}, ih_0..ih_{r-1}] (depth m+r inside).
    // motive = Var(m+r+k); P_a = Var(m+r+k+1+(p-1-a)); field_q = Var(r+(m-1-q)).
    let motive_v = (m + r + k) as u32;
    let param_vars: Vec<Tm> = (0..p)
        .map(|a| Tm::Var((m + r + k + 1 + (p - 1 - a)) as u32))
        .collect();
    let field_vars: Vec<Tm> = (0..m).map(|q| Tm::Var((r + (m - 1 - q)) as u32)).collect();

    // result motive (ret_indices_k) (Ctor I k P fields). ret_indices live in decl ctx [P,A_k];
    // relocate to body ctx: lift field refs by `r`, then param refs (≥ r+m) by `k+1` (proofs.md:180).
    let ret_args: Vec<Tm> = ret
        .iter()
        .map(|ri| shift(&shift(ri, r as i64, 0), (k + 1) as i64, (r + m) as u32))
        .collect();
    let ctor = apply(Tm::Ctor(i, k as u32), &param_vars);
    let ctor = apply(ctor, &field_vars);
    let mut motive_app = apply(Tm::Var(motive_v), &ret_args);
    motive_app = Tm::App(Box::new(motive_app), Box::new(ctor));
    let mut body = motive_app;

    // ih binders (ih_0 outermost): ih_j : motive (idx rec_j) rec_j. At the ih_j binder, j IHs are
    // bound below ⇒ motive=Var(m+j+k); field_{recs[j]}=Var(j+(m-1-q)); rec_j's own ret indices.
    for j in (0..r).rev() {
        let q = recs[j];
        let mvar = (m + j + k) as u32;
        // idx rec_j = the index args in the recursive field's own type `I P idxs` (proofs.md:187).
        // `idxs` live in field_q's decl ctx [P, f_<q] (depth q); relocate to this ih ctx
        // [P, motive, minor_<k, f_<m, ih_<j]: lift field refs by (j+m-q), then param refs (≥ j+m)
        // by motive+minors = k+1.
        let idxs = ind_indices(&fields[q], i, p);
        let idx_args: Vec<Tm> = idxs
            .iter()
            .map(|t| {
                shift(
                    &shift(t, (j + m - q) as i64, 0),
                    (k + 1) as i64,
                    (j + m) as u32,
                )
            })
            .collect();
        let ih_field = Tm::Var((j + (m - 1 - q)) as u32);
        let mut ih = apply(Tm::Var(mvar), &idx_args);
        ih = Tm::App(Box::new(ih), Box::new(ih_field));
        body = Tm::Pi(Box::new(ih), Box::new(body));
    }
    // field binders (field_0 outermost). Field type lives in decl ctx [P,field_<q]; relocate to
    // minor ctx [P,motive,minor_<k,field_<q] ⇒ shift param refs (≥ q) by motive+minors = k+1.
    for q in (0..m).rev() {
        let fty = shift(&fields[q], (k + 1) as i64, q as u32);
        body = Tm::Pi(Box::new(fty), Box::new(body));
    }
    body
}

/// Index arguments of a recursive field type `I P idxs` (the `nidx` args after the `p` params).
/// Returns the `idxs` terms in the field's own de Bruijn context (proofs.md:187, Lean:737).
fn ind_indices(field_ty: &Tm, i: IndId, p: usize) -> Vec<Tm> {
    let mut args = Vec::new();
    let mut cur = field_ty;
    while let Tm::App(f, x) = cur {
        args.push((**x).clone());
        cur = f;
    }
    if matches!(cur, Tm::Ind(j) if *j == i) && args.len() >= p {
        args.reverse();
        args[p..].to_vec()
    } else {
        Vec::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inductive::CtorDecl;

    fn nat() -> Inductive {
        Inductive {
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
        }
    }

    #[test]
    fn nat_recursor_type_shape() {
        // Π(motive:Nat→Sort1) Π(mz: motive zero) Π(ms: Π(n:Nat).motive n→motive(succ n)) Π(x:Nat). motive x
        let rt = recursor_type(&nat(), 1).unwrap();
        let expect = Tm::Pi(
            Box::new(Tm::Pi(Box::new(Tm::Ind(IndId(0))), Box::new(Tm::Sort(1)))), // motive
            Box::new(Tm::Pi(
                Box::new(Tm::App(
                    Box::new(Tm::Var(0)),
                    Box::new(Tm::Ctor(IndId(0), 0)),
                )), // mz: motive zero
                Box::new(Tm::Pi(
                    // ms: Π(n:Nat). Π(_: motive n). motive (succ n)
                    Box::new(Tm::Pi(
                        Box::new(Tm::Ind(IndId(0))),
                        Box::new(Tm::Pi(
                            Box::new(Tm::App(Box::new(Tm::Var(2)), Box::new(Tm::Var(0)))),
                            Box::new(Tm::App(
                                Box::new(Tm::Var(3)),
                                Box::new(Tm::App(
                                    Box::new(Tm::Ctor(IndId(0), 1)),
                                    Box::new(Tm::Var(1)),
                                )),
                            )),
                        )),
                    )),
                    Box::new(Tm::Pi(
                        Box::new(Tm::Ind(IndId(0))),                                   // x:Nat
                        Box::new(Tm::App(Box::new(Tm::Var(3)), Box::new(Tm::Var(0)))), // motive x
                    )),
                )),
            )),
        );
        assert_eq!(rt, expect);
    }
}
