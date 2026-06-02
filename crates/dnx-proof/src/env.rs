use crate::inductive::{ArityTable, Inductive};
use crate::symbol::ConstId;
use crate::tm::Tm;
use std::collections::HashMap;

#[derive(Default)]
pub struct GlobalEnv {
    pub consts: HashMap<ConstId, (Tm, Tm)>, // (ty, body)
    pub inds: HashMap<crate::symbol::IndId, Inductive>,
    pub recursors: HashMap<crate::symbol::IndId, ArityTable>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum AdmitError {
    Cycle(ConstId),
    Duplicate,
    BadDecl(&'static str),
}

impl GlobalEnv {
    /// δ-acyclicity: body may only reference consts ALREADY admitted ⇒ DAG (R7).
    pub fn add_const(&mut self, id: ConstId, ty: Tm, body: Tm) -> Result<(), AdmitError> {
        if self.consts.contains_key(&id) {
            return Err(AdmitError::Duplicate);
        }
        if refs_unknown_const(&body, &self.consts, id) {
            return Err(AdmitError::Cycle(id));
        }
        self.consts.insert(id, (ty, body));
        Ok(())
    }

    pub fn const_body(&self, id: ConstId) -> Option<&Tm> {
        self.consts.get(&id).map(|(_, b)| b)
    }

    /// Admit an inductive type: strict positivity (R3) + ctor-field universe (R11), then
    /// builds the ArityTable. R11 (proofs.md §4:155, Lean `inductive.cpp:435-442`): each
    /// ctor field's sort level ≤ the declared `sort` — STRICT, no `is_zero`/Prop escape
    /// (dnx predicative). A large field in a small inductive breaks predicativity ⇒ False.
    pub fn add_inductive(&mut self, ind: Inductive) -> Result<(), AdmitError> {
        if self.inds.contains_key(&ind.id) {
            return Err(AdmitError::Duplicate);
        }
        // R3: every ctor arg type must be strictly positive in the inductive's own id.
        for c in &ind.ctors {
            for arg in &c.args {
                if !crate::positivity::strictly_positive(self, ind.id, arg) {
                    return Err(AdmitError::BadDecl("non-positive"));
                }
            }
        }
        // R11 + ret-index well-formedness both need `infer(Ind self.id)` to resolve `Ind`/recursive
        // occurrences ⇒ register arity first, roll back on rejection (positivity already passed, so
        // only the two field/index checks below can still fail).
        let id = ind.id;
        self.inds.insert(id, ind.clone());
        if let Err(e) = self
            .check_field_universes(&ind)
            .and_then(|()| self.check_ret_indices(&ind))
        {
            self.inds.remove(&id);
            return Err(e);
        }
        let at = crate::inductive::ArityTable {
            ind: ind.id,
            nparams: ind.params.len() as u32,
            nindices: ind.indices.len() as u32,
            ctors: ind
                .ctors
                .iter()
                .map(|c| crate::inductive::CtorArity {
                    ctor_ix: c.ctor_ix,
                    nfields: c.args.len() as u32,
                    // nrec = #ctor args whose head is `Ind ind.id` (recursive fields)
                    nrec: c.args.iter().filter(|a| head_is_ind(a, ind.id)).count() as u32,
                })
                .collect(),
        };
        self.recursors.insert(ind.id, at); // `ind` already registered above for R11
        Ok(())
    }

    /// R11: reject any ctor field whose sort level exceeds the declared `sort`. The field's
    /// sort is inferred in the telescope ctx (params, then preceding fields), mirroring Lean's
    /// `ensure_type(binding_domain)` walk. `Ind self.id` already resolves (registered by caller).
    fn check_field_universes(&self, ind: &Inductive) -> Result<(), AdmitError> {
        for c in &ind.ctors {
            let mut ctx = ind.params.clone();
            for field in &c.args {
                let level = crate::infer::sort_of(self, &ctx, field)
                    .map_err(|_| AdmitError::BadDecl("ill-typed field"))?;
                if !crate::universe::le(level, ind.sort) {
                    return Err(AdmitError::BadDecl("field universe too big"));
                }
                ctx.push(field.clone());
            }
        }
        Ok(())
    }

    /// Indexed-family well-formedness (proofs.md §4:131-159 — `ret_indices` = "index values ctor
    /// returns"; the indexed-family analogue of the R11 gate). For each ctor, REJECT unless
    /// (a) `ret_indices.len() == ind.indices.len()` (no arity skew vs the declared index telescope)
    /// AND (b) each `ret_index` type-checks at the corresponding `ind.indices[t]` type, in the
    /// ctor's field context `[params, fields_k]`. Without this, `infer(Ctor)` (infer.rs:90) builds
    /// the ctor type from raw `ret_indices` unchecked ⇒ a malformed `Ind P ret_indices` head ⇒
    /// `recursor_type` emits a motive-application with arity skew ⇒ an ill-typed recursor whose
    /// minors inhabit a bogus motive instance = UNSOUND.
    ///
    /// Equivalently: the ctor's *return type* `I params ret_indices` (proofs.md:177,180) must be a
    /// well-formed type in the field ctx `[params, fields_k]`. We reuse the trusted `infer`/`sort_of`
    /// to type exactly that application — the SAME machinery `infer(Ctor)` (infer.rs:85-92) and T-App
    /// use — so there is no hand-rolled de Bruijn arithmetic in the gate:
    ///   - too few `ret_indices` ⇒ the head reduces to `Π(remaining indices). Sort` (a `Pi`, not a
    ///     `Sort`) ⇒ `sort_of` rejects (`NotASort`);
    ///   - too many ⇒ an extra `App` hits the `Sort` head ⇒ `as_pi` rejects (`NotAPi`);
    ///   - an ill-typed index ⇒ the spine's `check(arg, dom)` rejects (`Mismatch`).
    ///
    /// The explicit arity test below is a fast, precise pre-check (and documents intent); the
    /// `sort_of` then does the per-index type-check against `ind.indices[t]`.
    fn check_ret_indices(&self, ind: &Inductive) -> Result<(), AdmitError> {
        let np = ind.indices.len();
        for c in &ind.ctors {
            // (a) arity: the ctor must return EXACTLY one value per declared index.
            if c.ret_indices.len() != np {
                return Err(AdmitError::BadDecl("ret_indices arity mismatch"));
            }
            // (b) build the return type `I params ret_indices` in ctx `[params, fields_k]` and
            // demand it lands in a sort. Param `a` (outermost-first) is `Var(m+nparams-1-a)` in this
            // ctx (= infer.rs:89); the ret_indices are already stated in `[params, fields_k]`.
            let nparams = ind.params.len();
            let m = c.args.len();
            let mut ctx = ind.params.clone();
            ctx.extend(c.args.iter().cloned());
            let pvars = (0..nparams).map(|a| Tm::Var((m + (nparams - 1 - a)) as u32));
            let head_args: Vec<Tm> = pvars.chain(c.ret_indices.iter().cloned()).collect();
            let ret_ty = head_args.iter().fold(Tm::Ind(ind.id), |f, a| {
                Tm::App(Box::new(f), Box::new(a.clone()))
            });
            crate::infer::sort_of(self, &ctx, &ret_ty)
                .map_err(|_| AdmitError::BadDecl("ill-typed ret_index"))?;
        }
        Ok(())
    }
}

/// True if the head (after walking Pi codomains and App spine) is `Ind id`.
fn head_is_ind(t: &Tm, id: crate::symbol::IndId) -> bool {
    match t {
        Tm::Ind(j) => *j == id,
        Tm::App(f, _) => head_is_ind(f, id),
        Tm::Pi(_, b) => head_is_ind(b, id),
        _ => false,
    }
}

fn refs_unknown_const(t: &Tm, known: &HashMap<ConstId, (Tm, Tm)>, this: ConstId) -> bool {
    match t {
        Tm::Const(c) => *c == this || !known.contains_key(c),
        Tm::Pi(a, b) | Tm::Lam(a, b) | Tm::App(a, b) => {
            refs_unknown_const(a, known, this) || refs_unknown_const(b, known, this)
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inductive::{CtorDecl, Inductive};
    use crate::symbol::{ConstId, IndId};
    use crate::tm::Tm;

    #[test]
    fn r7_self_reference_rejected() {
        let mut env = GlobalEnv::default();
        let r = env.add_const(ConstId(0), Tm::Sort(0), Tm::Const(ConstId(0)));
        assert!(r.is_err());
    }

    #[test]
    fn forward_ref_ok_after_admit() {
        let mut env = GlobalEnv::default();
        env.add_const(ConstId(0), Tm::Sort(0), Tm::Sort(0)).unwrap();
        // ConstId(1) body references already-admitted ConstId(0): OK
        assert!(env
            .add_const(ConstId(1), Tm::Sort(0), Tm::Const(ConstId(0)))
            .is_ok());
    }

    #[test]
    fn inductive_admit_nat_succeeds() {
        let mut env = GlobalEnv::default();
        // Nat with zero and succ constructors
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
        assert!(env.add_inductive(nat).is_ok());
        // Verify it was stored
        assert!(env.inds.contains_key(&IndId(0)));
        assert!(env.recursors.contains_key(&IndId(0)));
    }

    #[test]
    fn inductive_admit_non_positive_rejected() {
        let mut env = GlobalEnv::default();
        // Bad inductive with ctor arg (Bad → Bad) → ...
        let bad = Inductive {
            id: IndId(0),
            params: vec![],
            indices: vec![],
            sort: 0,
            ctors: vec![CtorDecl {
                ctor_ix: 0,
                args: vec![Tm::Pi(
                    Box::new(Tm::Pi(
                        Box::new(Tm::Ind(IndId(0))),
                        Box::new(Tm::Ind(IndId(0))),
                    )),
                    Box::new(Tm::Ind(IndId(0))),
                )],
                ret_indices: vec![],
            }],
        };
        let result = env.add_inductive(bad);
        assert_eq!(result, Err(AdmitError::BadDecl("non-positive")));
    }

    #[test]
    fn inductive_admit_duplicate_rejected() {
        let mut env = GlobalEnv::default();
        let nat = Inductive {
            id: IndId(0),
            params: vec![],
            indices: vec![],
            sort: 0,
            ctors: vec![CtorDecl {
                ctor_ix: 0,
                args: vec![],
                ret_indices: vec![],
            }],
        };
        env.add_inductive(nat.clone()).unwrap();
        let result = env.add_inductive(nat);
        assert_eq!(result, Err(AdmitError::Duplicate));
    }

    #[test]
    fn inductive_arity_table_fields() {
        let mut env = GlobalEnv::default();
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
        env.add_inductive(nat).unwrap();
        let at = &env.recursors[&IndId(0)];
        assert_eq!(at.nparams, 0);
        assert_eq!(at.nindices, 0);
        assert_eq!(at.ctors.len(), 2);
        assert_eq!(at.ctors[0].nfields, 0);
        assert_eq!(at.ctors[0].nrec, 0);
        assert_eq!(at.ctors[1].nfields, 1);
        assert_eq!(at.ctors[1].nrec, 1); // succ arg is recursive
    }
}
