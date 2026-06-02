use dnx_ast::{Ast, Name, PrimFun, PrimVal};
use dnx_core::LinError;
use std::collections::HashMap;

/// Pass 1 output: linearity flags + usage levels for Pass 2 delta computation.
#[derive(Debug, Clone, Default)]
pub struct Pass1Result {
    pub era_used: bool,
    pub rep_used: bool,
    pub usage_levels: HashMap<Name, u32>,
}

/// Pass 1: linear check + usage level collection on a resolved Ast (no Fix, no def refs).
/// `era_used/rep_used` drive NetClass selection; `usage_levels` drive Pass 2 delta_i.
pub fn pass1<V: PrimVal, F: PrimFun>(expr: &Ast<V, F>) -> Result<Pass1Result, LinError> {
    let mut result = Pass1Result::default();
    let mut counts: ScopeStack = ScopeStack::new();
    collect(0, &mut counts, &mut result, expr)?;
    Ok(result)
}

// ScopeStack: stack of per-binder count maps (one frame per abs/rep binder).
struct ScopeStack {
    frames: Vec<HashMap<Name, u32>>,
    // flat map for the currently-active binders (merged view for increment)
    active: HashMap<Name, u32>,
}

impl ScopeStack {
    fn new() -> Self {
        ScopeStack {
            frames: vec![],
            active: HashMap::new(),
        }
    }

    fn push(&mut self, name: Name) {
        self.frames.push(HashMap::from([(name.clone(), 0)]));
        self.active.insert(name, 0);
    }

    fn pop(&mut self, name: &Name) -> u32 {
        let frame = self.frames.pop().expect("unbalanced pop");
        let count = *frame.get(name).unwrap_or(&0);
        self.active.remove(name);
        count
    }

    fn increment(&mut self, name: &Name) {
        if let Some(c) = self.active.get_mut(name) {
            *c += 1;
        }
        // Also update the top frame that owns this binder.
        for frame in self.frames.iter_mut().rev() {
            if let Some(c) = frame.get_mut(name) {
                *c += 1;
                break;
            }
        }
    }
}

fn collect<V: PrimVal, F: PrimFun>(
    level: u32,
    counts: &mut ScopeStack,
    result: &mut Pass1Result,
    expr: &Ast<V, F>,
) -> Result<(), LinError> {
    match expr {
        Ast::Name(n) => {
            counts.increment(n);
            result.usage_levels.insert(n.clone(), level);
        }
        Ast::Abs(x, body) => {
            counts.push(x.clone());
            collect(level, counts, result, body)?;
            let n = counts.pop(x);
            if n == 0 {
                return Err(LinError::Unused(x.clone()));
            }
            if n > 1 {
                return Err(LinError::MultiUse(x.clone(), n));
            }
        }
        Ast::App(f, x) => {
            collect(level, counts, result, f)?;
            collect(level + 1, counts, result, x)?;
        }
        Ast::Rep(e, a, b, body) => {
            result.rep_used = true;
            collect(level, counts, result, e)?;
            counts.push(a.clone());
            counts.push(b.clone());
            collect(level, counts, result, body)?;
            let nb = counts.pop(b);
            let na = counts.pop(a);
            if na == 0 {
                return Err(LinError::Unused(a.clone()));
            }
            if na > 1 {
                return Err(LinError::MultiUse(a.clone(), na));
            }
            if nb == 0 {
                return Err(LinError::Unused(b.clone()));
            }
            if nb > 1 {
                return Err(LinError::MultiUse(b.clone(), nb));
            }
        }
        Ast::Era(e, body) => {
            result.era_used = true;
            collect(level, counts, result, e)?;
            collect(level, counts, result, body)?;
        }
        Ast::Fix(inner) => {
            // Cyclic-net fix: the fixpoint value is its function applied to itself, so
            // its inner abstraction is linearity-checked + usage-leveled like any subterm
            // (self is bound by that abstraction and used exactly once after linearization).
            collect(level, counts, result, inner)?;
        }
        Ast::Perform(_, e) => {
            // No scope effect; free monad encoding — elaborated to Abs/App in Pass 2.
            collect(level, counts, result, e)?;
        }
        Ast::Handle(comp, branches) => {
            collect(level, counts, result, comp)?;
            for b in branches {
                counts.push(b.arg_name.clone());
                counts.push(b.k_name.clone());
                collect(level, counts, result, &b.body)?;
                let nk = counts.pop(&b.k_name);
                let na = counts.pop(&b.arg_name);
                if na == 0 {
                    return Err(LinError::Unused(b.arg_name.clone()));
                }
                if na > 1 {
                    return Err(LinError::MultiUse(b.arg_name.clone(), na));
                }
                if nk == 0 {
                    return Err(LinError::Unused(b.k_name.clone()));
                }
                if nk > 1 {
                    return Err(LinError::MultiUse(b.k_name.clone(), nk));
                }
            }
        }
        Ast::Val(_) | Ast::Fun(_) => {}
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use dnx_ast::Ast;
    use std::sync::Arc;

    #[derive(Debug, Clone, PartialEq)]
    struct NoVal;
    #[derive(Debug, Clone, PartialEq)]
    struct NoFun;
    impl PrimVal for NoVal {}
    impl PrimFun for NoFun {}

    type E = Ast<NoVal, NoFun>;

    fn nm(s: &str) -> E {
        Ast::Name(Arc::from(s))
    }
    fn ab(x: &str, b: E) -> E {
        Ast::Abs(Arc::from(x), Box::new(b))
    }
    fn ap(f: E, x: E) -> E {
        Ast::App(Box::new(f), Box::new(x))
    }
    fn rep(e: E, a: &str, b: &str, body: E) -> E {
        Ast::Rep(Box::new(e), Arc::from(a), Arc::from(b), Box::new(body))
    }
    fn era(e: E, body: E) -> E {
        Ast::Era(Box::new(e), Box::new(body))
    }

    #[test]
    fn pass1_identity_linear() -> Result<(), LinError> {
        // abs x . x  →  era_used=false, rep_used=false (ΔL)
        let r = pass1(&ab("x", nm("x")))?;
        assert!(!r.era_used && !r.rep_used);
        Ok(())
    }

    #[test]
    fn pass1_unused_error() {
        // abs x . (abs y . y) → y used, x UNUSED
        let e: E = ab("x", ab("y", nm("y")));
        assert!(matches!(pass1(&e), Err(LinError::Unused(n)) if n.as_ref() == "x"));
    }

    #[test]
    fn pass1_multiuse_error() {
        // abs x . x x → x used twice
        let e: E = ab("x", ap(nm("x"), nm("x")));
        assert!(matches!(pass1(&e), Err(LinError::MultiUse(n, 2)) if n.as_ref() == "x"));
    }

    #[test]
    fn pass1_rep_sets_rep_flag() -> Result<(), LinError> {
        // rep x as (a, b) in a  (b unused → would error; use b too)
        let e: E = ab("x", rep(nm("x"), "a", "b", ap(nm("a"), nm("b"))));
        let r = pass1(&e)?;
        assert!(r.rep_used);
        assert!(!r.era_used);
        Ok(())
    }

    #[test]
    fn pass1_era_sets_era_flag() -> Result<(), LinError> {
        // era x in y  (abs y . era y in (abs z . z))
        let e: E = ab("y", era(nm("y"), ab("z", nm("z"))));
        let r = pass1(&e)?;
        assert!(r.era_used);
        assert!(!r.rep_used);
        Ok(())
    }

    #[test]
    fn pass1_usage_level_app_arg_plus_one() -> Result<(), LinError> {
        // abs x . x   (x at level 0)
        // abs f . abs x . f x   (f at level 0, x at level 1)
        let e: E = ab("f", ab("x", ap(nm("f"), nm("x"))));
        let r = pass1(&e)?;
        assert_eq!(r.usage_levels[&Arc::from("f") as &Name], 0);
        assert_eq!(r.usage_levels[&Arc::from("x") as &Name], 1);
        Ok(())
    }
}
