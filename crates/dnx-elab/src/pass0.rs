use dnx_ast::{Ast, Name, PrimFun, PrimVal};
use dnx_core::LinError;
use std::collections::{HashMap, HashSet};

type DefMap<V, F> = HashMap<Name, Ast<V, F>>;

/// Pass 0: def resolution, Fix desugar, topo-sort mutual-recursion check.
/// Returns a resolved expression with no Name-refs to defs and no Fix nodes.
pub fn pass0<V: PrimVal + Clone, F: PrimFun + Clone>(
    defs: &DefMap<V, F>,
    expr: &Ast<V, F>,
) -> Result<Ast<V, F>, LinError> {
    // Build dependency graph for defs (used names that are def-names).
    topo_check(defs)?;
    resolve(defs, expr, &mut HashSet::new())
}

/// Topological check: cycle without Fix → MutualRecursion error.
fn topo_check<V: PrimVal, F: PrimFun>(defs: &DefMap<V, F>) -> Result<(), LinError> {
    let mut visiting: HashSet<Name> = HashSet::new();
    let mut visited: HashSet<Name> = HashSet::new();
    for name in defs.keys() {
        if !visited.contains(name) {
            dfs_check(defs, name, &mut visiting, &mut visited)?;
        }
    }
    Ok(())
}

fn dfs_check<V: PrimVal, F: PrimFun>(
    defs: &DefMap<V, F>,
    name: &Name,
    visiting: &mut HashSet<Name>,
    visited: &mut HashSet<Name>,
) -> Result<(), LinError> {
    if visiting.contains(name) {
        // Cycle detected — check if it's via Fix (safe) or bare (error).
        // At this point we signal the error; Fix is desugared before cycles form.
        let cycle: Vec<Name> = visiting.iter().cloned().collect();
        return Err(LinError::MutualRecursion(cycle));
    }
    if visited.contains(name) {
        return Ok(());
    }
    visiting.insert(name.clone());
    if let Some(body) = defs.get(name) {
        let refs = free_def_refs(defs, body);
        for dep in refs {
            dfs_check(defs, &dep, visiting, visited)?;
        }
    }
    visiting.remove(name);
    visited.insert(name.clone());
    Ok(())
}

fn free_def_refs<V: PrimVal, F: PrimFun>(defs: &DefMap<V, F>, expr: &Ast<V, F>) -> Vec<Name> {
    let mut refs = vec![];
    collect_def_refs(defs, expr, &mut refs);
    refs
}

fn collect_def_refs<V: PrimVal, F: PrimFun>(
    defs: &DefMap<V, F>,
    expr: &Ast<V, F>,
    out: &mut Vec<Name>,
) {
    match expr {
        Ast::Name(n) if defs.contains_key(n) => out.push(n.clone()),
        Ast::Name(_) => {}
        Ast::Abs(_, body) => collect_def_refs(defs, body, out),
        Ast::App(f, x) => {
            collect_def_refs(defs, f, out);
            collect_def_refs(defs, x, out);
        }
        Ast::Rep(e, _, _, body) => {
            collect_def_refs(defs, e, out);
            collect_def_refs(defs, body, out);
        }
        Ast::Era(e, body) => {
            collect_def_refs(defs, e, out);
            collect_def_refs(defs, body, out);
        }
        Ast::Fix(e) => collect_def_refs(defs, e, out),
        Ast::Perform(_, e) => collect_def_refs(defs, e, out),
        Ast::Handle(comp, branches) => {
            collect_def_refs(defs, comp, out);
            for b in branches {
                collect_def_refs(defs, &b.body, out);
            }
        }
        Ast::Val(_) | Ast::Fun(_) => {}
    }
}

/// Resolve: inline def refs, desugar Fix, leave bound names alone.
fn resolve<V: PrimVal + Clone, F: PrimFun + Clone>(
    defs: &DefMap<V, F>,
    expr: &Ast<V, F>,
    bound: &mut HashSet<Name>,
) -> Result<Ast<V, F>, LinError> {
    match expr {
        Ast::Name(n) => {
            if bound.contains(n) {
                Ok(Ast::Name(n.clone()))
            } else if let Some(def_body) = defs.get(n) {
                // Def ref → fresh AST copy (resolve the def's body too).
                resolve(defs, def_body, bound)
            } else {
                Ok(Ast::Name(n.clone()))
            }
        }
        Ast::Abs(x, body) => {
            bound.insert(x.clone());
            let body2 = resolve(defs, body, bound)?;
            bound.remove(x);
            Ok(Ast::Abs(x.clone(), Box::new(body2)))
        }
        Ast::App(f, x) => {
            let f2 = resolve(defs, f, bound)?;
            let x2 = resolve(defs, x, bound)?;
            Ok(Ast::App(Box::new(f2), Box::new(x2)))
        }
        Ast::Rep(e, a, b, body) => {
            let e2 = resolve(defs, e, bound)?;
            bound.insert(a.clone());
            bound.insert(b.clone());
            let body2 = resolve(defs, body, bound)?;
            bound.remove(a);
            bound.remove(b);
            Ok(Ast::Rep(
                Box::new(e2),
                a.clone(),
                b.clone(),
                Box::new(body2),
            ))
        }
        Ast::Era(e, body) => {
            let e2 = resolve(defs, e, bound)?;
            let body2 = resolve(defs, body, bound)?;
            Ok(Ast::Era(Box::new(e2), Box::new(body2)))
        }
        Ast::Fix(e) => {
            // Keep Fix as a native node; pass2 elaborates it to a cyclic Δ-net (the
            // paper-faithful fixpoint). The Y-combinator desugar is gone — its nested
            // self-application compounded replicator levels (unbounded climb / value
            // mis-delivery). See vic/research/recursion-rootcause-2026-06-04.md.
            let e2 = resolve(defs, e, bound)?;
            Ok(Ast::Fix(Box::new(e2)))
        }
        Ast::Perform(label, e) => {
            let e2 = resolve(defs, e, bound)?;
            Ok(Ast::Perform(label.clone(), Box::new(e2)))
        }
        Ast::Handle(comp, branches) => {
            let comp2 = resolve(defs, comp, bound)?;
            let branches2 = branches
                .iter()
                .map(|b| {
                    bound.insert(b.arg_name.clone());
                    bound.insert(b.k_name.clone());
                    let body2 = resolve(defs, &b.body, bound)?;
                    bound.remove(&b.arg_name);
                    bound.remove(&b.k_name);
                    Ok(dnx_ast::HandlerBranch {
                        label: b.label.clone(),
                        arg_name: b.arg_name.clone(),
                        k_name: b.k_name.clone(),
                        body: Box::new(body2),
                    })
                })
                .collect::<Result<Vec<_>, LinError>>()?;
            Ok(Ast::Handle(Box::new(comp2), branches2))
        }
        Ast::Val(v) => Ok(Ast::Val(v.clone())),
        Ast::Fun(f) => Ok(Ast::Fun(f.clone())),
    }
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

    fn name(s: &str) -> E {
        Ast::Name(Arc::from(s))
    }
    fn abs(x: &str, b: E) -> E {
        Ast::Abs(Arc::from(x), Box::new(b))
    }
    fn app(f: E, x: E) -> E {
        Ast::App(Box::new(f), Box::new(x))
    }
    fn fix_e(e: E) -> E {
        Ast::Fix(Box::new(e))
    }

    #[test]
    fn pass0_resolves_def_ref() -> Result<(), LinError> {
        let id: E = abs("x", name("x"));
        let mut defs = HashMap::new();
        defs.insert(Arc::from("id"), id.clone());
        let expr = app(name("id"), name("y"));
        let resolved = pass0(&defs, &expr)?;
        // id(y) → (abs x . x) y
        assert_eq!(resolved, app(abs("x", name("x")), name("y")));
        Ok(())
    }

    #[test]
    fn pass0_mutual_recursion_error() {
        // a = b, b = a (cycle, no fix)
        let mut defs: HashMap<Name, E> = HashMap::new();
        defs.insert(Arc::from("a"), name("b"));
        defs.insert(Arc::from("b"), name("a"));
        assert!(pass0(&defs, &name("a")).is_err());
    }

    #[test]
    fn pass0_keeps_fix_as_native_node() -> Result<(), LinError> {
        let defs: HashMap<Name, E> = HashMap::new();
        let expr = fix_e(name("f"));
        let resolved = pass0(&defs, &expr)?;
        // Fix is a native node now (cyclic-net elaboration in pass2), NOT desugared to a
        // Y-combinator App. Pass 0 only resolves the inner term.
        assert!(matches!(resolved, Ast::Fix(_)));
        Ok(())
    }
}
