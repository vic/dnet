use dnx_ast::{Ast, HandlerBranch, Name, PrimFun, PrimVal};
use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Arc;

/// Global α-rename counter. Monotone across the process so freshly-minted binder
/// names never collide with one another, nor with any source name (the `α` mint
/// marker `~` cannot occur in a parsed Nix identifier).
static ALPHA_CTR: AtomicU32 = AtomicU32::new(0);

fn fresh(base: &Name) -> Name {
    let n = ALPHA_CTR.fetch_add(1, Ordering::Relaxed);
    Arc::from(format!("{base}~{n}").as_str())
}

/// α-rename every binder to a globally-unique name (enforce Barendregt) on a
/// resolved `Ast`. Pass 1's flat usage/linearity maps and Pass 2's flat `env`
/// are keyed by binder name, so a SHADOWED name would make an inner binder's
/// `env.remove` consume the OUTER binding (capture). Making every binder unique
/// makes those flat maps correct by construction — α-equivalence is the law
/// (main.tex: bound names are immaterial). Free names (unbound `Ast::Name`,
/// e.g. a leftover global) pass through unchanged.
pub fn alpha_rename<V: PrimVal + Clone, F: PrimFun + Clone>(expr: &Ast<V, F>) -> Ast<V, F> {
    rename(expr, &HashMap::new())
}

fn rename<V: PrimVal + Clone, F: PrimFun + Clone>(
    expr: &Ast<V, F>,
    env: &HashMap<Name, Name>,
) -> Ast<V, F> {
    match expr {
        Ast::Name(n) => Ast::Name(env.get(n).cloned().unwrap_or_else(|| n.clone())),
        Ast::Abs(x, body) => {
            let x2 = fresh(x);
            let env2 = bind(env, x, &x2);
            Ast::Abs(x2, Box::new(rename(body, &env2)))
        }
        Ast::App(f, a) => Ast::App(Box::new(rename(f, env)), Box::new(rename(a, env))),
        Ast::Rep(e, a, b, body) => {
            // `e` is scrutinee — renamed under the OUTER env (a,b not in scope there).
            let e2 = rename(e, env);
            let a2 = fresh(a);
            let b2 = fresh(b);
            let env2 = bind(&bind(env, a, &a2), b, &b2);
            Ast::Rep(Box::new(e2), a2, b2, Box::new(rename(body, &env2)))
        }
        Ast::Era(e, body) => {
            Ast::Era(Box::new(rename(e, env)), Box::new(rename(body, env)))
        }
        Ast::Fix(inner) => Ast::Fix(Box::new(rename(inner, env))),
        Ast::Perform(label, e) => Ast::Perform(label.clone(), Box::new(rename(e, env))),
        Ast::Handle(comp, branches) => {
            let comp2 = rename(comp, env);
            let branches2 = branches
                .iter()
                .map(|b| {
                    let arg2 = fresh(&b.arg_name);
                    let k2 = fresh(&b.k_name);
                    let env2 = bind(&bind(env, &b.arg_name, &arg2), &b.k_name, &k2);
                    HandlerBranch {
                        label: b.label.clone(),
                        arg_name: arg2,
                        k_name: k2,
                        body: Box::new(rename(&b.body, &env2)),
                    }
                })
                .collect();
            Ast::Handle(Box::new(comp2), branches2)
        }
        Ast::Val(v) => Ast::Val(v.clone()),
        Ast::Fun(f) => Ast::Fun(f.clone()),
    }
}

fn bind(env: &HashMap<Name, Name>, from: &Name, to: &Name) -> HashMap<Name, Name> {
    let mut e = env.clone();
    e.insert(from.clone(), to.clone());
    e
}

#[cfg(test)]
mod tests {
    use super::*;
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

    /// A free (unbound) name is not renamed.
    #[test]
    fn free_name_unchanged() {
        assert_eq!(alpha_rename(&nm("g")), nm("g"));
    }

    /// Two distinct binders named `h` are renamed to two distinct fresh names,
    /// and each body-occurrence binds to its own binder (no capture).
    #[test]
    fn shadowed_binders_become_distinct() {
        // (h: (h: h) h)  — inner `h` shadows outer; both occurrences must bind locally.
        let e: E = ab("h", ap(ab("h", nm("h")), nm("h")));
        let out = alpha_rename(&e);
        let (outer, body) = match &out {
            Ast::Abs(x, b) => (x.clone(), b.as_ref()),
            _ => panic!("expected Abs"),
        };
        let (inner, inner_body, arg) = match body {
            Ast::App(f, a) => match f.as_ref() {
                Ast::Abs(y, ib) => (y.clone(), ib.as_ref(), a.as_ref()),
                _ => panic!("expected inner Abs"),
            },
            _ => panic!("expected App"),
        };
        assert_ne!(outer, inner, "shadowed binders distinct");
        // inner body `h` → inner binder; outer arg `h` → outer binder.
        assert_eq!(inner_body, &Ast::Name(inner));
        assert_eq!(arg, &Ast::Name(outer));
    }

    /// Idempotent shape: a linear identity stays an identity (one binder, body =
    /// that binder).
    #[test]
    fn identity_stays_identity() {
        let out = alpha_rename(&ab("x", nm("x")));
        match out {
            Ast::Abs(x, b) => assert_eq!(*b, Ast::Name(x)),
            _ => panic!("expected Abs"),
        }
    }

    /// Rep binders are renamed and their body uses follow.
    #[test]
    fn rep_binders_renamed() {
        let e: E = Ast::Rep(
            Box::new(nm("g")),
            Arc::from("a"),
            Arc::from("b"),
            Box::new(ap(nm("a"), nm("b"))),
        );
        match alpha_rename(&e) {
            Ast::Rep(e2, a, b, body) => {
                assert_eq!(*e2, nm("g"), "free scrutinee unchanged");
                assert_ne!(a, b);
                assert_eq!(*body, ap(Ast::Name(a), Ast::Name(b)));
            }
            _ => panic!("expected Rep"),
        }
    }
}
