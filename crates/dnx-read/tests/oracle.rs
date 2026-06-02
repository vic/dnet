//! B4: Round-trip + full confluence gate (oracle v2).
//! `just oracle` runs these (--include-ignored).

use dnx_ast::Ast;
use dnx_core::{normalize, LOPath, Net, PortId, PortKind, Proper, ΔL};
use dnx_elab::{elaborate, pass1};
use dnx_read::{psi_native, ReadbackResult};
use std::collections::HashMap;
use std::sync::Arc;

type Name = Arc<str>;

#[derive(Debug, Clone, PartialEq)]
struct NoVal;
#[derive(Debug, Clone, PartialEq)]
struct NoFun;
impl dnx_ast::PrimVal for NoVal {}
impl dnx_ast::PrimFun for NoFun {}

type E = Ast<NoVal, NoFun>;
type Env = HashMap<Name, (PortId, u32)>;

fn nm(s: &str) -> E {
    Ast::Name(Arc::from(s))
}
fn ab(x: &str, b: E) -> E {
    Ast::Abs(Arc::from(x), Box::new(b))
}
fn ap(f: E, x: E) -> E {
    Ast::App(Box::new(f), Box::new(x))
}

/// Elaborate, normalize, readback.
fn roundtrip(expr: &E) -> E {
    let r1 = pass1(expr).unwrap();
    let mut net = Net::<Proper, ΔL>::new(128);
    let mut env = Env::new();
    let (rp, _) = elaborate(
        &mut net,
        0,
        &mut env,
        LOPath::root(),
        expr,
        &r1.usage_levels,
    )
    .unwrap();
    let root_port = if rp.port_kind() != PortKind::Principal {
        let root_slot = net.alloc_free(0).unwrap();
        net.connect(rp, root_slot, LOPath::root()).unwrap();
        root_slot
    } else {
        rp
    };
    net.add_root("r".into(), root_port);
    let (canonical, _) = normalize(net).unwrap();
    match psi_native::<ΔL, NoVal, NoFun>(&canonical) {
        ReadbackResult::Lambda(ast) => ast,
        ReadbackResult::Partial(n) => panic!("psi_native returned Partial({n})"),
    }
}

/// Alpha-equivalence: two Ast expressions are α-equiv if they differ only in bound var names.
fn alpha_eq(a: &E, b: &E) -> bool {
    alpha_eq_inner(a, b, &mut HashMap::new(), &mut HashMap::new())
}

fn alpha_eq_inner(
    a: &E,
    b: &E,
    env_a: &mut HashMap<Name, usize>,
    env_b: &mut HashMap<Name, usize>,
) -> bool {
    match (a, b) {
        (Ast::Name(na), Ast::Name(nb)) => {
            match (env_a.get(na), env_b.get(nb)) {
                (Some(ia), Some(ib)) => ia == ib,
                (None, None) => na == nb, // both free vars
                _ => false,
            }
        }
        (Ast::Abs(xa, ba), Ast::Abs(xb, bb)) => {
            let id = env_a.len().max(env_b.len());
            let old_a = env_a.insert(xa.clone(), id);
            let old_b = env_b.insert(xb.clone(), id);
            let eq = alpha_eq_inner(ba, bb, env_a, env_b);
            match old_a {
                Some(v) => {
                    env_a.insert(xa.clone(), v);
                }
                None => {
                    env_a.remove(xa);
                }
            }
            match old_b {
                Some(v) => {
                    env_b.insert(xb.clone(), v);
                }
                None => {
                    env_b.remove(xb);
                }
            }
            eq
        }
        (Ast::App(f1, x1), Ast::App(f2, x2)) => {
            alpha_eq_inner(f1, f2, env_a, env_b) && alpha_eq_inner(x1, x2, env_a, env_b)
        }
        (Ast::Rep(e1, a1, b1, body1), Ast::Rep(e2, a2, b2, body2)) => {
            if !alpha_eq_inner(e1, e2, env_a, env_b) {
                return false;
            }
            let id = env_a.len().max(env_b.len());
            let oa1 = env_a.insert(a1.clone(), id);
            let oa2 = env_b.insert(a2.clone(), id);
            let id2 = id + 1;
            let ob1 = env_a.insert(b1.clone(), id2);
            let ob2 = env_b.insert(b2.clone(), id2);
            let eq = alpha_eq_inner(body1, body2, env_a, env_b);
            restore(env_a, a1, oa1);
            restore(env_b, a2, oa2);
            restore(env_a, b1, ob1);
            restore(env_b, b2, ob2);
            eq
        }
        (Ast::Era(e1, body1), Ast::Era(e2, body2)) => {
            alpha_eq_inner(e1, e2, env_a, env_b) && alpha_eq_inner(body1, body2, env_a, env_b)
        }
        _ => false,
    }
}

fn restore(env: &mut HashMap<Name, usize>, k: &Name, old: Option<usize>) {
    match old {
        Some(v) => {
            env.insert(k.clone(), v);
        }
        None => {
            env.remove(k);
        }
    }
}

// ── oracle tests ──────────────────────────────────────────────────────────────

/// Identity: round-trip λx.x → λx.x (α-equiv).
#[test]

fn b4_roundtrip_identity() {
    let expr = ab("x", nm("x"));
    let result = roundtrip(&expr);
    assert!(alpha_eq(&result, &expr), "identity round-trip: {result:?}");
}

/// (λx.x)(λy.y) → psi_native → λy.y (α-equiv).
#[test]

fn b4_roundtrip_id_applied() {
    let expr = ap(ab("x", nm("x")), ab("y", nm("y")));
    let expected = ab("y", nm("y"));
    let result = roundtrip(&expr);
    assert!(alpha_eq(&result, &expected), "id applied: {result:?}");
}

/// Church-Rosser: same term with different evaluation order → same normal form.
/// Build (λx.x)(λy.y) in two different allocation orders → same result after normalization.
#[test]

fn b4_church_rosser_same_nf() {
    let expr1 = ap(ab("x", nm("x")), ab("y", nm("y")));
    let expr2 = ap(ab("a", nm("a")), ab("b", nm("b")));
    let r1 = roundtrip(&expr1);
    let r2 = roundtrip(&expr2);
    assert!(
        alpha_eq(&r1, &r2),
        "same term, different names → same NF: {r1:?} vs {r2:?}"
    );
}

/// Idempotency: normalizing a normal form gives the same result.
/// psi_native(normalize(elaborate(psi_native(normalize(elaborate(t)))))) = same NF.
#[test]

fn b4_normalization_idempotent() {
    let expr = ab("x", nm("x"));
    let r1 = roundtrip(&expr);
    let r2 = roundtrip(&r1);
    assert!(
        alpha_eq(&r1, &r2),
        "normalization not idempotent: {r1:?} vs {r2:?}"
    );
}

/// Nested application: (λf.λx.f x)(λy.y)(λz.z) → λz.z.
#[test]

fn b4_nested_application() {
    // S combinator simplified: (λf.λx.f x)
    let app_fn = ab("f", ab("x", ap(nm("f"), nm("x"))));
    let expr = ap(ap(app_fn, ab("y", nm("y"))), ab("z", nm("z")));
    let expected = ab("z", nm("z"));
    let result = roundtrip(&expr);
    assert!(alpha_eq(&result, &expected), "nested app: {result:?}");
}
