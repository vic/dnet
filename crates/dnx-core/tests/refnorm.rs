//! A1 differential oracle (trusted.md T1 / proofs.md L1091 — φ_S-idempotency is
//! ASSERTED not proved). Generates closed pure-λ terms and checks the Δ-net
//! normalizer agrees with an INDEPENDENT, textbook normal-order β-normalizer:
//!
//!   α_eq( psi_native(normalize(elaborate(t))) , ref_nf(t) )
//!
//! The two paths share no code: `ref_nf` is a de-Bruijn capture-avoiding
//! leftmost-outermost reducer living entirely in this file; the dnx path is the
//! public bridge `pass1 → elaborate → normalize → psi_native`. Test-only.

use dnx_ast::{Ast, NoFun, NoVal};
use dnx_core::{normalize, DnxError, LOPath, Net, PortId, PortKind, Proper, ΔL};
use std::collections::HashMap;
use std::sync::Arc;

type E = Ast<NoVal, NoFun>;
type Env = HashMap<Arc<str>, (PortId, u32)>;

// ── reference normalizer (independent oracle) ──────────────────────────────────
//
// Pure λ-calculus over de-Bruijn indices. Substitution is capture-avoiding by
// construction (shift on binder crossing); reduction is normal-order (leftmost-
// outermost) so it reaches the β-normal form whenever one exists. Fuel-bounded:
// a term with no NF (e.g. Ω) returns `RefErr::Diverged` instead of looping.

#[derive(Debug, Clone, PartialEq)]
enum Db {
    Var(u32),
    Abs(Box<Db>),
    App(Box<Db>, Box<Db>),
}

#[derive(Debug, PartialEq)]
enum RefErr {
    Diverged,
    NotClosed,
    Unsupported,
}

/// Named `Ast` → de-Bruijn. Errors on free vars (oracle is for closed terms) or
/// any non-pure-λ node (Rep/Era/Fix/Val/Fun/Perform/Handle).
fn to_db(e: &E, scope: &mut Vec<Arc<str>>) -> Result<Db, RefErr> {
    match e {
        Ast::Name(n) => scope
            .iter()
            .rev()
            .position(|b| b == n)
            .map(|i| Db::Var(i as u32))
            .ok_or(RefErr::NotClosed),
        Ast::Abs(x, body) => {
            scope.push(x.clone());
            let b = to_db(body, scope);
            scope.pop();
            Ok(Db::Abs(Box::new(b?)))
        }
        Ast::App(f, x) => Ok(Db::App(
            Box::new(to_db(f, scope)?),
            Box::new(to_db(x, scope)?),
        )),
        _ => Err(RefErr::Unsupported),
    }
}

/// Shift free indices ≥ `cutoff` by `d`.
fn shift(t: &Db, d: i64, cutoff: u32) -> Db {
    match t {
        Db::Var(i) => {
            if *i >= cutoff {
                Db::Var((*i as i64 + d) as u32)
            } else {
                Db::Var(*i)
            }
        }
        Db::Abs(b) => Db::Abs(Box::new(shift(b, d, cutoff + 1))),
        Db::App(f, x) => Db::App(Box::new(shift(f, d, cutoff)), Box::new(shift(x, d, cutoff))),
    }
}

/// `t[j := s]` — capture-avoiding (s is shifted under binders).
fn subst(t: &Db, j: u32, s: &Db) -> Db {
    match t {
        Db::Var(i) => {
            if *i == j {
                s.clone()
            } else {
                Db::Var(*i)
            }
        }
        Db::Abs(b) => Db::Abs(Box::new(subst(b, j + 1, &shift(s, 1, 0)))),
        Db::App(f, x) => Db::App(Box::new(subst(f, j, s)), Box::new(subst(x, j, s))),
    }
}

/// One leftmost-outermost β-step, if any redex exists. `None` ⇒ normal form.
fn step(t: &Db) -> Option<Db> {
    match t {
        Db::App(f, x) => {
            if let Db::Abs(body) = f.as_ref() {
                // β: (λ.body) x → body[0:=x], then renumber the freed binder.
                let sub = subst(body, 0, &shift(x, 1, 0));
                Some(shift(&sub, -1, 0))
            } else if let Some(f2) = step(f) {
                Some(Db::App(Box::new(f2), x.clone()))
            } else {
                step(x).map(|x2| Db::App(f.clone(), Box::new(x2)))
            }
        }
        Db::Abs(b) => step(b).map(|b2| Db::Abs(Box::new(b2))),
        Db::Var(_) => None,
    }
}

const FUEL: u32 = 100_000;

fn db_nf(mut t: Db) -> Result<Db, RefErr> {
    for _ in 0..FUEL {
        match step(&t) {
            Some(next) => t = next,
            None => return Ok(t),
        }
    }
    Err(RefErr::Diverged)
}

/// de-Bruijn → named `Ast`, binders named canonically `v0, v1, …` by depth.
fn from_db(t: &Db, depth: u32) -> E {
    match t {
        Db::Var(i) => Ast::Name(name(depth.saturating_sub(1).wrapping_sub(*i))),
        Db::Abs(b) => Ast::Abs(name(depth), Box::new(from_db(b, depth + 1))),
        Db::App(f, x) => Ast::App(Box::new(from_db(f, depth)), Box::new(from_db(x, depth))),
    }
}

fn name(i: u32) -> Arc<str> {
    Arc::from(format!("v{i}").as_str())
}

/// Reference β-normal form of a closed pure-λ `Ast`, as a canonical named `Ast`.
fn ref_nf(e: &E) -> Result<E, RefErr> {
    let db = to_db(e, &mut Vec::new())?;
    Ok(from_db(&db_nf(db)?, 0))
}

// ── dnx net path (public bridge) ───────────────────────────────────────────────

/// `pass1 → elaborate → normalize → psi_native`. Errors propagate (no unwrap).
fn dnx_nf(expr: &E) -> Result<E, DnxError> {
    let r1 = dnx_elab::pass1(expr)?;
    let mut net = Net::<Proper, ΔL>::new(256);
    let mut env = Env::new();
    let (rp, _) = dnx_elab::elaborate(
        &mut net,
        0,
        &mut env,
        LOPath::root(),
        expr,
        &r1.usage_levels,
    )?;
    let root = if rp.port_kind() == PortKind::Principal {
        rp
    } else {
        let slot = net.alloc_free(0)?;
        net.connect(rp, slot, LOPath::root())?;
        slot
    };
    net.add_root("r".into(), root);
    let (canonical, _) = normalize(net)?;
    match dnx_read::psi_native::<ΔL, NoVal, NoFun>(&canonical) {
        dnx_read::ReadbackResult::Lambda(ast) => Ok(ast),
        dnx_read::ReadbackResult::Partial(_) => Err(DnxError::ReadbackIncomplete),
    }
}

// ── α-equivalence on readback ASTs ─────────────────────────────────────────────

fn alpha_eq(a: &E, b: &E) -> bool {
    alpha(a, b, &mut Vec::new(), &mut Vec::new())
}

fn alpha(a: &E, b: &E, sa: &mut Vec<Arc<str>>, sb: &mut Vec<Arc<str>>) -> bool {
    match (a, b) {
        (Ast::Name(x), Ast::Name(y)) => {
            match (
                sa.iter().rposition(|n| n == x),
                sb.iter().rposition(|n| n == y),
            ) {
                (Some(i), Some(j)) => i == j,
                (None, None) => x == y,
                _ => false,
            }
        }
        (Ast::Abs(x, bx), Ast::Abs(y, by)) => {
            sa.push(x.clone());
            sb.push(y.clone());
            let r = alpha(bx, by, sa, sb);
            sa.pop();
            sb.pop();
            r
        }
        (Ast::App(f1, x1), Ast::App(f2, x2)) => alpha(f1, f2, sa, sb) && alpha(x1, x2, sa, sb),
        // psi_native wraps unused binders in `Era(Name, body)`; the reference NF
        // has no such marker, so compare the Era body against the other side.
        (Ast::Era(_, body), other) | (other, Ast::Era(_, body)) => alpha(body, other, sa, sb),
        _ => false,
    }
}

// ── smoke: bridge + ref agree on hand-written closed terms ─────────────────────

fn nm(s: &str) -> E {
    Ast::Name(Arc::from(s))
}
fn ab(x: &str, b: E) -> E {
    Ast::Abs(Arc::from(x), Box::new(b))
}
fn ap(f: E, x: E) -> E {
    Ast::App(Box::new(f), Box::new(x))
}

/// Compare the two normalizers on one closed term. Returns Ok(true) when both
/// agree, Ok(false) when the reference has no NF (skip — nothing to compare),
/// Err on a genuine disagreement or a net failure where the reference succeeded.
fn agree(term: &E) -> Result<bool, String> {
    let reference = match ref_nf(term) {
        Ok(nf) => nf,
        Err(RefErr::Diverged) => return Ok(false),
        Err(e) => return Err(format!("ref rejected closed term: {e:?}")),
    };
    let dnx =
        dnx_nf(term).map_err(|e| format!("dnx failed but ref has NF {reference:?}: {e:?}"))?;
    if alpha_eq(&dnx, &reference) {
        Ok(true)
    } else {
        Err(format!(
            "DISAGREE term={term:?} dnx={dnx:?} ref={reference:?}"
        ))
    }
}

// ── corpus: hand-written LINEAR closed terms ───────────────────────────────────
//
// The dnx surface λ is LINEAR (pass1.rs:78-83): every ordinary binder is used
// EXACTLY once; duplication needs an explicit `Rep`, deletion an explicit `Era`.
// So K (`λx.λy.x`) and S (which duplicate/discard) are NOT admissible without
// fan nodes — the corpus stays inside the pure-linear fragment the oracle covers.

fn corpus() -> Vec<E> {
    let id = || ab("x", nm("x"));
    // B = λf.λg.λx. f (g x) — each of f,g,x used once (linear).
    let b = || ab("f", ab("g", ab("x", ap(nm("f"), ap(nm("g"), nm("x"))))));
    vec![
        // Linear normal forms (their own NF).
        id(),
        b(),
        ab("f", ab("x", ap(nm("f"), nm("x")))), // λf.λx. f x
        // β-redexes that collapse, all linear.
        ap(id(), id()),                                   // I I → I
        ap(ab("f", ab("x", ap(nm("f"), nm("x")))), id()), // (λf.λx.f x) I → λx. I x → λx.x
        ap(ap(ap(b(), id()), id()), ab("w", nm("w"))),    // B I I w → w
        // nested redex under a binder.
        ab("q", ap(id(), nm("q"))), // λq. I q → λq.q
        // deeper linear chain.
        ap(ap(b(), id()), id()), // B I I → λx. I (I x)
    ]
}

#[test]
fn diag_partial_app() -> Result<(), DnxError> {
    let s = ab("f", ab("x", ap(nm("f"), nm("x"))));
    let term = ap(s, ab("y", nm("y"))); // (λf.λx.f x) I
    let r1 = dnx_elab::pass1(&term)?;
    println!("DIAG pass1 ok era={} rep={}", r1.era_used, r1.rep_used);
    let mut net = Net::<Proper, ΔL>::new(256);
    let mut env = Env::new();
    let elab = dnx_elab::elaborate(
        &mut net,
        0,
        &mut env,
        LOPath::root(),
        &term,
        &r1.usage_levels,
    );
    println!(
        "DIAG elaborate = {:?}",
        elab.as_ref().map(|(p, l)| (p.port_kind(), *l))
    );
    let (rp, _) = elab?;
    let root = if rp.port_kind() == PortKind::Principal {
        rp
    } else {
        let slot = net.alloc_free(0)?;
        net.connect(rp, slot, LOPath::root())?;
        slot
    };
    net.add_root("r".into(), root);
    let (canonical, stats) = normalize(net)?;
    let rb = match dnx_read::psi_native::<ΔL, NoVal, NoFun>(&canonical) {
        dnx_read::ReadbackResult::Lambda(a) => format!("Lambda({a:?})"),
        dnx_read::ReadbackResult::Partial(n) => format!("Partial({n})"),
    };
    println!(
        "DIAG r4={} interactions={} rb={rb}",
        stats.r4_count, stats.interactions
    );
    Ok(())
}

#[test]
fn smoke_bridge_matches_ref() -> Result<(), String> {
    // (λf.λx. f x)(λy.y)(λz.z)  →β  λz.z
    let s = ab("f", ab("x", ap(nm("f"), nm("x"))));
    let term = ap(ap(s, ab("y", nm("y"))), ab("z", nm("z")));
    assert!(agree(&term)?, "term has a NF, must compare");
    Ok(())
}

#[test]
fn corpus_bridge_matches_ref() -> Result<(), String> {
    for (i, term) in corpus().into_iter().enumerate() {
        agree(&term).map_err(|e| format!("corpus[{i}] {term:?}: {e}"))?;
    }
    Ok(())
}

// ── D2 differential fuzz: generated LINEAR closed λ-terms ──────────────────────
//
// The generator emits terms in the admissible fragment (pass1.rs:78-83): closed,
// every binder used EXACTLY once. `gen_using(vars, size)` produces a term whose
// free variables are precisely the set `vars`, each occurring once:
//   • |vars|==1, small  → that variable (leaf, consumes it);
//   • Abs               → bind a fresh name, body must use `vars ∪ {fresh}`;
//   • App(f,x)          → DISJOINT split `vars = Sf ⊎ Sx` (linearity: no overlap).
// The whole term is generated with `vars = ∅` ⇒ closed. The reference normalizer
// guards the net: a term with no NF (ref Diverged) is discarded, so the net is
// only driven on guaranteed-normalizing input and cannot hang.

use proptest::prelude::*;

/// Random disjoint partition of `vars` into (left, right).
fn split(vars: &[Arc<str>]) -> impl Strategy<Value = (Vec<Arc<str>>, Vec<Arc<str>>)> {
    let v = vars.to_vec();
    proptest::collection::vec(any::<bool>(), v.len()).prop_map(move |mask| {
        let mut l = Vec::new();
        let mut r = Vec::new();
        for (keep_left, name) in mask.iter().zip(v.iter()) {
            if *keep_left {
                l.push(name.clone());
            } else {
                r.push(name.clone());
            }
        }
        (l, r)
    })
}

fn gen_using(vars: Vec<Arc<str>>, fresh: u32, size: u32) -> BoxedStrategy<E> {
    // Leaf only possible when exactly one variable remains to be consumed.
    if size == 0 && vars.len() == 1 {
        let only = vars[0].clone();
        return Just(Ast::Name(only)).boxed();
    }
    let fname: Arc<str> = Arc::from(format!("g{fresh}").as_str());
    // Abs: introduce `fname`, body consumes vars ∪ {fname}.
    let abs = {
        let mut inner = vars.clone();
        inner.push(fname.clone());
        let fn_for_map = fname.clone();
        gen_using(inner, fresh + 1, size.saturating_sub(1))
            .prop_map(move |body| Ast::Abs(fn_for_map.clone(), Box::new(body)))
    };
    // App: split vars disjointly between the two children.
    let app = {
        let vs = vars.clone();
        split(&vars).prop_flat_map(move |(sl, sr)| {
            let half = size / 2;
            let _ = &vs;
            (
                gen_using(sl, fresh + 1, half),
                gen_using(sr, fresh + 1000, half),
            )
                .prop_map(|(f, x)| Ast::App(Box::new(f), Box::new(x)))
        })
    };
    match (vars.len(), size) {
        // Nothing to consume: only an Abs (which binds+uses) keeps it linear+closed.
        (0, _) => abs.boxed(),
        // One var, but still have budget: leaf or wrap.
        (1, _) => {
            prop_oneof![2 => Just(Ast::Name(vars[0].clone())).boxed(), 1 => abs, 1 => app].boxed()
        }
        // Many vars: must distribute them — App, or bind one more under an Abs.
        _ => prop_oneof![3 => app, 1 => abs].boxed(),
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 2000, ..ProptestConfig::default() })]

    /// dnx-normalize ≡ ref-normalize on every generated LINEAR closed term that
    /// has a normal form. This is the A1 (φ_S-idempotency) differential oracle.
    #[test]
    fn dnx_normalize_eq_ref_normalize(term in gen_using(Vec::new(), 0, 6)) {
        match agree(&term) {
            Ok(_) => {}                         // agreed, or ref had no NF (skipped)
            Err(msg) => prop_assert!(false, "{}", msg),
        }
    }
}
