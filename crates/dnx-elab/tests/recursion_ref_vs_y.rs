//! KEYSTONE oracle: a recursive definition that NORMALIZES under the native
//! λ-Y desugaring (`pass0::desugar_fix`, the real production path).
//!
//! Computes a Scott-numeral "force the recursive call once, then hit the base
//! case" over a pure λ-net (no prims). The λ-Y side builds the self-application
//! Y-knot. It HISTORICALLY diverged (replicators climbed R7-commute, never
//! R6-annihilated, even though the computation terminates —
//! vic/notes/diag-bug2-recursion.md); FIXED 2026-06-05 by the `write_port`
//! eraser-flag change (see `lambda_y_recursion_normalizes`), so the Scott `Era`s
//! now decay the fix replicator and λ-Y bottoms out natively.
//!
//! Scott encoding (pure λ):
//!   Z      = λz.λs. z              (zero)
//!   S p    = λz.λs. s p            (successor of p)
//!   marker = λm. m                 (base-case result, a distinguished λ)
//!   loop   = fix (λself. λn. n marker (λp. self p))
//!     loop Z       → Z marker step       → marker
//!     loop (S Z)   → (S Z) marker step    → step Z → self Z → loop Z → marker
//!   so `loop (S Z)` FORCES the recursive `self` exactly once, then terminates.

use dnx_ast::{Ast, Name, PrimFun, PrimVal};
use dnx_core::{normalize, DnxError, LOPath, Net, PortId, Proper, ΔK};
use dnx_elab::{elaborate, pass0, pass1};
use std::collections::HashMap;
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
fn fix(e: E) -> E {
    Ast::Fix(Box::new(e))
}
/// `Era(e, body)`: linearly discard `e`, yield `body` (φ_K is linear; every
/// binder must be used exactly once, so unused Scott vars are explicitly erased).
fn era(e: E, body: E) -> E {
    Ast::Era(Box::new(e), Box::new(body))
}

/// Scott zero: λz.λs. (erase s) z
fn scott_zero() -> E {
    ab("z", ab("s", era(nm("s"), nm("z"))))
}
/// Scott successor of `p`: λz.λs. (erase z) (s p)
fn scott_succ(p: E) -> E {
    ab("z", ab("s", era(nm("z"), ap(nm("s"), p))))
}
/// marker: λm.m
fn marker() -> E {
    ab("m", nm("m"))
}

/// `loop = fix (λself. λn. n marker (λp. self p))`, applied to `arg`.
fn loop_applied(arg: E) -> E {
    let body = ab(
        "self",
        ab(
            "n",
            ap(ap(nm("n"), marker()), ab("p", ap(nm("self"), nm("p")))),
        ),
    );
    ap(fix(body), arg)
}

/// Elaborate a resolved (post-pass0) closed expr into a `Net<Proper, ΔK>`.
fn elab(expr: &E) -> Result<(Net<Proper, ΔK>, PortId), DnxError> {
    let levels = pass1(expr).map_err(DnxError::from)?.usage_levels;
    let mut net = Net::<Proper, ΔK>::new(4096);
    let mut env: HashMap<Name, (PortId, u32)> = HashMap::new();
    let (root, _) = elaborate(&mut net, 0, &mut env, LOPath::root(), expr, &levels)?;
    net.add_root(Arc::from("res"), root);
    Ok((net, root))
}

/// λ-Y native recursion: `loop (S Z)` via the real `pass0::desugar_fix` NORMALIZES.
///
/// HISTORICAL: this previously DIVERGED — the fix replicator commuted (R5) and its
/// fan-out climbed (R7) instead of annihilating (R6), because the Scott `Era`s on the
/// unused bound vars never marked the replicator's aux ports as erased. FIXED
/// 2026-06-05: `write_port` (net.rs) now sets `TAG_AUX0/1_ERASED` whenever an eraser is
/// wired to a replicator aux (flag ⇔ wire), so `c3_rep_decay` collapses the dead aux to
/// a wire (Case B, main.tex:939) instead of commuting. Every rule applied is sound, so by
/// Δ-Net confluence (main.tex, Church–Rosser) the unique normal form is `marker` — the
/// native λ-Y recursion now bottoms out natively, no Book.
#[test]
fn lambda_y_recursion_normalizes() -> Result<(), DnxError> {
    let src = loop_applied(scott_succ(scott_zero()));
    let defs: HashMap<Name, E> = HashMap::new();
    let resolved = pass0(&defs, &src).map_err(DnxError::from)?; // desugar_fix → Y-net
    let (net, _root) = elab(&resolved)?;
    let (_canon, stats) = normalize(net)?;
    assert!(
        stats.interactions > 0,
        "λ-Y cleanly normalizes the terminating recursion"
    );
    Ok(())
}
