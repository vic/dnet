//! T2 (trusted.md §T2) — φ_K replicator level/delta assignment vs `main.tex`.
//!
//! GATE: pins that the elaborator assigns replicator `level` + `delta0/delta1`
//! EXACTLY per the paper, so the keystone "App-fn-side rep lvl vs App-arg-side rep
//! lvl differ by one" stays a permanent green guarantee (driver-confirmed
//! paper-correct, not a bug).
//!
//! Paper rules asserted (quoted):
//!   * `main.tex:820` — "The level of an application's argument is one greater than
//!     that of the application itself, and the level of a replicator is one greater
//!     than that of its associated abstraction."
//!   * `main.tex:856` — `d_i = l_i - (l + 1)` (figure `fig:ltrules`, `[λx.M]_l, x∈FV(M)`).
//!
//! Code lines that assign these (cross-checked, no-invent):
//!   * App arg level bump: `pass1.rs:87` (`collect(level+1, .., x)`) + `pass2.rs:89`
//!     (`elab_impl(.., level + 1, .., x, ..)`); func stays `level` (`pass2.rs:79`).
//!   * Replicator level = abs_level+1: `pass2.rs:67` (`env.insert(x, (abs.aux1, level + 1))`),
//!     read back as `rep_level` when `e = name x` (`pass2.rs:61` returns stored level).
//!   * Deltas: `pass2.rs:108-109` (`d0 = la - rep_level`, `d1 = lb - rep_level`) with
//!     `la/lb = usage_levels[a]/[b]` (`pass2.rs:96-97`) — exactly `main.tex:856`.
//!
//! Assertions use the PAPER value (hand-computed below per term), never "whatever the
//! code emits" — a mismatch is a real elaborator bug, reported loudly.

use dnx_ast::{Ast, Name, PrimFun, PrimVal};
use dnx_core::{DnxError, LOPath, Net, PortId, PortKind, Proper, SlotView, ΔI, ΔL};
use dnx_elab::{elaborate, pass1};
use std::collections::{HashMap, HashSet};
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

fn nkey(s: &str) -> Name {
    Arc::from(s)
}

/// Pass-1 usage levels for `expr` (the source of `main.tex:820` arg-level bumps).
fn usage_levels(expr: &E) -> Result<HashMap<Name, u32>, DnxError> {
    Ok(pass1(expr).map_err(DnxError::from)?.usage_levels)
}

/// Walk the elaborated net from `root` over public ports, collecting every
/// reachable replicator slot's view. Mirrors the reachability of
/// `canonical_hash::dfs_assign` (principal/aux0/aux1 + back-edges), using only the
/// public `slot_view`/`peer` API. Dedup by `slot_idx` (a rep is entered via an aux
/// port, never its principal, so PortId-dedup would not coalesce the entry).
fn collect_reps<C: dnx_core::NetClassMarker>(net: &Net<Proper, C>, root: PortId) -> Vec<SlotView> {
    let mut seen: HashSet<u32> = HashSet::new();
    let mut reps: Vec<SlotView> = Vec::new();
    let mut stack: Vec<PortId> = vec![root];
    while let Some(port) = stack.pop() {
        if port.is_eraser() || port.is_null() {
            continue;
        }
        let idx = port.slot_idx();
        if !seen.insert(idx) {
            continue;
        }
        let s = net.slot_view(port);
        if s.is_free() {
            continue; // leaf
        }
        if s.is_rep() {
            reps.push(s);
        }
        let gen = port.gen_low();
        // All neighbors: principal peer + aux0 peer + aux1 peer.
        for kind in [PortKind::Principal, PortKind::Aux0, PortKind::Aux1] {
            let p = net.peer(PortId::new(idx, kind, gen));
            stack.push(p);
        }
    }
    reps
}

/// Elaborate `expr` (closed or open) under `ΔI` and return the reps reachable from
/// the result port. `ΔI` covers rep-only nets (no era) — `elaborator.md:32`.
fn reps_of(expr: &E) -> Result<Vec<SlotView>, DnxError> {
    let levels = usage_levels(expr)?;
    let mut net = Net::<Proper, ΔI>::new(64);
    let mut env: HashMap<Name, (PortId, u32)> = HashMap::new();
    let (result_p, _) = elaborate(&mut net, 0, &mut env, LOPath::root(), expr, &levels)?;
    Ok(collect_reps(&net, result_p))
}

// ---------------------------------------------------------------------------
// Term 1 — `λf. λx. f x` (church-1 / application shape).
//
// main.tex:820: app `f x` is at level 0; func `f` at level 0; arg `x` at 0+1 = 1.
// No replicator (f, x each linear). The keystone "fn-side vs arg-side" claim is the
// USE-LEVEL gap that *becomes* a rep level when a var is shared: arg-side is EXACTLY
// one greater than fn-side, in the paper direction.
// ---------------------------------------------------------------------------
#[test]
fn church1_app_fn_vs_arg_level_differ_by_one() -> Result<(), DnxError> {
    let e: E = ab("f", ab("x", ap(nm("f"), nm("x"))));
    let lv = usage_levels(&e)?;
    let lf = lv[&nkey("f")]; // func side
    let lx = lv[&nkey("x")]; // arg side
                             // main.tex:820 "level of an application's argument is one greater than the
                             // application itself" — assigned at pass1.rs:87 (collect(level+1, .., x)).
    assert_eq!(lf, 0, "func-side use level (pass1.rs:87 func at `level`)");
    assert_eq!(lx, 1, "arg-side use level (pass1.rs:87 arg at `level+1`)");
    assert_eq!(
        lx - lf,
        1,
        "arg-side exactly ONE greater than fn-side (main.tex:820)"
    );
    // No reps in a fully-linear term.
    assert!(reps_of(&e)?.is_empty(), "λf.λx.f x has no replicator");
    Ok(())
}

// ---------------------------------------------------------------------------
// Term 2 — nested application `f (g x)` (free f, g, x).
//
// main.tex:820 nesting: outer app @0 → f@0, (g x)@1; inner app @1 → g@1, x@2.
// Each arg-descent adds exactly one level.
// ---------------------------------------------------------------------------
#[test]
fn nested_app_level_nesting() -> Result<(), DnxError> {
    let e: E = ap(nm("f"), ap(nm("g"), nm("x")));
    let lv = usage_levels(&e)?;
    // f = outer func @0; g = inner func, sits in outer arg @0+1=1; x = inner arg @1+1=2.
    assert_eq!(lv[&nkey("f")], 0, "outer func @ level 0 (main.tex:820)");
    assert_eq!(
        lv[&nkey("g")],
        1,
        "inner func @ outer-arg level 1 (main.tex:820, pass1.rs:87)"
    );
    assert_eq!(
        lv[&nkey("x")],
        2,
        "inner arg @ level 2 (main.tex:820 applied twice)"
    );
    // Each step down an argument is +1.
    assert_eq!(lv[&nkey("g")] - lv[&nkey("f")], 1);
    assert_eq!(lv[&nkey("x")] - lv[&nkey("g")], 1);
    Ok(())
}

// ---------------------------------------------------------------------------
// Term 3 — self-applicator `λx. rep x as (a,b) in a b` (the Y/Ω shape).
//
// This is the EXACT keystone config (trusted.md:196; elaborator.md:247,322).
//   * λx @0 → x stored level = 0+1 = 1  (pass2.rs:67; main.tex:820 "rep level =
//     abs_level + 1").
//   * body app `a b` @0 → a (func/fn-side) @0; b (arg-side) @1  (pass1.rs:87).
//   * rep over `name x` → rep_level = x.stored = 1  (pass2.rs:61/98).
//   * d0 = la - rep_level = 0 - 1 = -1   (pass2.rs:108; main.tex:856 l_0=0,l+1=1).
//   * d1 = lb - rep_level = 1 - 1 =  0   (pass2.rs:109; main.tex:856 l_1=1,l+1=1).
// PAPER VALUE: rep level = 1, δ0 = -1, δ1 = 0.
// The fn-side use (a@0) is one BELOW the rep (δ0=-1); the arg-side use (b@1) is AT
// the rep (δ1=0) — the lvl-1/lvl-2 off-by-one the keystone bug was about.
// ---------------------------------------------------------------------------
#[test]
fn self_applicator_rep_level_and_deltas() -> Result<(), DnxError> {
    let e: E = ab("x", rep(nm("x"), "a", "b", ap(nm("a"), nm("b"))));

    // Use-level gap (fn-side a vs arg-side b) is exactly one — main.tex:820.
    let lv = usage_levels(&e)?;
    let la = lv[&nkey("a")]; // fn-side
    let lb = lv[&nkey("b")]; // arg-side
    assert_eq!(la, 0, "fn-side use a @0 (pass1.rs:87 func at level)");
    assert_eq!(lb, 1, "arg-side use b @1 (pass1.rs:87 arg at level+1)");
    assert_eq!(
        lb - la,
        1,
        "arg-side one greater than fn-side (main.tex:820)"
    );

    // The single replicator's emitted fields == paper.
    let reps = reps_of(&e)?;
    assert_eq!(reps.len(), 1, "exactly one rep for sharing x into (a,b)");
    let r = reps[0];
    assert!(r.is_rep());
    // rep level = abs_level + 1 = 1 (main.tex:820; pass2.rs:67).
    assert_eq!(r.data, 1, "rep level = abs_level+1 = 1 (main.tex:820)");
    // d_i = l_i - (l+1), l+1 = rep_level = 1 (main.tex:856; pass2.rs:108-109).
    assert_eq!(
        r.delta0, -1,
        "δ0 = la-rep = 0-1 = -1 (main.tex:856; elaborator.md:247)"
    );
    assert_eq!(
        r.delta1, 0,
        "δ1 = lb-rep = 1-1 = 0 (main.tex:856; elaborator.md:247)"
    );
    Ok(())
}

// ---------------------------------------------------------------------------
// Term 4 — multi-level delta: `λx. rep x as (a,b) in a ((λy.y) b)`.
//
// Exercises `d_i = l_i - (l+1)` (main.tex:856) at TWO distinct use levels
// (l_0 = 0, l_1 = 2), producing a negative AND a positive delta.
//   * λx @0 → x stored = 1 (pass2.rs:67); rep over `name x` → rep_level = 1.
//   * outer app `a (..)` @0 → a (fn-side) @0; arg `(λy.y) b` @1.
//   * inner app `(λy.y) b` @1 → `(λy.y)` @1; b (arg) @2  (pass1.rs:87 twice).
//   * la = 0, lb = 2, l+1 = rep_level = 1.
//   * d0 = 0 - 1 = -1 ; d1 = 2 - 1 = +1   (main.tex:856).
// PAPER VALUE: rep level = 1, δ0 = -1, δ1 = +1.
// ---------------------------------------------------------------------------
#[test]
fn multi_level_delta_scheme() -> Result<(), DnxError> {
    let inner = ap(ab("y", nm("y")), nm("b")); // (λy.y) b
    let e: E = ab("x", rep(nm("x"), "a", "b", ap(nm("a"), inner)));

    let lv = usage_levels(&e)?;
    assert_eq!(
        lv[&nkey("a")],
        0,
        "a (fn-side, outer func) @0 (pass1.rs:87)"
    );
    assert_eq!(
        lv[&nkey("b")],
        2,
        "b (arg of inner app) @2 (main.tex:820 ×2)"
    );

    let reps = reps_of(&e)?;
    assert_eq!(reps.len(), 1, "single rep sharing x");
    let r = reps[0];
    assert_eq!(r.data, 1, "rep level = abs_level+1 = 1 (main.tex:820)");
    // d_i = l_i - (l+1), l+1 = 1.
    assert_eq!(r.delta0, -1, "δ0 = 0-1 = -1 (main.tex:856, l_0=0)");
    assert_eq!(r.delta1, 1, "δ1 = 2-1 = +1 (main.tex:856, l_1=2)");
    Ok(())
}

// ---------------------------------------------------------------------------
// Cross-check: `λx. rep x as (a,b) in a b` under ΔL must be impossible (rep ⇒ ≥ΔI),
// so the rep path is genuinely exercised. (Sanity: rep_used flag drives class.)
// ---------------------------------------------------------------------------
#[test]
fn self_applicator_sets_rep_class() -> Result<(), DnxError> {
    let e: E = ab("x", rep(nm("x"), "a", "b", ap(nm("a"), nm("b"))));
    let r1 = pass1(&e).map_err(DnxError::from)?;
    assert!(r1.rep_used, "rep ⇒ NetClass ≥ I (elaborator.md:32)");
    assert!(!r1.era_used, "no era here");
    // ΔL would be the wrong class for a rep-using term — assert we never silently
    // build a linear net for it. (Construction under ΔL is a type-level mismatch;
    // we only ever elaborate it under ΔI above.)
    let _ = std::marker::PhantomData::<ΔL>;
    Ok(())
}
