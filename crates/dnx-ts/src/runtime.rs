//! `TsRuntime` — evaluate a JSON document on the *same* Dnx core as Nix. The
//! front-end (`to_ast`) parses with `tree-sitter-json` and lowers to
//! `Ast<NixPrimVal, NixPrimFun>`; everything after is the shared stack. This
//! runtime mirrors `NixRuntime::build_net`/`eval_with_base` (dnx-lang
//! runtime.rs:105/187) and `PyRuntime` (dnx-pyparse runtime.rs) exactly — same
//! `pass0`/`pass1`/`elaborate_with_prims`, same WHNF-spine force, same scalar
//! fast-path, same `psi_native` readback. Because the pipeline is identical, a
//! JSON object and the equivalent Nix attrset reduce to the same value.

use crate::error::TsError;
use crate::lower::lower_document;
use dnx_ast::Ast;
use dnx_core::prim::{PrimFunEntry, PrimState, PrimValue};
use dnx_core::{
    force_whnf_with_prims, normalize_demand, Canonical, LOPath, Net, NormalizeConfig, PortId,
    PortKind, Proper, SlotView, ΔK,
};
use dnx_elab::{elaborate_with_prims, pass0, pass1, PrimCtx};
use dnx_lang::nix_to_expr;
use dnx_lang::prim::{nix_prim_table, nixprimfun_name, NixPrimFun, NixPrimVal};
use dnx_lang::runtime::{NixEvalError, NixEvalResult};
use std::collections::HashMap;
use std::sync::Arc;

type TsAst = Ast<NixPrimVal, NixPrimFun>;

/// Result of evaluating a JSON document. Reuses `NixEvalResult` so a JSON value
/// and the equivalent Nix value are the *same* type and compare equal.
pub type TsEvalResult = NixEvalResult;

/// Scott-list prelude needed by JSON arrays. Same definitions as `dnx-lang`
/// and `dnx-pyparse` use (plain lambda calculus, parsed by the shared
/// `nix_to_expr`), so a JSON array `[1, 2]` elaborates to the identical Scott
/// term a Nix list `[ 1 2 ]` does. Objects use prims only and need no prelude.
const PRELUDE: &[(&str, &str)] = &[("nil", "c: n: n"), ("cons", "h: t: c: n: c h t")];

/// Runtime for pure JSON evaluation through the shared Dnx engine.
pub struct TsRuntime;

impl TsRuntime {
    pub fn pure() -> Self {
        TsRuntime
    }

    /// Parse JSON with tree-sitter and lower it to the shared core AST.
    fn to_ast(src: &str) -> Result<TsAst, TsError> {
        let mut parser = tree_sitter::Parser::new();
        parser
            .set_language(&tree_sitter_json::LANGUAGE.into())
            .map_err(|e| TsError::Parse(format!("set_language: {e}")))?;
        let tree = parser
            .parse(src, None)
            .ok_or_else(|| TsError::Parse("tree-sitter produced no tree".into()))?;
        let root = tree.root_node();
        if root.has_error() {
            return Err(TsError::Parse("JSON syntax error".into()));
        }
        lower_document(root, src)
    }

    /// Build the prelude def map by parsing each Scott definition with the shared
    /// Nix lambda parser (so prelude terms are byte-identical to Nix's).
    fn prelude_defs() -> Result<HashMap<Arc<str>, TsAst>, TsError> {
        let mut m = HashMap::with_capacity(PRELUDE.len());
        for (name, src) in PRELUDE {
            let ast = nix_to_expr(src).map_err(|e| TsError::Parse(e.to_string()))?;
            m.insert(Arc::from(*name), ast);
        }
        Ok(m)
    }

    /// Elaborate a JSON document to a Proper net ready for reduction. Mirrors
    /// `PyRuntime::build_net` (dnx-pyparse runtime.rs) and `NixRuntime::build_net`
    /// (dnx-lang runtime.rs:105) exactly; only the front-end differs.
    fn build_net(src: &str) -> Result<(Net<Proper, ΔK>, PrimState, PortId), NixEvalError> {
        let ast = Self::to_ast(src).map_err(|e| NixEvalError::Readback(e.to_string()))?;
        Self::build_net_from_ast(&ast)
    }

    /// The shared elaborate/reduce tail: lower any front-end `Ast` (JSON or the
    /// hand-grammar lambda surface) through the identical `pass0`/`pass1`/
    /// `elaborate_with_prims` pipeline. Both surfaces feed this, so they reduce
    /// on byte-identical machinery.
    fn build_net_from_ast(
        ast: &TsAst,
    ) -> Result<(Net<Proper, ΔK>, PrimState, PortId), NixEvalError> {
        let defs = Self::prelude_defs().map_err(|e| NixEvalError::Readback(e.to_string()))?;
        let ast = pass0(&defs, ast).map_err(NixEvalError::Elaborate2)?;
        let r1 = pass1(&ast).map_err(NixEvalError::Elaborate2)?;

        let mut prim_state = PrimState::default();
        let (rp, mut net) = {
            let mut ctx = PrimCtx {
                state: &mut prim_state,
                to_fun: tsprimfun_to_entry,
                to_val: tsprimval_to_value,
            };
            let mut net = Net::<Proper, ΔK>::new(1 << 16);
            let mut env = HashMap::new();
            let (rp, _) = elaborate_with_prims(
                &mut net,
                &mut ctx,
                0,
                &mut env,
                LOPath::root(),
                &ast,
                &r1.usage_levels,
            )
            .map_err(NixEvalError::Elaborate)?;
            (rp, net)
        };

        let root_port = if rp.port_kind() != PortKind::Principal {
            let rs = net.alloc_free(0).map_err(NixEvalError::Elaborate)?;
            net.connect(rp, rs, LOPath::root())
                .map_err(NixEvalError::Elaborate)?;
            rs
        } else {
            rp
        };
        net.add_root(Arc::from("r"), root_port);
        Ok((net, prim_state, root_port))
    }

    /// Evaluate JSON `src` to a value (parses with tree-sitter, lowers, reduces).
    pub fn eval(&self, src: &str) -> TsEvalResult {
        match Self::build_net(src) {
            Ok((net, ps, root)) => eval_net(net, ps, root),
            Err(e) => NixEvalResult::Error(e),
        }
    }

    /// Evaluate a hand-grammar lambda program `src` to a value. The only
    /// difference from `eval` is the front-end (`lower_lambda_surface` instead of
    /// the JSON CST); the elaborate/reduce tail is the shared `build_net_from_ast`
    /// + `eval_net`, so an equivalent nix lambda reduces to the same value.
    pub fn eval_lambda(&self, src: &str) -> TsEvalResult {
        let ast = match crate::surface::lower_lambda_surface(src) {
            Ok(a) => a,
            Err(e) => return NixEvalResult::Error(NixEvalError::Readback(e.to_string())),
        };
        match Self::build_net_from_ast(&ast) {
            Ok((net, ps, root)) => eval_net(net, ps, root),
            Err(e) => NixEvalResult::Error(e),
        }
    }
}

/// The shared reduce/readback tail, mirroring `PyRuntime::eval`
/// (dnx-pyparse runtime.rs): force the WHNF spine, take the scalar fast-path,
/// recognize a Scott list, else normalize and read back structurally. Both
/// front-ends (`eval`, `eval_lambda`) run this identical tail.
fn eval_net(
    mut net: Net<Proper, ΔK>,
    mut prim_state: PrimState,
    root_port: PortId,
) -> TsEvalResult {
    let cfg = NormalizeConfig {
        max_steps: Some(50_000_000),
        max_agents: Some((1 << 16) - 16),
    };
    if let Err(e) = force_whnf_with_prims(&mut net, &mut prim_state, root_port, &cfg) {
        return NixEvalResult::Error(NixEvalError::Elaborate(e));
    }
    if let Some(r) = read_scalar_head(&net, &prim_state, root_port) {
        return r;
    }

    // Scott-list head, mirroring dnx-lang runtime.rs:217 and dnx-pyparse
    // runtime.rs:163 — a JSON array lowers to a Scott `cons`/`nil` FanAbs the
    // scalar path misses; the shared `dnx_read::read_value` recognizer
    // reconstructs it structurally so a JSON array reads back as the same
    // `List` value the equivalent nix list does. Non-lists fall through to
    // full-NF lambda readback unchanged.
    if let Some(PrimValue::List(xs)) =
        dnx_read::read_value(&mut net, &mut prim_state, root_port, &cfg, 0)
    {
        return NixEvalResult::List(xs);
    }

    let canonical = match normalize_demand(net, &mut prim_state, root_port, &cfg) {
        Ok((c, _)) => c,
        Err(e) => return NixEvalResult::Error(NixEvalError::Elaborate(e)),
    };
    readback_result(&canonical, &prim_state)
}

/// True iff the slot holds a `PrimVal` (vs a `PrimFun`): both are prim slots,
/// differing in the low tag bit (PrimVal even). Read through the public
/// `SlotView` (dnx-pyparse runtime.rs `is_prim_val`), so no tag constant leaks.
fn is_prim_val(s: SlotView) -> bool {
    s.is_prim() && (s.tag & 1) == 0
}

fn prim_to_result(v: &PrimValue) -> Option<TsEvalResult> {
    Some(match v {
        PrimValue::Int(n) => NixEvalResult::Int(*n),
        PrimValue::Float(f) => NixEvalResult::Float(*f),
        PrimValue::Str(s) => NixEvalResult::Str(s.clone()),
        PrimValue::Bool(b) => NixEvalResult::Bool(*b),
        PrimValue::Null => NixEvalResult::Null,
        PrimValue::List(xs) => NixEvalResult::List(xs.clone()),
        PrimValue::AttrSet(kvs) => NixEvalResult::AttrSet(kvs.clone()),
        _ => return None,
    })
}

/// Read a scalar value sitting at the WHNF head (mirrors
/// `PyRuntime::read_scalar_head`, dnx-pyparse runtime.rs).
fn read_scalar_head(net: &Net<Proper, ΔK>, ps: &PrimState, root: PortId) -> Option<TsEvalResult> {
    let s0 = net.slot_view(root);
    let hp = if s0.is_free() { net.peer(root) } else { root };
    if hp.is_null() || hp.is_eraser() {
        return None;
    }
    let s = net.slot_view(hp);
    if !is_prim_val(s) {
        return None;
    }
    prim_to_result(ps.vals.get(s.data as usize)?)
}

/// Read back a canonical net to a value (mirrors `PyRuntime::readback_result`,
/// dnx-pyparse runtime.rs).
fn readback_result(net: &Net<Canonical, ΔK>, ps: &PrimState) -> TsEvalResult {
    use dnx_read::{psi_native, ReadbackResult};

    let root_slot = match net.roots().get("r").copied() {
        Some(p) => p,
        None => return NixEvalResult::Error(NixEvalError::Readback("no root".into())),
    };
    if root_slot.is_null() || root_slot.is_eraser() {
        return NixEvalResult::Error(NixEvalError::Readback("null root".into()));
    }
    let root_port = if net.slot_is_live(root_slot) && net.slot_view(root_slot).is_free() {
        net.peer(root_slot)
    } else {
        root_slot
    };
    if root_port.is_null() || root_port.is_eraser() {
        return NixEvalResult::Error(NixEvalError::Readback("null result".into()));
    }

    let s = net.slot_view(root_port);
    if is_prim_val(s) {
        match ps.vals.get(s.data as usize).and_then(prim_to_result) {
            Some(r) => r,
            None => NixEvalResult::Error(NixEvalError::Readback("unreadable prim".into())),
        }
    } else if s.is_prim() {
        NixEvalResult::Error(NixEvalError::Readback("unsaturated prim fun".into()))
    } else {
        match psi_native::<ΔK, NixPrimVal, NixPrimFun>(net) {
            ReadbackResult::Lambda(ast) => NixEvalResult::Lambda(ast),
            ReadbackResult::Partial(_) => {
                NixEvalResult::Error(NixEvalError::Readback("open term".into()))
            }
        }
    }
}

/// Map a `NixPrimFun` to its runtime entry via the shared Nix prim table, using
/// the canonical `nixprimfun_name` key (dnx-prim prim.rs:1310) so every prim
/// either front-end can emit — the JSON path's `insert`/`empty_attr_set` and the
/// lambda path's `add` — resolves to the same entry Nix registers.
fn tsprimfun_to_entry(f: &NixPrimFun) -> Option<PrimFunEntry> {
    let table = nix_prim_table();
    let id = table.lookup(nixprimfun_name(f)?)?;
    table.make_entry(id)
}

fn tsprimval_to_value(v: &NixPrimVal) -> Option<PrimValue> {
    Some(match v {
        NixPrimVal::Int(n) => PrimValue::Int(*n),
        NixPrimVal::Float(f) => PrimValue::Float(*f),
        NixPrimVal::Str(s) => PrimValue::Str(s.clone()),
        NixPrimVal::Bool(b) => PrimValue::Bool(*b),
        NixPrimVal::Path(p) => PrimValue::Path(p.clone()),
        NixPrimVal::Null => PrimValue::Null,
    })
}
