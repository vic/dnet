//! `PyRuntime` — evaluate the minimal Python surface on the *same* Dnx core as
//! Nix. The Python frontend lowers to `Ast<NixPrimVal, NixPrimFun>` (the exact
//! IR `dnx-lang` emits), then this runtime mirrors `NixRuntime::build_net`
//! and `eval_with_base` (dnx-lang runtime.rs:105/187): it runs the same
//! `pass0`/`pass1`/`elaborate_with_prims` elaboration, forces the WHNF spine,
//! reads a scalar head if present, and otherwise normalizes and reads back with
//! `psi_native`. Because the pipeline is identical, a Python `derivation(...)`
//! and a Nix `derivationStrict {...}` reduce to the same attrset (one substrate,
//! many languages).

use crate::error::PyError;
use crate::lower::lower_module;
use crate::parser::parse_module;
use dnx_ast::Ast;
use dnx_core::prim::{PrimFunEntry, PrimState, PrimValue};
use dnx_core::{
    force_whnf_with_prims, normalize_demand, Canonical, LOPath, Net, NormalizeConfig, PortId,
    PortKind, Proper, ΔK,
};
use dnx_elab::{alpha_rename, elaborate_with_prims, pass0, pass1, PrimCtx};
use dnx_lang::nix_to_expr;
use dnx_lang::runtime::{NixEvalError, NixEvalResult};
use dnx_prim::prim::{nix_prim_table, NixPrimFun, NixPrimVal};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

type PyAst = Ast<NixPrimVal, NixPrimFun>;

/// Result of evaluating Python source. Reuses `NixEvalResult` so a Python value
/// and the equivalent Nix value are the *same* type and compare with the same
/// `conv_eq` — the substrate-equality the demo proves.
pub type PyEvalResult = NixEvalResult;

/// Scott-encoded list prelude, supplied to `pass0` and inlined where used. Same
/// definitions as `dnx-lang`'s prelude (dnx-lang prelude.rs:14) — they
/// are plain lambda calculus, parsed by the shared `nix_to_expr`, so a Python
/// list `[1, 2, 3]` elaborates to the identical Scott term a Nix list does.
const PRELUDE: &[(&str, &str)] = &[
    ("nil", "c: n: n"),
    ("cons", "h: t: c: n: c h t"),
    ("head", "xs: xs (h: t: h) nil"),
    ("tail", "xs: xs (h: t: t) nil"),
    ("isNil", "xs: xs (h: t: false) true"),
    (
        "length",
        "xs: (fix (self: ys: acc: ys (h: t: self t (acc + 1)) acc)) xs 0",
    ),
    (
        "elemAt",
        "xs: i: (fix (self: ys: j: ys (h: t: if j == i then h else self t (j + 1)) nil)) xs 0",
    ),
    (
        "map",
        "f: xs: (fix (self: ys: ys (h: t: cons (f h) (self t)) nil)) xs",
    ),
    (
        "filter",
        "pred: xs: (fix (self: ys: ys (h: t: if pred h then cons h (self t) else self t) nil)) xs",
    ),
    (
        "concat",
        "a: b: (fix (self: xs: xs (h: t: cons h (self t)) b)) a",
    ),
    (
        "foldl",
        "op: acc: xs: (fix (self: a: ys: ys (h: t: self (op a h) t) a)) acc xs",
    ),
];

/// Runtime for pure Python evaluation.
pub struct PyRuntime;

impl PyRuntime {
    pub fn pure() -> Self {
        PyRuntime
    }

    /// Parse and lower Python source to the shared core AST.
    fn to_ast(src: &str) -> Result<PyAst, PyError> {
        let stmts = parse_module(src)?;
        let mut bound = HashSet::new();
        lower_module(&stmts, &mut bound)
    }

    /// Build the prelude def map by parsing each Scott definition with the
    /// shared Nix lambda parser (so prelude terms are byte-identical to Nix's).
    fn prelude_defs() -> Result<HashMap<Arc<str>, PyAst>, PyError> {
        let mut m = HashMap::with_capacity(PRELUDE.len());
        for (name, src) in PRELUDE {
            let ast = nix_to_expr(src).map_err(|e| PyError::Parse(e.to_string()))?;
            m.insert(Arc::from(*name), ast);
        }
        Ok(m)
    }

    /// Elaborate `src` to a Proper net ready for reduction. Mirrors
    /// `NixRuntime::build_net` (dnx-lang runtime.rs:105) exactly, only the
    /// front-end (`to_ast`) differs.
    fn build_net(src: &str) -> Result<(Net<Proper, ΔK>, PrimState, PortId), NixEvalError> {
        let ast = Self::to_ast(src).map_err(|e| NixEvalError::Readback(e.to_string()))?;
        let defs = Self::prelude_defs().map_err(|e| NixEvalError::Readback(e.to_string()))?;
        let ast = pass0(&defs, &ast).map_err(NixEvalError::Elaborate2)?;
        // Enforce Barendregt (mirror NixRuntime::build_net): inlined prelude bodies
        // (cons/nil/map/…) keep their binder names, shadowing call-site binders.
        // α-rename to globally-unique names so pass1/pass2's flat name maps hold.
        let ast = alpha_rename(&ast);
        let r1 = pass1(&ast).map_err(NixEvalError::Elaborate2)?;

        let mut prim_state = PrimState::default();
        let (rp, mut net) = {
            let mut ctx = PrimCtx {
                state: &mut prim_state,
                to_fun: pyprimfun_to_entry,
                to_val: pyprimval_to_value,
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

    /// Evaluate Python `src` to a value, mirroring `NixRuntime::eval_with_base`
    /// (dnx-lang runtime.rs:187): force the WHNF spine, take the scalar
    /// fast-path, else normalize and read back structurally.
    pub fn eval(&self, src: &str) -> PyEvalResult {
        let (mut net, mut prim_state, root_port) = match Self::build_net(src) {
            Ok(t) => t,
            Err(e) => return NixEvalResult::Error(e),
        };
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

        // Scott-list head, mirroring dnx-lang runtime.rs:217 — a list is a FanAbs
        // the scalar path misses; reconstruct it structurally on the Proper net so
        // the Python frontend reads `[1, 2, 3]` back as the same `List` value Nix
        // does. Non-lists fall through to full-NF lambda readback unchanged.
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
}

/// True iff the slot holds a `PrimVal` (vs a `PrimFun`). Both are "prim" slots
/// (`SlotView::is_prim`); they differ in the low tag bit (PrimVal even, PrimFun
/// odd — dnx-core net.rs:95, prim.rs:8). Read purely through the public
/// `SlotView`, so no internal tag constant is duplicated here.
fn is_prim_val(s: dnx_core::SlotView) -> bool {
    s.is_prim() && (s.tag & 1) == 0
}

fn prim_to_result(v: &PrimValue) -> Option<PyEvalResult> {
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
/// `NixRuntime::read_scalar_head`, dnx-lang runtime.rs:226).
fn read_scalar_head(net: &Net<Proper, ΔK>, ps: &PrimState, root: PortId) -> Option<PyEvalResult> {
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

/// Read back a canonical net to a value (mirrors `NixRuntime::readback_result`,
/// dnx-lang runtime.rs:248).
fn readback_result(net: &Net<Canonical, ΔK>, ps: &PrimState) -> PyEvalResult {
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

/// Map a `NixPrimFun` to its runtime entry via the shared Nix prim table — the
/// Python frontend emits the same prim funs Nix does, so the same table serves.
fn pyprimfun_to_entry(f: &NixPrimFun) -> Option<PrimFunEntry> {
    let table = nix_prim_table();
    let id = table.lookup(pyprimfun_name(f)?)?;
    table.make_entry(id)
}

fn pyprimval_to_value(v: &NixPrimVal) -> Option<PrimValue> {
    Some(match v {
        NixPrimVal::Int(n) => PrimValue::Int(*n),
        NixPrimVal::Float(f) => PrimValue::Float(*f),
        NixPrimVal::Str(s) => PrimValue::Str(s.clone()),
        NixPrimVal::Bool(b) => PrimValue::Bool(*b),
        NixPrimVal::Path(p) => PrimValue::Path(p.clone()),
        NixPrimVal::Null => PrimValue::Null,
    })
}

/// Prim-table key for each `NixPrimFun` the Python lowering can emit. Names match
/// `nix_prim_table` registrations (dnx-lang prim.rs:534); `derivationStrict`
/// is the `Builtin` the `derivation(...)` form lowers to.
fn pyprimfun_name(f: &NixPrimFun) -> Option<&'static str> {
    Some(match f {
        NixPrimFun::Add => "add",
        NixPrimFun::Sub => "sub",
        NixPrimFun::Mul => "mul",
        NixPrimFun::Div => "div",
        NixPrimFun::Neg => "neg",
        NixPrimFun::Eq => "eq",
        NixPrimFun::Ne => "ne",
        NixPrimFun::Lt => "lt",
        NixPrimFun::Le => "le",
        NixPrimFun::Gt => "gt",
        NixPrimFun::Ge => "ge",
        NixPrimFun::Select => "select",
        NixPrimFun::HasAttr => "has_attr",
        NixPrimFun::Insert => "insert",
        NixPrimFun::EmptyAttrSet => "empty_attr_set",
        // `toString` coercion emitted by f-string interpolation holes (mirrors
        // the Nix string-interp lowering, dnx-lang literals.rs:44).
        NixPrimFun::ToString2 => "to_string",
        // Builtins the Python frontend can emit (free names) map to the same
        // prim-table keys Nix uses (dnx-lang runtime.rs:346), so the shared
        // table serves both languages.
        NixPrimFun::Builtin(name) => match name.as_ref() {
            "derivationStrict" => "derivation_strict",
            "typeOf" => "type_of",
            "isFunction" => "is_function",
            "isInt" => "is_int",
            "isFloat" => "is_float",
            "isString" => "is_string",
            "isNull" => "is_null",
            "isList" => "is_list",
            "stringLength" => "string_length",
            "substring" => "substring",
            "toString" => "to_string",
            "toInt" => "to_int",
            "bitAnd" => "bit_and",
            "bitOr" => "bit_or",
            "bitXor" => "bit_xor",
            _ => return None,
        },
        _ => return None,
    })
}
