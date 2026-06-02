#![forbid(unsafe_code)]

use dnx_ast::{Ast, Name, PrimFun, PrimVal};
use dnx_core::prim::{PrimState, PrimValue};
use dnx_core::{
    force_whnf_with_prims, CRules, Canonical, DnxError, Net, NetClassMarker, NormalizeConfig,
    PortId, PortKind, Proper,
};
use std::collections::{HashMap, VecDeque};
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Arc;

/// Max nesting depth for Scott-list reconstruction — bounds the recursive
/// element/spine walk so a malformed or cyclic net cannot loop forever.
const LIST_DEPTH_CAP: usize = 1 << 16;

static VAR_CTR: AtomicU32 = AtomicU32::new(0);

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct VarId(u32);

fn fresh_var() -> VarId {
    VarId(VAR_CTR.fetch_add(1, Ordering::Relaxed))
}

fn var_name(id: VarId) -> Name {
    Arc::from(format!("v{}", id.0).as_str())
}

/// Intermediate lambda IR — no sharing nodes.
#[derive(Debug, Clone)]
pub enum LambdaIR {
    Var(VarId),
    Abs(VarId, Box<LambdaIR>),
    App(Box<LambdaIR>, Box<LambdaIR>),
}

/// Result of psi_native readback.
pub enum ReadbackResult<V: PrimVal, F: PrimFun> {
    Lambda(Ast<V, F>),
    Partial(Name),
}

/// psi_native: Net<Canonical, C> → ReadbackResult.
pub fn psi_native<C: NetClassMarker, V: PrimVal, F: PrimFun>(
    net: &Net<Canonical, C>,
) -> ReadbackResult<V, F> {
    let root_slot = net.roots().values().next().copied().unwrap_or(PortId::NULL);
    if root_slot.is_null() || root_slot.is_eraser() {
        return ReadbackResult::Partial(Arc::from("_null"));
    }
    // If root_slot is a Free slot: its peer is the actual expression port (updated by R4).
    // If root_slot IS the expression port directly (e.g., abs.principal): use it directly.
    let root_port = if net.slot_is_live(root_slot) && net.slot_view(root_slot).is_free() {
        net.peer(root_slot)
    } else {
        root_slot
    };
    if root_port.is_null() || root_port.is_eraser() {
        return ReadbackResult::Partial(Arc::from("_null"));
    }
    let mut occ_env: HashMap<PortId, VarId> = HashMap::new();
    // Fail-closed: an unexpected node (one a canonical net cannot contain — golden
    // L1087: all normal Δ-nets are canonical, so only abs/app/var/free fans are
    // reachable from the root) makes `psi_s` return `Err`. Rather than fabricate a
    // wrong lambda we degrade to `Partial`, which every consumer maps to an error.
    let ir = match psi_s(net, root_port, &mut occ_env) {
        Ok(ir) => ir,
        Err(_) => return ReadbackResult::Partial(Arc::from("_unexpected")),
    };
    let mut supply: HashMap<VarId, VecDeque<Name>> = HashMap::new();
    let ast = lambda_to_dnx(ir, &mut supply);
    ReadbackResult::Lambda(ast)
}

// ── Scott-list / value readback (Proper net) ────────────────────────────────
//
// Lists are Scott-encoded pure lambdas (`nil = c: n: n`, `cons h t = c: n: c h t`,
// prelude.rs:19-20). Forced to WHNF a list head is therefore an ordinary FanAbs
// (`λc. λn. body`), indistinguishable by tag from a user lambda — so generic
// `psi_native` reads it back as `Lambda`. `read_value` instead runs the list's
// own eliminator shape (verified against the forced net) to reconstruct a
// `PrimValue::List`, recursing on each element and the tail. It is total: any
// non-list head (genuine lambda, prim fun, stuck) → `None`.

const TAG_PRIM_VAL: u8 = 0x0C;

/// Resolve a `demand` port — the port the evaluator drives — to the value head
/// reached across its wire. A live free root slot or an App-arg / Abs-body aux
/// points *at* the value (its peer); a port already sitting on the value head
/// (Principal of a delivered agent) is returned unchanged.
fn value_head<C: NetClassMarker>(net: &Net<Proper, C>, demand: PortId) -> PortId {
    let live = net.slot_is_live(demand);
    let on_value =
        live && demand.port_kind() == PortKind::Principal && !net.slot_view(demand).is_free();
    if on_value {
        demand
    } else {
        net.peer(demand)
    }
}

/// Read the value reached by forcing `demand` (a wire the evaluator drives) into
/// a `PrimValue`. Forces `demand` to WHNF, follows it to the value head, then
/// dispatches: a `PrimVal` head returns its stored value; a FanAbs head is
/// probed for the Scott-list shape and reconstructed as `PrimValue::List`.
/// Anything else (open lambda, unsaturated prim fun, stuck term) yields `None`.
pub fn read_value<C: CRules>(
    net: &mut Net<Proper, C>,
    ps: &mut PrimState,
    demand: PortId,
    cfg: &NormalizeConfig,
    depth: usize,
) -> Option<PrimValue> {
    if depth > LIST_DEPTH_CAP {
        return None;
    }
    force_whnf_with_prims(net, ps, demand, cfg).ok()?;
    let hp = value_head(net, demand);
    if hp.is_null() || hp.is_eraser() {
        return None;
    }
    let s = net.slot_view(hp);
    if s.tag == TAG_PRIM_VAL {
        return ps.vals.get(s.data as usize).cloned();
    }
    if s.is_fan() && s.fan_is_abs() && hp.port_kind() == PortKind::Principal {
        return scott_list_elems(net, ps, hp, cfg, depth).map(PrimValue::List);
    }
    None
}

/// Reconstruct a Scott list whose spine head is the FanAbs at `outer_abs`.
///
/// Net shape per cons cell (forced, verified): `λc. λn. ((c h) t)` —
///   outer_abs (λc): aux0 → inner_abs (λn); aux1 → the bound var `c`.
///   inner_abs body (peer of inner_abs.aux0) → outer App `((c h) t)`:
///     outer_app.aux1 → tail `t`;  outer_app.principal → inner App `(c h)`:
///       inner_app.aux1 → head `h`;  inner_app.principal → the var `c`.
/// `nil = λc. λn. n` has no such App spine (inner_abs body is the var `n`),
/// which terminates the walk. The `c`-identity guard (inner_app.principal peers
/// back to outer_abs.aux1) rejects unrelated two-argument lambdas.
fn scott_list_elems<C: CRules>(
    net: &mut Net<Proper, C>,
    ps: &mut PrimState,
    outer_abs: PortId,
    cfg: &NormalizeConfig,
    depth: usize,
) -> Option<Vec<PrimValue>> {
    let mut out = Vec::new();
    let mut cur = outer_abs;
    let mut steps = 0usize;
    loop {
        if steps > LIST_DEPTH_CAP {
            return None;
        }
        steps += 1;
        let s = net.slot_view(cur);
        // A list cell is `λc. λn. …`: outer FanAbs entered at its principal.
        if !(s.is_fan() && s.fan_is_abs() && cur.port_kind() == PortKind::Principal) {
            return None;
        }
        let var_c = PortId::new(cur.slot_idx(), PortKind::Aux1, cur.gen_low());
        let inner_abs = net.peer(PortId::new(cur.slot_idx(), PortKind::Aux0, cur.gen_low()));
        let is = net.slot_view(inner_abs);
        // The inner `λn` must be a distinct abstraction entered at its output
        // (Principal). `λx.x` has its body peer back to its own var port (Aux1),
        // whose slot is the same abs — reject so a bare lambda is not a list.
        if !(is.is_fan() && is.fan_is_abs() && inner_abs.port_kind() == PortKind::Principal) {
            return None;
        }
        let body = net.peer(PortId::new(
            inner_abs.slot_idx(),
            PortKind::Aux0,
            inner_abs.gen_low(),
        ));
        // `nil`: body is the inner var, not an App spine → list ends.
        let bs = net.slot_view(body);
        let is_app = bs.is_fan() && !bs.fan_is_abs() && body.port_kind() == PortKind::Aux0;
        if !is_app {
            return Some(out);
        }
        // outer App `(_ t)`: tail wire at aux1, inner App at principal.
        let tail_arg = PortId::new(body.slot_idx(), PortKind::Aux1, body.gen_low());
        let inner_app = net.peer(PortId::new(
            body.slot_idx(),
            PortKind::Principal,
            body.gen_low(),
        ));
        let ias = net.slot_view(inner_app);
        if !(ias.is_fan() && !ias.fan_is_abs() && inner_app.port_kind() == PortKind::Aux0) {
            return None;
        }
        // inner App `(c h)`: head demand at aux1; guard principal peers `c`.
        let head_demand = PortId::new(inner_app.slot_idx(), PortKind::Aux1, inner_app.gen_low());
        let c_use = net.peer(PortId::new(
            inner_app.slot_idx(),
            PortKind::Principal,
            inner_app.gen_low(),
        ));
        if c_use != var_c {
            return None;
        }
        // Element read recurses (nested lists / scalars), forcing its own demand.
        out.push(read_value(net, ps, head_demand, cfg, depth + 1)?);
        // Advance to the tail's own WHNF head (next cons cell or nil). Force from
        // the App's arg port so its spine reduces, then follow to the value head.
        force_whnf_with_prims(net, ps, tail_arg, cfg).ok()?;
        cur = value_head(net, tail_arg);
    }
}

/// psi_S: traverse Net<Canonical> from output port → LambdaIR.
/// occ_env maps occurrence PortIds to VarId (populated on Abs entry).
///
/// Fail-closed: returns `Err(DnxError::ReadbackIncomplete)` on a node a canonical
/// net cannot contain (the catch-all). Eraser/null/free leaves are *legitimate*
/// canonical interface nodes (golden L913-918, L937), so they read back as a name,
/// not an error.
fn psi_s<C: NetClassMarker>(
    net: &Net<Canonical, C>,
    port: PortId,
    occ_env: &mut HashMap<PortId, VarId>,
) -> Result<LambdaIR, DnxError> {
    if port.is_eraser() || port.is_null() {
        return Ok(LambdaIR::Var(fresh_var()));
    }
    // Variable occurrence check: must come BEFORE slot-type dispatch.
    if let Some(&var_id) = occ_env.get(&port) {
        return Ok(LambdaIR::Var(var_id));
    }
    let idx = port.slot_idx();
    let s = net.slot_view(port);

    if s.is_free() {
        return Ok(LambdaIR::Var(fresh_var()));
    }

    match port.port_kind() {
        PortKind::Principal if s.is_fan() && s.fan_is_abs() => {
            // Abs: entered via abs.principal (its output port).
            let var_id = fresh_var();
            let var_port = PortId::new(idx, PortKind::Aux1, port.gen_low());
            // Collect occurrence ports from variable side.
            collect_occ_for_var(net, var_port, var_id, occ_env);
            // Recurse into body: peer of abs.aux0.
            let body_aux = PortId::new(idx, PortKind::Aux0, port.gen_low());
            let body_peer = net.peer(body_aux);
            let body = psi_s(net, body_peer, occ_env);
            // Clean up occurrences (even on the error path, to keep occ_env sound).
            remove_occ_for_var(net, var_port, occ_env);
            Ok(LambdaIR::Abs(var_id, Box::new(body?)))
        }
        PortKind::Aux0 if s.is_fan() && !s.fan_is_abs() => {
            // App: entered via app.aux0 (result port).
            let func_p = PortId::new(idx, PortKind::Principal, port.gen_low());
            let arg_p = PortId::new(idx, PortKind::Aux1, port.gen_low());
            let func_peer = net.peer(func_p);
            let arg_peer = net.peer(arg_p);
            let func = psi_s(net, func_peer, occ_env)?;
            let arg = psi_s(net, arg_peer, occ_env)?;
            Ok(LambdaIR::App(Box::new(func), Box::new(arg)))
        }
        // Fail-closed catch-all: a port a canonical net cannot present at this
        // position (golden L1087). Return Err rather than fabricate a fresh var —
        // a wrong value beats a crash, but an Err beats a wrong value.
        _ => Err(DnxError::ReadbackIncomplete),
    }
}

/// Collect occurrence ports for a variable from abs.aux1 (the variable port).
/// Inserts ports that psi_s will be called with into occ_env.
///
/// For a linear variable: abs.aux1 IS the occurrence port.
/// For a replicated variable: abs.aux1's peer is rep.principal; rep.aux0/aux1 are occurrences.
fn collect_occ_for_var<C: NetClassMarker>(
    net: &Net<Canonical, C>,
    var_port: PortId, // abs.aux1
    var_id: VarId,
    occ_env: &mut HashMap<PortId, VarId>,
) {
    let peer = net.peer(var_port);
    if peer.is_eraser() || peer.is_null() {
        return; // erased variable
    }
    let s = net.slot_view(peer);
    if s.is_rep() && peer.port_kind() == PortKind::Principal {
        // C4 invariant: rep.principal → abs.aux1.
        // The two copies are at rep.aux0 and rep.aux1.
        let a0 = PortId::new(peer.slot_idx(), PortKind::Aux0, peer.gen_low());
        let a1 = PortId::new(peer.slot_idx(), PortKind::Aux1, peer.gen_low());
        collect_rep_branch(net, a0, var_id, occ_env);
        collect_rep_branch(net, a1, var_id, occ_env);
    } else {
        // Linear: abs.aux1 IS the occurrence (psi_s is called with it as body_peer).
        occ_env.insert(var_port, var_id);
    }
}

/// Collect from a rep.aux port (which may itself connect to another rep.principal).
fn collect_rep_branch<C: NetClassMarker>(
    net: &Net<Canonical, C>,
    rep_aux: PortId, // rep.aux0 or rep.aux1
    var_id: VarId,
    occ_env: &mut HashMap<PortId, VarId>,
) {
    let peer = net.peer(rep_aux);
    if peer.is_eraser() || peer.is_null() {
        return;
    }
    let s = net.slot_view(peer);
    if s.is_rep() && peer.port_kind() == PortKind::Principal {
        // Deeper rep chain (rare in Net<Canonical> but possible).
        let a0 = PortId::new(peer.slot_idx(), PortKind::Aux0, peer.gen_low());
        let a1 = PortId::new(peer.slot_idx(), PortKind::Aux1, peer.gen_low());
        collect_rep_branch(net, a0, var_id, occ_env);
        collect_rep_branch(net, a1, var_id, occ_env);
    } else {
        // rep_aux IS the occurrence port (psi_s is called with rep.aux0/aux1).
        occ_env.insert(rep_aux, var_id);
    }
}

fn remove_occ_for_var<C: NetClassMarker>(
    net: &Net<Canonical, C>,
    var_port: PortId,
    occ_env: &mut HashMap<PortId, VarId>,
) {
    let peer = net.peer(var_port);
    if peer.is_eraser() || peer.is_null() {
        return;
    }
    let s = net.slot_view(peer);
    if s.is_rep() && peer.port_kind() == PortKind::Principal {
        let a0 = PortId::new(peer.slot_idx(), PortKind::Aux0, peer.gen_low());
        let a1 = PortId::new(peer.slot_idx(), PortKind::Aux1, peer.gen_low());
        remove_rep_branch(net, a0, occ_env);
        remove_rep_branch(net, a1, occ_env);
    } else {
        occ_env.remove(&var_port);
    }
}

fn remove_rep_branch<C: NetClassMarker>(
    net: &Net<Canonical, C>,
    rep_aux: PortId,
    occ_env: &mut HashMap<PortId, VarId>,
) {
    let peer = net.peer(rep_aux);
    if peer.is_eraser() || peer.is_null() {
        return;
    }
    let s = net.slot_view(peer);
    if s.is_rep() && peer.port_kind() == PortKind::Principal {
        let a0 = PortId::new(peer.slot_idx(), PortKind::Aux0, peer.gen_low());
        let a1 = PortId::new(peer.slot_idx(), PortKind::Aux1, peer.gen_low());
        remove_rep_branch(net, a0, occ_env);
        remove_rep_branch(net, a1, occ_env);
    } else {
        occ_env.remove(&rep_aux);
    }
}

fn count_free(ir: &LambdaIR, var_id: VarId) -> usize {
    match ir {
        LambdaIR::Var(v) => {
            if *v == var_id {
                1
            } else {
                0
            }
        }
        LambdaIR::Abs(_, body) => count_free(body, var_id),
        LambdaIR::App(f, x) => count_free(f, var_id) + count_free(x, var_id),
    }
}

fn lambda_to_dnx<V: PrimVal, F: PrimFun>(
    ir: LambdaIR,
    supply: &mut HashMap<VarId, VecDeque<Name>>,
) -> Ast<V, F> {
    match ir {
        LambdaIR::Var(v) => {
            if let Some(q) = supply.get_mut(&v) {
                if let Some(name) = q.pop_front() {
                    return Ast::Name(name);
                }
            }
            Ast::Name(var_name(v))
        }
        LambdaIR::App(f, x) => {
            let f_ast = lambda_to_dnx(*f, supply);
            let x_ast = lambda_to_dnx(*x, supply);
            Ast::App(Box::new(f_ast), Box::new(x_ast))
        }
        LambdaIR::Abs(v, body) => {
            let n = count_free(&body, v);
            let x_name = var_name(v);
            match n {
                0 => {
                    let body_ast = lambda_to_dnx(*body, supply);
                    Ast::Abs(
                        x_name.clone(),
                        Box::new(Ast::Era(Box::new(Ast::Name(x_name)), Box::new(body_ast))),
                    )
                }
                1 => {
                    let mut q = VecDeque::new();
                    q.push_back(x_name.clone());
                    supply.insert(v, q);
                    let body_ast = lambda_to_dnx(*body, supply);
                    supply.remove(&v);
                    Ast::Abs(x_name, Box::new(body_ast))
                }
                k => {
                    debug_assert!(k >= 2, "k={k} should be >=2 in rep case");
                    let names: Vec<Name> = (0..k)
                        .map(|i| Arc::from(format!("{x_name}__{i}").as_str()))
                        .collect();
                    let q: VecDeque<Name> = names.iter().cloned().collect();
                    supply.insert(v, q);
                    let body_ast = lambda_to_dnx(*body, supply);
                    supply.remove(&v);
                    // Split off the first two names so the `>=2` invariant is carried
                    // by the type (two `Name`s + a rest slice) — no runtime assert.
                    // `k >= 2` here means `names` has at least two elements.
                    let mut it = names.into_iter();
                    let (n0, n1) = match (it.next(), it.next()) {
                        (Some(n0), Some(n1)) => (n0, n1),
                        // Unreachable: this arm is `k >= 2`. Degrade to a plain abs
                        // body rather than panic if the invariant were ever violated.
                        _ => return Ast::Abs(x_name.clone(), Box::new(body_ast)),
                    };
                    let rest: Vec<Name> = it.collect();
                    Ast::Abs(
                        x_name.clone(),
                        Box::new(chain_reps(x_name, n0, n1, rest, body_ast)),
                    )
                }
            }
        }
    }
}

/// Build a chain of `Rep` nodes splitting `orig` into `n0, n1, rest…` names.
///
/// The `>=2` invariant the old `assert!(names.len() >= 2)` guarded is now carried
/// by the signature: two mandatory `Name`s (`n0`, `n1`) plus an optional `rest`,
/// so a sub-2 split is unrepresentable and there is no release panic.
fn chain_reps<V: PrimVal, F: PrimFun>(
    orig: Name,
    n0: Name,
    n1: Name,
    rest: Vec<Name>,
    body: Ast<V, F>,
) -> Ast<V, F> {
    if let Some((next0, more)) = rest.split_first() {
        // More than two copies: emit `orig → (n0, orig')`, recurse on `orig'`
        // splitting it into `n1, next0, more…`.
        let x_prime: Name = Arc::from(format!("{orig}'").as_str());
        let inner = chain_reps(x_prime.clone(), n1, next0.clone(), more.to_vec(), body);
        Ast::Rep(Box::new(Ast::Name(orig)), n0, x_prime, Box::new(inner))
    } else {
        // Exactly two copies: terminal `orig → (n0, n1)`.
        Ast::Rep(Box::new(Ast::Name(orig)), n0, n1, Box::new(body))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dnx_ast::Ast;
    use dnx_core::{normalize, LOPath, Proper, ΔL};
    use dnx_elab::{elaborate, pass1};
    use std::collections::HashMap as HM;

    #[derive(Debug, Clone, PartialEq)]
    struct NoVal;
    #[derive(Debug, Clone, PartialEq)]
    struct NoFun;
    impl dnx_ast::PrimVal for NoVal {}
    impl dnx_ast::PrimFun for NoFun {}

    type E = Ast<NoVal, NoFun>;
    type Env = HM<Name, (PortId, u32)>;

    fn nm(s: &str) -> E {
        Ast::Name(Arc::from(s))
    }
    fn ab(x: &str, b: E) -> E {
        Ast::Abs(Arc::from(x), Box::new(b))
    }
    fn ap(f: E, x: E) -> E {
        Ast::App(Box::new(f), Box::new(x))
    }

    fn elab_norm(expr: &E) -> (dnx_core::Net<Canonical, ΔL>, dnx_core::ReduceStats) {
        let r1 = pass1(expr).unwrap();
        let mut net = Net::<Proper, ΔL>::new(64);
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
        // For aux ports (app.aux0, rep.aux, name): connect a free slot so it survives R4.
        // For principal ports (abs.principal): store directly (no connect — would create active pair).
        let root_port = if rp.port_kind() != PortKind::Principal {
            let root_slot = net.alloc_free(0).unwrap();
            net.connect(rp, root_slot, LOPath::root()).unwrap();
            root_slot
        } else {
            rp
        };
        net.add_root("r".into(), root_port);
        normalize(net).unwrap()
    }

    #[test]
    fn psi_native_identity() {
        let e = ab("x", nm("x"));
        let (canonical, _) = elab_norm(&e);
        match psi_native::<ΔL, NoVal, NoFun>(&canonical) {
            ReadbackResult::Lambda(ast) => {
                assert!(matches!(ast, Ast::Abs(_, _)), "identity reads back as Abs");
            }
            ReadbackResult::Partial(_) => panic!("expected Lambda"),
        }
    }

    #[test]
    fn psi_native_id_applied_reads_back_abs() {
        let e = ap(ab("x", nm("x")), ab("y", nm("y")));
        let (canonical, stats) = elab_norm(&e);
        assert_eq!(stats.r4_count, 1);
        match psi_native::<ΔL, NoVal, NoFun>(&canonical) {
            ReadbackResult::Lambda(ast) => {
                assert!(matches!(ast, Ast::Abs(_, _)), "reads back as Abs");
            }
            ReadbackResult::Partial(_) => panic!("expected Lambda"),
        }
    }
}
