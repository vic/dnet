pub(crate) mod canon;
pub mod gpu;
pub mod parallel;
pub(crate) mod rules;
pub mod whnf;

use crate::class::{Canonical, NetClassMarker, Proper, ΔA, ΔI, ΔK, ΔL};
use crate::net::{certify_canonical, into_canonical, ActivePair, C4Candidate, Net};
use crate::{DnxError, PortId, PortKind};
use canon::{c1_mark_sweep, c2_rep_merge, c3_rep_decay, c4_aux_fan_replication};
use rules::{r2_era_fan, r3_era_rep, r4_fan_fan, r5_fan_rep, r6_rep_rep, r7_rep_rep};

/// Stats returned by normalize — used by oracle tests.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ReduceStats {
    pub interactions: u64,
    pub r4_count: u64,
}

/// Optional C-rule hooks — sealed by the 4 class impls.
pub trait CRules: NetClassMarker + Sized {
    fn c2(net: &mut Net<Proper, Self>, rep: PortId, lo: &crate::LOPath) -> Result<(), DnxError>;
    fn c3(net: &mut Net<Proper, Self>, rep: PortId, lo: &crate::LOPath) -> Result<(), DnxError>;
    fn c4(net: &mut Net<Proper, Self>, cand: &C4Candidate) -> Result<(), DnxError>;
    fn c1(net: &mut Net<Proper, Self>);
    const HAS_REP: bool;
    const HAS_ERA: bool;
}

impl CRules for ΔL {
    fn c2(_: &mut Net<Proper, ΔL>, _: PortId, _: &crate::LOPath) -> Result<(), DnxError> {
        Ok(())
    }
    fn c3(_: &mut Net<Proper, ΔL>, _: PortId, _: &crate::LOPath) -> Result<(), DnxError> {
        Ok(())
    }
    fn c4(_: &mut Net<Proper, ΔL>, _: &C4Candidate) -> Result<(), DnxError> {
        Ok(())
    }
    fn c1(_: &mut Net<Proper, ΔL>) {}
    const HAS_REP: bool = false;
    const HAS_ERA: bool = false;
}

impl CRules for ΔA {
    fn c2(_: &mut Net<Proper, ΔA>, _: PortId, _: &crate::LOPath) -> Result<(), DnxError> {
        Ok(())
    }
    fn c3(_: &mut Net<Proper, ΔA>, _: PortId, _: &crate::LOPath) -> Result<(), DnxError> {
        Ok(())
    }
    fn c4(_: &mut Net<Proper, ΔA>, _: &C4Candidate) -> Result<(), DnxError> {
        Ok(())
    }
    fn c1(net: &mut Net<Proper, ΔA>) {
        c1_mark_sweep(net);
    }
    const HAS_REP: bool = false;
    const HAS_ERA: bool = true;
}

impl CRules for ΔI {
    fn c2(net: &mut Net<Proper, ΔI>, rep: PortId, lo: &crate::LOPath) -> Result<(), DnxError> {
        c2_rep_merge(net, rep, lo)
    }
    fn c3(_: &mut Net<Proper, ΔI>, _: PortId, _: &crate::LOPath) -> Result<(), DnxError> {
        Ok(())
    }
    fn c4(net: &mut Net<Proper, ΔI>, cand: &C4Candidate) -> Result<(), DnxError> {
        c4_aux_fan_replication(net, cand)
    }
    fn c1(_: &mut Net<Proper, ΔI>) {}
    const HAS_REP: bool = true;
    const HAS_ERA: bool = false;
}

impl CRules for ΔK {
    fn c2(net: &mut Net<Proper, ΔK>, rep: PortId, lo: &crate::LOPath) -> Result<(), DnxError> {
        c2_rep_merge(net, rep, lo)
    }
    fn c3(net: &mut Net<Proper, ΔK>, rep: PortId, lo: &crate::LOPath) -> Result<(), DnxError> {
        c3_rep_decay(net, rep, lo)
    }
    fn c4(net: &mut Net<Proper, ΔK>, cand: &C4Candidate) -> Result<(), DnxError> {
        c4_aux_fan_replication(net, cand)
    }
    fn c1(net: &mut Net<Proper, ΔK>) {
        c1_mark_sweep(net);
    }
    const HAS_REP: bool = true;
    const HAS_ERA: bool = true;
}

#[allow(private_bounds)]
pub fn normalize<C: CRules>(
    mut net: Net<Proper, C>,
) -> Result<(Net<Canonical, C>, ReduceStats), DnxError> {
    let mut stats = ReduceStats::default();

    while let Some((_, pair)) = net.frontier1.pop_first() {
        if is_stale_pair(&pair, &net) {
            continue;
        }
        stats.interactions += 1;
        dispatch_phase1::<C>(&mut net, pair, &mut stats)?;
    }

    while drain_phase2(&mut net)? {}

    // C1: only A/K (guarded by net_pending_c1 at runtime).
    if net.net_pending_c1() {
        C::c1(&mut net);
    }

    let w = certify_canonical(&net)?;
    Ok((into_canonical(net, w), stats))
}

/// Reduce one active pair, handling prim interactions (PrimFun⊗PrimVal,
/// App⊗PrimFun, Rep⊗PrimVal) before falling through to structural R1-R7.
/// Shared by full normalization and demand-driven WHNF forcing.
fn prim_bool(ps: &crate::prim::PrimState, data: u16) -> Option<bool> {
    match ps.vals.get(data as usize) {
        Some(crate::prim::PrimValue::Bool(b)) => Some(*b),
        _ => None,
    }
}

pub(crate) fn step_with_prims<C: CRules>(
    net: &mut Net<Proper, C>,
    prim_state: &mut crate::prim::PrimState,
    pair: ActivePair,
    stats: &mut ReduceStats,
    cfg: &crate::NormalizeConfig,
) -> Result<(), DnxError> {
    use crate::prim::{prim_apply, prim_apply_with_cont, TAG_PRIM_FUN, TAG_PRIM_VAL};

    let s0 = *net.arena.slot(pair.p0.get().slot_idx());
    let s1 = *net.arena.slot(pair.p1.get().slot_idx());

    // Anything ⊗ Free = terminal result wire; not a reducible pair.
    if s0.is_free() || s1.is_free() {
        return Ok(());
    }

    if (s0.tag == TAG_PRIM_FUN && s1.tag == TAG_PRIM_VAL)
        || (s0.tag == TAG_PRIM_VAL && s1.tag == TAG_PRIM_FUN)
    {
        let (p_fun, p_arg) = if s0.tag == TAG_PRIM_FUN {
            (pair.p0.get(), pair.p1.get())
        } else {
            (pair.p1.get(), pair.p0.get())
        };
        if std::env::var("DNX_TRACE_PRIM").is_ok() {
            let av = net.slot_view(p_arg);
            eprintln!(
                "PRIM_APPLY fun_data={} arg_data={} arg_tag{:#04x}",
                net.slot_view(p_fun).data,
                av.data,
                av.tag
            );
        }
        prim_apply(net, prim_state, p_fun, p_arg, &pair.lo)?;
        return Ok(());
    }

    // App ⊗ PrimFun: apply prim to arg from App.aux1, continuation from App.aux0.
    let app_prim = if s0.is_fan() && !s0.fan_is_abs() && s1.tag == TAG_PRIM_FUN {
        Some((pair.p0.get(), pair.p1.get()))
    } else if s1.is_fan() && !s1.fan_is_abs() && s0.tag == TAG_PRIM_FUN {
        Some((pair.p1.get(), pair.p0.get()))
    } else {
        None
    };
    if let Some((p_app, p_pf)) = app_prim {
        let app_sv = net.slot_view(p_app);
        let arg = PortId::from_raw(app_sv.aux1);

        // Determine if arg is ready (PrimVal or recognized Church-bool FanAbs).
        let arg_ready = net.slot_is_live(arg) && {
            let asv = net.slot_view(arg);
            asv.tag == TAG_PRIM_VAL || (asv.is_fan() && asv.fan_is_abs())
        };

        if !arg_ready {
            // Prims are STRICT in their arguments (Nix semantics). Force the arg to
            // WHNF via the App's OWN aux1 port (the consumer side): force_whnf peers
            // once to reach the producer, so a shared DUP/Rep output (a var used
            // twice, `x + x`) reduces its Rep⊗PrimVal producer and delivers the
            // value. Passing the already-peered arg would double-peer back onto this
            // App and walk the wrong way (consumer, not producer).
            let arg_wire = PortId::new(p_app.slot_idx(), PortKind::Aux1, p_app.gen_low());
            crate::reduce::whnf::force_whnf_with_prims(net, prim_state, arg_wire, cfg)?;
        }

        // The strict-arg force runs arbitrary reductions that can retire and REUSE this
        // App's slot (arena bumps the generation on reuse). If so, `p_app` is now a stale
        // handle onto a different agent (e.g. a replicator left by a recursive unfold) and
        // the App⊗PrimFun redex no longer exists — it was consumed by the forcing. An
        // unguarded re-read would mis-read the reused agent's aux as the "argument" and
        // fabricate a spurious `PrimValue::Lambda` from a non-value head, corrupting a
        // downstream `==`. Re-validate (the same staleness gate `is_stale_pair` /
        // `take_spine_redex` / dispatch's post-C-rule use; main.tex:979 — no reduction in
        // a soon-erased subnet). Stale ⇒ the redex is gone, nothing to do.
        //
        // `port_live` (live slot + matching gen-low bit) is NOT sufficient: arena reuse can
        // alias the generation parity back (ABA), so a slot retired+reallocated an even
        // number of times passes `port_live` while now holding a *different agent type*. In
        // the recursion knot (`sum n≥2`) the forcing retires this App and reuses its slot as
        // a FAN_ABS that is wired live into the shared `n` fan-out (its aux1 = the binder
        // facing the demanded value's REP). The old guard let control fall through, then
        // `net.retire(p_app)` below destroyed that live abstraction — severing the recursive
        // `n` so its consumer REP dangled and `==`/`+` saw a fabricated `Lambda`
        // (→ "cannot compare functions"). Require the slot to *still be a FAN_APP* (the type
        // the App⊗PrimFun redex was matched as): any other type ⇒ the redex was consumed by
        // the forcing and the slot now belongs to an unrelated agent we must not touch.
        let p_app_reusable = port_live(p_app, net) && {
            let sv = net.slot_view(p_app);
            sv.is_fan() && !sv.fan_is_abs()
        };
        if !p_app_reusable {
            return Ok(());
        }
        // Re-read: forcing may have replaced the arg's head agent.
        let app_sv = net.slot_view(p_app);
        let arg = PortId::from_raw(app_sv.aux1);
        let cont = PortId::from_raw(app_sv.aux0);
        net.retire(p_app.slot_idx());

        let arg_sv = net.slot_view(arg);
        if arg_sv.tag == TAG_PRIM_VAL {
            prim_apply_with_cont(net, prim_state, p_pf, arg, cont, &pair.lo)?;
        } else {
            // FanAbs arg = opaque lambda (bools are tagged PrimVals now, never
            // Church here). Inspect as Lambda (typeOf/isFunction).
            let tmp = crate::prim::alloc_prim_val(net, prim_state, crate::prim::PrimValue::Lambda)?;
            // Erase the FanAbs (prim consumed it linearly; R2 fires from frontier).
            net.connect(arg, Net::<Proper, C>::eraser_port(), pair.lo.clone())?;
            prim_apply_with_cont(net, prim_state, p_pf, tmp, cont, &pair.lo)?;
        }
        return Ok(());
    }

    // App ⊗ PrimVal::Bool: coerce the tagged bool to its Church-bool net so the
    // enclosing `if`/`&&`/`||`/`!`/`->` (Church-application) branches lazily. Bools
    // are tagged PrimVals for storage/readback/typeOf; they become Church only when
    // applied as a condition.
    let app_bool = if s0.is_fan() && !s0.fan_is_abs() && s1.tag == TAG_PRIM_VAL {
        prim_bool(prim_state, s1.data).map(|b| (pair.p0.get(), pair.p1.get(), b))
    } else if s1.is_fan() && !s1.fan_is_abs() && s0.tag == TAG_PRIM_VAL {
        prim_bool(prim_state, s0.data).map(|b| (pair.p1.get(), pair.p0.get(), b))
    } else {
        None
    };
    if let Some((p_app, p_bool, b)) = app_bool {
        if std::env::var("DNX_TRACE_PRIM").is_ok() {
            eprintln!("COERCE_BOOL {b}");
        }
        net.retire(p_bool.slot_idx());
        let cp = crate::prim::emit_church_bool(net, b)?;
        net.connect(p_app, cp, pair.lo.clone())?;
        return Ok(());
    }

    // Rep ⊗ PrimVal: clone prim val to both rep aux ports.
    let is_rep_pv =
        (s0.is_rep() && s1.tag == TAG_PRIM_VAL) || (s0.tag == TAG_PRIM_VAL && s1.is_rep());
    if is_rep_pv {
        let (p_rep, p_pv) = if s0.is_rep() {
            (pair.p0.get(), pair.p1.get())
        } else {
            (pair.p1.get(), pair.p0.get())
        };
        let pv_sv = net.slot_view(p_pv);
        let pval = prim_state
            .vals
            .get(pv_sv.data as usize)
            .ok_or(DnxError::ReadbackIncomplete)?
            .clone();
        let rep_sv = *net.slot(p_rep);
        let aux0 = PortId::from_raw(rep_sv.aux0);
        let aux1 = PortId::from_raw(rep_sv.aux1);
        net.retire(p_rep.slot_idx());
        net.retire(p_pv.slot_idx());
        let v0 = crate::prim::alloc_prim_val(net, prim_state, pval.clone())?;
        let v1 = crate::prim::alloc_prim_val(net, prim_state, pval)?;
        net.connect(v0, aux0, pair.lo.extend_left()?)?;
        net.connect(v1, aux1, pair.lo.extend_right()?)?;
        return Ok(());
    }

    // Rep ⊗ PrimFun: a shared primitive *function* (e.g. `+` inside a λ used 2×)
    // surfaces when the phase-2 aux-fan-replication cascade lifts the replicator up
    // to the strict consumer. Mirror of Rep ⊗ PrimVal: clone the (immutable) entry
    // to each rep aux port. PrimFun's continuation is its principal wire, so the
    // per-copy connect re-establishes each copy's continuation. Prims orthogonal to
    // R1-R7 (prim.rs:3), so duplication is purely the rep's commute over a prim.
    let is_rep_pf =
        (s0.is_rep() && s1.tag == TAG_PRIM_FUN) || (s0.tag == TAG_PRIM_FUN && s1.is_rep());
    if is_rep_pf {
        let (p_rep, p_pf) = if s0.is_rep() {
            (pair.p0.get(), pair.p1.get())
        } else {
            (pair.p1.get(), pair.p0.get())
        };
        let pf_sv = net.slot_view(p_pf);
        let entry = prim_state
            .funs
            .get(pf_sv.data as usize)
            .ok_or(DnxError::ReadbackIncomplete)?
            .clone();
        let rep_sv = *net.slot(p_rep);
        let aux0 = PortId::from_raw(rep_sv.aux0);
        let aux1 = PortId::from_raw(rep_sv.aux1);
        net.retire(p_rep.slot_idx());
        net.retire(p_pf.slot_idx());
        let f0 = crate::prim::alloc_prim_fun(net, prim_state, entry.clone())?;
        let f1 = crate::prim::alloc_prim_fun(net, prim_state, entry)?;
        net.connect(f0, aux0, pair.lo.extend_left()?)?;
        net.connect(f1, aux1, pair.lo.extend_right()?)?;
        return Ok(());
    }

    dispatch_phase1::<C>(net, pair, stats)
}

/// Run C2-C4 + C1 finalization and certify a drained net into canonical form.
#[allow(private_bounds)]
pub fn finalize_canonical<C: CRules>(
    mut net: Net<Proper, C>,
) -> Result<Net<Canonical, C>, DnxError> {
    while drain_phase2(&mut net)? {}

    if net.net_pending_c1() {
        C::c1(&mut net);
    }

    let w = certify_canonical(&net)?;
    Ok(into_canonical(net, w))
}

/// normalize_with_prims: like normalize but dispatches PrimFun⊗PrimVal pairs.
#[allow(private_bounds)]
pub fn normalize_with_prims<C: CRules>(
    mut net: Net<Proper, C>,
    prim_state: &mut crate::prim::PrimState,
) -> Result<(Net<Canonical, C>, ReduceStats), DnxError> {
    let mut stats = ReduceStats::default();
    let cfg = crate::NormalizeConfig::default();

    while let Some((_, pair)) = net.frontier1.pop_first() {
        if is_stale_pair(&pair, &net) {
            continue;
        }
        stats.interactions += 1;
        step_with_prims::<C>(&mut net, prim_state, pair, &mut stats, &cfg)?;
    }

    let canonical = finalize_canonical(net)?;
    Ok((canonical, stats))
}

/// Demand-driven normalization: prime the root's WHNF spine (so recursion via
/// fix/Y bottoms out under LO demand instead of diverging), then drain the
/// residual and canonicalize. For a fully-forced result (scalar/bool/lambda/
/// finite-strict) the residual is empty; a still-lazy structure keeps a live
/// fix knot and is bounded by cfg fuel (→ StepLimitExceeded), pending deep
/// forcing for list output.
#[allow(private_bounds)]
pub fn normalize_demand<C: CRules>(
    mut net: Net<Proper, C>,
    prim_state: &mut crate::prim::PrimState,
    root: PortId,
    cfg: &crate::NormalizeConfig,
) -> Result<(Net<Canonical, C>, ReduceStats), DnxError> {
    crate::force_whnf_with_prims(&mut net, prim_state, root, cfg)?;

    let mut stats = ReduceStats::default();
    let mut steps = 0u64;
    while let Some((_, pair)) = net.frontier1.pop_first() {
        if is_stale_pair(&pair, &net) {
            continue;
        }
        steps += 1;
        if let Some(max) = cfg.max_steps {
            if steps > max {
                return Err(DnxError::StepLimitExceeded(steps));
            }
        }
        stats.interactions += 1;
        step_with_prims::<C>(&mut net, prim_state, pair, &mut stats, cfg)?;
    }

    let canonical = finalize_canonical(net)?;
    Ok((canonical, stats))
}

pub(crate) fn is_stale_pair<C: NetClassMarker>(pair: &ActivePair, net: &Net<Proper, C>) -> bool {
    !port_live(pair.p0.get(), net) || !port_live(pair.p1.get(), net)
}

pub(crate) fn is_stale_c4<C: NetClassMarker>(cand: &C4Candidate, net: &Net<Proper, C>) -> bool {
    !port_live(cand.rep_principal, net) || !port_live(cand.app_aux0, net)
}

pub(crate) fn port_live<C: NetClassMarker>(p: PortId, net: &Net<Proper, C>) -> bool {
    if p.is_eraser() {
        return true;
    }
    let idx = p.slot_idx();
    // A port whose generation no longer matches its slot refers to a since-retired,
    // reused agent (arena.rs reuse bumps generation): it is NOT live. Without this the
    // staleness gates (is_stale_pair/is_stale_c4) admit ABA-stale pairs/C4-candidates —
    // e.g. a frontier2 candidate whose FAN_APP slot was reused as a FAN_ABS — and the
    // rule then fires on the wrong agent types, producing illegal wires.
    net.arena.is_live(idx) && p.gen_low() == (net.arena.slot(idx).generation & 1) as u8
}

/// Phase-2 canonicalization drain (main.tex:1084-1085): for each frontier2
/// candidate apply C3 decay, C2 merge, then C4 aux-fan-replication, until none
/// remain. This is the second of the two reduction phases — it eliminates the
/// fan-out replicators that core (phase-1) interaction leaves behind. Shared by
/// full normalization (`normalize`, `finalize_canonical`) and demand-driven WHNF
/// (`force_whnf_with_prims` stuck path, which otherwise only runs phase-1).
/// Returns whether any live candidate was processed (→ retry the demand spine).
pub(crate) fn drain_phase2<C: CRules>(net: &mut Net<Proper, C>) -> Result<bool, DnxError> {
    if !C::HAS_REP {
        return Ok(false);
    }
    // ONE candidate per call (main.tex:1091 Ω_S localized to demand): the demand-driven
    // caller (force_whnf_with_prims) re-checks the head after each, so it stops as soon
    // as the demanded value is exposed — never eagerly replicating an off-spine/cyclic
    // replicator (which would unfold a recursive fixpoint without bound). The full-NF
    // callers (`normalize`/`finalize_canonical`) loop this until frontier2 drains.
    let Some((_, cand)) = net.frontier2.pop_first() else {
        return Ok(false);
    };
    if is_stale_c4(&cand, net) {
        return Ok(true);
    }
    if C::HAS_ERA {
        C::c3(net, cand.rep_principal, &cand.lo)?;
        if is_stale_c4(&cand, net) {
            return Ok(true);
        }
    }
    C::c2(net, cand.rep_principal, &cand.lo)?;
    if is_stale_c4(&cand, net) {
        return Ok(true);
    }
    C::c4(net, &cand)?;
    Ok(true)
}

fn dispatch_phase1<C: CRules>(
    net: &mut Net<Proper, C>,
    pair: ActivePair,
    stats: &mut ReduceStats,
) -> Result<(), DnxError> {
    let p0 = pair.p0.get();
    let p1 = pair.p1.get();
    let lo = pair.lo.clone();

    let s0_era = p0.is_eraser();
    let s1_era = p1.is_eraser();

    if s0_era && s1_era {
        // R1: virtual no-op.
        return Ok(());
    }

    if s0_era || s1_era {
        let live_p = if s0_era { p1 } else { p0 };
        let s = *net.arena.slot(live_p.slot_idx());
        if s.is_fan() {
            return r2_era_fan(net, live_p, &lo); // R2
        }
        // R3: Era ⊗ Rep
        if C::HAS_ERA {
            C::c3(net, live_p, &lo)?;
            if !port_live(live_p, net) {
                return Ok(());
            }
        }
        return r3_era_rep(net, live_p, &lo);
    }

    let s0 = *net.arena.slot(p0.slot_idx());
    let s1 = *net.arena.slot(p1.slot_idx());

    match (s0.is_fan(), s0.is_rep(), s1.is_fan(), s1.is_rep()) {
        (true, _, true, _) => {
            // R4: Fan ⊗ Fan (β)
            stats.r4_count += 1;
            r4_fan_fan(net, p0, p1, &lo)
        }
        (true, _, _, true) => {
            // R5: Fan ⊗ Rep (fan=p0, rep=p1)
            if C::HAS_ERA {
                C::c3(net, p1, &lo)?;
                if !port_live(p1, net) {
                    return Ok(());
                }
            }
            if C::HAS_REP {
                C::c2(net, p1, &lo)?;
                if !port_live(p1, net) {
                    return Ok(());
                }
            }
            r5_fan_rep(net, p0, p1, &lo)
        }
        (_, true, true, _) => {
            // R5: Rep ⊗ Fan (rep=p0, fan=p1)
            if C::HAS_ERA {
                C::c3(net, p0, &lo)?;
                if !port_live(p0, net) {
                    return Ok(());
                }
            }
            if C::HAS_REP {
                C::c2(net, p0, &lo)?;
                if !port_live(p0, net) {
                    return Ok(());
                }
            }
            r5_fan_rep(net, p1, p0, &lo)
        }
        (_, true, _, true) => {
            // R6 or R7: Rep ⊗ Rep
            if C::HAS_ERA {
                C::c3(net, p0, &lo)?;
                C::c3(net, p1, &lo)?;
                if !port_live(p0, net) || !port_live(p1, net) {
                    return Ok(());
                }
            }
            if C::HAS_REP {
                C::c2(net, p0, &lo)?;
                C::c2(net, p1, &lo)?;
                if !port_live(p0, net) || !port_live(p1, net) {
                    return Ok(());
                }
            }
            let ss0 = *net.arena.slot(p0.slot_idx());
            let ss1 = *net.arena.slot(p1.slot_idx());
            if std::env::var("DNX_TRACE_RR").is_ok() {
                let kind =
                    if ss0.data == ss1.data && ss0.delta0 == ss1.delta0 && ss0.delta1 == ss1.delta1
                    {
                        "R6"
                    } else {
                        "R7"
                    };
                eprintln!(
                    "{kind} p0(tag{:#04x} lvl{} d{},{} unp{}) p1(tag{:#04x} lvl{} d{},{} unp{}) depth={}",
                    ss0.tag, ss0.data, ss0.delta0, ss0.delta1, ss0.rep_is_unpaired() as u8,
                    ss1.tag, ss1.data, ss1.delta0, ss1.delta1, ss1.rep_is_unpaired() as u8,
                    lo.depth(),
                );
            }
            if std::env::var("DNX_TRACE_AUX").is_ok()
                && (ss0.rep_is_unpaired() || ss1.rep_is_unpaired())
                && !(ss0.data == ss1.data && ss0.delta0 == ss1.delta0 && ss0.delta1 == ss1.delta1)
            {
                let (up, ups) = if ss0.rep_is_unpaired() {
                    (p0, ss0)
                } else {
                    (p1, ss1)
                };
                for (nm, raw) in [("a0", ups.aux0), ("a1", ups.aux1)] {
                    let pp = PortId::from_raw(raw);
                    if pp.is_eraser() {
                        eprintln!("  AUX {nm}: ERA");
                    } else if pp.is_null() {
                        eprintln!("  AUX {nm}: NULL");
                    } else {
                        let ps = *net.arena.slot(pp.slot_idx());
                        eprintln!(
                            "  AUX {nm}: kind{:?} tag{:#04x} lvl{} d{},{} unp{}",
                            pp.port_kind(),
                            ps.tag,
                            ps.data,
                            ps.delta0,
                            ps.delta1,
                            ps.rep_is_unpaired() as u8
                        );
                    }
                }
                let _ = up;
            }
            if ss0.data == ss1.data && ss0.delta0 == ss1.delta0 && ss0.delta1 == ss1.delta1 {
                r6_rep_rep(net, p0, p1, &lo)
            } else {
                r7_rep_rep(net, p0, p1, &lo)
            }
        }
        _ => Err(DnxError::ReadbackIncomplete),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::net::Net;
    use crate::LOPath;

    // λx.x net: abs.aux0 = var, abs.aux1 = var (identity). No active pairs.
    #[test]
    fn normalize_identity_no_interactions() -> Result<(), DnxError> {
        let mut n = Net::<Proper, ΔL>::new(8);
        let abs = n.alloc_abs()?;
        let var = n.alloc_free(0)?;
        // abs.aux0 (var port) ↔ var.principal, abs.aux1 (body) ↔ var.aux0
        // These are non-principal/principal connections → no active pair.
        n.connect(abs.aux0, var, LOPath::root())?;
        n.connect(abs.aux1, var, LOPath::root())?;
        n.add_root("r".into(), abs.principal);
        let (_, stats) = normalize(n)?;
        assert_eq!(stats.interactions, 0);
        assert_eq!(stats.r4_count, 0);
        Ok(())
    }
}
