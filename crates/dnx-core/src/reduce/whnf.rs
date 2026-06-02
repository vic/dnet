/// Demand-driven WHNF forcing — reducer.md §Demand-Driven WHNF Forcing (SETTLED).
///
/// force_whnf drains frontier1 (R1-R7) in LO order until the head agent at `port`
/// is a value-head (FanAbs | PrimVal | PrimFun). Phase2/C4 NOT run — WHNF does not
/// require canonical form. Off-spine subnets are never touched (lazy / call-by-need).
///
/// Paper alignment (main.tex §4):
///   LO = normal order → reaches WHNF iff a WHNF exists (head normalization).
///   Perfect confluence (§2) → WHNF is unique regardless of order.
///   Optimality (§4) → no redex fired that WHNF does not need.
use super::{dispatch_phase1, drain_phase2, is_stale_pair, step_with_prims, CRules, ReduceStats};
use crate::net::{ActivePair, Net};
use crate::prim::PrimState;
use crate::{DnxError, PortId, PortKind, Proper};

/// Result of WHNF forcing at a given port.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueHead {
    /// Head is FanAbs (lambda) — Church-bools, data constructors, etc.
    Abs,
    /// Head is PrimVal or PrimFun (opaque primitive; frontend classifies further).
    Prim,
    /// Head-normal but not a value: free variable or neutral application.
    /// Carries the head-agent's principal PortId.
    Stuck(PortId),
}

/// Fuel config for force_whnf / normalize (driver.md §Divergence Policy).
#[derive(Debug, Clone, Default)]
pub struct NormalizeConfig {
    /// None = unbounded. Some(n) = stop after n rule firings → Err(StepLimitExceeded).
    pub max_steps: Option<u64>,
    /// None = unbounded. Agent count check: Err(ArenaCapacityExceeded) if exceeded.
    pub max_agents: Option<u32>,
}

/// Reduce ONLY the redexes on port's demand spine to WHNF.
///
/// Drains frontier1 in LO order (outermost first) until:
///   - head agent at `port` is a value-head → Ok(ValueHead::Abs | Prim)
///   - frontier1 empty, head not a value → Ok(ValueHead::Stuck)
///   - fuel exhausted → Err(StepLimitExceeded)
///
/// Requires &mut Net<Proper, C>; net stays Net<Proper> (not Net<Canonical>).
/// Phase2 (C4) and C1 are NOT run — lazy WHNF does not need canonical form.
#[allow(private_bounds)]
pub fn force_whnf<C: CRules>(
    net: &mut Net<Proper, C>,
    port: PortId,
    cfg: &NormalizeConfig,
) -> Result<ValueHead, DnxError> {
    let mut steps = 0u64;
    let mut stats = ReduceStats::default();

    loop {
        // Check head agent at current port
        let head = head_at(net, port);
        if let Some(vh) = classify_head(net, head) {
            return Ok(vh);
        }

        // Pop LO-min pair from frontier1
        let pair = loop {
            let Some((_, candidate)) = net.frontier1.pop_first() else {
                // frontier1 empty — head is head-normal but not a value (Stuck)
                return Ok(ValueHead::Stuck(head));
            };
            if !is_stale_pair(&candidate, net) {
                break candidate;
            }
        };

        steps += 1;
        if let Some(max) = cfg.max_steps {
            if steps > max {
                return Err(DnxError::StepLimitExceeded(steps));
            }
        }
        if let Some(max_a) = cfg.max_agents {
            if net.arena.slot_count() as u64 > max_a as u64 {
                return Err(DnxError::ArenaCapacityExceeded);
            }
        }

        dispatch_phase1::<C>(net, pair, &mut stats)?;
    }
}

/// Demand-driven WHNF with prim firing: like force_whnf but routes prim pairs
/// (PrimFun⊗PrimVal, App⊗PrimFun, Rep⊗PrimVal) through step_with_prims. This is
/// the runtime eval driver (nix.md §371) — recursion (fix/Y) terminates because
/// only the demanded head spine is reduced, never the full fixpoint expansion.
#[allow(private_bounds)]
pub fn force_whnf_with_prims<C: CRules>(
    net: &mut Net<Proper, C>,
    prim_state: &mut PrimState,
    port: PortId,
    cfg: &NormalizeConfig,
) -> Result<ValueHead, DnxError> {
    let mut steps = 0u64;
    let mut stats = ReduceStats::default();

    loop {
        let head = head_at(net, port);
        if let Some(vh) = classify_head(net, head) {
            return Ok(vh);
        }

        let Some(pair) = take_spine_redex(net, port) else {
            // Spine blocked: head is FanApp/Rep needing canonicalization, not a value
            // (classify_head returned None). The core (phase-1) interaction rules leave
            // fan-out replicators behind; demand-driven WHNF must replicate NF's phase-2
            // (main.tex:1084-1085, aux-fan-replication) to eliminate the fan-out bubble
            // blocking the demanded value, then retry the spine walk.
            if drain_phase2(net)? {
                continue;
            }
            return Ok(ValueHead::Stuck(head));
        };

        steps += 1;
        if let Some(max) = cfg.max_steps {
            if steps > max {
                return Err(DnxError::StepLimitExceeded(steps));
            }
        }
        if let Some(max_a) = cfg.max_agents {
            if net.arena.slot_count() as u64 > max_a as u64 {
                return Err(DnxError::ArenaCapacityExceeded);
            }
        }

        step_with_prims::<C>(net, prim_state, pair, &mut stats, cfg)?;
    }
}

/// Walk `port`'s demand spine (descend principal ports only — never args/aux1)
/// to the outermost active pair, then remove + return it from frontier1.
/// Returns None if the spine head is a value or stuck (no on-spine redex).
pub(crate) fn take_spine_redex<C: CRules>(
    net: &mut Net<Proper, C>,
    port: PortId,
) -> Option<ActivePair> {
    let mut cur = port;
    let mut lo = crate::LOPath::root();
    let mut guard = 0u32;
    let (pa, pb) = loop {
        guard += 1;
        if guard > 1_000_000 {
            return None;
        }
        let q = net.peer(cur);
        if q.is_null() || q.is_eraser() {
            return None;
        }
        if q.port_kind() == PortKind::Principal {
            // q is a principal; if it faces a free/root slot it's a delivered value,
            // not a redex. (Whether `cur` is itself principal is enforced below by
            // `ActivePair::new` — an aux `cur`, e.g. a demanded App.aux1 facing a
            // fan-out replicator, yields `None` so the caller runs phase-2 instead.)
            if net.arena.slot(q.slot_idx()).is_free() {
                return None;
            }
            if net.arena.slot(cur.slot_idx()).is_free() {
                return None;
            }
            break (cur, q);
        }
        // q is an aux of its agent → that agent produces its value by reducing its
        // own principal interaction; descend there. Track the LO path (aux0 = left,
        // aux1 = right) so a cache-missed redex can still be fired with a path.
        lo = match q.port_kind() {
            PortKind::Aux0 => lo.extend_left().ok()?,
            _ => lo.extend_right().ok()?,
        };
        cur = PortId::new(q.slot_idx(), PortKind::Principal, q.gen_low());
    };

    // A reducible active pair connects opposite polarities — a child principal facing
    // a parent principal (main.tex:951). Two same-polarity principals (e.g. a fan-out
    // REP_OUT⊗REP_OUT left by an incomplete canonicalization) is NOT a valid redex; do
    // not fire it. Prim pairs carry no polarity → allowed. Correct by construction:
    // the demand walker only ever drives genuine child↔parent redexes.
    if let (Some(pol_a), Some(pol_b)) = (
        net.arena.slot(pa.slot_idx()).polarity(pa.port_kind()),
        net.arena.slot(pb.slot_idx()).polarity(pb.port_kind()),
    ) {
        if pol_a == pol_b {
            return None;
        }
    }

    // Wire topology is the source of truth: the LO active pair is the two principals
    // at the top of the spine (main.tex:1075-1076). frontier1 is only a cache —
    // retire() never prunes it (→ stale entries) and a rewire can leave a live pair
    // unregistered (→ miss). The walk above already proved (pa, pb) are two live,
    // non-free principals = a genuine LO redex, so fire it: reuse the cache's stored
    // LO key when it still holds this exact pair live (the built, absolute path),
    // otherwise fire straight from the wires with the reconstructed path.
    let cached = net
        .frontier1
        .iter()
        .find(|(_, ap)| {
            (ap.p0.get() == pa && ap.p1.get() == pb) || (ap.p0.get() == pb && ap.p1.get() == pa)
        })
        .map(|(k, _)| k.clone());
    if let Some(key) = cached {
        if let Some(pair) = net.frontier1.remove(&key) {
            if !is_stale_pair(&pair, net) {
                return Some(pair);
            }
        }
    }
    ActivePair::new(pa, pb, lo)
}

/// Follow the wire from `port` to find the current head-agent's principal PortId.
/// port = principal port of a Free/root slot; returns the other end of its wire.
pub(crate) fn head_at<C: CRules>(net: &Net<Proper, C>, port: PortId) -> PortId {
    if port.is_eraser() || port.is_null() {
        return port;
    }
    let s = net.arena.slot(port.slot_idx());
    let raw = match port.port_kind() {
        PortKind::Principal => s.principal,
        PortKind::Aux0 => s.aux0,
        PortKind::Aux1 => s.aux1,
    };
    PortId::from_raw(raw)
}

/// Classify a head-agent PortId. Returns Some if it is a value-head; None if still reducible.
pub(crate) fn classify_head<C: CRules>(net: &Net<Proper, C>, head: PortId) -> Option<ValueHead> {
    if head.is_eraser() || head.is_null() {
        // ERA or NULL at head = stuck (should not occur in well-typed programs at root)
        return Some(ValueHead::Stuck(head));
    }
    let s = net.arena.slot(head.slot_idx());
    if s.is_fan() && s.fan_is_abs() {
        return Some(ValueHead::Abs);
    }
    if s.is_prim() {
        return Some(ValueHead::Prim);
    }
    // Free slot, App, Rep, or other — not a value head yet
    if s.is_free() {
        // Open term: free variable at head
        return Some(ValueHead::Stuck(head));
    }
    None // FanApp or Rep — still reducible (or needs C4 for canonical form)
}
