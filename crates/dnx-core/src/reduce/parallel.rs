/// True rayon parallel normalize — cpu.md WorkerOutput pattern.
///
/// Antichain guarantee (main.tex §4): every frontier1 pair is prefix-independent.
/// Independent pairs have disjoint write sets → fire simultaneously, zero sync.
/// Perfect confluence (§2): any firing order → same Net<Canonical>.
///
/// Architecture:
///   Coordinator owns Net exclusively. Workers get &Arena (read-only) + &mut WorkerOutput[i].
///   Workers read existing slots, record all mutations into WorkerOutput.
///   Coordinator commits outputs: retire old slots, commit new slots, apply rewiring, insert pairs.
///   C2/C3/C4/C1 remain on coordinator (non-local, quiescent required).
use super::canon::c2_gate_and_shift;
use super::CRules;
use crate::net::{certify_canonical, into_canonical, ActivePair, Net};
use crate::reduce::ReduceStats;
use crate::slot::{Slot, TAG_FAN_ABS, TAG_FAN_APP, TAG_REP_IN_UNKNOWN, TAG_REP_OUT_UNKNOWN};
use crate::{Canonical, DnxError, LOPath, PortId, PortKind, Proper};
use rayon::prelude::*;

// Each rule produces at most 4 new agents (R5: 2 fans + 2 reps; R7: 4 reps).
const MAX_NEW: usize = 4;

/// Mutations produced by firing one rule, without touching &mut Net.
pub(crate) struct WorkerOutput {
    /// Data for pre-reserved slots [base, base+new_agents.len()).
    pub new_agents: Vec<Slot>,
    /// Indices of consumed slots to retire.
    pub retired: Vec<u32>,
    /// Slot-level field mutations for C2/C3 (modifies existing rep neighbors).
    pub slot_muts: Vec<(u32, Slot)>,
    /// Connections coordinator calls connect(a, b, lo) for.
    pub connects: Vec<(PortId, PortId, LOPath)>,
    /// Ports coordinator calls set_eraser_on_port for (ERA propagation).
    pub set_erasers: Vec<PortId>,
    /// Direct link without pair detection (R4 identity self-loop).
    pub link_direct: Option<(PortId, PortId)>,
}

impl WorkerOutput {
    fn new() -> Self {
        WorkerOutput {
            new_agents: Vec::with_capacity(MAX_NEW),
            retired: Vec::with_capacity(2),
            slot_muts: Vec::with_capacity(2),
            connects: Vec::with_capacity(8),
            set_erasers: Vec::with_capacity(4),
            link_direct: None,
        }
    }

    /// Allocate a new agent slot at pre-reserved index (base + current count).
    fn alloc(
        &mut self,
        base: u32,
        tag: u8,
        data: u16,
        delta0: i16,
        delta1: i16,
    ) -> (PortId, PortId, PortId) {
        let idx = base + self.new_agents.len() as u32;
        let mut s = Slot::EMPTY;
        s.tag = tag;
        s.data = data;
        s.delta0 = delta0;
        s.delta1 = delta1;
        self.new_agents.push(s);
        (
            PortId::new(idx, PortKind::Principal, 0),
            PortId::new(idx, PortKind::Aux0, 0),
            PortId::new(idx, PortKind::Aux1, 0),
        )
    }

    fn retire(&mut self, idx: u32) {
        self.retired.push(idx);
    }
    fn connect(&mut self, a: PortId, b: PortId, lo: LOPath) {
        self.connects.push((a, b, lo));
    }
    fn era(&mut self, p: PortId) {
        self.set_erasers.push(p);
    }
}

fn apply_output<C: CRules>(
    net: &mut Net<Proper, C>,
    out: WorkerOutput,
    base: u32,
) -> Result<(), DnxError> {
    // 1. Commit new agent slots.
    for (j, slot) in out.new_agents.into_iter().enumerate() {
        net.arena.commit_slot(base + j as u32, slot);
    }
    // 2. Apply existing slot mutations (C2/C3 rep field updates).
    for (idx, slot) in out.slot_muts {
        *net.arena.slot_mut(idx) = slot;
    }
    // 3. Apply eraser propagation.
    for p in out.set_erasers {
        net.set_eraser_on_port(p);
    }
    // 4. Apply direct link (no pair detection).
    if let Some((a, b)) = out.link_direct {
        net.link_no_pair(a, b);
    }
    // 5. Apply connections (wires + pair detection → frontier1/frontier2).
    for (a, b, lo) in out.connects {
        net.connect(a, b, lo)?;
    }
    // 6. Retire consumed slots.
    for idx in out.retired {
        net.retire(idx);
    }
    Ok(())
}

/// True rayon parallel normalize (main.tex §2 perfect confluence + §4 optimality).
///
/// Phase1: drain entire frontier1 (antichain) → parallel batch.
///   Workers fire R1-R7 read-only, record mutations into WorkerOutput[i].
///   Coordinator applies all outputs sequentially (no mutex during workers).
/// C2/C3: run on coordinator before each batch (lazy pre-checks on reps).
/// Phase2 (C4) + C1: always on coordinator (non-local, quiescent).
pub fn normalize_parallel<C: CRules>(
    mut net: Net<Proper, C>,
    num_threads: usize,
) -> Result<(Net<Canonical, C>, ReduceStats), DnxError> {
    let mut stats = ReduceStats::default();

    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(num_threads)
        .build()
        .map_err(|_| DnxError::ArenaCapacityExceeded)?; // reuse existing error

    // Phase1: parallel batches until frontier1 empty.
    // C2/C3 inlined into workers (antichain → rep slots exclusive per pair).
    loop {
        // Drain entire frontier1 (antichain → safe to fire all in parallel).
        let batch: Vec<ActivePair> = std::mem::take(&mut net.frontier1).into_values().collect();
        if batch.is_empty() {
            break;
        }

        // Pre-reserve output slots for all pairs (coordinator, sequential, before dispatch).
        let bases: Vec<u32> = (0..batch.len())
            .map(|_| net.arena.reserve(MAX_NEW as u32))
            .collect::<Result<_, _>>()?;

        // Parallel: workers read &arena (shared), write only to own WorkerOutput.
        let arena_ref = &net.arena;
        let outputs: Vec<Result<WorkerOutput, DnxError>> = pool.install(|| {
            batch
                .par_iter()
                .zip(bases.par_iter())
                .map(|(pair, &base)| {
                    // Staleness check (arena read-only).
                    let p0_live =
                        pair.p0.get().is_eraser() || arena_ref.is_live(pair.p0.get().slot_idx());
                    let p1_live =
                        pair.p1.get().is_eraser() || arena_ref.is_live(pair.p1.get().slot_idx());
                    if !p0_live || !p1_live {
                        return Ok(WorkerOutput::new());
                    }
                    let mut out = WorkerOutput::new();
                    fire_rule_parallel_arena::<C>(arena_ref, pair, base, &mut out)?;
                    Ok(out)
                })
                .collect()
        });

        // Coordinator: apply outputs sequentially.
        for (i, res) in outputs.into_iter().enumerate() {
            let out = res?;
            let used = out.new_agents.len() as u32;
            let base = bases[i];
            let max = MAX_NEW as u32;
            // R4 (β): 2 retirements, no new agents, no erasers, 2 connects XOR link_direct.
            let is_r4 = out.new_agents.is_empty()
                && out.set_erasers.is_empty()
                && out.retired.len() == 2
                && ((out.connects.len() == 2 && out.link_direct.is_none())
                    || (out.connects.is_empty() && out.link_direct.is_some()));
            if is_r4 {
                stats.r4_count += 1;
            }
            if !out.retired.is_empty() || !out.connects.is_empty() || out.link_direct.is_some() {
                stats.interactions += 1;
            }
            apply_output(&mut net, out, base)?;
            // Release unused reserved slots.
            net.arena.release_reserved(base, used, max);
        }
    }

    // Phase2: C4 — coordinator only (non-local, quiescent).
    if C::HAS_REP {
        while let Some((_, cand)) = net.frontier2.pop_first() {
            if !crate::reduce::is_stale_c4(&cand, &net) {
                if C::HAS_ERA {
                    C::c3(&mut net, cand.rep_principal, &cand.lo)?;
                }
                if !crate::reduce::is_stale_c4(&cand, &net) {
                    C::c2(&mut net, cand.rep_principal, &cand.lo)?;
                }
                if !crate::reduce::is_stale_c4(&cand, &net) {
                    C::c4(&mut net, &cand)?;
                }
            }
        }
    }

    // C1: coordinator only.
    if net.net_pending_c1() {
        C::c1(&mut net);
    }

    let w = certify_canonical(&net)?;
    Ok((into_canonical(net, w), stats))
}

fn add_level(level: u16, delta: i16) -> Result<u16, DnxError> {
    let v = i32::from(level) + i32::from(delta);
    if (0..16384).contains(&v) {
        Ok(v as u16)
    } else {
        Err(DnxError::DeltaOverflow)
    }
}

/// Port live from worker perspective: arena-live AND not locally retired this batch.
fn local_live(arena: &crate::arena::Arena, out: &WorkerOutput, p: PortId) -> bool {
    p.is_eraser() || (arena.is_live(p.slot_idx()) && !out.retired.contains(&p.slot_idx()))
}

/// C3 (rep decay) inlined for workers — records into WorkerOutput, no &mut Net needed.
/// Mirrors c3_rep_decay from canon.rs. Only meaningful for ΔK (HAS_ERA).
fn c3_par(
    arena: &crate::arena::Arena,
    rep_p: PortId,
    lo: &LOPath,
    out: &mut WorkerOutput,
) -> Result<(), DnxError> {
    if !local_live(arena, out, rep_p) {
        return Ok(());
    }
    let rep = *arena.slot(rep_p.slot_idx());
    if !rep.rep_is_unpaired() {
        return Ok(());
    }
    let ext = PortId::from_raw(rep.principal);
    match (rep.rep_aux0_erased(), rep.rep_aux1_erased()) {
        (true, true) => {
            out.era(ext);
            out.retire(rep_p.slot_idx());
            out.connect(PortId::ERA, ext, lo.clone());
        }
        (true, false) if rep.delta1 == 0 => {
            let a1p = PortId::from_raw(rep.aux1);
            out.retire(rep_p.slot_idx());
            out.connect(ext, a1p, lo.clone());
        }
        (false, true) if rep.delta0 == 0 => {
            let a0p = PortId::from_raw(rep.aux0);
            out.retire(rep_p.slot_idx());
            out.connect(ext, a0p, lo.clone());
        }
        _ => {}
    }
    Ok(())
}

/// C2 (rep merge) inlined for workers — reads rep_a + neighbor rep_b, records mutation.
/// Mirrors c2_rep_merge from canon.rs. Only meaningful for ΔI/ΔK (HAS_REP).
fn c2_par(
    arena: &crate::arena::Arena,
    rep_a: PortId,
    lo: &LOPath,
    out: &mut WorkerOutput,
) -> Result<(), DnxError> {
    if !local_live(arena, out, rep_a) {
        return Ok(());
    }
    let a = *arena.slot(rep_a.slot_idx());
    if let Some(m) = c2_gate_and_shift(&a, |p| *arena.slot(p.slot_idx()))? {
        out.slot_muts.push((m.rep_b.slot_idx(), m.b_shifted));
        out.retire(rep_a.slot_idx());
        out.connect(m.rep_b, m.ext, lo.clone());
    }
    Ok(())
}

/// fire_rule variant taking &Arena directly (for rayon workers).
/// C2/C3 inlined (worker-local): antichain guarantees rep slots are exclusive per pair.
fn fire_rule_parallel_arena<C: CRules>(
    arena: &crate::arena::Arena,
    pair: &ActivePair,
    base: u32,
    out: &mut WorkerOutput,
) -> Result<(), DnxError> {
    let p0 = pair.p0.get();
    let p1 = pair.p1.get();
    let lo = &pair.lo;

    let s0_era = p0.is_eraser();
    let s1_era = p1.is_eraser();

    if s0_era && s1_era {
        return Ok(());
    } // R1

    if s0_era || s1_era {
        let live_p = if s0_era { p1 } else { p0 };
        let s = *arena.slot(live_p.slot_idx());
        if s.is_fan() {
            // R2: Era ⊗ Fan
            let ext0 = PortId::from_raw(s.aux0);
            let ext1 = PortId::from_raw(s.aux1);
            out.retire(live_p.slot_idx());
            out.era(ext0);
            out.era(ext1);
            out.connect(PortId::ERA, ext0, lo.extend_left()?);
            out.connect(PortId::ERA, ext1, lo.extend_right()?);
        } else {
            // R3: Era ⊗ Rep — C3 then C2 pre-checks (ΔK/ΔI only).
            if C::HAS_ERA {
                c3_par(arena, live_p, lo, out)?;
            }
            if !local_live(arena, out, live_p) {
                return Ok(());
            }
            if C::HAS_REP {
                c2_par(arena, live_p, lo, out)?;
            }
            if !local_live(arena, out, live_p) {
                return Ok(());
            }
            let s = *arena.slot(live_p.slot_idx());
            let ext0 = PortId::from_raw(s.aux0);
            let ext1 = PortId::from_raw(s.aux1);
            out.retire(live_p.slot_idx());
            out.era(ext0);
            out.era(ext1);
            out.connect(PortId::ERA, ext0, lo.extend_left()?);
            out.connect(PortId::ERA, ext1, lo.extend_right()?);
        }
        return Ok(());
    }

    let s0 = *arena.slot(p0.slot_idx());
    let s1 = *arena.slot(p1.slot_idx());

    match (s0.is_fan(), s1.is_fan(), s0.is_rep(), s1.is_rep()) {
        (true, true, _, _) => {
            // R4
            let (abs_p, app_p) = if s0.fan_is_abs() { (p0, p1) } else { (p1, p0) };
            let abs = *arena.slot(abs_p.slot_idx());
            let app = *arena.slot(app_p.slot_idx());
            let body_peer = PortId::from_raw(abs.aux0);
            let var_peer = PortId::from_raw(abs.aux1);
            let res_peer = PortId::from_raw(app.aux0);
            let arg_peer = PortId::from_raw(app.aux1);
            out.retire(abs_p.slot_idx());
            out.retire(app_p.slot_idx());
            if body_peer.slot_idx() == abs_p.slot_idx() && var_peer.slot_idx() == abs_p.slot_idx() {
                out.link_direct = Some((res_peer, arg_peer));
            } else {
                out.connect(body_peer, res_peer, lo.extend_left()?);
                out.connect(var_peer, arg_peer, lo.extend_right()?);
            }
        }
        (true, _, _, true) => {
            // R5: Fan ⊗ Rep (fan=p0, rep=p1) — C3/C2 on rep first.
            if C::HAS_ERA {
                c3_par(arena, p1, lo, out)?;
            }
            if !local_live(arena, out, p1) {
                return Ok(());
            }
            if C::HAS_REP {
                c2_par(arena, p1, lo, out)?;
            }
            if !local_live(arena, out, p1) {
                return Ok(());
            }
            r5_arena(arena, p0, p1, lo, base, out)?;
        }
        (_, true, true, _) => {
            // R5: Rep ⊗ Fan (rep=p0, fan=p1) — C3/C2 on rep first.
            if C::HAS_ERA {
                c3_par(arena, p0, lo, out)?;
            }
            if !local_live(arena, out, p0) {
                return Ok(());
            }
            if C::HAS_REP {
                c2_par(arena, p0, lo, out)?;
            }
            if !local_live(arena, out, p0) {
                return Ok(());
            }
            r5_arena(arena, p1, p0, lo, base, out)?;
        }
        (_, _, true, true) => {
            // R6/R7: Rep ⊗ Rep — C3/C2 on both reps first.
            if C::HAS_ERA {
                c3_par(arena, p0, lo, out)?;
                c3_par(arena, p1, lo, out)?;
            }
            if !local_live(arena, out, p0) || !local_live(arena, out, p1) {
                return Ok(());
            }
            if C::HAS_REP {
                c2_par(arena, p0, lo, out)?;
                c2_par(arena, p1, lo, out)?;
            }
            if !local_live(arena, out, p0) || !local_live(arena, out, p1) {
                return Ok(());
            }
            // Re-read slots after possible C2/C3 mutations.
            let ss0 = *arena.slot(p0.slot_idx());
            let ss1 = *arena.slot(p1.slot_idx());
            if ss0.data == ss1.data && ss0.delta0 == ss1.delta0 && ss0.delta1 == ss1.delta1 {
                // R6
                let a0 = PortId::from_raw(ss0.aux0);
                let a1 = PortId::from_raw(ss0.aux1);
                let b0 = PortId::from_raw(ss1.aux0);
                let b1 = PortId::from_raw(ss1.aux1);
                out.retire(p0.slot_idx());
                out.retire(p1.slot_idx());
                out.connect(a0, b0, lo.extend_left()?);
                out.connect(a1, b1, lo.extend_right()?);
            } else {
                // R7
                let (hi_p, hi, _lo_p, low) = if ss0.data > ss1.data {
                    (p0, ss0, p1, ss1)
                } else {
                    (p1, ss1, p0, ss0)
                };
                let hi_tag = hi.tag & 0x0F;
                let lo_tag = low.tag & 0x0F;
                let (hc0p, hc0a0, hc0a1) = out.alloc(
                    base,
                    hi_tag,
                    add_level(hi.data, low.delta0)?,
                    hi.delta0,
                    hi.delta1,
                );
                let (hc1p, hc1a0, hc1a1) = out.alloc(
                    base,
                    hi_tag,
                    add_level(hi.data, low.delta1)?,
                    hi.delta0,
                    hi.delta1,
                );
                let (lc0p, lc0a0, lc0a1) =
                    out.alloc(base, lo_tag, low.data, low.delta0, low.delta1);
                let (lc1p, lc1a0, lc1a1) =
                    out.alloc(base, lo_tag, low.data, low.delta0, low.delta1);
                let hi_a0 = PortId::from_raw(hi.aux0);
                let hi_a1 = PortId::from_raw(hi.aux1);
                let lo_a0 = PortId::from_raw(low.aux0);
                let lo_a1 = PortId::from_raw(low.aux1);
                let lo_p_idx = if ss0.data > ss1.data { p1 } else { p0 };
                out.retire(hi_p.slot_idx());
                out.retire(lo_p_idx.slot_idx());
                out.connect(hc0a0, lc0a0, lo.clone());
                out.connect(hc0a1, lc1a0, lo.clone());
                out.connect(hc1a0, lc0a1, lo.clone());
                out.connect(hc1a1, lc1a1, lo.clone());
                out.connect(hc0p, lo_a0, lo.extend_left()?.extend_left()?);
                out.connect(hc1p, lo_a1, lo.extend_left()?.extend_right()?);
                out.connect(lc0p, hi_a0, lo.extend_right()?.extend_left()?);
                out.connect(lc1p, hi_a1, lo.extend_right()?.extend_right()?);
            }
        }
        _ => return Err(DnxError::ReadbackIncomplete),
    }
    Ok(())
}

fn r5_arena(
    arena: &crate::arena::Arena,
    fan_p: PortId,
    rep_p: PortId,
    lo: &LOPath,
    base: u32,
    out: &mut WorkerOutput,
) -> Result<(), DnxError> {
    let fan = *arena.slot(fan_p.slot_idx());
    let rep = *arena.slot(rep_p.slot_idx());
    let is_abs = fan.fan_is_abs();
    let fan_tag = if is_abs { TAG_FAN_ABS } else { TAG_FAN_APP };
    let (ra_tag, rb_tag) = if is_abs {
        (TAG_REP_IN_UNKNOWN, TAG_REP_OUT_UNKNOWN)
    } else {
        (TAG_REP_OUT_UNKNOWN, TAG_REP_IN_UNKNOWN)
    };
    let (f0p, f0a0, f0a1) = out.alloc(base, fan_tag, 0, 0, 0);
    let (f1p, f1a0, f1a1) = out.alloc(base, fan_tag, 0, 0, 0);
    let (rap, raa0, raa1) = out.alloc(base, ra_tag, rep.data, rep.delta0, rep.delta1);
    let (rbp, rba0, rba1) = out.alloc(base, rb_tag, rep.data, rep.delta0, rep.delta1);
    let ext_a = PortId::from_raw(fan.aux0);
    let ext_b = PortId::from_raw(fan.aux1);
    let ext_c = PortId::from_raw(rep.aux0);
    let ext_d = PortId::from_raw(rep.aux1);
    out.retire(fan_p.slot_idx());
    out.retire(rep_p.slot_idx());
    let lo_00 = lo.extend_left()?.extend_left()?;
    let lo_01 = lo.extend_left()?.extend_right()?;
    let (ra_lo, rb_lo) = if is_abs {
        (
            lo.extend_right()?.extend_left()?,
            lo.extend_right()?.extend_right()?,
        )
    } else {
        (
            lo.extend_right()?.extend_right()?,
            lo.extend_right()?.extend_left()?,
        )
    };
    out.connect(f0a0, raa0, lo.clone());
    out.connect(f0a1, rba0, lo.clone());
    out.connect(f1a0, raa1, lo.clone());
    out.connect(f1a1, rba1, lo.clone());
    out.connect(f0p, ext_c, lo_00);
    out.connect(f1p, ext_d, lo_01);
    out.connect(rap, ext_a, ra_lo);
    out.connect(rbp, ext_b, rb_lo);
    Ok(())
}
