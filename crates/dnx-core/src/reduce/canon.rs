use crate::class::{IsEraNet, IsRepNet, Proper};
use crate::net::{C4Candidate, Net};
use crate::slot::{Slot, TAG_C1_MARK, TAG_FAN_APP, TAG_REP_IN_UNKNOWN};
use crate::{DnxError, LOPath, PortId, PortKind};
use std::collections::VecDeque;

/// Resolved C2 merge: the neighbor rep to fold into, the unpaired rep's external
/// port, and the neighbor's slot after the level/delta shift.
pub(crate) struct C2Merge {
    pub rep_b: PortId,
    pub ext: PortId,
    pub b_shifted: Slot,
}

/// C2 canonicalization gate + rep-label shift (main.tex L1069). Single source of
/// truth shared by sequential `c2_rep_merge` and parallel `c2_par`: scans `a`'s two
/// aux ports for an erased side whose neighbor (fetched via `fetch`) is a rep meeting
/// the merge constraint \(0 \le l_B - l_A \le d\), and returns that neighbor's slot
/// with deltas shifted by the level difference and level set to `a`'s level. `None`
/// when no aux port qualifies. PURE: no mutation, byte-identical math for both callers.
pub(crate) fn c2_gate_and_shift(
    a: &Slot,
    mut fetch: impl FnMut(PortId) -> Slot,
) -> Result<Option<C2Merge>, DnxError> {
    if !a.rep_is_unpaired() {
        return Ok(None);
    }
    for i in 0..2u8 {
        let other_erased = if i == 0 {
            a.rep_aux1_erased()
        } else {
            a.rep_aux0_erased()
        };
        if !other_erased {
            continue;
        }
        let rep_b = PortId::from_raw(if i == 0 { a.aux0 } else { a.aux1 });
        if rep_b.is_eraser() || rep_b.is_null() || rep_b.port_kind() != PortKind::Principal {
            continue;
        }
        let b = fetch(rep_b);
        if !b.is_rep() {
            continue;
        }
        let delta_i = i32::from(if i == 0 { a.delta0 } else { a.delta1 });
        let diff = i32::from(b.data) - i32::from(a.data);
        if diff < 0 || diff > delta_i {
            continue;
        }
        let shift = diff as i16;
        let mut b_shifted = b;
        b_shifted.delta0 = b.delta0.checked_add(shift).ok_or(DnxError::DeltaOverflow)?;
        b_shifted.delta1 = b.delta1.checked_add(shift).ok_or(DnxError::DeltaOverflow)?;
        b_shifted.data = a.data;
        return Ok(Some(C2Merge {
            rep_b,
            ext: PortId::from_raw(a.principal),
            b_shifted,
        }));
    }
    Ok(None)
}

// C2: Unpaired Rep Merge (lazy). Merges an unpaired rep_a (one aux erased, the other
// → rep_b.principal) into rep_b, shifting rep_b's level/deltas. ΔI or ΔK.
pub(crate) fn c2_rep_merge<C: IsRepNet>(
    net: &mut Net<Proper, C>,
    rep_a: PortId,
    lo: &LOPath,
) -> Result<(), DnxError> {
    let a = *net.slot(rep_a);
    if let Some(m) = c2_gate_and_shift(&a, |p| *net.slot(p))? {
        *net.slot_mut(m.rep_b) = m.b_shifted;
        net.retire(rep_a.slot_idx());
        net.connect(m.rep_b, m.ext, lo.clone())?;
    }
    Ok(())
}

// C3: Unpaired Rep Decay (lazy). ΔK (needs both reps and erasers).
pub(crate) fn c3_rep_decay<C: IsRepNet + IsEraNet>(
    net: &mut Net<Proper, C>,
    rep_p: PortId,
    lo: &LOPath,
) -> Result<(), DnxError> {
    let rep = *net.slot(rep_p);
    let ext = PortId::from_raw(rep.principal);
    match (rep.rep_aux0_erased(), rep.rep_aux1_erased()) {
        (true, true) if rep.rep_is_unpaired() => {
            // Case A: both aux erased → eraser propagates up; rep retired. Unpaired
            // only (main.tex:1062 unpaired replicator decay) — erasing a paired rep's
            // content is unsound.
            net.set_eraser_on_port(ext);
            net.retire(rep_p.slot_idx());
            net.connect(PortId::ERA, ext, lo.clone())?;
        }
        (true, false) if rep.delta1 == 0 => {
            // Case B1: one aux erased, the surviving aux has zero level delta → the rep
            // is a single-input/single-output level-0 pass-through = a wire (main.tex:939
            // "regardless of the replicator's level, is equivalent to a wire"). This is a
            // structural identity, sound for ANY pairedness — so it terminates a cyclic
            // fixpoint whose self-feedback aux was erased at the recursion's base case.
            let a1p = PortId::from_raw(rep.aux1);
            net.retire(rep_p.slot_idx());
            net.connect(ext, a1p, lo.clone())?;
        }
        (false, true) if rep.delta0 == 0 => {
            let a0p = PortId::from_raw(rep.aux0);
            net.retire(rep_p.slot_idx());
            net.connect(ext, a0p, lo.clone())?;
        }
        // Case B2 (delta != 0) and Case C (neither erased): no-op.
        _ => {}
    }
    Ok(())
}

// C4: Aux Fan Replication (Phase 2). Rep lifts past an app-fan it meets at app.aux0.
// new_rep (RepIn) + new_arg (RepOut), both Unknown, level=l, deltas=rep (main.tex:
// fan = replicator level0/delta0, so the commute preserves the rep's level+deltas). ΔI or ΔK.
pub(crate) fn c4_aux_fan_replication<C: IsRepNet>(
    net: &mut Net<Proper, C>,
    cand: &C4Candidate,
) -> Result<(), DnxError> {
    let app_aux0 = cand.app_aux0;
    let rep_p = cand.rep_principal;
    let lo = &cand.lo;
    let app = *net.slot(app_aux0);
    let rep = *net.slot(rep_p);

    if PortId::from_raw(app.aux0).is_eraser() {
        // Sub-case A: app.aux0 erased → erase the app fan (its peers are inert aux ports).
        let up = PortId::from_raw(app.principal);
        let arg = PortId::from_raw(app.aux1);
        net.set_eraser_on_port(up);
        net.set_eraser_on_port(arg);
        net.retire(app_aux0.slot_idx());
        net.retire(rep_p.slot_idx());
        net.connect(PortId::ERA, up, lo.extend_left()?)?;
        net.connect(PortId::ERA, arg, lo.extend_right()?)?;
        return Ok(());
    }

    // Sub-case B: full replication (paper Fig.ipsi).
    let ext_up = PortId::from_raw(app.principal);
    let ext_arg = PortId::from_raw(app.aux1);
    let ext_c = PortId::from_raw(rep.aux0);
    let ext_d = PortId::from_raw(rep.aux1);
    let new_rep = net.alloc_agent(TAG_REP_IN_UNKNOWN, rep.data, rep.delta0, rep.delta1)?;
    // The argument is SHARED by the replicated app copies, so it accumulates at a
    // fan-IN (main.tex:1085 "all fan-in replicators accumulate", :951 child↔parent).
    // A fan-OUT here wires parent↔parent (its principal to the arg's parent peer) and
    // child↔child (its child aux to the app copies' child arg ports) — both illegal.
    let new_arg = net.alloc_agent(TAG_REP_IN_UNKNOWN, rep.data, rep.delta0, rep.delta1)?;
    let app0 = net.alloc_agent(TAG_FAN_APP, 0, 0, 0)?;
    let app1 = net.alloc_agent(TAG_FAN_APP, 0, 0, 0)?;
    net.retire(app_aux0.slot_idx());
    net.retire(rep_p.slot_idx());

    net.connect(new_rep.aux0, app0.principal, lo.clone())?;
    net.connect(new_rep.aux1, app1.principal, lo.clone())?;
    net.connect(app0.aux1, new_arg.aux0, lo.clone())?;
    net.connect(app1.aux1, new_arg.aux1, lo.clone())?;
    net.connect(app0.aux0, ext_c, lo.extend_left()?.extend_left()?)?;
    net.connect(app1.aux0, ext_d, lo.extend_left()?.extend_right()?)?;
    net.connect(new_rep.principal, ext_up, lo.extend_right()?.extend_left()?)?;
    net.connect(
        new_arg.principal,
        ext_arg,
        lo.extend_right()?.extend_right()?,
    )?;
    Ok(())
}

// C1: Erasure Canonicalization (sequential, final). BFS-mark reachable from roots
// (free_slots), retire the unmarked, clear marks. ΔA or ΔK.
pub(crate) fn c1_mark_sweep<C: IsEraNet>(net: &mut Net<Proper, C>) {
    let mut queue: VecDeque<u32> = VecDeque::new();
    let roots: Vec<u32> = net.free_slots.values().map(|p| p.slot_idx()).collect();
    for idx in roots {
        if idx != 0 && !net.arena.slot(idx).is_c1_marked() {
            net.arena.slot_mut(idx).tag |= TAG_C1_MARK;
            queue.push_back(idx);
        }
    }
    while let Some(idx) = queue.pop_front() {
        let s = *net.arena.slot(idx);
        for raw in [s.principal, s.aux0, s.aux1] {
            let nidx = PortId::from_raw(raw).slot_idx();
            if nidx != 0 && !net.arena.slot(nidx).is_c1_marked() {
                net.arena.slot_mut(nidx).tag |= TAG_C1_MARK;
                queue.push_back(nidx);
            }
        }
    }
    for idx in net.arena.live().to_vec() {
        if net.arena.slot(idx).is_c1_marked() {
            net.arena.slot_mut(idx).tag &= !TAG_C1_MARK;
        } else {
            net.arena.retire_slot(idx);
        }
    }
    net.clear_pending_c1();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::class::{ΔA, ΔI, ΔK};

    #[test]
    fn c1_retires_unreachable() -> Result<(), DnxError> {
        let mut n = Net::<Proper, ΔA>::new(16);
        let root = n.alloc_free(0)?;
        let abs = n.alloc_abs()?;
        let _orphan = n.alloc_app()?;
        n.connect(root, abs.principal, LOPath::root())?;
        n.add_root("r".into(), root);
        let live0 = n.arena.live().len();
        c1_mark_sweep(&mut n);
        assert_eq!(n.arena.live().len(), live0 - 1);
        Ok(())
    }

    #[test]
    fn c2_merges_unpaired_rep_shifting_level() -> Result<(), DnxError> {
        let mut n = Net::<Proper, ΔI>::new(16);
        let a = n.alloc_rep_in(1, 5, 0)?;
        let b = n.alloc_rep_in(3, 0, 0)?;
        let parent = n.alloc_free(0)?;
        let bc = n.alloc_free(1)?;
        let bd = n.alloc_free(2)?;
        n.connect(a.principal, parent, LOPath::root())?;
        n.connect(a.aux0, b.principal, LOPath::root())?;
        n.set_eraser_on_port(a.aux1);
        n.connect(b.aux0, bc, LOPath::root())?;
        n.connect(b.aux1, bd, LOPath::root())?;
        let live0 = n.arena.live().len();
        c2_rep_merge(&mut n, a.principal, &LOPath::root())?;
        assert_eq!(n.arena.live().len(), live0 - 1);
        let bs = *n.slot(b.principal);
        assert_eq!((bs.data, bs.delta0, bs.delta1), (1, 2, 2)); // level←1, deltas += diff(2)
        Ok(())
    }

    #[test]
    fn c3_decay_case_a_erases_up() -> Result<(), DnxError> {
        let mut n = Net::<Proper, ΔK>::new(16);
        let rep = n.alloc_rep_in(1, 0, 0)?;
        let parent = n.alloc_free(0)?;
        n.connect(rep.principal, parent, LOPath::root())?;
        n.set_eraser_on_port(rep.aux0);
        n.set_eraser_on_port(rep.aux1);
        let live0 = n.arena.live().len();
        c3_rep_decay(&mut n, rep.principal, &LOPath::root())?;
        assert_eq!(n.arena.live().len(), live0 - 1);
        assert_eq!(n.slot(parent).principal, PortId::ERA.raw());
        Ok(())
    }

    #[test]
    fn c4_subb_replicates_preserving_level() -> Result<(), DnxError> {
        let mut n = Net::<Proper, ΔI>::new(32);
        let rep = n.alloc_rep_in(2, 0, 0)?;
        let app = n.alloc_app()?;
        let up = n.alloc_free(0)?;
        let arg = n.alloc_free(1)?;
        let c = n.alloc_free(2)?;
        let d = n.alloc_free(3)?;
        n.connect(app.principal, up, LOPath::root())?;
        n.connect(app.aux1, arg, LOPath::root())?;
        n.connect(rep.aux0, c, LOPath::root())?;
        n.connect(rep.aux1, d, LOPath::root())?;
        n.connect(rep.principal, app.aux0, LOPath::root())?; // C4 trigger → frontier2
        let cand = n.frontier2.values().next().cloned();
        let cand = match cand {
            Some(cand) => cand,
            None => return Err(DnxError::ReadbackIncomplete),
        };
        n.frontier1.clear();
        n.frontier2.clear();
        let live0 = n.arena.live().len();
        c4_aux_fan_replication(&mut n, &cand)?;
        assert_eq!(n.arena.live().len(), live0 + 2); // -2 (app,rep) +4
                                                     // boundary pairs: new_rep↔up, new_arg↔arg (c/d go to app aux0 = wire only).
        assert_eq!(n.frontier1.len(), 2);
        let mut levels: Vec<u16> = n
            .frontier1
            .values()
            .map(|p| n.slot(p.p0.get()).data)
            .collect();
        levels.sort_unstable();
        assert_eq!(levels, vec![2, 2]); // both new reps keep rep's level
        Ok(())
    }

    // ── C2 paper oracle: merge gate 0 ≤ l_B − l_A ≤ d (main.tex L1069) ──

    // rep_a (level la, delta0 da0) UNPAIRED, aux1 erased, aux0 → rep_b (level lb).
    fn c2_setup(
        la: u16,
        da0: i16,
        lb: u16,
    ) -> Result<(Net<Proper, ΔI>, PortId, PortId), DnxError> {
        let mut n = Net::<Proper, ΔI>::new(16);
        let a = n.alloc_rep_in(la, da0, 0)?;
        let b = n.alloc_rep_in(lb, 0, 0)?;
        let parent = n.alloc_free(0)?;
        let bc = n.alloc_free(1)?;
        let bd = n.alloc_free(2)?;
        n.connect(a.principal, parent, LOPath::root())?;
        n.connect(a.aux0, b.principal, LOPath::root())?;
        n.set_eraser_on_port(a.aux1);
        n.connect(b.aux0, bc, LOPath::root())?;
        n.connect(b.aux1, bd, LOPath::root())?;
        Ok((n, a.principal, b.principal))
    }

    #[test]
    fn c2_merge_gate_boundaries() -> Result<(), DnxError> {
        // diff = l_B − l_A ; merge iff 0 ≤ diff ≤ delta0.
        for (la, da0, lb, want_merge) in [
            (1u16, 5i16, 1u16, true), // diff 0 — lower bound
            (1, 5, 6, true),          // diff 5 = delta0 — upper bound
            (1, 5, 7, false),         // diff 6 > delta0 — skip
            (3, 5, 1, false),         // diff -2 < 0 — skip
        ] {
            let (mut n, ap, _) = c2_setup(la, da0, lb)?;
            let live0 = n.arena.live().len();
            c2_rep_merge(&mut n, ap, &LOPath::root())?;
            assert_eq!(
                n.arena.live().len() == live0 - 1,
                want_merge,
                "la={la} da0={da0} lb={lb}"
            );
        }
        Ok(())
    }

    #[test]
    fn c2_merged_level_delta_invariant() -> Result<(), DnxError> {
        // Merge takes rep_a's level; rep_b deltas shift by diff so absolute target
        // levels are preserved: l_A + delta_new == l_B + delta_old.
        let (mut n, ap, bp) = c2_setup(1, 5, 4)?; // diff = 3 ≤ 5 → merge
        c2_rep_merge(&mut n, ap, &LOPath::root())?;
        let b = *n.slot(bp);
        assert_eq!((b.data, b.delta0, b.delta1), (1, 3, 3));
        assert_eq!(i32::from(b.data) + i32::from(b.delta0), 4); // == l_B + old delta0(0)
        Ok(())
    }

    #[test]
    fn c3_decay_wire_through_iff_zero_delta() -> Result<(), DnxError> {
        // main.tex L1063: unpaired rep left with a single aux of level-delta 0 → wire.
        // aux0 erased, aux1 survives → wire-through (retire rep) iff delta1 == 0.
        for (delta1, want_retire) in [(0i16, true), (2i16, false)] {
            let mut n = Net::<Proper, ΔK>::new(16);
            let rep = n.alloc_rep_in(1, 0, delta1)?;
            let parent = n.alloc_free(0)?;
            let survivor = n.alloc_free(1)?;
            n.connect(rep.principal, parent, LOPath::root())?;
            n.set_eraser_on_port(rep.aux0);
            n.connect(rep.aux1, survivor, LOPath::root())?;
            let live0 = n.arena.live().len();
            c3_rep_decay(&mut n, rep.principal, &LOPath::root())?;
            assert_eq!(
                n.arena.live().len() == live0 - 1,
                want_retire,
                "delta1={delta1}"
            );
        }
        Ok(())
    }

    #[test]
    fn c4_subb_preserves_deltas_and_lopaths() -> Result<(), DnxError> {
        // C4 aux fan replication (main.tex fig:ipsi): new reps keep rep's level AND
        // deltas; boundary pairs at lo ++ 0b10 (up) and lo ++ 0b11 (arg).
        let mut n = Net::<Proper, ΔI>::new(32);
        let rep = n.alloc_rep_in(2, -3, 4)?;
        let app = n.alloc_app()?;
        let (up, arg, c, d) = (
            n.alloc_free(0)?,
            n.alloc_free(1)?,
            n.alloc_free(2)?,
            n.alloc_free(3)?,
        );
        let root = LOPath::root();
        n.connect(app.principal, up, root.clone())?;
        n.connect(app.aux1, arg, root.clone())?;
        n.connect(rep.aux0, c, root.clone())?;
        n.connect(rep.aux1, d, root.clone())?;
        n.connect(rep.principal, app.aux0, root.clone())?;
        let cand = match n.frontier2.values().next().cloned() {
            Some(c) => c,
            None => return Err(DnxError::ReadbackIncomplete),
        };
        n.frontier1.clear();
        n.frontier2.clear();
        c4_aux_fan_replication(&mut n, &cand)?;
        let up_key = root.extend_right()?.extend_left()?;
        let arg_key = root.extend_right()?.extend_right()?;
        for key in [&up_key, &arg_key] {
            let pr = match n.frontier1.get(key) {
                Some(pr) => pr,
                None => return Err(DnxError::ReadbackIncomplete),
            };
            let s0 = *n.slot(pr.p0.get());
            let s = if s0.is_rep() {
                s0
            } else {
                *n.slot(pr.p1.get())
            };
            assert_eq!(
                (s.data, s.delta0, s.delta1),
                (2, -3, 4),
                "C4 preserves level+deltas"
            );
        }
        Ok(())
    }
}
