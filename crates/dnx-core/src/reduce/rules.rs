use crate::class::{NetClassMarker, Proper};
use crate::net::Net;
use crate::slot::{TAG_FAN_ABS, TAG_FAN_APP, TAG_REP_IN_UNKNOWN, TAG_REP_OUT_UNKNOWN};
use crate::{DnxError, LOPath, PortId};

// R1 (Era ⊗ Era) is a dispatch no-op: both erasers are virtual (no slots).

pub(crate) fn r2_era_fan<C: NetClassMarker>(
    net: &mut Net<Proper, C>,
    fan_p: PortId,
    lo: &LOPath,
) -> Result<(), DnxError> {
    let fan = *net.slot(fan_p);
    let ext0 = PortId::from_raw(fan.aux0);
    let ext1 = PortId::from_raw(fan.aux1);
    net.set_eraser_on_port(ext0);
    net.set_eraser_on_port(ext1);
    net.retire(fan_p.slot_idx());
    net.connect(PortId::ERA, ext0, lo.extend_left()?)?;
    net.connect(PortId::ERA, ext1, lo.extend_right()?)?;
    Ok(())
}

pub(crate) fn r3_era_rep<C: NetClassMarker>(
    net: &mut Net<Proper, C>,
    rep_p: PortId,
    lo: &LOPath,
) -> Result<(), DnxError> {
    let rep = *net.slot(rep_p);
    let ext0 = PortId::from_raw(rep.aux0);
    let ext1 = PortId::from_raw(rep.aux1);
    net.set_eraser_on_port(ext0);
    net.set_eraser_on_port(ext1);
    net.retire(rep_p.slot_idx());
    net.connect(PortId::ERA, ext0, lo.extend_left()?)?;
    net.connect(PortId::ERA, ext1, lo.extend_right()?)?;
    Ok(())
}

pub(crate) fn r4_fan_fan<C: NetClassMarker>(
    net: &mut Net<Proper, C>,
    p0: PortId,
    p1: PortId,
    lo: &LOPath,
) -> Result<(), DnxError> {
    let (abs_p, app_p) = if net.slot(p0).fan_is_abs() {
        (p0, p1)
    } else {
        (p1, p0)
    };
    let abs = *net.slot(abs_p);
    let app = *net.slot(app_p);
    let body_peer = PortId::from_raw(abs.aux0);
    let var_peer = PortId::from_raw(abs.aux1);
    let res_peer = PortId::from_raw(app.aux0);
    let arg_peer = PortId::from_raw(app.aux1);
    net.retire(abs_p.slot_idx());
    net.retire(app_p.slot_idx());
    // Identity self-loop: body and var are both ports of the just-retired abs.
    // Wire result↔arg directly. Use link_no_pair to avoid spurious active pair
    // when result is a root Free slot and arg is a FanAbs principal.
    if body_peer.slot_idx() == abs_p.slot_idx() && var_peer.slot_idx() == abs_p.slot_idx() {
        net.link_no_pair(res_peer, arg_peer);
    } else {
        net.connect(body_peer, res_peer, lo.extend_left()?)?;
        net.connect(var_peer, arg_peer, lo.extend_right()?)?;
    }
    Ok(())
}

pub(crate) fn r5_fan_rep<C: NetClassMarker>(
    net: &mut Net<Proper, C>,
    fan_p: PortId,
    rep_p: PortId,
    lo: &LOPath,
) -> Result<(), DnxError> {
    let fan = *net.slot(fan_p);
    let rep = *net.slot(rep_p);
    let is_abs = fan.fan_is_abs();
    let fan_tag = if is_abs { TAG_FAN_ABS } else { TAG_FAN_APP };
    let ext_a = PortId::from_raw(fan.aux0);
    let ext_b = PortId::from_raw(fan.aux1);
    let ext_c = PortId::from_raw(rep.aux0);
    let ext_d = PortId::from_raw(rep.aux1);
    let f0 = net.alloc_agent(fan_tag, 0, 0, 0)?;
    let f1 = net.alloc_agent(fan_tag, 0, 0, 0)?;
    let lo_00 = lo.extend_left()?.extend_left()?;
    let lo_01 = lo.extend_left()?.extend_right()?;

    // Self-loop fan (e.g. λx.x: aux0↔aux1) → ext_a/ext_b point back into the fan
    // slot. Duplicating a self-loop yields two self-loop fans; the rep copies would
    // only annihilate their dual, so emit the fans directly (no reps). The general
    // path would wire rep copies into the just-retired fan slot, leaving a stale
    // principal pair that wedges the demand spine — the recursion blocker.
    if ext_a.slot_idx() == fan_p.slot_idx() && ext_b.slot_idx() == fan_p.slot_idx() {
        net.retire(fan_p.slot_idx());
        net.retire(rep_p.slot_idx());
        net.connect(f0.aux0, f0.aux1, lo.extend_left()?)?;
        net.connect(f1.aux0, f1.aux1, lo.extend_right()?)?;
        net.connect(f0.principal, ext_c, lo_00)?;
        net.connect(f1.principal, ext_d, lo_01)?;
        return Ok(());
    }

    let (ra_tag, rb_tag) = if is_abs {
        (TAG_REP_IN_UNKNOWN, TAG_REP_OUT_UNKNOWN)
    } else {
        (TAG_REP_OUT_UNKNOWN, TAG_REP_IN_UNKNOWN)
    };
    let ra = net.alloc_agent(ra_tag, rep.data, rep.delta0, rep.delta1)?;
    let rb = net.alloc_agent(rb_tag, rep.data, rep.delta0, rep.delta1)?;
    net.retire(fan_p.slot_idx());
    net.retire(rep_p.slot_idx());

    let lo_10 = lo.extend_right()?.extend_left()?;
    let lo_11 = lo.extend_right()?.extend_right()?;
    // RepIn copy → suffix 0b10, RepOut copy → suffix 0b11.
    let (ra_lo, rb_lo) = if is_abs {
        (lo_10, lo_11)
    } else {
        (lo_11, lo_10)
    };

    net.connect(f0.aux0, ra.aux0, lo.clone())?;
    net.connect(f0.aux1, rb.aux0, lo.clone())?;
    net.connect(f1.aux0, ra.aux1, lo.clone())?;
    net.connect(f1.aux1, rb.aux1, lo.clone())?;
    net.connect(f0.principal, ext_c, lo_00)?;
    net.connect(f1.principal, ext_d, lo_01)?;
    net.connect(ra.principal, ext_a, ra_lo)?;
    net.connect(rb.principal, ext_b, rb_lo)?;
    Ok(())
}

pub(crate) fn r6_rep_rep<C: NetClassMarker>(
    net: &mut Net<Proper, C>,
    p0: PortId,
    p1: PortId,
    lo: &LOPath,
) -> Result<(), DnxError> {
    let a = *net.slot(p0);
    let b = *net.slot(p1);
    debug_assert!(a.data == b.data && a.delta0 == b.delta0 && a.delta1 == b.delta1);
    let a0 = PortId::from_raw(a.aux0);
    let a1 = PortId::from_raw(a.aux1);
    let b0 = PortId::from_raw(b.aux0);
    let b1 = PortId::from_raw(b.aux1);
    net.retire(p0.slot_idx());
    net.retire(p1.slot_idx());
    // R6 cross-wires get distinct suffixes (antichain + frontier-key uniqueness;
    // lopath.md R6 prose "inherit lo unchanged" contradicts its own antichain proof).
    net.connect(a0, b0, lo.extend_left()?)?;
    net.connect(a1, b1, lo.extend_right()?)?;
    Ok(())
}

pub(crate) fn r7_rep_rep<C: NetClassMarker>(
    net: &mut Net<Proper, C>,
    p0: PortId,
    p1: PortId,
    lo: &LOPath,
) -> Result<(), DnxError> {
    let s0 = *net.slot(p0);
    let s1 = *net.slot(p1);
    // hi/lo split is by LEVEL (main.tex:792-793; the rule's precondition is l < k,
    // main.tex:693). For λ-derived nets equal level ⇒ equal agent (main.tex:787) ⇒ R6,
    // never here. But the dispatch gate routes any non-equal triple to R7, so an
    // equal-level/distinct-delta pair (improper per :787, reachable mid-reduction) can
    // arrive. Break ties lexicographically on the full (level, δ0, δ1) signature so the
    // designation is TOTAL and order-independent — required for confluence. The old
    // `debug_assert!(hi.data > low.data)` was unsound (claimed a strict-level invariant
    // the dispatch does not guarantee; panicked on l == k).
    let s0_key = (s0.data, s0.delta0, s0.delta1);
    let s1_key = (s1.data, s1.delta0, s1.delta1);
    let (hi_p, hi, lo_p, low) = if s0_key > s1_key {
        (p0, s0, p1, s1)
    } else {
        (p1, s1, p0, s0)
    };
    let hi_tag = hi.tag & 0x0F;
    let lo_tag = low.tag & 0x0F;
    let hc0 = net.alloc_agent(
        hi_tag,
        add_level(hi.data, low.delta0)?,
        hi.delta0,
        hi.delta1,
    )?;
    let hc1 = net.alloc_agent(
        hi_tag,
        add_level(hi.data, low.delta1)?,
        hi.delta0,
        hi.delta1,
    )?;
    let lc0 = net.alloc_agent(lo_tag, low.data, low.delta0, low.delta1)?;
    let lc1 = net.alloc_agent(lo_tag, low.data, low.delta0, low.delta1)?;

    let hi_a0 = PortId::from_raw(hi.aux0);
    let hi_a1 = PortId::from_raw(hi.aux1);
    let lo_a0 = PortId::from_raw(low.aux0);
    let lo_a1 = PortId::from_raw(low.aux1);
    net.retire(hi_p.slot_idx());
    net.retire(lo_p.slot_idx());

    net.connect(hc0.aux0, lc0.aux0, lo.clone())?;
    net.connect(hc0.aux1, lc1.aux0, lo.clone())?;
    net.connect(hc1.aux0, lc0.aux1, lo.clone())?;
    net.connect(hc1.aux1, lc1.aux1, lo.clone())?;
    net.connect(hc0.principal, lo_a0, lo.extend_left()?.extend_left()?)?;
    net.connect(hc1.principal, lo_a1, lo.extend_left()?.extend_right()?)?;
    net.connect(lc0.principal, hi_a0, lo.extend_right()?.extend_left()?)?;
    net.connect(lc1.principal, hi_a1, lo.extend_right()?.extend_right()?)?;
    Ok(())
}

fn add_level(level: u16, delta: i16) -> Result<u16, DnxError> {
    let v = i32::from(level) + i32::from(delta);
    if (0..16384).contains(&v) {
        Ok(v as u16)
    } else {
        Err(DnxError::DeltaOverflow)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::class::{ΔA, ΔI, ΔL};

    #[test]
    fn r2_era_fan_propagates_erasers() -> Result<(), DnxError> {
        let mut n = Net::<Proper, ΔA>::new(16);
        let app = n.alloc_app()?;
        let e0 = n.alloc_free(0)?;
        let e1 = n.alloc_free(1)?;
        let root = LOPath::root();
        n.connect(app.aux0, e0, root.clone())?;
        n.connect(app.aux1, e1, root.clone())?;
        r2_era_fan(&mut n, app.principal, &root)?;
        assert_eq!(n.frontier1.len(), 2);
        assert_eq!(n.slot(e0).principal, PortId::ERA.raw());
        Ok(())
    }

    #[test]
    fn r3_era_rep_propagates_erasers() -> Result<(), DnxError> {
        let mut n = Net::<Proper, ΔI>::new(16);
        let rep = n.alloc_rep_in(1, 0, 0)?;
        let e0 = n.alloc_free(0)?;
        let e1 = n.alloc_free(1)?;
        let root = LOPath::root();
        n.connect(rep.aux0, e0, root.clone())?;
        n.connect(rep.aux1, e1, root.clone())?;
        r3_era_rep(&mut n, rep.principal, &root)?;
        assert_eq!(n.frontier1.len(), 2);
        Ok(())
    }

    #[test]
    fn r4_beta_crosswires() -> Result<(), DnxError> {
        let mut n = Net::<Proper, ΔL>::new(32);
        let abs = n.alloc_abs()?;
        let app = n.alloc_app()?;
        let body = n.alloc_free(0)?;
        let var = n.alloc_free(1)?;
        let res = n.alloc_free(2)?;
        let arg = n.alloc_free(3)?;
        let root = LOPath::root();
        n.connect(abs.aux0, body, root.clone())?;
        n.connect(abs.aux1, var, root.clone())?;
        n.connect(app.aux0, res, root.clone())?;
        n.connect(app.aux1, arg, root.clone())?;
        let live0 = n.arena.live().len();
        r4_fan_fan(&mut n, abs.principal, app.principal, &root)?;
        assert_eq!(n.arena.live().len(), live0 - 2);
        assert_eq!(n.frontier1.len(), 2);
        Ok(())
    }

    #[test]
    fn r5_fan_rep_emits_four_agents_four_pairs() -> Result<(), DnxError> {
        let mut n = Net::<Proper, ΔI>::new(32);
        let fan = n.alloc_abs()?;
        let rep = n.alloc_rep_in(2, -1, 0)?;
        let a = n.alloc_free(0)?;
        let b = n.alloc_free(1)?;
        let c = n.alloc_free(2)?;
        let d = n.alloc_free(3)?;
        let root = LOPath::root();
        n.connect(fan.aux0, a, root.clone())?;
        n.connect(fan.aux1, b, root.clone())?;
        n.connect(rep.aux0, c, root.clone())?;
        n.connect(rep.aux1, d, root.clone())?;
        let live0 = n.arena.live().len();
        r5_fan_rep(&mut n, fan.principal, rep.principal, &root)?;
        assert_eq!(n.arena.live().len(), live0 + 2); // -2 + 4
        assert_eq!(n.frontier1.len(), 4);
        Ok(())
    }

    #[test]
    fn r6_annihilation_two_pairs() -> Result<(), DnxError> {
        let mut n = Net::<Proper, ΔI>::new(32);
        let ra = n.alloc_rep_in(3, 1, 2)?;
        let rb = n.alloc_rep_in(3, 1, 2)?;
        let w = n.alloc_free(0)?;
        let x = n.alloc_free(1)?;
        let y = n.alloc_free(2)?;
        let z = n.alloc_free(3)?;
        let root = LOPath::root();
        n.connect(ra.aux0, w, root.clone())?;
        n.connect(ra.aux1, x, root.clone())?;
        n.connect(rb.aux0, y, root.clone())?;
        n.connect(rb.aux1, z, root.clone())?;
        let live0 = n.arena.live().len();
        r6_rep_rep(&mut n, ra.principal, rb.principal, &root)?;
        assert_eq!(n.arena.live().len(), live0 - 2);
        assert_eq!(n.frontier1.len(), 2);
        Ok(())
    }

    #[test]
    fn r7_commutation_levels() -> Result<(), DnxError> {
        let mut n = Net::<Proper, ΔI>::new(32);
        let hi = n.alloc_rep_in(5, 0, 0)?;
        let low = n.alloc_rep_in(2, 1, -1)?;
        let a = n.alloc_free(0)?;
        let b = n.alloc_free(1)?;
        let c = n.alloc_free(2)?;
        let d = n.alloc_free(3)?;
        let root = LOPath::root();
        n.connect(hi.aux0, a, root.clone())?;
        n.connect(hi.aux1, b, root.clone())?;
        n.connect(low.aux0, c, root.clone())?;
        n.connect(low.aux1, d, root.clone())?;
        let live0 = n.arena.live().len();
        r7_rep_rep(&mut n, hi.principal, low.principal, &root)?;
        assert_eq!(n.arena.live().len(), live0 + 2);
        assert_eq!(n.frontier1.len(), 4);
        // hi-copy levels = hi.level + low.delta_i = {6, 4}; lo-copies = 2, 2
        let mut levels: Vec<u16> = n
            .frontier1
            .values()
            .map(|p| n.slot(p.p0.get()).data)
            .collect();
        levels.sort_unstable();
        assert_eq!(levels, vec![2, 2, 4, 6]);
        Ok(())
    }

    #[test]
    fn r7_delta_overflow_errors() -> Result<(), DnxError> {
        let mut n = Net::<Proper, ΔI>::new(16);
        let hi = n.alloc_rep_in(5, 0, 0)?;
        let low = n.alloc_rep_in(2, -10, 0)?;
        let root = LOPath::root();
        assert_eq!(
            r7_rep_rep(&mut n, hi.principal, low.principal, &root),
            Err(DnxError::DeltaOverflow)
        );
        Ok(())
    }

    // ── Paper oracle: levels + deltas + LOPaths together (main.tex §2/§4 + lopath.md) ──

    fn rep_triple(n: &Net<Proper, ΔI>, key: &LOPath) -> Option<(u16, i16, i16)> {
        n.frontier1.get(key).map(|pr| {
            let s0 = *n.slot(pr.p0.get());
            let s = if s0.is_rep() {
                s0
            } else {
                *n.slot(pr.p1.get())
            };
            (s.data, s.delta0, s.delta1)
        })
    }

    #[test]
    fn r7_oracle_levels_deltas_lopaths() -> Result<(), DnxError> {
        // main.tex L792-793: higher rep (level k) → copies at level k + lower.delta_i,
        // keeping higher's OWN deltas; lower rep → exact duplicates (level+deltas kept).
        // lopath.md R7: higher 0b00/0b01, lower 0b10/0b11.
        let mut n = Net::<Proper, ΔI>::new(32);
        let hi = n.alloc_rep_in(5, 7, 9)?;
        let low = n.alloc_rep_in(2, 1, -1)?;
        let (a, b, c, d) = (
            n.alloc_free(0)?,
            n.alloc_free(1)?,
            n.alloc_free(2)?,
            n.alloc_free(3)?,
        );
        let root = LOPath::root();
        n.connect(hi.aux0, a, root.clone())?;
        n.connect(hi.aux1, b, root.clone())?;
        n.connect(low.aux0, c, root.clone())?;
        n.connect(low.aux1, d, root.clone())?;
        r7_rep_rep(&mut n, hi.principal, low.principal, &root)?;
        let ll = root.extend_left()?.extend_left()?;
        let lr = root.extend_left()?.extend_right()?;
        let rl = root.extend_right()?.extend_left()?;
        let rr = root.extend_right()?.extend_right()?;
        assert_eq!(rep_triple(&n, &ll), Some((6, 7, 9))); // 5 + low.delta0(1)
        assert_eq!(rep_triple(&n, &lr), Some((4, 7, 9))); // 5 + low.delta1(-1)
        assert_eq!(rep_triple(&n, &rl), Some((2, 1, -1))); // lower exact copy
        assert_eq!(rep_triple(&n, &rr), Some((2, 1, -1)));
        Ok(())
    }

    #[test]
    fn r6_oracle_lopath_antichain() -> Result<(), DnxError> {
        // R6 same-level annihilation. main.tex §4 confluence ⇒ frontier1 antichain;
        // the two emitted pairs MUST be prefix-independent (distinct LOPaths {0},{1}).
        let mut n = Net::<Proper, ΔI>::new(32);
        let ra = n.alloc_rep_in(3, 1, 2)?;
        let rb = n.alloc_rep_in(3, 1, 2)?;
        let (w, x, y, z) = (
            n.alloc_free(0)?,
            n.alloc_free(1)?,
            n.alloc_free(2)?,
            n.alloc_free(3)?,
        );
        let root = LOPath::root();
        n.connect(ra.aux0, w, root.clone())?;
        n.connect(ra.aux1, x, root.clone())?;
        n.connect(rb.aux0, y, root.clone())?;
        n.connect(rb.aux1, z, root.clone())?;
        r6_rep_rep(&mut n, ra.principal, rb.principal, &root)?;
        let mut keys: Vec<LOPath> = n.frontier1.keys().cloned().collect();
        keys.sort();
        assert_eq!(keys, vec![root.extend_left()?, root.extend_right()?]);
        assert!(keys[0].prefix_independent(&keys[1]), "antichain");
        Ok(())
    }

    #[test]
    fn r5_oracle_status_unknown_levels_lopaths() -> Result<(), DnxError> {
        // main.tex L790/L1067: rep⊗fan → 2 exact rep copies, status UNPAIRED→UNKNOWN.
        // lopath.md R5: RepIn 0b10, RepOut 0b11; copies preserve level+deltas.
        let mut n = Net::<Proper, ΔI>::new(32);
        let fan = n.alloc_abs()?;
        let rep = n.alloc_rep_in(2, -1, 3)?;
        assert!(n.slot(rep.principal).rep_is_unpaired(), "rep born unpaired");
        let (a, b, c, d) = (
            n.alloc_free(0)?,
            n.alloc_free(1)?,
            n.alloc_free(2)?,
            n.alloc_free(3)?,
        );
        let root = LOPath::root();
        n.connect(fan.aux0, a, root.clone())?;
        n.connect(fan.aux1, b, root.clone())?;
        n.connect(rep.aux0, c, root.clone())?;
        n.connect(rep.aux1, d, root.clone())?;
        r5_fan_rep(&mut n, fan.principal, rep.principal, &root)?;
        let repin = root.extend_right()?.extend_left()?;
        let repout = root.extend_right()?.extend_right()?;
        for key in [&repin, &repout] {
            assert_eq!(
                rep_triple(&n, key),
                Some((2, -1, 3)),
                "level+deltas preserved"
            );
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
            assert!(
                !s.rep_is_unpaired(),
                "rep copy is UNKNOWN after fan commute"
            );
        }
        Ok(())
    }
}
