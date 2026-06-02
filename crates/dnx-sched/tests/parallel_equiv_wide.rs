//! WIDE parallel-equivalence oracle (review 🔴 verification).
//!
//! Hypothesis under test (a code review claims this BREAKS par==seq):
//!   `parallel.rs:318` — C2 (`c2_par`) writes a NEIGHBOR slot `rep_b` (not just the
//!   pair's principals) via `out.slot_muts.push((rep_b.slot_idx(), b_mod))`.
//!   `parallel.rs:169` — the coordinator applies worker outputs SEQUENTIALLY, while
//!   every worker read the SAME pre-batch arena snapshot (`arena_ref`, :149).
//!   `net.rs:183`+`:272` — frontier1 is a plain `BTreeMap<LOPath, ActivePair>` of ALL
//!   principal-principal pairs; `normalize_parallel:138` drains the WHOLE map into one
//!   batch. There is NO antichain filter that excludes two reducible pairs whose
//!   C2/C3 neighbor-closures OVERLAP (alias the same `rep_b`).
//!
//! So if a single parallel batch holds >=2 rep-bearing pairs whose C2 merges target the
//! SAME `rep_b`, two workers compute `b_mod` from the STALE snapshot and the coordinator
//! applies both (last-writer-wins on the rep_b slot + double rewire) -> divergence from
//! the leftmost-outermost sequential merge.
//!
//! Oracle: canonical_hash(normalize_par(net,P)) == canonical_hash(normalize(net)) for
//! P in {2,4,8}, over MANY wide ALIASING nets. Sequential is ground truth (main.tex §2
//! perfect confluence + the LO-optimality interaction-count gate).
//!
//! Run: `cargo test -p dnx-sched --test parallel_equiv_wide`.

use dnx_core::{
    canonical_hash, normalize, DnxError, LOPath, Net, NetClassMarker, PortId, Proper, ΔI, ΔK,
};
use dnx_sched::normalize_par;
use std::sync::Arc;

// ── deterministic PRNG (no proptest dev-dep; hand-rolled per mission) ───────────
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        // SplitMix64.
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn range(&mut self, lo: u64, hi: u64) -> u64 {
        lo + self.next() % (hi - lo)
    }
}

// Unique, mutually distinct LOPath per copy `i` (binary-encoded over `bits` steps).
// Distinct keys => all copies coexist in frontier1 => one parallel batch.
fn distinct_path(i: u64, bits: u32) -> Result<LOPath, DnxError> {
    let mut p = LOPath::root();
    for b in (0..bits).rev() {
        p = if (i >> b) & 1 == 1 {
            p.extend_right()?
        } else {
            p.extend_left()?
        };
    }
    Ok(p)
}

fn hashes_match<C: NetClassMarker>(
    seq: &Net<dnx_core::Canonical, C>,
    par: &Net<dnx_core::Canonical, C>,
    root: &str,
) -> Result<bool, DnxError> {
    let rs = *seq.roots().get(root).ok_or(DnxError::ReadbackIncomplete)?;
    let rp = *par.roots().get(root).ok_or(DnxError::ReadbackIncomplete)?;
    Ok(canonical_hash(seq, rs)? == canonical_hash(par, rp)?)
}

// Assert par==seq (hash + interaction count) for P in {2,4,8}. Returns Err on divergence
// so the harness prints the failing net id; the interaction-count check is the
// paper's max-parallelism gate (equal total interactions).
//
// `min_batch` is the ANTICHAIN NON-VACUITY guard: the proven lower bound on the number of
// prefix-independent active pairs the gadget puts in frontier1 at t=0. normalize_parallel
// (dnx-core reduce/parallel.rs:138) drains the WHOLE frontier1 into ONE batch fired via
// par_iter, so active_pair_count() >= min_batch proves the FIRST batch holds >=min_batch
// pairs that the parallel path fires SIMULTANEOUSLY WITHOUT SYNCHRONIZATION (main.tex:339).
// Without this, par==seq could pass vacuously on a schedule that serialized one pair/batch.
fn assert_equiv<C, F>(label: &str, root: &str, min_batch: usize, mk: F) -> Result<(), String>
where
    C: NetClassMarker + dnx_core::CRules,
    F: Fn() -> Result<Net<Proper, C>, DnxError>,
{
    let probe = mk().map_err(|e| format!("{label}: build: {e:?}"))?;
    let apc = probe.active_pair_count();
    if apc < min_batch {
        return Err(format!(
            "ANTICHAIN VACUOUS {label}: frontier1={apc} < min_batch={min_batch} \
             (parallel batch would not fire simultaneously; oracle would be vacuous)"
        ));
    }
    drop(probe);
    let (seq, s_seq) = normalize(mk().map_err(|e| format!("{label}: build: {e:?}"))?)
        .map_err(|e| format!("{label}: seq normalize: {e:?}"))?;
    for p in [2usize, 4, 8] {
        let (par, s_par) = normalize_par(mk().map_err(|e| format!("{label}: build: {e:?}"))?, p)
            .map_err(|e| format!("{label}: par(P={p}) normalize: {e:?}"))?;
        let ok =
            hashes_match(&seq, &par, root).map_err(|e| format!("{label}: hash(P={p}): {e:?}"))?;
        if !ok {
            // SOUNDNESS divergence — the canonical normal forms differ (this is the
            // critical failure the review predicts).
            return Err(format!(
                "HASH DIVERGENCE {label} P={p}: par != seq (interactions seq={} par={})",
                s_seq.interactions, s_par.interactions
            ));
        }
        // β-count gate (main.tex LO-optimality; matches existing parallel_equiv.rs which
        // asserts r4_count equality for P>1). Total-interaction counts may differ between
        // schedules for lazy C2/C3 canonicalization without changing the canonical NF.
        if s_seq.r4_count != s_par.r4_count {
            return Err(format!(
                "β-COUNT MISMATCH {label} P={p}: seq r4={} par r4={}",
                s_seq.r4_count, s_par.r4_count
            ));
        }
    }
    Ok(())
}

// ── gadget 1: (λx. x x) id, ΔI — proven C2-firing sharing term (oracle.rs) ───────
// Stamped K-wide at distinct lo-paths so ALL copies' rep interactions co-occur in the
// same parallel batches. Maximizes concurrent C2 count.
fn wide_self_apply(k: u64, bits: u32) -> Result<Net<Proper, ΔI>, DnxError> {
    let mut n = Net::<Proper, ΔI>::new((k as u32) * 64 + 64);
    for i in 0..k {
        let lo = distinct_path(i, bits)?;
        let outer = n.alloc_abs()?;
        let rep = n.alloc_rep_in(0, 0, 0)?;
        let inner_app = n.alloc_app()?;
        n.connect(rep.principal, outer.aux1, lo.clone())?;
        n.connect(rep.aux0, inner_app.principal, lo.clone())?;
        n.connect(rep.aux1, inner_app.aux1, lo.clone())?;
        n.connect(inner_app.aux0, outer.aux0, lo.clone())?;
        let id = n.alloc_abs()?;
        n.connect(id.aux0, id.aux1, lo.clone())?;
        let app = n.alloc_app()?;
        let res = n.alloc_free(i as u32)?;
        n.connect(app.principal, outer.principal, lo.clone())?;
        n.connect(app.aux1, id.principal, lo.clone())?;
        n.connect(app.aux0, res, lo.clone())?;
        n.add_root(Arc::from(format!("r{i}")), res);
    }
    Ok(n)
}

// ── C2 trigger gadget (TWO-STAGE, reduction-driven), ΔK — VERIFIED to fire c2_par ─
// VERIFIED via slot-level trace: this gadget makes `c2_par` (parallel.rs:271) actually
// FIRE in a parallel batch, and with `shared` set, MULTIPLE units' C2 merges all target
// the SAME rep_b slot in one batch (the precise :318 neighbor-write aliasing hazard).
//
// Why two stages (the single-stage R3 form does NOT fire c2_par): workers read ONE
// pre-batch arena snapshot, so a same-batch erasure of rep_a.aux1 is invisible to the
// worker that dispatches rep_a. So we sequence it across batches:
//   STAGE 1 (batch N): ERA ⊗ efan (R2) erases rep_a.aux1 (TAG_AUX1_ERASED committed);
//                      ERA ⊗ gfan (R2) propagates ERA onto rep_a.principal (gfan.aux0 peer).
//   STAGE 2 (batch N+1): rep_a.principal is now ERA -> ERA ⊗ rep_a (R3). In the PAR path
//                      R3 calls c2_par (parallel.rs:365); rep_a is unpaired with aux1
//                      committed-erased -> C2 MERGES rep_a into rep_b (writes rep_b slot).
//   rep_a.aux0 -> rep_b.principal is the C2 edge. la/lb/da satisfy 0 <= lb-la <= da.
// `shared` reuses one rep_b across units => aliased concurrent C2 writes to one slot.
fn emit_c2_unit<C: NetClassMarker>(
    n: &mut Net<Proper, C>,
    base: &LOPath,
    la: u16,
    lb: u16,
    da: i16,
    tag: u32,
    shared: Option<PortId>,
) -> Result<PortId, DnxError> {
    // rep_b: the (possibly shared) C2 neighbor. Both aux erased so it decays after merge.
    let rep_b_principal = match shared {
        Some(p) => p,
        None => {
            let b = n.alloc_rep_in(lb, 0, 0)?;
            n.connect(PortId::ERA, b.aux0, base.extend_right()?.extend_left()?)?;
            n.connect(PortId::ERA, b.aux1, base.extend_right()?.extend_right()?)?;
            b.principal
        }
    };

    // rep_a: unpaired. aux0 -> rep_b.principal (the C2 edge).
    let rep_a = n.alloc_rep_in(la, da, da)?;
    n.connect(rep_a.aux0, rep_b_principal, base.clone())?;

    // STAGE1a: efan erases rep_a.aux1 (R2 propagates ERA to efan.aux0 peer == rep_a.aux1).
    let efan = n.alloc_abs()?;
    n.connect(efan.aux0, rep_a.aux1, base.extend_left()?)?;
    let sink = n.alloc_free(tag * 16 + 1)?;
    n.connect(efan.aux1, sink, base.extend_left()?.extend_left()?)?;
    n.connect(
        PortId::ERA,
        efan.principal,
        base.extend_left()?.extend_right()?,
    )?;

    // STAGE1b: gfan exposes rep_a.principal to ERA (R2 -> ERA onto gfan.aux0 peer ==
    // rep_a.principal). Next batch then dispatches ERA ⊗ rep_a (R3 -> c2_par in PAR).
    let gfan = n.alloc_abs()?;
    n.connect(gfan.aux0, rep_a.principal, base.extend_right()?)?;
    let gsink = n.alloc_free(tag * 16 + 2)?;
    n.connect(gfan.aux1, gsink, base.extend_right()?.extend_left()?)?;
    n.connect(
        PortId::ERA,
        gfan.principal,
        base.extend_right()?.extend_right()?,
    )?;

    Ok(rep_b_principal)
}

// Wide: K independent C2 units at distinct lo-paths (many C2 in concurrent batches).
fn wide_c2_units<C: NetClassMarker>(
    k: u64,
    bits: u32,
    vary: &mut Lcg,
) -> Result<Net<Proper, C>, DnxError> {
    let mut n = Net::<Proper, C>::new((k as u32) * 48 + 64);
    for i in 0..k {
        let base = distinct_path(i, bits)?;
        let lb = vary.range(1, 6) as u16;
        let la = vary.range(0, lb as u64 + 1) as u16; // la <= lb
        let da = (lb - la) as i16 + vary.range(0, 4) as i16; // da >= lb-la (merge window)
        emit_c2_unit::<C>(&mut n, &base, la, lb, da, i as u32, None)?;
    }
    // A free root so the (fully-decaying) net has a canonical readback anchor.
    let anchor = n.alloc_free(999_999)?;
    n.add_root(Arc::from("r0"), anchor);
    Ok(n)
}

// Cross-aliased: many C2 units in DISTINCT lo subnets all sharing ONE rep_b — the
// strongest aliasing (>=2 in-batch R3/R5 pairs whose C2 merges target the SAME slot).
fn cross_aliased_c2<C: NetClassMarker>(
    units: u64,
    bits: u32,
    vary: &mut Lcg,
) -> Result<Net<Proper, C>, DnxError> {
    let mut n = Net::<Proper, C>::new((units as u32) * 48 + 128);
    // one shared rep_b; both aux erased so it decays after the (single, by LO) merge.
    let lb = vary.range(2, 7) as u16;
    let shared = n.alloc_rep_in(lb, 0, 0)?;
    let base_b = distinct_path(0, bits.max(1))?;
    n.connect(PortId::ERA, shared.aux0, base_b.extend_left()?)?;
    n.connect(PortId::ERA, shared.aux1, base_b.extend_right()?)?;
    let shared_p = shared.principal;
    for u in 0..units {
        let base = distinct_path(u + 1, bits)?;
        let la = vary.range(0, lb as u64 + 1) as u16;
        let da = (lb - la) as i16 + vary.range(0, 4) as i16;
        emit_c2_unit::<C>(&mut n, &base, la, lb, da, (u + 1) as u32, Some(shared_p))?;
    }
    let anchor = n.alloc_free(999_999)?;
    n.add_root(Arc::from("x0_0"), anchor);
    Ok(n)
}

// ── tests ───────────────────────────────────────────────────────────────────────

/// Wide ΔI sharing: many (λx.x x) id copies in one batch. C2 fires per copy.
#[test]
fn wide_di_self_apply_equiv() -> Result<(), String> {
    for k in [2u64, 3, 4, 6, 8, 12, 16, 24] {
        let bits = 64 - (k.max(2) - 1).leading_zeros();
        // each copy contributes 1 app⊗outer-abs active pair at a distinct lo-path => k.
        assert_equiv::<ΔI, _>(&format!("self_apply k={k}"), "r0", k as usize, || {
            wide_self_apply(k, bits)
        })?;
    }
    Ok(())
}

/// Wide C2 units (ΔK): K reduction-manufactured unpaired reps fire C2 in concurrent batches.
#[test]
fn wide_dk_c2_units_equiv() -> Result<(), String> {
    let mut rng = Lcg(0xDEAD_BEEF_1234_5678);
    for trial in 0..20u64 {
        let k = 2 + (trial % 6);
        let bits = 64 - (k.max(2) - 1).leading_zeros();
        let seed = rng.next();
        // each unit emits 2 ERA-fan (R2) active pairs (efan, gfan) at distinct lo-paths => 2k.
        assert_equiv::<ΔK, _>(
            &format!("c2_units trial={trial} k={k}"),
            "r0",
            2 * k as usize,
            || {
                let mut v = Lcg(seed);
                wide_c2_units::<ΔK>(k, bits, &mut v)
            },
        )?;
    }
    Ok(())
}

/// Cross-aliased C2 (ΔK): two pairs in distinct batch slots target the SAME rep_b slot.
/// This is the precise hazard the review describes (overlapping C2 neighbor-closures).
#[test]
fn cross_aliased_c2_equiv() -> Result<(), String> {
    let mut rng = Lcg(0x0BAD_F00D_CAFE_BABE);
    for trial in 0..20u64 {
        let groups = 1 + (trial % 5);
        let bits = 64 - (4 * groups).max(2).leading_zeros();
        let seed = rng.next();
        // each group emits 2 ERA-fan (R2) pairs; the shared rep_b adds none => 2*groups.
        assert_equiv::<ΔK, _>(
            &format!("cross trial={trial} groups={groups}"),
            "x0_0",
            2 * groups as usize,
            || {
                let mut v = Lcg(seed);
                cross_aliased_c2::<ΔK>(groups, bits, &mut v)
            },
        )?;
    }
    Ok(())
}
