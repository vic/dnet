//! par==seq confluence oracle on a RICHER multi-round ΔI net (main.tex §2 perfect
//! confluence + LO-optimality β-count gate).
//!
//! Gadget per unit: `((λx. x x) id) id`. Reduction proceeds in MULTIPLE rounds:
//!   round 1  the self-apply `(λx. x x)` β-fires; its ΔI rep duplicates `id` (C2).
//!   round 2  the produced `id id` β-fires.
//! so each unit fires 2 R4 (β) interactions — richer than the single-β
//! `(λx.x x) id` gadget already covered by `parallel_equiv_wide::wide_self_apply`,
//! and it additionally exercises a redex (`outer.principal ⊗ inner-result`) that
//! only becomes principal-principal via SUBSTITUTION mid-reduction, stressing the
//! parallel scheduler's cross-batch redex discovery.
//!
//! K units are stamped at mutually-distinct lo-paths so ALL K self-apply pairs
//! coexist in frontier1 at t=0 => one parallel batch of width K (non-vacuous
//! antichain). normalize_parallel (dnx-core reduce/parallel.rs) drains the whole
//! frontier1 into ONE batch fired via par_iter, so active_pair_count() == K proves
//! the first batch fires K pairs simultaneously without synchronization.
//!
//! Oracle: canonical_hash(normalize_par(net,P)) == canonical_hash(normalize(net))
//! AND equal R4 (β) counts, for P in {2,4,8}. Sequential is ground truth.
//!
//! Run: `cargo test -p dnx-sched --test parallel_equiv_spine`.

use dnx_core::{canonical_hash, normalize, DnxError, LOPath, Net, PortId, Proper, ΔI};
use dnx_sched::normalize_par;
use std::sync::Arc;

// Mutually-distinct lo-path per unit `i` (binary-encoded over `bits` steps) so all
// units' active pairs coexist in frontier1 => a single wide parallel batch.
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

// `λx. x x` (ΔI self-apply abstraction) — mirrors parallel_equiv::parallel_equiv_di_sharing.
fn self_apply_fn(n: &mut Net<Proper, ΔI>, lo: &LOPath) -> Result<PortId, DnxError> {
    let outer = n.alloc_abs()?;
    let rep = n.alloc_rep_in(0, 0, 0)?;
    let inner_app = n.alloc_app()?;
    n.connect(rep.principal, outer.aux1, lo.clone())?;
    n.connect(rep.aux0, inner_app.principal, lo.clone())?;
    n.connect(rep.aux1, inner_app.aux1, lo.clone())?;
    n.connect(inner_app.aux0, outer.aux0, lo.clone())?;
    Ok(outer.principal)
}

// `λx. x` identity.
fn id_fn(n: &mut Net<Proper, ΔI>, lo: &LOPath) -> Result<PortId, DnxError> {
    let id = n.alloc_abs()?;
    n.connect(id.aux0, id.aux1, lo.clone())?;
    Ok(id.principal)
}

// `((λx.x x) id) id` wired to `root`.
fn spine_unit(n: &mut Net<Proper, ΔI>, lo: &LOPath, root: PortId) -> Result<(), DnxError> {
    let f = self_apply_fn(n, lo)?;
    let id1 = id_fn(n, lo)?;
    let inner = n.alloc_app()?;
    n.connect(inner.principal, f, lo.clone())?; // (λx.x x) id  — fires at t=0
    n.connect(inner.aux1, id1, lo.clone())?;
    let id2 = id_fn(n, lo)?;
    let outer = n.alloc_app()?;
    n.connect(outer.aux1, id2, lo.clone())?;
    n.connect(outer.principal, inner.aux0, lo.clone())?; // (inner result) id  — fires later
    n.connect(outer.aux0, root, lo.clone())?;
    Ok(())
}

// K spine units at distinct lo-paths.
fn wide_spine(k: u64, bits: u32) -> Result<Net<Proper, ΔI>, DnxError> {
    let mut n = Net::<Proper, ΔI>::new((k as u32) * 96 + 64);
    for i in 0..k {
        let lo = distinct_path(i, bits)?;
        let res = n.alloc_free(i as u32)?;
        spine_unit(&mut n, &lo, res)?;
        n.add_root(Arc::from(format!("r{i}")), res);
    }
    Ok(n)
}

// par==seq over P in {2,4,8}: canonical-hash equality + R4 (β) equality. `min_batch`
// is the antichain non-vacuity guard (proven first-batch width).
fn assert_equiv(label: &str, min_batch: usize, k: u64, bits: u32) -> Result<(), String> {
    let probe = wide_spine(k, bits).map_err(|e| format!("{label}: build: {e:?}"))?;
    let apc = probe.active_pair_count();
    if apc < min_batch {
        return Err(format!(
            "ANTICHAIN VACUOUS {label}: frontier1={apc} < min_batch={min_batch}"
        ));
    }
    drop(probe);
    let (seq, s_seq) =
        normalize(wide_spine(k, bits).map_err(|e| format!("{label}: build: {e:?}"))?)
            .map_err(|e| format!("{label}: seq normalize: {e:?}"))?;
    let rs = *seq
        .roots()
        .get("r0")
        .ok_or_else(|| format!("{label}: seq root r0 missing"))?;
    let hseq = canonical_hash(&seq, rs).map_err(|e| format!("{label}: seq hash: {e:?}"))?;
    for p in [2usize, 4, 8] {
        let (par, s_par) = normalize_par(
            wide_spine(k, bits).map_err(|e| format!("{label}: build: {e:?}"))?,
            p,
        )
        .map_err(|e| format!("{label}: par(P={p}) normalize: {e:?}"))?;
        let rp = *par
            .roots()
            .get("r0")
            .ok_or_else(|| format!("{label}: par root r0 missing"))?;
        let hpar =
            canonical_hash(&par, rp).map_err(|e| format!("{label}: par hash(P={p}): {e:?}"))?;
        if hseq != hpar {
            return Err(format!(
                "HASH DIVERGENCE {label} P={p}: par != seq (β seq={} par={})",
                s_seq.r4_count, s_par.r4_count
            ));
        }
        if s_seq.r4_count != s_par.r4_count {
            return Err(format!(
                "β-COUNT MISMATCH {label} P={p}: seq r4={} par r4={}",
                s_seq.r4_count, s_par.r4_count
            ));
        }
    }
    Ok(())
}

/// Wide multi-round ΔI spine: K copies of `((λx.x x) id) id` fire 2 β-rounds each;
/// par==seq by canonical hash + β-count for P in {2,4,8}, antichain width K.
#[test]
fn wide_spine_multiround_equiv() -> Result<(), String> {
    for k in [2u64, 3, 4, 6, 8, 12, 16] {
        let bits = 64 - (k.max(2) - 1).leading_zeros();
        // each unit puts exactly one (λx.x x)⊗id active pair at a distinct lo-path => K.
        assert_equiv(&format!("spine k={k}"), k as usize, k, bits)?;
    }
    Ok(())
}
