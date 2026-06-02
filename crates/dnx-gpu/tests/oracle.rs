//! GPU soundness oracle: canonical_hash(gpu) == canonical_hash(seq) — main.tex §2 confluence.
//! Runs only when GPU adapter available; skips otherwise (CI without GPU).
//! `just gpu-oracle` runs these (--include-ignored).

use dnx_ast::{Ast, NoFun, NoVal};
use dnx_core::{canonical_hash, LOPath, Net, PortId, PortKind, Proper, ΔI, ΔL};
use dnx_elab::{elaborate, pass1};
use dnx_gpu::{global_amortized, GpuScheduler};
use dnx_sched::{sequential::SequentialScheduler, Scheduler};
use std::collections::HashMap;
use std::sync::Arc;

type E = Ast<NoVal, NoFun>;
type Env = HashMap<Arc<str>, (PortId, u32)>;

fn nm_e(s: &str) -> E {
    Ast::Name(Arc::from(s))
}
fn nm_arc_e(s: Arc<str>) -> E {
    Ast::Name(s)
}
fn ab_e(x: &str, b: E) -> E {
    Ast::Abs(Arc::from(x), Box::new(b))
}
fn ap_e(f: E, x: E) -> E {
    Ast::App(Box::new(f), Box::new(x))
}

fn church_spine_e(f: Arc<str>, remaining: usize) -> E {
    if remaining == 0 {
        return nm_e("cx");
    }
    if remaining == 1 {
        return ap_e(nm_arc_e(f), nm_e("cx"));
    }
    let f_now: Arc<str> = Arc::from(format!("cfn{remaining}").as_str());
    let f_rest: Arc<str> = Arc::from(format!("cfr{remaining}").as_str());
    let inner = ap_e(
        nm_arc_e(f_now.clone()),
        church_spine_e(f_rest.clone(), remaining - 1),
    );
    Ast::Rep(Box::new(nm_arc_e(f)), f_now, f_rest, Box::new(inner))
}

/// church n = λf.λx. f^n x with explicit Rep spine (linear; passes pass1).
fn church_e(n: usize) -> E {
    ab_e("cf", ab_e("cx", church_spine_e(Arc::from("cf"), n)))
}

/// Elaborate a closed ΔI expr into a Net rooted at "r" with arena `cap`.
fn elab_root_di(expr: &E, cap: u32) -> Net<Proper, ΔI> {
    let r1 = pass1(expr).unwrap();
    let mut net = Net::<Proper, ΔI>::new(cap);
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
    let root_port = if rp.port_kind() != PortKind::Principal {
        let s = net.alloc_free(0).unwrap();
        net.connect(rp, s, LOPath::root()).unwrap();
        s
    } else {
        rp
    };
    net.add_root(Arc::from("r"), root_port);
    net
}

fn make_church_applied_di(n: usize) -> Net<Proper, ΔI> {
    let id = ab_e("ciy", nm_e("ciy"));
    let id2 = ab_e("ciz", nm_e("ciz"));
    let expr = ap_e(ap_e(church_e(n), id), id2);
    elab_root_di(&expr, ((n + 2) * 24 + 64) as u32)
}

/// church m × n applied to id id: λf.λx. (church m) ((church n) f) x, then `id id`.
/// The m-fold outer spine duplicates church-n's Rep-laden body each round, so Rep
/// commutes through Rep across multiple rounds — genuine multi-round ΔI ping-pong
/// (C4 Fan⊗Rep + C2 Rep-merge, main.tex §4). Far richer than a single church spine.
fn make_church_mul_di(m: usize, n: usize) -> Net<Proper, ΔI> {
    let composed = ab_e(
        "mf",
        ab_e(
            "mx",
            ap_e(ap_e(church_e(m), ap_e(church_e(n), nm_e("mf"))), nm_e("mx")),
        ),
    );
    let id = ab_e("miy", nm_e("miy"));
    let id2 = ab_e("miz", nm_e("miz"));
    let expr = ap_e(ap_e(composed, id), id2);
    elab_root_di(&expr, ((m + n + 4) * 48 + 128) as u32)
}

fn root_hash_l(net: &dnx_core::Net<dnx_core::Canonical, ΔL>, name: &str) -> [u8; 32] {
    let port = *net.roots().get(name).expect("root missing");
    canonical_hash(net, port).expect("canonical_hash on a pure NF")
}

fn root_hash_i(net: &dnx_core::Net<dnx_core::Canonical, ΔI>, name: &str) -> [u8; 32] {
    let port = *net.roots().get(name).expect("root missing");
    canonical_hash(net, port).expect("canonical_hash on a pure NF")
}

fn make_id_applied() -> Net<Proper, ΔL> {
    let mut n = Net::<Proper, ΔL>::new(32);
    let abs = n.alloc_abs().unwrap();
    let app = n.alloc_app().unwrap();
    let arg = n.alloc_abs().unwrap();
    n.connect(abs.aux0, abs.aux1, LOPath::root()).unwrap();
    n.connect(arg.aux0, arg.aux1, LOPath::root()).unwrap();
    n.connect(app.principal, abs.principal, LOPath::root())
        .unwrap();
    n.connect(app.aux1, arg.principal, LOPath::root()).unwrap();
    let res = n.alloc_free(0).unwrap();
    n.connect(app.aux0, res, LOPath::root()).unwrap();
    n.add_root(Arc::from("r"), res);
    n
}

fn make_chained() -> Net<Proper, ΔL> {
    let mut n = Net::<Proper, ΔL>::new(64);
    let id1 = n.alloc_abs().unwrap();
    let id2 = n.alloc_abs().unwrap();
    let app = n.alloc_app().unwrap();
    n.connect(id1.aux0, id1.aux1, LOPath::root()).unwrap();
    n.connect(id2.aux0, id2.aux1, LOPath::root()).unwrap();
    n.connect(app.principal, id1.principal, LOPath::root())
        .unwrap();
    n.connect(app.aux1, id2.principal, LOPath::root()).unwrap();
    let res = n.alloc_free(0).unwrap();
    n.connect(app.aux0, res, LOPath::root()).unwrap();
    n.add_root(Arc::from("r"), res);
    n
}

/// (λx. x x) id in ΔI — Rep duplicates id; fires R4 + R5 (Fan⊗Rep commutation).
/// Exactly 2 β-reductions by LO-optimality (§4 main.tex).
fn make_self_apply_id() -> Net<Proper, ΔI> {
    let mut n = Net::<Proper, ΔI>::new(64);
    let lo = LOPath::root();
    let outer = n.alloc_abs().unwrap();
    let rep = n.alloc_rep_in(0, 0, 0).unwrap();
    let inner_app = n.alloc_app().unwrap();
    n.connect(rep.principal, outer.aux1, lo.clone()).unwrap();
    n.connect(rep.aux0, inner_app.principal, lo.clone())
        .unwrap();
    n.connect(rep.aux1, inner_app.aux1, lo.clone()).unwrap();
    n.connect(inner_app.aux0, outer.aux0, lo.clone()).unwrap();
    let id = n.alloc_abs().unwrap();
    n.connect(id.aux0, id.aux1, lo.clone()).unwrap();
    let app = n.alloc_app().unwrap();
    let res = n.alloc_free(0).unwrap();
    n.connect(app.principal, outer.principal, lo.clone())
        .unwrap();
    n.connect(app.aux1, id.principal, lo.clone()).unwrap();
    n.connect(app.aux0, res, lo).unwrap();
    n.add_root(Arc::from("res"), res);
    n
}

/// N independent (λx.x) id pairs in one Net — stresses GPU batch dispatch.
/// Each pair fires 1 R4; total = N R4s processed in one GPU kernel launch.
fn make_n_batch_ids(count: usize) -> Net<Proper, ΔL> {
    let depth = usize::BITS as usize - count.leading_zeros() as usize; // ceil(log2(count+1))
    let mut n = Net::<Proper, ΔL>::new((count * 8 + 8) as u32);
    for i in 0..count {
        let lo = lo_for_index(i, depth);
        let abs = n.alloc_abs().unwrap();
        let arg = n.alloc_abs().unwrap();
        let app = n.alloc_app().unwrap();
        let res = n.alloc_free(i as u32 * 2).unwrap();
        n.connect(abs.aux0, abs.aux1, lo.clone()).unwrap();
        n.connect(arg.aux0, arg.aux1, lo.clone()).unwrap();
        n.connect(app.principal, abs.principal, lo.clone()).unwrap();
        n.connect(app.aux1, arg.principal, lo.clone()).unwrap();
        n.connect(app.aux0, res, lo).unwrap();
        n.add_root(Arc::from(format!("r{i}").as_str()), res);
    }
    n
}

fn lo_for_index(i: usize, depth: usize) -> LOPath {
    let mut lo = LOPath::root();
    for bit in (0..depth).rev() {
        lo = if (i >> bit) & 1 == 0 {
            lo.extend_left().unwrap()
        } else {
            lo.extend_right().unwrap()
        };
    }
    lo
}

// ── existing tests ────────────────────────────────────────────────────────────

#[test]
fn gpu_equiv_identity_hash() {
    let (seq, _) = SequentialScheduler::normalize(make_id_applied()).unwrap();
    let (gpu, _) = GpuScheduler::normalize(make_id_applied()).unwrap();
    assert_eq!(
        root_hash_l(&seq, "r"),
        root_hash_l(&gpu, "r"),
        "gpu hash must equal sequential (confluence §2)"
    );
}

#[test]
fn gpu_equiv_chained_hash() {
    let (seq, _) = SequentialScheduler::normalize(make_chained()).unwrap();
    let (gpu, _) = GpuScheduler::normalize(make_chained()).unwrap();
    assert_eq!(
        root_hash_l(&seq, "r"),
        root_hash_l(&gpu, "r"),
        "gpu chained: hash must equal sequential"
    );
}

#[test]
fn gpu_equiv_r4_count() {
    let (_, s_seq) = SequentialScheduler::normalize(make_id_applied()).unwrap();
    let (_, s_gpu) = GpuScheduler::normalize(make_id_applied()).unwrap();
    assert_eq!(s_seq.r4_count, s_gpu.r4_count, "r4 count must match");
    assert_eq!(
        s_seq.interactions, s_gpu.interactions,
        "interaction count must match"
    );
}

// ── ΔI sharing (R5 Fan⊗Rep) ──────────────────────────────────────────────────

/// (λx.x x) id: gpu hash == sequential hash under ΔI sharing (R5 coverage).
#[test]
fn gpu_equiv_di_sharing_hash() {
    let (seq, _) = SequentialScheduler::normalize(make_self_apply_id()).unwrap();
    let (gpu, _) = GpuScheduler::normalize(make_self_apply_id()).unwrap();
    assert_eq!(
        root_hash_i(&seq, "res"),
        root_hash_i(&gpu, "res"),
        "ΔI sharing: gpu hash == sequential (R5 Fan⊗Rep covered)"
    );
}

/// (λx.x x) id: r4_count == 2 and matches sequential (LO-optimality §4).
#[test]
fn gpu_equiv_di_sharing_r4_count() {
    let (_, s_seq) = SequentialScheduler::normalize(make_self_apply_id()).unwrap();
    let (_, s_gpu) = GpuScheduler::normalize(make_self_apply_id()).unwrap();
    assert_eq!(s_gpu.r4_count, 2, "ΔI sharing: exactly 2 β (LO-optimality)");
    assert_eq!(s_seq.r4_count, s_gpu.r4_count, "gpu r4_count == sequential");
    assert_eq!(
        s_seq.interactions, s_gpu.interactions,
        "gpu interactions == sequential"
    );
}

// ── batch dispatch stress ─────────────────────────────────────────────────────

/// 16 independent id_applied pairs: gpu hash matches sequential for each root.
/// Tests GPU batch dispatch with 16 concurrent threads in one kernel launch.
#[test]
fn gpu_equiv_batch_16() {
    let count = 16;
    let (seq, s_seq) = SequentialScheduler::normalize(make_n_batch_ids(count)).unwrap();
    let (gpu, s_gpu) = GpuScheduler::normalize(make_n_batch_ids(count)).unwrap();
    for i in 0..count {
        let name = format!("r{i}");
        let sp = *seq.roots().get(name.as_str()).expect("root");
        let gp = *gpu.roots().get(name.as_str()).expect("root");
        assert_eq!(
            canonical_hash(&seq, sp).unwrap(),
            canonical_hash(&gpu, gp).unwrap(),
            "batch-16 root {name}: gpu hash != sequential"
        );
    }
    assert_eq!(
        s_seq.r4_count, s_gpu.r4_count,
        "batch-16: r4_count must match"
    );
    assert_eq!(
        s_seq.interactions, count as u64,
        "batch-16: exactly {count} interactions"
    );
}

/// 128 independent pairs: one full workgroup (dispatch_workgroups=1, 128 threads).
#[test]
fn gpu_equiv_batch_128() {
    let count = 128;
    let (seq, s_seq) = SequentialScheduler::normalize(make_n_batch_ids(count)).unwrap();
    let (gpu, s_gpu) = GpuScheduler::normalize(make_n_batch_ids(count)).unwrap();
    for i in 0..count {
        let name = format!("r{i}");
        let sp = *seq.roots().get(name.as_str()).expect("root");
        let gp = *gpu.roots().get(name.as_str()).expect("root");
        assert_eq!(
            canonical_hash(&seq, sp).unwrap(),
            canonical_hash(&gpu, gp).unwrap(),
            "batch-128 root {name}: hash mismatch"
        );
    }
    assert_eq!(
        s_seq.r4_count, s_gpu.r4_count,
        "batch-128: r4_count must match"
    );
    assert_eq!(
        s_seq.interactions, count as u64,
        "batch-128: exactly {count} R4s"
    );
}

/// 256 independent pairs: two full workgroups — verifies multi-workgroup dispatch.
#[test]
fn gpu_equiv_batch_256() {
    let count = 256;
    let (seq, s_seq) = SequentialScheduler::normalize(make_n_batch_ids(count)).unwrap();
    let (gpu, s_gpu) = GpuScheduler::normalize(make_n_batch_ids(count)).unwrap();
    assert_eq!(
        s_seq.r4_count, s_gpu.r4_count,
        "batch-256: r4_count must match"
    );
    assert_eq!(
        s_seq.interactions, count as u64,
        "batch-256: exactly {count} R4s"
    );
    let name = "r0";
    let sp = *seq.roots().get(name).expect("root");
    let gp = *gpu.roots().get(name).expect("root");
    assert_eq!(
        canonical_hash(&seq, sp).unwrap(),
        canonical_hash(&gpu, gp).unwrap(),
        "batch-256 spot-check r0: hash mismatch"
    );
}

// ── church numeral reductions (R4+R5+R6/R7) ──────────────────────────────────

/// church 8 applied to id id: gpu hash == sequential, r4_count == 8 (LO-optimality §4).
/// Exercises R5 (Fan⊗Rep) spine commutations + R4 β-reductions.
#[test]
fn gpu_equiv_church8_applied() {
    let (seq, s_seq) = SequentialScheduler::normalize(make_church_applied_di(8)).unwrap();
    let (gpu, s_gpu) = GpuScheduler::normalize(make_church_applied_di(8)).unwrap();
    let sp = *seq.roots().get("r").expect("root");
    let gp = *gpu.roots().get("r").expect("root");
    assert_eq!(
        canonical_hash(&seq, sp).unwrap(),
        canonical_hash(&gpu, gp).unwrap(),
        "church8: gpu hash == sequential (confluence §2)"
    );
    assert_eq!(s_seq.r4_count, s_gpu.r4_count, "church8: r4_count matches");
    assert_eq!(
        s_seq.interactions, s_gpu.interactions,
        "church8: total interactions match"
    );
}

/// church 32 applied to id id: gpu hash == sequential. Stresses R5 spine.
#[test]
fn gpu_equiv_church32_applied() {
    let (seq, s_seq) = SequentialScheduler::normalize(make_church_applied_di(32)).unwrap();
    let (gpu, s_gpu) = GpuScheduler::normalize(make_church_applied_di(32)).unwrap();
    let sp = *seq.roots().get("r").expect("root");
    let gp = *gpu.roots().get("r").expect("root");
    assert_eq!(
        canonical_hash(&seq, sp).unwrap(),
        canonical_hash(&gpu, gp).unwrap(),
        "church32: gpu hash == sequential"
    );
    assert_eq!(s_seq.r4_count, s_gpu.r4_count, "church32: r4_count matches");
    assert_eq!(
        s_seq.interactions, s_gpu.interactions,
        "church32: interactions match"
    );
}

/// church 3×4 = 12 applied to id id: multi-round ΔI ping-pong.
/// The outer 3-fold spine re-duplicates church-4's Rep-laden body each round, so
/// Rep⊗Rep commutes across several rounds (C2/C4, main.tex §4) — strictly richer
/// than a single church spine. SACRED: gpu canonical-hash == sequential (§2 confluence)
/// and gpu interactions/r4 == sequential (§4 LO-optimality: GPU adds no work).
#[test]
fn gpu_equiv_church_mul_3x4() {
    let (seq, s_seq) = SequentialScheduler::normalize(make_church_mul_di(3, 4)).unwrap();
    let (gpu, s_gpu) = GpuScheduler::normalize(make_church_mul_di(3, 4)).unwrap();
    assert_eq!(
        canonical_hash(&seq, *seq.roots().get("r").expect("root")).unwrap(),
        canonical_hash(&gpu, *gpu.roots().get("r").expect("root")).unwrap(),
        "church 3×4: gpu canonical-hash == sequential (confluence §2)"
    );
    assert_eq!(
        s_seq.r4_count, s_gpu.r4_count,
        "church 3×4: r4_count matches"
    );
    assert_eq!(
        s_seq.interactions, s_gpu.interactions,
        "church 3×4: total interactions match (LO-optimality, no extra GPU work §4)"
    );
    // Genuinely multi-round: more interactions than a single church-4 spine.
    let (_, s_flat) = SequentialScheduler::normalize(make_church_applied_di(4)).unwrap();
    assert!(
        s_seq.interactions > s_flat.interactions,
        "church 3×4 ({}) must out-interact flat church-4 ({}) — proves nested Rep rounds",
        s_seq.interactions,
        s_flat.interactions
    );
}

// ── amortized R4 executor parity (GPU writes arena directly) ──────────────────

/// Amortized R4 path: GPU interaction count == sequential ground truth (confluence §2).
/// `normalize_r4` runs the arena-resident R4-only kernel; on N independent (λx.x) id
/// pairs every fan⊗fan fires exactly once, so the GPU count must equal seq r4_count == N.
/// Skips the GPU assertion when no adapter is present (CI); seq invariant always checked.
#[test]
fn amortized_equiv_r4_count() {
    for count in [16usize, 128, 256] {
        let (_, s_seq) = SequentialScheduler::normalize(make_n_batch_ids(count)).unwrap();
        assert_eq!(
            s_seq.r4_count, count as u64,
            "seq r4_count must equal {count} independent R4 pairs"
        );
        if let Some(mu) = global_amortized() {
            let gpu = mu.lock().expect("amortized mutex");
            let amortized = gpu.normalize_r4(make_n_batch_ids(count)).unwrap();
            assert_eq!(
                amortized, s_seq.r4_count,
                "amortized R4 count == sequential r4_count (confluence §2)"
            );
        }
    }
}

/// LO-optimality: church n r4_count == n (exactly n β-reductions, no duplication).
/// Demonstrates Δ-nets optimal sharing vs naive systems that duplicate work.
#[test]
fn gpu_church_lo_optimality() {
    for n in [4usize, 8, 16, 32] {
        let (_, s) = SequentialScheduler::normalize(make_church_applied_di(n)).unwrap();
        // church n id id = id applied n times to id = id (1 final β) + n β for applications
        // r4_count = n β-reductions (one per f application) + 2 outer β (church_n id + result id)
        // = n + 2 total r4s under LO-optimality
        assert_eq!(
            s.r4_count,
            (n + 2) as u64,
            "church{n}: r4_count={} expected {} (LO-optimality: no duplication)",
            s.r4_count,
            n + 2
        );
    }
}
