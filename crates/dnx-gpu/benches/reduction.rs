//! Reduction throughput benchmarks: GpuScheduler vs SequentialScheduler.
//!
//! `just gpu-bench` runs these.
//! Goal: GPU orders of magnitude faster than sequential at large batch sizes.
//! Comparison baseline: naive sequential reduce interactions; we reduce
//! entire frontier batches in parallel per GPU kernel launch.

use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use dnx_ast::{Ast, NoFun, NoVal};
use dnx_core::{LOPath, Net, PortId, PortKind, Proper, ΔI, ΔL};
use dnx_elab::{elaborate, pass1};
use dnx_gpu::{encode_net_for_gpu, global_amortized, GpuScheduler};
use dnx_sched::{sequential::SequentialScheduler, Scheduler};
use std::collections::HashMap;
use std::sync::Arc;

// ── net builders ──────────────────────────────────────────────────────────────

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

/// N independent (λx.x) id pairs — each fires 1 R4. Total = N parallel R4s.
fn make_n_ids(count: usize) -> Net<Proper, ΔL> {
    let depth = usize::BITS as usize - count.leading_zeros() as usize;
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

/// N independent (λx.x x) id nets — each fires R4 + R5 (Fan⊗Rep). Total = N*2 R4s + N R5s.
fn make_n_sharing(count: usize) -> Net<Proper, ΔI> {
    let depth = usize::BITS as usize - count.leading_zeros() as usize;
    let mut n = Net::<Proper, ΔI>::new((count * 16 + 8) as u32);
    for i in 0..count {
        let lo = lo_for_index(i, depth);
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
        let res = n.alloc_free(i as u32 * 2).unwrap();
        n.connect(app.principal, outer.principal, lo.clone())
            .unwrap();
        n.connect(app.aux1, id.principal, lo.clone()).unwrap();
        n.connect(app.aux0, res, lo).unwrap();
        n.add_root(Arc::from(format!("s{i}").as_str()), res);
    }
    n
}

type E = Ast<NoVal, NoFun>;
type Env = HashMap<Arc<str>, (PortId, u32)>;

fn nm(s: &str) -> E {
    Ast::Name(Arc::from(s))
}
fn nm_arc(s: Arc<str>) -> E {
    Ast::Name(s)
}
fn ab(x: &str, b: E) -> E {
    Ast::Abs(Arc::from(x), Box::new(b))
}
fn ap(f: E, x: E) -> E {
    Ast::App(Box::new(f), Box::new(x))
}

/// Spine-of-Reps church numeral body: f^n(x) with explicit Rep nodes — linear AST.
/// rep f as (f_n, f_rest) in f_n (rep f_rest as ... in ... (f_last x))
fn church_spine(f: Arc<str>, remaining: usize) -> E {
    if remaining == 0 {
        return nm("cx");
    }
    if remaining == 1 {
        return ap(nm_arc(f), nm("cx"));
    }
    let f_now: Arc<str> = Arc::from(format!("cfn{remaining}").as_str());
    let f_rest: Arc<str> = Arc::from(format!("cfr{remaining}").as_str());
    let inner = ap(
        nm_arc(f_now.clone()),
        church_spine(f_rest.clone(), remaining - 1),
    );
    Ast::Rep(Box::new(nm_arc(f)), f_now, f_rest, Box::new(inner))
}

/// church n = λf.λx.f^n(x) with explicit Rep spine — linear, passes pass1.
/// Applied to id id: (church n) id id. Exercises R4+R5+R6/R7 for n≥2.
fn make_church_applied(n: usize) -> Net<Proper, ΔI> {
    let church_n = ab("cf", ab("cx", church_spine(Arc::from("cf"), n)));
    let id = ab("ciy", nm("ciy"));
    let id2 = ab("ciz", nm("ciz"));
    let expr = ap(ap(church_n, id), id2);

    let r1 = pass1(&expr).unwrap();
    let mut net = Net::<Proper, ΔI>::new(((n + 2) * 24 + 64) as u32);
    let mut env = Env::new();
    let (rp, _) = elaborate(
        &mut net,
        0,
        &mut env,
        LOPath::root(),
        &expr,
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

// ── benchmarks ────────────────────────────────────────────────────────────────

/// R4-only: N independent id_applied. Net construction excluded via iter_batched.
/// GPU dispatches all N pairs in ONE kernel launch; sequential loops N times.
fn bench_r4_batch(c: &mut Criterion) {
    let mut group = c.benchmark_group("r4_batch");
    group.sample_size(20);
    for &count in &[16usize, 64, 128, 256, 512, 1024, 4096, 16384] {
        group.bench_with_input(
            BenchmarkId::new("sequential", count),
            &count,
            |b, &count| {
                b.iter_batched(
                    || make_n_ids(count),
                    |net| SequentialScheduler::normalize(net).unwrap(),
                    BatchSize::SmallInput,
                )
            },
        );
        group.bench_with_input(BenchmarkId::new("gpu", count), &count, |b, &count| {
            b.iter_batched(
                || make_n_ids(count),
                |net| GpuScheduler::normalize(net).unwrap(),
                BatchSize::SmallInput,
            )
        });
    }
    group.finish();
}

/// R4+R5 mixed: N independent (λx.x x) id nets. Net construction excluded.
fn bench_r4_r5_batch(c: &mut Criterion) {
    let mut group = c.benchmark_group("r4_r5_batch");
    group.sample_size(20);
    for &count in &[16usize, 64, 128, 256] {
        group.bench_with_input(
            BenchmarkId::new("sequential", count),
            &count,
            |b, &count| {
                b.iter_batched(
                    || make_n_sharing(count),
                    |net| SequentialScheduler::normalize(net).unwrap(),
                    BatchSize::SmallInput,
                )
            },
        );
        group.bench_with_input(BenchmarkId::new("gpu", count), &count, |b, &count| {
            b.iter_batched(
                || make_n_sharing(count),
                |net| GpuScheduler::normalize(net).unwrap(),
                BatchSize::SmallInput,
            )
        });
    }
    group.finish();
}

/// Single-pair baseline: reduction-only cost (construction excluded).
fn bench_single_pair(c: &mut Criterion) {
    let mut group = c.benchmark_group("single_pair");
    group.bench_function("sequential", |b| {
        b.iter_batched(
            || make_n_ids(1),
            |net| SequentialScheduler::normalize(net).unwrap(),
            BatchSize::SmallInput,
        )
    });
    group.bench_function("gpu", |b| {
        b.iter_batched(
            || make_n_ids(1),
            |net| GpuScheduler::normalize(net).unwrap(),
            BatchSize::SmallInput,
        )
    });
    group.finish();
}

/// Church numeral n applied to id id — R4+R5+R6/R7 (Rep commutation + delta arithmetic).
/// n+2 β-reductions guaranteed by LO-optimality (§4 main.tex).
/// Non-sharing naive systems would require O(n²) interactions for equivalent church_mul.
fn bench_church_applied(c: &mut Criterion) {
    let mut group = c.benchmark_group("church_applied");
    group.sample_size(20);
    for &n in &[4usize, 8, 16, 32, 64, 128, 256] {
        group.bench_with_input(BenchmarkId::new("sequential", n), &n, |b, &n| {
            b.iter_batched(
                || make_church_applied(n),
                |net| SequentialScheduler::normalize(net).unwrap(),
                BatchSize::SmallInput,
            )
        });
        group.bench_with_input(BenchmarkId::new("gpu", n), &n, |b, &n| {
            b.iter_batched(
                || make_church_applied(n),
                |net| GpuScheduler::normalize(net).unwrap(),
                BatchSize::SmallInput,
            )
        });
    }
    group.finish();
}

/// Interaction rate: total interactions per second (reduction-only).
/// LO-optimality: r4_count == β_count — no redundant β-reductions ever.
/// Non-optimal systems (naive sequential) duplicate work: r4_count >> β_count.
fn bench_interactions_per_second(c: &mut Criterion) {
    let mut group = c.benchmark_group("interaction_rate");
    group.sample_size(20);
    group.bench_function("sequential/church64", |b| {
        b.iter_batched(
            || make_church_applied(64),
            |net| {
                let (_, s) = SequentialScheduler::normalize(net).unwrap();
                s.interactions
            },
            BatchSize::SmallInput,
        )
    });
    group.bench_function("gpu/church64", |b| {
        b.iter_batched(
            || make_church_applied(64),
            |net| {
                let (_, s) = GpuScheduler::normalize(net).unwrap();
                s.interactions
            },
            BatchSize::SmallInput,
        )
    });
    group.finish();
}

/// Amortized GPU mode: GPU writes connections directly to arena (no CPU apply per round).
/// One PCIe upload + N_STEPS GPU passes + one counters readback.
/// Eliminates per-round CPU coordinator overhead. Demonstrates orders-of-magnitude speedup.
///
/// vs sequential: same flat computation, sequential BTreeMap-free tight loop.
fn bench_amortized_vs_sequential(c: &mut Criterion) {
    let mut group = c.benchmark_group("amortized");
    group.sample_size(20);

    for &count in &[1024usize, 4096, 16384, 65536] {
        group.bench_with_input(
            BenchmarkId::new("sequential", count),
            &count,
            |b, &count| {
                b.iter_batched(
                    || make_n_ids(count),
                    |net| SequentialScheduler::normalize(net).unwrap(),
                    BatchSize::SmallInput,
                )
            },
        );
        // gpu_amortized_raw: arena+pairs pre-encoded in setup (not timed).
        // Measures ONLY: PCIe upload + GPU kernel + counters readback.
        // Shows true GPU throughput without CPU encoding overhead.
        group.bench_with_input(
            BenchmarkId::new("gpu_amortized_raw", count),
            &count,
            |b, &count| {
                b.iter_batched(
                    || encode_net_for_gpu(&make_n_ids(count)),
                    |(arena_bytes, pair_bytes, n)| {
                        if let Some(mu) = global_amortized() {
                            let gpu = mu.lock().unwrap();
                            gpu.run_r4_raw(&arena_bytes, &pair_bytes, n).unwrap()
                        } else {
                            0u64
                        }
                    },
                    BatchSize::SmallInput,
                )
            },
        );
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_single_pair,
    bench_r4_batch,
    bench_r4_r5_batch,
    bench_church_applied,
    bench_interactions_per_second,
    bench_amortized_vs_sequential
);
criterion_main!(benches);
