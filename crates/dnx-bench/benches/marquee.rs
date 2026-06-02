//! Criterion benchmarks for the marquee dnx performance numbers, measured through
//! the PUBLIC APIs of dnx-core / dnx-sched only (no runtime crate is edited):
//!
//!   1. List construct + readback — build a length-N Scott cons-list then normalize
//!      it to canonical form (the readback). Cost is the O(N) net construction.
//!   2. Parallel speedup — sequential `dnx_core::normalize` vs `dnx_sched::normalize_par(P)`
//!      over a wide antichain (all units fire in one parallel batch).
//!
//! Builders are replicated from the example/oracle (test/example code is not
//! importable) and return `Result`; every fallible op is propagated, never
//! unwrapped — a construction error surfaces as a `black_box`-ed `Err` value, the
//! harness never panics.
//!
//! Run (optimizer on): `cargo bench -p dnx-bench`.

use std::hint::black_box;
use std::sync::Arc;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

use dnx_core::{normalize, DnxError, LOPath, Net, PortId, Proper, ReduceStats, ΔK, ΔL};
use dnx_sched::normalize_par;

// ── Scott-numeral / loop builders (mirror recursion_ref_vs_y.rs) ──────────────────

/// Scott zero as a native net: `λz.λs. (erase s) z`. Returns the λz principal.
fn net_scott_zero(net: &mut Net<Proper, ΔK>) -> Result<PortId, DnxError> {
    let lo = LOPath::root();
    let z = net.alloc_abs()?;
    let s = net.alloc_abs()?;
    net.connect(z.aux0, s.principal, lo.clone())?;
    net.connect(s.aux0, z.aux1, lo.clone())?;
    net.connect(s.aux1, Net::<Proper, ΔK>::eraser_port(), lo)?;
    Ok(z.principal)
}

/// Scott successor of `p`: `λz.λs. (erase z) (s p)`. Returns the λz principal.
fn net_scott_succ(net: &mut Net<Proper, ΔK>, p: PortId) -> Result<PortId, DnxError> {
    let lo = LOPath::root();
    let z = net.alloc_abs()?;
    let s = net.alloc_abs()?;
    let app = net.alloc_app()?;
    net.connect(z.aux0, s.principal, lo.clone())?;
    net.connect(s.aux1, app.principal, lo.clone())?;
    net.connect(app.aux1, p, lo.clone())?;
    net.connect(app.aux0, s.aux0, lo.clone())?;
    net.connect(z.aux1, Net::<Proper, ΔK>::eraser_port(), lo)?;
    Ok(z.principal)
}

// ── Scott-list builders (cons/nil) ───────────────────────────────────────────

/// Scott nil: `λc.λn. (erase c) n`. Returns the λc principal.
fn net_nil(net: &mut Net<Proper, ΔK>) -> Result<PortId, DnxError> {
    let lo = LOPath::root();
    let c = net.alloc_abs()?;
    let n = net.alloc_abs()?;
    net.connect(c.aux0, n.principal, lo.clone())?;
    net.connect(n.aux0, c.aux1, lo.clone())?;
    net.connect(c.aux1, Net::<Proper, ΔK>::eraser_port(), lo)?;
    Ok(c.principal)
}

/// Scott cons of head `h` onto tail `t`: `λc.λn. (erase n) ((c h) t)`.
fn net_cons(net: &mut Net<Proper, ΔK>, h: PortId, t: PortId) -> Result<PortId, DnxError> {
    let lo = LOPath::root();
    let c = net.alloc_abs()?;
    let n = net.alloc_abs()?;
    let app_ch = net.alloc_app()?;
    let app_cht = net.alloc_app()?;
    net.connect(c.aux0, n.principal, lo.clone())?;
    net.connect(n.aux1, app_ch.principal, lo.clone())?;
    net.connect(app_ch.aux1, h, lo.clone())?;
    net.connect(app_ch.aux0, app_cht.principal, lo.clone())?;
    net.connect(app_cht.aux1, t, lo.clone())?;
    net.connect(app_cht.aux0, n.aux0, lo.clone())?;
    net.connect(n.aux1, Net::<Proper, ΔK>::eraser_port(), lo)?;
    Ok(c.principal)
}

/// Build a length-`len` Scott cons-list `[S Z, …]` with a `nil` tail; returns
/// `(net, res_port)`. Reduction (readback) is the caller's job.
fn build_list(len: usize) -> Result<(Net<Proper, ΔK>, PortId), DnxError> {
    let mut net = Net::<Proper, ΔK>::new(8_000_000);
    let lo = LOPath::root();
    let mut spine = net_nil(&mut net)?;
    for _ in 0..len {
        let zero = net_scott_zero(&mut net)?;
        let head = net_scott_succ(&mut net, zero)?;
        spine = net_cons(&mut net, head, spine)?;
    }
    let res = net.alloc_free(0)?;
    net.connect(spine, res, lo)?;
    net.add_root(Arc::from("res"), res);
    Ok((net, res))
}

/// Normalize a constructed list to canonical form (the readback).
fn read_list(net: Net<Proper, ΔK>, _res: PortId) -> Result<ReduceStats, DnxError> {
    let (_canon, stats) = normalize(net)?;
    Ok(stats)
}

/// Construction only (timed in its own group): build the list, discard it.
fn bench_list_construct(c: &mut Criterion) {
    let mut group = c.benchmark_group("list_construct");
    for &len in &[1_000usize, 10_000] {
        group.throughput(Throughput::Elements(len as u64));
        group.bench_with_input(BenchmarkId::from_parameter(len), &len, |b, &len| {
            b.iter(|| -> Result<PortId, DnxError> {
                let (net, res) = build_list(len)?;
                Ok(black_box((net, res)).1)
            });
        });
    }
    group.finish();
}

/// Construct (untimed) + readback (timed): the normalize-to-canonical cost.
fn bench_list_readback(c: &mut Criterion) {
    let mut group = c.benchmark_group("list_readback");
    for &len in &[1_000usize, 10_000] {
        group.throughput(Throughput::Elements(len as u64));
        group.bench_with_input(BenchmarkId::from_parameter(len), &len, |b, &len| {
            b.iter_batched(
                || build_list(len),
                |built| -> Result<ReduceStats, DnxError> {
                    let (net, res) = built?;
                    read_list(net, res)
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

// ── parallel speedup builders (wide antichain; mirror bench.rs) ───────────────────

/// Mutually-distinct LOPath for copy `i` over `bits` binary steps; distinct keys ⇒
/// all copies coexist in frontier1 ⇒ ONE parallel batch (the antichain).
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

/// `k` independent `(λx.x) free` copies at distinct lo-paths under roots `r{i}`:
/// `k` β-interactions, all in one antichain (max parallelism).
fn wide_id(k: u64, bits: u32) -> Result<Net<Proper, ΔL>, DnxError> {
    let mut n = Net::<Proper, ΔL>::new((k as u32) * 32 + 64);
    for i in 0..k {
        let lo = distinct_path(i, bits)?;
        let abs = n.alloc_abs()?;
        let app = n.alloc_app()?;
        let arg = n.alloc_free((i as u32) * 2)?;
        let res = n.alloc_free((i as u32) * 2 + 1)?;
        n.connect(abs.aux0, abs.aux1, lo.clone())?;
        n.connect(app.aux0, res, lo.clone())?;
        n.connect(app.aux1, arg, lo.clone())?;
        n.connect(abs.principal, app.principal, lo.clone())?;
        n.add_root(Arc::from(format!("r{i}")), res);
    }
    Ok(n)
}

/// Sequential `normalize` vs `normalize_par(P)` over the SAME wide net, P ∈ {1,2,4,8}.
/// P=1 in the parallel group is the seq baseline; criterion's ratio across P shows
/// the speedup. Net is rebuilt per iter (normalize consumes it), OUTSIDE timing.
fn bench_parallel(c: &mut Criterion) {
    const K: u64 = 200_000;
    const BITS: u32 = 20;

    let mut seq = c.benchmark_group("normalize_sequential");
    seq.throughput(Throughput::Elements(K));
    seq.bench_function("wide_id_200k", |b| {
        b.iter_batched(
            || wide_id(K, BITS),
            |built| -> Result<ReduceStats, DnxError> { Ok(normalize(built?)?.1) },
            criterion::BatchSize::SmallInput,
        );
    });
    seq.finish();

    let mut par = c.benchmark_group("normalize_parallel");
    par.throughput(Throughput::Elements(K));
    for &p in &[1usize, 2, 4, 8] {
        par.bench_with_input(BenchmarkId::from_parameter(p), &p, |b, &p| {
            b.iter_batched(
                || wide_id(K, BITS),
                |built| -> Result<ReduceStats, DnxError> { Ok(normalize_par(built?, p)?.1) },
                criterion::BatchSize::SmallInput,
            );
        });
    }
    par.finish();
}

criterion_group!(
    benches,
    bench_list_construct,
    bench_list_readback,
    bench_parallel
);
criterion_main!(benches);
