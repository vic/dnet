/// GPU batch output for one rule firing.
/// Produced by GPU kernel, applied by CPU coordinator (same pattern as WorkerOutput).
pub struct GpuOutput {
    /// New agents: (tag, data, delta0, delta1). Committed to arena[base + k].
    pub new_agents: Vec<(u8, u16, i16, i16)>,
    /// Consumed slot indices to retire.
    pub retired: Vec<u32>,
    /// Connections: (a, b, lo) applied via net.connect().
    pub connects: Vec<(crate::PortId, crate::PortId, crate::LOPath)>,
    /// Ports to propagate eraser onto.
    pub set_erasers: Vec<crate::PortId>,
    /// Direct link (no pair detection) for R4 identity self-loop.
    pub link_direct: Option<(crate::PortId, crate::PortId)>,
}

/// GPU-batched normalize: coordinator loop with external GPU kernel per batch.
///
/// Mirrors normalize_parallel but delegates rule firing to `batch_fn`.
/// `batch_fn` receives (pairs, arena_words, bases) and returns Vec<GpuOutput>.
/// C2/C3 run on CPU coordinator before dispatching reps to GPU.
/// Phase2 (C4) + C1 always on CPU coordinator.
#[allow(private_bounds)]
pub fn normalize_gpu_batched<C: super::CRules, F>(
    mut net: crate::net::Net<crate::Proper, C>,
    mut batch_fn: F,
) -> Result<(crate::net::Net<crate::Canonical, C>, super::ReduceStats), crate::DnxError>
where
    F: FnMut(
        &[(crate::PortId, crate::PortId, crate::LOPath)],
        &[u32],
        &[u32],
    ) -> Result<Vec<GpuOutput>, crate::DnxError>,
{
    use super::{is_stale_c4, ReduceStats};
    use crate::net::{certify_canonical, into_canonical};
    use crate::slot::Slot;

    const MAX_NEW: u32 = 4;
    let mut stats = ReduceStats::default();

    loop {
        let batch: Vec<(crate::PortId, crate::PortId, crate::LOPath)> =
            std::mem::take(&mut net.frontier1)
                .into_values()
                .map(|p| (p.p0.get(), p.p1.get(), p.lo))
                .collect();
        if batch.is_empty() {
            break;
        }

        let bases: Vec<u32> = (0..batch.len())
            .map(|_| net.arena.reserve(MAX_NEW))
            .collect::<Result<_, _>>()?;

        let arena_words = net.arena.encode_gpu();
        let outputs = batch_fn(&batch, &arena_words, &bases)?;

        for (i, out) in outputs.into_iter().enumerate() {
            let base = bases[i];
            let used = out.new_agents.len() as u32;
            let is_r4 = out.retired.len() == 2
                && used == 0
                && out.set_erasers.is_empty()
                && (out.connects.len() == 2 || out.link_direct.is_some());

            for (j, (tag, data, d0, d1)) in out.new_agents.into_iter().enumerate() {
                let mut s = Slot::EMPTY;
                s.tag = tag;
                s.data = data;
                s.delta0 = d0;
                s.delta1 = d1;
                net.arena.commit_slot(base + j as u32, s);
            }
            for p in &out.set_erasers {
                net.set_eraser_on_port(*p);
            }
            if let Some((a, b)) = out.link_direct {
                net.link_no_pair(a, b);
            }
            let fired =
                !out.retired.is_empty() || !out.connects.is_empty() || out.link_direct.is_some();
            if fired {
                stats.interactions += 1;
            }
            if is_r4 {
                stats.r4_count += 1;
            }
            for (a, b, lo) in out.connects {
                net.connect(a, b, lo)?;
            }
            for idx in out.retired {
                net.retire(idx);
            }
            net.arena.release_reserved(base, used, MAX_NEW);
        }
    }

    if C::HAS_REP {
        while let Some((_, cand)) = net.frontier2.pop_first() {
            if is_stale_c4(&cand, &net) {
                continue;
            }
            if C::HAS_ERA {
                C::c3(&mut net, cand.rep_principal, &cand.lo)?;
            }
            if is_stale_c4(&cand, &net) {
                continue;
            }
            C::c2(&mut net, cand.rep_principal, &cand.lo)?;
            if is_stale_c4(&cand, &net) {
                continue;
            }
            C::c4(&mut net, &cand)?;
        }
    }
    if net.net_pending_c1() {
        C::c1(&mut net);
    }

    let w = certify_canonical(&net)?;
    Ok((into_canonical(net, w), stats))
}
