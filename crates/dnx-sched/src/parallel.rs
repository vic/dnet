/// ParallelScheduler — rayon-based batch parallel reduction (cpu.md WorkerOutput pattern).
/// Antichain guarantee: entire frontier1 is prefix-independent → whole batch fires in parallel.
/// Zero mutex: workers read &Arena, write only to pre-reserved WorkerOutput[i].
/// C2/C3/C4/C1: coordinator-only (non-local, quiescent required).
use crate::Scheduler;
use dnx_core::{normalize_parallel, CRules, Canonical, DnxError, Net, Proper, ReduceStats};

/// P>1 parallel scheduler using rayon (true parallel, not sequential fallback).
pub struct ParallelScheduler {
    pub num_threads: usize,
}

impl ParallelScheduler {
    pub fn new(num_threads: usize) -> Self {
        ParallelScheduler { num_threads }
    }
}

impl Scheduler for ParallelScheduler {
    fn normalize<C: CRules>(
        net: Net<Proper, C>,
    ) -> Result<(Net<Canonical, C>, ReduceStats), DnxError> {
        normalize_parallel(net, rayon::current_num_threads())
    }
}

/// Normalize with explicit thread count.
pub fn normalize_par<C: CRules>(
    net: Net<Proper, C>,
    num_threads: usize,
) -> Result<(Net<Canonical, C>, ReduceStats), DnxError> {
    normalize_parallel(net, num_threads)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sequential::SequentialScheduler;
    use dnx_core::{canonical_hash, LOPath, Net, Proper, ΔL};
    use std::sync::Arc;

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
        let id3 = n.alloc_abs().unwrap();
        let app1 = n.alloc_app().unwrap();
        let app2 = n.alloc_app().unwrap();
        n.connect(id1.aux0, id1.aux1, LOPath::root()).unwrap();
        n.connect(id2.aux0, id2.aux1, LOPath::root()).unwrap();
        n.connect(id3.aux0, id3.aux1, LOPath::root()).unwrap();
        n.connect(app1.principal, id1.principal, LOPath::root())
            .unwrap();
        n.connect(app1.aux1, id2.principal, LOPath::root()).unwrap();
        n.connect(app2.principal, app1.aux0, LOPath::root())
            .unwrap();
        n.connect(app2.aux1, id3.principal, LOPath::root()).unwrap();
        let res = n.alloc_free(0).unwrap();
        n.connect(app2.aux0, res, LOPath::root()).unwrap();
        n.add_root(Arc::from("r"), res);
        n
    }

    /// Parallel hash == sequential hash: perfect confluence (main.tex §2).
    #[test]
    fn parallel_equiv_identity_hash() {
        let (seq, _) = SequentialScheduler::normalize(make_id_applied()).unwrap();
        let (par, _) = normalize_par(make_id_applied(), 2).unwrap();
        let r_seq = seq.roots().get("r").copied().unwrap();
        let r_par = par.roots().get("r").copied().unwrap();
        assert_eq!(
            canonical_hash(&seq, r_seq).unwrap(),
            canonical_hash(&par, r_par).unwrap(),
            "parallel NF hash must equal sequential NF hash (confluence)"
        );
    }

    #[test]
    fn parallel_equiv_chained_hash() {
        let (seq, _) = SequentialScheduler::normalize(make_chained()).unwrap();
        let (par, _) = normalize_par(make_chained(), 4).unwrap();
        let r_seq = seq.roots().get("r").copied().unwrap();
        let r_par = par.roots().get("r").copied().unwrap();
        assert_eq!(
            canonical_hash(&seq, r_seq).unwrap(),
            canonical_hash(&par, r_par).unwrap(),
            "chained: parallel hash == sequential hash"
        );
    }

    #[test]
    fn parallel_equiv_stats_match() {
        let (_, s_seq) = SequentialScheduler::normalize(make_id_applied()).unwrap();
        let (_, s_par) = normalize_par(make_id_applied(), 2).unwrap();
        assert_eq!(s_seq.r4_count, s_par.r4_count, "r4_count must match");
    }
}
