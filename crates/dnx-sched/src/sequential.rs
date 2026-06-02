use crate::Scheduler;
use dnx_core::{normalize, CRules, Canonical, DnxError, Net, Proper, ReduceStats};

/// P=1 sequential scheduler: exact reducer.md normalize loop, no rayon.
pub struct SequentialScheduler;

impl Scheduler for SequentialScheduler {
    fn normalize<C: CRules>(
        net: Net<Proper, C>,
    ) -> Result<(Net<Canonical, C>, ReduceStats), DnxError> {
        normalize(net)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dnx_core::{LOPath, ΔL};

    #[test]
    fn sequential_identity_zero_steps() {
        let mut n = Net::<Proper, ΔL>::new(8);
        let abs = n.alloc_abs().unwrap();
        n.connect(abs.aux0, abs.aux1, LOPath::root()).unwrap();
        n.add_root("r".into(), abs.principal);
        let (_, stats) = SequentialScheduler::normalize(n).unwrap();
        assert_eq!(stats.interactions, 0);
    }

    #[test]
    fn sequential_id_applied_one_beta() {
        let mut n = Net::<Proper, ΔL>::new(32);
        let abs = n.alloc_abs().unwrap();
        let app = n.alloc_app().unwrap();
        let arg = n.alloc_abs().unwrap(); // second identity as argument
                                          // abs x . x
        n.connect(abs.aux0, abs.aux1, LOPath::root()).unwrap();
        // arg y . y
        n.connect(arg.aux0, arg.aux1, LOPath::root()).unwrap();
        // app.principal ↔ abs.principal (active pair)
        n.connect(app.principal, abs.principal, LOPath::root())
            .unwrap();
        // app.aux1 ← arg
        n.connect(app.aux1, arg.principal, LOPath::root()).unwrap();
        // result
        let res = n.alloc_free(0).unwrap();
        n.connect(app.aux0, res, LOPath::root()).unwrap();
        n.add_root("r".into(), res);
        let (_, stats) = SequentialScheduler::normalize(n).unwrap();
        assert_eq!(stats.r4_count, 1);
    }
}
