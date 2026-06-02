#![forbid(unsafe_code)]

pub mod parallel;
pub mod sequential;

pub use parallel::{normalize_par, ParallelScheduler};
pub use sequential::SequentialScheduler;

use dnx_core::{
    CRules, Canonical, DnxError, Net, NormalizeConfig, PortId, Proper, ReduceStats, ValueHead,
};

/// Scheduler trait: full normalization + WHNF lazy forcing.
pub trait Scheduler {
    /// Full normalization — consumes net, produces Net<Canonical>.
    /// Used only for content-addressing (canonical hash) and artifact export.
    fn normalize<C: CRules>(
        net: Net<Proper, C>,
    ) -> Result<(Net<Canonical, C>, ReduceStats), DnxError>;

    /// Lazy WHNF forcing — drains frontier1 LO-ordered until head at `port` is a value.
    /// Off-spine subnets untouched (call-by-need). Net stays Net<Proper>.
    /// Default: sequential (all schedulers share sequential WHNF; parallelism not needed for WHNF).
    fn force_whnf<C: CRules>(
        net: &mut Net<Proper, C>,
        port: PortId,
        cfg: &NormalizeConfig,
    ) -> Result<ValueHead, DnxError> {
        dnx_core::force_whnf(net, port, cfg)
    }
}

/// Worker configuration for scheduler selection.
pub enum Workers {
    Sequential,
    Parallel(usize),
    ParallelMax,
}
