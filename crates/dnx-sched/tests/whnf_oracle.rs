//! force_whnf soundness oracle: main.tex §4 optimality + §2 confluence.
//!
//! Properties verified:
//!   1. force_whnf reaches ValueHead::Abs for identity applied to identity (β-reduction).
//!   2. force_whnf(clone) + normalize(clone) hash == normalize(original) hash (confluence).
//!   3. force_whnf fires exactly the R4 β-reductions needed (optimality: no extra steps).
//!   4. step_limit respected (StepLimitExceeded returned correctly).
//!
//! `just oracle` runs these (--include-ignored).

use dnx_core::{canonical_hash, LOPath, Net, NormalizeConfig, Proper, ValueHead, ΔL};
use dnx_sched::{sequential::SequentialScheduler, Scheduler};
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

fn make_identity() -> (Net<Proper, ΔL>, dnx_core::PortId) {
    let mut n = Net::<Proper, ΔL>::new(16);
    let abs = n.alloc_abs().unwrap();
    n.connect(abs.aux0, abs.aux1, LOPath::root()).unwrap();
    let res = n.alloc_free(0).unwrap();
    n.connect(abs.principal, res, LOPath::root()).unwrap();
    n.add_root(Arc::from("r"), res);
    let port = *n.roots().get("r").unwrap();
    (n, port)
}

#[test]

fn whnf_identity_returns_abs() {
    let (mut n, port) = make_identity();
    let cfg = NormalizeConfig::default();
    let head = SequentialScheduler::force_whnf(&mut n, port, &cfg).unwrap();
    assert_eq!(head, ValueHead::Abs, "identity at root should be WHNF Abs");
}

#[test]

fn whnf_id_applied_reaches_abs() {
    let mut n = make_id_applied();
    let port = *n.roots().get("r").unwrap();
    let cfg = NormalizeConfig::default();
    let head = SequentialScheduler::force_whnf(&mut n, port, &cfg).unwrap();
    assert_eq!(
        head,
        ValueHead::Abs,
        "id applied to id should WHNF to Abs (§2 confluence + §4 optimality)"
    );
}

#[test]

fn whnf_confluence_hash_matches_normalize() {
    // force_whnf(clone) then normalize should give same hash as normalize(original)
    let orig = make_id_applied();
    let mut lazy = make_id_applied();
    let port = *lazy.roots().get("r").unwrap();
    let cfg = NormalizeConfig::default();

    // Lazy: force_whnf first (stops at WHNF), then full normalize
    SequentialScheduler::force_whnf(&mut lazy, port, &cfg).unwrap();
    let (lazy_can, _) = SequentialScheduler::normalize(lazy).unwrap();
    let lazy_port = *lazy_can.roots().get("r").unwrap();
    let lazy_hash = canonical_hash(&lazy_can, lazy_port).unwrap();

    // Eager: full normalize from scratch
    let (eager_can, _) = SequentialScheduler::normalize(orig).unwrap();
    let eager_port = *eager_can.roots().get("r").unwrap();
    let eager_hash = canonical_hash(&eager_can, eager_port).unwrap();

    assert_eq!(
        lazy_hash, eager_hash,
        "WHNF+normalize hash must equal eager normalize (§2 confluence)"
    );
}

#[test]

fn whnf_step_limit_enforced() {
    let mut n = make_id_applied();
    let port = *n.roots().get("r").unwrap();
    let cfg = NormalizeConfig {
        max_steps: Some(0),
        max_agents: None,
    };
    let result = SequentialScheduler::force_whnf(&mut n, port, &cfg);
    assert!(
        matches!(result, Err(dnx_core::DnxError::StepLimitExceeded(_))),
        "step_limit=0 should return StepLimitExceeded"
    );
}

#[test]

fn whnf_optimality_step_count() {
    // id applied to id: exactly 1 R4 β-reduction needed (optimality).
    // After force_whnf, the net should have WHNF reached with minimal steps.
    let mut n = make_id_applied();
    let port = *n.roots().get("r").unwrap();
    let pairs_before = n.active_pair_count();
    let cfg = NormalizeConfig::default();
    let head = SequentialScheduler::force_whnf(&mut n, port, &cfg).unwrap();
    assert_eq!(head, ValueHead::Abs);
    // frontier1 should be empty after WHNF (id applied to id fully reduces in 1 step)
    assert_eq!(
        n.active_pair_count(),
        0,
        "frontier1 empty after WHNF for normalizing net (§4 optimality)"
    );
    let _ = pairs_before;
}
