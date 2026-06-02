//! Parallel soundness gate: parallel ≡ sequential by canonical hash (main.tex §2 confluence).
//! `just oracle` runs these (--include-ignored).

use dnx_core::{canonical_hash, normalize, LOPath, Net, Proper, ΔI, ΔL};
use dnx_sched::{normalize_par, sequential::SequentialScheduler, Scheduler};
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

fn root_hash(net: &dnx_core::Net<dnx_core::Canonical, ΔL>, name: &str) -> [u8; 32] {
    let port = *net.roots().get(name).expect("root missing");
    canonical_hash(net, port).expect("canonical_hash on a pure NF")
}

#[test]

fn parallel_equiv_p1() {
    let (seq, s_seq) = SequentialScheduler::normalize(make_id_applied()).unwrap();
    let (par, s_par) = normalize_par(make_id_applied(), 1).unwrap();
    assert_eq!(
        root_hash(&seq, "r"),
        root_hash(&par, "r"),
        "P=1: hash must match"
    );
    assert_eq!(s_seq.interactions, s_par.interactions);
    assert_eq!(s_seq.r4_count, s_par.r4_count);
}

#[test]

fn parallel_equiv_p2() {
    let (seq, s_seq) = SequentialScheduler::normalize(make_id_applied()).unwrap();
    let (par, s_par) = normalize_par(make_id_applied(), 2).unwrap();
    assert_eq!(
        root_hash(&seq, "r"),
        root_hash(&par, "r"),
        "P=2: hash must match"
    );
    assert_eq!(s_seq.r4_count, s_par.r4_count);
}

#[test]

fn parallel_equiv_p4() {
    let (seq, s_seq) = SequentialScheduler::normalize(make_id_applied()).unwrap();
    let (par, s_par) = normalize_par(make_id_applied(), 4).unwrap();
    assert_eq!(
        root_hash(&seq, "r"),
        root_hash(&par, "r"),
        "P=4: hash must match"
    );
    assert_eq!(s_seq.r4_count, s_par.r4_count);
}

#[test]

fn parallel_equiv_p8() {
    let (seq, s_seq) = SequentialScheduler::normalize(make_id_applied()).unwrap();
    let (par, s_par) = normalize_par(make_id_applied(), 8).unwrap();
    assert_eq!(
        root_hash(&seq, "r"),
        root_hash(&par, "r"),
        "P=8: hash must match"
    );
    assert_eq!(s_seq.r4_count, s_par.r4_count);
}

/// ΔI sharing: (λx.x x) id — rep involved, tests C2 inlined in workers.
#[test]

fn parallel_equiv_di_sharing() {
    let mk = || -> Net<Proper, ΔI> {
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
        n.connect(app.aux0, res, lo.clone()).unwrap();
        n.add_root(Arc::from("res"), res);
        n
    };
    let (seq, _) = normalize(mk()).unwrap();
    let (par, _) = normalize_par(mk(), 4).unwrap();
    let r_seq = *seq.roots().get("res").unwrap();
    let r_par = *par.roots().get("res").unwrap();
    assert_eq!(
        canonical_hash(&seq, r_seq).unwrap(),
        canonical_hash(&par, r_par).unwrap(),
        "ΔI sharing: parallel hash == sequential hash"
    );
}
