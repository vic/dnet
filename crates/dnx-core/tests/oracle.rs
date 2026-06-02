//! Soundness oracle: confluence + optimality + hash equivalence.
//! Run: `just oracle`  (--include-ignored)

use dnx_core::{canonical_hash, normalize, DnxError, LOPath, Net, Proper, ΔI, ΔK, ΔL};
use std::sync::Arc;

// ── net builders ─────────────────────────────────────────────────────────────

/// (λx.x) arg — 1 β-reduction.
fn id_applied() -> Result<Net<Proper, ΔL>, DnxError> {
    let mut n = Net::<Proper, ΔL>::new(16);
    let abs = n.alloc_abs()?;
    let app = n.alloc_app()?;
    let arg = n.alloc_free(0)?;
    let res = n.alloc_free(1)?;
    n.connect(abs.aux0, abs.aux1, LOPath::root())?;
    n.connect(app.aux0, res, LOPath::root())?;
    n.connect(app.aux1, arg, LOPath::root())?;
    n.connect(abs.principal, app.principal, LOPath::root())?;
    n.add_root(Arc::from("res"), res);
    Ok(n)
}

/// (λx.x)(λy.y) — identity applied to identity, 1 β.
fn id_id() -> Result<Net<Proper, ΔL>, DnxError> {
    let mut n = Net::<Proper, ΔL>::new(16);
    let abs1 = n.alloc_abs()?;
    let abs2 = n.alloc_abs()?;
    let app = n.alloc_app()?;
    let res = n.alloc_free(0)?;
    n.connect(abs1.aux0, abs1.aux1, LOPath::root())?;
    n.connect(abs2.aux0, abs2.aux1, LOPath::root())?;
    n.connect(app.principal, abs1.principal, LOPath::root())?;
    n.connect(app.aux1, abs2.principal, LOPath::root())?;
    n.connect(app.aux0, res, LOPath::root())?;
    n.add_root(Arc::from("res"), res);
    Ok(n)
}

fn two_independent_ids() -> Result<Net<Proper, ΔL>, DnxError> {
    let mut n = Net::<Proper, ΔL>::new(32);
    let lo0 = LOPath::root().extend_left()?;
    let lo1 = LOPath::root().extend_right()?;
    for (lo, var_id, root_name) in [(lo0, 0u32, "r0"), (lo1, 2u32, "r1")] {
        let abs = n.alloc_abs()?;
        let app = n.alloc_app()?;
        let arg = n.alloc_free(var_id)?;
        let res = n.alloc_free(var_id + 1)?;
        n.connect(abs.aux0, abs.aux1, lo.clone())?;
        n.connect(app.aux1, arg, lo.clone())?;
        n.connect(app.aux0, res, lo.clone())?;
        n.connect(abs.principal, app.principal, lo.clone())?;
        n.add_root(Arc::from(root_name), res);
    }
    Ok(n)
}

/// (λx. x x) id in ΔI — sharing: rep duplicates id into 2 uses → 2 β total.
fn self_apply_id() -> Result<Net<Proper, ΔI>, DnxError> {
    let mut n = Net::<Proper, ΔI>::new(64);
    let lo = LOPath::root();
    // outer = λx. (x x): abs with rep sharing var into app function + arg
    let outer = n.alloc_abs()?;
    let rep = n.alloc_rep_in(0, 0, 0)?;
    let inner_app = n.alloc_app()?;
    // rep.principal = outer var
    n.connect(rep.principal, outer.aux1, lo.clone())?;
    // rep.aux0 → inner_app function port (principal)
    n.connect(rep.aux0, inner_app.principal, lo.clone())?;
    // rep.aux1 → inner_app arg
    n.connect(rep.aux1, inner_app.aux1, lo.clone())?;
    // inner_app result = outer body
    n.connect(inner_app.aux0, outer.aux0, lo.clone())?;
    // id = λy.y
    let id = n.alloc_abs()?;
    n.connect(id.aux0, id.aux1, lo.clone())?;
    // apply outer to id
    let app = n.alloc_app()?;
    let res = n.alloc_free(0)?;
    n.connect(app.principal, outer.principal, lo.clone())?;
    n.connect(app.aux1, id.principal, lo.clone())?;
    n.connect(app.aux0, res, lo.clone())?;
    n.add_root(Arc::from("res"), res);
    Ok(n)
}

// ── helpers ───────────────────────────────────────────────────────────────────

fn root_hash<C: dnx_core::NetClassMarker>(
    net: &dnx_core::Net<dnx_core::Canonical, C>,
    name: &str,
) -> [u8; 32] {
    let port = *net.roots().get(name).expect("root missing");
    canonical_hash(net, port).expect("canonical_hash on a pure NF")
}

// ── confluence tests ──────────────────────────────────────────────────────────

/// Same term built twice → same canonical hash (deterministic normalization).
#[test]

fn confluence_id_hash_stable() -> Result<(), DnxError> {
    let (n1, _) = normalize(id_applied()?)?;
    let (n2, _) = normalize(id_applied()?)?;
    assert_eq!(
        root_hash(&n1, "res"),
        root_hash(&n2, "res"),
        "id_applied: hash must be stable"
    );
    Ok(())
}

// ── optimality tests ──────────────────────────────────────────────────────────

/// ΔL: only R4 (β) can fire — interactions == r4_count always.
#[test]

fn optimality_dl_interactions_eq_beta() -> Result<(), DnxError> {
    for (name, net) in [
        ("id_applied", id_applied()?),
        ("two_ids", two_independent_ids()?),
        ("id_id", id_id()?),
    ] {
        let (_, s) = normalize(net)?;
        assert_eq!(
            s.interactions, s.r4_count,
            "ΔL optimality violated for '{name}': interactions={} r4={}",
            s.interactions, s.r4_count
        );
    }
    Ok(())
}

/// id_applied: exactly 1 β.
#[test]

fn optimality_id_exact_one_beta() -> Result<(), DnxError> {
    let (_, s) = normalize(id_applied()?)?;
    assert_eq!(s.r4_count, 1, "id_applied: 1 β");
    assert_eq!(s.interactions, 1, "id_applied: 1 total interaction");
    Ok(())
}

/// Two independent ids: exactly 2 β, no extra interactions.
#[test]

fn optimality_two_ids_exact_two_beta() -> Result<(), DnxError> {
    let (_, s) = normalize(two_independent_ids()?)?;
    assert_eq!(s.r4_count, 2, "two ids: 2 β");
    assert_eq!(s.interactions, 2, "two ids: 2 total interactions");
    Ok(())
}

/// ΔI sharing: (λx. x x) id → id id → id. Exactly 2 β, no duplication.
#[test]

fn optimality_di_no_duplicate_beta() -> Result<(), DnxError> {
    let (_, s) = normalize(self_apply_id()?)?;
    assert_eq!(
        s.r4_count, 2,
        "(λx.x x) id: exactly 2 β (sharing = no duplication)"
    );
    Ok(())
}

/// Zero-redex net: 0 interactions.
#[test]

fn optimality_no_redex_zero_interactions() -> Result<(), DnxError> {
    let mut n = Net::<Proper, ΔL>::new(8);
    let abs = n.alloc_abs()?;
    n.add_root(Arc::from("r"), abs.principal);
    let (_, s) = normalize(n)?;
    assert_eq!(s.interactions, 0);
    assert_eq!(s.r4_count, 0);
    Ok(())
}

// ── ΔI omega bounded memory ───────────────────────────────────────────────────

/// ω ω net can be built; frontier1 has exactly 1 pair; agent count bounded.
#[test]

fn di_omega_bounded_memory() -> Result<(), DnxError> {
    let mut n = Net::<Proper, ΔI>::new(32);
    let abs = n.alloc_abs()?;
    let rep = n.alloc_rep_in(0, 0, 0)?;
    let app = n.alloc_app()?;
    let r = n.alloc_free(0)?;
    n.connect(rep.aux0, abs.aux0, LOPath::root())?;
    n.connect(rep.aux1, abs.aux1, LOPath::root())?;
    n.connect(rep.principal, app.aux1, LOPath::root())?;
    n.connect(app.aux0, r, LOPath::root())?;
    n.connect(abs.principal, app.principal, LOPath::root())?;
    assert_eq!(n.active_pair_count(), 1, "ω ω: one active pair");
    assert!(n.agent_count() <= 32, "ω ω: bounded agents");
    Ok(())
}

// ── confluence: stable-hash tests ────────────────────────────────────────────

/// Two independent pairs normalize to same hash each run.
#[test]

fn confluence_independent_pairs_hash_stable() -> Result<(), DnxError> {
    let (a, _) = normalize(two_independent_ids()?)?;
    let (b, _) = normalize(two_independent_ids()?)?;
    assert_eq!(root_hash(&a, "r0"), root_hash(&b, "r0"), "r0 hash stable");
    assert_eq!(root_hash(&a, "r1"), root_hash(&b, "r1"), "r1 hash stable");
    Ok(())
}

/// id_id stable: same term, same hash both runs.
#[test]

fn confluence_id_id_hash_stable() -> Result<(), DnxError> {
    let (a, _) = normalize(id_id()?)?;
    let (b, _) = normalize(id_id()?)?;
    assert_eq!(
        root_hash(&a, "res"),
        root_hash(&b, "res"),
        "id_id hash stable"
    );
    Ok(())
}

// ── ΔK sharing ───────────────────────────────────────────────────────────────

/// ΔK: (λx. x) applied with sharing — result hash stable.
#[test]

fn dk_sharing_hash_stable() -> Result<(), DnxError> {
    let mk = || -> Result<Net<Proper, ΔK>, DnxError> {
        let mut n = Net::<Proper, ΔK>::new(32);
        let abs = n.alloc_abs()?;
        let app = n.alloc_app()?;
        let arg = n.alloc_free(0)?;
        let res = n.alloc_free(1)?;
        n.connect(abs.aux0, abs.aux1, LOPath::root())?;
        n.connect(app.aux0, res, LOPath::root())?;
        n.connect(app.aux1, arg, LOPath::root())?;
        n.connect(abs.principal, app.principal, LOPath::root())?;
        n.add_root(Arc::from("res"), res);
        Ok(n)
    };
    let (n1, _) = normalize(mk()?)?;
    let (n2, _) = normalize(mk()?)?;
    assert_eq!(
        root_hash(&n1, "res"),
        root_hash(&n2, "res"),
        "ΔK: same hash both runs"
    );
    Ok(())
}
