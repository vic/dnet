/// Structural function equality for interaction nets.
///
/// Two closed lambda-nets are equal iff their canonical serializations are
/// byte-identical (canonical-hash.md:13-17, proofs.md:110). This uses
/// `canonical_hash` (Blake3 of the DFS-serialized canonical form) — the same
/// primitive the trusted kernel uses for conv (`Interner::intern_local`).
///
/// # When to use which
/// - Same-session pair: prefer `Interner::intern_local` (O(1) compare after
///   the first intern, no hash collision risk in TCB).
/// - Cross-call / this function: `canonical_hash` compares the Blake3 digest
///   bytes directly; collision probability is negligible (2^-256) and this fn
///   never enters the soundness TCB.
use crate::canonical_hash::canonical_hash;
use crate::class::NetClassMarker;
use crate::error::DnxError;
use crate::net::Net;
use crate::{Canonical, PortId};

/// Decide structural equality of two function (lambda) nets.
///
/// Returns `Ok(true)` iff the canonical serializations of `net_a` rooted at
/// `root_a` and `net_b` rooted at `root_b` are byte-identical.
///
/// Both nets must already be in `Canonical` form (i.e. produced by
/// `normalize`). No reduction is performed here.
pub fn fn_eq<C: NetClassMarker>(
    net_a: &Net<Canonical, C>,
    root_a: PortId,
    net_b: &Net<Canonical, C>,
    root_b: PortId,
) -> Result<bool, DnxError> {
    let ha = canonical_hash(net_a, root_a)?;
    let hb = canonical_hash(net_b, root_b)?;
    Ok(ha == hb)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::net::Net;
    use crate::{normalize, LOPath, Proper, ΔL};

    /// Build the identity net λx.x (FanAbs with body wired to var).
    fn make_id() -> (Net<Canonical, ΔL>, PortId) {
        let mut n = Net::<Proper, ΔL>::new(16);
        let abs = n.alloc_abs().unwrap();
        // λx.x: body port (aux0) wired to var port (aux1)
        n.connect(abs.aux0, abs.aux1, LOPath::root()).unwrap();
        n.add_root("r".into(), abs.principal);
        let (c, _) = normalize(n).unwrap();
        (c, abs.principal)
    }

    /// Build λf.λx.f x (S-like: two abstractions + one app, no erasure/rep).
    fn make_app() -> (Net<Canonical, ΔL>, PortId) {
        let mut n = Net::<Proper, ΔL>::new(32);
        let abs1 = n.alloc_abs().unwrap();
        let abs2 = n.alloc_abs().unwrap();
        let app = n.alloc_app().unwrap();
        // λf . λx . f x
        n.connect(abs1.aux0, abs2.principal, LOPath::root())
            .unwrap();
        n.connect(app.principal, abs1.aux1, LOPath::root()).unwrap();
        n.connect(app.aux1, abs2.aux1, LOPath::root()).unwrap();
        n.connect(abs2.aux0, app.aux0, LOPath::root()).unwrap();
        n.add_root("r".into(), abs1.principal);
        let (c, _) = normalize(n).unwrap();
        (c, abs1.principal)
    }

    #[test]
    fn id_eq_id() {
        let (n1, r1) = make_id();
        let (n2, r2) = make_id();
        assert!(fn_eq(&n1, r1, &n2, r2).unwrap(), "λx.x == λx.x");
    }

    #[test]
    fn id_ne_app() {
        let (n1, r1) = make_id();
        let (n2, r2) = make_app();
        assert!(!fn_eq(&n1, r1, &n2, r2).unwrap(), "λx.x != λf.λx.f x");
    }
}
