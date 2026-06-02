//! Paper-rule conformance oracles for the Δ-Nets core interaction system.
//!
//! Each test drives the PUBLIC reducer API (`normalize`) on a hand-built net and
//! asserts the observable result matches the Δ-Nets interaction rules of the paper
//! EXACTLY (levels, level-deltas, annihilate-vs-commute). These are black-box
//! regression oracles: any future edit to the internal `reduce/*` rules that breaks
//! a paper-rule's level/delta arithmetic (or the annihilate/commute decision) makes
//! one of these FAIL — independent of the internal `#[cfg(test)]` unit tests.
//!
//! Paper = `vic/main.tex`. Authoritative rule statements (re-quoted at each test).
//!
//! L787: equal agents ANNIHILATE; "two replicators are equal if and only if they
//! have the same level, number of auxiliary ports, and level deltas".
//!
//! L789: "Since an eraser has no auxiliary ports, it erases every agent it
//! interacts with."
//!
//! L790: replicator ⊗ fan — the replicator is copied twice (fan's 2 aux ports) and
//! a fan is emitted per replicator aux port.
//!
//! L792: distinct replicators COMMUTE; "whereas a duplication produces exact copies,
//! a replication produces copies that may or may not be exact".
//!
//! L793: "The level of each resulting replica is the sum of the level of the original
//! higher-level replicator and the appropriate level delta of the lower-level
//! replicator." (Fig L722/727/732: top-row replica levels are k+d_0 … k+d_n.)
//!
//! L856: signed level deltas — "d_i = l_i - (l + 1)".

use dnx_core::{
    normalize, Canonical, DnxError, LOPath, Net, PortId, PortKind, Proper, SlotView, ΔA, ΔI,
};
use std::sync::Arc;

// ── builder/observer helpers ──────────────────────────────────────────────────

/// Build a net holding `principal_a ⊗ principal_b` (built last), where each agent's
/// two aux ports are parked on the aux0 of a fresh rooted "holder" abs. After
/// `normalize`, the agent that survived on each original aux port is observable by
/// reading the holder's aux0 peer. Holders are pure plumbing (their principals are
/// roots, so C1 never sweeps them and they never form their own active pair).
struct Harness {
    net: Net<Proper, ΔI>,
    root: LOPath,
}

impl Harness {
    fn new() -> Self {
        Harness {
            net: Net::<Proper, ΔI>::new(64),
            root: LOPath::root(),
        }
    }

    /// Park `port` on a fresh holder's aux0 and root the holder under `name`.
    fn park(&mut self, name: &str, port: PortId) -> Result<(), DnxError> {
        let h = self.net.alloc_abs()?;
        self.net.connect(port, h.aux0, self.root.clone())?;
        self.net.add_root(Arc::from(name), h.principal);
        Ok(())
    }
}

/// SlotView of the agent now sitting on the named holder's aux0 wire.
fn parked(canon: &Net<Canonical, ΔI>, name: &str) -> Result<SlotView, DnxError> {
    let &hp = canon
        .roots()
        .get(name)
        .ok_or(DnxError::ReadbackIncomplete)?;
    let port = PortId::new(hp.slot_idx(), PortKind::Aux0, hp.gen_low());
    Ok(canon.slot_view(canon.peer(port)))
}

/// (is_rep, level, delta0, delta1) of the parked agent — the rep "identity triple"
/// the paper compares for equality (L787) plus the level it carries.
fn rep_id(canon: &Net<Canonical, ΔI>, name: &str) -> Result<(bool, u16, i16, i16), DnxError> {
    let sv = parked(canon, name)?;
    Ok((sv.is_rep(), sv.data, sv.delta0, sv.delta1))
}

// ── R4: Fan ⊗ Fan annihilation (β) ────────────────────────────────────────────

/// main.tex L787: "When equal agents interact, they annihilate one another."
/// A λ-fan meeting an @-fan is the β-redex; it annihilates in exactly one
/// interaction and produces no replication. (ΔL: only R4 can fire ⇒
/// interactions == r4_count, the optimality oracle.)
#[test]
fn r4_fan_fan_annihilates_in_one_beta() -> Result<(), DnxError> {
    use dnx_core::ΔL;
    let mut n = Net::<Proper, ΔL>::new(16);
    let root = LOPath::root();
    let abs = n.alloc_abs()?; // λx.x
    let app = n.alloc_app()?; // (_ arg)
    let arg = n.alloc_free(0)?;
    let res = n.alloc_free(1)?;
    n.connect(abs.aux0, abs.aux1, root.clone())?; // identity body
    n.connect(app.aux0, res, root.clone())?;
    n.connect(app.aux1, arg, root.clone())?;
    n.connect(abs.principal, app.principal, root.clone())?; // β redex
    n.add_root(Arc::from("res"), res);
    let (_canon, stats) = normalize(n)?;
    assert_eq!(stats.r4_count, 1, "exactly one β (annihilation)");
    assert_eq!(
        stats.interactions, 1,
        "annihilation is a single interaction"
    );
    Ok(())
}

// ── R6: Rep ⊗ Rep annihilation (equal level + deltas) ─────────────────────────

/// main.tex L787: two replicators "are equal if and only if they have the same
/// level, number of auxiliary ports, and level deltas" ⇒ they ANNIHILATE.
/// Observable: a single interaction, no β, and NEITHER original aux port still
/// carries a replicator (the four aux wires are cross-connected, reps gone).
#[test]
fn r6_rep_rep_equal_annihilates() -> Result<(), DnxError> {
    let mut h = Harness::new();
    let ra = h.net.alloc_rep_in(3, 1, 2)?;
    let rb = h.net.alloc_rep_in(3, 1, 2)?; // identical (level,δ0,δ1) ⇒ equal
    h.park("a0", ra.aux0)?;
    h.park("a1", ra.aux1)?;
    h.park("b0", rb.aux0)?;
    h.park("b1", rb.aux1)?;
    h.net.connect(ra.principal, rb.principal, h.root.clone())?;
    let (canon, stats) = normalize(h.net)?;
    assert_eq!(
        stats.interactions, 1,
        "rep-rep annihilation = one interaction"
    );
    assert_eq!(stats.r4_count, 0, "no β in a pure rep-rep interaction");
    for nm in ["a0", "a1", "b0", "b1"] {
        let (is_rep, ..) = rep_id(&canon, nm)?;
        assert!(!is_rep, "{nm}: annihilation removes both replicators");
    }
    Ok(())
}

// ── R7: Rep ⊗ Rep commutation (distinct) — the core level/delta arithmetic ─────

/// main.tex L792-793: distinct replicators commute. The lower-level rep is
/// duplicated EXACTLY (level + both deltas preserved); each replica of the
/// HIGHER-level rep gets level = (higher level) + (the lower rep's delta for the
/// aux port it exits), while keeping the higher rep's OWN deltas. Fig L722/727:
/// top-row replica levels are k+d_0 … k+d_n.
///
/// Wiring (rules.rs r7): higher-rep aux peers receive the lower-rep duplicates;
/// lower-rep aux peers receive the higher-rep replicas. So:
///   higher.aux0/aux1 holders → exact lower copies
///   lower.aux0/aux1 holders → higher replicas at k+δ0_low, k+δ1_low
#[test]
fn r7_rep_rep_distinct_commutes_with_exact_level_arithmetic() -> Result<(), DnxError> {
    let mut h = Harness::new();
    let hi = h.net.alloc_rep_in(5, 7, 9)?; // higher level k=5, own deltas 7,9
    let low = h.net.alloc_rep_in(2, 1, -1)?; // lower level l=2, deltas 1,-1
    h.park("hi0", hi.aux0)?;
    h.park("hi1", hi.aux1)?;
    h.park("lo0", low.aux0)?;
    h.park("lo1", low.aux1)?;
    h.net.connect(hi.principal, low.principal, h.root.clone())?;
    let (canon, stats) = normalize(h.net)?;
    assert_eq!(stats.interactions, 1, "commutation = one interaction");
    assert_eq!(stats.r4_count, 0, "no β");

    // Higher rep's aux peers see EXACT duplicates of the lower rep (L792).
    assert_eq!(rep_id(&canon, "hi0")?, (true, 2, 1, -1), "exact lower dup");
    assert_eq!(rep_id(&canon, "hi1")?, (true, 2, 1, -1), "exact lower dup");
    // Lower rep's aux peers see higher-rep replicas: level = k + lower.delta_i,
    // keeping the higher rep's OWN deltas (7,9) (L793 + Fig L722/727).
    assert_eq!(rep_id(&canon, "lo0")?, (true, 6, 7, 9), "5 + low.δ0(1) = 6");
    assert_eq!(
        rep_id(&canon, "lo1")?,
        (true, 4, 7, 9),
        "5 + low.δ1(-1) = 4"
    );
    Ok(())
}

/// main.tex L856: level deltas are SIGNED (`d_i = l_i - (l + 1)`). A negative
/// lower delta must LOWER the higher replica's level. Pins the signed add so a
/// future edit that uses unsigned/abs arithmetic is caught.
#[test]
fn r7_signed_negative_delta_lowers_replica_level() -> Result<(), DnxError> {
    let mut h = Harness::new();
    let hi = h.net.alloc_rep_in(8, 0, 0)?; // k = 8
    let low = h.net.alloc_rep_in(3, -3, 2)?; // signed deltas: -3 and +2
    h.park("hi0", hi.aux0)?;
    h.park("hi1", hi.aux1)?;
    h.park("lo0", low.aux0)?;
    h.park("lo1", low.aux1)?;
    h.net.connect(hi.principal, low.principal, h.root.clone())?;
    let (canon, _stats) = normalize(h.net)?;
    assert_eq!(
        rep_id(&canon, "lo0")?,
        (true, 5, 0, 0),
        "8 + (-3) = 5 (signed down)"
    );
    assert_eq!(
        rep_id(&canon, "lo1")?,
        (true, 10, 0, 0),
        "8 + 2 = 10 (signed up)"
    );
    Ok(())
}

/// A lower delta that would drive a replica level below 0 (or past the 14-bit
/// level ceiling) must fail — the arithmetic is checked, not wrapped.
/// (rules.rs `add_level`: valid range 0..16384, else `DeltaOverflow`.)
#[test]
fn r7_delta_underflow_is_error_not_wraparound() -> Result<(), DnxError> {
    let mut h = Harness::new();
    let hi = h.net.alloc_rep_in(2, 0, 0)?; // k = 2
    let low = h.net.alloc_rep_in(1, -10, 0)?; // 2 + (-10) = -8 → out of range
    h.park("hi0", hi.aux0)?;
    h.park("hi1", hi.aux1)?;
    h.park("lo0", low.aux0)?;
    h.park("lo1", low.aux1)?;
    h.net.connect(hi.principal, low.principal, h.root.clone())?;
    match normalize(h.net) {
        Err(DnxError::DeltaOverflow) => Ok(()),
        Err(e) => panic!("expected DeltaOverflow, got {e:?}"),
        Ok(_) => panic!("expected DeltaOverflow, but normalize succeeded (level wrapped?)"),
    }
}

/// main.tex L787: equal replicators annihilate; "only replicator levels need to be
/// compared for equality in practice" ⇒ LEVEL is the annihilate-vs-commute key, and
/// the commute (R7) hi/lo roles are assigned by LEVEL (not by delta magnitude). This
/// pins that discriminator: the LOWER-level rep here carries the LARGER deltas, yet
/// it is still treated as the lower agent (exact-duplicated), while the
/// HIGHER-level rep is the one replicated at level = hi + lower.delta_i.
#[test]
fn r7_hi_lo_split_is_by_level_not_delta_magnitude() -> Result<(), DnxError> {
    let mut h = Harness::new();
    let hi = h.net.alloc_rep_in(6, 1, 1)?; // higher level, SMALL deltas
    let low = h.net.alloc_rep_in(3, 9, 8)?; // lower level, LARGE deltas
    h.park("hi0", hi.aux0)?;
    h.park("hi1", hi.aux1)?;
    h.park("lo0", low.aux0)?;
    h.park("lo1", low.aux1)?;
    h.net.connect(hi.principal, low.principal, h.root.clone())?;
    let (canon, stats) = normalize(h.net)?;
    assert_eq!(stats.interactions, 1);
    // Lower rep (level 3) is exact-duplicated despite its larger deltas (L792).
    assert_eq!(
        rep_id(&canon, "hi0")?,
        (true, 3, 9, 8),
        "lower exact-duped (by level)"
    );
    assert_eq!(rep_id(&canon, "hi1")?, (true, 3, 9, 8));
    // Higher rep (level 6) is replicated at 6 + lower.delta_i, keeping its own deltas.
    assert_eq!(
        rep_id(&canon, "lo0")?,
        (true, 15, 1, 1),
        "6 + low.δ0(9) = 15"
    );
    assert_eq!(
        rep_id(&canon, "lo1")?,
        (true, 14, 1, 1),
        "6 + low.δ1(8) = 14"
    );
    Ok(())
}

// ── R5: Rep ⊗ Fan commutation ─────────────────────────────────────────────────

/// main.tex L790: "When a replicator interacts with a fan, the replicator travels
/// through and out of the fan's two auxiliary ports, resulting in two exact copies
/// of the replicator." The copies preserve the replicator's level AND deltas.
#[test]
fn r5_fan_rep_yields_two_exact_replicator_copies() -> Result<(), DnxError> {
    let mut h = Harness::new();
    let rep = h.net.alloc_rep_in(2, -1, 3)?;
    let lam = h.net.alloc_abs()?; // a fan (λ)
    h.park("r0", rep.aux0)?;
    h.park("r1", rep.aux1)?;
    h.park("f0", lam.aux0)?;
    h.park("f1", lam.aux1)?;
    h.net
        .connect(rep.principal, lam.principal, h.root.clone())?;
    let (canon, stats) = normalize(h.net)?;
    assert_eq!(stats.interactions, 1, "rep⊗fan = one interaction");
    assert_eq!(stats.r4_count, 0, "rep⊗fan is not β");
    // The fan's two aux peers each receive an EXACT replicator copy (L790):
    // same level and deltas as the original replicator.
    for nm in ["f0", "f1"] {
        assert_eq!(
            rep_id(&canon, nm)?,
            (true, 2, -1, 3),
            "{nm}: exact replicator copy (level+deltas preserved)"
        );
    }
    Ok(())
}

// ── Eraser rules: R1 / R2 / R3 (main.tex L789) ────────────────────────────────

/// main.tex L789: "Since an eraser has no auxiliary ports, it erases every agent it
/// interacts with." An eraser meeting a fan (R2) IS reachable through the public
/// builder: `eraser_port()` is a valid principal endpoint, so connecting it to a
/// fan's principal forms an active pair that fires. The fan is erased (no longer a
/// live slot) and the erasure propagates outward (interactions > 1); no β occurs.
#[test]
fn r2_eraser_fan_is_reachable_and_erases_the_fan() -> Result<(), DnxError> {
    let mut n = Net::<Proper, ΔA>::new(16);
    let root = LOPath::root();
    let app = n.alloc_app()?;
    let res = n.alloc_free(0)?;
    n.connect(app.aux0, res, root.clone())?;
    n.connect(app.aux1, Net::<Proper, ΔA>::eraser_port(), root.clone())?;
    n.add_root(Arc::from("res"), res);
    n.connect(
        app.principal,
        Net::<Proper, ΔA>::eraser_port(),
        root.clone(),
    )?;
    assert_eq!(n.active_pair_count(), 1, "eraser⊗fan forms an active pair");
    let (canon, stats) = normalize(n)?;
    assert!(stats.interactions >= 1, "the eraser interaction fired");
    assert_eq!(stats.r4_count, 0, "erasure is not β");
    assert!(
        !canon.slot_is_live(app.principal),
        "the fan was erased (R2)"
    );
    Ok(())
}

/// main.tex L789: an eraser erases EVERY agent — including a replicator (R3).
/// Reachable identically: connect `eraser_port()` to a replicator's principal.
/// Under ΔI the eraser propagates into the rep's aux ports; the rep principal is
/// consumed. We assert the interaction fires and the replicator is gone.
#[test]
fn r3_eraser_rep_is_reachable_and_erases_the_rep() -> Result<(), DnxError> {
    let mut n = Net::<Proper, ΔI>::new(16);
    let root = LOPath::root();
    let rep = n.alloc_rep_in(3, 0, 0)?;
    let c = n.alloc_free(0)?;
    let d = n.alloc_free(1)?;
    n.connect(rep.aux0, c, root.clone())?;
    n.connect(rep.aux1, d, root.clone())?;
    n.add_root(Arc::from("c"), c);
    n.add_root(Arc::from("d"), d);
    n.connect(
        rep.principal,
        Net::<Proper, ΔI>::eraser_port(),
        root.clone(),
    )?;
    assert_eq!(n.active_pair_count(), 1, "eraser⊗rep forms an active pair");
    let (canon, stats) = normalize(n)?;
    assert!(stats.interactions >= 1, "the eraser interaction fired");
    assert_eq!(stats.r4_count, 0, "erasure is not β");
    assert!(
        !canon.slot_is_live(rep.principal),
        "the replicator was erased (R3)"
    );
    Ok(())
}

/// main.tex L787 + Fig L768 caption (R1): when two erasers meet they annihilate;
/// since erasers are sentinel ports with no aux ports and no slots, the interaction
/// is a virtual no-op. It IS reachable through the public builder — connecting the
/// two eraser sentinels' principals forms one active pair — and it fires as exactly
/// one interaction that produces nothing (no β, no surviving agents).
#[test]
fn r1_eraser_eraser_fires_as_a_virtual_noop() -> Result<(), DnxError> {
    let mut n = Net::<Proper, ΔA>::new(8);
    let root = LOPath::root();
    n.connect(
        Net::<Proper, ΔA>::eraser_port(),
        Net::<Proper, ΔA>::eraser_port(),
        root,
    )?;
    assert_eq!(
        n.active_pair_count(),
        1,
        "eraser⊗eraser forms one active pair"
    );
    let (_canon, stats) = normalize(n)?;
    assert_eq!(stats.interactions, 1, "R1 fires as exactly one interaction");
    assert_eq!(stats.r4_count, 0, "R1 is a no-op, not β");
    assert!(PortId::ERA.is_eraser());
    Ok(())
}
