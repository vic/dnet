use crate::class::NetClassMarker;
use crate::error::DnxError;
use crate::net::Net;
use crate::{Canonical, PortId, PortKind};
use std::collections::HashMap;
use std::sync::Arc;

pub type Blake3Hash = [u8; 32];

// Version tag (first byte of serialization).
const CANON_HASH_V1: u8 = 0x01;

// Agent kind codes (stable across versions). `pub(crate)` so the inverse
// (`blob::deserialize`) shares the one format contract — never a second copy.
pub(crate) const CANON_HASH_V1_TAG: u8 = CANON_HASH_V1;
pub(crate) const KIND_FAN_ABS: u8 = 0x01;
pub(crate) const KIND_FAN_APP: u8 = 0x02;
pub(crate) const KIND_REP_IN: u8 = 0x03;
pub(crate) const KIND_FREE_VAR: u8 = 0x04;
pub(crate) const KIND_ERASER: u8 = 0xFF;

// Canonical index sentinel: emitted ONLY for a genuine eraser/null edge
// (canonical-hash.md:91-93). Never a fallback for a missed live peer.
pub(crate) const ERASER_IDX: u32 = u32::MAX;
// Edge eraser-selector byte companion to `ERASER_IDX` (emit_edge writes 0xFF).
pub(crate) const ERASER_SEL: u8 = 0xFF;

/// Canonical-index map: keyed by AGENT identity (`slot_idx`), value = canonical
/// first-visit index (canonical-hash.md serialize). The peer's port-kind is
/// serialized separately on the edge, so an agent is interned once regardless of
/// which port reaches it (fixes C1: PortId-keying missed shared/back-edge peers).
type IdxMap = HashMap<u32, u32>;

/// `ArtifactId` LOCAL representation (proofs.md:110, canonical-hash.md:13-17): an
/// intern id over the canonical `serialize` bytes. Equality is exact byte-equality
/// (the intern table is ground-truth, the hash only buckets) — NO cryptographic
/// hash in the conv/soundness TCB (= Lean `is_eqp`, type_checker.cpp:1059).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct ArtifactLocal(u64);

/// Intern table for the LOCAL `ArtifactId` representation: `serialize`-bytes → id.
/// The keys (bytes) are the ground truth — `Eq` decides identity on a bucket hit;
/// the bucket hash never enters the equality decision. Two artifacts interned in
/// the same table are equal iff their canonical serializations are byte-identical.
#[derive(Default)]
pub struct Interner {
    table: HashMap<Vec<u8>, u64>,
}

impl Interner {
    pub fn new() -> Self {
        Interner::default()
    }

    /// Intern a canonical net's serialization → its LOCAL `ArtifactId`. O(1) per
    /// subsequent compare; the one O(n) walk is the serialize already required.
    pub fn intern_local<C: NetClassMarker>(
        &mut self,
        net: &Net<Canonical, C>,
        root: PortId,
    ) -> Result<ArtifactLocal, DnxError> {
        let bytes = serialize(net, root)?;
        let next = self.table.len() as u64;
        let id = *self.table.entry(bytes).or_insert(next);
        Ok(ArtifactLocal(id))
    }
}

/// Compute the WIRE representation: `BLAKE3(serialize)` — a compact cross-machine
/// content-address (canonical-hash.md:18). A collision here is a distribution
/// dedup miss, NOT a conv/soundness dependency; the conv decision uses
/// `Interner::intern_local` (structural-exact), never this hash.
pub fn canonical_hash<C: NetClassMarker>(
    net: &Net<Canonical, C>,
    root: PortId,
) -> Result<Blake3Hash, DnxError> {
    let bytes = serialize(net, root)?;
    Ok(*blake3::hash(&bytes).as_bytes())
}

pub(crate) fn serialize<C: NetClassMarker>(
    net: &Net<Canonical, C>,
    root: PortId,
) -> Result<Vec<u8>, DnxError> {
    let mut buf: Vec<u8> = Vec::with_capacity(256);
    buf.push(CANON_HASH_V1);

    // DFS traversal to assign canonical indices (keyed by agent = slot_idx).
    let mut canonical_idx: IdxMap = HashMap::new();
    let mut order: Vec<PortId> = Vec::new();
    dfs_assign(net, root, &mut canonical_idx, &mut order);

    // Emit record count.
    let n = order.len() as u32;
    buf.extend_from_slice(&n.to_le_bytes());

    // Emit each record.
    for port in &order {
        emit_record(net, *port, &canonical_idx, &mut buf)?;
    }

    Ok(buf)
}

/// DFS first-visit assigns a canonical index to each AGENT (`slot_idx`). Uses an
/// explicit work-stack (NOT native recursion): a deep/adversarial net would
/// overflow the call stack, and this runs on untrusted blobs re-hashed by the
/// verify-on-read path. The visit order is identical to the recursive
/// pre-order — children pushed in reverse (aux1, aux0, principal) so principal
/// is popped first.
fn dfs_assign<C: NetClassMarker>(
    net: &Net<Canonical, C>,
    root: PortId,
    canonical_idx: &mut IdxMap,
    order: &mut Vec<PortId>,
) {
    let mut stack: Vec<PortId> = vec![root];
    while let Some(port) = stack.pop() {
        if port.is_eraser() || port.is_null() {
            continue;
        }
        let slot_idx = port.slot_idx();
        if canonical_idx.contains_key(&slot_idx) {
            continue;
        }
        let idx = order.len() as u32;
        canonical_idx.insert(slot_idx, idx);
        order.push(port);

        let s = net.slot_view(port);
        if s.is_free() {
            continue; // Leaf: no children.
        }
        if s.is_fan() || s.is_rep() {
            // Push in reverse canonical port order so the next pop visits the
            // principal first, then aux0, then aux1 (matches the old recursion).
            let gen = port.gen_low();
            stack.push(net.peer(PortId::new(slot_idx, PortKind::Aux1, gen)));
            stack.push(net.peer(PortId::new(slot_idx, PortKind::Aux0, gen)));
            stack.push(net.peer(PortId::new(slot_idx, PortKind::Principal, gen)));
        }
    }
}

fn emit_record<C: NetClassMarker>(
    net: &Net<Canonical, C>,
    port: PortId,
    canonical_idx: &IdxMap,
    buf: &mut Vec<u8>,
) -> Result<(), DnxError> {
    if port.is_eraser() {
        buf.push(KIND_ERASER);
        return Ok(());
    }
    let s = net.slot_view(port);
    let slot_idx = port.slot_idx();
    let gen = port.gen_low();

    if s.is_free() {
        buf.push(KIND_FREE_VAR);
        let var_id = s.free_var_id();
        buf.extend_from_slice(&(var_id as u32).to_le_bytes());
        return Ok(());
    }

    if s.is_fan() && s.fan_is_abs() {
        buf.push(KIND_FAN_ABS);
        // Edges: body (aux0), var (aux1).
        emit_edge(
            net,
            PortId::new(slot_idx, PortKind::Aux0, gen),
            canonical_idx,
            buf,
        )?;
        emit_edge(
            net,
            PortId::new(slot_idx, PortKind::Aux1, gen),
            canonical_idx,
            buf,
        )?;
        return Ok(());
    }

    if s.is_fan() {
        buf.push(KIND_FAN_APP);
        // Edges: func (principal peer), arg (aux1 peer).
        emit_edge(
            net,
            PortId::new(slot_idx, PortKind::Principal, gen),
            canonical_idx,
            buf,
        )?;
        emit_edge(
            net,
            PortId::new(slot_idx, PortKind::Aux1, gen),
            canonical_idx,
            buf,
        )?;
        return Ok(());
    }

    if s.is_rep() {
        buf.push(KIND_REP_IN);
        buf.extend_from_slice(&s.data.to_le_bytes()); // level
        buf.extend_from_slice(&s.delta0.to_le_bytes());
        buf.extend_from_slice(&s.delta1.to_le_bytes());
        emit_edge(
            net,
            PortId::new(slot_idx, PortKind::Aux0, gen),
            canonical_idx,
            buf,
        )?;
        emit_edge(
            net,
            PortId::new(slot_idx, PortKind::Aux1, gen),
            canonical_idx,
            buf,
        )?;
        return Ok(());
    }

    // PrimVal/PrimFun: Phase C — propagate, never panic (dnx axiom).
    Err(DnxError::PrimError(Arc::from(
        "canonical_hash: PrimVal/PrimFun not yet supported (Phase C)",
    )))
}

fn emit_edge<C: NetClassMarker>(
    net: &Net<Canonical, C>,
    port: PortId,
    canonical_idx: &IdxMap,
    buf: &mut Vec<u8>,
) -> Result<(), DnxError> {
    let peer = net.peer(port);
    if peer.is_eraser() || peer.is_null() {
        buf.extend_from_slice(&ERASER_IDX.to_le_bytes());
        buf.push(ERASER_SEL);
        return Ok(());
    }
    // A live peer MUST have been assigned a canonical index by the DFS. A miss is a
    // serialize invariant break (net not fully reachable from root) — a HARD error,
    // never the eraser sentinel (C1: a missed live wire serialized as an eraser is a
    // FALSE `≡`).
    let idx = canonical_idx
        .get(&peer.slot_idx())
        .copied()
        .ok_or(DnxError::ReadbackIncomplete)?;
    buf.extend_from_slice(&idx.to_le_bytes());
    let port_sel: u8 = match peer.port_kind() {
        PortKind::Principal => 0,
        PortKind::Aux0 => 1,
        PortKind::Aux1 => 2,
    };
    buf.push(port_sel);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::net::Net;
    use crate::{normalize, LOPath, Proper, ΔL};

    #[test]
    fn hash_equal_nets_equal() {
        // Two identity nets (different slot orders) should produce the same hash.
        fn make_id() -> (Net<Canonical, ΔL>, PortId) {
            let mut n = Net::<Proper, ΔL>::new(16);
            let abs = n.alloc_abs().unwrap();
            n.connect(abs.aux0, abs.aux1, LOPath::root()).unwrap();
            n.add_root("r".into(), abs.principal);
            let (c, _) = normalize(n).unwrap();
            (c, abs.principal)
        }
        let (n1, r1) = make_id();
        let (n2, r2) = make_id();
        let h1 = canonical_hash(&n1, r1).unwrap();
        let h2 = canonical_hash(&n2, r2).unwrap();
        assert_eq!(h1, h2, "equal nets should have equal hash");
    }

    #[test]
    fn hash_different_nets_differ() {
        // Identity λx.x vs λx.λy.y (structurally different).
        fn make_id() -> (Net<Canonical, ΔL>, PortId) {
            let mut n = Net::<Proper, ΔL>::new(16);
            let abs = n.alloc_abs().unwrap();
            n.connect(abs.aux0, abs.aux1, LOPath::root()).unwrap();
            n.add_root("r".into(), abs.principal);
            let (c, _) = normalize(n).unwrap();
            (c, abs.principal)
        }
        fn make_k() -> (Net<Canonical, ΔL>, PortId) {
            // λx.λy.x -- K combinator (ΔA actually, but let's just test structural diff)
            // Actually ΔL doesn't support erasure, so just λx.λy.y with x erased is ΔA.
            // Use λf.λx.f x instead (no era/rep).
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
        let (n1, r1) = make_id();
        let (n2, r2) = make_k();
        let h1 = canonical_hash(&n1, r1).unwrap();
        let h2 = canonical_hash(&n2, r2).unwrap();
        assert_ne!(h1, h2, "different nets should have different hash");
    }

    // ── S3: PrimVal/PrimFun → Err, NEVER panic (dnx axiom) ──────────────────
    #[test]
    fn prim_slot_serialize_errs_not_panics() {
        use crate::prim::TAG_PRIM_VAL;
        // A net whose root agent is a tagged PrimVal (bools are tagged PrimVals,
        // reduce/mod.rs:236). serialize/canonical_hash must RETURN Err, not panic.
        let mut n = Net::<Proper, ΔL>::new(8);
        let p = n.alloc_agent(TAG_PRIM_VAL, 0, 0, 0).unwrap();
        n.add_root("r".into(), p.principal);
        let (c, _) = normalize(n).unwrap();
        let r = canonical_hash(&c, p.principal);
        assert!(
            matches!(r, Err(DnxError::PrimError(_))),
            "prim slot must yield Err(PrimError), got {r:?}"
        );
    }

    // ── C1: serialize must emit EXACTLY ONE record per reachable AGENT, with edges
    // in canonical-index space (canonical-hash.md:91-99 "a shared node is emitted
    // once, referenced by index"). The old PortId-keyed map indexed each PORT-KIND
    // of an agent separately → a shared/back-edge agent was emitted MULTIPLE times
    // under MULTIPLE indices, breaking the canonical-uniqueness invariant (the
    // sentinel-as-identity class: a non-canonical serialization is unsound for `≡`).
    #[test]
    fn one_record_per_agent_shared_var() {
        // λf. f f — 3 agents: abs, app, rep(dups `f`). `f` (abs.aux1) is shared by the
        // App's func (rep.aux0→app.principal) and arg (rep.aux1→app.aux1): the rep is
        // reached via two port-kinds. Canonical serialize ⇒ 3 records, not more.
        let mut n = Net::<Proper, ΔL>::new(32);
        let abs = n.alloc_abs().unwrap();
        let app = n.alloc_app().unwrap();
        let rep = n.alloc_rep_in(0, 0, 0).unwrap();
        n.connect(rep.principal, abs.aux1, LOPath::root()).unwrap();
        n.connect(app.principal, rep.aux0, LOPath::root()).unwrap();
        n.connect(app.aux1, rep.aux1, LOPath::root()).unwrap();
        n.connect(abs.aux0, app.aux0, LOPath::root()).unwrap();
        n.add_root("r".into(), abs.principal);
        let (c, _) = normalize(n).unwrap();
        let s = serialize(&c, abs.principal).unwrap();
        // Record count = bytes[1..5] (little-endian u32 after the version tag).
        let n_records = u32::from_le_bytes([s[1], s[2], s[3], s[4]]);
        // Count distinct reachable agents (slot indices) from the same root.
        let agents = reachable_agents(&c, abs.principal);
        assert_eq!(
            n_records as usize, agents,
            "serialize must emit one record per agent ({agents}), got {n_records} \
             (old PortId-keying over-counts shared/back-edge agents — C1)"
        );
        // And no live edge masquerades as the eraser sentinel.
        assert!(
            !s.windows(4).any(|w| w == ERASER_IDX.to_le_bytes()),
            "no live edge may serialize to the eraser sentinel (C1)"
        );
    }

    /// Count distinct reachable agents (slot indices) via the canonical port order —
    /// the independent oracle for "one record per agent".
    fn reachable_agents<C: NetClassMarker>(net: &Net<Canonical, C>, root: PortId) -> usize {
        fn go<C: NetClassMarker>(
            net: &Net<Canonical, C>,
            p: PortId,
            seen: &mut std::collections::HashSet<u32>,
        ) {
            if p.is_eraser() || p.is_null() || !seen.insert(p.slot_idx()) {
                return;
            }
            let s = net.slot_view(p);
            if s.is_fan() || s.is_rep() {
                let g = p.gen_low();
                go(
                    net,
                    net.peer(PortId::new(p.slot_idx(), PortKind::Principal, g)),
                    seen,
                );
                go(
                    net,
                    net.peer(PortId::new(p.slot_idx(), PortKind::Aux0, g)),
                    seen,
                );
                go(
                    net,
                    net.peer(PortId::new(p.slot_idx(), PortKind::Aux1, g)),
                    seen,
                );
            }
        }
        let mut seen = std::collections::HashSet::new();
        go(net, root, &mut seen);
        seen.len()
    }
}
