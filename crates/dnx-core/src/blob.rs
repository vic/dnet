//! Canonical-net blob codec: the on-the-wire export/import boundary for the
//! distribution layer (distribution-mvp-plan.md §A.2, §D.1-D.2).
//!
//! `to_blob` wraps the existing one-way `canonical_hash::serialize`
//! (canonical-hash.md:59-93). `from_blob` is its inverse — `deserialize`
//! rebuilds a `Net<Proper>` from the byte stream, then `certify_canonical`
//! (net.rs) gates it into the unforgeable `Net<Canonical>` typestate
//! (net.md:431). Malformed bytes never panic: every read is bounds-checked
//! and propagates `DnxError::ReadbackIncomplete` (driver.md:194).

use crate::canonical_hash::{
    serialize, CANON_HASH_V1_TAG, ERASER_IDX, ERASER_SEL, KIND_ERASER, KIND_FAN_ABS, KIND_FAN_APP,
    KIND_FREE_VAR, KIND_REP_IN,
};
use crate::class::NetClassMarker;
use crate::error::DnxError;
use crate::net::{certify_canonical, into_canonical, Net};
use crate::{Canonical, LOPath, PortId, PortKind, Proper};

/// Free-var id domain: 14 bits (`data & 0x3FFF`, net.rs:102/233). serialize
/// widens this to u32; deserialize rejects anything wider as malformed.
const FREE_VAR_ID_MAX: u32 = 0x3FFF;

/// Serialize a canonical net to its content-addressed blob (the `code`
/// payload of a shipped artifact, distribution-design.md:46-48). Pure wrapper
/// over `serialize` so `Net<Canonical>` construction stays inside core.
pub fn to_blob<C: NetClassMarker>(
    net: &Net<Canonical, C>,
    root: PortId,
) -> Result<Vec<u8>, DnxError> {
    serialize(net, root)
}

/// Inverse of `to_blob`: parse an untrusted blob back into the
/// `Net<Canonical>` typestate. Rejects malformed input with
/// `DnxError::ReadbackIncomplete` (never panics); the returned net is the
/// root (canonical index 0). The frontend prim-compat / hash-recompute checks
/// (distribution-mvp-plan.md §F) layer ON TOP of this in `dnx-dist`.
pub fn from_blob<C: NetClassMarker>(bytes: &[u8]) -> Result<(Net<Canonical, C>, PortId), DnxError> {
    deserialize(bytes)
}

/// A live-edge target as emitted by `emit_edge`: peer canonical index + the
/// peer's port selector (0/1/2). The eraser sentinel (`ERASER_IDX`/`ERASER_SEL`)
/// is decoded to `None` (a virtual eraser port, canonical-hash.md:91-93).
type Edge = Option<(u32, PortKind)>;

/// One decoded record: the kind plus the wires this record's OWN ports carry
/// (serialize emits edges for a fixed subset of ports per kind — the rest are
/// wired as back-references from other records). `(local_port, edge)` pairs.
struct Record {
    kind: u8,
    level: u16,
    delta0: i16,
    delta1: i16,
    var_id: u32,
    edges: Vec<(PortKind, Edge)>,
}

/// Forward-only bounds-checked byte cursor — every read is fallible so a
/// truncated/malformed blob yields `Err`, never an index panic.
struct Reader<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Reader { bytes, pos: 0 }
    }

    fn u8(&mut self) -> Result<u8, DnxError> {
        let b = *self
            .bytes
            .get(self.pos)
            .ok_or(DnxError::ReadbackIncomplete)?;
        self.pos += 1;
        Ok(b)
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N], DnxError> {
        let end = self
            .pos
            .checked_add(N)
            .ok_or(DnxError::ReadbackIncomplete)?;
        let slice = self
            .bytes
            .get(self.pos..end)
            .ok_or(DnxError::ReadbackIncomplete)?;
        let mut out = [0u8; N];
        out.copy_from_slice(slice);
        self.pos = end;
        Ok(out)
    }

    fn u32(&mut self) -> Result<u32, DnxError> {
        Ok(u32::from_le_bytes(self.take::<4>()?))
    }

    fn u16(&mut self) -> Result<u16, DnxError> {
        Ok(u16::from_le_bytes(self.take::<2>()?))
    }

    fn i16(&mut self) -> Result<i16, DnxError> {
        Ok(i16::from_le_bytes(self.take::<2>()?))
    }

    /// Decode one edge: `(u32 idx, u8 sel)`. Eraser sentinel → `None`.
    fn edge(&mut self) -> Result<Edge, DnxError> {
        let idx = self.u32()?;
        let sel = self.u8()?;
        if idx == ERASER_IDX && sel == ERASER_SEL {
            return Ok(None);
        }
        Ok(Some((idx, port_kind_of(sel)?)))
    }

    fn done(&self) -> bool {
        self.pos == self.bytes.len()
    }
}

/// Map a serialized port selector back to its `PortKind` (inverse of the
/// `PortKind::bits()` table, port.rs:20-26). An out-of-range selector is a
/// malformed blob.
fn port_kind_of(sel: u8) -> Result<PortKind, DnxError> {
    match sel {
        0 => Ok(PortKind::Principal),
        1 => Ok(PortKind::Aux0),
        2 => Ok(PortKind::Aux1),
        _ => Err(DnxError::ReadbackIncomplete),
    }
}

/// Read one record's edge for `kind` in the SAME field order `emit_record`
/// wrote them (canonical_hash.rs `emit_record`).
fn read_record(r: &mut Reader) -> Result<Record, DnxError> {
    let kind = r.u8()?;
    let mut rec = Record {
        kind,
        level: 0,
        delta0: 0,
        delta1: 0,
        var_id: 0,
        edges: Vec::new(),
    };
    match kind {
        KIND_ERASER => {}
        KIND_FREE_VAR => {
            // serialize emits `free_var_id()` (≤ 0x3FFF, net.rs:102) widened to
            // u32. A value outside that 14-bit domain is malformed — reject it
            // rather than let `alloc_free`'s mask (net.rs:233) silently truncate
            // (which would also hide a tampered high byte).
            let var_id = r.u32()?;
            if var_id > FREE_VAR_ID_MAX {
                return Err(DnxError::ReadbackIncomplete);
            }
            rec.var_id = var_id;
        }
        KIND_FAN_ABS => {
            // emit order: body (Aux0), var (Aux1).
            rec.edges.push((PortKind::Aux0, r.edge()?));
            rec.edges.push((PortKind::Aux1, r.edge()?));
        }
        KIND_FAN_APP => {
            // emit order: func (Principal), arg (Aux1).
            rec.edges.push((PortKind::Principal, r.edge()?));
            rec.edges.push((PortKind::Aux1, r.edge()?));
        }
        KIND_REP_IN => {
            rec.level = r.u16()?;
            rec.delta0 = r.i16()?;
            rec.delta1 = r.i16()?;
            rec.edges.push((PortKind::Aux0, r.edge()?));
            rec.edges.push((PortKind::Aux1, r.edge()?));
        }
        _ => return Err(DnxError::ReadbackIncomplete),
    }
    Ok(rec)
}

/// Allocate the agent for `rec`, returning a representative port (principal,
/// gen baked in) used to address every port of that agent in pass 2. An
/// eraser record allocates nothing — it maps to the virtual eraser port.
fn alloc_record<C: NetClassMarker>(
    net: &mut Net<Proper, C>,
    rec: &Record,
) -> Result<PortId, DnxError> {
    match rec.kind {
        KIND_ERASER => Ok(PortId::ERA),
        KIND_FREE_VAR => net.alloc_free(rec.var_id),
        KIND_FAN_ABS => Ok(net.alloc_abs()?.principal),
        KIND_FAN_APP => Ok(net.alloc_app()?.principal),
        KIND_REP_IN => Ok(net
            .alloc_rep_in(rec.level, rec.delta0, rec.delta1)?
            .principal),
        _ => Err(DnxError::ReadbackIncomplete),
    }
}

/// Resolve a stored peer-edge to a concrete `PortId` against the allocated
/// agents (`slots[idx].slot_idx` + the peer's gen). A `None` edge is the
/// eraser port; an out-of-range index is malformed.
fn resolve(slots: &[PortId], edge: Edge) -> Result<PortId, DnxError> {
    match edge {
        None => Ok(PortId::ERA),
        Some((idx, kind)) => {
            let base = *slots
                .get(idx as usize)
                .ok_or(DnxError::ReadbackIncomplete)?;
            Ok(PortId::new(base.slot_idx(), kind, base.gen_low()))
        }
    }
}

/// The inverse of `canonical_hash::serialize` (canonical-hash.md:59-93):
/// version-check, two-pass rebuild (alloc all agents, then wire every edge),
/// then `certify_canonical` → `Net<Canonical>`.
///
/// Two soundness properties this must uphold against an UNTRUSTED blob:
///
/// 1. No memory-amplification: the record count `n` is attacker-controlled, so
///    NOTHING is pre-sized from it. `read_record` consumes ≥1 byte per record,
///    so a bogus `n` runs out of real input immediately and yields `Err` having
///    allocated ~nothing. Every buffer (records / slots / arena) is sized from
///    the VALIDATED `records.len()`, never from raw `n`.
///
/// 2. No forged canonicity: pass 2 wires with `connect` (NOT `link_no_pair`) so
///    active-pair detection runs as each edge is laid. A canonical net is
///    normal — it has no active pairs — so a well-formed blob leaves both
///    frontiers empty and `certify_canonical` admits it. A crafted blob wiring
///    two principal ports together (a redex) populates `frontier1`, so
///    `certify_canonical` rejects it: the `Net<Canonical>` typestate (the
///    unforgeable canonicity proof, net.rs `CanonicalWitness`) cannot be forged.
fn deserialize<C: NetClassMarker>(bytes: &[u8]) -> Result<(Net<Canonical, C>, PortId), DnxError> {
    let mut r = Reader::new(bytes);
    if r.u8()? != CANON_HASH_V1_TAG {
        return Err(DnxError::ReadbackIncomplete);
    }
    // Attacker-controlled count: used ONLY as a loop bound, never to pre-size a
    // buffer. `read_record` is the real gate — it fails on the first missing
    // byte, so a forged `n` cannot amplify allocation.
    let n = r.u32()?;

    // Pass 0: decode every record (also validates field framing). `records`
    // grows on demand — its final length is the trustworthy agent count.
    let mut records: Vec<Record> = Vec::new();
    for _ in 0..n {
        records.push(read_record(&mut r)?);
    }
    // No trailing bytes — a clean, exact stream.
    if !r.done() {
        return Err(DnxError::ReadbackIncomplete);
    }
    // The root (index 0) must exist for a non-empty net.
    if records.is_empty() {
        return Err(DnxError::ReadbackIncomplete);
    }

    // Pass 1: allocate every agent so canonical index → live port is known. The
    // arena is sized from the VALIDATED record count (+1 sentinel slot), never
    // from the raw `n`.
    let count = records.len();
    let mut net = Net::<Proper, C>::new(((count as u32).saturating_add(1)).max(2));
    let mut slots: Vec<PortId> = Vec::with_capacity(count);
    for rec in &records {
        slots.push(alloc_record(&mut net, rec)?);
    }

    // Pass 2: wire each emitted edge with `connect`, which runs `detect_pair`.
    // Any active pair (a non-canonical redex in the untrusted blob) thus lands
    // in a frontier and is caught by `certify_canonical` below. A wire emitted
    // from one end only is written once; the partner port keeps the back-link.
    for (i, rec) in records.iter().enumerate() {
        let base = slots[i];
        for (local_kind, edge) in &rec.edges {
            let src = PortId::new(base.slot_idx(), *local_kind, base.gen_low());
            let dst = resolve(&slots, *edge)?;
            net.connect(src, dst, LOPath::root())?;
        }
    }

    let root = slots[0];
    let witness = certify_canonical(&net)?;
    Ok((into_canonical(net, witness), root))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::canonical_hash::canonical_hash;
    use crate::{normalize, LOPath, ΔL};

    // ── builders (canonical nets the distribution layer ships) ──────────────

    /// λx.x — exercises FAN_ABS + a self back-edge (var wired to body).
    fn id() -> (Net<Canonical, ΔL>, PortId) {
        let mut n = Net::<Proper, ΔL>::new(16);
        let abs = n.alloc_abs().unwrap();
        n.connect(abs.aux0, abs.aux1, LOPath::root()).unwrap();
        n.add_root("r".into(), abs.principal);
        let (c, _) = normalize(n).unwrap();
        (c, abs.principal)
    }

    /// λf.λx.f x — exercises nested FAN_ABS + FAN_APP + free-var-free wiring.
    fn church_one() -> (Net<Canonical, ΔL>, PortId) {
        let mut n = Net::<Proper, ΔL>::new(32);
        let abs1 = n.alloc_abs().unwrap();
        let abs2 = n.alloc_abs().unwrap();
        let app = n.alloc_app().unwrap();
        n.connect(abs1.aux0, abs2.principal, LOPath::root())
            .unwrap();
        n.connect(app.principal, abs1.aux1, LOPath::root()).unwrap();
        n.connect(app.aux1, abs2.aux1, LOPath::root()).unwrap();
        n.connect(abs2.aux0, app.aux0, LOPath::root()).unwrap();
        n.add_root("r".into(), abs1.principal);
        let (c, _) = normalize(n).unwrap();
        (c, abs1.principal)
    }

    /// λf.f f — exercises KIND_REP_IN + a shared/back-edge agent reached via
    /// two port-kinds (the C1 shape).
    fn dup() -> (Net<Canonical, ΔL>, PortId) {
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
        (c, abs.principal)
    }

    /// from_blob(to_blob(net)) is hash-equal to net — the round-trip oracle
    /// (distribution-mvp-plan.md §C/§D). Equality is by `canonical_hash`
    /// (canonical-hash.md:96 — invariant to slot/alloc order).
    fn assert_round_trip(net: &Net<Canonical, ΔL>, root: PortId) {
        let blob = to_blob(net, root).unwrap();
        let want = canonical_hash(net, root).unwrap();
        let (back, back_root): (Net<Canonical, ΔL>, PortId) = from_blob(&blob).unwrap();
        let got = canonical_hash(&back, back_root).unwrap();
        assert_eq!(want, got, "round-trip must be canonical_hash-equal");
        // And the re-serialized bytes are byte-identical (stronger than hash).
        assert_eq!(
            blob,
            to_blob(&back, back_root).unwrap(),
            "blob must be stable"
        );
    }

    #[test]
    fn round_trip_id() {
        let (c, r) = id();
        assert_round_trip(&c, r);
    }

    #[test]
    fn round_trip_church_one() {
        let (c, r) = church_one();
        assert_round_trip(&c, r);
    }

    #[test]
    fn round_trip_dup_rep() {
        let (c, r) = dup();
        assert_round_trip(&c, r);
    }

    // ── malformed input → Err, never panic (dnx axiom) ─────────────────────

    #[test]
    fn empty_blob_errs() {
        let r: Result<(Net<Canonical, ΔL>, PortId), _> = from_blob(&[]);
        assert!(matches!(r, Err(DnxError::ReadbackIncomplete)));
    }

    #[test]
    fn bad_version_errs() {
        let mut blob = to_blob(&id().0, id().1).unwrap();
        blob[0] = 0x02; // unknown format version
        let r: Result<(Net<Canonical, ΔL>, PortId), _> = from_blob(&blob);
        assert!(matches!(r, Err(DnxError::ReadbackIncomplete)));
    }

    #[test]
    fn truncated_blob_errs() {
        let blob = to_blob(&church_one().0, church_one().1).unwrap();
        // Drop the final byte — framing must reject, not panic.
        let r: Result<(Net<Canonical, ΔL>, PortId), _> = from_blob(&blob[..blob.len() - 1]);
        assert!(matches!(r, Err(DnxError::ReadbackIncomplete)));
    }

    #[test]
    fn trailing_bytes_err() {
        let mut blob = to_blob(&id().0, id().1).unwrap();
        blob.push(0x00); // extra trailing byte
        let r: Result<(Net<Canonical, ΔL>, PortId), _> = from_blob(&blob);
        assert!(matches!(r, Err(DnxError::ReadbackIncomplete)));
    }

    #[test]
    fn bad_edge_index_errs() {
        // A record count of 1 (an id λx.x: one FAN_ABS) but its body edge
        // points at canonical index 9 (out of range) → reject.
        let mut blob = vec![CANON_HASH_V1_TAG];
        blob.extend_from_slice(&1u32.to_le_bytes()); // n = 1
        blob.push(KIND_FAN_ABS);
        blob.extend_from_slice(&9u32.to_le_bytes()); // body → idx 9 (oob)
        blob.push(1); // sel Aux0
        blob.extend_from_slice(&ERASER_IDX.to_le_bytes()); // var → eraser
        blob.push(ERASER_SEL);
        let r: Result<(Net<Canonical, ΔL>, PortId), _> = from_blob(&blob);
        assert!(matches!(r, Err(DnxError::ReadbackIncomplete)));
    }

    #[test]
    fn bad_selector_errs() {
        let mut blob = vec![CANON_HASH_V1_TAG];
        blob.extend_from_slice(&1u32.to_le_bytes());
        blob.push(KIND_FAN_ABS);
        blob.extend_from_slice(&0u32.to_le_bytes());
        blob.push(7); // selector 7 is not a valid PortKind
        blob.extend_from_slice(&ERASER_IDX.to_le_bytes());
        blob.push(ERASER_SEL);
        let r: Result<(Net<Canonical, ΔL>, PortId), _> = from_blob(&blob);
        assert!(matches!(r, Err(DnxError::ReadbackIncomplete)));
    }

    // ── adversarial: untrusted-input soundness/DoS (dist-threat-model) ───────

    #[test]
    fn huge_record_count_no_amplification() {
        // A 5-byte blob whose record count `n` is 0xFFFFFFFF. The decoder must
        // NEVER pre-size any buffer (records / slots / arena) from this
        // unvalidated length — it must run out of real bytes at the FIRST
        // `read_record` and return `Err`, allocating ~nothing (memory
        // amplification DoS: a 5-byte input forcing a multi-GB alloc).
        let mut blob = vec![CANON_HASH_V1_TAG];
        blob.extend_from_slice(&u32::MAX.to_le_bytes()); // n = 0xFFFFFFFF
        let r: Result<(Net<Canonical, ΔL>, PortId), _> = from_blob(&blob);
        assert!(matches!(r, Err(DnxError::ReadbackIncomplete)));
    }

    #[test]
    fn forged_active_pair_rejected() {
        // Two FAN_APP records whose PRINCIPAL ports are wired to each other:
        // an active pair (Principal↔Principal). A canonical net has NO active
        // pairs, so `certify_canonical` MUST reject this — otherwise the
        // forged blob would mint a fake `Net<Canonical>` (the unforgeable
        // canonicity proof, net.rs `CanonicalWitness`) and could poison the
        // content-addressed cache. `from_blob` must return `Err`, never `Ok`.
        let mut blob = vec![CANON_HASH_V1_TAG];
        blob.extend_from_slice(&2u32.to_le_bytes()); // n = 2
                                                     // rec0 = FAN_APP: principal → idx1.Principal ; aux1 → eraser
        blob.push(KIND_FAN_APP);
        blob.extend_from_slice(&1u32.to_le_bytes());
        blob.push(0); // sel Principal
        blob.extend_from_slice(&ERASER_IDX.to_le_bytes());
        blob.push(ERASER_SEL);
        // rec1 = FAN_APP: principal → idx0.Principal ; aux1 → eraser
        blob.push(KIND_FAN_APP);
        blob.extend_from_slice(&0u32.to_le_bytes());
        blob.push(0); // sel Principal
        blob.extend_from_slice(&ERASER_IDX.to_le_bytes());
        blob.push(ERASER_SEL);
        let r: Result<(Net<Canonical, ΔL>, PortId), _> = from_blob(&blob);
        assert!(
            matches!(r, Err(DnxError::ReadbackIncomplete)),
            "a forged active-pair blob must NOT mint a Canonical net, got Ok"
        );
    }

    /// Build a blob encoding a chain of `len` FAN_ABS agents: agent i's body
    /// (Aux0) → agent i+1; the last body → eraser. Var (Aux1) of each → eraser.
    /// A deep chain that a recursive serializer would stack-overflow on.
    fn abs_chain_blob(len: u32) -> Vec<u8> {
        let mut blob = vec![CANON_HASH_V1_TAG];
        blob.extend_from_slice(&len.to_le_bytes());
        for i in 0..len {
            blob.push(KIND_FAN_ABS);
            if i + 1 < len {
                blob.extend_from_slice(&(i + 1).to_le_bytes()); // body → next
                blob.push(1); // sel Aux0
            } else {
                blob.extend_from_slice(&ERASER_IDX.to_le_bytes()); // last → eraser
                blob.push(ERASER_SEL);
            }
            blob.extend_from_slice(&ERASER_IDX.to_le_bytes()); // var → eraser
            blob.push(ERASER_SEL);
        }
        blob
    }

    #[test]
    fn deep_chain_no_stack_overflow() {
        // A deep (but well-formed) chain must NOT blow the stack when it is
        // later serialized/hashed (the verify-on-read path re-hashes every
        // loaded blob). 200k frames overflows a recursive DFS; an iterative
        // walk handles it. The net is LEGAL, so re-serialization must succeed
        // and round-trip — no panic, no spurious error.
        let blob = abs_chain_blob(200_000);
        let (net, root): (Net<Canonical, ΔL>, PortId) =
            from_blob(&blob).expect("deep chain decodes");
        // Re-hash (the disk verify-on-read step) must not overflow.
        let h = canonical_hash(&net, root).expect("deep chain hashes");
        // And the round-trip is byte-stable.
        assert_eq!(to_blob(&net, root).unwrap(), blob, "deep chain round-trips");
        assert_eq!(h.len(), 32);
    }
}
