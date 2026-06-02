use crate::arena::Arena;
use crate::class::{Canonical, NetClassMarker, NetState, Proper};
use crate::slot::{
    Slot, TAG_AUX0_ERASED, TAG_AUX1_ERASED, TAG_ERASING_ABS, TAG_FAN_ABS, TAG_FAN_APP, TAG_FREE,
    TAG_REP_IN_UNPAIRED,
};
use crate::{DnxError, LOPath, PortId, PortKind, PrincipalPortId};
use std::collections::{BTreeMap, HashMap};
use std::marker::PhantomData;
use std::sync::Arc;

#[cfg(test)]
const FLAG_HAS_ERA: u8 = 0b01;
#[cfg(test)]
const FLAG_HAS_REP: u8 = 0b10;
const FLAG_PENDING_C1: u8 = 0x04;

/// An active pair: two **principal** ports facing each other — the only kind of
/// interaction-net redex. Each end is a [`PrincipalPortId`], so an aux or free
/// port cannot be placed here — correct by construction, no runtime guard needed.
#[derive(Clone, Debug)]
pub(crate) struct ActivePair {
    pub(crate) p0: PrincipalPortId,
    pub(crate) p1: PrincipalPortId,
    pub(crate) lo: LOPath,
}

impl ActivePair {
    /// Construct an active pair, returning `None` unless both ports are principal.
    pub(crate) fn new(p0: PortId, p1: PortId, lo: LOPath) -> Option<ActivePair> {
        Some(ActivePair {
            p0: PrincipalPortId::new(p0)?,
            p1: PrincipalPortId::new(p1)?,
            lo,
        })
    }
}

#[derive(Clone, Debug)]
pub struct C4Candidate {
    pub rep_principal: PortId,
    pub app_aux0: PortId,
    pub lo: LOPath,
}

pub struct AgentPorts {
    pub principal: PortId,
    pub aux0: PortId,
    pub aux1: PortId,
}

pub struct Net<S: NetState, C: NetClassMarker> {
    pub(crate) arena: Arena,
    pub(crate) frontier1: BTreeMap<LOPath, ActivePair>,
    pub(crate) frontier2: BTreeMap<LOPath, C4Candidate>,
    pub(crate) free_slots: HashMap<Arc<str>, PortId>,
    pub(crate) net_flags: u8,
    _state: PhantomData<(S, C)>,
}

pub(crate) struct CanonicalWitness(());

pub(crate) fn certify_canonical<C: NetClassMarker>(
    net: &Net<Proper, C>,
) -> Result<CanonicalWitness, DnxError> {
    if net.frontier1.is_empty() && net.frontier2.is_empty() && !net.net_pending_c1() {
        Ok(CanonicalWitness(()))
    } else {
        Err(DnxError::ReadbackIncomplete)
    }
}

pub(crate) fn into_canonical<C: NetClassMarker>(
    net: Net<Proper, C>,
    _witness: CanonicalWitness,
) -> Net<Canonical, C> {
    Net {
        arena: net.arena,
        frontier1: net.frontier1,
        frontier2: net.frontier2,
        free_slots: net.free_slots,
        net_flags: net.net_flags,
        _state: PhantomData,
    }
}

/// Public view of a slot for readback (psi_S, psi_native).
#[derive(Copy, Clone, Debug)]
pub struct SlotView {
    pub tag: u8,
    pub principal: u32,
    pub aux0: u32,
    pub aux1: u32,
    pub data: u16,
    pub delta0: i16,
    pub delta1: i16,
}

impl SlotView {
    pub fn is_fan(self) -> bool {
        (self.tag & 0x0C) == 0x04
    }
    pub fn is_rep(self) -> bool {
        (self.tag & 0x0C) == 0x08
    }
    pub fn is_free(self) -> bool {
        (self.tag & 0x0C) == 0x00
    }
    pub fn is_prim(self) -> bool {
        (self.tag & 0x0E) == 0x0C
    }
    pub fn fan_is_abs(self) -> bool {
        (self.tag & 0x01) != 0
    }
    pub fn free_var_id(self) -> u16 {
        self.data & 0x3FFF
    }
}

impl<S: NetState, C: NetClassMarker> Net<S, C> {
    /// Read slot at given PortId (uses slot_idx from port).
    pub fn slot_view(&self, port: PortId) -> SlotView {
        let s = self.arena.slot(port.slot_idx());
        SlotView {
            tag: s.tag,
            principal: s.principal,
            aux0: s.aux0,
            aux1: s.aux1,
            data: s.data,
            delta0: s.delta0,
            delta1: s.delta1,
        }
    }

    /// Follow a port to get the port it's connected to (peer).
    pub fn peer(&self, port: PortId) -> PortId {
        if port.is_eraser() || port.is_null() {
            return port;
        }
        let s = self.arena.slot(port.slot_idx());
        let raw = match port.port_kind() {
            PortKind::Principal => s.principal,
            PortKind::Aux0 => s.aux0,
            PortKind::Aux1 => s.aux1,
        };
        PortId::from_raw(raw)
    }

    /// Root ports (free variables / named outputs from add_root).
    pub fn roots(&self) -> &std::collections::HashMap<Arc<str>, PortId> {
        &self.free_slots
    }

    pub fn slot_is_live(&self, port: PortId) -> bool {
        !port.is_eraser() && !port.is_null() && self.arena.is_live(port.slot_idx())
    }

    #[cfg(test)]
    pub(crate) fn net_has_rep(&self) -> bool {
        (self.net_flags & FLAG_HAS_REP) != 0
    }
    #[cfg(test)]
    pub(crate) fn net_has_era(&self) -> bool {
        (self.net_flags & FLAG_HAS_ERA) != 0
    }
    pub(crate) fn net_pending_c1(&self) -> bool {
        (self.net_flags & FLAG_PENDING_C1) != 0
    }
    pub(crate) fn set_pending_c1(&mut self) {
        self.net_flags |= FLAG_PENDING_C1;
    }
    pub(crate) fn clear_pending_c1(&mut self) {
        self.net_flags &= !FLAG_PENDING_C1;
    }
}

impl<C: NetClassMarker> Net<Proper, C> {
    /// GPU amortized mode: encode arena as flat u32 array.
    pub fn encode_arena_gpu(&self) -> Vec<u32> {
        self.arena.encode_gpu()
    }

    /// GPU amortized mode: encode active frontier pairs as (p0_raw, p1_raw, lo_bits[4], lo_len).
    pub fn encode_frontier_gpu(&self) -> Vec<(u32, u32, [u32; 4], u8)> {
        self.frontier1
            .values()
            .map(|p| {
                let (bits, len) = p.lo.gpu_bits();
                (p.p0.get().raw(), p.p1.get().raw(), bits, len)
            })
            .collect()
    }

    pub fn new(capacity: u32) -> Net<Proper, C> {
        Net {
            arena: Arena::new(capacity),
            frontier1: BTreeMap::new(),
            frontier2: BTreeMap::new(),
            free_slots: HashMap::new(),
            net_flags: C::CLASS_BITS,
            _state: PhantomData,
        }
    }

    pub fn eraser_port() -> PortId {
        PortId::ERA
    }

    pub fn alloc_abs(&mut self) -> Result<AgentPorts, DnxError> {
        self.alloc_agent(TAG_FAN_ABS, 0, 0, 0)
    }

    pub fn alloc_app(&mut self) -> Result<AgentPorts, DnxError> {
        self.alloc_agent(TAG_FAN_APP, 0, 0, 0)
    }

    pub fn alloc_rep_in(
        &mut self,
        level: u16,
        delta0: i16,
        delta1: i16,
    ) -> Result<AgentPorts, DnxError> {
        debug_assert!(level <= 385);
        self.alloc_agent(TAG_REP_IN_UNPAIRED, level, delta0, delta1)
    }

    pub(crate) fn alloc_agent(
        &mut self,
        tag: u8,
        data: u16,
        delta0: i16,
        delta1: i16,
    ) -> Result<AgentPorts, DnxError> {
        let idx = self.arena.alloc_slot()?;
        let s = self.arena.slot_mut(idx);
        s.tag = tag;
        s.data = data;
        s.delta0 = delta0;
        s.delta1 = delta1;
        Ok(self.ports(idx))
    }

    pub fn alloc_free(&mut self, var_id: u32) -> Result<PortId, DnxError> {
        let idx = self.arena.alloc_slot()?;
        let s = self.arena.slot_mut(idx);
        s.tag = TAG_FREE;
        s.data = (var_id & 0x3FFF) as u16;
        let g = (s.generation & 1) as u8;
        Ok(PortId::new(idx, PortKind::Principal, g))
    }

    fn ports(&self, idx: u32) -> AgentPorts {
        let g = (self.arena.slot(idx).generation & 1) as u8;
        AgentPorts {
            principal: PortId::new(idx, PortKind::Principal, g),
            aux0: PortId::new(idx, PortKind::Aux0, g),
            aux1: PortId::new(idx, PortKind::Aux1, g),
        }
    }

    /// Connect two ports WITHOUT adding an active pair. Used for root→result wires.
    pub(crate) fn link_no_pair(&mut self, a: PortId, b: PortId) {
        self.write_port(a, b);
        self.write_port(b, a);
    }

    pub fn connect(&mut self, a: PortId, b: PortId, lo: LOPath) -> Result<(), DnxError> {
        self.write_port(a, b);
        self.write_port(b, a);
        self.detect_pair(a, b, lo);
        Ok(())
    }

    fn write_port(&mut self, port: PortId, val: PortId) {
        if port.is_eraser() || port.is_null() {
            return;
        }
        let s = self.arena.slot_mut(port.slot_idx());
        match port.port_kind() {
            PortKind::Principal => s.principal = val.raw(),
            // An eraser wired to a replicator's auxiliary port marks that branch dead
            // = partial unpaired replicator decay (main.tex ΔK: "all auxiliary ports
            // connected to erasers should be removed"). The erased-flag is the single
            // source of truth for `c3_rep_decay`, so it must track the wire whatever
            // path delivered the eraser — β/`connect`, not only `set_eraser_on_port`.
            // Correct by construction: flag ⇔ aux=ERA, so a shared unused binder's
            // feedback decays instead of commuting (R5) into a stuck fan-out.
            PortKind::Aux0 => {
                s.aux0 = val.raw();
                if val.is_eraser() && s.is_rep() {
                    s.tag |= TAG_AUX0_ERASED;
                }
            }
            PortKind::Aux1 => {
                s.aux1 = val.raw();
                if val.is_eraser() && s.is_rep() {
                    s.tag |= TAG_AUX1_ERASED;
                }
            }
        }
    }

    fn detect_pair(&mut self, a: PortId, b: PortId, lo: LOPath) {
        match (a.port_kind(), b.port_kind()) {
            (PortKind::Principal, PortKind::Principal) if !a.is_null() && !b.is_null() => {
                if let Some(ap) = ActivePair::new(a, b, lo.clone()) {
                    self.frontier1.insert(lo, ap);
                }
            }
            (PortKind::Principal, PortKind::Aux0)
                if self.is_rep_port(a) && self.is_app_fan_port(b) =>
            {
                self.frontier2.insert(
                    lo.clone(),
                    C4Candidate {
                        rep_principal: a,
                        app_aux0: b,
                        lo,
                    },
                );
            }
            (PortKind::Aux0, PortKind::Principal)
                if self.is_app_fan_port(a) && self.is_rep_port(b) =>
            {
                self.frontier2.insert(
                    lo.clone(),
                    C4Candidate {
                        rep_principal: b,
                        app_aux0: a,
                        lo,
                    },
                );
            }
            _ => {}
        }
    }

    fn is_rep_port(&self, p: PortId) -> bool {
        !p.is_eraser() && !p.is_null() && self.arena.slot(p.slot_idx()).is_rep()
    }

    fn is_app_fan_port(&self, p: PortId) -> bool {
        if p.is_eraser() || p.is_null() {
            return false;
        }
        let s = self.arena.slot(p.slot_idx());
        s.is_fan() && s.fan_is_app()
    }

    pub(crate) fn set_eraser_on_port(&mut self, port: PortId) {
        if port.is_eraser() || port.is_null() {
            return;
        }
        let idx = port.slot_idx();
        match port.port_kind() {
            PortKind::Principal => {
                self.arena.slot_mut(idx).principal = PortId::ERA.raw();
            }
            PortKind::Aux0 => {
                let s = self.arena.slot_mut(idx);
                s.aux0 = PortId::ERA.raw();
                if s.is_rep() {
                    s.tag |= TAG_AUX0_ERASED;
                }
                self.set_pending_c1();
            }
            PortKind::Aux1 => {
                let s = self.arena.slot_mut(idx);
                s.aux1 = PortId::ERA.raw();
                if s.is_rep() {
                    s.tag |= TAG_AUX1_ERASED;
                }
                if s.fan_is_abs() {
                    s.tag |= TAG_ERASING_ABS;
                }
                self.set_pending_c1();
            }
        }
    }

    pub(crate) fn slot(&self, port: PortId) -> &Slot {
        self.arena.slot(port.slot_idx())
    }

    pub(crate) fn slot_mut(&mut self, port: PortId) -> &mut Slot {
        self.arena.slot_mut(port.slot_idx())
    }

    pub fn add_root(&mut self, name: Arc<str>, port: PortId) {
        self.free_slots.insert(name, port);
    }

    pub fn agent_count(&self) -> usize {
        self.arena.live().len()
    }

    pub fn active_pair_count(&self) -> usize {
        self.frontier1.len()
    }

    pub(crate) fn retire(&mut self, idx: u32) {
        self.arena.retire_slot(idx);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::class::{ΔA, ΔI, ΔK, ΔL};

    #[test]
    fn class_flags_and_eraser_port() {
        let nk = Net::<Proper, ΔK>::new(16);
        assert!(nk.net_has_rep() && nk.net_has_era());
        let nl = Net::<Proper, ΔL>::new(16);
        assert!(!nl.net_has_rep() && !nl.net_has_era());
        let ni = Net::<Proper, ΔI>::new(16);
        assert!(ni.net_has_rep() && !ni.net_has_era());
        let na = Net::<Proper, ΔA>::new(16);
        assert!(!na.net_has_rep() && na.net_has_era());
        assert!(Net::<Proper, ΔL>::eraser_port().is_eraser());
    }

    #[test]
    fn alloc_sets_tag_and_rep_data() -> Result<(), DnxError> {
        let mut n = Net::<Proper, ΔK>::new(16);
        let abs = n.alloc_abs()?;
        assert!(n.arena.slot(abs.principal.slot_idx()).fan_is_abs());
        let app = n.alloc_app()?;
        assert!(n.arena.slot(app.principal.slot_idx()).fan_is_app());
        let rep = n.alloc_rep_in(1, -1, 0)?;
        let rs = n.arena.slot(rep.principal.slot_idx());
        assert!(rs.is_rep() && rs.rep_is_in() && rs.rep_is_unpaired());
        assert_eq!((rs.data, rs.delta0, rs.delta1), (1, -1, 0));
        Ok(())
    }

    #[test]
    fn principal_pair_routes_to_frontier1() -> Result<(), DnxError> {
        let mut n = Net::<Proper, ΔL>::new(16);
        let f = n.alloc_app()?;
        let g = n.alloc_app()?;
        n.connect(f.principal, g.principal, LOPath::root())?;
        assert_eq!((n.frontier1.len(), n.frontier2.len()), (1, 0));
        if let Some(p) = n.frontier1.values().next() {
            assert_eq!((p.p0.get(), p.p1.get()), (f.principal, g.principal));
            assert_eq!(p.lo, LOPath::root());
        }
        Ok(())
    }

    #[test]
    fn rep_principal_to_app_aux0_routes_to_frontier2() -> Result<(), DnxError> {
        let mut n = Net::<Proper, ΔI>::new(16);
        let rep = n.alloc_rep_in(1, 0, 0)?;
        let app = n.alloc_app()?;
        n.connect(rep.principal, app.aux0, LOPath::root())?;
        assert_eq!((n.frontier1.len(), n.frontier2.len()), (0, 1));
        if let Some(c) = n.frontier2.values().next() {
            assert_eq!((c.rep_principal, c.app_aux0), (rep.principal, app.aux0));
            assert_eq!(c.lo, LOPath::root());
        }
        Ok(())
    }

    #[test]
    fn plain_wire_routes_to_neither() -> Result<(), DnxError> {
        let mut n = Net::<Proper, ΔL>::new(16);
        let f = n.alloc_abs()?;
        let g = n.alloc_app()?;
        n.connect(f.aux0, g.aux1, LOPath::root())?;
        assert_eq!((n.frontier1.len(), n.frontier2.len()), (0, 0));
        Ok(())
    }

    #[test]
    fn eraser_on_rep_aux1_sets_flag_and_pending_c1() -> Result<(), DnxError> {
        let mut n = Net::<Proper, ΔK>::new(16);
        let rep = n.alloc_rep_in(1, 0, 0)?;
        n.set_eraser_on_port(rep.aux1);
        let s = n.arena.slot(rep.principal.slot_idx());
        assert!(s.rep_aux1_erased());
        assert_eq!(s.aux1, PortId::ERA.raw());
        assert!(n.net_pending_c1());
        Ok(())
    }

    #[test]
    fn witness_gates_canonical_transition() -> Result<(), DnxError> {
        let n = Net::<Proper, ΔL>::new(16);
        let w = certify_canonical(&n)?;
        let _c: Net<Canonical, ΔL> = into_canonical(n, w);

        let mut m = Net::<Proper, ΔL>::new(16);
        let f = m.alloc_app()?;
        let g = m.alloc_app()?;
        m.connect(f.principal, g.principal, LOPath::root())?;
        assert!(certify_canonical(&m).is_err());
        Ok(())
    }
}
