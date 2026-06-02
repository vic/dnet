#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct PortId(u32);

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum PortKind {
    Principal,
    Aux0,
    Aux1,
}

/// Port direction in the child↔parent duality (main.tex:951 "every wire connects a
/// child port with a parent port"). Same-polarity wires are illegal.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(crate) enum Polarity {
    Child,
    Parent,
}

impl PortKind {
    fn from_bits(bits: u32) -> PortKind {
        match bits & 0x3 {
            0 => PortKind::Principal,
            1 => PortKind::Aux0,
            _ => PortKind::Aux1,
        }
    }

    fn bits(self) -> u32 {
        match self {
            PortKind::Principal => 0,
            PortKind::Aux0 => 1,
            PortKind::Aux1 => 2,
        }
    }
}

impl PortId {
    pub const NULL: PortId = PortId(0);
    pub const ERA: PortId = PortId(0b10);

    pub fn new(slot_idx: u32, kind: PortKind, gen_low: u8) -> PortId {
        PortId((slot_idx << 4) | (kind.bits() << 2) | u32::from(gen_low & 1))
    }

    pub fn slot_idx(self) -> u32 {
        self.0 >> 4
    }

    pub fn port_kind(self) -> PortKind {
        PortKind::from_bits(self.0 >> 2)
    }

    pub fn is_eraser(self) -> bool {
        (self.0 >> 1) & 1 == 1
    }

    pub fn gen_low(self) -> u8 {
        (self.0 & 1) as u8
    }

    pub fn is_null(self) -> bool {
        self.0 == 0
    }

    pub fn raw(self) -> u32 {
        self.0
    }

    pub fn from_raw(v: u32) -> PortId {
        PortId(v)
    }
}

/// A [`PortId`] proven to be a principal port. Positions the interaction rules
/// require to be principal — e.g. the two ends of an active pair — store this
/// instead of a bare `PortId`, so an aux or free port cannot be placed there.
/// Correct by construction: the only way in is [`PrincipalPortId::new`].
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) struct PrincipalPortId(PortId);

impl PrincipalPortId {
    /// `Some` iff `p` is a principal port.
    pub(crate) fn new(p: PortId) -> Option<PrincipalPortId> {
        match p.port_kind() {
            PortKind::Principal => Some(PrincipalPortId(p)),
            _ => None,
        }
    }

    /// The underlying port.
    pub(crate) fn get(self) -> PortId {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn portid_roundtrip() {
        let p = PortId::new(5, PortKind::Aux1, 1);
        assert_eq!(p.slot_idx(), 5);
        assert_eq!(p.port_kind(), PortKind::Aux1);
        assert_eq!(p.gen_low(), 1);
        assert!(!p.is_eraser());
    }

    #[test]
    fn sentinels() {
        assert!(PortId::ERA.is_eraser());
        assert!(PortId::NULL.is_null());
        assert_eq!(PortId::NULL.slot_idx(), 0);
    }
}
