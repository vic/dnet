#[repr(C, align(32))]
#[derive(Copy, Clone, Debug)]
pub(crate) struct Slot {
    pub(crate) tag: u8,
    pub(crate) claim: u8,
    _pad0: [u8; 2],
    pub(crate) generation: u32,
    pub(crate) principal: u32,
    pub(crate) aux0: u32,
    pub(crate) aux1: u32,
    pub(crate) data: u16,
    pub(crate) delta0: i16,
    pub(crate) delta1: i16,
    pub(crate) epoch: u16,
    _pad1: [u8; 4],
}

const _: () = assert!(core::mem::size_of::<Slot>() == 32);
const _: () = assert!(core::mem::align_of::<Slot>() == 32);

pub(crate) const TAG_FREE: u8 = 0b0000;
pub(crate) const TAG_FAN_APP: u8 = 0b0100;
pub(crate) const TAG_FAN_ABS: u8 = 0b0101;
pub(crate) const TAG_REP_IN_UNPAIRED: u8 = 0b1000;
pub(crate) const TAG_REP_IN_UNKNOWN: u8 = 0b1010;
pub(crate) const TAG_REP_OUT_UNKNOWN: u8 = 0b1011;
pub(crate) const TAG_AUX0_ERASED: u8 = 0x40;
pub(crate) const TAG_AUX1_ERASED: u8 = 0x80;
pub(crate) const TAG_ERASING_ABS: u8 = 0x10;
pub(crate) const TAG_C1_MARK: u8 = 0x20;

impl Slot {
    pub(crate) const EMPTY: Slot = Slot {
        tag: 0,
        claim: 0,
        _pad0: [0; 2],
        generation: 0,
        principal: 0,
        aux0: 0,
        aux1: 0,
        data: 0,
        delta0: 0,
        delta1: 0,
        epoch: 0,
        _pad1: [0; 4],
    };

    pub(crate) fn is_free(&self) -> bool {
        (self.tag & 0x0C) == 0x00
    }
    pub(crate) fn is_fan(&self) -> bool {
        (self.tag & 0x0C) == 0x04
    }
    pub(crate) fn is_rep(&self) -> bool {
        (self.tag & 0x0C) == 0x08
    }
    pub(crate) fn is_prim(&self) -> bool {
        (self.tag & 0x0E) == 0x0C
    }
    #[cfg(test)]
    pub(crate) fn rep_is_in(&self) -> bool {
        (self.tag & 0x01) == 0
    }
    pub(crate) fn rep_is_unpaired(&self) -> bool {
        (self.tag & 0x02) == 0
    }
    pub(crate) fn fan_is_abs(&self) -> bool {
        (self.tag & 0x01) != 0
    }

    /// Port polarity in the child↔parent duality (main.tex:944/950/954/956). `None`
    /// for non-fan/non-rep agents (prim/free/era/ref are outside the duality system).
    /// App: principal=Child(fn), aux0=Parent(result), aux1=Child(arg). Abs: principal=
    /// Parent, aux0=Child(body), aux1=Parent(var). REP_IN: principal=Child, aux=Parent.
    /// REP_OUT: principal=Parent, aux=Child. (FAN_ABS and REP_OUT share tag bit 0.)
    pub(crate) fn polarity(&self, kind: crate::PortKind) -> Option<crate::port::Polarity> {
        use crate::port::Polarity::{Child, Parent};
        use crate::PortKind;
        let fan = self.is_fan();
        if !fan && !self.is_rep() {
            return None;
        }
        let flipped = (self.tag & 0x01) != 0; // FAN_ABS or REP_OUT
        Some(match kind {
            PortKind::Principal if flipped => Parent,
            PortKind::Principal => Child,
            PortKind::Aux0 if fan => {
                if flipped {
                    Child
                } else {
                    Parent
                }
            }
            PortKind::Aux1 if fan => {
                if flipped {
                    Parent
                } else {
                    Child
                }
            }
            _ if flipped => Child,
            _ => Parent,
        })
    }
    pub(crate) fn fan_is_app(&self) -> bool {
        (self.tag & 0x01) == 0
    }
    pub(crate) fn rep_aux1_erased(&self) -> bool {
        (self.tag & 0x80) != 0
    }
    pub(crate) fn rep_aux0_erased(&self) -> bool {
        (self.tag & 0x40) != 0
    }
    pub(crate) fn is_c1_marked(&self) -> bool {
        (self.tag & 0x20) != 0
    }
    #[cfg(test)]
    pub(crate) fn abs_is_erasing(&self) -> bool {
        (self.tag & 0x10) != 0
    }
    #[cfg(test)]
    pub(crate) fn rep_c3_candidate(&self) -> bool {
        (self.tag & 0xCA) == 0x88
    }
    #[cfg(test)]
    pub(crate) fn is_value_head(&self) -> bool {
        self.is_prim() || (self.tag & 0x0D) == 0x05
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::{align_of, size_of};

    fn t(tag: u8) -> Slot {
        Slot { tag, ..Slot::EMPTY }
    }

    #[test]
    fn slot_is_32_bytes_2_per_cache_line() {
        assert_eq!(size_of::<Slot>(), 32);
        assert_eq!(align_of::<Slot>(), 32);
    }

    #[test]
    fn variant_table_round_trips() {
        assert!(t(0b0000).is_free());
        assert!(t(0b0100).is_fan() && t(0b0100).fan_is_app());
        assert!(t(0b0101).is_fan() && t(0b0101).fan_is_abs());
        assert!(t(0b1000).is_rep() && t(0b1000).rep_is_in() && t(0b1000).rep_is_unpaired());
        assert!(t(0b1001).is_rep() && !t(0b1001).rep_is_in() && t(0b1001).rep_is_unpaired());
        assert!(t(0b1010).is_rep() && t(0b1010).rep_is_in() && !t(0b1010).rep_is_unpaired());
        assert!(t(0b1011).is_rep() && !t(0b1011).rep_is_in() && !t(0b1011).rep_is_unpaired());
        assert!(t(0xC).is_prim() && t(0xD).is_prim());
    }

    #[test]
    fn polarity_matches_paper_child_parent_duality() {
        use crate::port::Polarity::{Child, Parent};
        use crate::PortKind::{Aux0, Aux1, Principal};
        // App (main.tex:944,950): principal=Child(fn), aux0=Parent(result), aux1=Child(arg).
        assert_eq!(t(0b0100).polarity(Principal), Some(Child));
        assert_eq!(t(0b0100).polarity(Aux0), Some(Parent));
        assert_eq!(t(0b0100).polarity(Aux1), Some(Child));
        // Abs (main.tex:950 + β-validity): principal=Parent, aux0=Child(body), aux1=Parent(var).
        assert_eq!(t(0b0101).polarity(Principal), Some(Parent));
        assert_eq!(t(0b0101).polarity(Aux0), Some(Child));
        assert_eq!(t(0b0101).polarity(Aux1), Some(Parent));
        // REP_IN (main.tex:954): principal=Child, aux=Parent.
        assert_eq!(t(0b1010).polarity(Principal), Some(Child));
        assert_eq!(t(0b1010).polarity(Aux0), Some(Parent));
        // REP_OUT (main.tex:956): principal=Parent, aux=Child.
        assert_eq!(t(0b1011).polarity(Principal), Some(Parent));
        assert_eq!(t(0b1011).polarity(Aux0), Some(Child));
        // prim / free are outside the duality system.
        assert_eq!(t(0b0000).polarity(Principal), None);
        assert_eq!(t(0x0C).polarity(Principal), None);
    }

    #[test]
    fn prim_predicate_excludes_0xe_0xf() {
        assert!(!t(0x0E).is_prim() && !t(0x0E).is_rep() && !t(0x0E).is_fan());
        assert!(!t(0x0F).is_prim() && !t(0x0F).is_rep() && !t(0x0F).is_fan());
    }

    #[test]
    fn upper_nibble_flags() {
        assert!(t(0xA8).rep_aux1_erased() && !t(0xA8).rep_aux0_erased());
        assert!(t(0x20).is_c1_marked());
        assert!(t(0x15).fan_is_abs() && t(0x15).abs_is_erasing());
        // C3 candidate: rep, in, unpaired, aux1 erased, aux0 not
        assert!(t(0x88).rep_c3_candidate());
        assert!(!t(0x08).rep_c3_candidate());
    }

    #[test]
    fn value_head_is_prim_or_fanabs() {
        assert!(t(0xC).is_value_head() && t(0xD).is_value_head());
        assert!(t(0b0101).is_value_head()); // FanAbs
        assert!(!t(0b0100).is_value_head()); // FanApp
        assert!(!t(0b1000).is_value_head()); // RepIn
    }
}
