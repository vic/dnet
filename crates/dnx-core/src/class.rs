mod sealed {
    pub trait Sealed {}
}

pub trait NetClassMarker: sealed::Sealed {
    const CLASS_BITS: u8;
}

pub struct ΔL;
pub struct ΔA;
pub struct ΔI;
pub struct ΔK;

impl sealed::Sealed for ΔL {}
impl sealed::Sealed for ΔA {}
impl sealed::Sealed for ΔI {}
impl sealed::Sealed for ΔK {}

impl NetClassMarker for ΔL {
    const CLASS_BITS: u8 = 0b00;
}
impl NetClassMarker for ΔA {
    const CLASS_BITS: u8 = 0b01;
}
impl NetClassMarker for ΔI {
    const CLASS_BITS: u8 = 0b10;
}
impl NetClassMarker for ΔK {
    const CLASS_BITS: u8 = 0b11;
}

pub struct Proper;
pub struct Canonical;

impl sealed::Sealed for Proper {}
impl sealed::Sealed for Canonical {}

pub trait NetState: sealed::Sealed {}
impl NetState for Proper {}
impl NetState for Canonical {}

pub trait IsRepNet: NetClassMarker {}
impl IsRepNet for ΔI {}
impl IsRepNet for ΔK {}

pub trait IsEraNet: NetClassMarker {}
impl IsEraNet for ΔA {}
impl IsEraNet for ΔK {}
