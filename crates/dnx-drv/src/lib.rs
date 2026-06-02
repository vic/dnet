#![forbid(unsafe_code)]

//! Userland derivations for Dnx: our own flat, input-addressed build
//! description plus a builder runner. Not the cppNix ATerm `.drv` format.
//! See `vic/plans/dnx-demo-arch.md` §3.

mod drv;
mod error;

pub use drv::{from_attrs, Derivation};
pub use error::DrvError;
