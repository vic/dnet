#![forbid(unsafe_code)]

pub mod alpha;
pub mod pass0;
pub mod pass1;
pub mod pass2;

pub use alpha::alpha_rename;
pub use pass0::pass0;
pub use pass1::{pass1, Pass1Result};
pub use pass2::{elaborate, elaborate_with_prims, PrimCtx};
