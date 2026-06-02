#![forbid(unsafe_code)]

//! `dnx-flake`: the flake front-end. Parse a `flake.nix`, enumerate its
//! output attribute names (`dnx flake show`), evaluate an output path to WHNF,
//! and round-trip our minimal `flake.lock` (local-path inputs pinned by BLAKE3).
//!
//! Out of scope (a later `dnx-drv` consolidation pass turns a resolved WHNF
//! into a `Derivation` and realizes it): the `.#attr -> Derivation -> realize`
//! half. The seam is [`Flake::resolve_attr`], which returns the WHNF of an
//! output path for a future drv layer to consume.

mod error;
mod flake;
mod lock;
mod report;

pub use error::FlakeError;
pub use flake::{Flake, FlakeInput, FlakeInputs, FlakeOutputs, LockStatus};
pub use lock::{LockEntry, LockFile};
pub use report::{FlakeReport, OutputKind};
