#![forbid(unsafe_code)]

//! Userland content-addressed store for Dnx. BLAKE3-keyed, no root, never
//! touches `/nix`. See `vic/plans/dnx-demo-arch.md` §2.

mod error;
mod path;
mod store;

pub use error::StoreError;
pub use path::StorePath;
pub use store::{PathInfo, Store};
