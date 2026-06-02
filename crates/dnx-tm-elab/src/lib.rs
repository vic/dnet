//! UNTRUSTED fix→Elim translator (spec `vic/plans/fix-to-elim-spec.md`). Turns Coq-style
//! primitive `Fixpoint` (structural `fix` + `match` + guard) into kernel `Tm::Elim` so the
//! dnx-proof kernel can RE-CHECK it (infer + ι). A bug here = a type-error caught by the
//! kernel, NOT a soundness hole (proofs.md:165 "recursor TCB; elaborator cannot forge").
//!
//! v1 scope (spec §7-§8): no-param NON-INDEXED inductives only (kernel `recursor_type`
//! `recursor.rs:26` bails on params/indices). Single structural split, uniform non-decreasing
//! args, motive carried from the surface. Out: mutual / nested / well-founded / varying-arg.

#![forbid(unsafe_code)]

pub mod lower;
pub mod surface;

pub use lower::{lower, LowerError};
pub use surface::{Fix, Match, SrcArm, SrcTm};
