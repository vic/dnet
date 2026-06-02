#![forbid(unsafe_code)]
//! `dnx-ts` — a tree-sitter front-end spike. It reuses an *existing*
//! tree-sitter grammar (`tree-sitter-json`) as surface syntax and lowers the
//! CST to the shared core IR `dnx_ast::Ast<NixPrimVal, NixPrimFun>` — the exact
//! waist `dnx-lang` and `dnx-pyparse` target — then evaluates on the same
//! engine (parse → pass0 → pass1 → elaborate → reduce → readback). JSON values
//! therefore become dnx values: a JSON object is a nix attrset, a JSON array a
//! nix list, and they read back through the same `NixEvalResult`.
//!
//! ## Why a feature flag
//! tree-sitter is a C library: its grammars compile via `cc` at build time. dnx
//! ships as a single *static musl* binary, so the C dependency is gated behind
//! the off-by-default `tree-sitter` feature. With the feature off this crate is
//! empty and the default (musl) build pulls no C. See `Cargo.toml`.
//!
//! ## Scope (this spike)
//! Two surfaces share the eval tail. (1) JSON — a total, side-effect-free map
//! validating the plumbing "foreign CST → Ast → eval". (2) A hand-written micro
//! lambda-calculus (`surface`) — the *binder* path JSON sidesteps: `\x. body`,
//! application, `+`, parens; a bound variable is `Rep`-split or `Era`-dropped so
//! the lowered term is linearity-legal, exactly as the nix front-end does. Both
//! lower to `Ast<NixPrimVal, NixPrimFun>` and reduce on the one shared engine.

#[cfg(feature = "tree-sitter")]
mod error;
#[cfg(feature = "tree-sitter")]
mod lower;
#[cfg(feature = "tree-sitter")]
pub mod runtime;
#[cfg(feature = "tree-sitter")]
mod surface;

#[cfg(feature = "tree-sitter")]
pub use error::TsError;
#[cfg(feature = "tree-sitter")]
pub use runtime::{TsEvalResult, TsRuntime};
#[cfg(feature = "tree-sitter")]
pub use surface::lower_lambda_surface;
