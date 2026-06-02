#![forbid(unsafe_code)]

pub mod error;
pub mod parser;
mod prelude;
pub mod prim;
pub mod runtime;
pub mod scope;
pub mod suite;

pub use parser::nix_to_expr;
pub use suite::{discover_computed, is_literal_attrset, parse_test_suite, TestCase, ValueCase};
