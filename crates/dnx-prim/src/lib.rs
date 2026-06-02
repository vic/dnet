#![forbid(unsafe_code)]

//! Neutral prim vocabulary: the concrete `(NixPrimVal, NixPrimFun)` universe
//! and its checked-arithmetic eval table, plus the bridges that bind those
//! enums to the engine's `dnx_core::prim` runtime. No parser, no rnix — so
//! any surface front-end can instantiate `Ast<NixPrimVal, NixPrimFun>` without
//! depending on a nix parser.

pub mod prim;
