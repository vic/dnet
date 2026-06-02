//! Nix prim vocabulary. The value/fun enums, their checked-arith eval table,
//! and the engine bridges now live in the neutral `dnx-prim` crate, so non-nix
//! front-ends can reuse them without dragging in the rnix parser. They are
//! re-exported here for backward compat (`crate::prim::…` / `dnx_lang::prim::…`).
//!
//! Only `binop_prim_fun` stays: it is rnix-typed glue (parser desugar), not
//! part of the neutral vocabulary.

pub use dnx_prim::prim::*;

/// Map rnix BinOpKind to NixPrimFun variant.
pub fn binop_prim_fun(op: &rnix::ast::BinOpKind) -> Option<NixPrimFun> {
    use rnix::ast::BinOpKind;
    match op {
        BinOpKind::Add => Some(NixPrimFun::Add),
        BinOpKind::Sub => Some(NixPrimFun::Sub),
        BinOpKind::Mul => Some(NixPrimFun::Mul),
        BinOpKind::Div => Some(NixPrimFun::Div),
        BinOpKind::Equal => Some(NixPrimFun::Eq),
        BinOpKind::NotEqual => Some(NixPrimFun::Ne),
        BinOpKind::Less => Some(NixPrimFun::Lt),
        BinOpKind::LessOrEq => Some(NixPrimFun::Le),
        BinOpKind::More => Some(NixPrimFun::Gt),
        BinOpKind::MoreOrEq => Some(NixPrimFun::Ge),
        BinOpKind::Update => Some(NixPrimFun::Update),
        // Concat (++) handled in translate_binop, &&, ||, -> are Church-bool native
        _ => None,
    }
}
