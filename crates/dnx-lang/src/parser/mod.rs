mod binding;
mod collections;
mod helpers;
mod lambda;
mod literals;

use dnx_ast::Ast;
use rnix::ast;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Arc;

use crate::error::NixError;
use crate::prim::{NixPrimFun, NixPrimVal};
use crate::scope::{Name, Scope};

pub(crate) type E = Ast<NixPrimVal, NixPrimFun>;

static FRESH_CTR: AtomicU32 = AtomicU32::new(0);

pub(super) fn fresh(prefix: &str) -> Name {
    let n = FRESH_CTR.fetch_add(1, Ordering::Relaxed);
    Arc::from(format!("_nix_{prefix}{n}").as_str())
}

pub(super) fn true_val() -> E {
    Ast::Val(NixPrimVal::Bool(true))
}

pub(super) fn false_val() -> E {
    Ast::Val(NixPrimVal::Bool(false))
}

pub fn nix_to_expr(src: &str) -> Result<E, NixError> {
    let mut scope = Scope::new();
    parse_with(src, &mut scope)
}

/// The dotted name of an attrset entry's key (`a.b.c`), for suite discovery.
pub(crate) fn attrpath_value_name(apv: &ast::AttrpathValue) -> Result<String, NixError> {
    helpers::attrpath_simple_name(apv).map(|n| n.to_string())
}

/// Parse `src` whose relative `import`s resolve against `base_dir`.
pub fn nix_to_expr_at(src: &str, base_dir: std::path::PathBuf) -> Result<E, NixError> {
    let mut scope = Scope::with_base(base_dir);
    parse_with(src, &mut scope)
}

pub(super) fn parse_with(src: &str, scope: &mut Scope) -> Result<E, NixError> {
    let parse = rnix::Root::parse(src);
    if !parse.errors().is_empty() {
        let errs: Vec<String> = parse.errors().iter().map(|e| e.to_string()).collect();
        return Err(NixError::ParseError(errs.join("; ")));
    }
    let root = parse.tree();
    let expr = root
        .expr()
        .ok_or_else(|| NixError::ParseError("empty program".into()))?;
    translate_expr(expr, scope)
}

/// Reference a prelude def by name. pass0 inlines it where used, so no
/// scope use-count is needed (each reference becomes an independent copy).
pub(super) fn prelude_ref(name: &str) -> E {
    Ast::Name(Arc::from(name))
}

pub(super) fn translate_expr(expr: ast::Expr, scope: &mut Scope) -> Result<E, NixError> {
    match expr {
        ast::Expr::Ident(ident) => lambda::translate_ident(ident, scope),
        ast::Expr::Lambda(lambda) => lambda::translate_lambda(lambda, scope),
        ast::Expr::Apply(apply) => lambda::translate_apply(apply, scope),
        ast::Expr::LetIn(let_in) => binding::translate_let_in(let_in, scope),
        ast::Expr::IfElse(if_else) => binding::translate_if_else(if_else, scope),
        ast::Expr::Assert(assert_) => binding::translate_assert(assert_, scope),
        ast::Expr::With(with) => binding::translate_with(with, scope),
        ast::Expr::Literal(lit) => literals::translate_literal(lit),
        ast::Expr::Str(s) => literals::translate_str(s, scope),
        ast::Expr::Path(p) => literals::translate_path(p, scope),
        ast::Expr::BinOp(binop) => literals::translate_binop(binop, scope),
        ast::Expr::UnaryOp(unary) => literals::translate_unary(unary, scope),
        ast::Expr::List(list) => collections::translate_list(list, scope),
        ast::Expr::AttrSet(attrset) => collections::translate_attrset(attrset, scope),
        ast::Expr::Select(select) => collections::translate_select(select, scope),
        ast::Expr::HasAttr(has_attr) => collections::translate_has_attr(has_attr, scope),
        ast::Expr::Paren(paren) => {
            let inner = paren
                .expr()
                .ok_or_else(|| NixError::UnsupportedSyntax("empty paren".into()))?;
            translate_expr(inner, scope)
        }
        ast::Expr::Root(root) => {
            let inner = root
                .expr()
                .ok_or_else(|| NixError::UnsupportedSyntax("empty root".into()))?;
            translate_expr(inner, scope)
        }
        _ => Err(NixError::UnsupportedSyntax(
            "unknown expression type".into(),
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dnx_ast::Ast;

    #[test]
    fn parse_integer() {
        let e = nix_to_expr("42").unwrap();
        assert_eq!(e, Ast::Val(NixPrimVal::Int(42)));
    }

    #[test]
    fn parse_string() {
        let e = nix_to_expr("\"hello\"").unwrap();
        assert_eq!(e, Ast::Val(NixPrimVal::Str(Arc::from("hello"))));
    }

    #[test]
    fn parse_null() {
        let e = nix_to_expr("null").unwrap();
        assert_eq!(e, Ast::Val(NixPrimVal::Null));
    }

    #[test]
    fn parse_identity_lambda() {
        let e = nix_to_expr("x: x").unwrap();
        assert!(matches!(e, Ast::Abs(_, _)));
    }

    #[test]
    fn parse_application() {
        let e = nix_to_expr("(x: x) 1").unwrap();
        assert!(matches!(e, Ast::App(_, _)));
    }

    #[test]
    fn parse_let_in() {
        let e = nix_to_expr("let x = 1; in x").unwrap();
        assert!(matches!(e, Ast::App(_, _)));
    }

    #[test]
    fn parse_binop_add() {
        let e = nix_to_expr("1 + 2").unwrap();
        assert!(matches!(e, Ast::App(_, _)));
    }

    #[test]
    fn parse_if_else() {
        let e = nix_to_expr("if true then 1 else 2").unwrap();
        assert!(matches!(e, Ast::App(_, _)));
    }

    #[test]
    fn parse_list_empty() {
        // `[]` now lowers to the prelude `nil` def-reference (Scott-encoded),
        // inlined by pass0; no longer a NixPrimVal::Nil literal.
        let e = nix_to_expr("[]").unwrap();
        assert!(matches!(e, Ast::Name(n) if n.as_ref() == "nil"));
    }

    #[test]
    fn parse_float() {
        let e = nix_to_expr("3.14").unwrap();
        assert!(matches!(e, Ast::Val(NixPrimVal::Float(_))));
    }
}
