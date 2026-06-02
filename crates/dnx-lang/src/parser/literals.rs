use dnx_ast::Ast;
use rnix::ast;
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;

use crate::error::NixError;
use crate::prim::{binop_prim_fun, NixPrimFun, NixPrimVal};

use super::{false_val, translate_expr, true_val, E};

pub(super) fn translate_literal(lit: ast::Literal) -> Result<E, NixError> {
    use rnix::ast::LiteralKind;
    match lit.kind() {
        LiteralKind::Integer(n) => Ok(Ast::Val(NixPrimVal::Int(
            n.value().map_err(|e| NixError::ParseError(e.to_string()))?,
        ))),
        LiteralKind::Float(n) => Ok(Ast::Val(NixPrimVal::Float(
            n.value().map_err(|e| NixError::ParseError(e.to_string()))?,
        ))),
        LiteralKind::Uri(u) => Ok(Ast::Val(NixPrimVal::Str(Arc::from(u.to_string().as_str())))),
    }
}

pub(super) fn translate_str(s: ast::Str, scope: &mut crate::scope::Scope) -> Result<E, NixError> {
    // Desugar `"pre${e}post"` to `Add(Add("pre", toString e), "post")`: literal
    // parts become Str values, holes are `toString`-coerced, all folded with the
    // wired `+`/`to_string` prims. `''…''` shares this site (rnix yields ast::Str).
    let lit = |l: &str| Ast::Val(NixPrimVal::Str(Arc::from(l)));
    let add = |acc: E, next: E| {
        Ast::App(
            Box::new(Ast::App(Box::new(Ast::Fun(NixPrimFun::Add)), Box::new(acc))),
            Box::new(next),
        )
    };
    let mut acc: Option<E> = None;
    for part in s.normalized_parts() {
        let e = match part {
            ast::InterpolPart::Literal(l) => lit(&l),
            ast::InterpolPart::Interpolation(i) => {
                let inner = i
                    .expr()
                    .ok_or_else(|| NixError::UnsupportedSyntax("empty interpolation".into()))?;
                Ast::App(
                    Box::new(Ast::Fun(NixPrimFun::ToString2)),
                    Box::new(translate_expr(inner, scope)?),
                )
            }
        };
        acc = Some(match acc {
            Some(prev) => add(prev, e),
            None => e,
        });
    }
    Ok(acc.unwrap_or_else(|| lit("")))
}

/// Lower a path literal to an absolute `Path` value. Nix resolves a relative
/// path literal at parse time against the enclosing file's directory, falling
/// back to the process CWD when there is no file context (`dnx eval`). This is
/// the same base used by `import` (`lambda.rs:206-211`); we extend it with the
/// CWD fallback so a bare `./foo` is absolutised exactly as cppNix does. `/abs`
/// literals pass through unchanged.
pub(super) fn translate_path(p: ast::Path, scope: &crate::scope::Scope) -> Result<E, NixError> {
    let raw = PathBuf::from(p.to_string());
    let abs = if raw.is_relative() {
        let base = match &scope.base_dir {
            Some(b) => b.clone(),
            None => std::env::current_dir()
                .map_err(|e| NixError::ParseError(format!("path literal cwd: {e}")))?,
        };
        lexical_abs(&base.join(raw))
    } else {
        lexical_abs(&raw)
    };
    Ok(Ast::Val(NixPrimVal::Path(Arc::from(
        abs.to_string_lossy().as_ref(),
    ))))
}

/// Collapse `.`/`..` components lexically (no filesystem access — path literals
/// need not exist, so `canonicalize` is unusable). Matches Nix's parse-time
/// normalisation: `/a/./b` → `/a/b`, `/a/c/../b` → `/a/b`.
fn lexical_abs(p: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for c in p.components() {
        match c {
            Component::CurDir => {}
            Component::ParentDir => {
                out.pop();
            }
            other => out.push(other),
        }
    }
    out
}

pub(super) fn translate_binop(
    binop: ast::BinOp,
    scope: &mut crate::scope::Scope,
) -> Result<E, NixError> {
    use rnix::ast::BinOpKind;
    let op = binop
        .operator()
        .ok_or_else(|| NixError::UnsupportedSyntax("binop missing operator".into()))?;
    let lhs_expr = binop
        .lhs()
        .ok_or_else(|| NixError::UnsupportedSyntax("binop missing lhs".into()))?;
    let rhs_expr = binop
        .rhs()
        .ok_or_else(|| NixError::UnsupportedSyntax("binop missing rhs".into()))?;
    match op {
        BinOpKind::And => {
            let a = translate_expr(lhs_expr, scope)?;
            let b = translate_expr(rhs_expr, scope)?;
            let f = false_val();
            return Ok(Ast::App(
                Box::new(Ast::App(Box::new(a), Box::new(b))),
                Box::new(f),
            ));
        }
        BinOpKind::Or => {
            let a = translate_expr(lhs_expr, scope)?;
            let b = translate_expr(rhs_expr, scope)?;
            let t = true_val();
            return Ok(Ast::App(
                Box::new(Ast::App(Box::new(a), Box::new(t))),
                Box::new(b),
            ));
        }
        BinOpKind::Implication => {
            let a = translate_expr(lhs_expr, scope)?;
            let b = translate_expr(rhs_expr, scope)?;
            let t = true_val();
            return Ok(Ast::App(
                Box::new(Ast::App(Box::new(a), Box::new(b))),
                Box::new(t),
            ));
        }
        BinOpKind::Concat => {
            let lhs = translate_expr(lhs_expr, scope)?;
            let rhs = translate_expr(rhs_expr, scope)?;
            let concat = super::prelude_ref("concat");
            return Ok(Ast::App(
                Box::new(Ast::App(Box::new(concat), Box::new(lhs))),
                Box::new(rhs),
            ));
        }
        _ => {}
    }
    if let Some(prim_fun) = binop_prim_fun(&op) {
        let lhs = translate_expr(lhs_expr, scope)?;
        let rhs = translate_expr(rhs_expr, scope)?;
        let prim = Ast::Fun(prim_fun);
        Ok(Ast::App(
            Box::new(Ast::App(Box::new(prim), Box::new(lhs))),
            Box::new(rhs),
        ))
    } else {
        Err(NixError::UnsupportedSyntax(format!("binop: {op:?}")))
    }
}

pub(super) fn translate_unary(
    unary: ast::UnaryOp,
    scope: &mut crate::scope::Scope,
) -> Result<E, NixError> {
    use rnix::ast::UnaryOpKind;
    let op = unary
        .operator()
        .ok_or_else(|| NixError::UnsupportedSyntax("unary missing op".into()))?;
    let operand = translate_expr(
        unary
            .expr()
            .ok_or_else(|| NixError::UnsupportedSyntax("unary missing expr".into()))?,
        scope,
    )?;
    match op {
        UnaryOpKind::Invert => {
            let t = true_val();
            let f = false_val();
            Ok(Ast::App(
                Box::new(Ast::App(Box::new(operand), Box::new(f))),
                Box::new(t),
            ))
        }
        UnaryOpKind::Negate => Ok(Ast::App(
            Box::new(Ast::Fun(NixPrimFun::Neg)),
            Box::new(operand),
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scope::Scope;

    fn path_ast(src: &str) -> ast::Path {
        match rnix::Root::parse(src).tree().expr() {
            Some(ast::Expr::Path(p)) => p,
            other => panic!("expected bare path literal, got {other:?}"),
        }
    }

    fn lower(src: &str, scope: &Scope) -> String {
        match translate_path(path_ast(src), scope).expect("lower ok") {
            Ast::Val(NixPrimVal::Path(p)) => p.to_string(),
            other => panic!("expected Path, got {other:?}"),
        }
    }

    #[test]
    fn relative_literal_absolutised_against_cwd() {
        let cwd = std::env::current_dir().expect("cwd");
        let got = lower("./foo", &Scope::new());
        assert_eq!(got, cwd.join("foo").to_string_lossy());
        assert!(std::path::Path::new(&got).is_absolute());
    }

    #[test]
    fn absolute_literal_passes_through() {
        assert_eq!(lower("/abs/foo", &Scope::new()), "/abs/foo");
    }

    #[test]
    fn parent_and_curdir_collapsed() {
        let base = PathBuf::from("/a/b");
        let scope = Scope::with_base(base);
        assert_eq!(lower("./c/../d", &scope), "/a/b/d");
        assert_eq!(lower("../e", &scope), "/a/e");
    }

    #[test]
    fn base_dir_takes_precedence_over_cwd() {
        let scope = Scope::with_base(PathBuf::from("/proj/src"));
        assert_eq!(lower("./mod.nix", &scope), "/proj/src/mod.nix");
    }

    fn str_ast(src: &str) -> ast::Str {
        match rnix::Root::parse(src).tree().expr() {
            Some(ast::Expr::Str(s)) => s,
            other => panic!("expected string literal, got {other:?}"),
        }
    }

    /// Lower an interpolation-free string literal to its folded `Str` value.
    /// Pure-literal strings fold to a single `Ast::Val(Str(_))` (no `Add`
    /// spine), so the parse-time string content is directly assertable.
    fn lower_str(src: &str) -> String {
        let mut scope = Scope::new();
        match translate_str(str_ast(src), &mut scope).expect("lower ok") {
            Ast::Val(NixPrimVal::Str(s)) => s.to_string(),
            other => panic!("expected literal Str, got {other:?}"),
        }
    }

    #[test]
    fn double_quoted_escapes() {
        // `\n \t \\ \" \$` and `\d` (unknown → literal `d`); matches cppNix.
        assert_eq!(lower_str(r#""a\nb\tc\\d\"e""#), "a\nb\tc\\d\"e");
        assert_eq!(lower_str(r#""x\${y}z""#), "x${y}z");
        assert_eq!(lower_str(r#""end\$""#), "end$");
        assert_eq!(lower_str(r#""a\db""#), "adb");
    }

    #[test]
    fn indented_string_strips_common_indent() {
        // Common leading indent removed; deeper indent kept relative. The
        // opening-line newline is dropped, the final newline retained.
        assert_eq!(lower_str("''\n  foo\n    bar\n''"), "foo\n  bar\n");
        assert_eq!(
            lower_str("''\n    indented\n  less\n''"),
            "  indented\nless\n"
        );
    }

    #[test]
    fn indented_string_escapes() {
        // `''${` and `'''` are the indented-string escapes; `''\n`/`''\t`/`''\$`
        // are the backslash escapes that survive into the value.
        assert_eq!(lower_str("''''${x}''"), "${x}");
        assert_eq!(lower_str("''a'''b''"), "a''b");
        assert_eq!(lower_str("''a''\\nb''"), "a\nb");
        assert_eq!(lower_str("''a''\\tb''"), "a\tb");
        assert_eq!(lower_str("''a''\\$b''"), "a$b");
    }
}
