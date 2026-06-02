use dnx_ast::Ast;
use rnix::ast::{self, HasEntry};

use crate::error::NixError;
use crate::prim::{NixPrimFun, NixPrimVal};
use crate::scope::Name;

use super::helpers::{attrpath_simple_name, count_uses_in, desugar_inherit, wrap_uses};
use super::{fresh, translate_expr, E};

/// A let binding's value before lowering: source AST (normal binding) or a
/// pre-built IR value (an `inherit`, already resolved in the enclosing scope).
enum BindVal {
    Ast(ast::Expr),
    Ir(E),
}

pub(super) fn translate_let_in(
    let_in: ast::LetIn,
    scope: &mut crate::scope::Scope,
) -> Result<E, NixError> {
    let body_expr = let_in
        .body()
        .ok_or_else(|| NixError::UnsupportedSyntax("let missing body".into()))?;
    // A let value is either source AST (a normal binding, translated *after*
    // all names are bound so it can see its siblings) or an already-built IR
    // value (an `inherit`, resolved in the enclosing scope — cppNix
    // `Kind::Inherited` — so it must be translated *before* the binds).
    let mut bindings: Vec<(Name, BindVal)> = vec![];
    for entry in let_in.entries() {
        match entry {
            ast::Entry::AttrpathValue(apv) => {
                let name = attrpath_simple_name(&apv)?;
                let val = apv.value().ok_or_else(|| {
                    NixError::UnsupportedSyntax("let binding missing value".into())
                })?;
                bindings.push((name, BindVal::Ast(val)));
            }
            ast::Entry::Inherit(inherit) => {
                for (name, val) in desugar_inherit(inherit, scope)? {
                    bindings.push((name, BindVal::Ir(val)));
                }
            }
        }
    }
    if bindings.is_empty() {
        return translate_expr(body_expr, scope);
    }
    let names: Vec<Name> = bindings.iter().map(|(n, _)| n.clone()).collect();
    for n in &names {
        scope.bind(n.clone());
    }
    let mut val_exprs: Vec<E> = vec![];
    for (_, val) in bindings {
        val_exprs.push(match val {
            BindVal::Ast(e) => translate_expr(e, scope)?,
            BindVal::Ir(e) => e,
        });
    }
    let mut body = translate_expr(body_expr, scope)?;
    let use_counts: Vec<u32> = names.iter().map(|n| scope.use_count(n)).collect();
    for n in &names {
        scope.unbind(n);
    }
    for ((name, val), uses) in names.iter().zip(val_exprs).zip(use_counts.iter()).rev() {
        let wrapped_body = wrap_uses(name.clone(), *uses, body);
        body = Ast::App(
            Box::new(Ast::Abs(name.clone(), Box::new(wrapped_body))),
            Box::new(val),
        );
    }
    Ok(body)
}

pub(super) fn translate_if_else(
    if_else: ast::IfElse,
    scope: &mut crate::scope::Scope,
) -> Result<E, NixError> {
    let cond = translate_expr(
        if_else
            .condition()
            .ok_or_else(|| NixError::UnsupportedSyntax("if missing cond".into()))?,
        scope,
    )?;
    let then = translate_expr(
        if_else
            .body()
            .ok_or_else(|| NixError::UnsupportedSyntax("if missing then".into()))?,
        scope,
    )?;
    let else_ = translate_expr(
        if_else
            .else_body()
            .ok_or_else(|| NixError::UnsupportedSyntax("if missing else".into()))?,
        scope,
    )?;
    Ok(Ast::App(
        Box::new(Ast::App(Box::new(cond), Box::new(then))),
        Box::new(else_),
    ))
}

pub(super) fn translate_assert(
    assert_: ast::Assert,
    scope: &mut crate::scope::Scope,
) -> Result<E, NixError> {
    let cond = translate_expr(
        assert_
            .condition()
            .ok_or_else(|| NixError::UnsupportedSyntax("assert missing cond".into()))?,
        scope,
    )?;
    let body = translate_expr(
        assert_
            .body()
            .ok_or_else(|| NixError::UnsupportedSyntax("assert missing body".into()))?,
        scope,
    )?;
    let throw = Ast::App(
        Box::new(Ast::Fun(NixPrimFun::Throw)),
        Box::new(Ast::Val(NixPrimVal::Str(std::sync::Arc::from(
            "assertion failed",
        )))),
    );
    Ok(Ast::App(
        Box::new(Ast::App(Box::new(cond), Box::new(body))),
        Box::new(throw),
    ))
}

/// `with e; body`: free names in `body` that are neither lexically bound, a
/// prelude name, nor a registered builtin fall back to attrs of `e` (`x` →
/// `select e "x"`). Strategy A of with-rec-design.md §3a: translate `body`
/// normally (such names land as `Fun(Builtin(name))`, lambda.rs:36), then
/// rewrite each into a per-field `let` binder `select w "name"`. The per-field
/// hoist (one bound scalar per field) dodges the two-selects-under-one-prim bug
/// (§3c; firsthand `(s: s.a + s.b) {…}` errors but the hoisted `let` form gives
/// 12). Lexical names beat `with` for free — a bound `x` is already `Name(x)`,
/// never a `Builtin`, so the rewrite never sees it.
///
/// Limitation (§3d): a name absent from `e` is still rewritten to `select w …`
/// and so errors `attribute … missing` instead of falling through to an outer
/// `with`/builtin. Acceptable for the common single-`with` case; the faithful
/// `selectOr` fallback chain (strategy B) is the upgrade.
pub(super) fn translate_with(
    with_: ast::With,
    scope: &mut crate::scope::Scope,
) -> Result<E, NixError> {
    let env = translate_expr(
        with_
            .namespace()
            .ok_or_else(|| NixError::UnsupportedSyntax("with missing namespace".into()))?,
        scope,
    )?;
    let body = translate_expr(
        with_
            .body()
            .ok_or_else(|| NixError::UnsupportedSyntax("with missing body".into()))?,
        scope,
    )?;
    let w = fresh("with");
    let (body, fields) = rewrite_with_fields(body);
    // Wrap each resolved field in its own `let` binder `__with_f = select w "f"`,
    // folded right-to-left exactly like `translate_let_in`. `w` is used once per
    // field, so `wrap_uses` splits it via the rep chain.
    let mut lets = body;
    for f in fields.iter().rev() {
        let binder = with_field_binder(f);
        let uses = count_uses_in(&lets, &binder);
        let wrapped = wrap_uses(binder.clone(), uses, lets);
        let select = Ast::App(
            Box::new(Ast::App(
                Box::new(Ast::Fun(NixPrimFun::Select)),
                Box::new(Ast::Name(w.clone())),
            )),
            Box::new(Ast::Val(NixPrimVal::Str(f.clone()))),
        );
        lets = Ast::App(
            Box::new(Ast::Abs(binder, Box::new(wrapped))),
            Box::new(select),
        );
    }
    let w_uses = fields.len() as u32;
    let lets = wrap_uses(w.clone(), w_uses, lets);
    Ok(Ast::App(
        Box::new(Ast::Abs(w, Box::new(lets))),
        Box::new(env),
    ))
}

/// The let-binder name a `with`-resolved field `f` is hoisted to.
fn with_field_binder(f: &Name) -> Name {
    std::sync::Arc::from(format!("_nix_with_{f}").as_str())
}

/// Rewrite every `Fun(Builtin(name))` whose `name` is not a registered prim into
/// `Name(_nix_with_name)`, collecting the distinct field names (first-seen order).
/// Registered builtins (`nixprimfun_name` returns `Some`) are left untouched so a
/// `with` env never shadows a real builtin (`toString`, etc.).
fn rewrite_with_fields(body: E) -> (E, Vec<Name>) {
    let mut fields: Vec<Name> = vec![];
    let out = rewrite_node(body, &mut fields);
    (out, fields)
}

fn rewrite_node(node: E, fields: &mut Vec<Name>) -> E {
    match node {
        Ast::Fun(NixPrimFun::Builtin(name))
            if crate::prim::nixprimfun_name(&NixPrimFun::Builtin(name.clone())).is_none() =>
        {
            if !fields.contains(&name) {
                fields.push(name.clone());
            }
            Ast::Name(with_field_binder(&name))
        }
        Ast::Abs(x, body) => Ast::Abs(x, Box::new(rewrite_node(*body, fields))),
        Ast::App(f, x) => Ast::App(
            Box::new(rewrite_node(*f, fields)),
            Box::new(rewrite_node(*x, fields)),
        ),
        Ast::Rep(e, a, b, body) => Ast::Rep(
            Box::new(rewrite_node(*e, fields)),
            a,
            b,
            Box::new(rewrite_node(*body, fields)),
        ),
        Ast::Era(e, body) => Ast::Era(
            Box::new(rewrite_node(*e, fields)),
            Box::new(rewrite_node(*body, fields)),
        ),
        Ast::Fix(e) => Ast::Fix(Box::new(rewrite_node(*e, fields))),
        other => other,
    }
}

#[cfg(test)]
mod tests {
    use crate::runtime::{NixEvalResult, NixRuntime};

    fn int(src: &str) -> i64 {
        match NixRuntime::pure().eval(src) {
            NixEvalResult::Int(n) => n,
            other => panic!("{src} => non-int {other:?}", other = ResultTag(&other)),
        }
    }

    fn string(src: &str) -> String {
        match NixRuntime::pure().eval(src) {
            NixEvalResult::Str(s) => s.to_string(),
            other => panic!("{src} => non-str {other:?}", other = ResultTag(&other)),
        }
    }

    struct ResultTag<'a>(&'a NixEvalResult);
    impl std::fmt::Debug for ResultTag<'_> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self.0 {
                NixEvalResult::Int(n) => write!(f, "Int({n})"),
                NixEvalResult::Str(s) => write!(f, "Str({s})"),
                NixEvalResult::Bool(b) => write!(f, "Bool({b})"),
                NixEvalResult::Lambda(_) => write!(f, "Lambda"),
                NixEvalResult::Error(e) => write!(f, "Error({e})"),
                _ => write!(f, "other"),
            }
        }
    }

    #[test]
    fn with_single_field() {
        assert_eq!(int("with { a = 5; }; a"), 5);
    }

    #[test]
    fn with_two_fields_under_strict_prim() {
        // §3c: two with-resolved fields feeding `+` must hoist to per-field
        // binders to dodge the two-selects-under-one-prim bug.
        assert_eq!(int("with { a = 5; b = 7; }; a + b"), 12);
    }

    #[test]
    fn lexical_binding_shadows_with() {
        // A lexically-bound name beats a `with` field of the same name.
        assert_eq!(int("let x = 1; in with { x = 99; }; x"), 1);
    }

    #[test]
    fn with_does_not_clobber_real_builtin() {
        // `toString` is a registered builtin: it must NOT be rewritten to
        // `select w "toString"`, even when a `with` env is in scope.
        assert_eq!(string("with { a = 5; }; toString a"), "5");
    }
}
