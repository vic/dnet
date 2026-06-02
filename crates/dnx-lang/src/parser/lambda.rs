use dnx_ast::Ast;
use rnix::ast::{self, Param};
use std::sync::Arc;

use crate::error::NixError;
use crate::prim::{NixPrimFun, NixPrimVal};
use crate::scope::Name;

use super::helpers::{count_uses_in, wrap_uses};
use super::{fresh, translate_expr, E};

pub(super) fn translate_ident(
    ident: ast::Ident,
    scope: &mut crate::scope::Scope,
) -> Result<E, NixError> {
    let name: Name = Arc::from(
        ident
            .ident_token()
            .map(|t| t.text().to_string())
            .unwrap_or_default()
            .as_str(),
    );
    match name.as_ref() {
        "true" => return Ok(super::true_val()),
        "false" => return Ok(super::false_val()),
        "null" => return Ok(Ast::Val(NixPrimVal::Null)),
        _ => {}
    }
    if scope.is_bound(name.as_ref()) {
        scope.use_var(&name);
        Ok(Ast::Name(name))
    } else if crate::prelude::is_prelude_name(name.as_ref()) {
        // Resolved by pass0 (inlined from the prelude def map).
        Ok(Ast::Name(name))
    } else {
        Ok(Ast::Fun(NixPrimFun::Builtin(name)))
    }
}

pub(super) fn translate_lambda(
    lambda: ast::Lambda,
    scope: &mut crate::scope::Scope,
) -> Result<E, NixError> {
    let param = lambda
        .param()
        .ok_or_else(|| NixError::UnsupportedSyntax("lambda missing param".into()))?;
    let body_expr = lambda
        .body()
        .ok_or_else(|| NixError::UnsupportedSyntax("lambda missing body".into()))?;
    match param {
        Param::IdentParam(ident_param) => {
            let x: Name = Arc::from(
                ident_param
                    .ident()
                    .and_then(|i| i.ident_token())
                    .map(|t| t.text().to_string())
                    .unwrap_or_else(|| "_".to_string())
                    .as_str(),
            );
            scope.bind(x.clone());
            let body = translate_expr(body_expr, scope)?;
            let uses = scope.use_count(&x);
            scope.unbind(&x);
            let body_wrapped = wrap_uses(x.clone(), uses, body);
            Ok(Ast::Abs(x, Box::new(body_wrapped)))
        }
        Param::Pattern(pattern) => translate_lambda_pattern(pattern, body_expr, scope),
    }
}

fn translate_lambda_pattern(
    pat: ast::Pattern,
    body_expr: ast::Expr,
    scope: &mut crate::scope::Scope,
) -> Result<E, NixError> {
    let arg_name: Name = if let Some(bind) = pat.pat_bind() {
        bind.ident()
            .and_then(|i| i.ident_token())
            .map(|t| Arc::from(t.text()))
            .unwrap_or_else(|| fresh("arg"))
    } else {
        fresh("arg")
    };
    let fields: Vec<(Name, Option<ast::Expr>)> = pat
        .pat_entries()
        .map(|e| {
            let name = e
                .ident()
                .and_then(|i| i.ident_token())
                .map(|t| Arc::from(t.text()))
                .unwrap_or_else(|| fresh("f"));
            (name, e.default())
        })
        .collect();
    scope.bind(arg_name.clone());
    // Bind every field before translating the body so a field reference resolves
    // to its `Name` (and is use-counted), not to a `Builtin` fall-through.
    for (f, _) in &fields {
        scope.bind(f.clone());
    }
    let mut body = translate_expr(body_expr, scope)?;
    for (field, default) in fields.iter().rev() {
        let arg = Box::new(Ast::Name(arg_name.clone()));
        let key = Box::new(Ast::Val(NixPrimVal::Str(field.clone())));
        // `a ? d` → SelectOr(arg, "a", d); bare `a` → Select(arg, "a") (Nix-strict
        // on a missing field). The default is translated with the fields in scope,
        // matching cppNix (a default may reference the other formals).
        let select_expr: E = match default {
            Some(d) => {
                let dflt = translate_expr(d.clone(), scope)?;
                Ast::App(
                    Box::new(Ast::App(
                        Box::new(Ast::App(Box::new(Ast::Fun(NixPrimFun::SelectOr)), arg)),
                        key,
                    )),
                    Box::new(dflt),
                )
            }
            None => Ast::App(
                Box::new(Ast::App(Box::new(Ast::Fun(NixPrimFun::Select)), arg)),
                key,
            ),
        };
        let field_uses = scope.use_count(field);
        scope.unbind(field);
        let inner_body = wrap_uses(field.clone(), field_uses, body);
        body = Ast::App(
            Box::new(Ast::Abs(field.clone(), Box::new(inner_body))),
            Box::new(select_expr),
        );
    }
    // `arg_name` is now used once per field-select (plus any `@`-ref). Rep-split it
    // by its real total so N uses of the single pattern arg are linearity-legal.
    let arg_uses = count_uses_in(&body, &arg_name);
    scope.unbind(&arg_name);
    body = wrap_uses(arg_name.clone(), arg_uses, body);
    Ok(Ast::Abs(arg_name, Box::new(body)))
}

pub(super) fn translate_apply(
    apply: ast::Apply,
    scope: &mut crate::scope::Scope,
) -> Result<E, NixError> {
    let func = apply
        .lambda()
        .ok_or_else(|| NixError::UnsupportedSyntax("apply missing func".into()))?;
    let arg = apply
        .argument()
        .ok_or_else(|| NixError::UnsupportedSyntax("apply missing arg".into()))?;
    // `fix g` → Ast::Fix(g): the designed Y-net recursion (pass0 desugars it).
    if let ast::Expr::Ident(id) = &func {
        let txt = id.ident_token().map(|t| t.text().to_string());
        if txt.as_deref() == Some("fix") && !scope.is_bound("fix") {
            let g = translate_expr(arg, scope)?;
            return Ok(Ast::Fix(Box::new(g)));
        }
        // `import <path>` → splice the parsed file in place (pre-eval inlining,
        // arch §5). Resolved relative to the importing file's directory.
        if txt.as_deref() == Some("import") && !scope.is_bound("import") {
            // `import <name/sub>` is a search-path ref: resolve it through the
            // registry to a local path, then import that path normally
            // (nixpkgs-lib-design.md §1). A `<…>` token can ONLY take this
            // branch, so the bracket-literal-as-filename bug is unrepresentable.
            if let Some(inner) = angle_inner(&arg) {
                return import_file(resolve_angle(&inner, scope)?, scope);
            }
            // Otherwise `import` only accepts a literal path/string target. A
            // non-literal arg (e.g. `import 5`) is rejected up-front with a
            // typed error rather than falling through to a reducer "readback
            // incomplete" (imports-design.md:172).
            let p = literal_path_text(&arg)
                .ok_or_else(|| NixError::UnsupportedSyntax("import: non-literal path".into()))?;
            return import_file(p.into(), scope);
        }
    }
    let f = translate_expr(func, scope)?;
    let x = translate_expr(arg, scope)?;
    Ok(Ast::App(Box::new(f), Box::new(x)))
}

/// The bracket-inner text of a search-path argument: `<nixpkgs/lib>` → Some
/// `"nixpkgs/lib"`. rnix lexes an angle path as `ast::Expr::Path` whose
/// `to_string()` keeps the surrounding `<` `>` (concurs imports-design.md §4).
/// Any other expression is `None` and falls through to literal-path handling.
fn angle_inner(arg: &ast::Expr) -> Option<String> {
    if let ast::Expr::Path(p) = arg {
        let t = p.to_string();
        return t
            .strip_prefix('<')
            .and_then(|t| t.strip_suffix('>'))
            .map(str::to_string);
    }
    None
}

/// Resolve a search-path ref (`nixpkgs/lib`) to a local path via the scope's
/// registry (nixpkgs-lib-design.md §1.3). The whole inner string is tried as a
/// key first (`nixpkgs/lib=…/lib-shim.nix`); failing that, the first path
/// segment is the root key and the remainder is joined onto it (`nixpkgs=DIR`
/// → `DIR/lib`). An unknown root is a typed `SearchPathUnset`, never a
/// filesystem ENOENT.
fn resolve_angle(inner: &str, scope: &crate::scope::Scope) -> Result<std::path::PathBuf, NixError> {
    if let Some(dir) = scope.search_paths.get(inner) {
        return Ok(dir.clone());
    }
    if let Some((root, sub)) = inner.split_once('/') {
        if let Some(dir) = scope.search_paths.get(root) {
            return Ok(dir.join(sub));
        }
    }
    Err(NixError::SearchPathUnset(inner.to_string()))
}

/// Extract a literal path/string `import` target. Search-path (`<…>`) targets
/// are handled separately by [`angle_inner`]/[`resolve_angle`] before this.
fn literal_path_text(arg: &ast::Expr) -> Option<String> {
    match arg {
        ast::Expr::Path(p) => Some(p.to_string()),
        ast::Expr::Str(s) => {
            let mut out = String::new();
            for part in s.normalized_parts() {
                match part {
                    ast::InterpolPart::Literal(l) => out.push_str(&l),
                    ast::InterpolPart::Interpolation(_) => return None,
                }
            }
            Some(out)
        }
        _ => None,
    }
}

/// Cap on `import` nesting depth — guards a pathological (non-cyclic) deep
/// import chain from exhausting the Rust stack before the cycle set would.
const MAX_IMPORT_DEPTH: usize = 256;

/// Read, parse and splice an imported file, resolving relative paths against the
/// current scope's base directory. The imported file's own directory becomes the
/// base for any nested `import`s.
///
/// Cycle-safe: the canonical path of every file currently being resolved up this
/// chain is tracked in `scope.in_progress`; re-entering one (mutual or self
/// import) returns `NixError::ImportCycle` instead of recursing the Rust stack
/// into a stack overflow (vic/plans/imports-design.md:166-167).
fn import_file(mut full: std::path::PathBuf, scope: &crate::scope::Scope) -> Result<E, NixError> {
    if full.is_relative() {
        if let Some(base) = &scope.base_dir {
            full = base.join(&full);
        }
    }
    // Importing a directory resolves to its `default.nix` (cppNix semantics we
    // keep — imports-design.md §1/§2.2). Do this before the read so a directory
    // target reads the right file instead of failing with "Is a directory".
    if full.is_dir() {
        full.push("default.nix");
    }
    // Depth cap fires on the resolve-chain length regardless of whether this
    // file exists — guards a pathological deep chain before any further I/O or
    // stack recursion (imports-design.md:166-167).
    if scope.in_progress.len() >= MAX_IMPORT_DEPTH {
        let canon = full.canonicalize().unwrap_or(full);
        return Err(NixError::ImportCycle(canon));
    }
    let src = std::fs::read_to_string(&full)
        .map_err(|e| NixError::ParseError(format!("import {}: {e}", full.display())))?;
    // Canonical identity for cycle detection (read succeeded, so the file exists).
    let canon = full.canonicalize().unwrap_or_else(|_| full.clone());
    if scope.in_progress.contains(&canon) {
        return Err(NixError::ImportCycle(canon));
    }
    let base = canon
        .parent()
        .map(std::path::Path::to_path_buf)
        .unwrap_or_default();
    let mut child = crate::scope::Scope::with_base(base);
    child.in_progress = scope.in_progress.clone();
    child.in_progress.insert(canon);
    // Inherit the parent's registry (cheap Arc clone) so nested `import <…>`
    // resolve identically regardless of import depth.
    child.search_paths = scope.search_paths.clone();
    super::parse_with(&src, &mut child)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use std::path::PathBuf;

    fn scope_with(entries: &[(&str, &str)]) -> crate::scope::Scope {
        let map: HashMap<String, PathBuf> = entries
            .iter()
            .map(|(k, v)| ((*k).to_string(), PathBuf::from(*v)))
            .collect();
        crate::scope::Scope {
            search_paths: Arc::new(map),
            ..crate::scope::Scope::new()
        }
    }

    fn angle(src: &str) -> ast::Expr {
        rnix::Root::parse(src)
            .tree()
            .expr()
            .expect("angle expr parses")
    }

    #[test]
    fn angle_inner_strips_brackets() {
        assert_eq!(
            angle_inner(&angle("<nixpkgs/lib>")).as_deref(),
            Some("nixpkgs/lib")
        );
        assert_eq!(angle_inner(&angle("<nixpkgs>")).as_deref(), Some("nixpkgs"));
    }

    #[test]
    fn angle_inner_rejects_non_angle() {
        // A relative path literal is not a search-path ref.
        assert_eq!(angle_inner(&angle("./val.nix")), None);
    }

    #[test]
    fn resolve_angle_exact_key_wins() {
        let scope = scope_with(&[("nixpkgs/lib", "/shim/lib-shim.nix")]);
        assert_eq!(
            resolve_angle("nixpkgs/lib", &scope).expect("resolves"),
            PathBuf::from("/shim/lib-shim.nix")
        );
    }

    #[test]
    fn resolve_angle_root_joins_sub() {
        let scope = scope_with(&[("nixpkgs", "/nixpkgs-dir")]);
        assert_eq!(
            resolve_angle("nixpkgs/lib", &scope).expect("resolves"),
            PathBuf::from("/nixpkgs-dir/lib")
        );
    }

    #[test]
    fn resolve_angle_unset_is_typed_error() {
        let scope = scope_with(&[]);
        match resolve_angle("nixpkgs/lib", &scope) {
            Err(NixError::SearchPathUnset(n)) => assert_eq!(n, "nixpkgs/lib"),
            other => panic!("expected SearchPathUnset, got {other:?}"),
        }
    }
}
