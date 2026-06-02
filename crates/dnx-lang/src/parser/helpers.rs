use dnx_ast::Ast;
use rnix::ast;
use std::sync::Arc;

use crate::error::NixError;
use crate::prim::{NixPrimFun, NixPrimVal};
use crate::scope::Name;

pub(super) type E = Ast<NixPrimVal, NixPrimFun>;

pub(super) fn wrap_uses(name: Name, uses: u32, body: E) -> E {
    match uses {
        0 => Ast::Era(Box::new(Ast::Name(name)), Box::new(body)),
        1 => body,
        n => build_rep_chain(name, n as usize, body),
    }
}

pub(super) fn build_rep_chain(name: Name, uses: usize, body: E) -> E {
    if uses <= 1 {
        return body;
    }
    let split_names: Vec<Name> = (0..uses)
        .map(|i| Arc::from(format!("{name}__{i}").as_str()))
        .collect();
    let mut idx = 0;
    let body = indexed_rename(body, &name, &split_names, &mut idx);
    nest_reps(Ast::Name(name), &split_names, body)
}

fn indexed_rename(expr: E, from: &Name, names: &[Name], idx: &mut usize) -> E {
    match expr {
        Ast::Name(n) if &n == from => {
            let r = names[*idx].clone();
            *idx += 1;
            Ast::Name(r)
        }
        Ast::Name(n) => Ast::Name(n),
        Ast::Abs(x, body) if &x == from => Ast::Abs(x, body),
        Ast::Abs(x, body) => Ast::Abs(x, Box::new(indexed_rename(*body, from, names, idx))),
        Ast::App(f, x) => Ast::App(
            Box::new(indexed_rename(*f, from, names, idx)),
            Box::new(indexed_rename(*x, from, names, idx)),
        ),
        Ast::Rep(e, a, b, body) => {
            let e2 = Box::new(indexed_rename(*e, from, names, idx));
            if &a == from || &b == from {
                Ast::Rep(e2, a, b, body)
            } else {
                Ast::Rep(e2, a, b, Box::new(indexed_rename(*body, from, names, idx)))
            }
        }
        Ast::Era(e, body) => Ast::Era(
            Box::new(indexed_rename(*e, from, names, idx)),
            Box::new(indexed_rename(*body, from, names, idx)),
        ),
        Ast::Fix(e) => Ast::Fix(Box::new(indexed_rename(*e, from, names, idx))),
        other => other,
    }
}

fn nest_reps(expr: E, names: &[Name], body: E) -> E {
    if names.len() == 2 {
        Ast::Rep(
            Box::new(expr),
            names[0].clone(),
            names[1].clone(),
            Box::new(body),
        )
    } else {
        let rest: Name = Arc::from(format!("__rr_{}", names[1]).as_str());
        let inner = nest_reps(Ast::Name(rest.clone()), &names[1..], body);
        Ast::Rep(Box::new(expr), names[0].clone(), rest, Box::new(inner))
    }
}

pub(super) fn count_uses_in(expr: &E, name: &Name) -> u32 {
    match expr {
        Ast::Name(n) if n == name => 1,
        Ast::Name(_) => 0,
        Ast::Abs(x, _) if x == name => 0,
        Ast::Abs(_, body) => count_uses_in(body, name),
        Ast::App(f, x) => count_uses_in(f, name) + count_uses_in(x, name),
        Ast::Rep(e, a, b, body) => {
            count_uses_in(e, name)
                + if a == name || b == name {
                    0
                } else {
                    count_uses_in(body, name)
                }
        }
        Ast::Era(e, body) => count_uses_in(e, name) + count_uses_in(body, name),
        // INVARIANT: this match MUST count exactly the occurrences `indexed_rename`
        // rewrites — same traversal coverage — or the rep-split `split_names` length
        // diverges from `*idx` and `names[*idx]` over-indexes. `indexed_rename`
        // descends into `Fix` (it is NOT a binder), so we must too.
        Ast::Fix(e) => count_uses_in(e, name),
        // `Val`/`Fun`/`Perform`/`Handle`: `indexed_rename` does NOT descend these
        // (its `other => other` arm), so they contribute 0 here to stay in lockstep.
        Ast::Val(_) | Ast::Fun(_) | Ast::Perform(_, _) | Ast::Handle(_, _) => 0,
    }
}

/// Lower a single attr key to a runtime string `E`. Static `Ident`/`Str` keys
/// become `Str` literals; a dynamic `${e}` key lowers its inner expr (which must
/// evaluate to a string), so select/hasAttr/insert prims receive the key as a
/// runtime value either way. Var refs inside `${e}` are use-counted via `scope`.
pub(super) fn attr_key_expr(
    attr: &ast::Attr,
    scope: &mut crate::scope::Scope,
) -> Result<E, NixError> {
    match attr {
        ast::Attr::Ident(_) | ast::Attr::Str(_) => {
            Ok(Ast::Val(NixPrimVal::Str(attr_static_name(attr)?)))
        }
        ast::Attr::Dynamic(d) => super::translate_expr(
            d.expr()
                .ok_or_else(|| NixError::UnsupportedSyntax("dynamic attr: empty ${}".into()))?,
            scope,
        ),
    }
}

/// The static text of an `Ident`/`Str` attr. Errors on a dynamic attr (callers
/// that accept dynamics use `attr_key_expr` instead).
pub(super) fn attr_static_name(attr: &ast::Attr) -> Result<Name, NixError> {
    match attr {
        ast::Attr::Ident(i) => Ok(i
            .ident_token()
            .map(|t| Arc::from(t.text()))
            .unwrap_or_else(|| Arc::from(""))),
        ast::Attr::Str(s) => {
            let mut r = String::new();
            for part in s.normalized_parts() {
                if let ast::InterpolPart::Literal(l) = part {
                    r.push_str(&l);
                }
            }
            Ok(Arc::from(r.as_str()))
        }
        ast::Attr::Dynamic(_) => Err(NixError::UnsupportedSyntax("dynamic attr key".into())),
    }
}

pub(super) fn attrpath_simple_name(apv: &ast::AttrpathValue) -> Result<Name, NixError> {
    let ap = apv
        .attrpath()
        .ok_or_else(|| NixError::UnsupportedSyntax("missing attrpath".into()))?;
    attrpath_to_str(&ap)
}

pub(super) fn attrpath_to_str(ap: &ast::Attrpath) -> Result<Name, NixError> {
    let mut parts: Vec<String> = vec![];
    for attr in ap.attrs() {
        parts.push(attr_static_name(&attr)?.to_string());
    }
    Ok(Arc::from(parts.join(".").as_str()))
}

/// Desugar an `inherit` entry to `(name, value)` IR pairs.
/// `inherit a b;` → `a = a; b = b;` (each name resolved in the enclosing
/// scope — cppNix `Kind::Inherited`). `inherit (e) a b;` → `a = e.a; b = e.b;`.
///
/// With a source, `e` is re-translated once per name: dnx is linear, so each
/// `e.NAME` needs its own counted use of `e` (a single shared clone would
/// under-count and trip the rep/era checker). Re-translation duplicates a
/// simple source ref cheaply and keeps the use counts honest.
pub(super) fn desugar_inherit(
    inherit: ast::Inherit,
    scope: &mut crate::scope::Scope,
) -> Result<Vec<(Name, E)>, NixError> {
    let from = inherit.from();
    let mut out = vec![];
    for attr in inherit.attrs() {
        let name = inherit_attr_name(&attr)?;
        let val = match &from {
            // `inherit (e) name` → `e.name` via the Select primitive.
            Some(f) => {
                let src = super::translate_expr(
                    f.expr().ok_or_else(|| {
                        NixError::UnsupportedSyntax("inherit (e): empty source".into())
                    })?,
                    scope,
                )?;
                let key: E = Ast::Val(NixPrimVal::Str(name.clone()));
                Ast::App(
                    Box::new(Ast::App(
                        Box::new(Ast::Fun(NixPrimFun::Select)),
                        Box::new(src),
                    )),
                    Box::new(key),
                )
            }
            // `inherit name` → reference to the enclosing `name`.
            None => {
                scope.use_var(&name);
                Ast::Name(name.clone())
            }
        };
        out.push((name, val));
    }
    Ok(out)
}

fn inherit_attr_name(attr: &ast::Attr) -> Result<Name, NixError> {
    attr_static_name(attr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::nix_to_expr;

    /// Count every `Name(==from)` leaf in `e` — the ground truth `indexed_rename`
    /// must rewrite. Independent of `count_uses_in` so it can judge it.
    fn occurrences(e: &E, from: &Name) -> usize {
        match e {
            Ast::Name(n) if n == from => 1,
            Ast::Name(_) | Ast::Val(_) | Ast::Fun(_) => 0,
            Ast::Abs(x, _) if x == from => 0,
            Ast::Abs(_, b) => occurrences(b, from),
            Ast::App(f, x) => occurrences(f, from) + occurrences(x, from),
            Ast::Rep(e, a, b, body) => {
                occurrences(e, from)
                    + if a == from || b == from {
                        0
                    } else {
                        occurrences(body, from)
                    }
            }
            Ast::Era(e, b) => occurrences(e, from) + occurrences(b, from),
            Ast::Fix(e) => occurrences(e, from),
            Ast::Perform(_, e) => occurrences(e, from),
            Ast::Handle(e, _) => occurrences(e, from),
        }
    }

    /// `count_uses_in` MUST equal the number of leaves `indexed_rename` consumes,
    /// for a body that puts the name inside a `Fix` — the divergence the bug hit.
    #[test]
    fn count_uses_matches_rename_under_fix() {
        let name: Name = Arc::from("self");
        // self used twice, both inside a Fix body: f (self self)
        let body: E = Ast::Fix(Box::new(Ast::App(
            Box::new(Ast::Name(name.clone())),
            Box::new(Ast::Name(name.clone())),
        )));
        let uses = count_uses_in(&body, &name);
        assert_eq!(uses, 2, "count_uses_in must see Fix-internal uses");
        assert_eq!(uses as usize, occurrences(&body, &name));

        // build_rep_chain consumes exactly `uses` split-names — no over-index panic.
        let split: Vec<Name> = (0..uses)
            .map(|i| Arc::from(format!("{name}__{i}").as_str()))
            .collect();
        let mut idx = 0usize;
        let _ = indexed_rename(body, &name, &split, &mut idx);
        assert_eq!(idx, split.len(), "indexed_rename consumed all split names");
    }

    /// e2e: `with e; fix (self: f)` family — `f` is a with-field, and one of its
    /// uses lives inside the `Fix`. The Fix-internal use must be counted, else the
    /// rep-split `split_names` is too short and `indexed_rename` over-indexes
    /// `names[*idx]` → panic. We force the rep chain (uses ≥ 2 outside the Fix)
    /// plus an extra use inside the Fix, the exact divergence the audit flagged.
    #[test]
    fn with_field_used_inside_fix_no_panic() {
        // f used twice in `[f f]` (rep chain) + once inside `fix (self: f)`.
        let e = nix_to_expr("with { f = (x: x); }; [ f f (fix (self: f)) ]");
        assert!(e.is_ok(), "must not panic/err: {e:?}");
        // top is the `with` env-binder application; the Fix sits below.
        assert!(matches!(e.unwrap(), Ast::App(_, _)));
    }

    /// e2e: pattern `@`-arg whose bound name is referenced inside a `fix`.
    /// The `@`-arg path (`lambda.rs:134`) feeds `uses` from `count_uses_in` too,
    /// so a Fix-internal use of the arg must be counted the same way.
    #[test]
    fn pattern_at_arg_used_inside_fix_no_panic() {
        // `args` used twice (rep chain) + once inside the Fix body.
        let e = nix_to_expr("args@{ f }: [ args args (fix (self: args.f)) ]");
        assert!(e.is_ok(), "must not panic/err: {e:?}");
        assert!(matches!(e.unwrap(), Ast::Abs(_, _)));
    }
}
