use dnx_ast::Ast;
use rnix::ast::{self, HasEntry};

use crate::error::NixError;
use crate::prim::{NixPrimFun, NixPrimVal};
use crate::scope::Name;

use super::helpers::{
    attr_key_expr, attr_static_name, attrpath_simple_name, count_uses_in, desugar_inherit,
    wrap_uses,
};
use super::{fresh, translate_expr, E};

pub(super) fn translate_list(
    list: ast::List,
    scope: &mut crate::scope::Scope,
) -> Result<E, NixError> {
    let elems: Vec<ast::Expr> = list.items().collect();
    let mut result: E = super::prelude_ref("nil");
    for elem in elems.into_iter().rev() {
        let e = translate_expr(elem, scope)?;
        let cons = super::prelude_ref("cons");
        result = Ast::App(
            Box::new(Ast::App(Box::new(cons), Box::new(e))),
            Box::new(result),
        );
    }
    Ok(result)
}

pub(super) fn translate_attrset(
    attrset: ast::AttrSet,
    scope: &mut crate::scope::Scope,
) -> Result<E, NixError> {
    if attrset.rec_token().is_some() {
        return translate_rec_attrset(attrset, scope);
    }
    let mut set: E = Ast::Fun(NixPrimFun::EmptyAttrSet);
    for entry in attrset.entries() {
        for (key, val) in entry_pairs(entry, scope)? {
            set = app3(NixPrimFun::Insert, set, key, val);
        }
    }
    Ok(set)
}

/// Lower one attrset entry to `(key_expr, value_expr)` insert pairs. An
/// `AttrpathValue` yields one pair (its key lowered as a runtime string, so a
/// dynamic `${k}` key is supported); an `inherit` yields one pair per name.
fn entry_pairs(
    entry: ast::Entry,
    scope: &mut crate::scope::Scope,
) -> Result<Vec<(E, E)>, NixError> {
    match entry {
        ast::Entry::AttrpathValue(apv) => {
            let key = apv_key_expr(&apv, scope)?;
            let val = translate_expr(
                apv.value()
                    .ok_or_else(|| NixError::UnsupportedSyntax("attrset missing value".into()))?,
                scope,
            )?;
            Ok(vec![(key, val)])
        }
        ast::Entry::Inherit(inherit) => Ok(desugar_inherit(inherit, scope)?
            .into_iter()
            .map(|(name, src)| (Ast::Val(NixPrimVal::Str(name)), src))
            .collect()),
    }
}

/// An entry key as a runtime string `E`. A single `${k}` attr lowers its inner
/// expr (dynamic key); a dotted path stays a static joined name.
fn apv_key_expr(apv: &ast::AttrpathValue, scope: &mut crate::scope::Scope) -> Result<E, NixError> {
    let ap = apv
        .attrpath()
        .ok_or_else(|| NixError::UnsupportedSyntax("missing attrpath".into()))?;
    let attrs: Vec<ast::Attr> = ap.attrs().collect();
    match attrs.as_slice() {
        [one] => attr_key_expr(one, scope),
        _ => Ok(Ast::Val(NixPrimVal::Str(attrpath_simple_name(apv)?))),
    }
}

/// `rec { a = …; b = a; }` — values may reference sibling keys. Desugars to a
/// let-fold (same lowering as `let … in`): bind all names, translate values so
/// each sees its siblings, build the attrset over those bound names, then wrap
/// every name in an `Abs`/`App` whose arity is its measured use count (dnx is
/// linear). Acyclic / non-self-referential keys only; a key that uses itself
/// needs the recursion (`Fix`) work and is not handled here.
fn translate_rec_attrset(
    attrset: ast::AttrSet,
    scope: &mut crate::scope::Scope,
) -> Result<E, NixError> {
    let mut names: Vec<Name> = vec![];
    let mut val_srcs: Vec<ast::Expr> = vec![];
    let mut inherits: Vec<(E, E)> = vec![];
    for entry in attrset.entries() {
        match entry {
            ast::Entry::AttrpathValue(apv) => {
                names.push(attrpath_simple_name(&apv)?);
                val_srcs.push(apv.value().ok_or_else(|| {
                    NixError::UnsupportedSyntax("rec attrset missing value".into())
                })?);
            }
            // `inherit` resolves in the *enclosing* scope, so it is not part of
            // the recursive group; lower it eagerly like a non-rec entry.
            ast::Entry::Inherit(inherit) => {
                for (name, src) in desugar_inherit(inherit, scope)? {
                    inherits.push((Ast::Val(NixPrimVal::Str(name)), src));
                }
            }
        }
    }
    for n in &names {
        scope.bind(n.clone());
    }
    let vals: Vec<E> = val_srcs
        .into_iter()
        .map(|e| translate_expr(e, scope))
        .collect::<Result<_, _>>()?;
    // Build the set body over the bound names (each name used once here).
    let mut set: E = Ast::Fun(NixPrimFun::EmptyAttrSet);
    for (key, val) in inherits {
        set = app3(NixPrimFun::Insert, set, key, val);
    }
    for n in &names {
        let key = Ast::Val(NixPrimVal::Str(n.clone()));
        // This `Name` ref is a real use; record it so the count matches the AST
        // (sibling-value uses are already tracked by `translate_expr`).
        scope.use_var(n);
        set = app3(NixPrimFun::Insert, set, key, Ast::Name(n.clone()));
    }
    let uses: Vec<u32> = names.iter().map(|n| scope.use_count(n)).collect();
    for n in &names {
        scope.unbind(n);
    }
    let mut body = set;
    for ((name, val), n) in names.iter().zip(vals).zip(uses.iter()).rev() {
        let wrapped = wrap_uses(name.clone(), *n, body);
        body = Ast::App(
            Box::new(Ast::Abs(name.clone(), Box::new(wrapped))),
            Box::new(val),
        );
    }
    Ok(body)
}

pub(super) fn translate_select(
    select: ast::Select,
    scope: &mut crate::scope::Scope,
) -> Result<E, NixError> {
    let set_expr = select
        .expr()
        .ok_or_else(|| NixError::UnsupportedSyntax("select missing set".into()))?;
    let attr_path = select
        .attrpath()
        .ok_or_else(|| NixError::UnsupportedSyntax("select missing attrpath".into()))?;

    let default = match select.default_expr() {
        Some(d) if select.or_token().is_some() => Some(translate_expr(d, scope)?),
        _ => None,
    };

    // `builtins.NAME` → the primitive directly (builtins namespace, no real attrset).
    let builtins_ns = matches!(&set_expr, ast::Expr::Ident(i)
        if i.ident_token().map(|t| t.text() == "builtins").unwrap_or(false))
        && !scope.is_bound("builtins");
    let attrs: Vec<ast::Attr> = attr_path.attrs().collect();

    // `e.a.b or d`: the default guards the *whole* path (Nix manual) — it falls
    // back when *any* hop is missing, and the default itself is never re-selected
    // (`e.x.y or d` with `x` absent is `d`, not `d.y`). A per-hop `SelectOr` chain
    // would wrongly re-select into the returned default, so a multi-hop default
    // lowers to `let s = e in if (s ? a.b) then s.a.b else d` instead: one
    // existence test over the whole path, then the plain select chain. `s` is
    // hoisted (used by both the test and the chain) so `e` is translated once and
    // dnx stays linear.
    if let (true, false, [_, _, ..]) = (default.is_some(), builtins_ns, attrs.as_slice()) {
        let dexpr = default.ok_or_else(|| NixError::UnsupportedSyntax("select or".into()))?;
        let sname = fresh("sel");
        // Keys are shared by the existence test and the select chain; hoist them
        // (and the set) to binders so each is evaluated once and dynamic `${k}`
        // keys are supported (was static-only via `attr_static_name`).
        let body = bind_path_keys(&attrs, scope, |keys| {
            let cond = has_path_named(Ast::Name(sname.clone()), keys)?;
            let chain = select_chain(Ast::Name(sname.clone()), keys);
            Ok(app2_raw(cond, chain, dexpr))
        })?;
        let set = translate_expr(set_expr, scope)?;
        return Ok(let_bind(sname, set, body));
    }

    let mut iter = attrs.into_iter();
    let mut result = if builtins_ns {
        let first = iter
            .next()
            .ok_or_else(|| NixError::UnsupportedSyntax("builtins. missing attr".into()))?;
        let name = attr_static_name(&first)?;
        // Scott-list builtins (`head`/`map`/`length`/…) are Nix-defined prelude
        // defs, not prim-table entries (`to_fun` returns None for them). Route
        // `builtins.NAME` to the prelude `Name` so pass0 inlines the def — exactly
        // as a bare `NAME` ident resolves (lambda.rs:32). Real prims stay `Builtin`.
        if crate::prelude::is_prelude_name(name.as_ref()) {
            Ast::Name(name)
        } else {
            Ast::Fun(NixPrimFun::Builtin(name))
        }
    } else {
        translate_expr(set_expr, scope)?
    };
    let last = iter.len().saturating_sub(1);
    let mut default = default;
    for (i, attr) in iter.enumerate() {
        let key = attr_key_expr(&attr, scope)?;
        result = match default.take().filter(|_| i == last) {
            Some(d) => app3(NixPrimFun::SelectOr, result, key, d),
            None => app2(NixPrimFun::Select, result, key),
        };
    }
    Ok(result)
}

/// Plain `set.k0.k1.…kn` select chain (no default) over already-lowered key
/// names (each a `Name` bound to a key-value by `bind_path_keys`).
fn select_chain(set: E, keys: &[Name]) -> E {
    let mut result = set;
    for k in keys {
        result = app2(NixPrimFun::Select, result, Ast::Name(k.clone()));
    }
    result
}

/// Hoist `val` into a single `let`-binder over `body`: `(\name. body') val`,
/// where `body'` rep-splits the `name` uses so dnx stays linear when `name`
/// occurs more than once (mirrors the `with`-field hoist, binding.rs §3c).
fn let_bind(name: Name, val: E, body: E) -> E {
    let uses = count_uses_in(&body, &name);
    let wrapped = wrap_uses(name.clone(), uses, body);
    Ast::App(Box::new(Ast::Abs(name, Box::new(wrapped))), Box::new(val))
}

fn app2(f: NixPrimFun, a: E, b: E) -> E {
    Ast::App(
        Box::new(Ast::App(Box::new(Ast::Fun(f)), Box::new(a))),
        Box::new(b),
    )
}

fn app3(f: NixPrimFun, a: E, b: E, c: E) -> E {
    Ast::App(Box::new(app2(f, a, b)), Box::new(c))
}

pub(super) fn translate_has_attr(
    has: ast::HasAttr,
    scope: &mut crate::scope::Scope,
) -> Result<E, NixError> {
    let set = translate_expr(
        has.expr()
            .ok_or_else(|| NixError::UnsupportedSyntax("hasAttr missing set".into()))?,
        scope,
    )?;
    let attr_path = has
        .attrpath()
        .ok_or_else(|| NixError::UnsupportedSyntax("hasAttr missing attrpath".into()))?;
    let attrs: Vec<ast::Attr> = attr_path.attrs().collect();
    match attrs.as_slice() {
        // Single key (the common `s ? k` / `s ? ${k}`) lowers the key as a
        // runtime value, so a dynamic `${k}` is supported.
        [one] => Ok(app2(NixPrimFun::HasAttr, set, attr_key_expr(one, scope)?)),
        // Nested `s ? a.b.c`: the path exists iff every prefix-hop has its next
        // key, i.e. `(s ? a) && (s.a ? b) && (s.a.b ? c)` (Nix manual). `s` and
        // each key are hoisted to binders (translated once, rep-split per hop) so
        // dnx stays linear; dynamic `${k}` keys in any hop are supported.
        keys => bind_path_keys(keys, scope, |knames| has_path_named(set, knames)),
    }
}

/// `set ? k0.k1.…kn` as the conjunction of per-hop existence tests over a single
/// hoisted `set` binder, given already-lowered key names. `set` and each key are
/// reused across hops, so the caller hoists them to `Name` binders (`bind_path`,
/// `bind_path_keys`) and the rep-split machinery keeps dnx linear.
fn has_path_named(set: E, keys: &[Name]) -> Result<E, NixError> {
    let sname = fresh("has");
    let mut term: Option<E> = None;
    for i in 0..keys.len() {
        let mut prefix = Ast::Name(sname.clone());
        for k in &keys[..i] {
            prefix = app2(NixPrimFun::Select, prefix, Ast::Name(k.clone()));
        }
        let hop = app2(NixPrimFun::HasAttr, prefix, Ast::Name(keys[i].clone()));
        term = Some(match term {
            Some(acc) => and(acc, hop),
            None => hop,
        });
    }
    let body = term.ok_or_else(|| NixError::UnsupportedSyntax("hasAttr empty path".into()))?;
    Ok(let_bind(sname, set, body))
}

/// Lower each attrpath key once (counted once in `scope`) and hoist it to a
/// fresh `Name` binder over `body`. The key names (in path order) are handed to
/// `make_body`, which builds the select/has chains referencing them; a key used
/// at several hops is rep-split by `let_bind`, so dynamic `${k}` keys (whose
/// inner expr may reference variables) stay linear and are evaluated once.
fn bind_path_keys(
    keys: &[ast::Attr],
    scope: &mut crate::scope::Scope,
    make_body: impl FnOnce(&[Name]) -> Result<E, NixError>,
) -> Result<E, NixError> {
    let lowered: Vec<(Name, E)> = keys
        .iter()
        .map(|a| Ok((fresh("k"), attr_key_expr(a, scope)?)))
        .collect::<Result<_, NixError>>()?;
    let names: Vec<Name> = lowered.iter().map(|(n, _)| n.clone()).collect();
    let mut body = make_body(&names)?;
    for (name, key) in lowered.into_iter().rev() {
        body = let_bind(name, key, body);
    }
    Ok(body)
}

/// Church-bool `a && b` (native `&&`, literals.rs): `a b false`.
fn and(a: E, b: E) -> E {
    app2_raw(a, b, super::false_val())
}

fn app2_raw(f: E, a: E, b: E) -> E {
    Ast::App(Box::new(Ast::App(Box::new(f), Box::new(a))), Box::new(b))
}

#[cfg(test)]
mod tests {
    use crate::runtime::{NixEvalResult, NixRuntime};

    fn eval(src: &str) -> NixEvalResult {
        NixRuntime::pure().eval(src)
    }
    fn int(src: &str) -> i64 {
        match eval(src) {
            NixEvalResult::Int(n) => n,
            _ => panic!("{src}: unexpected result"),
        }
    }
    fn boolv(src: &str) -> bool {
        match eval(src) {
            NixEvalResult::Bool(b) => b,
            _ => panic!("{src}: unexpected result"),
        }
    }
    fn is_err(src: &str) -> bool {
        matches!(eval(src), NixEvalResult::Error(_))
    }

    // --- dynamic attrs (#4) ---
    #[test]
    fn dyn_select() {
        assert_eq!(int(r#"let s = { a = 1; }; k = "a"; in s.${k}"#), 1);
    }
    #[test]
    fn dyn_key_insert() {
        assert_eq!(int(r#"let k = "x"; in { ${k} = 5; }.x"#), 5);
    }
    #[test]
    fn dyn_has_attr_present() {
        assert!(boolv(r#"let k = "a"; in { a = 1; } ? ${k}"#));
    }
    #[test]
    fn dyn_has_attr_missing() {
        assert!(!boolv(r#"let k = "z"; in { a = 1; } ? ${k}"#));
    }

    // --- dynamic key in a MULTI-HOP attrpath (gen-algebra rec.nix) ---
    // `r.e.${l} or d`: static prefix hop, dynamic leaf, with a default. The
    // multi-hop-default branch hoists the path into an existence test + chain;
    // both must accept the dynamic leaf key (was rejected by `attr_static_name`).
    #[test]
    fn dyn_select_multihop_or_present() {
        assert_eq!(
            int(r#"let r = { e = { x = 7; }; }; l = "x"; in r.e.${l} or 0"#),
            7
        );
    }
    #[test]
    fn dyn_select_multihop_or_missing_leaf() {
        assert_eq!(
            int(r#"let r = { e = { y = 7; }; }; l = "x"; in r.e.${l} or 9"#),
            9
        );
    }
    // `s ? a.${l}`: nested hasAttr with a dynamic leaf key.
    #[test]
    fn dyn_has_attr_multihop_present() {
        assert!(boolv(
            r#"let r = { e = { x = 1; }; }; l = "x"; in r ? e.${l}"#
        ));
    }
    #[test]
    fn dyn_has_attr_multihop_missing() {
        assert!(!boolv(
            r#"let r = { e = { x = 1; }; }; l = "z"; in r ? e.${l}"#
        ));
    }
    // NOTE: the rec.nix line-12 shape `builtins.head (r.e.${l} or [])` (list-valued
    // multi-hop default) is NOT tested here: the *lowering* is exercised by the
    // int/bool cases above, but a list-valued multi-hop `or` hits the reducer's
    // documented demand-eval gap (2nd-arg force-to-WHNF, full-nix-coverage-roadmap.md
    // #2) — `r.e.x or []` (STATIC) fails identically, so this is a pre-existing
    // reducer limitation, not a dynamic-key lowering gap. No regression.

    // --- or-default (#5) ---
    #[test]
    fn or_default_present() {
        assert_eq!(int("{ a = 1; }.a or 9"), 1);
    }
    #[test]
    fn or_default_missing() {
        assert_eq!(int("{ a = 1; }.b or 9"), 9);
    }

    // --- rec (#7): acyclic / non-self-referential ---
    #[test]
    fn rec_sibling_ref() {
        assert_eq!(int("rec { a = 1; b = a; }.b"), 1);
    }
    #[test]
    fn rec_chain() {
        assert_eq!(int("rec { a = 1; b = a; c = b; }.c"), 1);
    }
    #[test]
    fn rec_dup_use() {
        // `a` referenced by two siblings → Rep-duplicated, must stay linear.
        assert_eq!(int("rec { a = 1; b = a; c = a; }.b"), 1);
    }
    #[test]
    fn rec_inherit_member() {
        assert_eq!(int("let x = 7; in rec { a = x; b = a; }.b"), 7);
    }
    #[test]
    fn rec_self_ref_unsupported() {
        // Genuine self-recursion needs the `Fix` work; must error, not loop/crash.
        assert!(is_err("rec { a = a; }.a"));
    }

    // --- nested attrpath `?` (full-nix-coverage-roadmap.md #2/#4) ---
    #[test]
    fn nested_has_present() {
        assert!(boolv("{ a = { b = 1; }; } ? a.b"));
    }
    #[test]
    fn nested_has_missing_leaf() {
        assert!(!boolv("{ a = { b = 1; }; } ? a.c"));
    }
    #[test]
    fn nested_has_missing_root() {
        // First hop absent → false, must not error on the inner re-select.
        assert!(!boolv("{ a = { b = 1; }; } ? x.y"));
    }
    #[test]
    fn nested_has_deep() {
        assert!(boolv("{ a = { b = { c = 1; }; }; } ? a.b.c"));
        assert!(!boolv("{ a = { b = { c = 1; }; }; } ? a.b.d"));
    }

    // --- nested attrpath `or` (default guards the whole path) ---
    #[test]
    fn nested_or_present() {
        assert_eq!(int("{ a = { b = 1; }; }.a.b or 9"), 1);
    }
    #[test]
    fn nested_or_missing_leaf() {
        assert_eq!(int("{ a = { b = 1; }; }.a.c or 9"), 9);
    }
    // NOTE: a multi-hop `or` whose *root* hop is absent (`{…}.x.y or 9`) is not
    // tested here: the lowering is the correct Nix desugar (`if (s ? x.y) then
    // s.x.y else 9`), but the reducer eagerly forces the failing intermediate
    // `select s "x"` inside the existence test's second conjunct, so it is
    // forcing-gated on the documented demand-eval gap
    // (full-nix-coverage-roadmap.md #2, "nested ?/or … need 2nd-arg
    // force-to-WHNF"). It errors rather than yielding `9`, exactly as the old
    // single-hop-`SelectOr` lowering did — no regression. Leaf-missing and
    // present paths (which never select through an absent hop) pass above.
}
