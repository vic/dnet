//! `tests.nix` discovery: walk an attrset of `nix-unit`-style cases and pull
//! out each case's `expr`/`expected` as source text, so the runner can evaluate
//! the two sides independently (and in parallel) rather than eagerly folding the
//! whole suite into one value (dnx-test-runner-design.md §2).
//!
//! A leaf is a CASE iff it is an attrset with both an `expr` and an `expected`
//! attribute; any other attrset is a GROUP and is walked recursively. The case
//! id is the dotted path (`arithmetic.testMul`). This structural rule (rather
//! than the `test*`-name convention) is the design's recommended discovery
//! (dnx-test-runner-design.md §10.4) — it is simpler and admits nested groups.
//!
//! A suite may wrap its cases in a top-level `let … in { … }` (the import-tree
//! shape, and the shape every generated adapter emits). Those bindings — `let`
//! defs and `inherit`s alike — are captured verbatim as a source PREFIX and
//! prepended to each case side, so `let lib = …; in { c.expr = lib.f; … }`
//! evaluates each side with `lib` in scope. Per-case evaluation, parallelism and
//! the source-keyed cache are untouched: the prefix is baked into the case
//! source, so its hash still changes iff that case (or the shared bindings) does.

use rnix::ast::{self, HasEntry};

use dnx_core::prim::PrimValue;

use crate::error::NixError;
use crate::runtime::{NixEvalResult, NixRuntime};

/// One discovered test case: a dotted `path` and the two sides as Nix source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TestCase {
    pub path: String,
    pub expr: String,
    pub expected: String,
}

/// One discovered case from a COMPUTED suite: a dotted `path` and the two sides
/// as already-reduced `PrimValue`s (the suite file was evaluated to a value tree,
/// not re-parsed per side — computed-suite-runner.md §2). The sides compare by
/// `PrimValue` equality (`dnx-core::prim`), no second evaluation.
#[derive(Debug, Clone, PartialEq)]
pub struct ValueCase {
    pub path: String,
    pub expr: PrimValue,
    pub expected: PrimValue,
}

/// Parse `src` (the content of a `tests.nix`) and return every case under the
/// top-level attrset, in source order. Any enclosing `let … in` bindings are
/// captured as a source prefix and prepended to each case side (see module
/// docs). A parse error, or a top level that is not an attrset (after peeling
/// parens and a `let`), is an `Err`.
pub fn parse_test_suite(src: &str) -> Result<Vec<TestCase>, NixError> {
    let parse = rnix::Root::parse(src);
    if !parse.errors().is_empty() {
        let errs: Vec<String> = parse.errors().iter().map(|e| e.to_string()).collect();
        return Err(NixError::ParseError(errs.join("; ")));
    }
    let expr = parse
        .tree()
        .expr()
        .ok_or_else(|| NixError::ParseError("empty program".into()))?;
    let mut prelude = String::new();
    let top = as_attrset(&expr, src, &mut prelude)
        .ok_or_else(|| NixError::UnsupportedSyntax("tests file must be an attrset".into()))?;

    let mut out = Vec::new();
    walk(&top, "", &prelude, src, &mut out)?;
    Ok(out)
}

/// Cheap shape peek for the runner's dispatch: does `src` parse to a top level
/// the LITERAL path ([`parse_test_suite`]) accepts — a syntactic attrset, after
/// peeling parens / root / a `let … in`? If so the literal path applies; if not
/// (an application, `mapAttrs`, …) the caller routes to [`discover_computed`].
/// A parse error answers `true`: the literal path owns the clean parse error, so
/// it must not be re-routed into the computed evaluator.
pub fn is_literal_attrset(src: &str) -> bool {
    let parse = rnix::Root::parse(src);
    if !parse.errors().is_empty() {
        return true;
    }
    fn peel(expr: &ast::Expr) -> bool {
        match expr {
            ast::Expr::AttrSet(_) => true,
            ast::Expr::Paren(p) => p.expr().as_ref().is_some_and(peel),
            ast::Expr::Root(r) => r.expr().as_ref().is_some_and(peel),
            ast::Expr::LetIn(l) => l.body().as_ref().is_some_and(peel),
            _ => false,
        }
    }
    parse.tree().expr().as_ref().is_some_and(peel)
}

/// Evaluate `src` (a COMPUTED `tests.nix` whose top level is an application,
/// `mapAttrs`, `flatten`, …) to a single attrset VALUE and read every case from
/// the reduced tree (computed-suite-runner.md §2). The evaluator resolves all
/// scope while reducing, so there is no source prefix to carry: each side is a
/// closed, already-reduced `PrimValue`. A leaf is the same structural rule as the
/// literal path — an attrset with both `expr` and `expected`. Errors: the file
/// failing to reduce, or reducing to a non-attrset.
pub fn discover_computed(src: &str) -> Result<Vec<ValueCase>, NixError> {
    let (value, _interactions) = NixRuntime::pure()
        .eval_canonical(src)
        .map_err(|e| NixError::InternalError(format!("computed suite: {e}")))?;
    let NixEvalResult::AttrSet(kvs) = value else {
        return Err(NixError::UnsupportedSyntax(
            "computed suite must evaluate to an attrset".into(),
        ));
    };
    let mut out = Vec::new();
    walk_value(&PrimValue::AttrSet(kvs), "", &mut out);
    Ok(out)
}

/// Recursively collect cases from a reduced value tree, mirroring the AST `walk`:
/// an attrset value with both `expr` and `expected` is a case at `prefix`; any
/// other attrset is a group whose key extends the dotted path. A non-attrset (or
/// an attrset missing either key, at a non-leaf position) is skipped — the value
/// analogue of the literal walk's "non-case attrs are skipped" rule.
fn walk_value(value: &PrimValue, prefix: &str, out: &mut Vec<ValueCase>) {
    let PrimValue::AttrSet(kvs) = value else {
        return;
    };
    let pick = |name: &str| kvs.iter().find(|(k, _)| &**k == name).map(|(_, v)| v);
    match (pick("expr"), pick("expected")) {
        (Some(expr), Some(expected)) => out.push(ValueCase {
            path: prefix.to_string(),
            expr: expr.clone(),
            expected: expected.clone(),
        }),
        _ => {
            for (key, child) in kvs {
                let path = if prefix.is_empty() {
                    key.to_string()
                } else {
                    format!("{prefix}.{key}")
                };
                walk_value(child, &path, out);
            }
        }
    }
}

/// Unwrap parens/root down to an attrset, if that is what `expr` is. A `let … in`
/// is peeled to its body, and its `let … in ` source (bindings only) is appended
/// to `prelude` so each case side can be evaluated with those bindings in scope.
fn as_attrset(expr: &ast::Expr, src: &str, prelude: &mut String) -> Option<ast::AttrSet> {
    match expr {
        ast::Expr::AttrSet(a) => Some(a.clone()),
        ast::Expr::Paren(p) => as_attrset(&p.expr()?, src, prelude),
        ast::Expr::Root(r) => as_attrset(&r.expr()?, src, prelude),
        // `let … in { tests }` (import-tree shape): peel to the body attrset and
        // keep the bindings as a `let … in ` prefix for each case (module docs).
        ast::Expr::LetIn(l) => {
            prelude.push_str(let_bindings_src(l, src)?);
            prelude.push(' '); // token range ends at `in`; keep it off the next token
            as_attrset(&l.body()?, src, prelude)
        }
        _ => None,
    }
}

/// The `let … in ` header of a `LetIn` as it appears in `src` — everything from
/// the `let` keyword up to and including `in` (so bindings and `inherit`s are
/// kept verbatim), ready to prefix a case side: `let <bindings> in <case>`.
fn let_bindings_src<'a>(l: &ast::LetIn, src: &'a str) -> Option<&'a str> {
    let start: usize = l.let_token()?.text_range().start().into();
    let end: usize = l.in_token()?.text_range().end().into();
    src.get(start..end)
}

/// The `(key, value-expr)` pairs of an attrset. `inherit` entries bind names,
/// not cases, so they are not returned here; when they appear in a top-level
/// `let … in`, those bindings are already captured in the prelude (so the names
/// they bring in stay in scope for every case).
fn entries(set: &ast::AttrSet) -> Result<Vec<(String, ast::Expr)>, NixError> {
    let mut pairs = Vec::new();
    for entry in set.entries() {
        if let ast::Entry::AttrpathValue(apv) = entry {
            let key = crate::parser::attrpath_value_name(&apv)?;
            let val = apv
                .value()
                .ok_or_else(|| NixError::UnsupportedSyntax("attr missing value".into()))?;
            pairs.push((key, val));
        }
    }
    Ok(pairs)
}

/// Look up a single attribute's value-expr within a set (None if absent).
fn lookup<'a>(pairs: &'a [(String, ast::Expr)], name: &str) -> Option<&'a ast::Expr> {
    pairs.iter().find(|(k, _)| k == name).map(|(_, v)| v)
}

/// Recursively collect cases: a set with `expr`+`expected` is a case at `prefix`;
/// any other nested set is a group whose name extends the dotted path. `prelude`
/// is the captured `let … in ` header so far (possibly empty); a group or case
/// value that is itself a `let … in` extends it for that subtree, so nested
/// bindings stay in scope for the cases beneath them.
fn walk(
    set: &ast::AttrSet,
    prefix: &str,
    prelude: &str,
    src: &str,
    out: &mut Vec<TestCase>,
) -> Result<(), NixError> {
    for (key, val) in entries(set)? {
        let path = if prefix.is_empty() {
            key.clone()
        } else {
            format!("{prefix}.{key}")
        };
        let mut child = prelude.to_string();
        let Some(inner) = as_attrset(&val, src, &mut child) else {
            continue;
        };
        let inner_pairs = entries(&inner)?;
        match (
            lookup(&inner_pairs, "expr"),
            lookup(&inner_pairs, "expected"),
        ) {
            (Some(e), Some(x)) => out.push(TestCase {
                path,
                expr: with_prelude(&child, e),
                expected: with_prelude(&child, x),
            }),
            _ => walk(&inner, &path, &child, src, out)?,
        }
    }
    Ok(())
}

/// Render a case side, prepending the captured `let … in ` bindings (if any) and
/// parenthesising the side so the `in` binds the whole expression. `prelude`
/// already ends in a separator space when non-empty.
fn with_prelude(prelude: &str, side: &ast::Expr) -> String {
    if prelude.is_empty() {
        side.to_string()
    } else {
        format!("{prelude}({side})")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flat_cases() {
        let cases = parse_test_suite(
            "{ testAdd = { expr = 1 + 2; expected = 3; }; \
               testStr = { expr = \"a\" + \"b\"; expected = \"ab\"; }; }",
        )
        .expect("parse");
        assert_eq!(cases.len(), 2);
        assert_eq!(cases[0].path, "testAdd");
        assert_eq!(cases[0].expr.trim(), "1 + 2");
        assert_eq!(cases[0].expected.trim(), "3");
        assert_eq!(cases[1].path, "testStr");
    }

    #[test]
    fn nested_groups_get_dotted_paths() {
        let cases =
            parse_test_suite("{ arithmetic = { testMul = { expr = 6 * 7; expected = 42; }; }; }")
                .expect("parse");
        assert_eq!(cases.len(), 1);
        assert_eq!(cases[0].path, "arithmetic.testMul");
        assert_eq!(cases[0].expr.trim(), "6 * 7");
    }

    #[test]
    fn non_case_attrs_are_skipped() {
        // A bare scalar attr (no expr/expected, not an attrset) is neither a case
        // nor a group → ignored, not an error.
        let cases =
            parse_test_suite("{ description = \"x\"; testT = { expr = 1; expected = 1; }; }")
                .expect("parse");
        assert_eq!(cases.len(), 1);
        assert_eq!(cases[0].path, "testT");
    }

    #[test]
    fn non_attrset_top_is_error() {
        assert!(parse_test_suite("1 + 2").is_err());
    }

    #[test]
    fn let_in_wrapper_prepends_bindings_to_each_side() {
        // import-tree's top level is `let lib;…; in { tests }`. Discovery peels
        // the `let` to reach the body attrset AND captures the bindings as a
        // prefix so each case side sees them (P0 #3: a case using a top binding
        // must not run with it unbound).
        let cases = parse_test_suite(
            "let base = 1; in { grp.\"test add\" = { expr = base + 1; expected = 2; }; }",
        )
        .expect("parse");
        assert_eq!(cases.len(), 1);
        assert_eq!(cases[0].path, "grp.test add");
        assert_eq!(cases[0].expr, "let base = 1; in (base + 1)");
        assert_eq!(cases[0].expected, "let base = 1; in (2)");
    }

    #[test]
    fn let_binding_is_in_scope_for_attr_access() {
        // The exact P0 #3 shape: a case selects from a top-level `let` binding.
        let cases =
            parse_test_suite("let lib = { f = 7; }; in { c = { expr = lib.f; expected = 7; }; }")
                .expect("parse");
        assert_eq!(cases.len(), 1);
        assert_eq!(cases[0].expr, "let lib = { f = 7; }; in (lib.f)");
    }

    #[test]
    fn top_level_inherit_is_captured_in_prelude() {
        // `inherit` in the top `let` must reach each case — it is part of the
        // captured `let … in ` header, not skipped.
        let cases = parse_test_suite(
            "let outer = 9; in let inherit outer; in { c = { expr = outer; expected = 9; }; }",
        )
        .expect("parse");
        assert_eq!(cases.len(), 1);
        assert!(
            cases[0].expr.contains("inherit outer;"),
            "inherit kept in prelude: {}",
            cases[0].expr
        );
        assert!(cases[0].expr.ends_with("(outer)"));
    }

    #[test]
    fn nested_let_extends_scope_for_subtree() {
        // A group whose value is itself a `let … in` extends the prelude for the
        // cases beneath it (both bindings in scope).
        let cases = parse_test_suite(
            "let a = 1; in { g = let b = 2; in { c = { expr = a + b; expected = 3; }; }; }",
        )
        .expect("parse");
        assert_eq!(cases.len(), 1);
        assert_eq!(cases[0].path, "g.c");
        assert_eq!(cases[0].expr, "let a = 1; in let b = 2; in (a + b)");
    }

    // ── computed-suite value walk (computed-suite-runner.md §2b) ──────────────

    fn attr(pairs: &[(&str, PrimValue)]) -> PrimValue {
        PrimValue::AttrSet(
            pairs
                .iter()
                .map(|(k, v)| ((*k).into(), v.clone()))
                .collect(),
        )
    }
    fn case(expr: PrimValue, expected: PrimValue) -> PrimValue {
        attr(&[("expr", expr), ("expected", expected)])
    }

    #[test]
    fn walk_value_flat_cases() {
        let tree = attr(&[
            ("a", case(PrimValue::Int(1), PrimValue::Int(1))),
            ("b", case(PrimValue::Bool(true), PrimValue::Bool(true))),
        ]);
        let mut out = Vec::new();
        walk_value(&tree, "", &mut out);
        assert_eq!(out.len(), 2);
        assert_eq!(out[0].path, "a");
        assert_eq!(out[0].expr, PrimValue::Int(1));
        assert_eq!(out[1].path, "b");
    }

    #[test]
    fn walk_value_nested_groups_get_dotted_paths() {
        let tree = attr(&[(
            "arithmetic",
            attr(&[("testMul", case(PrimValue::Int(42), PrimValue::Int(42)))]),
        )]);
        let mut out = Vec::new();
        walk_value(&tree, "", &mut out);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].path, "arithmetic.testMul");
    }

    #[test]
    fn walk_value_skips_non_case_attrs() {
        // A scalar attr, and an attrset missing `expected`, are neither case nor
        // group-with-cases → skipped, not an error (mirrors the AST walk).
        let tree = attr(&[
            ("description", PrimValue::Str("x".into())),
            ("partial", attr(&[("expr", PrimValue::Int(1))])),
            ("t", case(PrimValue::Int(1), PrimValue::Int(1))),
        ]);
        let mut out = Vec::new();
        walk_value(&tree, "", &mut out);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].path, "t");
    }

    #[test]
    fn walk_value_collection_leaf_is_a_case() {
        // A leaf whose sides are collections is a case (compared structurally),
        // not descended into — more capable than the text path (§3b).
        let list = PrimValue::List(vec![PrimValue::Int(1), PrimValue::Int(2)]);
        let tree = attr(&[("c", case(list.clone(), list))]);
        let mut out = Vec::new();
        walk_value(&tree, "", &mut out);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].path, "c");
        assert!(out[0].expr == out[0].expected);
    }

    #[test]
    fn discover_computed_reduces_application_top_level() {
        // The gate: a top level that is an APPLICATION (not a literal attrset)
        // reduces to a value tree and yields its cases — the literal path errors
        // on this with "tests file must be an attrset".
        let cases = discover_computed("(x: { c = { expr = x; expected = 7; }; }) 7").expect("eval");
        assert_eq!(cases.len(), 1);
        assert_eq!(cases[0].path, "c");
        assert_eq!(cases[0].expr, PrimValue::Int(7));
        assert_eq!(cases[0].expected, PrimValue::Int(7));
        // The same source is rejected by the literal parser.
        assert!(parse_test_suite("(x: { c = { expr = x; expected = 7; }; }) 7").is_err());
    }

    #[test]
    fn discover_computed_non_attrset_is_error() {
        assert!(discover_computed("1 + 2").is_err());
    }

    #[test]
    fn is_literal_attrset_classifies_top_level() {
        // Literal shapes the literal path accepts.
        assert!(is_literal_attrset("{ a = 1; }"));
        assert!(is_literal_attrset("({ a = 1; })"));
        assert!(is_literal_attrset("let x = 1; in { a = x; }"));
        // Computed shapes route to discover_computed.
        assert!(!is_literal_attrset("(x: { c = x; }) 1"));
        assert!(!is_literal_attrset(
            "builtins.mapAttrs (n: v: v) { a = 1; }"
        ));
        // A parse error stays on the literal path (clean ParseError there).
        assert!(is_literal_attrset("{ a = "));
    }
}
