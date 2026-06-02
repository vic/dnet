//! Lower a `tree-sitter-json` CST to the shared core `Ast<NixPrimVal,
//! NixPrimFun>` — the exact IR `dnx-lang`/`dnx-pyparse` produce. The
//! mapper is the direct analog of `translate_expr` (dnx-lang parser/mod.rs)
//! and `lower_expr` (dnx-pyparse lower.rs): a `match node.kind()` dispatch over
//! the grammar's named node kinds. JSON has no binders, so the variable-
//! multiplicity machinery (rep/era/use-count) the other front-ends carry is not
//! needed here — only literals, `Insert`-fold objects, and `cons`/`nil`-fold
//! arrays. Node kinds + the `pair` `key`/`value` field names are from
//! `tree-sitter-json`'s `node-types.json`.

use crate::error::TsError;
use dnx_ast::Ast;
use dnx_lang::prim::{NixPrimFun, NixPrimVal};
use std::sync::Arc;
use tree_sitter::Node;

/// The shared core expression type (identical to `dnx-lang`'s `E`).
type E = Ast<NixPrimVal, NixPrimFun>;

/// `comment` is a named node `tree-sitter-json` emits for `extras` (grammar.js
/// `extras: [$.comment]`): it can appear anywhere whitespace can. Comments carry
/// no value, so every named-child walk skips them rather than rejecting them.
fn is_comment(node: Node<'_>) -> bool {
    node.kind() == "comment"
}

/// Lower a parsed JSON `document` node to one core expression. The document's
/// sole value child may be preceded/followed by `comment` extras; pick the first
/// non-comment named child.
pub(crate) fn lower_document(node: Node<'_>, src: &str) -> Result<E, TsError> {
    if node.kind() != "document" {
        return Err(TsError::Unsupported(format!("root is {}", node.kind())));
    }
    let mut cursor = node.walk();
    let child = node
        .named_children(&mut cursor)
        .find(|n| !is_comment(*n))
        .ok_or_else(|| TsError::Parse("empty JSON document".into()))?;
    lower_value(child, src)
}

/// Lower any JSON value node. The dispatch key is `node.kind()` (a `&str`,
/// unlike rnix's typed enum) — the only structural difference from the nix path.
fn lower_value(node: Node<'_>, src: &str) -> Result<E, TsError> {
    match node.kind() {
        "object" => lower_object(node, src),
        "array" => lower_array(node, src),
        "string" => Ok(Ast::Val(NixPrimVal::Str(parse_string(node, src)?))),
        "number" => lower_number(node, src),
        "true" => Ok(Ast::Val(NixPrimVal::Bool(true))),
        "false" => Ok(Ast::Val(NixPrimVal::Bool(false))),
        "null" => Ok(Ast::Val(NixPrimVal::Null)),
        other => Err(TsError::Unsupported(other.to_string())),
    }
}

/// `{ "k": v, … }` → fold `Insert set "k" v` over `EmptyAttrSet`, the same shape
/// the nix and python front-ends use (dnx-pyparse lower.rs `lower_attrset`), so
/// the resulting `PrimValue::AttrSet` is identical given identical keys/values.
fn lower_object(node: Node<'_>, src: &str) -> Result<E, TsError> {
    let mut set: E = Ast::Fun(NixPrimFun::EmptyAttrSet);
    let mut cursor = node.walk();
    for pair in node.named_children(&mut cursor) {
        if is_comment(pair) {
            continue;
        }
        if pair.kind() != "pair" {
            return Err(TsError::Unsupported(format!(
                "object child {}",
                pair.kind()
            )));
        }
        let key_node = pair
            .child_by_field_name("key")
            .ok_or_else(|| TsError::Parse("pair without key".into()))?;
        let val_node = pair
            .child_by_field_name("value")
            .ok_or_else(|| TsError::Parse("pair without value".into()))?;
        let key = parse_string(key_node, src)?;
        let v = lower_value(val_node, src)?;
        set = Ast::App(
            Box::new(app2(
                Ast::Fun(NixPrimFun::Insert),
                set,
                Ast::Val(NixPrimVal::Str(key)),
            )),
            Box::new(v),
        );
    }
    Ok(set)
}

/// `[ a, b, … ]` → fold-right into Scott `cons h (… nil)`, reusing the same
/// prelude names the nix list path uses (dnx-pyparse lower.rs `lower_list`).
fn lower_array(node: Node<'_>, src: &str) -> Result<E, TsError> {
    let mut cursor = node.walk();
    let items: Vec<Node<'_>> = node
        .named_children(&mut cursor)
        .filter(|n| !is_comment(*n))
        .collect();
    let mut acc: E = Ast::Name(Arc::from("nil"));
    for item in items.into_iter().rev() {
        let h = lower_value(item, src)?;
        acc = app2(Ast::Name(Arc::from("cons")), h, acc);
    }
    Ok(acc)
}

/// A JSON `number` is an `Int` when it parses as `i64` with no fractional or
/// exponent part, else a `Float` (the two `NixPrimVal` numeric kinds).
fn lower_number(node: Node<'_>, src: &str) -> Result<E, TsError> {
    let text = node_text(node, src)?;
    let is_int = !text.contains(['.', 'e', 'E']);
    if is_int {
        if let Ok(n) = text.parse::<i64>() {
            return Ok(Ast::Val(NixPrimVal::Int(n)));
        }
    }
    text.parse::<f64>()
        .map(|f| Ast::Val(NixPrimVal::Float(f)))
        .map_err(|_| TsError::Parse(format!("invalid number {text:?}")))
}

/// Slice a node's source text by its byte range (UTF-8 safe).
fn node_text<'a>(node: Node<'_>, src: &'a str) -> Result<&'a str, TsError> {
    src.get(node.byte_range())
        .ok_or_else(|| TsError::Parse("node byte range out of source bounds".into()))
}

/// Decode a JSON `string` node to its content. The node span includes the
/// surrounding quotes (tree-sitter-json `node-types.json`); strip them and
/// decode the standard JSON escapes.
fn parse_string(node: Node<'_>, src: &str) -> Result<Arc<str>, TsError> {
    let raw = node_text(node, src)?;
    let inner = raw
        .strip_prefix('"')
        .and_then(|s| s.strip_suffix('"'))
        .ok_or_else(|| TsError::Parse(format!("string not quoted: {raw:?}")))?;
    decode_escapes(inner)
}

/// Decode JSON string escapes (`\" \\ \/ \n \t \r \b \f \uXXXX`). A lone `\`
/// or unknown escape is a parse error rather than a silent pass-through.
fn decode_escapes(s: &str) -> Result<Arc<str>, TsError> {
    if !s.contains('\\') {
        return Ok(Arc::from(s));
    }
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        let esc = chars
            .next()
            .ok_or_else(|| TsError::Parse("trailing backslash in string".into()))?;
        match esc {
            '"' => out.push('"'),
            '\\' => out.push('\\'),
            '/' => out.push('/'),
            'n' => out.push('\n'),
            't' => out.push('\t'),
            'r' => out.push('\r'),
            'b' => out.push('\u{0008}'),
            'f' => out.push('\u{000C}'),
            'u' => out.push(decode_unicode_escape(&mut chars)?),
            other => return Err(TsError::Parse(format!("unknown escape \\{other}"))),
        }
    }
    Ok(Arc::from(out.as_str()))
}

/// Decode the four hex digits following `\u` into a `char`. Surrogate halves and
/// non-scalar values are rejected (a designed limit, not silent corruption).
fn decode_unicode_escape(chars: &mut std::str::Chars<'_>) -> Result<char, TsError> {
    let mut code: u32 = 0;
    for _ in 0..4 {
        let d = chars
            .next()
            .ok_or_else(|| TsError::Parse("short \\u escape".into()))?;
        let v = d
            .to_digit(16)
            .ok_or_else(|| TsError::Parse(format!("bad hex digit {d:?} in \\u escape")))?;
        code = code * 16 + v;
    }
    char::from_u32(code)
        .ok_or_else(|| TsError::Parse(format!("\\u{code:04X} is not a scalar value")))
}

fn app2(f: E, a: E, b: E) -> E {
    Ast::App(Box::new(Ast::App(Box::new(f), Box::new(a))), Box::new(b))
}
