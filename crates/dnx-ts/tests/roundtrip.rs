//! Oracle for the tree-sitter JSON front-end spike: a JSON document parsed by
//! `tree-sitter-json`, lowered to the shared core `Ast`, and evaluated on the
//! Dnx engine. The decisive oracle (design §6.5) is *parity with the nix
//! front-end*: equivalent inputs must produce the identical `NixEvalResult`.
//!
//! Two facts surfaced by the spike, both confirmed against the nix front-end:
//!  1. A list literal (Scott-encoded) reads back as `Lambda`, not a
//!     `PrimValue::List` — exactly as a nix `[ 1 2 3 ]` does (dnx-pyparse
//!     tests/eval.rs:95).
//!  2. A multi-key attrset with a non-scalar value hits a *pre-existing*
//!     shared-engine bug in the `insert`-fold (`insert: first arg must be
//!     attrset`). It reproduces identically via the shipped nix front-end on
//!     `{ a = 1; b = [ 2 3 ]; }`, so it is an engine issue, not a mapper bug.
//!
//! The whole crate is behind the `tree-sitter` feature.
#![cfg(feature = "tree-sitter")]

use dnx_core::prim::PrimValue;
use dnx_lang::runtime::{NixEvalResult, NixRuntime};
use dnx_ts::TsRuntime;

fn ts(src: &str) -> NixEvalResult {
    TsRuntime::pure().eval(src)
}

fn nix(src: &str) -> NixEvalResult {
    NixRuntime::pure().eval(src)
}

/// `NixEvalResult` does not implement `Debug`, so name the variant for panics
/// (mirrors `dnx-pyparse` tests/eval.rs `tag`).
fn tag(r: &NixEvalResult) -> String {
    match r {
        NixEvalResult::Int(n) => format!("Int({n})"),
        NixEvalResult::Float(f) => format!("Float({f})"),
        NixEvalResult::Str(s) => format!("Str({s:?})"),
        NixEvalResult::Bool(b) => format!("Bool({b})"),
        NixEvalResult::Null => "Null".into(),
        NixEvalResult::List(_) => "List".into(),
        NixEvalResult::AttrSet(_) => "AttrSet".into(),
        NixEvalResult::Lambda(_) => "Lambda".into(),
        NixEvalResult::Error(e) => format!("Error({e:?})"),
    }
}

/// THE SPIKE ORACLE (Vic's case). `{"a":1,"b":[2,3]}` lowers via tree-sitter,
/// evaluates, and reads back *identically to the equivalent nix literal*. Both
/// front-ends currently hit the same pre-existing engine bug in the
/// multi-key/list-value `insert`-fold — proving the tree-sitter mapper drives
/// the engine with exact nix parity (the design §6.5 oracle), bug-for-bug.
#[test]
fn json_object_matches_nix_literal() {
    let from_json = ts(r#"{"a":1,"b":[2,3]}"#);
    let from_nix = nix("{ a = 1; b = [ 2 3 ]; }");
    assert_eq!(
        tag(&from_json),
        tag(&from_nix),
        "tree-sitter JSON must match the nix front-end for the equivalent literal"
    );
}

/// A purely-scalar object reads back as a real `PrimValue::AttrSet`, and matches
/// the nix front-end key-for-key.
#[test]
fn scalar_object_roundtrips() {
    let kvs = match ts(r#"{"a":1,"b":2}"#) {
        NixEvalResult::AttrSet(kvs) => kvs,
        other => panic!("expected AttrSet, got {}", tag(&other)),
    };
    assert_eq!(kvs.len(), 2, "two keys");
    let get = |name: &str| {
        kvs.iter()
            .find(|(k, _)| &**k == name)
            .map(|(_, v)| v.clone())
            .unwrap_or_else(|| panic!("key {name} present"))
    };
    assert_eq!(get("a"), PrimValue::Int(1));
    assert_eq!(get("b"), PrimValue::Int(2));

    // Same value as the equivalent nix literal.
    match nix("{ a = 1; b = 2; }") {
        NixEvalResult::AttrSet(n) => assert_eq!(n, kvs, "JSON object == nix attrset"),
        other => panic!("nix gave {}", tag(&other)),
    }
}

/// Scalars take the WHNF fast-path; a bare number reads back as `Int`.
#[test]
fn scalar_number() {
    assert!(matches!(ts("42"), NixEvalResult::Int(42)));
    assert!(matches!(ts("2.5"), NixEvalResult::Float(f) if f == 2.5));
    assert!(matches!(ts("true"), NixEvalResult::Bool(true)));
    assert!(matches!(ts("null"), NixEvalResult::Null));
    assert!(matches!(ts(r#""hi""#), NixEvalResult::Str(s) if &*s == "hi"));
}

/// A JSON array lowers to a Scott-encoded term, and the shared
/// `dnx_read::read_value` recognizer reconstructs it structurally — so it reads
/// back as the identical `List` value the equivalent nix list literal does
/// (mirrors dnx-pyparse tests/eval.rs `list_evaluates_like_nix`). One substrate,
/// two surface syntaxes.
#[test]
fn array_matches_nix_list() {
    match (ts("[1,2,3]"), nix("[ 1 2 3 ]")) {
        (NixEvalResult::List(j), NixEvalResult::List(n)) => assert_eq!(j, n, "same list"),
        (j, n) => panic!("JSON array {} vs nix list {}", tag(&j), tag(&n)),
    }
}

/// Heterogeneous arrays read back identically too: scalars of every JSON kind in
/// one list reconstruct to the same `List` on both front-ends.
#[test]
fn mixed_array_matches_nix_list() {
    match (ts("[1,2.5,true,null]"), nix("[ 1 2.5 true null ]")) {
        (NixEvalResult::List(j), NixEvalResult::List(n)) => assert_eq!(j, n, "same mixed list"),
        (j, n) => panic!("JSON array {} vs nix list {}", tag(&j), tag(&n)),
    }
}

/// String escapes decode correctly.
#[test]
fn string_escapes() {
    assert!(matches!(ts(r#""a\nb""#), NixEvalResult::Str(s) if &*s == "a\nb"));
    assert!(matches!(ts(r#""A""#), NixEvalResult::Str(s) if &*s == "A"));
}

/// Malformed JSON is a typed parse error, not a panic.
#[test]
fn malformed_is_error() {
    assert!(matches!(ts("{ not json"), NixEvalResult::Error(_)));
}

/// `comment` is a named node in `tree-sitter-json` (it lives in the grammar's
/// `extras`, grammar.js:16, and is materialized in the tree), so it appears as a
/// named child of `document`/`array`/`object`. Comments are non-semantic and
/// must be skipped, not rejected: JSON-with-comments evaluates to the value of
/// the JSON with the comments stripped.
#[test]
fn line_comment_at_top_level() {
    assert!(matches!(ts("// hi\n42"), NixEvalResult::Int(42)));
}

#[test]
fn block_comment_at_top_level() {
    assert!(matches!(ts("/* c */ 42"), NixEvalResult::Int(42)));
}

#[test]
fn comment_inside_object() {
    let kvs = match ts("{\n  // a key\n  \"a\": 1,\n  \"b\": 2 // trailing\n}") {
        NixEvalResult::AttrSet(kvs) => kvs,
        other => panic!("expected AttrSet, got {}", tag(&other)),
    };
    assert_eq!(kvs.len(), 2, "comments must not become keys");
    match nix("{ a = 1; b = 2; }") {
        NixEvalResult::AttrSet(n) => assert_eq!(n, kvs, "comments are whitespace"),
        other => panic!("nix gave {}", tag(&other)),
    }
}

#[test]
fn comment_inside_array() {
    assert_eq!(
        tag(&ts("[ /* one */ 1, 2 /* two */ ]")),
        tag(&ts("[1,2]")),
        "comments in arrays are skipped"
    );
}
