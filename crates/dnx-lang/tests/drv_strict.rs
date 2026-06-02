use dnx_core::prim::PrimValue;
use dnx_lang::runtime::{NixEvalResult, NixRuntime};

fn eval(src: &str) -> NixEvalResult {
    NixRuntime::pure().eval(src)
}

fn get<'a>(kvs: &'a [(std::sync::Arc<str>, PrimValue)], k: &str) -> Option<&'a PrimValue> {
    kvs.iter()
        .find(|(key, _)| key.as_ref() == k)
        .map(|(_, v)| v)
}

#[test]
fn derivation_strict_returns_drv_attrset() {
    match eval(r#"derivationStrict { name = "hi"; builder = "/bin/sh"; system = "x86_64-linux"; }"#)
    {
        NixEvalResult::AttrSet(kvs) => {
            assert!(
                matches!(get(&kvs, "type"), Some(PrimValue::Str(s)) if s.as_ref() == "derivation"),
                "marked as derivation"
            );
            assert!(matches!(get(&kvs, "name"), Some(PrimValue::Str(s)) if s.as_ref() == "hi"));
            assert!(
                matches!(get(&kvs, "builder"), Some(PrimValue::Str(s)) if s.as_ref() == "/bin/sh")
            );
        }
        NixEvalResult::Error(e) => panic!("derivationStrict error: {e:?}"),
        _ => panic!("expected attrset"),
    }
}

#[test]
fn derivation_wrapper_matches_derivation_strict() {
    // `derivation { … }` (no list) must lower to the same drv attrset as
    // `derivationStrict { … }` — same attrs ⇒ same to_bytes ⇒ same drvPath.
    // (List `args` is TASK1-blocked, so the no-list case is the oracle.)
    let drv = r#"derivation { name = "x"; builder = "/bin/sh"; system = "x86_64-linux"; }"#;
    let strict =
        r#"derivationStrict { name = "x"; builder = "/bin/sh"; system = "x86_64-linux"; }"#;
    match (eval(drv), eval(strict)) {
        (NixEvalResult::AttrSet(a), NixEvalResult::AttrSet(b)) => assert_eq!(a, b),
        (NixEvalResult::Error(e), _) => panic!("derivation wrapper error: {e:?}"),
        (a, b) => panic!("expected attrsets, got {} / {}", tag(&a), tag(&b)),
    }
}

#[test]
fn derivation_strict_missing_builder_errors() {
    match eval(r#"derivationStrict { name = "hi"; }"#) {
        NixEvalResult::Error(_) => {}
        other => panic!("expected error for missing builder, got {}", tag(&other)),
    }
}

#[test]
fn derivation_strict_field_select() {
    // The drv attrset is selectable like any attrset.
    match eval(r#"(derivationStrict { name = "hi"; builder = "/bin/sh"; }).name"#) {
        NixEvalResult::Str(s) if s.as_ref() == "hi" => {}
        other => panic!("expected \"hi\", got {}", tag(&other)),
    }
}

fn tag(r: &NixEvalResult) -> &'static str {
    match r {
        NixEvalResult::Int(_) => "int",
        NixEvalResult::Float(_) => "float",
        NixEvalResult::Str(_) => "str",
        NixEvalResult::Bool(_) => "bool",
        NixEvalResult::Null => "null",
        NixEvalResult::List(_) => "list",
        NixEvalResult::AttrSet(_) => "set",
        NixEvalResult::Lambda(_) => "lambda",
        NixEvalResult::Error(_) => "error",
    }
}
