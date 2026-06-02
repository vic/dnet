use dnx_drv::{from_attrs, Derivation};
use dnx_store::Store;
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

/// A throwaway store under the system temp dir, unique per call.
fn scratch_store() -> Store {
    static CTR: AtomicU64 = AtomicU64::new(0);
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("dnx-drv-test-{}-{}", std::process::id(), n));
    Store::open_at(dir).expect("open scratch store")
}

fn sh_echo_hi() -> Derivation {
    Derivation {
        name: Arc::from("hi"),
        builder: Arc::from("/bin/sh"),
        args: vec![Arc::from("-c"), Arc::from("echo -n hi > $out")],
        env: BTreeMap::new(),
        input_srcs: Vec::new(),
        outputs: vec![Arc::from("out")],
    }
}

#[test]
fn realize_produces_hi() {
    let store = scratch_store();
    let outs = sh_echo_hi().realize(&store).expect("realize");
    let out = outs.get("out").expect("out path");
    let bytes = store.get(out).expect("get").expect("present");
    assert_eq!(bytes, b"hi", "realised output content");
}

#[test]
fn instantiate_is_deterministic() {
    let store = scratch_store();
    let drv = sh_echo_hi();
    let a = drv.instantiate(&store).expect("instantiate a");
    let b = drv.instantiate(&store).expect("instantiate b");
    assert_eq!(a, b, "same derivation yields same drvPath");
    assert!(a.name().ends_with(".drv"));
}

#[test]
fn instantiate_differs_on_builder_change() {
    let store = scratch_store();
    let a = sh_echo_hi().instantiate(&store).expect("a");
    let mut other = sh_echo_hi();
    other.args = vec![Arc::from("-c"), Arc::from("echo -n bye > $out")];
    let b = other.instantiate(&store).expect("b");
    assert_ne!(a.hash(), b.hash(), "different drv → different drvPath");
}

#[test]
fn realize_failing_builder_errors() {
    let store = scratch_store();
    let drv = Derivation {
        name: Arc::from("boom"),
        builder: Arc::from("/bin/sh"),
        args: vec![Arc::from("-c"), Arc::from("exit 3")],
        env: BTreeMap::new(),
        input_srcs: Vec::new(),
        outputs: vec![Arc::from("out")],
    };
    assert!(drv.realize(&store).is_err(), "non-zero exit must error");
}

#[test]
fn realize_rejects_symlink_output() {
    use dnx_drv::DrvError;
    let store = scratch_store();
    // Give the builder the test runner's PATH so `ln` resolves on any host;
    // the builder then points $out at a host file. realize must reject the
    // symlink instead of capturing the linked-to bytes.
    let mut env = BTreeMap::new();
    if let Some(path) = std::env::var_os("PATH") {
        env.insert(
            Arc::from("PATH"),
            Arc::from(path.to_string_lossy().as_ref()),
        );
    }
    let drv = Derivation {
        name: Arc::from("evil"),
        builder: Arc::from("/bin/sh"),
        args: vec![Arc::from("-c"), Arc::from("ln -s /etc/hostname \"$out\"")],
        env,
        input_srcs: Vec::new(),
        outputs: vec![Arc::from("out")],
    };
    match drv.realize(&store) {
        Err(DrvError::OutputSymlink(_)) => {}
        other => panic!("expected OutputSymlink rejection, got {other:?}"),
    }
}

#[test]
fn realize_injects_fixed_base_path() {
    let store = scratch_store();
    // No PATH in env; builder dumps its own PATH. realize must supply a
    // fixed base PATH so builds do not depend on the host environment.
    let drv = Derivation {
        name: Arc::from("path"),
        builder: Arc::from("/bin/sh"),
        args: vec![Arc::from("-c"), Arc::from("printf %s \"$PATH\" > $out")],
        env: BTreeMap::new(),
        input_srcs: Vec::new(),
        outputs: vec![Arc::from("out")],
    };
    let outs = drv.realize(&store).expect("realize");
    let bytes = store
        .get(outs.get("out").expect("out"))
        .expect("get")
        .expect("present");
    assert_eq!(bytes, b"/usr/bin:/bin", "builder sees the fixed base PATH");
}

#[test]
fn instantiate_ignores_input_src_order() {
    let store = scratch_store();
    let a = store.add("a", b"alpha").expect("add a");
    let b = store.add("b", b"beta").expect("add b");
    let mut one = sh_echo_hi();
    one.input_srcs = vec![a.clone(), b.clone()];
    let mut two = sh_echo_hi();
    two.input_srcs = vec![b, a];
    let pa = one.instantiate(&store).expect("inst one");
    let pb = two.instantiate(&store).expect("inst two");
    assert_eq!(pa, pb, "input_srcs order must not change the drvPath");
}

#[test]
fn instantiate_differs_on_input_src_name() {
    // Two store paths with identical content (same hash) but different names
    // are distinct inputs, so a derivation depending on one must not collide
    // with one depending on the other. The drvPath is content-addressed by the
    // full description (dnx-demo-arch.md:168), which includes each input's name.
    let store = scratch_store();
    let same_bytes = b"shared";
    let a = store.add("alpha", same_bytes).expect("add alpha");
    let b = store.add("beta", same_bytes).expect("add beta");
    assert_eq!(a.hash(), b.hash(), "same content must hash equal");
    let mut one = sh_echo_hi();
    one.input_srcs = vec![a];
    let mut two = sh_echo_hi();
    two.input_srcs = vec![b];
    let pa = one.instantiate(&store).expect("inst one");
    let pb = two.instantiate(&store).expect("inst two");
    assert_ne!(
        pa.hash(),
        pb.hash(),
        "inputs differing only by name must yield different drvPaths"
    );
}

#[test]
fn realize_failure_leaves_no_temp_dir() {
    let store = scratch_store();
    let drv = Derivation {
        name: Arc::from("leakcheck"),
        builder: Arc::from("/bin/sh"),
        args: vec![Arc::from("-c"), Arc::from("exit 1")],
        env: BTreeMap::new(),
        input_srcs: Vec::new(),
        outputs: vec![Arc::from("out")],
    };
    let _ = drv.realize(&store);
    let leaked = std::fs::read_dir(std::env::temp_dir())
        .expect("read temp")
        .filter_map(Result::ok)
        .any(|e| {
            e.file_name().to_string_lossy().contains("dnx-build-")
                && e.file_name().to_string_lossy().contains("leakcheck")
        });
    assert!(!leaked, "a failing build must remove its temp dir");
}

#[test]
fn realize_builtin_write_emits_text() {
    // The deterministic, environment-independent builder: no external process,
    // no /bin/sh, no coreutils. `builder = "builtin:write"` copies the `text`
    // env var into every output, in-process. Works anywhere, needs no root.
    let store = scratch_store();
    let mut env = BTreeMap::new();
    env.insert(Arc::from("text"), Arc::from("hello dnx"));
    let drv = Derivation {
        name: Arc::from("greeting"),
        builder: Arc::from("builtin:write"),
        args: Vec::new(),
        env,
        input_srcs: Vec::new(),
        outputs: vec![Arc::from("out")],
    };
    let outs = drv.realize(&store).expect("realize builtin");
    let out = outs.get("out").expect("out path");
    let bytes = store.get(out).expect("get").expect("present");
    assert_eq!(bytes, b"hello dnx", "builtin:write copies `text` to $out");
}

#[test]
fn realize_builtin_write_is_deterministic() {
    // Same text → same content-addressed path, every time, no host dependence.
    let store = scratch_store();
    let mk = || {
        let mut env = BTreeMap::new();
        env.insert(Arc::from("text"), Arc::from("repeatable"));
        Derivation {
            name: Arc::from("det"),
            builder: Arc::from("builtin:write"),
            args: Vec::new(),
            env,
            input_srcs: Vec::new(),
            outputs: vec![Arc::from("out")],
        }
    };
    let a = mk().realize(&store).expect("a")["out"].clone();
    let b = mk().realize(&store).expect("b")["out"].clone();
    assert_eq!(a, b, "builtin:write output path is content-addressed");
}

#[test]
fn realize_builtin_write_requires_text() {
    // Missing `text` is a typed error, never a panic.
    use dnx_drv::DrvError;
    let store = scratch_store();
    let drv = Derivation {
        name: Arc::from("notext"),
        builder: Arc::from("builtin:write"),
        args: Vec::new(),
        env: BTreeMap::new(),
        input_srcs: Vec::new(),
        outputs: vec![Arc::from("out")],
    };
    match drv.realize(&store) {
        Err(DrvError::BadAttrs(_)) => {}
        other => panic!("expected BadAttrs for missing text, got {other:?}"),
    }
}

#[test]
fn realize_builtin_concat_joins_inputs() {
    // `builtin:concat` joins the byte contents of every `input_srcs` store
    // path, in the same canonical (hash, name) order `to_bytes` uses, into
    // each output. A pure builder: output is a function of input contents,
    // themselves content-addressed. No env, no process, no host dependence.
    let store = scratch_store();
    let a = store.add("a", b"foo").expect("add a");
    let b = store.add("b", b"bar").expect("add b");
    let drv = Derivation {
        name: Arc::from("joined"),
        builder: Arc::from("builtin:concat"),
        args: Vec::new(),
        env: BTreeMap::new(),
        input_srcs: vec![a, b],
        outputs: vec![Arc::from("out")],
    };
    let outs = drv.realize(&store).expect("realize concat");
    let out = outs.get("out").expect("out path");
    let bytes = store.get(out).expect("get").expect("present");
    // Order is canonical (hash, name)-sorted, not insertion order, so assert
    // against whichever of the two arrangements the input hashes dictate.
    assert!(
        bytes == b"foobar" || bytes == b"barfoo",
        "concat joins both inputs, got {bytes:?}"
    );
    assert_eq!(bytes.len(), 6, "concat is exactly the two inputs joined");
}

#[test]
fn realize_builtin_concat_is_order_canonical() {
    // The output is independent of input_srcs *insertion* order: two
    // derivations differing only in that order realise byte-identically,
    // because concat uses the same (hash, name) sort as the drvPath.
    let store = scratch_store();
    let a = store.add("a", b"foo").expect("add a");
    let b = store.add("b", b"bar").expect("add b");
    let mk = |srcs: Vec<dnx_store::StorePath>| Derivation {
        name: Arc::from("ord"),
        builder: Arc::from("builtin:concat"),
        args: Vec::new(),
        env: BTreeMap::new(),
        input_srcs: srcs,
        outputs: vec![Arc::from("out")],
    };
    let one = mk(vec![a.clone(), b.clone()]).realize(&store).expect("one")["out"].clone();
    let two = mk(vec![b, a]).realize(&store).expect("two")["out"].clone();
    assert_eq!(one, two, "concat output is independent of insertion order");
}

#[test]
fn realize_builtin_concat_empty_inputs_is_empty() {
    // No inputs → an empty (but present) output, never a panic.
    let store = scratch_store();
    let drv = Derivation {
        name: Arc::from("nada"),
        builder: Arc::from("builtin:concat"),
        args: Vec::new(),
        env: BTreeMap::new(),
        input_srcs: Vec::new(),
        outputs: vec![Arc::from("out")],
    };
    let outs = drv.realize(&store).expect("realize empty concat");
    let bytes = store
        .get(outs.get("out").expect("out"))
        .expect("get")
        .expect("present");
    assert!(bytes.is_empty(), "no inputs yields an empty output");
}

#[test]
fn realize_builtin_json_serializes_env() {
    // `builtin:json` writes the derivation's `env` as a canonical JSON object
    // to every output: sorted keys (the `BTreeMap` guarantees order), each
    // value a JSON string. Pure and in-process — no env beyond the attrs, no
    // external program, byte-identical on any host.
    let store = scratch_store();
    let mut env = BTreeMap::new();
    env.insert(Arc::from("b"), Arc::from("two"));
    env.insert(Arc::from("a"), Arc::from("one"));
    let drv = Derivation {
        name: Arc::from("cfg"),
        builder: Arc::from("builtin:json"),
        args: Vec::new(),
        env,
        input_srcs: Vec::new(),
        outputs: vec![Arc::from("out")],
    };
    let outs = drv.realize(&store).expect("realize json");
    let out = outs.get("out").expect("out path");
    let bytes = store.get(out).expect("get").expect("present");
    assert_eq!(
        bytes, br#"{"a":"one","b":"two"}"#,
        "builtin:json emits sorted-key JSON of env"
    );
}

#[test]
fn realize_builtin_json_escapes_and_handles_empty() {
    // Special characters are escaped per RFC 8259, and an empty env is the
    // empty JSON object — never a panic.
    let store = scratch_store();
    let empty = Derivation {
        name: Arc::from("empty"),
        builder: Arc::from("builtin:json"),
        args: Vec::new(),
        env: BTreeMap::new(),
        input_srcs: Vec::new(),
        outputs: vec![Arc::from("out")],
    };
    let outs = empty.realize(&store).expect("realize empty json");
    let bytes = store
        .get(outs.get("out").expect("out"))
        .expect("get")
        .expect("present");
    assert_eq!(bytes, b"{}", "no env yields the empty JSON object");

    let mut env = BTreeMap::new();
    env.insert(Arc::from("q"), Arc::from("a\"b\\c\n"));
    let esc = Derivation {
        name: Arc::from("esc"),
        builder: Arc::from("builtin:json"),
        args: Vec::new(),
        env,
        input_srcs: Vec::new(),
        outputs: vec![Arc::from("out")],
    };
    let outs = esc.realize(&store).expect("realize esc json");
    let bytes = store
        .get(outs.get("out").expect("out"))
        .expect("get")
        .expect("present");
    assert_eq!(
        bytes, br#"{"q":"a\"b\\c\n"}"#,
        "quote, backslash and newline are JSON-escaped"
    );
}

#[test]
fn realize_builtin_json_is_deterministic() {
    // Same env → same content-addressed path, every time, no host dependence.
    let store = scratch_store();
    let mk = || {
        let mut env = BTreeMap::new();
        env.insert(Arc::from("k"), Arc::from("v"));
        Derivation {
            name: Arc::from("detjson"),
            builder: Arc::from("builtin:json"),
            args: Vec::new(),
            env,
            input_srcs: Vec::new(),
            outputs: vec![Arc::from("out")],
        }
    };
    let a = mk().realize(&store).expect("a")["out"].clone();
    let b = mk().realize(&store).expect("b")["out"].clone();
    assert_eq!(a, b, "builtin:json output path is content-addressed");
}

#[test]
fn realize_rejects_unknown_builtin() {
    use dnx_drv::DrvError;
    let store = scratch_store();
    let drv = Derivation {
        name: Arc::from("bogus"),
        builder: Arc::from("builtin:nope"),
        args: Vec::new(),
        env: BTreeMap::new(),
        input_srcs: Vec::new(),
        outputs: vec![Arc::from("out")],
    };
    match drv.realize(&store) {
        Err(DrvError::UnknownBuiltin(n)) => assert_eq!(n.as_ref(), "nope"),
        other => panic!("expected UnknownBuiltin, got {other:?}"),
    }
}

#[test]
fn from_attrs_rejects_name_with_slash() {
    use dnx_core::prim::PrimValue;
    let attrs = vec![
        (Arc::from("name"), PrimValue::Str(Arc::from("../escape"))),
        (Arc::from("builder"), PrimValue::Str(Arc::from("/bin/sh"))),
    ];
    assert!(
        from_attrs(&attrs).is_err(),
        "a name that is not a single normal path component must be rejected"
    );
    let attrs2 = vec![
        (Arc::from("name"), PrimValue::Str(Arc::from("a/b"))),
        (Arc::from("builder"), PrimValue::Str(Arc::from("/bin/sh"))),
    ];
    assert!(
        from_attrs(&attrs2).is_err(),
        "a name with '/' must be rejected"
    );
}

#[test]
fn from_attrs_rejects_output_env_collision() {
    use dnx_core::prim::PrimValue;
    let attrs = vec![
        (Arc::from("name"), PrimValue::Str(Arc::from("clash"))),
        (Arc::from("builder"), PrimValue::Str(Arc::from("/bin/sh"))),
        (Arc::from("out"), PrimValue::Str(Arc::from("oops"))),
    ];
    assert!(
        from_attrs(&attrs).is_err(),
        "an output name colliding with an env key is ambiguous and must be rejected"
    );
}

#[test]
fn from_attrs_lifts_flat_attrset() {
    use dnx_core::prim::PrimValue;
    let attrs = vec![
        (Arc::from("name"), PrimValue::Str(Arc::from("hi"))),
        (Arc::from("builder"), PrimValue::Str(Arc::from("/bin/sh"))),
        (
            Arc::from("args"),
            PrimValue::List(vec![
                PrimValue::Str(Arc::from("-c")),
                PrimValue::Str(Arc::from("echo hi")),
            ]),
        ),
        (
            Arc::from("system"),
            PrimValue::Str(Arc::from("x86_64-linux")),
        ),
    ];
    let drv = from_attrs(&attrs).expect("from_attrs");
    assert_eq!(drv.name.as_ref(), "hi");
    assert_eq!(drv.builder.as_ref(), "/bin/sh");
    assert_eq!(drv.args.len(), 2);
    assert_eq!(drv.outputs, vec![Arc::from("out")]);
    assert_eq!(
        drv.env.get("system").map(|s| s.as_ref()),
        Some("x86_64-linux")
    );
}
