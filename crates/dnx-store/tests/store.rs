use dnx_store::{PathInfo, Store, StoreError, StorePath};
use std::path::PathBuf;
use std::sync::Arc;

/// A unique scratch dir under the system temp dir (no root, no deps).
fn scratch(tag: &str) -> PathBuf {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let dir = std::env::temp_dir().join(format!("dnx-store-test-{tag}-{nonce}"));
    let _ = std::fs::remove_dir_all(&dir);
    dir
}

#[test]
fn add_then_get_round_trips_identical_bytes() {
    let store = Store::open_at(scratch("rt")).expect("open");
    let bytes = b"hello dnx store".to_vec();
    let path = store.add("greeting", &bytes).expect("add");

    let got = store.get(&path).expect("get").expect("present");
    assert_eq!(got, bytes);
}

#[test]
fn same_content_yields_same_path() {
    let store = Store::open_at(scratch("dedup")).expect("open");
    let a = store.add("x", b"identical").expect("add a");
    let b = store.add("x", b"identical").expect("add b");
    assert_eq!(a, b, "CAS: identical content must dedup to one path");

    let diff = store.add("x", b"different").expect("add diff");
    assert_ne!(a.hash(), diff.hash(), "different content must differ");
}

#[test]
fn store_survives_reopen() {
    let dir = scratch("persist");
    let path = {
        let store = Store::open_at(&dir).expect("open 1");
        store.add("persisted", b"on disk").expect("add")
    };
    let reopened = Store::open_at(&dir).expect("open 2");
    assert!(reopened.has(&path), "path must survive reopen");
    let got = reopened.get(&path).expect("get").expect("present");
    assert_eq!(got, b"on disk");
}

#[test]
fn add_tree_round_trips_a_small_dir() {
    let src = scratch("tree-src");
    std::fs::create_dir_all(src.join("sub")).expect("mkdir");
    std::fs::write(src.join("a.txt"), b"alpha").expect("write a");
    std::fs::write(src.join("sub/b.txt"), b"beta").expect("write b");

    let store = Store::open_at(scratch("tree-store")).expect("open");
    let path = store.add_tree("pkg", &src).expect("add_tree");

    let landed = store.root().join(path.to_string());
    assert_eq!(
        std::fs::read(landed.join("a.txt")).expect("read a"),
        b"alpha"
    );
    assert_eq!(
        std::fs::read(landed.join("sub/b.txt")).expect("read b"),
        b"beta"
    );

    // Same tree content re-added → same path (deterministic tree hash).
    let again = store.add_tree("pkg", &src).expect("add_tree 2");
    assert_eq!(path, again);
}

#[test]
fn path_is_under_store_dir_with_temp_env_and_no_root() {
    let dir = scratch("env");
    std::env::set_var("DNX_STORE", &dir);
    let store = Store::open().expect("open via $DNX_STORE");
    std::env::remove_var("DNX_STORE");

    assert_eq!(store.root(), dir, "store root honours $DNX_STORE");
    let path = store.add("u", b"userland").expect("add");
    let on_disk = store.root().join(path.to_string());
    assert!(on_disk.starts_with(&dir), "blob lives under the store dir");
    assert!(on_disk.exists(), "no root needed to write the store");
}

#[test]
fn storepath_display_round_trips_through_parse() {
    let store = Store::open_at(scratch("parse")).expect("open");
    let path = store.add("with-dashes-ok", b"x").expect("add");
    let parsed = StorePath::parse(&path.to_string()).expect("parse");
    assert_eq!(path, parsed);
}

#[test]
fn concurrent_identical_add_both_succeed_no_torn_file() {
    let store = Arc::new(Store::open_at(scratch("race-add")).expect("open"));
    let bytes: &[u8] = b"the same content from two writers at once";

    // Many threads add identical content concurrently; the unique-staging +
    // atomic-rename CAS must let every writer succeed onto one intact final
    // file (no two writers share a staging slot, so none can truncate
    // another mid-write).
    let handles: Vec<_> = (0..8)
        .map(|_| {
            let store = Arc::clone(&store);
            std::thread::spawn(move || store.add("dup", bytes).expect("concurrent add"))
        })
        .collect();
    let paths: Vec<StorePath> = handles
        .into_iter()
        .map(|h| h.join().expect("join"))
        .collect();

    assert!(
        paths.windows(2).all(|w| w[0] == w[1]),
        "all dedup to one path"
    );
    // Store intact: the published bytes read back whole (no torn/partial file).
    let got = store.get(&paths[0]).expect("get").expect("present");
    assert_eq!(got, bytes, "final file is the full content, not torn");
    // No staging file leaked beside the final blob.
    assert!(
        !any_staging_left(store.root()),
        "no .tmp staging left behind"
    );
}

#[test]
fn add_tree_error_path_leaves_no_staging() {
    let dir = scratch("tree-err");
    let store = Store::open_at(&dir).expect("open");

    let src = scratch("tree-err-src");
    std::fs::create_dir_all(&src).expect("mkdir src");
    std::fs::write(src.join("f.txt"), b"data").expect("write f");

    // Make the store root read-only so staging-dir creation fails (EACCES).
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o555)).expect("chmod ro");

    let err = store.add_tree("pkg", &src);

    // Restore perms before asserting so the dir is always inspectable/cleanable.
    std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o755)).expect("chmod rw");

    assert!(
        matches!(err, Err(StoreError::Io(_))),
        "genuine io error surfaced"
    );
    assert!(
        !any_staging_left(store.root()),
        "error path left no .tmp-tree staging"
    );
}

#[test]
fn get_on_a_tree_path_is_typed_not_eisdir() {
    let src = scratch("get-tree-src");
    std::fs::create_dir_all(src.join("sub")).expect("mkdir");
    std::fs::write(src.join("a.txt"), b"alpha").expect("write a");

    let store = Store::open_at(scratch("get-tree")).expect("open");
    let tree = store.add_tree("pkg", &src).expect("add_tree");

    // get is blob-only: a tree path is a clean typed IsTree, never raw EISDIR.
    match store.get(&tree) {
        Err(StoreError::IsTree) => {}
        other => panic!("expected IsTree, got {other:?}"),
    }
}

#[test]
fn storepath_new_rejects_non_component_names() {
    let h = [0u8; 32];
    for bad in ["..", "a\\b", "a\0b", ".", "a/b", "/abs", ""] {
        assert!(
            matches!(StorePath::new(h, bad), Err(StoreError::BadName(_))),
            "name {bad:?} must be rejected as a non-single-component"
        );
    }
    // A plain dashed name still validates (keeps existing behaviour).
    assert!(StorePath::new(h, "with-dashes-ok").is_ok());
}

#[test]
fn has_hash_probes_by_hash_only() {
    let store = Store::open_at(scratch("has-hash")).expect("open");
    let path = store.add("greeting", b"hello").expect("add");

    // Present by hash alone — no name needed (the wire holds only a hash).
    assert!(store.has_hash(path.hash()).expect("has_hash present"));

    // A different hash is absent.
    let mut absent = *path.hash();
    absent[0] ^= 0xff;
    assert!(!store.has_hash(&absent).expect("has_hash absent"));
}

#[test]
fn ca_path_is_independent_of_store_root() {
    // The content-addressed name must depend ONLY on the bytes, never on which
    // custom root holds them. Two stores at different user-chosen roots must
    // mint the *same* StorePath for the same content (and a different one for
    // different content) — the core CAS guarantee across roots.
    let a = Store::open_at(scratch("ca-root-a")).expect("open a");
    let b = Store::open_at(scratch("ca-root-b")).expect("open b");
    assert_ne!(a.root(), b.root(), "two distinct custom roots");

    let pa = a.add("blob", b"deterministic").expect("add a");
    let pb = b.add("blob", b"deterministic").expect("add b");
    assert_eq!(pa, pb, "same content → same CA path regardless of root");

    let pc = b.add("blob", b"other-content").expect("add c");
    assert_ne!(pa, pc, "different content → different CA path");
}

#[test]
fn default_root_is_xdg_userland_never_nix() {
    // With $DNX_STORE unset, the store must root under the XDG userland default
    // ($HOME/.local/share/dnx/store) — a user-writable, no-root path that never
    // touches /nix (arch §2). We point $HOME at a temp dir so the test is
    // hermetic and actually writes there with no privileges.
    let fake_home = scratch("xdg-home");
    std::fs::create_dir_all(&fake_home).expect("mkdir fake home");
    let prev_home = std::env::var_os("HOME");
    let prev_store = std::env::var_os("DNX_STORE");
    std::env::remove_var("DNX_STORE");
    std::env::set_var("HOME", &fake_home);

    let store = Store::open();

    // Restore env before asserting so a failure can't poison other tests.
    match prev_home {
        Some(h) => std::env::set_var("HOME", h),
        None => std::env::remove_var("HOME"),
    }
    if let Some(s) = prev_store {
        std::env::set_var("DNX_STORE", s);
    }

    let store = store.expect("open via XDG default");
    let expected = fake_home
        .join(".local")
        .join("share")
        .join("dnx")
        .join("store");
    assert_eq!(store.root(), expected, "default root is XDG userland");
    assert!(
        !store.root().starts_with("/nix"),
        "default root never under /nix"
    );
    assert!(
        store.root().is_dir(),
        "default root created, no root needed"
    );
}

#[test]
fn stored_blob_is_owned_by_current_user_not_root() {
    // Rootless proof: a written blob is owned by the same unprivileged uid that
    // created the store dir (i.e. this process), never chowned to root (uid 0).
    // The store performs no privileged ownership change. We anchor "current
    // user" to the uid of the root dir this very test just created with no
    // privilege — a dep-free, non-circular reference.
    use std::os::unix::fs::MetadataExt;
    let root = scratch("ownership");
    let store = Store::open_at(&root).expect("open");
    let me = std::fs::metadata(&root).expect("stat root").uid();

    let path = store.add("owned", b"mine").expect("add");
    let on_disk = store.root().join(path.to_string());
    let owner = std::fs::metadata(&on_disk).expect("stat blob").uid();

    assert_eq!(owner, me, "blob owned by the unprivileged store creator");
    assert_ne!(owner, 0, "blob is not owned by root (no privilege used)");
}

#[test]
fn parse_rejects_traversal_and_separator_names() {
    // parse() must never reconstruct a path whose name segment could escape the
    // store dir. A crafted `<hex>-<name>` carrying `..`, a `/`, a `\`, or a NUL
    // in the name part is rejected — so a parsed StorePath is always one
    // well-formed component under the root.
    let hex = "0".repeat(HEX_LEN_TEST);
    for evil_name in ["..", "a/b", "..\\x", "a\0b", "/abs", "."] {
        let crafted = format!("{hex}-{evil_name}");
        assert!(
            matches!(StorePath::parse(&crafted), Err(StoreError::BadName(_))),
            "parse must reject traversal/separator name {evil_name:?}"
        );
    }
    // A benign dashed name still parses (no regression).
    let ok = format!("{hex}-fine-name");
    assert!(StorePath::parse(&ok).is_ok(), "benign name still parses");
}

#[test]
fn add_with_traversal_name_errors_and_writes_nothing_outside_root() {
    // Defence in depth at the `add` seam: a traversal name is rejected as
    // BadName *before* any byte hits disk, so nothing is ever written outside
    // the store root.
    let dir = scratch("add-traversal");
    let store = Store::open_at(&dir).expect("open");

    let err = store.add("../escape", b"payload");
    assert!(
        matches!(err, Err(StoreError::BadName(_))),
        "traversal name rejected as BadName, got {err:?}"
    );

    // The sibling path the name tried to escape to must not exist.
    let escaped = dir.parent().expect("scratch has a parent").join("escape");
    assert!(!escaped.exists(), "no byte written outside the store root");
    // And the store root holds no real blob (only possibly itself).
    let leaked = std::fs::read_dir(&dir)
        .expect("read root")
        .filter_map(|e| e.ok())
        .any(|e| !e.file_name().to_string_lossy().starts_with(".tmp"));
    assert!(!leaked, "no blob persisted on the reject path");
}

#[test]
fn add_raw_round_trips_a_replication_pull() {
    // The arch §8 push→pull headline: a source store builds an output; a peer,
    // given only (hash, name, bytes) over the wire, inserts it with add_raw and
    // reads back identical bytes — never rebuilding. Source and dest are two
    // distinct stores at different roots, exactly like two nodes.
    let source = Store::open_at(scratch("repl-src")).expect("open source");
    let dest = Store::open_at(scratch("repl-dst")).expect("open dest");

    let bytes = b"a built output to replicate".to_vec();
    let pushed = source.add("artifact", &bytes).expect("source add");

    // What crosses the wire: the content hash, the name, the bytes.
    let landed = dest
        .add_raw(*pushed.hash(), pushed.name(), &bytes)
        .expect("dest add_raw");

    // The peer minted the same content-addressed path and can read it back.
    assert_eq!(pushed, landed, "same CA path on both nodes");
    let got = dest.get(&landed).expect("dest get").expect("present");
    assert_eq!(got, bytes, "pulled bytes are byte-identical to the source");

    // Idempotent: pulling the same content again is a no-op, same path.
    let again = dest
        .add_raw(*pushed.hash(), pushed.name(), &bytes)
        .expect("second add_raw");
    assert_eq!(landed, again, "re-pull dedups to one path");
}

#[test]
fn add_raw_rejects_a_hash_that_does_not_match_the_bytes() {
    // A corrupt or lying transfer: the claimed hash disagrees with blake3(bytes).
    // add_raw must refuse with HashMismatch and write NOTHING — content-
    // addressing gives integrity for free, no byte lands under a wrong key.
    let dir = scratch("repl-bad");
    let dest = Store::open_at(&dir).expect("open");

    let honest = *blake3::hash(b"the real bytes").as_bytes();
    let mut lying = honest;
    lying[0] ^= 0xff; // a hash that the bytes do not produce

    let err = dest.add_raw(lying, "artifact", b"tampered bytes");
    assert!(
        matches!(err, Err(StoreError::HashMismatch)),
        "mismatched hash rejected as HashMismatch, got {err:?}"
    );

    // Nothing persisted: no blob under the lying key, no staging left.
    assert!(
        !dest.has_hash(&lying).expect("probe lying key"),
        "no blob written under the unmatched key"
    );
    assert!(
        !any_staging_left(dest.root()),
        "reject path left no staging file"
    );
}

#[test]
fn list_enumerates_every_published_path_and_skips_staging() {
    let store = Store::open_at(scratch("list")).expect("open");

    // Publish a mix of blobs and a tree — list must see all of them.
    let mut want: Vec<StorePath> = vec![
        store.add("one", b"first").expect("add one"),
        store.add("two", b"second").expect("add two"),
        store.add("three", b"third").expect("add three"),
    ];
    let src = scratch("list-tree-src");
    std::fs::create_dir_all(&src).expect("mkdir src");
    std::fs::write(src.join("a.txt"), b"alpha").expect("write a");
    want.push(store.add_tree("pkg", &src).expect("add_tree"));

    // A stray staging entry beside the real paths must NOT appear in the list.
    std::fs::write(store.root().join(".tmp-bogus"), b"junk").expect("write staging");

    let mut got = store.list().expect("list");
    got.sort_by_key(|p| p.to_string());
    want.sort_by_key(|p| p.to_string());
    assert_eq!(got, want, "list returns exactly the published paths");

    // Round-trip: every listed path resolves back to a present store entry.
    for p in &got {
        assert!(store.has(p), "listed path {p} is present on disk");
    }
}

#[test]
fn verify_holds_for_an_intact_blob() {
    // An untouched blob re-hashes to its key: verify is Ok(true).
    let store = Store::open_at(scratch("verify-blob-ok")).expect("open");
    let path = store.add("intact", b"sound bytes").expect("add");
    assert!(store.verify(&path).expect("verify"), "intact blob verifies");
}

#[test]
fn verify_is_false_for_an_absent_path() {
    // Absence is not corruption: a path that was never added verifies as
    // Ok(false) (mirrors `get`'s Ok(None)), never an error.
    let source = Store::open_at(scratch("verify-absent-src")).expect("open src");
    let empty = Store::open_at(scratch("verify-absent-dst")).expect("open dst");
    let path = source.add("ghost", b"only in source").expect("add");
    assert!(
        !empty.verify(&path).expect("verify absent"),
        "absent path verifies false, not error"
    );
}

#[test]
fn verify_detects_a_corrupted_blob() {
    // Tamper a published blob on disk; verify must catch the key/content
    // disagreement as HashMismatch — integrity for free (arch §8).
    let store = Store::open_at(scratch("verify-blob-bad")).expect("open");
    let path = store.add("victim", b"original content").expect("add");

    let on_disk = store.root().join(path.to_string());
    std::fs::write(&on_disk, b"silently swapped content").expect("tamper blob");

    match store.verify(&path) {
        Err(StoreError::HashMismatch) => {}
        other => panic!("expected HashMismatch on a tampered blob, got {other:?}"),
    }
}

#[test]
fn verify_holds_for_an_intact_tree() {
    // A tree re-derives the same deterministic hash from disk: Ok(true).
    let src = scratch("verify-tree-ok-src");
    std::fs::create_dir_all(src.join("sub")).expect("mkdir");
    std::fs::write(src.join("a.txt"), b"alpha").expect("write a");
    std::fs::write(src.join("sub/b.txt"), b"beta").expect("write b");

    let store = Store::open_at(scratch("verify-tree-ok")).expect("open");
    let path = store.add_tree("pkg", &src).expect("add_tree");
    assert!(store.verify(&path).expect("verify"), "intact tree verifies");
}

#[test]
fn verify_detects_a_corrupted_tree() {
    // Tamper one file inside a published tree; the re-derived tree hash no
    // longer matches the key — HashMismatch. This is the only path that
    // re-checks tree integrity post-write (add_tree alone never re-verifies).
    let src = scratch("verify-tree-bad-src");
    std::fs::create_dir_all(src.join("sub")).expect("mkdir");
    std::fs::write(src.join("a.txt"), b"alpha").expect("write a");
    std::fs::write(src.join("sub/b.txt"), b"beta").expect("write b");

    let store = Store::open_at(scratch("verify-tree-bad")).expect("open");
    let path = store.add_tree("pkg", &src).expect("add_tree");

    let landed = store.root().join(path.to_string());
    std::fs::write(landed.join("sub/b.txt"), b"gamma").expect("tamper file in tree");

    match store.verify(&path) {
        Err(StoreError::HashMismatch) => {}
        other => panic!("expected HashMismatch on a tampered tree, got {other:?}"),
    }
}

/// Hex width of a BLAKE3 key in a `<hex>-<name>` filename (mirrors the
/// crate-internal `HEX_LEN`; kept local so the test stays black-box).
const HEX_LEN_TEST: usize = 64;

/// True if any `.tmp` staging entry remains in the store root.
fn any_staging_left(root: &std::path::Path) -> bool {
    std::fs::read_dir(root)
        .expect("read store root")
        .filter_map(|e| e.ok())
        .any(|e| e.file_name().to_string_lossy().starts_with(".tmp"))
}

#[test]
fn query_path_info_round_trips_a_blob() {
    // A freshly added blob reports its byte length, a blob (not a tree), and a
    // hash re-derived from disk that equals the key the path claims.
    let store = Store::open_at(scratch("info-blob")).expect("open");
    let bytes = b"size matters".to_vec();
    let path = store.add("blob", &bytes).expect("add");

    let info = store
        .query_path_info(&path)
        .expect("query")
        .expect("present");
    assert_eq!(
        info,
        PathInfo {
            size: bytes.len() as u64,
            is_tree: false,
            hash: *path.hash(),
        },
        "blob info: length, is_tree=false, disk hash == key"
    );
}

#[test]
fn query_path_info_round_trips_a_tree() {
    // A published tree reports is_tree=true, the deterministic disk hash (==
    // key), and a size equal to the sum of its entry contents.
    let src = scratch("info-tree-src");
    std::fs::create_dir_all(src.join("sub")).expect("mkdir");
    std::fs::write(src.join("a.txt"), b"alpha").expect("write a");
    std::fs::write(src.join("sub/b.txt"), b"beta").expect("write b");

    let store = Store::open_at(scratch("info-tree")).expect("open");
    let path = store.add_tree("pkg", &src).expect("add_tree");

    let info = store
        .query_path_info(&path)
        .expect("query")
        .expect("present");
    assert_eq!(
        info,
        PathInfo {
            size: (b"alpha".len() + b"beta".len()) as u64,
            is_tree: true,
            hash: *path.hash(),
        },
        "tree info: is_tree=true, summed size, disk hash == key"
    );
}

#[test]
fn query_path_info_is_none_for_an_absent_path() {
    // Absence is not an error: a never-added path queries Ok(None), mirroring
    // get's Ok(None) and verify's Ok(false).
    let source = Store::open_at(scratch("info-absent-src")).expect("open src");
    let empty = Store::open_at(scratch("info-absent-dst")).expect("open dst");
    let path = source.add("ghost", b"only in source").expect("add");
    assert_eq!(
        empty.query_path_info(&path).expect("query absent"),
        None,
        "absent path queries None, not error"
    );
}
