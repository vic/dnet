//! Phase-1 on-disk CAS oracle (distribution-mvp-plan.md §C done-test):
//! store a canonical net to disk, drop the handle, reopen, load by hash →
//! the loaded net re-hashes to the SAME `net_hash`; a corrupted byte is
//! rejected on load (verify-on-read, §F.1-F.2). An absent key → `None`.

use std::sync::Arc;

use dnx_core::{
    canonical_hash, normalize, Blake3Hash, Canonical, DnxError, LOPath, Net, PortId, Proper, ΔL,
};
use dnx_dist::{CacheError, DiskCache};

const ROOT: &str = "res";

/// (λx.x) arg — one β-reduction, pure, ΔL (mirrors the cache oracle builder).
fn id_applied() -> Result<Net<Proper, ΔL>, DnxError> {
    let mut n = Net::<Proper, ΔL>::new(16);
    let abs = n.alloc_abs()?;
    let app = n.alloc_app()?;
    let arg = n.alloc_free(0)?;
    let res = n.alloc_free(1)?;
    n.connect(abs.aux0, abs.aux1, LOPath::root())?;
    n.connect(app.aux0, res, LOPath::root())?;
    n.connect(app.aux1, arg, LOPath::root())?;
    n.connect(abs.principal, app.principal, LOPath::root())?;
    n.add_root(Arc::from(ROOT), res);
    Ok(n)
}

fn norm() -> Result<(Net<Canonical, ΔL>, PortId), DnxError> {
    let (c, _) = normalize(id_applied()?)?;
    let root = *c.roots().get(ROOT).ok_or(DnxError::ReadbackIncomplete)?;
    Ok((c, root))
}

/// A throwaway unique directory under the OS temp dir (no `tempfile` dep).
fn scratch(tag: &str) -> std::path::PathBuf {
    let mut p = std::env::temp_dir();
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    p.push(format!("dnx-dist-{tag}-{}-{nanos}", std::process::id()));
    p
}

#[test]
fn store_reload_hash_equal() -> Result<(), CacheError> {
    let dir = scratch("rt");
    let (net, root) = norm()?;
    let want: Blake3Hash = canonical_hash(&net, root)?;

    // Store, then DROP the cache handle (simulating a process restart).
    let key = {
        let cache = DiskCache::open(&dir)?;
        let key = cache.store(&net, root)?;
        assert_eq!(key, want, "store key == content-address");
        assert!(cache.contains(&key), "stored blob must be present");
        key
    };

    // Reopen the dir fresh; load by hash; the loaded net re-hashes equal.
    let cache = DiskCache::open(&dir)?;
    let (back, back_root): (Net<Canonical, ΔL>, PortId) = cache
        .load(&key)?
        .ok_or(CacheError::Decode(DnxError::ReadbackIncomplete))?;
    assert_eq!(
        canonical_hash(&back, back_root)?,
        want,
        "reload must hash-equal"
    );

    let _ = std::fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn absent_key_is_none() -> Result<(), CacheError> {
    let dir = scratch("absent");
    let cache = DiskCache::open(&dir)?;
    let missing: Blake3Hash = [0u8; 32];
    assert!(!cache.contains(&missing));
    let got: Option<(Net<Canonical, ΔL>, PortId)> = cache.load(&missing)?;
    assert!(got.is_none(), "absent key must yield None, not error");
    let _ = std::fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn corrupt_blob_rejected_on_load() -> Result<(), CacheError> {
    let dir = scratch("corrupt");
    let (net, root) = norm()?;
    let cache = DiskCache::open(&dir)?;
    let key = cache.store(&net, root)?;

    // Flip a byte inside the stored blob file directly; load must reject.
    let blob_path = dir.join("blobs").join(hex(&key));
    let mut bytes = std::fs::read(&blob_path).map_err(CacheError::Io)?;
    let last = bytes.len() - 1;
    bytes[last] ^= 0xff;
    std::fs::write(&blob_path, &bytes).map_err(CacheError::Io)?;

    let r: Result<Option<(Net<Canonical, ΔL>, PortId)>, _> = cache.load(&key);
    assert!(r.is_err(), "a tampered blob must be rejected on load");

    let _ = std::fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn store_is_atomic_no_debris() -> Result<(), CacheError> {
    // Atomic write = temp-file + rename: after a store, the blobs dir holds
    // exactly the final content-addressed file (no leftover `.tmp`), and the
    // bytes are whole (load + re-hash succeeds). A re-store (overwrite) is an
    // atomic replace — still exactly one file, still valid. This is the
    // crash-safety property: a reader ever sees old-or-new, never a torn blob.
    let dir = scratch("atomic");
    let (net, root) = norm()?;
    let cache = DiskCache::open(&dir)?;

    let key = cache.store(&net, root)?;
    cache.store(&net, root)?; // overwrite via atomic rename

    let blobs = dir.join("blobs");
    let entries: Vec<_> = std::fs::read_dir(&blobs)
        .map_err(CacheError::Io)?
        .filter_map(Result::ok)
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .collect();
    assert_eq!(
        entries,
        vec![hex(&key)],
        "exactly the final blob, no .tmp debris"
    );

    // The stored blob is whole: it loads and re-hashes to its key.
    let (back, back_root): (Net<Canonical, ΔL>, PortId) = cache
        .load(&key)?
        .ok_or(CacheError::Decode(DnxError::ReadbackIncomplete))?;
    assert_eq!(
        canonical_hash(&back, back_root)?,
        key,
        "atomically-written blob is intact"
    );

    let _ = std::fs::remove_dir_all(&dir);
    Ok(())
}

/// Lower-case hex (mirrors the on-disk file-name scheme) for the corrupt test.
fn hex(hash: &Blake3Hash) -> String {
    const LUT: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(64);
    for &b in hash {
        s.push(LUT[(b >> 4) as usize] as char);
        s.push(LUT[(b & 0x0F) as usize] as char);
    }
    s
}
