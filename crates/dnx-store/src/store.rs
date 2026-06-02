use crate::error::StoreError;
use crate::path::StorePath;
use dnx_core::Blake3Hash;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

/// A userland content-addressed store rooted at a single directory.
///
/// Never touches `/nix` and needs no root. Keys are BLAKE3 (our semantics),
/// laid out as `<root>/<hex(hash)>-<name>`.
pub struct Store {
    root: PathBuf,
}

/// What a store path resolves to on disk, re-derived from the bytes (never the
/// claimed key) so it reports the truth content-addressing buys for free
/// (arch §8): `hash` is `blake3(blob)` or the deterministic tree digest of what
/// is actually stored, `size` the logical content-byte count that digest folds
/// over, and `is_tree` distinguishes a stored directory from a blob. No
/// inter-field invariant exists, so the fields are read-only data, not a state
/// machine. A path whose on-disk content has been tampered re-derives to a key
/// that no longer matches — querying never reports a stale claim.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PathInfo {
    /// Total logical content bytes: a blob's length, or the sum of a tree's
    /// entry data lengths (the bytes its deterministic hash folds over).
    pub size: u64,
    /// `true` if the path resolves to a stored directory tree, `false` for a
    /// blob.
    pub is_tree: bool,
    /// The content hash re-derived from what is on disk right now.
    pub hash: Blake3Hash,
}

impl Store {
    /// Open (creating if absent) the store at `$DNX_STORE`, else the XDG
    /// default `$HOME/.local/share/dnx/store`.
    pub fn open() -> Result<Self, StoreError> {
        let root = match std::env::var_os("DNX_STORE") {
            Some(dir) => PathBuf::from(dir),
            None => default_root()?,
        };
        Store::open_at(root)
    }

    /// Open (creating if absent) the store at an explicit directory.
    pub fn open_at(root: impl Into<PathBuf>) -> Result<Self, StoreError> {
        let root = root.into();
        fs::create_dir_all(&root)?;
        Ok(Store { root })
    }

    /// The store's root directory.
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Add a blob. Keyed by `blake3(bytes)`; write-once and idempotent —
    /// re-adding identical content is a no-op and yields the same path.
    pub fn add(&self, name: &str, bytes: &[u8]) -> Result<StorePath, StoreError> {
        self.add_raw(*blake3::hash(bytes).as_bytes(), name, bytes)
    }

    /// Insert bytes that arrived already content-addressed — a replication
    /// pull (arch §8): a peer hands us the claimed `hash`, the `name`, and the
    /// `bytes`. We re-derive `blake3(bytes)` and refuse the insert unless it
    /// equals `hash` (`HashMismatch`), so a corrupt or lying transfer can never
    /// land under a key it does not hash to — integrity is free from
    /// content-addressing, no signing needed. The `name` is carried over the
    /// wire to preserve the `<hex>-<name>` layout (arch §2). Write-once and
    /// idempotent, exactly like `add`.
    pub fn add_raw(
        &self,
        hash: Blake3Hash,
        name: &str,
        bytes: &[u8],
    ) -> Result<StorePath, StoreError> {
        if blake3::hash(bytes).as_bytes() != &hash {
            return Err(StoreError::HashMismatch);
        }
        let path = StorePath::new(hash, name)?;
        let target = self.locate(&path);
        if !target.exists() {
            write_atomic(&self.root, &target, bytes)?;
        }
        Ok(path)
    }

    /// Add a directory tree as one store path. Keyed by a deterministic
    /// BLAKE3 over its sorted `(relpath, bytes)` entries. Write-once.
    pub fn add_tree(&self, name: &str, dir: &Path) -> Result<StorePath, StoreError> {
        let contents = tree_contents(dir)?;
        let path = StorePath::new(hash_contents(&contents), name)?;

        let target = self.locate(&path);
        if !target.exists() {
            // Per-writer-unique staging dir: concurrent identical-tree adds
            // never collide, so no writer's `remove_dir_all` can wipe
            // another's in-flight tree.
            let staging = unique_staging(&self.root, ".tmp-tree");
            stage_tree(&staging, &contents)?;
            match fs::rename(&staging, &target) {
                Ok(()) => {}
                // A racer already published the identical tree; drop ours.
                Err(_) if target.exists() => {
                    let _ = fs::remove_dir_all(&staging);
                }
                // Genuine failure: never leak the staging dir.
                Err(e) => {
                    let _ = fs::remove_dir_all(&staging);
                    return Err(StoreError::Io(e));
                }
            }
        }
        Ok(path)
    }

    /// Read a blob back. `Ok(None)` if absent; `Err` only on a real I/O
    /// failure (absence is not an error). Blob-only by design (arch §2): a
    /// path that resolves to a stored tree yields `Err(StoreError::IsTree)`
    /// rather than a spurious EISDIR.
    pub fn get(&self, path: &StorePath) -> Result<Option<Vec<u8>>, StoreError> {
        let on_disk = self.locate(path);
        if on_disk.is_dir() {
            return Err(StoreError::IsTree);
        }
        match fs::read(&on_disk) {
            Ok(bytes) => {
                if blake3::hash(&bytes).as_bytes() != path.hash() {
                    return Err(StoreError::HashMismatch);
                }
                Ok(Some(bytes))
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(e) => Err(StoreError::Io(e)),
        }
    }

    /// Whether a store path is present (the cache-hit check).
    pub fn has(&self, path: &StorePath) -> bool {
        self.locate(path).exists()
    }

    /// Whether ANY blob keyed by `hash` is present, ignoring its name — the
    /// hash-only membership probe a content-addressed peer needs (it holds a
    /// `Blake3Hash`, not the original `<hex>-<name>`). On-disk names are
    /// `<hex>-<name>` (`StorePath::Display`), so this scans the root for one
    /// entry whose hex prefix matches. `Err` only on a real I/O failure.
    pub fn has_hash(&self, hash: &Blake3Hash) -> Result<bool, StoreError> {
        const LUT: &[u8; 16] = b"0123456789abcdef";
        let mut prefix = String::with_capacity(65);
        for &b in hash {
            prefix.push(LUT[(b >> 4) as usize] as char);
            prefix.push(LUT[(b & 0x0F) as usize] as char);
        }
        prefix.push('-');
        for entry in fs::read_dir(&self.root)? {
            let entry = entry?;
            if entry.file_name().to_string_lossy().starts_with(&prefix) {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Enumerate every published store path (blobs and trees alike share the
    /// `<hex>-<name>` layout, arch §2). In-flight `.tmp-*` staging entries are
    /// not store paths and are skipped; every published name round-trips
    /// through `StorePath::parse`, so a name that fails to parse is a foreign
    /// intruder in the root and surfaces as `BadName` rather than being
    /// silently dropped. `Err` only on a real I/O failure.
    pub fn list(&self) -> Result<Vec<StorePath>, StoreError> {
        let mut paths = Vec::new();
        for entry in fs::read_dir(&self.root)? {
            let name = entry?.file_name();
            let name = name.to_string_lossy();
            if name.starts_with(".tmp") {
                continue;
            }
            paths.push(StorePath::parse(&name)?);
        }
        Ok(paths)
    }

    /// Re-derive the content hash of what is on disk and check it against the
    /// key the path claims — the integrity re-check content-addressing buys for
    /// free (arch §8). `Ok(true)` if present and the bytes (blob) or the
    /// deterministic tree hash (tree) match the key; `Ok(false)` if absent
    /// (absence is not corruption, mirroring `get`); `Err(HashMismatch)` if
    /// present but the on-disk content no longer hashes to the key; `Err(Io)`
    /// on a real I/O failure. For trees this is the only post-write integrity
    /// check — `add_tree` itself never re-verifies a published tree.
    pub fn verify(&self, path: &StorePath) -> Result<bool, StoreError> {
        let on_disk = self.locate(path);
        if on_disk.is_dir() {
            return match hash_contents(&tree_contents(&on_disk)?) == *path.hash() {
                true => Ok(true),
                false => Err(StoreError::HashMismatch),
            };
        }
        match fs::read(&on_disk) {
            Ok(bytes) if blake3::hash(&bytes).as_bytes() == path.hash() => Ok(true),
            Ok(_) => Err(StoreError::HashMismatch),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(false),
            Err(e) => Err(StoreError::Io(e)),
        }
    }

    /// Report what a store path resolves to without reading content over any
    /// wire — the net-less metadata probe a peer or a cache makes before
    /// pulling. `Ok(None)` if absent (mirrors `get`/`verify`: absence is not an
    /// error); `Ok(Some(info))` with `size`/`is_tree`/`hash` re-derived from the
    /// bytes on disk (so the reported `hash` is the disk's true digest, like
    /// `verify`, not the key the path merely claims); `Err(Io)` on a real I/O
    /// failure. Shares `tree_contents`/`hash_contents` with `add_tree`/`verify`,
    /// so the three can never disagree on a tree's size or hash.
    pub fn query_path_info(&self, path: &StorePath) -> Result<Option<PathInfo>, StoreError> {
        let on_disk = self.locate(path);
        if on_disk.is_dir() {
            let contents = tree_contents(&on_disk)?;
            let size = contents.iter().map(|(_, data)| data.len() as u64).sum();
            return Ok(Some(PathInfo {
                size,
                is_tree: true,
                hash: hash_contents(&contents),
            }));
        }
        match fs::read(&on_disk) {
            Ok(bytes) => Ok(Some(PathInfo {
                size: bytes.len() as u64,
                is_tree: false,
                hash: *blake3::hash(&bytes).as_bytes(),
            })),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(e) => Err(StoreError::Io(e)),
        }
    }

    fn locate(&self, path: &StorePath) -> PathBuf {
        self.root.join(path.to_string())
    }
}

fn default_root() -> Result<PathBuf, StoreError> {
    let home =
        std::env::var_os("HOME").ok_or_else(|| StoreError::BadName("$HOME unset".to_owned()))?;
    Ok(PathBuf::from(home)
        .join(".local")
        .join("share")
        .join("dnx")
        .join("store"))
}

/// Read a directory tree into its deterministic `(relpath, bytes)` entries,
/// sorted by relpath. The single source of a tree's content used by both
/// `add_tree` (to publish) and `verify` (to re-derive), so the two can never
/// disagree on what a tree's hash is over.
fn tree_contents(dir: &Path) -> Result<Vec<(String, Vec<u8>)>, StoreError> {
    let mut entries: Vec<(String, PathBuf)> = Vec::new();
    collect_files(dir, dir, &mut entries)?;
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    let mut contents = Vec::with_capacity(entries.len());
    for (rel, abs) in entries {
        contents.push((rel, fs::read(&abs)?));
    }
    Ok(contents)
}

/// The deterministic BLAKE3 key of a tree: length-delimited `(relpath, bytes)`
/// folded in sorted order so the digest is independent of directory iteration
/// order and unambiguous across entry boundaries.
fn hash_contents(contents: &[(String, Vec<u8>)]) -> Blake3Hash {
    let mut hasher = blake3::Hasher::new();
    for (rel, data) in contents {
        hasher.update(&(rel.len() as u64).to_le_bytes());
        hasher.update(rel.as_bytes());
        hasher.update(&(data.len() as u64).to_le_bytes());
        hasher.update(data);
    }
    *hasher.finalize().as_bytes()
}

fn collect_files(
    base: &Path,
    dir: &Path,
    out: &mut Vec<(String, PathBuf)>,
) -> Result<(), StoreError> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if entry.file_type()?.is_dir() {
            collect_files(base, &path, out)?;
        } else {
            let rel = path
                .strip_prefix(base)
                .map_err(|_| StoreError::BadName(path.to_string_lossy().into_owned()))?;
            out.push((rel.to_string_lossy().replace('\\', "/"), path));
        }
    }
    Ok(())
}

/// A process-and-call-unique staging name, so concurrent writers of identical
/// content never share (and thus never truncate or race) one staging slot.
/// `<prefix>-<pid>-<nonce>`.
fn unique_staging(root: &Path, prefix: &str) -> PathBuf {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let nonce = COUNTER.fetch_add(1, Ordering::Relaxed);
    root.join(format!("{prefix}-{}-{nonce}", std::process::id()))
}

/// Materialise `contents` into a fresh staging dir. Any error removes the
/// partial staging dir before returning, so a genuine failure never leaks.
fn stage_tree(staging: &Path, contents: &[(String, Vec<u8>)]) -> Result<(), StoreError> {
    let build = || -> Result<(), StoreError> {
        fs::create_dir_all(staging)?;
        for (rel, data) in contents {
            let dst = staging.join(rel);
            if let Some(parent) = dst.parent() {
                fs::create_dir_all(parent)?;
            }
            fs::write(&dst, data)?;
        }
        Ok(())
    };
    build().inspect_err(|_| {
        let _ = fs::remove_dir_all(staging);
    })
}

fn write_atomic(root: &Path, target: &Path, bytes: &[u8]) -> Result<(), StoreError> {
    // Exclusive-create a per-writer-unique staging file (never the shared
    // content-hash name), fill it, then atomically rename to the
    // content-addressed final path. A losing racer sees `target.exists()`.
    let staging = unique_staging(root, ".tmp-blob");
    let mut f = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&staging)?;
    if let Err(e) = f.write_all(bytes).and_then(|()| f.sync_all()) {
        drop(f);
        let _ = fs::remove_file(&staging);
        return Err(StoreError::Io(e));
    }
    drop(f);
    match fs::rename(&staging, target) {
        Ok(()) => Ok(()),
        Err(_) if target.exists() => {
            let _ = fs::remove_file(&staging);
            Ok(())
        }
        Err(e) => {
            let _ = fs::remove_file(&staging);
            Err(StoreError::Io(e))
        }
    }
}
