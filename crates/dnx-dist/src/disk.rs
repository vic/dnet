//! Phase-1 on-disk content-addressed store (distribution-mvp-plan.md §C).
//!
//! A blob is keyed by its `net_hash` = `ArtifactId.wire` = `BLAKE3(serialize)`
//! (canonical-hash.md:123). Layout (distribution-design.md:74-79):
//!
//! ```text
//! <root>/blobs/<hex(net_hash)>   → canonical-net blob (= to_blob(net, root))
//! ```
//!
//! Load verifies-on-read (§C:198-200, §F.1-F.2): `from_blob` gates the bytes
//! into the `Net<Canonical>` typestate, then the re-hash must equal the key —
//! a corrupted blob is rejected, never trusted. Content addresses are
//! immutable, so a stored blob is cacheable forever (distribution-design.md:86).

use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use dnx_core::NetClassMarker;
use dnx_core::{canonical_hash, from_blob, to_blob, Blake3Hash, Canonical, DnxError, Net, PortId};

/// On-disk CAS error: I/O failure, or a blob that fails to decode / verify.
/// Kept distinct from `DnxError` so the placement layer's I/O concerns never
/// leak into the reduction core (vic: no stringly-typed errors).
#[derive(Debug)]
pub enum CacheError {
    Io(io::Error),
    Decode(DnxError),
    /// Loaded bytes re-hash to a value other than their content-address key —
    /// integrity violation (distribution-design.md:219-221).
    HashMismatch,
}

impl fmt::Display for CacheError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CacheError::Io(e) => write!(f, "cache io: {e}"),
            CacheError::Decode(e) => write!(f, "cache decode: {e}"),
            CacheError::HashMismatch => write!(f, "cache integrity: blob does not match its key"),
        }
    }
}

impl std::error::Error for CacheError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            CacheError::Io(e) => Some(e),
            CacheError::Decode(e) => Some(e),
            CacheError::HashMismatch => None,
        }
    }
}

impl From<io::Error> for CacheError {
    fn from(e: io::Error) -> Self {
        CacheError::Io(e)
    }
}

impl From<DnxError> for CacheError {
    fn from(e: DnxError) -> Self {
        CacheError::Decode(e)
    }
}

/// Write `bytes` to `final_path` atomically: stream to a sibling temp file in
/// the SAME directory, then `fs::rename` (an atomic replace on the same
/// filesystem). A crash or concurrent reader therefore sees either the old
/// blob or the complete new one — never a torn/partial blob
/// (distribution-design.md:219-221: content addresses are immutable, so a
/// stored blob must be whole-or-absent). On any failure the temp file is
/// removed so no debris accumulates.
fn atomic_write(final_path: &Path, bytes: &[u8]) -> io::Result<()> {
    let dir = final_path.parent().unwrap_or_else(|| Path::new("."));
    let name = final_path
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("blob");
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let tmp = dir.join(format!(".{name}.{}.{nanos}.tmp", std::process::id()));
    let write_then_rename = || -> io::Result<()> {
        fs::write(&tmp, bytes)?;
        fs::rename(&tmp, final_path)
    };
    write_then_rename().inspect_err(|_| {
        let _ = fs::remove_file(&tmp);
    })
}

/// Lower-case hex of a 32-byte content-address (the on-disk file name).
/// Hand-rolled to avoid a `hex` dependency (distribution-mvp-plan.md §D.3).
fn hex(hash: &Blake3Hash) -> String {
    const LUT: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(64);
    for &b in hash {
        s.push(LUT[(b >> 4) as usize] as char);
        s.push(LUT[(b & 0x0F) as usize] as char);
    }
    s
}

/// A decoded canonical net plus its root port, as produced by a CAS load.
pub type LoadedNet<C> = (Net<Canonical, C>, PortId);

/// An on-disk content-addressed store rooted at a directory.
pub struct DiskCache {
    blobs: PathBuf,
}

impl DiskCache {
    /// Open (creating if absent) a CAS under `root`; ensures `<root>/blobs/`.
    pub fn open(root: impl AsRef<Path>) -> Result<Self, CacheError> {
        let blobs = root.as_ref().join("blobs");
        fs::create_dir_all(&blobs)?;
        Ok(DiskCache { blobs })
    }

    fn path(&self, hash: &Blake3Hash) -> PathBuf {
        self.blobs.join(hex(hash))
    }

    /// Whether a blob for `hash` is present on disk.
    pub fn contains(&self, hash: &Blake3Hash) -> bool {
        self.path(hash).is_file()
    }

    /// Store `net`'s canonical blob, keyed by its own content-address; returns
    /// that key. Idempotent — the same net overwrites with identical bytes.
    pub fn store<C: NetClassMarker>(
        &self,
        net: &Net<Canonical, C>,
        root: PortId,
    ) -> Result<Blake3Hash, CacheError> {
        let hash = canonical_hash(net, root)?;
        let blob = to_blob(net, root)?;
        atomic_write(&self.path(&hash), &blob)?;
        Ok(hash)
    }

    /// Load the blob keyed by `hash`, verifying-on-read: decode into the
    /// `Net<Canonical>` typestate, then require the re-hash to equal `hash`.
    /// Absent key → `Ok(None)`; corrupt/foreign bytes → `Err`.
    pub fn load<C: NetClassMarker>(
        &self,
        hash: &Blake3Hash,
    ) -> Result<Option<LoadedNet<C>>, CacheError> {
        let path = self.path(hash);
        if !path.is_file() {
            return Ok(None);
        }
        let bytes = fs::read(&path)?;
        let (net, root): (Net<Canonical, C>, PortId) = from_blob(&bytes)?;
        if canonical_hash(&net, root)? != *hash {
            return Err(CacheError::HashMismatch);
        }
        Ok(Some((net, root)))
    }

    /// Export the raw blob bytes keyed by `hash` for transport to a peer (the
    /// publishing side of the two-node fetch, distribution-mvp-plan.md §F:291
    /// `Store::get`). Absent key → `Ok(None)`. Returns the bytes verbatim —
    /// integrity is re-checked by the importer (`import`), never assumed.
    pub fn export(&self, hash: &Blake3Hash) -> Result<Option<Vec<u8>>, CacheError> {
        let path = self.path(hash);
        if !path.is_file() {
            return Ok(None);
        }
        Ok(Some(fs::read(&path)?))
    }

    /// Import an untrusted peer blob claimed to be `claimed`, persisting it only
    /// if it verifies (distribution-mvp-plan.md §E:240-242, §F:299-303). The
    /// blob must (1) `from_blob`-decode into the `Net<Canonical>` typestate
    /// (the unforgeable canonicity proof, net.md:431) and (2) re-hash to
    /// exactly `claimed`; a mismatch is `HashMismatch` and nothing is written —
    /// no false accept (distribution-design.md:219-221). Single-frontend MVP ⇒
    /// prim-compat holds by construction (§F.3:312-313).
    pub fn import<C: NetClassMarker>(
        &self,
        claimed: Blake3Hash,
        blob: &[u8],
    ) -> Result<(), CacheError> {
        let (net, root): (Net<Canonical, C>, PortId) = from_blob(blob)?;
        if canonical_hash(&net, root)? != claimed {
            return Err(CacheError::HashMismatch);
        }
        atomic_write(&self.path(&claimed), blob)?;
        Ok(())
    }

    /// The fetch-frontier diff: of `keys`, the ones this store lacks — so a
    /// node requests from a peer only what it does not already hold
    /// (distribution-mvp-plan.md §E:234; the Unison missing-dependency frontier,
    /// degenerate to a flat set for the monolithic-blob MVP).
    pub fn missing(&self, keys: &[Blake3Hash]) -> Vec<Blake3Hash> {
        keys.iter().filter(|k| !self.contains(k)).copied().collect()
    }
}
