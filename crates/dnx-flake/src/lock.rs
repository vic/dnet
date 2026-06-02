use std::path::Path;
use std::sync::Arc;

use crate::error::FlakeError;

/// One locked input: a local path pinned by the BLAKE3 hash of its content.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockEntry {
    name: Arc<str>,
    path: Arc<str>,
    hash: [u8; 32],
}

impl LockEntry {
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn path(&self) -> &str {
        &self.path
    }
    pub fn hash(&self) -> &[u8; 32] {
        &self.hash
    }
}

/// Our minimal `flake.lock`: a sorted set of local-path inputs, each pinned by
/// a BLAKE3 content hash. Not the cppNix node-graph format. One input per line:
/// `name\tpath\thex(blake3)`.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LockFile {
    entries: Vec<LockEntry>,
}

impl LockFile {
    pub fn entries(&self) -> &[LockEntry] {
        &self.entries
    }

    /// Pin a local-path input by hashing the content at `content` while
    /// recording `path` as its lockfile location. `path` is the portable
    /// (flake-relative) identity stored in the lock; `content` is the on-disk
    /// file actually read to compute the BLAKE3 hash. They coincide for a path
    /// that is already its own portable identity (e.g. an absolute input pinned
    /// directly in a test); `Flake::lock` passes a flake-relative `path` so the
    /// lock is identical regardless of how the flake dir was spelled.
    pub fn pin(&mut self, name: &str, path: &Path, content: &Path) -> Result<(), FlakeError> {
        let bytes = std::fs::read(content)
            .map_err(|e| FlakeError::Io(Arc::from(format!("{}: {e}", content.display()))))?;
        let hash = *blake3::hash(&bytes).as_bytes();
        let entry = LockEntry {
            name: Arc::from(name),
            path: Arc::from(path.to_string_lossy().as_ref()),
            hash,
        };
        match self.entries.iter().position(|e| e.name == entry.name) {
            Some(i) => self.entries[i] = entry,
            None => self.entries.push(entry),
        }
        self.entries.sort_by(|a, b| a.name.cmp(&b.name));
        Ok(())
    }

    /// Serialize to our flat text format.
    pub fn to_text(&self) -> String {
        let mut s = String::new();
        for e in &self.entries {
            s.push_str(&e.name);
            s.push('\t');
            s.push_str(&e.path);
            s.push('\t');
            s.push_str(&hex_encode(&e.hash));
            s.push('\n');
        }
        s
    }

    /// Parse our flat text format.
    pub fn from_text(text: &str) -> Result<LockFile, FlakeError> {
        let mut entries = Vec::new();
        for line in text.lines() {
            if line.is_empty() {
                continue;
            }
            let mut cols = line.split('\t');
            let name = cols
                .next()
                .ok_or_else(|| FlakeError::Lock("missing name column".into()))?;
            let path = cols
                .next()
                .ok_or_else(|| FlakeError::Lock("missing path column".into()))?;
            let hex = cols
                .next()
                .ok_or_else(|| FlakeError::Lock("missing hash column".into()))?;
            if cols.next().is_some() {
                return Err(FlakeError::Lock("extra columns".into()));
            }
            entries.push(LockEntry {
                name: Arc::from(name),
                path: Arc::from(path),
                hash: hex_decode(hex)?,
            });
        }
        entries.sort_by(|a, b| a.name.cmp(&b.name));
        Ok(LockFile { entries })
    }

    /// Re-hash every pinned path and confirm it matches the recorded hash. Each
    /// recorded path is resolved against `base` (the flake's directory): the
    /// stored path is flake-relative for portability, so it only names a file
    /// once joined to the dir it was locked from. An already-absolute stored
    /// path ignores `base` (`Path::join` returns the absolute operand), so a
    /// directly-pinned absolute input still verifies against any base.
    pub fn verify(&self, base: &Path) -> Result<(), FlakeError> {
        for e in &self.entries {
            let file = base.join(e.path.as_ref());
            let bytes = std::fs::read(&file)
                .map_err(|err| FlakeError::Io(Arc::from(format!("{}: {err}", file.display()))))?;
            if blake3::hash(&bytes).as_bytes() != &e.hash {
                return Err(FlakeError::HashMismatch {
                    input: e.name.clone(),
                });
            }
        }
        Ok(())
    }
}

fn hex_encode(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes {
        s.push(nibble(b >> 4));
        s.push(nibble(b & 0x0f));
    }
    s
}

fn nibble(n: u8) -> char {
    match n {
        0..=9 => (b'0' + n) as char,
        _ => (b'a' + (n - 10)) as char,
    }
}

fn hex_decode(s: &str) -> Result<[u8; 32], FlakeError> {
    let bytes = s.as_bytes();
    if bytes.len() != 64 {
        return Err(FlakeError::Lock("hash must be 64 hex chars".into()));
    }
    let mut out = [0u8; 32];
    for (i, pair) in bytes.chunks_exact(2).enumerate() {
        let hi = un_nibble(pair[0])?;
        let lo = un_nibble(pair[1])?;
        out[i] = (hi << 4) | lo;
    }
    Ok(out)
}

fn un_nibble(c: u8) -> Result<u8, FlakeError> {
    match c {
        b'0'..=b'9' => Ok(c - b'0'),
        b'a'..=b'f' => Ok(c - b'a' + 10),
        _ => Err(FlakeError::Lock("invalid hex digit".into())),
    }
}
