//! A source-keyed result cache for the runner: the content hash of a case's
//! source maps to its verdict, so an unchanged case is served without any
//! reduction on a re-run (`interactions == 0`, dnx-test-runner-design.md §5).
//!
//! Keying by the case source (not the result net) is the only content address
//! available here: the canonical-net hasher does not yet cover scalar/prim
//! normal forms (canonical_hash.rs:193), which is what these cases reduce to.
//! Source identity is a sound proxy — identical source ⇒ identical net ⇒
//! identical normal form — and is exactly the per-case granularity the design
//! wants (editing one case changes only its key, design §5).

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use dnx_lang::TestCase;

use crate::Outcome;

/// Content key of a case = FNV-1a-64 of `path\0expr\0expected`, as hex. A
/// hand-rolled hash keeps the crate dependency-free (no `blake3`/`hex`); it need
/// only be deterministic and collision-resistant enough to address test cases.
pub(crate) fn case_key(case: &TestCase) -> String {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    // Feed each field with a `0` separator between them so field boundaries are
    // significant (the FNV-1a step folds the byte then mixes).
    for byte in case
        .path
        .bytes()
        .chain([0])
        .chain(case.expr.bytes())
        .chain([0])
        .chain(case.expected.bytes())
    {
        h ^= byte as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    format!("{h:016x}")
}

/// On-disk verdict cache rooted at a directory; one file per case key.
pub struct DiskResultCache {
    dir: PathBuf,
}

impl DiskResultCache {
    /// Open (creating if absent) a cache under `dir`.
    pub fn open(dir: impl AsRef<Path>) -> io::Result<Self> {
        let dir = dir.as_ref().to_path_buf();
        fs::create_dir_all(&dir)?;
        Ok(DiskResultCache { dir })
    }

    fn path(&self, key: &str) -> PathBuf {
        self.dir.join(key)
    }

    /// The cached verdict for `key`, if present and well-formed. A corrupt entry
    /// reads as a miss (it is simply recomputed and overwritten).
    pub fn get(&self, key: &str) -> Option<Outcome> {
        let bytes = fs::read(self.path(key)).ok()?;
        decode(&String::from_utf8(bytes).ok()?)
    }

    /// Store `outcome` for `key`, written atomically (temp + rename) so a
    /// concurrent reader never sees a torn entry. A write failure is ignored:
    /// the cache is an optimization, never a correctness dependency.
    pub fn put(&self, key: &str, outcome: &Outcome) {
        let tmp = self.dir.join(format!(".{key}.{}.tmp", std::process::id()));
        if fs::write(&tmp, encode(outcome)).is_ok() && fs::rename(&tmp, self.path(key)).is_err() {
            let _ = fs::remove_file(&tmp);
        }
    }
}

/// Verdict wire form: tab-separated, newline-free fields (renders are
/// single-line). `P` pass · `F\texpected\tgot` fail · `E\tmsg` error.
fn encode(o: &Outcome) -> String {
    match o {
        Outcome::Pass => "P".to_string(),
        Outcome::Fail { expected, got } => {
            format!("F\t{}\t{}", sanitize(expected), sanitize(got))
        }
        Outcome::Error(msg) => format!("E\t{}", sanitize(msg)),
    }
}

fn decode(s: &str) -> Option<Outcome> {
    let mut it = s.splitn(3, '\t');
    match it.next()? {
        "P" => Some(Outcome::Pass),
        "F" => {
            let expected = it.next()?.to_string();
            let got = it.next()?.to_string();
            Some(Outcome::Fail { expected, got })
        }
        "E" => Some(Outcome::Error(it.next().unwrap_or("").to_string())),
        _ => None,
    }
}

/// Keep encoded fields single-line and delimiter-free so the flat format round-trips.
fn sanitize(s: &str) -> String {
    s.replace(['\t', '\n', '\r'], " ")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn case(path: &str, expr: &str, expected: &str) -> TestCase {
        TestCase {
            path: path.into(),
            expr: expr.into(),
            expected: expected.into(),
        }
    }

    #[test]
    fn key_is_stable_and_distinguishes_source() {
        let a = case("t", "1 + 2", "3");
        let b = case("t", "1 + 2", "3");
        let c = case("t", "1 + 4", "3");
        assert_eq!(case_key(&a), case_key(&b), "same source → same key");
        assert_ne!(case_key(&a), case_key(&c), "different expr → different key");
    }

    #[test]
    fn roundtrips_outcomes() {
        for o in [
            Outcome::Pass,
            Outcome::Fail {
                expected: "3".into(),
                got: "2".into(),
            },
            Outcome::Error("boom".into()),
        ] {
            assert_eq!(decode(&encode(&o)), Some(o));
        }
    }

    #[test]
    fn get_put_roundtrip() {
        let dir = std::env::temp_dir().join(format!("dnx-cache-ut-{}", std::process::id()));
        let c = DiskResultCache::open(&dir).expect("open");
        assert_eq!(c.get("k"), None, "absent key misses");
        c.put("k", &Outcome::Pass);
        assert_eq!(c.get("k"), Some(Outcome::Pass));
        let _ = std::fs::remove_dir_all(&dir);
    }
}
