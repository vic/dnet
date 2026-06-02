use crate::error::StoreError;
use dnx_core::Blake3Hash;
use std::fmt;
use std::path::{Component, Path};
use std::sync::Arc;

const HEX_LEN: usize = 64;

/// A content-addressed store path: a BLAKE3 key plus a human name.
///
/// Invalid state is unrepresentable — the only constructor validates the
/// name, so `Display`/the on-disk filename `<hex>-<name>` is always a single
/// well-formed path component.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct StorePath {
    hash: Blake3Hash,
    name: Arc<str>,
}

impl StorePath {
    /// Build a path from a key and a name. The name must denote exactly one
    /// normal path component — no `/`, `\`, `.`/`..`, root, NUL, or other
    /// control char — so the on-disk filename `<hex>-<name>` is always a
    /// single well-formed component that cannot escape the store dir. The
    /// fixed-width hex prefix keeps the filename unambiguous, so `-` inside
    /// the name is allowed.
    pub fn new(hash: Blake3Hash, name: &str) -> Result<Self, StoreError> {
        if !is_single_component(name) {
            return Err(StoreError::BadName(name.to_owned()));
        }
        Ok(StorePath {
            hash,
            name: Arc::from(name),
        })
    }

    /// The BLAKE3 key.
    pub fn hash(&self) -> &Blake3Hash {
        &self.hash
    }

    /// The human-readable name component.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Parse a `<hex>-<name>` filename back into a `StorePath`.
    pub fn parse(component: &str) -> Result<Self, StoreError> {
        let bad = || StoreError::BadName(component.to_owned());
        if component.len() < HEX_LEN + 2 || component.as_bytes().get(HEX_LEN) != Some(&b'-') {
            return Err(bad());
        }
        let (hex, rest) = component.split_at(HEX_LEN);
        let mut hash = [0u8; 32];
        for (i, byte) in hash.iter_mut().enumerate() {
            let hi = hex_val(hex.as_bytes()[i * 2]).ok_or_else(bad)?;
            let lo = hex_val(hex.as_bytes()[i * 2 + 1]).ok_or_else(bad)?;
            *byte = (hi << 4) | lo;
        }
        StorePath::new(hash, &rest[1..])
    }
}

/// A name is valid iff it is exactly one `Component::Normal` and free of any
/// separator, backslash, or control char. The direct `/` reject is load-
/// bearing: `Path::components` *strips* a trailing slash (`"a/"` normalises to
/// one `Normal("a")`), so the component check alone would admit a name still
/// carrying a separator. Rejecting `/` and `\0`/control bytes outright keeps
/// the on-disk filename `<hex>-<name>` a single uncorruptible component.
fn is_single_component(name: &str) -> bool {
    let mut parts = Path::new(name).components();
    let one_normal = matches!(parts.next(), Some(Component::Normal(_))) && parts.next().is_none();
    one_normal
        && !name
            .chars()
            .any(|c| c.is_control() || c == '\\' || c == '/')
}

fn hex_val(c: u8) -> Option<u8> {
    match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        _ => None,
    }
}

impl fmt::Display for StorePath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in &self.hash {
            write!(f, "{byte:02x}")?;
        }
        write!(f, "-{}", self.name)
    }
}
