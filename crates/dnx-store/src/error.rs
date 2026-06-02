use std::fmt;
use std::io;

/// Errors from store operations. Typed, never panics.
#[derive(Debug)]
pub enum StoreError {
    /// Underlying filesystem failure.
    Io(io::Error),
    /// A store-path name was not a single normal path component, or a
    /// filename failed to parse back into a `<hex>-<name>` path.
    BadName(String),
    /// Bytes read back from the store did not hash to the expected key.
    HashMismatch,
    /// `get` (blob-only) was called on a path that resolves to a stored
    /// directory tree. Read trees with the tree API, not `get`.
    IsTree,
}

impl fmt::Display for StoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StoreError::Io(e) => write!(f, "store io: {e}"),
            StoreError::BadName(n) => write!(f, "invalid store name: {n:?}"),
            StoreError::HashMismatch => write!(f, "content hash mismatch"),
            StoreError::IsTree => write!(f, "store path is a tree, not a blob"),
        }
    }
}

impl std::error::Error for StoreError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            StoreError::Io(e) => Some(e),
            _ => None,
        }
    }
}

impl From<io::Error> for StoreError {
    fn from(e: io::Error) -> Self {
        StoreError::Io(e)
    }
}
