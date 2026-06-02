use dnx_store::{StoreError, StorePath};
use std::fmt;
use std::sync::Arc;

/// Errors from derivation instantiation and realization. Typed, never panics.
#[derive(Debug)]
pub enum DrvError {
    /// An underlying store operation failed.
    Store(StoreError),
    /// Spawning or running the builder failed at the OS level.
    Spawn(std::io::Error),
    /// The builder ran but exited non-zero. `code` is `None` if killed by a signal.
    Build { code: Option<i32> },
    /// The builder succeeded but produced no output at the expected `$out` path.
    MissingOutput(Arc<str>),
    /// The output path is a symlink. Rejected: a build output must be a real
    /// file or directory the builder created, never a link to a host file
    /// (which would exfiltrate its bytes into the store).
    OutputSymlink(Arc<str>),
    /// A `derivationStrict` attrset was missing a field or had the wrong type.
    BadAttrs(String),
    /// The builder named a `builtin:<x>` we do not implement.
    UnknownBuiltin(Arc<str>),
    /// A builtin needed an `input_srcs` path that is absent from the store.
    MissingInput(StorePath),
    /// Serialized derivation bytes were truncated, over-long, or otherwise
    /// malformed (the inverse of `to_bytes` could not parse them).
    Decode(String),
}

impl fmt::Display for DrvError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DrvError::Store(e) => write!(f, "store: {e}"),
            DrvError::Spawn(e) => write!(f, "builder spawn: {e}"),
            DrvError::Build { code: Some(c) } => write!(f, "builder failed with exit code {c}"),
            DrvError::Build { code: None } => write!(f, "builder killed by signal"),
            DrvError::MissingOutput(n) => write!(f, "builder produced no output {n:?}"),
            DrvError::OutputSymlink(n) => {
                write!(
                    f,
                    "output {n:?} is a symlink; build outputs must be real files"
                )
            }
            DrvError::BadAttrs(m) => write!(f, "invalid derivation attrs: {m}"),
            DrvError::UnknownBuiltin(n) => write!(f, "unknown builtin builder \"builtin:{n}\""),
            DrvError::MissingInput(p) => write!(f, "input {p} is not in the store"),
            DrvError::Decode(m) => write!(f, "malformed derivation bytes: {m}"),
        }
    }
}

impl std::error::Error for DrvError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            DrvError::Store(e) => Some(e),
            DrvError::Spawn(e) => Some(e),
            _ => None,
        }
    }
}

impl From<StoreError> for DrvError {
    fn from(e: StoreError) -> Self {
        DrvError::Store(e)
    }
}
