use std::fmt;
use std::sync::Arc;

/// Errors from loading, parsing, showing, or locking a flake.
#[derive(Debug)]
pub enum FlakeError {
    Io(Arc<str>),
    Parse(Arc<str>),
    NotAFlake(Arc<str>),
    AttrNotFound(Arc<str>),
    Eval(Arc<str>),
    Lock(Arc<str>),
    HashMismatch { input: Arc<str> },
}

impl fmt::Display for FlakeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FlakeError::Io(s) => write!(f, "io error: {s}"),
            FlakeError::Parse(s) => write!(f, "parse error: {s}"),
            FlakeError::NotAFlake(s) => write!(f, "not a flake: {s}"),
            FlakeError::AttrNotFound(s) => write!(f, "attribute not found: {s}"),
            FlakeError::Eval(s) => write!(f, "eval error: {s}"),
            FlakeError::Lock(s) => write!(f, "lock error: {s}"),
            FlakeError::HashMismatch { input } => {
                write!(f, "hash mismatch for input '{input}'")
            }
        }
    }
}

impl std::error::Error for FlakeError {}
