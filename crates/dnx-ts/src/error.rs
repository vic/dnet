use std::fmt;

/// Errors from the tree-sitter JSON front-end. Typed (no stringly-typed
/// control flow): `Parse` is a grammar/parse failure, `Unsupported` is a CST
/// node kind the JSON mapper does not handle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TsError {
    Parse(String),
    Unsupported(String),
}

impl fmt::Display for TsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TsError::Parse(s) => write!(f, "parse error: {s}"),
            TsError::Unsupported(s) => write!(f, "unsupported JSON node: {s}"),
        }
    }
}

impl std::error::Error for TsError {}
