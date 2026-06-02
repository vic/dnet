use std::fmt;

/// Parse-time errors for the minimal Python surface.
#[derive(Debug, Clone, PartialEq)]
pub enum PyError {
    Lex(String),
    Parse(String),
    Unsupported(String),
}

impl fmt::Display for PyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PyError::Lex(s) => write!(f, "lex error: {s}"),
            PyError::Parse(s) => write!(f, "parse error: {s}"),
            PyError::Unsupported(s) => write!(f, "unsupported syntax: {s}"),
        }
    }
}

impl std::error::Error for PyError {}
