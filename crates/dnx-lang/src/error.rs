use std::fmt;
use std::path::PathBuf;
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq)]
pub enum NixError {
    ParseError(String),
    UnboundVariable(Arc<str>),
    UnsupportedSyntax(String),
    LinearityViolation(String),
    InternalError(String),
    /// `import` re-entered a file already being resolved (cyclic or self
    /// import), or nesting exceeded the resolve-depth cap. Carries the
    /// canonical path that closed the cycle.
    ImportCycle(PathBuf),
    /// `import <name>` / `import <name/sub>` named a search-path root that the
    /// registry (built from `DNX_PATH`) has no entry for. Carries the
    /// unresolved bracket-inner text, so the miss is distinct from a filesystem
    /// `ParseError` ENOENT (`nixpkgs-lib-design.md` §1.4).
    SearchPathUnset(String),
}

impl fmt::Display for NixError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NixError::ParseError(s) => write!(f, "parse error: {s}"),
            NixError::UnboundVariable(n) => write!(f, "unbound variable: {n}"),
            NixError::UnsupportedSyntax(s) => write!(f, "unsupported syntax: {s}"),
            NixError::LinearityViolation(s) => write!(f, "linearity violation: {s}"),
            NixError::InternalError(s) => write!(f, "internal error: {s}"),
            NixError::ImportCycle(p) => write!(f, "import cycle: {}", p.display()),
            NixError::SearchPathUnset(n) => {
                write!(f, "search path <{n}> not set (configure via DNX_PATH)")
            }
        }
    }
}

impl std::error::Error for NixError {}
