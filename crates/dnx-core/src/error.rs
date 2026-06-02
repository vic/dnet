use std::fmt;
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DnxError {
    LinError(LinError),
    LOPathDepthExceeded,
    StepLimitExceeded(u64),
    ArenaCapacityExceeded,
    DeltaOverflow,
    StalePair,
    ABAViolation,
    PrimError(Arc<str>),
    ReadbackIncomplete,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LinError {
    Unused(Arc<str>),
    MultiUse(Arc<str>, u32),
    MutualRecursion(Vec<Arc<str>>),
    TooManyFreeVars,
}

impl fmt::Display for DnxError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DnxError::LinError(e) => write!(f, "linearity: {e}"),
            DnxError::LOPathDepthExceeded => write!(f, "LO path depth exceeded (>384)"),
            DnxError::StepLimitExceeded(n) => write!(f, "step limit exceeded: {n}"),
            DnxError::ArenaCapacityExceeded => write!(f, "arena capacity exceeded"),
            DnxError::DeltaOverflow => write!(f, "replicator delta overflow"),
            DnxError::StalePair => write!(f, "stale active pair"),
            DnxError::ABAViolation => write!(f, "ABA generation violation"),
            DnxError::PrimError(m) => write!(f, "primitive error: {m}"),
            DnxError::ReadbackIncomplete => write!(f, "readback incomplete: net not canonical"),
        }
    }
}

impl fmt::Display for LinError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LinError::Unused(n) => write!(f, "variable `{n}` unused"),
            LinError::MultiUse(n, c) => write!(f, "variable `{n}` used {c} times"),
            LinError::MutualRecursion(ns) => write!(f, "mutual recursion without `fix`: {ns:?}"),
            LinError::TooManyFreeVars => write!(f, "too many free variables (>16383)"),
        }
    }
}

impl std::error::Error for DnxError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            DnxError::LinError(e) => Some(e),
            _ => None,
        }
    }
}

impl std::error::Error for LinError {}

impl From<LinError> for DnxError {
    fn from(e: LinError) -> Self {
        DnxError::LinError(e)
    }
}
