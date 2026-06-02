use std::sync::Arc;

use dnx_core::prim::PrimValue;
use dnx_drv::from_attrs;
use dnx_lang::runtime::NixEvalResult;
use dnx_store::{Store, StorePath};

use crate::error::FlakeError;
use crate::flake::Flake;

/// What an evaluated output attribute path turned out to be.
#[derive(Debug)]
pub enum OutputKind {
    /// A derivation leaf, instantiated to its drvPath (no builder runs).
    Derivation { drv_path: StorePath },
    /// A non-derivation WHNF value (its dnx type name, e.g. `"int"`).
    Value { kind: &'static str },
    /// The output could not be evaluated or is not a well-formed derivation
    /// (the eval seam, or a derivation that fails attribute validation).
    Unresolved { reason: Arc<str> },
}

/// The evaluated outputs of a flake: each enumerated attribute path paired with
/// what it resolved to. Produced by [`Flake::report`], consumed by
/// `dnx flake show` (render) and `dnx flake check` ([`FlakeReport::ok`]).
#[derive(Debug)]
pub struct FlakeReport {
    entries: Vec<(Arc<str>, OutputKind)>,
}

impl FlakeReport {
    /// The output paths and their resolved kinds, in `show` (sorted-path) order.
    pub fn entries(&self) -> &[(Arc<str>, OutputKind)] {
        &self.entries
    }

    /// Whether every output resolved: no [`OutputKind::Unresolved`] entry.
    /// This is the `dnx flake check` gate (false → nonzero exit).
    pub fn ok(&self) -> bool {
        !self
            .entries
            .iter()
            .any(|(_, k)| matches!(k, OutputKind::Unresolved { .. }))
    }
}

impl Flake {
    /// Evaluate every enumerated output to WHNF and classify it: a derivation
    /// leaf is instantiated to its drvPath (pure, no builder), a plain value
    /// keeps its type name, and an output that hits the eval seam (or is a
    /// malformed derivation) is recorded as `Unresolved` rather than aborting
    /// the whole report. `store` is where derivation descriptions are written
    /// to compute their drvPath.
    pub fn report(&self, store: &Store) -> Result<FlakeReport, FlakeError> {
        let mut entries = Vec::new();
        for path in self.show()?.paths() {
            let kind = match self.resolve_attr(path) {
                Ok(value) => classify(&value, store),
                Err(e) => OutputKind::Unresolved {
                    reason: Arc::from(e.to_string()),
                },
            };
            entries.push((path.clone(), kind));
        }
        Ok(FlakeReport { entries })
    }
}

/// Classify a resolved output value. A `type = "derivation"` attrset is lifted
/// to a `Derivation` and instantiated; anything else is a plain value.
fn classify(value: &NixEvalResult, store: &Store) -> OutputKind {
    match value {
        NixEvalResult::AttrSet(kvs) if is_derivation(kvs) => match from_attrs(kvs) {
            Ok(drv) => match drv.instantiate(store) {
                Ok(drv_path) => OutputKind::Derivation { drv_path },
                Err(e) => OutputKind::Unresolved {
                    reason: Arc::from(e.to_string()),
                },
            },
            Err(e) => OutputKind::Unresolved {
                reason: Arc::from(e.to_string()),
            },
        },
        other => OutputKind::Value {
            kind: kind_of(other),
        },
    }
}

/// Whether a WHNF attrset carries the `type = "derivation"` marker that
/// `derivationStrict` stamps on every derivation (prim.rs `prim_derivation_strict`).
fn is_derivation(kvs: &[(Arc<str>, PrimValue)]) -> bool {
    kvs.iter().any(|(k, v)| {
        k.as_ref() == "type" && matches!(v, PrimValue::Str(s) if s.as_ref() == "derivation")
    })
}

/// The dnx type name of a WHNF value, for the `show` listing of a non-derivation
/// output. (An `Error` cannot reach here — `resolve_attr` returns it as `Err`.)
fn kind_of(r: &NixEvalResult) -> &'static str {
    match r {
        NixEvalResult::Int(_) => "int",
        NixEvalResult::Float(_) => "float",
        NixEvalResult::Str(_) => "string",
        NixEvalResult::Bool(_) => "bool",
        NixEvalResult::Null => "null",
        NixEvalResult::List(_) => "list",
        NixEvalResult::AttrSet(_) => "set",
        NixEvalResult::Lambda(_) => "lambda",
        NixEvalResult::Error(_) => "error",
    }
}
