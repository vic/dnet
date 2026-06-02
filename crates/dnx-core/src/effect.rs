/// Phase C: Two-tier effect architecture (D1-D10).
use crate::canonical_hash::Blake3Hash;
use crate::net::Net;
use crate::prim::{PrimState, PrimValue};
use crate::{DnxError, LOPath, NetClassMarker, PortId, Proper};
use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

pub type EffectLabel = Arc<str>;

/// Well-known builtin effect labels.
pub mod labels {
    pub const IO: &str = "io";
    pub const STORE: &str = "nix.store";
    pub const FILE: &str = "fs.file";
    pub const TIME: &str = "time";
    pub const ENV: &str = "env";
    pub const RAND: &str = "random";
}

/// Effect row: sorted set of required capabilities.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectRow {
    pub labels: BTreeSet<EffectLabel>,
    pub tail: Option<Arc<str>>, // None = closed, Some = open
}

impl EffectRow {
    pub fn pure() -> Self {
        EffectRow {
            labels: BTreeSet::new(),
            tail: None,
        }
    }

    pub fn is_pure(&self) -> bool {
        self.labels.is_empty() && self.tail.is_none()
    }

    pub fn single(label: &str) -> Self {
        let mut row = Self::pure();
        row.labels.insert(Arc::from(label));
        row
    }

    pub fn union(a: &Self, b: &Self) -> Self {
        let mut labels = a.labels.clone();
        labels.extend(b.labels.iter().cloned());
        let tail = a.tail.clone().or_else(|| b.tail.clone());
        EffectRow { labels, tail }
    }
}

/// A pending effect request captured during normalization.
pub struct EffRequest {
    pub label: EffectLabel,
    pub args: Vec<PrimValue>,
    pub continuation: PortId,
    pub lo: LOPath,
}

/// Handler return value.
pub enum HandlerResult {
    Resume(PrimValue),
    Abort(PrimValue),
}

/// Handler error.
#[derive(Debug)]
pub enum HandlerError {
    HandlerFailed(String),
    NoHandler(EffectLabel),
}

/// A single effect handler.
pub trait EffectHandler: Send + Sync {
    fn handle(&self, args: &[PrimValue]) -> Result<HandlerResult, HandlerError>;
}

/// Environment of all registered handlers.
pub struct HandlerEnv {
    handlers: HashMap<EffectLabel, Box<dyn EffectHandler>>,
}

impl HandlerEnv {
    pub fn new() -> Self {
        HandlerEnv {
            handlers: HashMap::new(),
        }
    }

    pub fn register(&mut self, label: &str, handler: Box<dyn EffectHandler>) {
        self.handlers.insert(Arc::from(label), handler);
    }

    pub fn has_handler(&self, label: &str) -> bool {
        self.handlers.contains_key(label)
    }

    pub fn handle(&self, label: &str, args: &[PrimValue]) -> Result<HandlerResult, HandlerError> {
        match self.handlers.get(label) {
            Some(h) => h.handle(args),
            None => Err(HandlerError::NoHandler(Arc::from(label))),
        }
    }
}

impl Default for HandlerEnv {
    fn default() -> Self {
        Self::new()
    }
}

/// D8: validate_handlers — startup check that all required effects have handlers.
pub fn validate_handlers(env: &HandlerEnv, row: &EffectRow) -> Result<(), HandlerError> {
    for label in &row.labels {
        if !env.has_handler(label) {
            return Err(HandlerError::NoHandler(label.clone()));
        }
    }
    Ok(())
}

/// D6: ArtifactId — content-addressed identity with effect metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArtifactId {
    pub net_hash: Blake3Hash,
    pub effect_row: EffectRow,
}

impl ArtifactId {
    pub fn pure(net_hash: Blake3Hash) -> Self {
        ArtifactId {
            net_hash,
            effect_row: EffectRow::pure(),
        }
    }
}

/// normalize_effectful: trampoline loop for Tier-1 effects.
/// Drains frontier, collects EffRequests, dispatches handlers, repeats.
pub fn normalize_effectful<C: NetClassMarker>(
    net: &mut Net<Proper, C>,
    prim_state: &mut PrimState,
    env: &HandlerEnv,
    pending_effects: &mut Vec<EffRequest>,
) -> Result<(), DnxError> {
    loop {
        // normalize_inner: not yet wired (Phase C completion).
        // For now: if no pending effects, break.
        if pending_effects.is_empty() {
            break;
        }
        let reqs = std::mem::take(pending_effects);
        for req in reqs {
            let val = match env.handle(&req.label, &req.args) {
                Ok(HandlerResult::Resume(v)) => v,
                Ok(HandlerResult::Abort(v)) => v, // simplified: treat as resume
                Err(HandlerError::NoHandler(l)) => {
                    return Err(DnxError::PrimError(Arc::from(
                        format!("no handler for effect '{l}'").as_str(),
                    )));
                }
                Err(HandlerError::HandlerFailed(msg)) => {
                    return Err(DnxError::PrimError(Arc::from(msg.as_str())));
                }
            };
            let p = crate::prim::alloc_prim_val(net, prim_state, val)?;
            net.connect(p, req.continuation, req.lo)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    struct ConstHandler(PrimValue);
    impl EffectHandler for ConstHandler {
        fn handle(&self, _: &[PrimValue]) -> Result<HandlerResult, HandlerError> {
            Ok(HandlerResult::Resume(self.0.clone()))
        }
    }

    #[test]
    fn effect_row_union() {
        let a = EffectRow::single("io");
        let b = EffectRow::single("nix.store");
        let c = EffectRow::union(&a, &b);
        assert_eq!(c.labels.len(), 2);
        assert!(!c.is_pure());
    }

    #[test]
    fn validate_handlers_ok() {
        let mut env = HandlerEnv::new();
        env.register("io", Box::new(ConstHandler(PrimValue::Null)));
        let row = EffectRow::single("io");
        assert!(validate_handlers(&env, &row).is_ok());
    }

    #[test]
    fn validate_handlers_missing() {
        let env = HandlerEnv::new();
        let row = EffectRow::single("io");
        assert!(matches!(
            validate_handlers(&env, &row),
            Err(HandlerError::NoHandler(_))
        ));
    }

    #[test]
    fn effect_row_pure() {
        assert!(EffectRow::pure().is_pure());
        assert!(!EffectRow::single("io").is_pure());
    }
}
