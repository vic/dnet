use crate::net::Net;
/// Phase C: Primitive functions and values.
/// Orthogonal to main.tex — never touches R1-R7.
use crate::{DnxError, LOPath, NetClassMarker, PortId, Proper};
use std::sync::Arc;

// Prim slot tags (alignment B3).
pub(crate) const TAG_PRIM_VAL: u8 = 0x0C; // PrimVal: 0b1100
pub(crate) const TAG_PRIM_FUN: u8 = 0x0D; // PrimFun: 0b1101

/// Runtime value: result of evaluating a Nix expression to normal form.
#[derive(Debug, Clone)]
pub enum PrimValue {
    Int(i64),
    Float(f64),
    Str(Arc<str>),
    Path(Arc<str>),
    Bool(bool),
    Null,
    List(Vec<PrimValue>),
    AttrSet(Vec<(Arc<str>, PrimValue)>), // sorted by key
    Closure(Box<PrimFunEntry>),
    Lambda, // opaque native FanAbs; type-inspection only (typeOf/isFunction/isBool)
}

impl PartialEq for PrimValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (PrimValue::Int(a), PrimValue::Int(b)) => a == b,
            (PrimValue::Float(a), PrimValue::Float(b)) => a.to_bits() == b.to_bits(),
            (PrimValue::Str(a), PrimValue::Str(b)) => a == b,
            (PrimValue::Path(a), PrimValue::Path(b)) => a == b,
            (PrimValue::Bool(a), PrimValue::Bool(b)) => a == b,
            (PrimValue::Null, PrimValue::Null) => true,
            (PrimValue::List(a), PrimValue::List(b)) => a == b,
            (PrimValue::AttrSet(a), PrimValue::AttrSet(b)) => a == b,
            (PrimValue::Lambda, PrimValue::Lambda) => true,
            _ => false,
        }
    }
}

pub type PrimApplyFn = fn(&[PrimValue]) -> Result<PrimValue, DnxError>;

/// PrimImpl: whether a primitive is pure Rust or an effectful call.
#[derive(Debug, Clone)]
pub enum PrimImpl {
    Pure(PrimApplyFn),
    Effectful(Arc<str>), // effect label
}

/// A (possibly partially-applied) primitive function.
#[derive(Debug, Clone)]
pub struct PrimFunEntry {
    pub name: Arc<str>,
    pub arity_remaining: u8,
    pub captured: Vec<PrimValue>,
    pub impl_: PrimImpl,
}

/// Result of firing a prim rule.
pub enum PrimFireResult {
    Complete(PrimValue),
    Partial(PrimFunEntry),
    NetFragment(PortId),
    EffectSaturated(Arc<str>, Vec<PrimValue>),
    Error(String),
}

/// Global prim table (prim_id → entry).
pub struct PrimTable {
    pub names: Vec<Arc<str>>,
    pub impls: Vec<(u8, PrimImpl)>, // (arity, impl)
}

impl PrimTable {
    pub fn empty() -> Self {
        PrimTable {
            names: vec![],
            impls: vec![],
        }
    }

    pub fn register(&mut self, name: &str, arity: u8, impl_: PrimImpl) -> u16 {
        let id = self.names.len() as u16;
        self.names.push(Arc::from(name));
        self.impls.push((arity, impl_));
        id
    }

    pub fn lookup(&self, name: &str) -> Option<u16> {
        self.names
            .iter()
            .position(|n| n.as_ref() == name)
            .map(|i| i as u16)
    }

    pub fn make_entry(&self, prim_id: u16) -> Option<PrimFunEntry> {
        let (arity, impl_) = self.impls.get(prim_id as usize)?.clone();
        let name = self.names.get(prim_id as usize)?.clone();
        Some(PrimFunEntry {
            name,
            arity_remaining: arity,
            captured: vec![],
            impl_,
        })
    }
}

/// Side table for prim values in a net.
/// Indexed by prim_val_id (slot.data field).
#[derive(Default)]
pub struct PrimState {
    pub vals: Vec<PrimValue>,
    pub funs: Vec<PrimFunEntry>,
}

impl PrimState {
    pub fn alloc_val(&mut self, v: PrimValue) -> Result<u16, DnxError> {
        if self.vals.len() >= u16::MAX as usize {
            return Err(DnxError::ArenaCapacityExceeded);
        }
        let id = self.vals.len() as u16;
        self.vals.push(v);
        Ok(id)
    }

    pub fn alloc_fun(&mut self, entry: PrimFunEntry) -> Result<u16, DnxError> {
        if self.funs.len() >= u16::MAX as usize {
            return Err(DnxError::ArenaCapacityExceeded);
        }
        let id = self.funs.len() as u16;
        self.funs.push(entry);
        Ok(id)
    }
}

/// Allocate a PrimVal slot. Returns its principal port.
pub fn alloc_prim_val<C: NetClassMarker>(
    net: &mut Net<Proper, C>,
    prim_state: &mut PrimState,
    value: PrimValue,
) -> Result<PortId, DnxError> {
    let val_id = prim_state.alloc_val(value)?;
    let ports = net.alloc_agent(TAG_PRIM_VAL, val_id, 0, 0)?;
    Ok(ports.principal)
}

/// Allocate a PrimFun slot. Returns its principal port.
pub fn alloc_prim_fun<C: NetClassMarker>(
    net: &mut Net<Proper, C>,
    prim_state: &mut PrimState,
    entry: PrimFunEntry,
) -> Result<PortId, DnxError> {
    let fun_id = prim_state.alloc_fun(entry)?;
    let ports = net.alloc_agent(TAG_PRIM_FUN, fun_id, 0, 0)?;
    Ok(ports.principal)
}

/// Emit Church-encoded boolean as native FanAbs subnet.
/// true  = λt.λe.t  (inner var_e erased)
/// false = λt.λe.e  (outer var_t erased)
pub fn emit_church_bool<C: NetClassMarker>(
    net: &mut Net<Proper, C>,
    b: bool,
) -> Result<PortId, DnxError> {
    let lo = LOPath::root();
    let outer = net.alloc_abs()?; // λt
    let inner = net.alloc_abs()?; // λe
    net.connect(outer.aux0, inner.principal, lo.clone())?;
    if b {
        // body = t: inner.aux0 → outer.aux1 (var_t); var_e erased
        net.connect(inner.aux0, outer.aux1, lo.clone())?;
        net.connect(inner.aux1, Net::<Proper, C>::eraser_port(), lo)?;
    } else {
        // body = e: inner.aux0 → inner.aux1 (var_e); var_t erased
        net.connect(inner.aux0, inner.aux1, lo.clone())?;
        net.connect(outer.aux1, Net::<Proper, C>::eraser_port(), lo)?;
    }
    Ok(outer.principal)
}

/// Recognize a Church-encoded boolean from a FanAbs port in the net.
/// true  = λt.λe.t: outer.aux0→inner FanAbs; inner.aux1 is eraser.
/// false = λt.λe.e: outer.aux0→inner FanAbs; outer.aux1 is eraser.
/// Returns None if p is not a Church-bool (user lambda or other shape).
pub fn try_church_bool<C: NetClassMarker>(net: &Net<Proper, C>, p: PortId) -> Option<bool> {
    let outer = net.slot_view(p);
    if !outer.is_fan() || !outer.fan_is_abs() {
        return None;
    }
    let inner_p = PortId::from_raw(outer.aux0);
    if !net.slot_is_live(inner_p) {
        return None;
    }
    let inner = net.slot_view(inner_p);
    if !inner.is_fan() || !inner.fan_is_abs() {
        return None;
    }
    if PortId::from_raw(inner.aux1).is_eraser() {
        return Some(true);
    }
    if PortId::from_raw(outer.aux1).is_eraser() {
        return Some(false);
    }
    None
}

/// prim_apply: dispatch rule for PrimFun⊗PrimVal.
/// Continuation taken from PrimFun.principal field.
pub fn prim_apply<C: NetClassMarker>(
    net: &mut Net<Proper, C>,
    prim_state: &mut PrimState,
    p_fun: PortId, // PrimFun principal
    p_arg: PortId, // PrimVal principal
    lo: &LOPath,
) -> Result<(), DnxError> {
    let fun_view = net.slot_view(p_fun);
    let cont_port = PortId::from_raw(fun_view.principal);
    prim_apply_inner(net, prim_state, p_fun, p_arg, cont_port, lo)
}

/// prim_apply_with_cont: App⊗PrimFun rule — explicit continuation.
/// Call after retiring the App node.
pub fn prim_apply_with_cont<C: NetClassMarker>(
    net: &mut Net<Proper, C>,
    prim_state: &mut PrimState,
    p_fun: PortId, // PrimFun principal
    p_arg: PortId, // PrimVal principal
    cont: PortId,  // explicit continuation (App.aux0's peer)
    lo: &LOPath,
) -> Result<(), DnxError> {
    prim_apply_inner(net, prim_state, p_fun, p_arg, cont, lo)
}

fn prim_apply_inner<C: NetClassMarker>(
    net: &mut Net<Proper, C>,
    prim_state: &mut PrimState,
    p_fun: PortId,
    p_arg: PortId,
    cont_port: PortId,
    lo: &LOPath,
) -> Result<(), DnxError> {
    let fun_view = net.slot_view(p_fun);
    let fun_id = fun_view.data;
    let entry = prim_state
        .funs
        .get(fun_id as usize)
        .ok_or(DnxError::ReadbackIncomplete)?
        .clone();

    let arg_view = net.slot_view(p_arg);
    if !arg_view.is_prim() || arg_view.tag == TAG_PRIM_FUN {
        return Err(DnxError::ReadbackIncomplete);
    }
    let val_id = arg_view.data;
    let arg_val = prim_state
        .vals
        .get(val_id as usize)
        .ok_or(DnxError::ReadbackIncomplete)?
        .clone();

    net.retire(p_fun.slot_idx());
    net.retire(p_arg.slot_idx());

    let mut new_captured = entry.captured.clone();
    new_captured.push(arg_val);

    if entry.arity_remaining > 1 {
        // Partial application: emit new PrimFun.
        let new_entry = PrimFunEntry {
            name: entry.name.clone(),
            arity_remaining: entry.arity_remaining - 1,
            captured: new_captured,
            impl_: entry.impl_.clone(),
        };
        let new_p = alloc_prim_fun(net, prim_state, new_entry)?;
        net.connect(new_p, cont_port, lo.clone())?;
    } else {
        // Saturated: fire.
        match &entry.impl_ {
            PrimImpl::Pure(f) => match f(&new_captured) {
                Ok(result) => {
                    let new_p = alloc_prim_val(net, prim_state, result)?;
                    net.connect(new_p, cont_port, lo.clone())?;
                }
                Err(e) => return Err(e),
            },
            PrimImpl::Effectful(_label) => {
                // Phase C: trampoline for Tier-1 effects — emit EffectSaturated, halt.
                return Err(DnxError::ReadbackIncomplete); // placeholder
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{LOPath, Proper, ΔL};

    fn add_fn(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
        match args {
            [PrimValue::Int(a), PrimValue::Int(b)] => Ok(PrimValue::Int(a + b)),
            _ => Err(DnxError::ReadbackIncomplete),
        }
    }

    #[test]
    fn prim_table_register_lookup() {
        let mut t = PrimTable::empty();
        let id = t.register("add", 2, PrimImpl::Pure(add_fn));
        assert_eq!(id, 0);
        assert_eq!(t.lookup("add"), Some(0));
    }

    #[test]
    fn prim_state_alloc() {
        let mut ps = PrimState::default();
        let id = ps.alloc_val(PrimValue::Int(42)).unwrap();
        assert_eq!(id, 0);
        assert_eq!(ps.vals[0], PrimValue::Int(42));
    }

    // prim_apply is called with p_fun = PrimFun.principal, p_arg = PrimVal.principal.
    // For the test: manually set fun_slot.principal = result (the continuation).
    // Then prim_apply reads cont_port from fun_slot.principal.
    #[test]
    fn prim_apply_add_fires() {
        let mut net = Net::<Proper, ΔL>::new(32);
        let mut ps = PrimState::default();
        let entry = PrimFunEntry {
            name: Arc::from("add1"),
            arity_remaining: 1,
            captured: vec![PrimValue::Int(2)],
            impl_: PrimImpl::Pure(add_fn),
        };
        let fun_p = alloc_prim_fun(&mut net, &mut ps, entry).unwrap();
        let val_p = alloc_prim_val(&mut net, &mut ps, PrimValue::Int(3)).unwrap();
        let result = net.alloc_free(0).unwrap();
        // Wire: result ← fun (fun stores result as continuation in principal field).
        // fun_slot.principal = result: done by write_port.
        // val_slot.principal = fun: done by write_port.
        // But DON'T use connect() (creates active pairs). Use link_no_pair.
        net.link_no_pair(fun_p, result); // fun_slot.principal = result; result_slot.principal = fun_p
                                         // Now manually connect val to fun for the active pair.
                                         // But prim_apply is called DIRECTLY with known ports, not via frontier.
                                         // fun_slot.principal was just set to result by link_no_pair.
        prim_apply(&mut net, &mut ps, fun_p, val_p, &LOPath::root()).unwrap();
        // After: new PrimVal connected to result.
        let result_peer = net.peer(result);
        assert!(!result_peer.is_null(), "result should be connected");
        let s = net.slot_view(result_peer);
        assert!(s.is_prim(), "result should be PrimVal");
        assert_eq!(s.tag, TAG_PRIM_VAL, "tag should be PrimVal 0x0C");
        let val = &ps.vals[s.data as usize];
        assert_eq!(*val, PrimValue::Int(5), "2 + 3 = 5");
    }
}
