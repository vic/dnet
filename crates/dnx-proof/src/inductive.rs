use crate::symbol::IndId;
use crate::tm::{Level, Telescope, Tm};

#[derive(Clone, Debug)]
pub struct Inductive {
    pub id: IndId,
    pub params: Telescope,
    pub indices: Telescope,
    pub sort: Level,
    pub ctors: Vec<CtorDecl>,
}

#[derive(Clone, Debug)]
pub struct CtorDecl {
    pub ctor_ix: u32,
    pub args: Telescope,
    pub ret_indices: Vec<Tm>,
}

#[derive(Clone, Debug)]
pub struct ArityTable {
    pub ind: IndId,
    pub nparams: u32,
    pub nindices: u32,
    pub ctors: Vec<CtorArity>,
}

#[derive(Clone, Debug)]
pub struct CtorArity {
    pub ctor_ix: u32,
    pub nfields: u32,
    pub nrec: u32,
}
