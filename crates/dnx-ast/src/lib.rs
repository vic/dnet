#![forbid(unsafe_code)]

use std::sync::Arc;

pub type Name = Arc<str>;

pub trait PrimVal: std::fmt::Debug + Clone + PartialEq {}
pub trait PrimFun: std::fmt::Debug + Clone + PartialEq {}

/// Empty PrimVal/PrimFun for nets with no primitive values.
#[derive(Debug, Clone, PartialEq)]
pub struct NoVal;
#[derive(Debug, Clone, PartialEq)]
pub struct NoFun;
impl PrimVal for NoVal {}
impl PrimFun for NoFun {}

/// Core Dnx AST. Produced by frontends; consumed by elaborator.
#[derive(Debug, Clone, PartialEq)]
pub enum Ast<V: PrimVal, F: PrimFun> {
    Name(Name),
    Abs(Name, Box<Ast<V, F>>),
    App(Box<Ast<V, F>>, Box<Ast<V, F>>),
    Rep(Box<Ast<V, F>>, Name, Name, Box<Ast<V, F>>),
    Era(Box<Ast<V, F>>, Box<Ast<V, F>>),
    Fix(Box<Ast<V, F>>),
    Val(V),
    Fun(F),
    Perform(Name, Box<Ast<V, F>>),
    Handle(Box<Ast<V, F>>, Vec<HandlerBranch<V, F>>),
}

/// One handler branch: `label x k → body`.
#[derive(Debug, Clone, PartialEq)]
pub struct HandlerBranch<V: PrimVal, F: PrimFun> {
    pub label: Name,
    pub arg_name: Name,
    pub k_name: Name,
    pub body: Box<Ast<V, F>>,
}

/// Opaque type annotation placeholder; erased by phi_k before elaboration.
#[derive(Debug, Clone, PartialEq)]
pub struct Type;

/// Typed surface AST from frontends; desugars to `Ast` via phi_k.
#[derive(Debug, Clone, PartialEq)]
pub enum LambdaAst<V: PrimVal, F: PrimFun> {
    Var(Name),
    Abs(Name, Box<LambdaAst<V, F>>),
    App(Box<LambdaAst<V, F>>, Box<LambdaAst<V, F>>),
    Let {
        bindings: Vec<(Name, Box<LambdaAst<V, F>>)>,
        body: Box<LambdaAst<V, F>>,
    },
    Val(V),
    Fun(F),
    Ann(Box<LambdaAst<V, F>>, Type),
    Perform(Name, Box<LambdaAst<V, F>>),
    Handle(Box<LambdaAst<V, F>>, Vec<HandlerBranch<V, F>>),
}
