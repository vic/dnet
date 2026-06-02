use std::sync::Arc;

pub(crate) type PyName = Arc<str>;

/// Binary operators of the supported subset.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    In,
    And,
    Or,
}

/// Minimal Python surface expression. Recursion/loops/comprehensions are out of
/// scope; `Deriv` is the single keyword-argument form (`derivation(name=...)`).
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum PyExpr {
    Int(i64),
    Float(f64),
    Str(Arc<str>),
    /// `f"pre{e}post"` — alternating literal text and interpolated expressions,
    /// in source order. Mirrors Nix interpolation `"pre${e}post"`.
    FStr(Vec<FStrPart>),
    Bool(bool),
    None_,
    Name(PyName),
    Lambda(PyName, Box<PyExpr>),
    Call(Box<PyExpr>, Vec<PyExpr>),
    Deriv(Vec<(PyName, PyExpr)>),
    BinOp(BinOp, Box<PyExpr>, Box<PyExpr>),
    Neg(Box<PyExpr>),
    Not(Box<PyExpr>),
    /// `then if cond else otherwise` (Python ternary order).
    IfExp(Box<PyExpr>, Box<PyExpr>, Box<PyExpr>),
    List(Vec<PyExpr>),
    Dict(Vec<(PyExpr, PyExpr)>),
    Index(Box<PyExpr>, Box<PyExpr>),
    Attr(Box<PyExpr>, PyName),
}

/// One segment of an f-string: literal text or an interpolated expression.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum FStrPart {
    Lit(Arc<str>),
    Hole(Box<PyExpr>),
}

/// A top-level statement. A module is a sequence of these; the final statement
/// must be an expression (the value the module evaluates to).
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum PyStmt {
    Assign(PyName, PyExpr),
    /// `def name(param): return body` — single-parameter, single-line body.
    Def(PyName, PyName, PyExpr),
    Expr(PyExpr),
}
