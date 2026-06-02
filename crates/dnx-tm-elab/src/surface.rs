//! Surface IR — the `fix`/`match` we accept (spec §1:38-47). NOT core `Tm`: this is the
//! UNTRUSTED translator's input, mirroring exactly Coq's primitive `fix f /aᵢ . λ a⃗. <match aᵢ>`
//! (Rocq refman desugaring, A005:74). The inductive + motive are ALREADY resolved by the
//! source frontend (no metavars, no motive inference here — spec §1:50, ⚑V2).

use dnx_proof::symbol::IndId;
use dnx_proof::tm::Tm;

/// A surface term. de Bruijn indices follow core `Tm` (0 = innermost binder). Only the shapes
/// that can CONTAIN a self-call or a `match` are surface nodes; every other core shape
/// (Sort/Pi/Const/Ind/Ctor) is a `Core` leaf that lowers 1:1 (spec §1:39 "pass through").
#[derive(Clone, Debug)]
pub enum SrcTm {
    /// A bound variable. Inside a `Fix.body`, `Var(n)` may refer to the recursive self `f`
    /// (the binder the `fix` introduces just outside `body`).
    Var(u32),
    /// Application; `App*` spines carry self-calls `f … rec_j …` that §3c rewrites to IHs.
    App(Box<SrcTm>, Box<SrcTm>),
    /// λ binder (`dom` is a core type, `body` binds 1). The `fix` body is `λ a₁..aₙ. <…match…>`.
    Lam(Tm, Box<SrcTm>),
    /// Already-core subterm (Sort/Pi/Const/Ind/Ctor or any closed core fragment): lowers 1:1.
    Core(Tm),
    /// Structural `Fixpoint f a₁..aₙ {struct aᵢ} : ty := body` (spec §1:40-43).
    Fix(Fix),
    /// `match scrut return motive with | C_k x⃗ ⇒ rhs_k end` (spec §1:44-47).
    Match(Match),
}

/// `Fix{rec_arg, ty, body}` (spec §1:40-43). `body = λ a₁..aₙ. <…match a_{rec_arg}…>` where the
/// outermost binder (one level above `body`) is the recursive self `f`.
#[derive(Clone, Debug)]
pub struct Fix {
    /// The `{struct aᵢ}` position: index (0-based, left→right) of the decreasing arg.
    pub rec_arg: usize,
    /// Full fix type `Π a₁..aₙ. T` (core).
    pub ty: Tm,
    /// `λ a₁..aₙ. <body>` (surface; the match on the decreasing arg lives inside).
    pub body: Box<SrcTm>,
}

/// `Match{scrut, ind, motive, arms}` (spec §1:44-47).
#[derive(Clone, Debug)]
pub struct Match {
    /// The term being matched (surface).
    pub scrut: Box<SrcTm>,
    /// Which inductive (resolved by the source frontend's type-check).
    pub ind: IndId,
    /// Return-type motive `Π(X)(x:I P X). Sort` (core; carried from the source — spec §1:52).
    pub motive: Tm,
    /// One arm per ctor, IN ctor order (spec §1:46).
    pub arms: Vec<SrcArm>,
}

/// `SrcArm{ctor_ix, binders, rhs}` (spec §1:47): `binders` = the ctor field telescope.
#[derive(Clone, Debug)]
pub struct SrcArm {
    pub ctor_ix: u32,
    /// Ctor field binder types (must MATCH `ctors[k].args` arity — else reject, spec §4:124).
    pub binders: Vec<Tm>,
    /// Right-hand side (surface; self-calls on recursive fields become IHs — spec §3c).
    pub rhs: Box<SrcTm>,
}
