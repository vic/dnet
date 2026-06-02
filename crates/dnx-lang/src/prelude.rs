/// Nix list prelude: builtins defined in Nix, Scott-encoded, supplied to pass0
/// as a def map. References are inlined where used (unused = zero cost), so the
/// list machinery never weighs on programs that ignore it. Recursion goes
/// through `fix` (pass0 rejects bare def cycles), not self-application.
///
/// Scott encoding: `nil = c: n: n`, `cons h t = c: n: c h t` — pure lambdas,
/// lazy via call-by-need, like Church booleans.
use crate::parser::{nix_to_expr, E};
use crate::scope::Name;
use std::collections::HashMap;
use std::sync::Arc;

/// (name, Nix source of the definition body).
const DEFS: &[(&str, &str)] = &[
    // Thin wrapper over the `derivationStrict` primop, mirroring cppNix's
    // `builtins.derivation` (a `.nix` wrapper). No-list passthrough; defaults
    // like `outputs = ["out"]` are applied later by `dnx-drv::from_attrs`.
    ("derivation", "drv: derivationStrict drv"),
    ("nil", "c: n: n"),
    ("cons", "h: t: c: n: c h t"),
    ("head", "xs: xs (h: t: h) nil"),
    ("tail", "xs: xs (h: t: t) nil"),
    ("isNil", "xs: xs (h: t: false) true"),
    (
        "length",
        "xs: (fix (self: ys: acc: ys (h: t: self t (acc + 1)) acc)) xs 0",
    ),
    (
        "elemAt",
        "xs: i: (fix (self: ys: j: ys (h: t: if j == i then h else self t (j + 1)) nil)) xs 0",
    ),
    (
        "elem",
        "x: xs: (fix (self: ys: ys (h: t: if h == x then true else self t) false)) xs",
    ),
    (
        "concat",
        "a: b: (fix (self: xs: xs (h: t: cons h (self t)) b)) a",
    ),
    (
        "map",
        "f: xs: (fix (self: ys: ys (h: t: cons (f h) (self t)) nil)) xs",
    ),
    (
        "filter",
        "pred: xs: (fix (self: ys: ys (h: t: if pred h then cons h (self t) else self t) nil)) xs",
    ),
    (
        "foldl'",
        "op: acc: xs: (fix (self: a: ys: ys (h: t: self (op a h) t) a)) acc xs",
    ),
    (
        "genList",
        "gen: count: (fix (self: i: if i < count then cons (gen i) (self (i + 1)) else nil)) 0",
    ),
    (
        "concatMap",
        "f: xs: (fix (self: ys: ys (h: t: concat (f h) (self t)) nil)) xs",
    ),
];

/// Names defined by the prelude — used by the parser to route unbound
/// identifiers to `Ast::Name` (inlined by pass0) instead of `Builtin`.
pub(crate) fn is_prelude_name(name: &str) -> bool {
    DEFS.iter().any(|(n, _)| *n == name)
}

/// Parse each definition body into an AST, keyed by name. Errors are
/// impossible for the fixed source unless the prelude itself is malformed.
pub(crate) fn defs() -> Result<HashMap<Name, E>, crate::error::NixError> {
    let mut m = HashMap::with_capacity(DEFS.len());
    for (name, src) in DEFS {
        m.insert(Arc::from(*name), nix_to_expr(src)?);
    }
    Ok(m)
}
