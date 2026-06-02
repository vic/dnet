#![forbid(unsafe_code)]
//! `dnx-pyparse` — a minimal Python-like surface language that lowers to the
//! *same* Dnx core IR (`dnx_ast::Ast<NixPrimVal, NixPrimFun>`) as `dnx`, and
//! evaluates on the *same* engine (parse → pass0 → pass1 → elaborate → reduce →
//! readback). This is the "one substrate, many languages" demo: a Python
//! `derivation(...)` and a Nix `derivationStrict {...}` reduce to the identical
//! derivation attrset.
//!
//! ## Supported subset (non-recursive)
//! - literals: `int`, `float`, `True`/`False`, `str`, `None`
//! - arithmetic `+ - * /`, comparisons `== != < <= > >=`, `and`/`or`/`not`
//! - ternary `A if C else B`
//! - `lambda x: e` and `def f(x): return e` (single param, single-line body)
//! - calls `f(x, y)` (curried), lists `[...]`, dicts `{ "k": v }`
//! - attribute `e.name` and subscript `e[k]` (attrset/dict access)
//! - f-strings `f"pre{e}post"` → the same interpolation core as Nix `"pre${e}post"`
//! - `derivation(name=..., builder=..., ...)` → the same `derivationStrict` primop
//!
//! ## Out of scope (engine/scope limits)
//! Loops, recursion (the engine diverges on genuine recursion), comprehensions,
//! multi-statement function bodies, classes, and general keyword arguments.

mod ast;
mod error;
mod lexer;
mod lower;
mod parser;
pub mod runtime;

pub use error::PyError;
pub use runtime::{PyEvalResult, PyRuntime};
