//! Lower the Python surface AST to the shared core `Ast<NixPrimVal, NixPrimFun>`
//! — the exact IR `dnx-lang` produces. Every construct mirrors a Nix
//! lowering so both languages elaborate to the same net (one substrate):
//! list = cons-fold (collections.rs:11), dict = Insert-fold (collections.rs:28),
//! ternary/and/or = Church-bool application (binding.rs:83, literals.rs:57),
//! binop = `App(App(Fun, l), r)` (literals.rs:95), lambda = `Abs` with rep/era
//! multiplicity wrapping (lambda.rs:64, helpers.rs:11).

use crate::ast::{BinOp, FStrPart, PyExpr, PyName, PyStmt};
use crate::error::PyError;
use dnx_ast::Ast;
use dnx_prim::prim::{NixPrimFun, NixPrimVal};
use std::collections::HashSet;
use std::sync::Arc;

/// The shared core expression type (identical to `dnx-lang`'s `E`).
type E = Ast<NixPrimVal, NixPrimFun>;

/// Lower a module to a single core expression. Statements desugar to nested
/// `let` (an immediately-applied lambda per binding, mirroring Nix `let`):
/// `x = v; <rest>` becomes `(λx. <rest>) v`. The final statement supplies the
/// value; a trailing non-expression statement is rejected.
pub(crate) fn lower_module(stmts: &[PyStmt], bound: &mut HashSet<PyName>) -> Result<E, PyError> {
    let (last, init) = stmts
        .split_last()
        .ok_or_else(|| PyError::Parse("empty module".into()))?;
    let body_expr = match last {
        PyStmt::Expr(e) => e.clone(),
        PyStmt::Assign(..) | PyStmt::Def(..) => {
            return Err(PyError::Unsupported(
                "module must end in an expression".into(),
            ))
        }
    };
    // Bind every statement name first (Nix `let` is recursive in scope; we keep
    // it simple — names are visible to later statements, sufficient for the
    // non-recursive subset). Then lower bodies and the trailing expression.
    let names: Vec<(PyName, &PyExpr, Option<PyName>)> = init
        .iter()
        .map(|s| match s {
            PyStmt::Assign(n, v) => Ok((n.clone(), v, None)),
            PyStmt::Def(n, p, b) => Ok((n.clone(), b, Some(p.clone()))),
            PyStmt::Expr(_) => Err(PyError::Unsupported(
                "expression statement before module end is discarded".into(),
            )),
        })
        .collect::<Result<_, _>>()?;
    for (n, _, _) in &names {
        bound.insert(n.clone());
    }
    let mut lowered: Vec<(PyName, E)> = Vec::with_capacity(names.len());
    for (n, body, param) in &names {
        let val = match param {
            None => lower_expr(body, bound)?,
            Some(p) => lower_lambda(p, body, bound)?,
        };
        lowered.push((n.clone(), val));
    }
    let mut body = lower_expr(&body_expr, bound)?;
    for (n, val) in lowered.into_iter().rev() {
        let uses = count_uses_in(&body, &n);
        let wrapped = wrap_uses(n.clone(), uses, body);
        body = Ast::App(Box::new(Ast::Abs(n, Box::new(wrapped))), Box::new(val));
    }
    Ok(body)
}

fn lower_expr(e: &PyExpr, bound: &mut HashSet<PyName>) -> Result<E, PyError> {
    Ok(match e {
        PyExpr::Int(n) => Ast::Val(NixPrimVal::Int(*n)),
        PyExpr::Float(f) => Ast::Val(NixPrimVal::Float(*f)),
        PyExpr::Str(s) => Ast::Val(NixPrimVal::Str(s.clone())),
        PyExpr::FStr(parts) => lower_fstring(parts, bound)?,
        PyExpr::Bool(b) => Ast::Val(NixPrimVal::Bool(*b)),
        PyExpr::None_ => Ast::Val(NixPrimVal::Null),
        PyExpr::Name(n) => lower_name(n, bound),
        PyExpr::Lambda(p, body) => lower_lambda(p, body, bound)?,
        PyExpr::Neg(e) => Ast::App(
            Box::new(Ast::Fun(NixPrimFun::Neg)),
            Box::new(lower_expr(e, bound)?),
        ),
        PyExpr::Not(e) => {
            // Church-bool invert: `b false true` (literals.rs:123).
            let b = lower_expr(e, bound)?;
            app2(b, false_val(), true_val())
        }
        PyExpr::BinOp(op, l, r) => lower_binop(*op, l, r, bound)?,
        PyExpr::IfExp(cond, then, els) => {
            // Church-bool elimination: `cond then else` (binding.rs:83).
            let c = lower_expr(cond, bound)?;
            let t = lower_expr(then, bound)?;
            let e = lower_expr(els, bound)?;
            app2(c, t, e)
        }
        PyExpr::Call(f, args) => {
            let mut acc = lower_expr(f, bound)?;
            for a in args {
                acc = Ast::App(Box::new(acc), Box::new(lower_expr(a, bound)?));
            }
            acc
        }
        PyExpr::Deriv(kwargs) => {
            // `derivation(name=.., builder=..)` == Nix `derivationStrict { .. }`:
            // build the same attrset, apply the same primop (prim.rs:502).
            let set = lower_attrset(kwargs, bound)?;
            Ast::App(
                Box::new(Ast::Fun(NixPrimFun::Builtin(Arc::from("derivationStrict")))),
                Box::new(set),
            )
        }
        PyExpr::List(items) => lower_list(items, bound)?,
        PyExpr::Dict(pairs) => lower_dict(pairs, bound)?,
        PyExpr::Index(e, key) => {
            // Attrset-style access `d[k]` → Select (collections.rs:96); list
            // integer indexing is out of scope (use `elemAt`).
            let set = lower_expr(e, bound)?;
            let k = lower_expr(key, bound)?;
            app2(Ast::Fun(NixPrimFun::Select), set, k)
        }
        PyExpr::Attr(e, name) => {
            let set = lower_expr(e, bound)?;
            app2(
                Ast::Fun(NixPrimFun::Select),
                set,
                Ast::Val(NixPrimVal::Str(name.clone())),
            )
        }
    })
}

/// A bound name lowers to a variable reference; a free name lowers to a builtin
/// primop (mirrors `translate_ident`, lambda.rs:23). The prelude names (`cons`,
/// `head`, …) are injected by `pass0` from the def map, so they resolve as
/// `Ast::Name` too — but only when the program actually binds them. Here a free
/// name is assumed to be a builtin; prelude lookups happen via the def map.
fn lower_name(n: &PyName, bound: &HashSet<PyName>) -> E {
    if bound.contains(n) {
        Ast::Name(n.clone())
    } else {
        Ast::Fun(NixPrimFun::Builtin(n.clone()))
    }
}

fn lower_lambda(param: &PyName, body: &PyExpr, bound: &mut HashSet<PyName>) -> Result<E, PyError> {
    let fresh = !bound.contains(param);
    bound.insert(param.clone());
    let body_e = lower_expr(body, bound)?;
    if fresh {
        bound.remove(param);
    }
    let uses = count_uses_in(&body_e, param);
    Ok(Ast::Abs(
        param.clone(),
        Box::new(wrap_uses(param.clone(), uses, body_e)),
    ))
}

fn lower_binop(
    op: BinOp,
    l: &PyExpr,
    r: &PyExpr,
    bound: &mut HashSet<PyName>,
) -> Result<E, PyError> {
    let lhs = lower_expr(l, bound)?;
    let rhs = lower_expr(r, bound)?;
    Ok(match op {
        // Church-bool short-circuit forms (literals.rs:57-73).
        BinOp::And => app2(lhs, rhs, false_val()),
        BinOp::Or => app2(lhs, true_val(), rhs),
        // Python `key in set` is the same membership primop as Nix `set ? key`
        // (collections.rs:222); operands swap so the attrset comes first.
        BinOp::In => app2(Ast::Fun(NixPrimFun::HasAttr), rhs, lhs),
        // Python overloads `+`: list+list concatenates, scalar+scalar adds. The
        // substrate cannot dispatch at runtime — a Scott list is a FanAbs, so
        // `isList` cannot tell it from a function (dnx-read read_value.rs:72).
        // Two list literals are the unambiguous concat case: lower them through
        // the same prelude `concat` Nix `++` uses (literals.rs:142-149,
        // runtime.rs PRELUDE `concat`). Every other `+` stays `Add`, whose prim
        // already overloads Int/Float/Str (dnx-prim prim.rs:90-105).
        BinOp::Add if matches!((l, r), (PyExpr::List(_), PyExpr::List(_))) => {
            app2(Ast::Name(Arc::from("concat")), lhs, rhs)
        }
        _ => app2(Ast::Fun(arith_prim(op)), lhs, rhs),
    })
}

fn arith_prim(op: BinOp) -> NixPrimFun {
    match op {
        BinOp::Add => NixPrimFun::Add,
        BinOp::Sub => NixPrimFun::Sub,
        BinOp::Mul => NixPrimFun::Mul,
        BinOp::Div => NixPrimFun::Div,
        BinOp::Eq => NixPrimFun::Eq,
        BinOp::Ne => NixPrimFun::Ne,
        BinOp::Lt => NixPrimFun::Lt,
        BinOp::Le => NixPrimFun::Le,
        BinOp::Gt => NixPrimFun::Gt,
        BinOp::Ge => NixPrimFun::Ge,
        // And/Or/In never reach here (handled in lower_binop).
        BinOp::And | BinOp::Or | BinOp::In => NixPrimFun::Add,
    }
}

fn lower_list(items: &[PyExpr], bound: &mut HashSet<PyName>) -> Result<E, PyError> {
    // Fold-right into Scott `cons h (… nil)` (collections.rs:11).
    let mut acc: E = Ast::Name(Arc::from("nil"));
    for item in items.iter().rev() {
        let h = lower_expr(item, bound)?;
        acc = app2(Ast::Name(Arc::from("cons")), h, acc);
    }
    Ok(acc)
}

fn lower_dict(pairs: &[(PyExpr, PyExpr)], bound: &mut HashSet<PyName>) -> Result<E, PyError> {
    let mut kvs: Vec<(PyName, &PyExpr)> = Vec::with_capacity(pairs.len());
    for (k, v) in pairs {
        let key = match k {
            PyExpr::Str(s) => s.clone(),
            _ => {
                return Err(PyError::Unsupported(
                    "dict key must be a string literal".into(),
                ))
            }
        };
        kvs.push((key, v));
    }
    lower_attrset(
        &kvs.into_iter()
            .map(|(k, v)| (k, v.clone()))
            .collect::<Vec<_>>(),
        bound,
    )
}

/// Build an attrset by folding `Insert set "k" v` over `EmptyAttrSet`
/// (collections.rs:28) — the same shape Nix uses, so the resulting
/// `PrimValue::AttrSet` is identical given identical keys/values.
fn lower_attrset(kvs: &[(PyName, PyExpr)], bound: &mut HashSet<PyName>) -> Result<E, PyError> {
    let mut set: E = Ast::Fun(NixPrimFun::EmptyAttrSet);
    for (key, val) in kvs {
        let v = lower_expr(val, bound)?;
        set = Ast::App(
            Box::new(app2(
                Ast::Fun(NixPrimFun::Insert),
                set,
                Ast::Val(NixPrimVal::Str(key.clone())),
            )),
            Box::new(v),
        );
    }
    Ok(set)
}

/// Lower an f-string to the same core a Nix interpolated string produces
/// (dnx-lang literals.rs:24-54): literal parts are `Str` values, holes are
/// `toString`-coerced (`ToString2`), and segments are folded left with the wired
/// `+`. An empty f-string is the empty string.
fn lower_fstring(parts: &[FStrPart], bound: &mut HashSet<PyName>) -> Result<E, PyError> {
    let mut acc: Option<E> = None;
    for part in parts {
        let e = match part {
            FStrPart::Lit(s) => Ast::Val(NixPrimVal::Str(s.clone())),
            FStrPart::Hole(inner) => Ast::App(
                Box::new(Ast::Fun(NixPrimFun::ToString2)),
                Box::new(lower_expr(inner, bound)?),
            ),
        };
        acc = Some(match acc {
            Some(prev) => app2(Ast::Fun(NixPrimFun::Add), prev, e),
            None => e,
        });
    }
    Ok(acc.unwrap_or_else(|| Ast::Val(NixPrimVal::Str(Arc::from("")))))
}

fn app2(f: E, a: E, b: E) -> E {
    Ast::App(Box::new(Ast::App(Box::new(f), Box::new(a))), Box::new(b))
}

fn true_val() -> E {
    Ast::Val(NixPrimVal::Bool(true))
}

fn false_val() -> E {
    Ast::Val(NixPrimVal::Bool(false))
}

// ---- variable multiplicity (replicated from nixparse helpers.rs:11/77 —
// those are pub(super); these operate purely on the shared `Ast`) ----

fn wrap_uses(name: PyName, uses: u32, body: E) -> E {
    match uses {
        0 => Ast::Era(Box::new(Ast::Name(name)), Box::new(body)),
        1 => body,
        n => build_rep_chain(name, n as usize, body),
    }
}

fn build_rep_chain(name: PyName, uses: usize, body: E) -> E {
    if uses <= 1 {
        return body;
    }
    let split: Vec<PyName> = (0..uses)
        .map(|i| Arc::from(format!("{name}__{i}").as_str()))
        .collect();
    let mut idx = 0;
    let body = indexed_rename(body, &name, &split, &mut idx);
    nest_reps(Ast::Name(name), &split, body)
}

fn indexed_rename(expr: E, from: &PyName, names: &[PyName], idx: &mut usize) -> E {
    match expr {
        Ast::Name(n) if &n == from => {
            let r = names[*idx].clone();
            *idx += 1;
            Ast::Name(r)
        }
        Ast::Name(n) => Ast::Name(n),
        Ast::Abs(x, body) if &x == from => Ast::Abs(x, body),
        Ast::Abs(x, body) => Ast::Abs(x, Box::new(indexed_rename(*body, from, names, idx))),
        Ast::App(f, x) => Ast::App(
            Box::new(indexed_rename(*f, from, names, idx)),
            Box::new(indexed_rename(*x, from, names, idx)),
        ),
        Ast::Rep(e, a, b, body) => {
            let e2 = Box::new(indexed_rename(*e, from, names, idx));
            if &a == from || &b == from {
                Ast::Rep(e2, a, b, body)
            } else {
                Ast::Rep(e2, a, b, Box::new(indexed_rename(*body, from, names, idx)))
            }
        }
        Ast::Era(e, body) => Ast::Era(
            Box::new(indexed_rename(*e, from, names, idx)),
            Box::new(indexed_rename(*body, from, names, idx)),
        ),
        Ast::Fix(e) => Ast::Fix(Box::new(indexed_rename(*e, from, names, idx))),
        other => other,
    }
}

fn nest_reps(expr: E, names: &[PyName], body: E) -> E {
    if names.len() == 2 {
        Ast::Rep(
            Box::new(expr),
            names[0].clone(),
            names[1].clone(),
            Box::new(body),
        )
    } else {
        let rest: PyName = Arc::from(format!("__rr_{}", names[1]).as_str());
        let inner = nest_reps(Ast::Name(rest.clone()), &names[1..], body);
        Ast::Rep(Box::new(expr), names[0].clone(), rest, Box::new(inner))
    }
}

fn count_uses_in(expr: &E, name: &PyName) -> u32 {
    match expr {
        Ast::Name(n) if n == name => 1,
        Ast::Name(_) => 0,
        Ast::Abs(x, _) if x == name => 0,
        Ast::Abs(_, body) => count_uses_in(body, name),
        Ast::App(f, x) => count_uses_in(f, name) + count_uses_in(x, name),
        Ast::Rep(e, a, b, body) => {
            count_uses_in(e, name)
                + if a == name || b == name {
                    0
                } else {
                    count_uses_in(body, name)
                }
        }
        Ast::Era(e, body) => count_uses_in(e, name) + count_uses_in(body, name),
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    //! Parse → core-IR coverage. These pin the *shape* of the lowered
    //! `Ast<NixPrimVal, NixPrimFun>` for each construct, witnessing the
    //! "one substrate" claim: every Python form lowers to the same core term a
    //! Nix form would (citations to the mirrored Nix lowerings live in the
    //! module header). No evaluation engine is involved — pure lowering.
    use super::*;
    use crate::parser::parse_module;

    fn lower(src: &str) -> E {
        let stmts = parse_module(src).expect("parse");
        lower_module(&stmts, &mut HashSet::new()).expect("lower")
    }

    fn name(s: &str) -> E {
        Ast::Name(Arc::from(s))
    }

    fn int(n: i64) -> E {
        Ast::Val(NixPrimVal::Int(n))
    }

    #[test]
    fn literals_lower_to_prim_vals() {
        assert_eq!(lower("42"), Ast::Val(NixPrimVal::Int(42)));
        assert_eq!(lower("1.5"), Ast::Val(NixPrimVal::Float(1.5)));
        assert_eq!(lower(r#""hi""#), Ast::Val(NixPrimVal::Str(Arc::from("hi"))));
        assert_eq!(lower("True"), Ast::Val(NixPrimVal::Bool(true)));
    }

    #[test]
    fn none_lowers_to_null() {
        // Python `None` is the Nix `null` value — the same `PrimVal::Null`.
        assert_eq!(lower("None"), Ast::Val(NixPrimVal::Null));
    }

    #[test]
    fn arithmetic_lowers_to_prim_application() {
        // `1 + 2` == `App(App(Fun(Add), 1), 2)` — the binop shape Nix emits.
        assert_eq!(
            lower("1 + 2"),
            app2(Ast::Fun(NixPrimFun::Add), int(1), int(2))
        );
    }

    #[test]
    fn comparison_lowers_to_prim_application() {
        assert_eq!(
            lower("1 < 2"),
            app2(Ast::Fun(NixPrimFun::Lt), int(1), int(2))
        );
    }

    #[test]
    fn negation_lowers_to_neg_prim() {
        assert_eq!(
            lower("-5"),
            Ast::App(Box::new(Ast::Fun(NixPrimFun::Neg)), Box::new(int(5)))
        );
    }

    #[test]
    fn and_lowers_to_church_bool_select() {
        // `a and b` short-circuits via Church-bool application: `a b false`.
        assert_eq!(lower("True and False"), {
            app2(
                Ast::Val(NixPrimVal::Bool(true)),
                Ast::Val(NixPrimVal::Bool(false)),
                false_val(),
            )
        });
    }

    #[test]
    fn or_lowers_to_church_bool_select() {
        assert_eq!(lower("False or True"), {
            app2(
                Ast::Val(NixPrimVal::Bool(false)),
                true_val(),
                Ast::Val(NixPrimVal::Bool(true)),
            )
        });
    }

    #[test]
    fn not_lowers_to_church_bool_invert() {
        // `not b` == `b false true`.
        assert_eq!(
            lower("not True"),
            app2(Ast::Val(NixPrimVal::Bool(true)), false_val(), true_val())
        );
    }

    #[test]
    fn ifexp_lowers_to_church_bool_elim() {
        // `t if c else e` == `c t e` (Church-bool elimination).
        assert_eq!(
            lower("1 if True else 2"),
            app2(Ast::Val(NixPrimVal::Bool(true)), int(1), int(2))
        );
    }

    #[test]
    fn list_lowers_to_scott_cons_nil() {
        // `[1, 2]` == `cons 1 (cons 2 nil)` — the Scott encoding Nix lists use.
        assert_eq!(
            lower("[1, 2]"),
            app2(
                name("cons"),
                int(1),
                app2(name("cons"), int(2), name("nil"))
            )
        );
        assert_eq!(lower("[]"), name("nil"));
    }

    #[test]
    fn list_plus_list_lowers_to_concat() {
        // `[1] + [2]` dispatches to prelude `concat` (mirrors Nix `++`,
        // literals.rs:142-149), NOT `Add`. The list operands are themselves
        // Scott `cons`/`nil` terms.
        let l = app2(name("cons"), int(1), name("nil"));
        let r = app2(name("cons"), int(2), name("nil"));
        assert_eq!(lower("[1] + [2]"), app2(name("concat"), l, r));
    }

    #[test]
    fn scalar_plus_stays_add() {
        // Only two list literals route to `concat`; `+` on anything else stays
        // `Add` (string concat / arithmetic via the overloaded prim).
        assert_eq!(
            lower("1 + 2"),
            app2(Ast::Fun(NixPrimFun::Add), int(1), int(2))
        );
        assert_eq!(
            lower(r#""a" + "b""#),
            app2(
                Ast::Fun(NixPrimFun::Add),
                Ast::Val(NixPrimVal::Str(Arc::from("a"))),
                Ast::Val(NixPrimVal::Str(Arc::from("b"))),
            )
        );
    }

    #[test]
    fn fstring_lowers_like_nix_interpolation() {
        // `f"v={1}"` == `Add(Str"v=", toString 1)` — the same core a Nix
        // interpolated string yields (dnx-lang literals.rs:24-54).
        assert_eq!(
            lower(r#"f"v={1}""#),
            app2(
                Ast::Fun(NixPrimFun::Add),
                Ast::Val(NixPrimVal::Str(Arc::from("v="))),
                Ast::App(Box::new(Ast::Fun(NixPrimFun::ToString2)), Box::new(int(1))),
            )
        );
    }

    #[test]
    fn empty_fstring_lowers_to_empty_str() {
        assert_eq!(lower(r#"f"""#), Ast::Val(NixPrimVal::Str(Arc::from(""))));
    }

    #[test]
    fn dict_lowers_to_insert_fold() {
        // `{"a": 1}` == `Insert EmptyAttrSet "a" 1` — the attrset shape Nix uses.
        let expected = Ast::App(
            Box::new(app2(
                Ast::Fun(NixPrimFun::Insert),
                Ast::Fun(NixPrimFun::EmptyAttrSet),
                Ast::Val(NixPrimVal::Str(Arc::from("a"))),
            )),
            Box::new(int(1)),
        );
        assert_eq!(lower(r#"{"a": 1}"#), expected);
    }

    #[test]
    fn dict_non_string_key_is_unsupported() {
        let stmts = parse_module("{1: 2}").expect("parse");
        assert!(matches!(
            lower_module(&stmts, &mut HashSet::new()),
            Err(PyError::Unsupported(_))
        ));
    }

    #[test]
    fn attr_and_index_lower_to_select() {
        // Both `e.a` and `e["a"]` are `Select e "a"`.
        let key = Ast::Val(NixPrimVal::Str(Arc::from("a")));
        let via_attr = lower("e.a");
        let via_index = lower(r#"e["a"]"#);
        assert_eq!(
            via_attr,
            app2(
                Ast::Fun(NixPrimFun::Select),
                Ast::Fun(NixPrimFun::Builtin(Arc::from("e"))),
                key.clone(),
            )
        );
        assert_eq!(via_attr, via_index);
    }

    #[test]
    fn membership_lowers_to_has_attr_swapped() {
        // `"a" in d` == `HasAttr d "a"` — operands swap so the attrset is first,
        // matching Nix `d ? a` (collections.rs:222).
        assert_eq!(
            lower(r#""a" in d"#),
            app2(
                Ast::Fun(NixPrimFun::HasAttr),
                Ast::Fun(NixPrimFun::Builtin(Arc::from("d"))),
                Ast::Val(NixPrimVal::Str(Arc::from("a"))),
            )
        );
    }

    #[test]
    fn free_name_lowers_to_builtin() {
        // An unbound name is a builtin primop reference (mirrors translate_ident).
        assert_eq!(
            lower("toString"),
            Ast::Fun(NixPrimFun::Builtin(Arc::from("toString")))
        );
    }

    #[test]
    fn lambda_lowers_to_abs() {
        // `lambda x: x` — single use, no rep/era wrapping: `Abs("x", Name x)`.
        assert_eq!(
            lower("lambda x: x"),
            Ast::Abs(Arc::from("x"), Box::new(name("x")))
        );
    }

    #[test]
    fn unused_lambda_param_is_erased() {
        // `lambda x: 1` never uses x → the body is wrapped in `Era` (multiplicity 0).
        assert_eq!(
            lower("lambda x: 1"),
            Ast::Abs(
                Arc::from("x"),
                Box::new(Ast::Era(Box::new(name("x")), Box::new(int(1)))),
            )
        );
    }

    #[test]
    fn assignment_lowers_to_applied_lambda() {
        // `x = 5; x` == `(λx. x) 5` — Nix `let` desugaring.
        assert_eq!(
            lower("x = 5\nx"),
            Ast::App(
                Box::new(Ast::Abs(Arc::from("x"), Box::new(name("x")))),
                Box::new(int(5)),
            )
        );
    }

    #[test]
    fn def_lowers_to_let_bound_lambda() {
        // `def f(x): return x; f` binds f to `λx. x` then references it.
        assert_eq!(
            lower("def f(x): return x\nf"),
            Ast::App(
                Box::new(Ast::Abs(Arc::from("f"), Box::new(name("f")))),
                Box::new(Ast::Abs(Arc::from("x"), Box::new(name("x")))),
            )
        );
    }

    #[test]
    fn call_lowers_to_curried_application() {
        // `f(1, 2)` == `App(App(f, 1), 2)`.
        assert_eq!(
            lower("f(1, 2)"),
            app2(
                Ast::Fun(NixPrimFun::Builtin(Arc::from("f"))),
                int(1),
                int(2)
            )
        );
    }

    #[test]
    fn derivation_lowers_to_derivation_strict_primop() {
        // `derivation(name="hi")` applies the same `derivationStrict` builtin Nix
        // does to the same attrset.
        let set = Ast::App(
            Box::new(app2(
                Ast::Fun(NixPrimFun::Insert),
                Ast::Fun(NixPrimFun::EmptyAttrSet),
                Ast::Val(NixPrimVal::Str(Arc::from("name"))),
            )),
            Box::new(Ast::Val(NixPrimVal::Str(Arc::from("hi")))),
        );
        assert_eq!(
            lower(r#"derivation(name="hi")"#),
            Ast::App(
                Box::new(Ast::Fun(NixPrimFun::Builtin(Arc::from("derivationStrict")))),
                Box::new(set),
            )
        );
    }

    #[test]
    fn module_must_end_in_expression() {
        let stmts = parse_module("x = 1").expect("parse");
        assert!(matches!(
            lower_module(&stmts, &mut HashSet::new()),
            Err(PyError::Unsupported(_))
        ));
    }
}
