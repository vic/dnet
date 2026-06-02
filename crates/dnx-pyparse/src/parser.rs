use crate::ast::{BinOp, FStrPart, PyExpr, PyName, PyStmt};
use crate::error::PyError;
use crate::lexer::{lex, FRaw, Tok};
use std::sync::Arc;

/// Parse a module: newline-separated statements, the last of which is the
/// expression the module evaluates to.
pub(crate) fn parse_module(src: &str) -> Result<Vec<PyStmt>, PyError> {
    let toks = lex(src)?;
    let mut p = Parser { toks, pos: 0 };
    let mut stmts = Vec::new();
    p.skip_newlines();
    while !p.at_end() {
        stmts.push(p.statement()?);
        p.skip_newlines();
    }
    if stmts.is_empty() {
        return Err(PyError::Parse("empty program".into()));
    }
    Ok(stmts)
}

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
}

impl Parser {
    fn at_end(&self) -> bool {
        self.pos >= self.toks.len()
    }

    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos)
    }

    fn bump(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.pos).cloned();
        if t.is_some() {
            self.pos += 1;
        }
        t
    }

    fn eat(&mut self, t: &Tok) -> bool {
        if self.peek() == Some(t) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, t: &Tok) -> Result<(), PyError> {
        if self.eat(t) {
            Ok(())
        } else {
            Err(PyError::Parse(format!(
                "expected {t:?}, found {:?}",
                self.peek()
            )))
        }
    }

    fn skip_newlines(&mut self) {
        while self.eat(&Tok::Newline) {}
    }

    fn ident(&mut self) -> Result<PyName, PyError> {
        match self.bump() {
            Some(Tok::Ident(n)) => Ok(n),
            other => Err(PyError::Parse(format!(
                "expected identifier, found {other:?}"
            ))),
        }
    }

    // ---- statements ----

    fn statement(&mut self) -> Result<PyStmt, PyError> {
        match self.peek() {
            Some(Tok::Def) => self.def_stmt(),
            Some(Tok::Ident(_)) if self.peek_at(1) == Some(&Tok::Assign) => {
                let name = self.ident()?;
                self.expect(&Tok::Assign)?;
                Ok(PyStmt::Assign(name, self.expr()?))
            }
            _ => Ok(PyStmt::Expr(self.expr()?)),
        }
    }

    fn peek_at(&self, off: usize) -> Option<&Tok> {
        self.toks.get(self.pos + off)
    }

    fn def_stmt(&mut self) -> Result<PyStmt, PyError> {
        self.expect(&Tok::Def)?;
        let name = self.ident()?;
        self.expect(&Tok::LParen)?;
        let param = self.ident()?;
        self.expect(&Tok::RParen)?;
        self.expect(&Tok::Colon)?;
        self.expect(&Tok::Return)?;
        Ok(PyStmt::Def(name, param, self.expr()?))
    }

    // ---- expressions (precedence climbing) ----

    fn expr(&mut self) -> Result<PyExpr, PyError> {
        self.ternary()
    }

    /// `then if cond else otherwise`.
    fn ternary(&mut self) -> Result<PyExpr, PyError> {
        let then = self.or_expr()?;
        if self.eat(&Tok::If) {
            let cond = self.or_expr()?;
            self.expect(&Tok::Else)?;
            let otherwise = self.expr()?;
            Ok(PyExpr::IfExp(
                Box::new(cond),
                Box::new(then),
                Box::new(otherwise),
            ))
        } else {
            Ok(then)
        }
    }

    fn or_expr(&mut self) -> Result<PyExpr, PyError> {
        let mut lhs = self.and_expr()?;
        while self.eat(&Tok::Or) {
            let rhs = self.and_expr()?;
            lhs = PyExpr::BinOp(BinOp::Or, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn and_expr(&mut self) -> Result<PyExpr, PyError> {
        let mut lhs = self.not_expr()?;
        while self.eat(&Tok::And) {
            let rhs = self.not_expr()?;
            lhs = PyExpr::BinOp(BinOp::And, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn not_expr(&mut self) -> Result<PyExpr, PyError> {
        if self.eat(&Tok::Not) {
            Ok(PyExpr::Not(Box::new(self.not_expr()?)))
        } else {
            self.compare()
        }
    }

    /// Comparison, with Python chaining: `a < b < c` means `(a < b) and (b < c)`
    /// — each operand is compared to its neighbour and the results are `and`ed
    /// (the middle operand is shared, hence cloned). A single comparison keeps
    /// its plain `BinOp` shape; a non-comparison just returns the `add` operand.
    fn compare(&mut self) -> Result<PyExpr, PyError> {
        let first = self.add()?;
        let mut ops: Vec<(BinOp, PyExpr)> = Vec::new();
        while let Some(op) = self.peek().and_then(cmp_op) {
            self.pos += 1;
            ops.push((op, self.add()?));
        }
        Ok(chain_compare(first, ops))
    }

    fn add(&mut self) -> Result<PyExpr, PyError> {
        let mut lhs = self.mul()?;
        loop {
            let op = match self.peek() {
                Some(Tok::Plus) => BinOp::Add,
                Some(Tok::Minus) => BinOp::Sub,
                _ => break,
            };
            self.pos += 1;
            let rhs = self.mul()?;
            lhs = PyExpr::BinOp(op, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn mul(&mut self) -> Result<PyExpr, PyError> {
        let mut lhs = self.unary()?;
        loop {
            let op = match self.peek() {
                Some(Tok::Star) => BinOp::Mul,
                Some(Tok::Slash) => BinOp::Div,
                _ => break,
            };
            self.pos += 1;
            let rhs = self.unary()?;
            lhs = PyExpr::BinOp(op, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn unary(&mut self) -> Result<PyExpr, PyError> {
        if self.eat(&Tok::Minus) {
            Ok(PyExpr::Neg(Box::new(self.unary()?)))
        } else {
            self.postfix()
        }
    }

    /// Postfix chain: calls `f(..)`, indexing `e[k]`, attribute `e.name`.
    fn postfix(&mut self) -> Result<PyExpr, PyError> {
        let mut e = self.atom()?;
        loop {
            match self.peek() {
                Some(Tok::LParen) => e = self.finish_call(e)?,
                Some(Tok::LBracket) => {
                    self.pos += 1;
                    let key = self.expr()?;
                    self.expect(&Tok::RBracket)?;
                    e = PyExpr::Index(Box::new(e), Box::new(key));
                }
                Some(Tok::Dot) => {
                    self.pos += 1;
                    let name = self.ident()?;
                    e = PyExpr::Attr(Box::new(e), name);
                }
                _ => break,
            }
        }
        Ok(e)
    }

    /// Parse a call's argument list. `derivation(name=...)` is the one
    /// keyword-argument form; all other calls take positional arguments.
    fn finish_call(&mut self, callee: PyExpr) -> Result<PyExpr, PyError> {
        self.expect(&Tok::LParen)?;
        let is_deriv = matches!(&callee, PyExpr::Name(n) if n.as_ref() == "derivation");
        if is_deriv {
            let kwargs = self.kwargs()?;
            return Ok(PyExpr::Deriv(kwargs));
        }
        let mut args = Vec::new();
        if self.peek() != Some(&Tok::RParen) {
            loop {
                args.push(self.expr()?);
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        self.expect(&Tok::RParen)?;
        Ok(PyExpr::Call(Box::new(callee), args))
    }

    fn kwargs(&mut self) -> Result<Vec<(PyName, PyExpr)>, PyError> {
        let mut kwargs = Vec::new();
        if self.peek() != Some(&Tok::RParen) {
            loop {
                let key = self.ident()?;
                self.expect(&Tok::Assign)?;
                kwargs.push((key, self.expr()?));
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        self.expect(&Tok::RParen)?;
        Ok(kwargs)
    }

    fn atom(&mut self) -> Result<PyExpr, PyError> {
        match self.bump() {
            Some(Tok::Int(n)) => Ok(PyExpr::Int(n)),
            Some(Tok::Float(f)) => Ok(PyExpr::Float(f)),
            Some(Tok::Str(s)) => Ok(PyExpr::Str(s)),
            Some(Tok::FStr(raw)) => fstring(raw),
            Some(Tok::True) => Ok(PyExpr::Bool(true)),
            Some(Tok::False) => Ok(PyExpr::Bool(false)),
            Some(Tok::None) => Ok(PyExpr::None_),
            Some(Tok::Ident(n)) => Ok(PyExpr::Name(n)),
            Some(Tok::Lambda) => self.lambda_tail(),
            Some(Tok::LParen) => {
                let e = self.expr()?;
                self.expect(&Tok::RParen)?;
                Ok(e)
            }
            Some(Tok::LBracket) => self.list_tail(),
            Some(Tok::LBrace) => self.dict_tail(),
            other => Err(PyError::Parse(format!("unexpected token {other:?}"))),
        }
    }

    /// After `lambda`: `params: body`, curried into nested single-param lambdas.
    fn lambda_tail(&mut self) -> Result<PyExpr, PyError> {
        let mut params: Vec<Arc<str>> = vec![self.ident()?];
        while self.eat(&Tok::Comma) {
            params.push(self.ident()?);
        }
        self.expect(&Tok::Colon)?;
        let mut body = self.expr()?;
        for p in params.into_iter().rev() {
            body = PyExpr::Lambda(p, Box::new(body));
        }
        Ok(body)
    }

    fn list_tail(&mut self) -> Result<PyExpr, PyError> {
        let mut items = Vec::new();
        if self.peek() != Some(&Tok::RBracket) {
            loop {
                items.push(self.expr()?);
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        self.expect(&Tok::RBracket)?;
        Ok(PyExpr::List(items))
    }

    fn dict_tail(&mut self) -> Result<PyExpr, PyError> {
        let mut pairs = Vec::new();
        if self.peek() != Some(&Tok::RBrace) {
            loop {
                let key = self.expr()?;
                self.expect(&Tok::Colon)?;
                pairs.push((key, self.expr()?));
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        self.expect(&Tok::RBrace)?;
        Ok(PyExpr::Dict(pairs))
    }
}

/// Fold a comparison chain into pairwise comparisons joined by `and`. With no
/// operators the head passes through; with one it is a single `BinOp`; with more
/// each adjacent pair `(prev op next)` is `and`ed, sharing (cloning) the middle
/// operands — exactly Python's chained-comparison desugaring.
fn chain_compare(first: PyExpr, ops: Vec<(BinOp, PyExpr)>) -> PyExpr {
    let mut prev = first;
    let mut acc: Option<PyExpr> = None;
    for (op, next) in ops {
        let cmp = PyExpr::BinOp(op, Box::new(prev), Box::new(next.clone()));
        acc = Some(match acc {
            None => cmp,
            Some(a) => PyExpr::BinOp(BinOp::And, Box::new(a), Box::new(cmp)),
        });
        prev = next;
    }
    acc.unwrap_or(prev)
}

/// Build an `FStr` expression from raw lexer segments: literals pass through,
/// hole sources are re-parsed as expressions (a hole is a single expression, so
/// it must parse to exactly one trailing `Expr` statement).
fn fstring(raw: Vec<FRaw>) -> Result<PyExpr, PyError> {
    let mut parts = Vec::with_capacity(raw.len());
    for seg in raw {
        parts.push(match seg {
            FRaw::Lit(s) => FStrPart::Lit(s),
            FRaw::Hole(src) => FStrPart::Hole(Box::new(parse_hole(&src)?)),
        });
    }
    Ok(PyExpr::FStr(parts))
}

fn parse_hole(src: &str) -> Result<PyExpr, PyError> {
    let mut stmts = parse_module(src)?;
    match (stmts.len(), stmts.pop()) {
        (1, Some(PyStmt::Expr(e))) => Ok(e),
        _ => Err(PyError::Parse(format!(
            "f-string hole must be a single expression: {src:?}"
        ))),
    }
}

fn cmp_op(t: &Tok) -> Option<BinOp> {
    Some(match t {
        Tok::EqEq => BinOp::Eq,
        Tok::NotEq => BinOp::Ne,
        Tok::Lt => BinOp::Lt,
        Tok::Le => BinOp::Le,
        Tok::Gt => BinOp::Gt,
        Tok::Ge => BinOp::Ge,
        Tok::In => BinOp::In,
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    //! Parse → AST coverage, one assertion per supported Python construct. Each
    //! checks the *exact* `PyExpr`/`PyStmt` shape the parser produces, so a
    //! grammar regression (precedence, associativity, currying) fails loudly
    //! without needing the evaluation engine.
    use super::*;

    fn n(s: &str) -> PyName {
        Arc::from(s)
    }

    fn b(e: PyExpr) -> Box<PyExpr> {
        Box::new(e)
    }

    /// Parse a module whose final statement is an expression; return that expr.
    fn expr(src: &str) -> PyExpr {
        match parse_module(src).expect("parse").pop().expect("one stmt") {
            PyStmt::Expr(e) => e,
            other => panic!("expected trailing expression, got {other:?}"),
        }
    }

    /// Parse a single-statement module and return that statement.
    fn stmt(src: &str) -> PyStmt {
        let mut s = parse_module(src).expect("parse");
        assert_eq!(s.len(), 1, "expected exactly one statement");
        s.pop().expect("one stmt")
    }

    #[test]
    fn int_literal() {
        assert_eq!(expr("42"), PyExpr::Int(42));
    }

    #[test]
    fn float_literal() {
        assert_eq!(expr("1.5"), PyExpr::Float(1.5));
    }

    #[test]
    fn string_literal_both_quotes() {
        assert_eq!(expr(r#""hi""#), PyExpr::Str(n("hi")));
        assert_eq!(expr("'hi'"), PyExpr::Str(n("hi")));
    }

    #[test]
    fn bool_literals() {
        assert_eq!(expr("True"), PyExpr::Bool(true));
        assert_eq!(expr("False"), PyExpr::Bool(false));
    }

    #[test]
    fn none_literal() {
        assert_eq!(expr("None"), PyExpr::None_);
    }

    #[test]
    fn name_atom() {
        assert_eq!(expr("foo"), PyExpr::Name(n("foo")));
    }

    #[test]
    fn list_literal() {
        assert_eq!(
            expr("[1, 2, 3]"),
            PyExpr::List(vec![PyExpr::Int(1), PyExpr::Int(2), PyExpr::Int(3)])
        );
        assert_eq!(expr("[]"), PyExpr::List(vec![]));
    }

    #[test]
    fn dict_literal() {
        assert_eq!(
            expr(r#"{"a": 1, "b": 2}"#),
            PyExpr::Dict(vec![
                (PyExpr::Str(n("a")), PyExpr::Int(1)),
                (PyExpr::Str(n("b")), PyExpr::Int(2)),
            ])
        );
    }

    #[test]
    fn lambda_single_param() {
        assert_eq!(
            expr("lambda x: x"),
            PyExpr::Lambda(n("x"), b(PyExpr::Name(n("x"))))
        );
    }

    #[test]
    fn lambda_multi_param_curries() {
        // `lambda x, y: x` curries to `λx. λy. x`.
        assert_eq!(
            expr("lambda x, y: x"),
            PyExpr::Lambda(n("x"), b(PyExpr::Lambda(n("y"), b(PyExpr::Name(n("x"))))))
        );
    }

    #[test]
    fn def_statement() {
        assert_eq!(
            stmt("def f(x): return x"),
            PyStmt::Def(n("f"), n("x"), PyExpr::Name(n("x")))
        );
    }

    #[test]
    fn if_expression_python_order() {
        // `<then> if <cond> else <else>`.
        assert_eq!(
            expr("1 if c else 2"),
            PyExpr::IfExp(
                b(PyExpr::Name(n("c"))),
                b(PyExpr::Int(1)),
                b(PyExpr::Int(2)),
            )
        );
    }

    #[test]
    fn arithmetic_precedence_and_assoc() {
        // `*` binds tighter than `+`: `1 + (2 * 3)`.
        assert_eq!(
            expr("1 + 2 * 3"),
            PyExpr::BinOp(
                BinOp::Add,
                b(PyExpr::Int(1)),
                b(PyExpr::BinOp(
                    BinOp::Mul,
                    b(PyExpr::Int(2)),
                    b(PyExpr::Int(3))
                )),
            )
        );
        // `-` is left-associative: `(10 - 3) - 2`.
        assert_eq!(
            expr("10 - 3 - 2"),
            PyExpr::BinOp(
                BinOp::Sub,
                b(PyExpr::BinOp(
                    BinOp::Sub,
                    b(PyExpr::Int(10)),
                    b(PyExpr::Int(3))
                )),
                b(PyExpr::Int(2)),
            )
        );
    }

    #[test]
    fn division_operator() {
        assert_eq!(
            expr("6 / 2"),
            PyExpr::BinOp(BinOp::Div, b(PyExpr::Int(6)), b(PyExpr::Int(2)))
        );
    }

    #[test]
    fn unary_negation() {
        assert_eq!(expr("-5"), PyExpr::Neg(b(PyExpr::Int(5))));
    }

    #[test]
    fn all_comparison_operators() {
        for (src, op) in [
            ("a == b", BinOp::Eq),
            ("a != b", BinOp::Ne),
            ("a < b", BinOp::Lt),
            ("a <= b", BinOp::Le),
            ("a > b", BinOp::Gt),
            ("a >= b", BinOp::Ge),
        ] {
            assert_eq!(
                expr(src),
                PyExpr::BinOp(op, b(PyExpr::Name(n("a"))), b(PyExpr::Name(n("b")))),
                "comparison {src}"
            );
        }
    }

    #[test]
    fn membership_in_is_comparison() {
        // `k in d` parses at comparison precedence (same level as `==`).
        assert_eq!(
            expr("k in d"),
            PyExpr::BinOp(BinOp::In, b(PyExpr::Name(n("k"))), b(PyExpr::Name(n("d"))))
        );
    }

    #[test]
    fn boolean_and_or_not() {
        assert_eq!(
            expr("a and b"),
            PyExpr::BinOp(BinOp::And, b(PyExpr::Name(n("a"))), b(PyExpr::Name(n("b"))))
        );
        assert_eq!(
            expr("a or b"),
            PyExpr::BinOp(BinOp::Or, b(PyExpr::Name(n("a"))), b(PyExpr::Name(n("b"))))
        );
        assert_eq!(expr("not a"), PyExpr::Not(b(PyExpr::Name(n("a")))));
    }

    #[test]
    fn boolean_binds_looser_than_comparison() {
        // `(1 == 1) and (2 == 2)` — `and` sits above comparison in precedence.
        assert_eq!(
            expr("1 == 1 and 2 == 2"),
            PyExpr::BinOp(
                BinOp::And,
                b(PyExpr::BinOp(
                    BinOp::Eq,
                    b(PyExpr::Int(1)),
                    b(PyExpr::Int(1))
                )),
                b(PyExpr::BinOp(
                    BinOp::Eq,
                    b(PyExpr::Int(2)),
                    b(PyExpr::Int(2))
                )),
            )
        );
    }

    #[test]
    fn comparison_chains_desugar_to_and() {
        // `a < b < c` == `(a < b) and (b < c)` — middle operand shared, results
        // `and`ed (Python chained comparison), not the left-folded `(a<b)<c`.
        let lt = |x, y| PyExpr::BinOp(BinOp::Lt, b(PyExpr::Name(n(x))), b(PyExpr::Name(n(y))));
        assert_eq!(
            expr("a < b < c"),
            PyExpr::BinOp(BinOp::And, b(lt("a", "b")), b(lt("b", "c")))
        );
        // A single comparison keeps its plain shape (no `and` wrapper).
        assert_eq!(expr("a < b"), lt("a", "b"));
    }

    #[test]
    fn assignment_statement() {
        assert_eq!(stmt("x = 5"), PyStmt::Assign(n("x"), PyExpr::Int(5)));
    }

    #[test]
    fn call_positional_args() {
        assert_eq!(
            expr("f(1, 2)"),
            PyExpr::Call(
                b(PyExpr::Name(n("f"))),
                vec![PyExpr::Int(1), PyExpr::Int(2)]
            )
        );
        assert_eq!(expr("g()"), PyExpr::Call(b(PyExpr::Name(n("g"))), vec![]));
    }

    #[test]
    fn attribute_access() {
        assert_eq!(
            expr("e.field"),
            PyExpr::Attr(b(PyExpr::Name(n("e"))), n("field"))
        );
    }

    #[test]
    fn subscript_index() {
        assert_eq!(
            expr("e[k]"),
            PyExpr::Index(b(PyExpr::Name(n("e"))), b(PyExpr::Name(n("k"))))
        );
    }

    #[test]
    fn postfix_chains_left_to_right() {
        // `f(1).a[0]` → Index(Attr(Call(f,[1]), "a"), 0).
        assert_eq!(
            expr("f(1).a[0]"),
            PyExpr::Index(
                b(PyExpr::Attr(
                    b(PyExpr::Call(b(PyExpr::Name(n("f"))), vec![PyExpr::Int(1)])),
                    n("a"),
                )),
                b(PyExpr::Int(0)),
            )
        );
    }

    #[test]
    fn fstring_parses_to_parts() {
        // `f"a{x}b"` → literal/hole/literal, the hole a re-parsed expression.
        assert_eq!(
            expr(r#"f"a{x}b""#),
            PyExpr::FStr(vec![
                FStrPart::Lit(n("a")),
                FStrPart::Hole(b(PyExpr::Name(n("x")))),
                FStrPart::Lit(n("b")),
            ])
        );
    }

    #[test]
    fn fstring_hole_is_full_expression() {
        // The hole source is parsed with full expression grammar (precedence).
        assert_eq!(
            expr(r#"f"{1 + 2}""#),
            PyExpr::FStr(vec![FStrPart::Hole(b(PyExpr::BinOp(
                BinOp::Add,
                b(PyExpr::Int(1)),
                b(PyExpr::Int(2)),
            )))])
        );
    }

    #[test]
    fn fstring_escaped_braces_are_literal() {
        // `{{`/`}}` collapse to literal braces (no hole).
        assert_eq!(
            expr(r#"f"{{x}}""#),
            PyExpr::FStr(vec![FStrPart::Lit(n("{x}"))])
        );
    }

    #[test]
    fn fstring_empty_hole_is_error() {
        assert!(matches!(parse_module(r#"f"{}""#), Err(PyError::Lex(_))));
    }

    #[test]
    fn derivation_keyword_args() {
        assert_eq!(
            expr(r#"derivation(name="hi", builder="/bin/sh")"#),
            PyExpr::Deriv(vec![
                (n("name"), PyExpr::Str(n("hi"))),
                (n("builder"), PyExpr::Str(n("/bin/sh"))),
            ])
        );
    }

    #[test]
    fn multi_statement_module_order() {
        // Assignment then trailing expression — two statements, in order.
        assert_eq!(
            parse_module("x = 1\nx + 2").expect("parse"),
            vec![
                PyStmt::Assign(n("x"), PyExpr::Int(1)),
                PyStmt::Expr(PyExpr::BinOp(
                    BinOp::Add,
                    b(PyExpr::Name(n("x"))),
                    b(PyExpr::Int(2)),
                )),
            ]
        );
    }

    #[test]
    fn comment_and_blank_lines_ignored() {
        assert_eq!(expr("# a comment\n\n7  # trailing"), PyExpr::Int(7));
    }

    #[test]
    fn empty_program_is_error() {
        assert!(matches!(parse_module("   \n# c\n"), Err(PyError::Parse(_))));
    }

    #[test]
    fn parenthesized_overrides_precedence() {
        // `(1 + 2) * 3` — parens force the addition first.
        assert_eq!(
            expr("(1 + 2) * 3"),
            PyExpr::BinOp(
                BinOp::Mul,
                b(PyExpr::BinOp(
                    BinOp::Add,
                    b(PyExpr::Int(1)),
                    b(PyExpr::Int(2))
                )),
                b(PyExpr::Int(3)),
            )
        );
    }
}
