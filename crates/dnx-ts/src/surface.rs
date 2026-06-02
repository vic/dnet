//! A hand-written micro lambda-calculus surface, lowered to the shared core
//! `Ast<NixPrimVal, NixPrimFun>` — the same waist `dnx-lang`/`dnx-pyparse` target.
//! Where the JSON spike (`lower.rs`) is binder-free, this surface is the
//! *binder* path: `\x. body`, juxtaposition application, `+`, parens, integers
//! and identifiers. A bound variable is `Rep`-split when used more than once and
//! `Era`-dropped when unused, so the lowered term is linearity-legal exactly the
//! way the nix front-end's is.
//!
//! Grammar (recursive descent):
//! ```text
//! expr   := '\' ident '.' expr
//!         | 'let' ident '=' expr ';' 'in' expr   -- App(Abs(x,body),v), as nix
//!         | add
//! add    := app ('+' app)*           -- left-assoc, lowers to App(App(Add,l),r)
//! app    := postfix postfix*         -- left-assoc juxtaposition
//! postfix:= atom ('.' ident)*        -- select, lowers to App(App(Select,s),"k")
//! atom   := int | ident | '(' expr ')' | '{' (ident '=' expr ';')* '}'
//! ```
//! The attrset literal `{ k = v; }` lowers to an `Insert`-fold over
//! `EmptyAttrSet` and `s.k` to the `Select` prim — the byte-identical shapes the
//! nix front-end produces (dnx-lang collections.rs:38-44/202), so both surfaces'
//! IR stays equal and the eval-parity oracle holds.
//!
//! The multiplicity helpers (`wrap_uses`/`count_uses_in`/`build_rep_chain`) are
//! replicated from `dnx-lang` parser/helpers.rs:11/77 — those are `pub(super)`,
//! and (like `dnx-pyparse` lower.rs:255) these operate purely on the shared
//! `Ast`, so the produced IR is byte-identical to the nix front-end's.

use crate::error::TsError;
use dnx_ast::Ast;
use dnx_lang::prim::{NixPrimFun, NixPrimVal};
use std::collections::HashSet;
use std::sync::Arc;

type E = Ast<NixPrimVal, NixPrimFun>;
type Name = Arc<str>;

#[derive(Debug, Clone, PartialEq)]
enum Tok {
    Lambda,
    Dot,
    LParen,
    RParen,
    LBrace,
    RBrace,
    Plus,
    Eq,
    Semi,
    Int(i64),
    Ident(Name),
}

fn lex(src: &str) -> Result<Vec<Tok>, TsError> {
    let mut toks = vec![];
    let mut chars = src.chars().peekable();
    while let Some(&c) = chars.peek() {
        match c {
            c if c.is_whitespace() => {
                chars.next();
            }
            '\\' => {
                chars.next();
                toks.push(Tok::Lambda);
            }
            '.' => {
                chars.next();
                toks.push(Tok::Dot);
            }
            '(' => {
                chars.next();
                toks.push(Tok::LParen);
            }
            ')' => {
                chars.next();
                toks.push(Tok::RParen);
            }
            '{' => {
                chars.next();
                toks.push(Tok::LBrace);
            }
            '}' => {
                chars.next();
                toks.push(Tok::RBrace);
            }
            '+' => {
                chars.next();
                toks.push(Tok::Plus);
            }
            '=' => {
                chars.next();
                toks.push(Tok::Eq);
            }
            ';' => {
                chars.next();
                toks.push(Tok::Semi);
            }
            c if c.is_ascii_digit() => {
                let mut n = String::new();
                while let Some(&d) = chars.peek() {
                    if d.is_ascii_digit() {
                        n.push(d);
                        chars.next();
                    } else {
                        break;
                    }
                }
                let v = n
                    .parse::<i64>()
                    .map_err(|_| TsError::Parse(format!("integer out of range: {n}")))?;
                toks.push(Tok::Int(v));
            }
            c if c.is_alphabetic() || c == '_' => {
                let mut id = String::new();
                while let Some(&d) = chars.peek() {
                    if d.is_alphanumeric() || d == '_' {
                        id.push(d);
                        chars.next();
                    } else {
                        break;
                    }
                }
                toks.push(Tok::Ident(Arc::from(id.as_str())));
            }
            other => return Err(TsError::Parse(format!("unexpected character {other:?}"))),
        }
    }
    Ok(toks)
}

/// A cursor over the token stream plus the set of lexically-bound names (so a
/// free identifier lowers to `Builtin`, a bound one to `Name` — mirrors
/// `dnx-lang` lambda.rs:23-37, restricted to this surface's forms).
struct Parser<'a> {
    toks: &'a [Tok],
    pos: usize,
    bound: HashSet<Name>,
}

impl<'a> Parser<'a> {
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

    fn expect(&mut self, want: &Tok) -> Result<(), TsError> {
        match self.bump() {
            Some(ref t) if t == want => Ok(()),
            other => Err(TsError::Parse(format!("expected {want:?}, got {other:?}"))),
        }
    }

    fn expr(&mut self) -> Result<E, TsError> {
        match self.peek() {
            Some(&Tok::Lambda) => return self.lambda(),
            Some(Tok::Ident(n)) if &**n == "let" => return self.let_in(),
            _ => {}
        }
        self.add()
    }

    /// `let x = v; in body`, lowering to `App(Abs(x, wrap_uses(x, uses, body)),
    /// v)` — the byte-identical shape the nix front-end produces for a single
    /// binding (dnx-lang binding.rs:65-71), so `wrap_uses`/`count_uses_in` give
    /// the same `Rep`/`Era` IR the lambda path already shares.
    fn let_in(&mut self) -> Result<E, TsError> {
        self.bump(); // `let`
        let name: Name = match self.bump() {
            Some(Tok::Ident(n)) => n,
            other => {
                return Err(TsError::Parse(format!(
                    "let binder must be an ident, got {other:?}"
                )))
            }
        };
        self.expect(&Tok::Eq)?;
        let val = self.expr()?;
        self.expect(&Tok::Semi)?;
        match self.bump() {
            Some(Tok::Ident(n)) if &*n == "in" => {}
            other => return Err(TsError::Parse(format!("expected `in`, got {other:?}"))),
        }
        let fresh = self.bound.insert(name.clone());
        let body = self.expr()?;
        if fresh {
            self.bound.remove(&name);
        }
        let uses = count_uses_in(&body, &name);
        Ok(Ast::App(
            Box::new(Ast::Abs(
                name.clone(),
                Box::new(wrap_uses(name, uses, body)),
            )),
            Box::new(val),
        ))
    }

    fn lambda(&mut self) -> Result<E, TsError> {
        self.expect(&Tok::Lambda)?;
        let param: Name = match self.bump() {
            Some(Tok::Ident(n)) => n,
            other => {
                return Err(TsError::Parse(format!(
                    "lambda param must be an ident, got {other:?}"
                )))
            }
        };
        self.expect(&Tok::Dot)?;
        let fresh = self.bound.insert(param.clone());
        let body = self.expr()?;
        if fresh {
            self.bound.remove(&param);
        }
        let uses = count_uses_in(&body, &param);
        Ok(Ast::Abs(
            param.clone(),
            Box::new(wrap_uses(param, uses, body)),
        ))
    }

    fn add(&mut self) -> Result<E, TsError> {
        let mut acc = self.app()?;
        while self.peek() == Some(&Tok::Plus) {
            self.bump();
            let rhs = self.app()?;
            // `l + r` → App(App(Fun(Add), l), r), exactly the nix lowering
            // (dnx-lang literals.rs:153-160).
            acc = app2(Ast::Fun(NixPrimFun::Add), acc, rhs);
        }
        Ok(acc)
    }

    fn app(&mut self) -> Result<E, TsError> {
        let mut acc = self.postfix()?;
        while self.starts_atom() {
            let arg = self.postfix()?;
            acc = Ast::App(Box::new(acc), Box::new(arg));
        }
        Ok(acc)
    }

    /// `atom ('.' ident)*` — postfix select binds tighter than application and
    /// `+`. `set.k` → `App(App(Select, set), Str("k"))`, the nix lowering
    /// (dnx-lang collections.rs:202). The leading `\x. …` dot is consumed inside
    /// `lambda`, so a `.` here is always a selector.
    fn postfix(&mut self) -> Result<E, TsError> {
        let mut acc = self.atom()?;
        while self.peek() == Some(&Tok::Dot) {
            self.bump();
            let key: Name = match self.bump() {
                Some(Tok::Ident(n)) => n,
                other => {
                    return Err(TsError::Parse(format!(
                        "select key must be an ident, got {other:?}"
                    )))
                }
            };
            acc = app2(
                Ast::Fun(NixPrimFun::Select),
                acc,
                Ast::Val(NixPrimVal::Str(key)),
            );
        }
        Ok(acc)
    }

    /// True iff the next token can begin an `atom` (so application stops at `+`,
    /// `)`, `.` or end-of-input).
    fn starts_atom(&self) -> bool {
        matches!(
            self.peek(),
            Some(Tok::Int(_))
                | Some(Tok::Ident(_))
                | Some(Tok::LParen)
                | Some(Tok::LBrace)
                | Some(Tok::Lambda)
        )
    }

    fn atom(&mut self) -> Result<E, TsError> {
        match self.bump() {
            Some(Tok::Int(n)) => Ok(Ast::Val(NixPrimVal::Int(n))),
            Some(Tok::Ident(n)) => Ok(lower_name(&n, &self.bound)),
            Some(Tok::LParen) => {
                let e = self.expr()?;
                self.expect(&Tok::RParen)?;
                Ok(e)
            }
            Some(Tok::LBrace) => {
                self.pos -= 1;
                self.attrset()
            }
            Some(Tok::Lambda) => {
                self.pos -= 1;
                self.lambda()
            }
            other => Err(TsError::Parse(format!("expected an atom, got {other:?}"))),
        }
    }

    /// `{ k = v; … }` → fold `Insert set "k" v` over `EmptyAttrSet`, the
    /// byte-identical shape the nix front-end produces (dnx-lang
    /// collections.rs:38-44). Keys are static idents lowered to string literals,
    /// values are full expressions, so the resulting `PrimValue::AttrSet` is
    /// identical to nix's given identical keys/values.
    fn attrset(&mut self) -> Result<E, TsError> {
        self.expect(&Tok::LBrace)?;
        let mut set: E = Ast::Fun(NixPrimFun::EmptyAttrSet);
        while self.peek() != Some(&Tok::RBrace) {
            let key: Name = match self.bump() {
                Some(Tok::Ident(n)) => n,
                other => {
                    return Err(TsError::Parse(format!(
                        "attrset key must be an ident, got {other:?}"
                    )))
                }
            };
            self.expect(&Tok::Eq)?;
            let val = self.expr()?;
            self.expect(&Tok::Semi)?;
            set = Ast::App(
                Box::new(app2(
                    Ast::Fun(NixPrimFun::Insert),
                    set,
                    Ast::Val(NixPrimVal::Str(key)),
                )),
                Box::new(val),
            );
        }
        self.expect(&Tok::RBrace)?;
        Ok(set)
    }
}

/// A bound name is a variable reference; a free name is a builtin primop
/// (mirrors `dnx-lang` lambda.rs:29-37).
fn lower_name(n: &Name, bound: &HashSet<Name>) -> E {
    if bound.contains(n) {
        Ast::Name(n.clone())
    } else {
        Ast::Fun(NixPrimFun::Builtin(n.clone()))
    }
}

/// Parse and lower a micro-lambda program to one shared-core expression.
pub fn lower_lambda_surface(src: &str) -> Result<E, TsError> {
    let toks = lex(src)?;
    let mut p = Parser {
        toks: &toks,
        pos: 0,
        bound: HashSet::new(),
    };
    let e = p.expr()?;
    if p.pos != toks.len() {
        return Err(TsError::Parse(format!(
            "trailing tokens after expression: {:?}",
            &toks[p.pos..]
        )));
    }
    Ok(e)
}

fn app2(f: E, a: E, b: E) -> E {
    Ast::App(Box::new(Ast::App(Box::new(f), Box::new(a))), Box::new(b))
}

// ---- variable multiplicity (replicated from dnx-lang helpers.rs:11/77 — those
// are pub(super); these operate purely on the shared `Ast`, as dnx-pyparse
// lower.rs:255 also does) ----

fn wrap_uses(name: Name, uses: u32, body: E) -> E {
    match uses {
        0 => Ast::Era(Box::new(Ast::Name(name)), Box::new(body)),
        1 => body,
        n => build_rep_chain(name, n as usize, body),
    }
}

fn build_rep_chain(name: Name, uses: usize, body: E) -> E {
    if uses <= 1 {
        return body;
    }
    let split: Vec<Name> = (0..uses)
        .map(|i| Arc::from(format!("{name}__{i}").as_str()))
        .collect();
    let mut idx = 0;
    let body = indexed_rename(body, &name, &split, &mut idx);
    nest_reps(Ast::Name(name), &split, body)
}

fn indexed_rename(expr: E, from: &Name, names: &[Name], idx: &mut usize) -> E {
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

fn nest_reps(expr: E, names: &[Name], body: E) -> E {
    if names.len() == 2 {
        Ast::Rep(
            Box::new(expr),
            names[0].clone(),
            names[1].clone(),
            Box::new(body),
        )
    } else {
        let rest: Name = Arc::from(format!("__rr_{}", names[1]).as_str());
        let inner = nest_reps(Ast::Name(rest.clone()), &names[1..], body);
        Ast::Rep(Box::new(expr), names[0].clone(), rest, Box::new(inner))
    }
}

fn count_uses_in(expr: &E, name: &Name) -> u32 {
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
