use crate::error::PyError;
use std::sync::Arc;

/// Tokens of the minimal Python surface. Statement separation is by `Newline`;
/// indentation blocks are out of scope (single-line `def`, see crate docs).
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Tok {
    Int(i64),
    Float(f64),
    Str(Arc<str>),
    /// `f"..."` segments: literal text or the raw source of an interpolation
    /// hole (re-parsed as an expression by the parser).
    FStr(Vec<FRaw>),
    Ident(Arc<str>),
    // keywords
    Lambda,
    Def,
    Return,
    If,
    Else,
    True,
    False,
    None,
    And,
    Or,
    Not,
    In,
    // symbols
    Plus,
    Minus,
    Star,
    Slash,
    EqEq,
    NotEq,
    Lt,
    Le,
    Gt,
    Ge,
    Assign,
    Colon,
    Comma,
    Dot,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Newline,
}

/// A raw f-string segment as captured by the lexer: literal text, or the
/// uninterpreted source of a `{…}` hole (parsed later as an expression).
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum FRaw {
    Lit(Arc<str>),
    Hole(Arc<str>),
}

fn keyword(word: &str) -> Option<Tok> {
    Some(match word {
        "lambda" => Tok::Lambda,
        "def" => Tok::Def,
        "return" => Tok::Return,
        "if" => Tok::If,
        "else" => Tok::Else,
        "True" => Tok::True,
        "False" => Tok::False,
        "None" => Tok::None,
        "and" => Tok::And,
        "or" => Tok::Or,
        "not" => Tok::Not,
        "in" => Tok::In,
        _ => return None,
    })
}

/// Tokenize `src`. Newlines are significant (statement separators); leading
/// indentation and blank lines collapse to a single `Newline`.
pub(crate) fn lex(src: &str) -> Result<Vec<Tok>, PyError> {
    let chars: Vec<char> = src.chars().collect();
    let mut out: Vec<Tok> = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        match c {
            ' ' | '\t' | '\r' => i += 1,
            '#' => {
                while i < chars.len() && chars[i] != '\n' {
                    i += 1;
                }
            }
            '\n' => {
                if !matches!(out.last(), None | Some(Tok::Newline)) {
                    out.push(Tok::Newline);
                }
                i += 1;
            }
            'f' | 'F' if matches!(peek(&chars, i + 1), Some('"' | '\'')) => {
                let quote = chars[i + 1];
                let (parts, next) = lex_fstring(&chars, i + 1, quote)?;
                out.push(Tok::FStr(parts));
                i = next;
            }
            '"' | '\'' => {
                let (s, next) = lex_string(&chars, i, c)?;
                out.push(Tok::Str(s));
                i = next;
            }
            '(' => push1(&mut out, &mut i, Tok::LParen),
            ')' => push1(&mut out, &mut i, Tok::RParen),
            '[' => push1(&mut out, &mut i, Tok::LBracket),
            ']' => push1(&mut out, &mut i, Tok::RBracket),
            '{' => push1(&mut out, &mut i, Tok::LBrace),
            '}' => push1(&mut out, &mut i, Tok::RBrace),
            '+' => push1(&mut out, &mut i, Tok::Plus),
            '-' => push1(&mut out, &mut i, Tok::Minus),
            '*' => push1(&mut out, &mut i, Tok::Star),
            '/' => push1(&mut out, &mut i, Tok::Slash),
            ':' => push1(&mut out, &mut i, Tok::Colon),
            ',' => push1(&mut out, &mut i, Tok::Comma),
            '.' if !next_is_digit(&chars, i) => push1(&mut out, &mut i, Tok::Dot),
            '=' if peek(&chars, i + 1) == Some('=') => push2(&mut out, &mut i, Tok::EqEq),
            '=' => push1(&mut out, &mut i, Tok::Assign),
            '!' if peek(&chars, i + 1) == Some('=') => push2(&mut out, &mut i, Tok::NotEq),
            '<' if peek(&chars, i + 1) == Some('=') => push2(&mut out, &mut i, Tok::Le),
            '<' => push1(&mut out, &mut i, Tok::Lt),
            '>' if peek(&chars, i + 1) == Some('=') => push2(&mut out, &mut i, Tok::Ge),
            '>' => push1(&mut out, &mut i, Tok::Gt),
            c if c.is_ascii_digit() || (c == '.' && next_is_digit(&chars, i)) => {
                let (t, next) = lex_number(&chars, i)?;
                out.push(t);
                i = next;
            }
            c if c.is_alphabetic() || c == '_' => {
                let (word, next) = lex_ident(&chars, i);
                out.push(keyword(&word).unwrap_or_else(|| Tok::Ident(Arc::from(word.as_str()))));
                i = next;
            }
            other => return Err(PyError::Lex(format!("unexpected character {other:?}"))),
        }
    }
    Ok(out)
}

fn push1(out: &mut Vec<Tok>, i: &mut usize, t: Tok) {
    out.push(t);
    *i += 1;
}

fn push2(out: &mut Vec<Tok>, i: &mut usize, t: Tok) {
    out.push(t);
    *i += 2;
}

fn peek(chars: &[char], i: usize) -> Option<char> {
    chars.get(i).copied()
}

fn next_is_digit(chars: &[char], i: usize) -> bool {
    chars.get(i + 1).is_some_and(|c| c.is_ascii_digit())
}

fn lex_ident(chars: &[char], start: usize) -> (String, usize) {
    let mut i = start;
    while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
        i += 1;
    }
    (chars[start..i].iter().collect(), i)
}

fn lex_number(chars: &[char], start: usize) -> Result<(Tok, usize), PyError> {
    let mut i = start;
    let mut is_float = false;
    while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '.') {
        if chars[i] == '.' {
            is_float = true;
        }
        i += 1;
    }
    let text: String = chars[start..i].iter().collect();
    if is_float {
        let f = text
            .parse::<f64>()
            .map_err(|e| PyError::Lex(format!("bad float {text:?}: {e}")))?;
        Ok((Tok::Float(f), i))
    } else {
        let n = text
            .parse::<i64>()
            .map_err(|e| PyError::Lex(format!("bad int {text:?}: {e}")))?;
        Ok((Tok::Int(n), i))
    }
}

fn lex_string(chars: &[char], start: usize, quote: char) -> Result<(Arc<str>, usize), PyError> {
    let mut i = start + 1;
    let mut s = String::new();
    while i < chars.len() {
        match chars[i] {
            c if c == quote => return Ok((Arc::from(s.as_str()), i + 1)),
            '\\' => {
                let next = chars
                    .get(i + 1)
                    .ok_or_else(|| PyError::Lex("trailing backslash in string".into()))?;
                s.push(unescape(*next)?);
                i += 2;
            }
            c => {
                s.push(c);
                i += 1;
            }
        }
    }
    Err(PyError::Lex("unterminated string".into()))
}

/// Lex an f-string body (`quote` is the opening quote at `open`). Produces
/// alternating literal/hole segments: `{…}` is a hole whose raw source is parsed
/// later; `{{`/`}}` are literal braces; backslash escapes match `lex_string`.
fn lex_fstring(chars: &[char], open: usize, quote: char) -> Result<(Vec<FRaw>, usize), PyError> {
    let mut i = open + 1;
    let mut parts: Vec<FRaw> = Vec::new();
    let mut lit = String::new();
    while i < chars.len() {
        match chars[i] {
            c if c == quote => {
                if !lit.is_empty() {
                    parts.push(FRaw::Lit(Arc::from(lit.as_str())));
                }
                return Ok((parts, i + 1));
            }
            '{' if peek(chars, i + 1) == Some('{') => {
                lit.push('{');
                i += 2;
            }
            '}' if peek(chars, i + 1) == Some('}') => {
                lit.push('}');
                i += 2;
            }
            '}' => return Err(PyError::Lex("single '}' in f-string".into())),
            '{' => {
                if !lit.is_empty() {
                    parts.push(FRaw::Lit(Arc::from(lit.as_str())));
                    lit.clear();
                }
                let (src, next) = lex_hole(chars, i + 1)?;
                parts.push(FRaw::Hole(Arc::from(src.as_str())));
                i = next;
            }
            '\\' => {
                let next = chars
                    .get(i + 1)
                    .ok_or_else(|| PyError::Lex("trailing backslash in f-string".into()))?;
                lit.push(unescape(*next)?);
                i += 2;
            }
            c => {
                lit.push(c);
                i += 1;
            }
        }
    }
    Err(PyError::Lex("unterminated f-string".into()))
}

/// Capture the raw source of an f-string hole, from just after `{` to the
/// matching `}`. Nested braces are balanced and quoted substrings are skipped so
/// braces inside them do not close the hole.
fn lex_hole(chars: &[char], start: usize) -> Result<(String, usize), PyError> {
    let mut i = start;
    let mut depth = 0u32;
    let mut s = String::new();
    while i < chars.len() {
        match chars[i] {
            '}' if depth == 0 => {
                if s.trim().is_empty() {
                    return Err(PyError::Lex("empty f-string hole".into()));
                }
                return Ok((s, i + 1));
            }
            '{' => {
                depth += 1;
                s.push('{');
                i += 1;
            }
            '}' => {
                depth -= 1;
                s.push('}');
                i += 1;
            }
            q @ ('"' | '\'') => {
                let (_, next) = lex_string(chars, i, q)?;
                s.extend(chars[i..next].iter());
                i = next;
            }
            c => {
                s.push(c);
                i += 1;
            }
        }
    }
    Err(PyError::Lex("unterminated f-string hole".into()))
}

/// Translate a backslash escape (shared by string and f-string literals).
fn unescape(next: char) -> Result<char, PyError> {
    Ok(match next {
        'n' => '\n',
        't' => '\t',
        '\\' => '\\',
        '"' => '"',
        '\'' => '\'',
        other => return Err(PyError::Lex(format!("bad escape \\{other}"))),
    })
}
