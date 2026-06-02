use dnx_ast::{PrimFun, PrimVal};
use dnx_core::prim::{PrimFunEntry, PrimImpl, PrimTable, PrimValue};
use dnx_core::DnxError;
use std::sync::Arc;

/// Nix primitive value (literals + runtime values).
#[derive(Debug, Clone, PartialEq)]
pub enum NixPrimVal {
    Int(i64),
    Float(f64),
    Str(Arc<str>),
    Bool(bool),
    Null,
    Path(Arc<str>),
}

impl PrimVal for NixPrimVal {}

/// Nix primitive function (resolved at parse time).
#[derive(Debug, Clone, PartialEq)]
pub enum NixPrimFun {
    // AttrSet
    Select,
    SelectOr,
    SelectDyn,
    EmptyAttrSet,
    HasAttr,
    Insert,
    InsertDyn,
    MkSingleton,
    Update,
    AttrNames,
    AttrValues,
    MapAttrs,
    FilterAttrs,
    ListToAttrs,
    // List (eager versions removed — now use Scott-encoded prelude)
    IsList,
    // String
    StrConcat,
    ToStr,
    PathConcat,
    Substring,
    StringLength,
    // Bitwise
    BitAnd,
    BitOr,
    BitXor,
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Neg,
    // Comparison (emit Church-bool)
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    // Type checks
    TypeOf,
    IsInt,
    IsFloat,
    IsString,
    IsBool,
    IsNull,
    IsAttrs,
    IsFunction,
    IsPath,
    // Conversion
    ToInt,
    ToFloat,
    ToString2,
    ToJSON,
    FromJSON,
    TryEval,
    // Misc
    Throw,
    Abort,
    // Derivations (the `derivationStrict` primop — derivation.nix wraps it)
    DerivationStrict,
    // Unknown builtins
    Builtin(Arc<str>),
}

impl PrimFun for NixPrimFun {}

fn prim_add(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Int(a), PrimValue::Int(b)] => {
            Ok(PrimValue::Int(a.checked_add(*b).ok_or_else(|| {
                DnxError::PrimError("integer overflow".into())
            })?))
        }
        [PrimValue::Float(a), PrimValue::Float(b)] => Ok(PrimValue::Float(a + b)),
        [PrimValue::Int(a), PrimValue::Float(b)] => Ok(PrimValue::Float(*a as f64 + b)),
        [PrimValue::Float(a), PrimValue::Int(b)] => Ok(PrimValue::Float(a + *b as f64)),
        [PrimValue::Str(a), PrimValue::Str(b)] => {
            let mut s = String::with_capacity(a.len() + b.len());
            s.push_str(a);
            s.push_str(b);
            Ok(PrimValue::Str(Arc::from(s)))
        }
        _ => Err(DnxError::PrimError("add: type mismatch".into())),
    }
}

fn prim_sub(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Int(a), PrimValue::Int(b)] => {
            Ok(PrimValue::Int(a.checked_sub(*b).ok_or_else(|| {
                DnxError::PrimError("integer overflow".into())
            })?))
        }
        [PrimValue::Float(a), PrimValue::Float(b)] => Ok(PrimValue::Float(a - b)),
        [PrimValue::Int(a), PrimValue::Float(b)] => Ok(PrimValue::Float(*a as f64 - b)),
        [PrimValue::Float(a), PrimValue::Int(b)] => Ok(PrimValue::Float(a - *b as f64)),
        _ => Err(DnxError::PrimError("sub: expected two numbers".into())),
    }
}

fn prim_mul(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Int(a), PrimValue::Int(b)] => {
            Ok(PrimValue::Int(a.checked_mul(*b).ok_or_else(|| {
                DnxError::PrimError("integer overflow".into())
            })?))
        }
        [PrimValue::Float(a), PrimValue::Float(b)] => Ok(PrimValue::Float(a * b)),
        [PrimValue::Int(a), PrimValue::Float(b)] => Ok(PrimValue::Float(*a as f64 * b)),
        [PrimValue::Float(a), PrimValue::Int(b)] => Ok(PrimValue::Float(a * *b as f64)),
        _ => Err(DnxError::PrimError("mul: expected two numbers".into())),
    }
}

fn prim_div(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Int(_), PrimValue::Int(0)] => {
            Err(DnxError::PrimError("div: division by zero".into()))
        }
        [PrimValue::Int(a), PrimValue::Int(b)] => {
            Ok(PrimValue::Int(a.checked_div(*b).ok_or_else(|| {
                DnxError::PrimError("integer overflow".into())
            })?))
        }
        [PrimValue::Float(a), PrimValue::Float(b)] => Ok(PrimValue::Float(a / b)),
        [PrimValue::Int(a), PrimValue::Float(b)] => Ok(PrimValue::Float(*a as f64 / b)),
        [PrimValue::Float(a), PrimValue::Int(b)] => Ok(PrimValue::Float(a / *b as f64)),
        _ => Err(DnxError::PrimError("div: expected two numbers".into())),
    }
}

fn prim_neg(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Int(a)] => {
            Ok(PrimValue::Int(a.checked_neg().ok_or_else(|| {
                DnxError::PrimError("integer overflow".into())
            })?))
        }
        [PrimValue::Float(a)] => Ok(PrimValue::Float(-a)),
        _ => Err(DnxError::PrimError("neg: expected a number".into())),
    }
}

/// Deep structural equality of two values, per cppNix `==`: scalars by value,
/// lists pairwise + same length, attrsets by same keys + recursively-equal
/// values. Functions are incomparable and yield `None` (cppNix throws on
/// function equality); a caller maps `None` to a typed error so no two lambdas
/// ever compare equal. Cross-type pairs are `Some(false)`.
fn value_eq(a: &PrimValue, b: &PrimValue) -> Option<bool> {
    use PrimValue::*;
    match (a, b) {
        (Int(x), Int(y)) => Some(x == y),
        (Float(x), Float(y)) => Some(x.to_bits() == y.to_bits()),
        (Int(x), Float(y)) | (Float(y), Int(x)) => Some((*x as f64).to_bits() == y.to_bits()),
        (Str(x), Str(y)) => Some(x == y),
        (Path(x), Path(y)) => Some(x == y),
        (Bool(x), Bool(y)) => Some(x == y),
        (Null, Null) => Some(true),
        (List(x), List(y)) => {
            if x.len() != y.len() {
                return Some(false);
            }
            for (xi, yi) in x.iter().zip(y) {
                if !value_eq(xi, yi)? {
                    return Some(false);
                }
            }
            Some(true)
        }
        (AttrSet(x), AttrSet(y)) => {
            if x.len() != y.len() {
                return Some(false);
            }
            // Both sides are key-sorted (PrimValue::AttrSet invariant), so equal
            // sets line up positionally.
            for ((kx, vx), (ky, vy)) in x.iter().zip(y) {
                if kx != ky || !value_eq(vx, vy)? {
                    return Some(false);
                }
            }
            Some(true)
        }
        // A function on either side of a structural compare is incomparable.
        (Lambda, _) | (_, Lambda) | (Closure(_), _) | (_, Closure(_)) => None,
        _ => Some(false),
    }
}

fn prim_eq(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [a, b] => value_eq(a, b)
            .map(PrimValue::Bool)
            .ok_or_else(|| DnxError::PrimError("==: cannot compare functions for equality".into())),
        _ => Err(DnxError::PrimError("==: expected two arguments".into())),
    }
}

fn prim_ne(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match prim_eq(args)? {
        PrimValue::Bool(b) => Ok(PrimValue::Bool(!b)),
        other => Ok(other),
    }
}

fn prim_lt(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Int(a), PrimValue::Int(b)] => Ok(PrimValue::Bool(a < b)),
        [PrimValue::Float(a), PrimValue::Float(b)] => Ok(PrimValue::Bool(a < b)),
        [PrimValue::Int(a), PrimValue::Float(b)] => Ok(PrimValue::Bool((*a as f64) < *b)),
        [PrimValue::Float(a), PrimValue::Int(b)] => Ok(PrimValue::Bool(*a < *b as f64)),
        [PrimValue::Str(a), PrimValue::Str(b)] => Ok(PrimValue::Bool(a < b)),
        _ => Err(DnxError::PrimError("lt: incompatible types".into())),
    }
}

fn prim_le(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Int(a), PrimValue::Int(b)] => Ok(PrimValue::Bool(a <= b)),
        [PrimValue::Float(a), PrimValue::Float(b)] => Ok(PrimValue::Bool(a <= b)),
        [PrimValue::Int(a), PrimValue::Float(b)] => Ok(PrimValue::Bool((*a as f64) <= *b)),
        [PrimValue::Float(a), PrimValue::Int(b)] => Ok(PrimValue::Bool(*a <= *b as f64)),
        [PrimValue::Str(a), PrimValue::Str(b)] => Ok(PrimValue::Bool(a <= b)),
        _ => Err(DnxError::PrimError("le: incompatible types".into())),
    }
}

fn prim_gt(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Int(a), PrimValue::Int(b)] => Ok(PrimValue::Bool(a > b)),
        [PrimValue::Float(a), PrimValue::Float(b)] => Ok(PrimValue::Bool(a > b)),
        [PrimValue::Int(a), PrimValue::Float(b)] => Ok(PrimValue::Bool((*a as f64) > *b)),
        [PrimValue::Float(a), PrimValue::Int(b)] => Ok(PrimValue::Bool(*a > *b as f64)),
        [PrimValue::Str(a), PrimValue::Str(b)] => Ok(PrimValue::Bool(a > b)),
        _ => Err(DnxError::PrimError("gt: incompatible types".into())),
    }
}

fn prim_ge(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Int(a), PrimValue::Int(b)] => Ok(PrimValue::Bool(a >= b)),
        [PrimValue::Float(a), PrimValue::Float(b)] => Ok(PrimValue::Bool(a >= b)),
        [PrimValue::Int(a), PrimValue::Float(b)] => Ok(PrimValue::Bool((*a as f64) >= *b)),
        [PrimValue::Float(a), PrimValue::Int(b)] => Ok(PrimValue::Bool(*a >= *b as f64)),
        [PrimValue::Str(a), PrimValue::Str(b)] => Ok(PrimValue::Bool(a >= b)),
        _ => Err(DnxError::PrimError("ge: incompatible types".into())),
    }
}

fn prim_type_of(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [v] => Ok(PrimValue::Str(Arc::from(match v {
            PrimValue::Int(_) => "int",
            PrimValue::Float(_) => "float",
            PrimValue::Str(_) => "string",
            PrimValue::Path(_) => "path",
            PrimValue::Null => "null",
            PrimValue::Bool(_) => "bool",
            PrimValue::List(_) => "list",
            PrimValue::AttrSet(_) => "set",
            PrimValue::Closure(_) | PrimValue::Lambda => "lambda",
        }))),
        _ => Err(DnxError::PrimError("type_of: arity".into())),
    }
}

fn prim_string_length(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Str(s)] => Ok(PrimValue::Int(s.len() as i64)),
        _ => Err(DnxError::PrimError("stringLength: expected string".into())),
    }
}

fn prim_substring(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Int(start), PrimValue::Int(len), PrimValue::Str(s)] => {
            let start = (*start).max(0) as usize;
            let len = (*len).max(0) as usize;

            let s_str = s.as_ref();
            let chars: Vec<char> = s_str.chars().collect();
            let end = start.saturating_add(len).min(chars.len());

            if start >= chars.len() {
                Ok(PrimValue::Str(Arc::from("")))
            } else {
                let result: String = chars[start..end].iter().collect();
                Ok(PrimValue::Str(Arc::from(result)))
            }
        }
        _ => Err(DnxError::PrimError(
            "substring: expected (int, int, string)".into(),
        )),
    }
}

fn prim_to_string(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Int(n)] => Ok(PrimValue::Str(Arc::from(n.to_string()))),
        [PrimValue::Float(f)] => Ok(PrimValue::Str(Arc::from(f.to_string()))),
        [PrimValue::Str(s)] => Ok(PrimValue::Str(s.clone())),
        [PrimValue::Path(p)] => Ok(PrimValue::Str(p.clone())),
        [PrimValue::Bool(true)] => Ok(PrimValue::Str(Arc::from("1"))),
        [PrimValue::Bool(false)] => Ok(PrimValue::Str(Arc::from(""))),
        [PrimValue::Null] => Ok(PrimValue::Str(Arc::from(""))),
        _ => Err(DnxError::PrimError("toString: unsupported type".into())),
    }
}

fn prim_bit_and(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Int(a), PrimValue::Int(b)] => Ok(PrimValue::Int(a & b)),
        _ => Err(DnxError::PrimError("bitAnd: expected two integers".into())),
    }
}

fn prim_bit_or(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Int(a), PrimValue::Int(b)] => Ok(PrimValue::Int(a | b)),
        _ => Err(DnxError::PrimError("bitOr: expected two integers".into())),
    }
}

fn prim_bit_xor(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Int(a), PrimValue::Int(b)] => Ok(PrimValue::Int(a ^ b)),
        _ => Err(DnxError::PrimError("bitXor: expected two integers".into())),
    }
}

fn prim_to_int(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Str(s)] => {
            let trimmed = s.trim();
            match trimmed.parse::<i64>() {
                Ok(n) => Ok(PrimValue::Int(n)),
                Err(_) => Err(DnxError::PrimError("toInt: invalid integer string".into())),
            }
        }
        _ => Err(DnxError::PrimError("toInt: expected string".into())),
    }
}

fn prim_is_function(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Lambda | PrimValue::Closure(_)] => Ok(PrimValue::Bool(true)),
        [_] => Ok(PrimValue::Bool(false)),
        _ => Err(DnxError::PrimError("is_function: arity".into())),
    }
}

fn prim_is_int(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Int(_)] => Ok(PrimValue::Bool(true)),
        [_] => Ok(PrimValue::Bool(false)),
        _ => Err(DnxError::PrimError("is_int: arity".into())),
    }
}

fn prim_is_float(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Float(_)] => Ok(PrimValue::Bool(true)),
        [_] => Ok(PrimValue::Bool(false)),
        _ => Err(DnxError::PrimError("is_float: arity".into())),
    }
}

fn prim_is_string(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Str(_)] => Ok(PrimValue::Bool(true)),
        [_] => Ok(PrimValue::Bool(false)),
        _ => Err(DnxError::PrimError("is_string: arity".into())),
    }
}

fn prim_is_null(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Null] => Ok(PrimValue::Bool(true)),
        [_] => Ok(PrimValue::Bool(false)),
        _ => Err(DnxError::PrimError("is_null: arity".into())),
    }
}

fn prim_is_list(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::List(_)] => Ok(PrimValue::Bool(true)),
        [_] => Ok(PrimValue::Bool(false)),
        _ => Err(DnxError::PrimError("is_list: arity".into())),
    }
}

fn prim_empty_attr_set(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [] => Ok(PrimValue::AttrSet(vec![])),
        _ => Err(DnxError::PrimError("empty_attr_set: arity".into())),
    }
}

fn prim_insert(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::AttrSet(set), PrimValue::Str(key), val] => {
            let mut result = set.clone();
            let key_arc = key.clone();
            if let Some(pos) = result.iter().position(|(k, _)| k == key) {
                result[pos].1 = val.clone();
            } else {
                result.push((key_arc, val.clone()));
                result.sort_by(|a, b| a.0.as_ref().cmp(b.0.as_ref()));
            }
            Ok(PrimValue::AttrSet(result))
        }
        [PrimValue::AttrSet(_), _, _] => {
            Err(DnxError::PrimError("insert: key must be string".into()))
        }
        [_, _, _] => Err(DnxError::PrimError(
            "insert: first arg must be attrset".into(),
        )),
        _ => Err(DnxError::PrimError("insert: arity".into())),
    }
}

fn prim_select(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::AttrSet(set), PrimValue::Str(key)] => {
            for (k, v) in set {
                if k == key {
                    return Ok(v.clone());
                }
            }
            Err(DnxError::PrimError(Arc::from(format!(
                "attribute '{}' missing",
                key
            ))))
        }
        [PrimValue::AttrSet(_), _] => Err(DnxError::PrimError("select: key must be string".into())),
        [_, _] => Err(DnxError::PrimError(
            "select: first arg must be attrset".into(),
        )),
        _ => Err(DnxError::PrimError("select: arity".into())),
    }
}

fn prim_select_or(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::AttrSet(set), PrimValue::Str(key), default] => {
            for (k, v) in set {
                if k == key {
                    return Ok(v.clone());
                }
            }
            Ok(default.clone())
        }
        [PrimValue::AttrSet(_), _, _] => {
            Err(DnxError::PrimError("select_or: key must be string".into()))
        }
        [_, _, _] => Err(DnxError::PrimError(
            "select_or: first arg must be attrset".into(),
        )),
        _ => Err(DnxError::PrimError("select_or: arity".into())),
    }
}

fn prim_has_attr(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::AttrSet(set), PrimValue::Str(key)] => {
            let present = set.iter().any(|(k, _)| k == key);
            Ok(PrimValue::Bool(present))
        }
        [PrimValue::AttrSet(_), _] => {
            Err(DnxError::PrimError("has_attr: key must be string".into()))
        }
        [_, _] => Err(DnxError::PrimError(
            "has_attr: first arg must be attrset".into(),
        )),
        _ => Err(DnxError::PrimError("has_attr: arity".into())),
    }
}

fn prim_update(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::AttrSet(a), PrimValue::AttrSet(b)] => {
            let mut result = a.clone();
            for (k_b, v_b) in b {
                if let Some(pos) = result.iter().position(|(k, _)| k == k_b) {
                    result[pos].1 = v_b.clone();
                } else {
                    result.push((k_b.clone(), v_b.clone()));
                }
            }
            result.sort_by(|a, b| a.0.as_ref().cmp(b.0.as_ref()));
            Ok(PrimValue::AttrSet(result))
        }
        [PrimValue::AttrSet(_), _] => Err(DnxError::PrimError(
            "update: second arg must be attrset".into(),
        )),
        [_, _] => Err(DnxError::PrimError(
            "update: first arg must be attrset".into(),
        )),
        _ => Err(DnxError::PrimError("update: arity".into())),
    }
}

fn prim_mk_singleton(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Str(key), val] => Ok(PrimValue::AttrSet(vec![(key.clone(), val.clone())])),
        [_, _] => Err(DnxError::PrimError(
            "mk_singleton: key must be string".into(),
        )),
        _ => Err(DnxError::PrimError("mk_singleton: arity".into())),
    }
}

/// `derivationStrict`: validate a flat derivation attrset and return it as the
/// recognized derivation description (a `type = "derivation"` marker is added,
/// mirroring cppNix). Store paths are NOT computed here — that needs a `Store`
/// and happens at realize time in `dnx-drv` (kept out of the pure evaluator).
fn prim_derivation_strict(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    let set = match args {
        [PrimValue::AttrSet(set)] => set,
        [_] => {
            return Err(DnxError::PrimError(
                "derivationStrict: expected an attrset".into(),
            ))
        }
        _ => return Err(DnxError::PrimError("derivationStrict: arity".into())),
    };
    let require = |key: &str| -> Result<(), DnxError> {
        match set.iter().find(|(k, _)| k.as_ref() == key) {
            Some((_, PrimValue::Str(_))) => Ok(()),
            Some(_) => Err(DnxError::PrimError(Arc::from(format!(
                "derivationStrict: {key} must be a string"
            )))),
            None => Err(DnxError::PrimError(Arc::from(format!(
                "derivationStrict: missing required attr '{key}'"
            )))),
        }
    };
    require("name")?;
    require("builder")?;
    let mut out = set.clone();
    if !out.iter().any(|(k, _)| k.as_ref() == "type") {
        out.push((Arc::from("type"), PrimValue::Str(Arc::from("derivation"))));
        out.sort_by(|a, b| a.0.as_ref().cmp(b.0.as_ref()));
    }
    Ok(PrimValue::AttrSet(out))
}

fn prim_attr_names(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::AttrSet(set)] => Ok(PrimValue::List(
            set.iter().map(|(k, _)| PrimValue::Str(k.clone())).collect(),
        )),
        [_] => Err(DnxError::PrimError("attrNames: expected attrset".into())),
        _ => Err(DnxError::PrimError("attrNames: arity".into())),
    }
}

fn prim_attr_values(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::AttrSet(set)] => Ok(PrimValue::List(
            set.iter().map(|(_, v)| v.clone()).collect(),
        )),
        [_] => Err(DnxError::PrimError("attrValues: expected attrset".into())),
        _ => Err(DnxError::PrimError("attrValues: arity".into())),
    }
}

fn prim_is_attrs(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::AttrSet(_)] => Ok(PrimValue::Bool(true)),
        [_] => Ok(PrimValue::Bool(false)),
        _ => Err(DnxError::PrimError("is_attrs: arity".into())),
    }
}

fn prim_is_bool(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Bool(_)] => Ok(PrimValue::Bool(true)),
        [_] => Ok(PrimValue::Bool(false)),
        _ => Err(DnxError::PrimError("is_bool: arity".into())),
    }
}

fn prim_is_path(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Path(_)] => Ok(PrimValue::Bool(true)),
        [_] => Ok(PrimValue::Bool(false)),
        _ => Err(DnxError::PrimError("is_path: arity".into())),
    }
}

fn prim_to_float(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Float(f)] => Ok(PrimValue::Float(*f)),
        [PrimValue::Int(n)] => Ok(PrimValue::Float(*n as f64)),
        [PrimValue::Str(s)] => match s.trim().parse::<f64>() {
            Ok(f) => Ok(PrimValue::Float(f)),
            Err(_) => Err(DnxError::PrimError("toFloat: invalid float string".into())),
        },
        [_] => Err(DnxError::PrimError(
            "toFloat: expected string or number".into(),
        )),
        _ => Err(DnxError::PrimError("toFloat: arity".into())),
    }
}

/// Serialize an already-reduced `PrimValue` tree to JSON. Pure structural
/// recursion over a finite value (NOT Nix-level recursion). Functions cannot
/// be serialized, matching cppNix `builtins.toJSON`.
fn json_of(v: &PrimValue, out: &mut String) -> Result<(), DnxError> {
    match v {
        PrimValue::Int(n) => out.push_str(&n.to_string()),
        PrimValue::Float(f) => out.push_str(&f.to_string()),
        PrimValue::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
        PrimValue::Null => out.push_str("null"),
        PrimValue::Str(s) | PrimValue::Path(s) => json_str(s, out),
        PrimValue::List(xs) => {
            out.push('[');
            for (i, x) in xs.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                json_of(x, out)?;
            }
            out.push(']');
        }
        PrimValue::AttrSet(kvs) => {
            out.push('{');
            for (i, (k, val)) in kvs.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                json_str(k, out);
                out.push(':');
                json_of(val, out)?;
            }
            out.push('}');
        }
        PrimValue::Closure(_) | PrimValue::Lambda => {
            return Err(DnxError::PrimError(
                "toJSON: cannot serialize a function".into(),
            ))
        }
    }
    Ok(())
}

fn json_str(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            _ => out.push(c),
        }
    }
    out.push('"');
}

fn prim_to_json(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [v] => {
            let mut out = String::new();
            json_of(v, &mut out)?;
            Ok(PrimValue::Str(Arc::from(out)))
        }
        _ => Err(DnxError::PrimError("toJSON: arity".into())),
    }
}

fn prim_throw(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Str(msg)] => Err(DnxError::PrimError(msg.clone())),
        [_] => Err(DnxError::PrimError("throw: expected a string".into())),
        _ => Err(DnxError::PrimError("throw: arity".into())),
    }
}

fn prim_abort(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Str(msg)] => Err(DnxError::PrimError(Arc::from(format!(
            "evaluation aborted with the following error message: '{msg}'"
        )))),
        [_] => Err(DnxError::PrimError("abort: expected a string".into())),
        _ => Err(DnxError::PrimError("abort: arity".into())),
    }
}

fn prim_base_name_of(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Str(s)] => Ok(PrimValue::Str(Arc::from(base_name(s)))),
        [PrimValue::Path(p)] => Ok(PrimValue::Str(Arc::from(base_name(p)))),
        [_] => Err(DnxError::PrimError(
            "baseNameOf: expected string or path".into(),
        )),
        _ => Err(DnxError::PrimError("baseNameOf: arity".into())),
    }
}

fn base_name(s: &str) -> &str {
    let trimmed = s.strip_suffix('/').unwrap_or(s);
    match trimmed.rfind('/') {
        Some(i) => &trimmed[i + 1..],
        None => trimmed,
    }
}

fn prim_dir_of(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Str(s)] => Ok(PrimValue::Str(Arc::from(dir_name(s)))),
        [PrimValue::Path(p)] => Ok(PrimValue::Path(Arc::from(dir_name(p)))),
        [_] => Err(DnxError::PrimError("dirOf: expected string or path".into())),
        _ => Err(DnxError::PrimError("dirOf: arity".into())),
    }
}

fn dir_name(s: &str) -> &str {
    let trimmed = s.strip_suffix('/').unwrap_or(s);
    match trimmed.rfind('/') {
        Some(0) => "/",
        Some(i) => &trimmed[..i],
        None => ".",
    }
}

// ----------------------------------------------------------------------------
// Scalar / string / attrset builtins that operate purely on already-reduced
// `PrimValue` data (args arrive in normal form via `prim_apply`). No user-
// lambda application or AST introspection — those are DEFERRED (see below).
// ----------------------------------------------------------------------------

/// `getAttr name set` — `builtins.getAttr`. Same as `set.${name}` but missing
/// key is an error. cppNix primops.cc `prim_getAttr`.
fn prim_get_attr(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Str(key), PrimValue::AttrSet(set)] => set
            .iter()
            .find(|(k, _)| k == key)
            .map(|(_, v)| v.clone())
            .ok_or_else(|| DnxError::PrimError(Arc::from(format!("attribute '{key}' missing")))),
        [PrimValue::Str(_), _] => Err(DnxError::PrimError(
            "getAttr: second arg must be attrset".into(),
        )),
        [_, _] => Err(DnxError::PrimError("getAttr: name must be string".into())),
        _ => Err(DnxError::PrimError("getAttr: arity".into())),
    }
}

/// `removeAttrs set list` — set minus every name in `list`. cppNix
/// `prim_removeAttrs`. Result stays sorted (filtering preserves order).
fn prim_remove_attrs(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::AttrSet(set), PrimValue::List(names)] => {
            let drop: Vec<&str> = names
                .iter()
                .map(|n| match n {
                    PrimValue::Str(s) => Ok(s.as_ref()),
                    _ => Err(DnxError::PrimError(
                        "removeAttrs: names must be strings".into(),
                    )),
                })
                .collect::<Result<_, _>>()?;
            Ok(PrimValue::AttrSet(
                set.iter()
                    .filter(|(k, _)| !drop.contains(&k.as_ref()))
                    .cloned()
                    .collect(),
            ))
        }
        [PrimValue::AttrSet(_), _] => Err(DnxError::PrimError(
            "removeAttrs: second arg must be list".into(),
        )),
        [_, _] => Err(DnxError::PrimError(
            "removeAttrs: first arg must be attrset".into(),
        )),
        _ => Err(DnxError::PrimError("removeAttrs: arity".into())),
    }
}

/// `intersectAttrs e1 e2` — attrs of `e2` whose names are also in `e1`, with
/// `e2`'s values. cppNix `prim_intersectAttrs`. Result preserves `e2` order.
fn prim_intersect_attrs(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::AttrSet(a), PrimValue::AttrSet(b)] => Ok(PrimValue::AttrSet(
            b.iter()
                .filter(|(k, _)| a.iter().any(|(ka, _)| ka == k))
                .cloned()
                .collect(),
        )),
        [_, _] => Err(DnxError::PrimError(
            "intersectAttrs: both args must be attrsets".into(),
        )),
        _ => Err(DnxError::PrimError("intersectAttrs: arity".into())),
    }
}

/// `catAttrs name list-of-sets` — collect `set.${name}` from each set that has
/// it, skipping sets without it. cppNix `prim_catAttrs`.
fn prim_cat_attrs(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Str(name), PrimValue::List(sets)] => {
            let mut out = Vec::new();
            for s in sets {
                match s {
                    PrimValue::AttrSet(kvs) => {
                        if let Some((_, v)) = kvs.iter().find(|(k, _)| k == name) {
                            out.push(v.clone());
                        }
                    }
                    _ => {
                        return Err(DnxError::PrimError(
                            "catAttrs: list must hold attrsets".into(),
                        ))
                    }
                }
            }
            Ok(PrimValue::List(out))
        }
        [PrimValue::Str(_), _] => Err(DnxError::PrimError(
            "catAttrs: second arg must be list".into(),
        )),
        [_, _] => Err(DnxError::PrimError("catAttrs: name must be string".into())),
        _ => Err(DnxError::PrimError("catAttrs: arity".into())),
    }
}

/// `concatLists list-of-lists` — flatten one level. cppNix `prim_concatLists`.
fn prim_concat_lists(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::List(lists)] => {
            let mut out = Vec::new();
            for l in lists {
                match l {
                    PrimValue::List(xs) => out.extend(xs.iter().cloned()),
                    _ => {
                        return Err(DnxError::PrimError(
                            "concatLists: elements must be lists".into(),
                        ))
                    }
                }
            }
            Ok(PrimValue::List(out))
        }
        [_] => Err(DnxError::PrimError("concatLists: expected a list".into())),
        _ => Err(DnxError::PrimError("concatLists: arity".into())),
    }
}

/// `concatStringsSep sep list` — join string list with separator. cppNix
/// `prim_concatStringsSep` (note: arg order is `sep` then the list).
fn prim_concat_strings_sep(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Str(sep), PrimValue::List(parts)] => {
            let mut out = String::new();
            for (i, p) in parts.iter().enumerate() {
                if i > 0 {
                    out.push_str(sep);
                }
                match p {
                    PrimValue::Str(s) | PrimValue::Path(s) => out.push_str(s),
                    _ => {
                        return Err(DnxError::PrimError(
                            "concatStringsSep: list must hold strings".into(),
                        ))
                    }
                }
            }
            Ok(PrimValue::Str(Arc::from(out)))
        }
        [PrimValue::Str(_), _] => Err(DnxError::PrimError(
            "concatStringsSep: second arg must be list".into(),
        )),
        [_, _] => Err(DnxError::PrimError(
            "concatStringsSep: separator must be string".into(),
        )),
        _ => Err(DnxError::PrimError("concatStringsSep: arity".into())),
    }
}

/// `listToAttrs [{name; value;}]` — build a set; on duplicate `name` the FIRST
/// occurrence wins (cppNix `prim_listToAttrs`). Result sorted by key.
fn prim_list_to_attrs(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::List(items)] => {
            let mut out: Vec<(Arc<str>, PrimValue)> = Vec::new();
            for item in items {
                let kvs = match item {
                    PrimValue::AttrSet(kvs) => kvs,
                    _ => {
                        return Err(DnxError::PrimError(
                            "listToAttrs: elements must be attrsets".into(),
                        ))
                    }
                };
                let name = match kvs.iter().find(|(k, _)| k.as_ref() == "name") {
                    Some((_, PrimValue::Str(s))) => s.clone(),
                    Some(_) => {
                        return Err(DnxError::PrimError(
                            "listToAttrs: 'name' must be a string".into(),
                        ))
                    }
                    None => {
                        return Err(DnxError::PrimError(
                            "listToAttrs: element missing 'name'".into(),
                        ))
                    }
                };
                let value = match kvs.iter().find(|(k, _)| k.as_ref() == "value") {
                    Some((_, v)) => v.clone(),
                    None => {
                        return Err(DnxError::PrimError(
                            "listToAttrs: element missing 'value'".into(),
                        ))
                    }
                };
                if !out.iter().any(|(k, _)| *k == name) {
                    out.push((name, value));
                }
            }
            out.sort_by(|a, b| a.0.as_ref().cmp(b.0.as_ref()));
            Ok(PrimValue::AttrSet(out))
        }
        [_] => Err(DnxError::PrimError("listToAttrs: expected a list".into())),
        _ => Err(DnxError::PrimError("listToAttrs: arity".into())),
    }
}

/// `seq e1 e2` — args arrive already forced to WHNF, so this just returns the
/// second. cppNix `prim_seq` (force first, return second).
fn prim_seq(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [_, e2] => Ok(e2.clone()),
        _ => Err(DnxError::PrimError("seq: arity".into())),
    }
}

/// `deepSeq e1 e2` — args arrive fully reduced (the evaluator forces the whole
/// value tree before a prim fires), so deep-forcing is already done; return the
/// second. cppNix `prim_deepSeq`.
fn prim_deep_seq(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [_, e2] => Ok(e2.clone()),
        _ => Err(DnxError::PrimError("deepSeq: arity".into())),
    }
}

/// `replaceStrings from to s` — left-to-right scan; at each position the first
/// matching `from[i]` wins (NOT longest); non-overlapping; empty pattern emits
/// its replacement then the current char. cppNix `prim_replaceStrings`.
fn prim_replace_strings(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    let (from, to, s) = match args {
        [PrimValue::List(from), PrimValue::List(to), PrimValue::Str(s)] => (from, to, s),
        [PrimValue::List(_), PrimValue::List(_), _] => {
            return Err(DnxError::PrimError(
                "replaceStrings: third arg must be string".into(),
            ))
        }
        [_, _, _] => {
            return Err(DnxError::PrimError(
                "replaceStrings: first two args must be lists".into(),
            ))
        }
        _ => return Err(DnxError::PrimError("replaceStrings: arity".into())),
    };
    if from.len() != to.len() {
        return Err(DnxError::PrimError(
            "replaceStrings: 'from' and 'to' must have equal length".into(),
        ));
    }
    let pats: Vec<&str> = from
        .iter()
        .map(|p| match p {
            PrimValue::Str(p) => Ok(p.as_ref()),
            _ => Err(DnxError::PrimError(
                "replaceStrings: 'from' must hold strings".into(),
            )),
        })
        .collect::<Result<_, _>>()?;
    let reps: Vec<&str> = to
        .iter()
        .map(|r| match r {
            PrimValue::Str(r) => Ok(r.as_ref()),
            _ => Err(DnxError::PrimError(
                "replaceStrings: 'to' must hold strings".into(),
            )),
        })
        .collect::<Result<_, _>>()?;
    let bytes = s.as_bytes();
    let mut out = String::with_capacity(s.len());
    let mut p = 0usize;
    while p <= bytes.len() {
        let mut matched = false;
        for (pat, rep) in pats.iter().zip(reps.iter()) {
            if p + pat.len() <= bytes.len() && &s[p..p + pat.len()] == *pat {
                out.push_str(rep);
                if pat.is_empty() {
                    if p < bytes.len() {
                        let cl = char_len(s, p);
                        out.push_str(&s[p..p + cl]);
                        p += cl;
                    } else {
                        p += 1;
                    }
                } else {
                    p += pat.len();
                }
                matched = true;
                break;
            }
        }
        if !matched {
            if p < bytes.len() {
                let cl = char_len(s, p);
                out.push_str(&s[p..p + cl]);
                p += cl;
            } else {
                break;
            }
        }
    }
    Ok(PrimValue::Str(Arc::from(out)))
}

/// Byte length of the UTF-8 char starting at byte index `p` (≥1; clamps at end).
fn char_len(s: &str, p: usize) -> usize {
    s[p..].chars().next().map(char::len_utf8).unwrap_or(1)
}

/// `fromJSON s` — parse a JSON document into a `PrimValue`. Self-contained
/// recursive-descent parser (no external dep): JSON object → sorted AttrSet,
/// array → List, numbers → Int when integral else Float. cppNix
/// `prim_fromJSON`. Pure structural recursion over a finite string.
fn prim_from_json(args: &[PrimValue]) -> Result<PrimValue, DnxError> {
    match args {
        [PrimValue::Str(s)] => {
            let bytes = s.as_bytes();
            let mut pos = 0usize;
            let v = json_parse_value(bytes, &mut pos)?;
            json_skip_ws(bytes, &mut pos);
            if pos != bytes.len() {
                return Err(DnxError::PrimError("fromJSON: trailing data".into()));
            }
            Ok(v)
        }
        [_] => Err(DnxError::PrimError("fromJSON: expected string".into())),
        _ => Err(DnxError::PrimError("fromJSON: arity".into())),
    }
}

fn json_skip_ws(b: &[u8], pos: &mut usize) {
    while *pos < b.len() && matches!(b[*pos], b' ' | b'\t' | b'\n' | b'\r') {
        *pos += 1;
    }
}

fn json_parse_value(b: &[u8], pos: &mut usize) -> Result<PrimValue, DnxError> {
    json_skip_ws(b, pos);
    match b.get(*pos) {
        Some(b'{') => json_parse_object(b, pos),
        Some(b'[') => json_parse_array(b, pos),
        Some(b'"') => Ok(PrimValue::Str(Arc::from(json_parse_string(b, pos)?))),
        Some(b't') => json_parse_lit(b, pos, "true", PrimValue::Bool(true)),
        Some(b'f') => json_parse_lit(b, pos, "false", PrimValue::Bool(false)),
        Some(b'n') => json_parse_lit(b, pos, "null", PrimValue::Null),
        Some(c) if *c == b'-' || c.is_ascii_digit() => json_parse_number(b, pos),
        _ => Err(DnxError::PrimError("fromJSON: unexpected token".into())),
    }
}

fn json_parse_lit(
    b: &[u8],
    pos: &mut usize,
    lit: &str,
    v: PrimValue,
) -> Result<PrimValue, DnxError> {
    if b[*pos..].starts_with(lit.as_bytes()) {
        *pos += lit.len();
        Ok(v)
    } else {
        Err(DnxError::PrimError("fromJSON: invalid literal".into()))
    }
}

fn json_parse_number(b: &[u8], pos: &mut usize) -> Result<PrimValue, DnxError> {
    let start = *pos;
    let mut is_float = false;
    while let Some(&c) = b.get(*pos) {
        match c {
            b'0'..=b'9' | b'-' | b'+' => {}
            b'.' | b'e' | b'E' => is_float = true,
            _ => break,
        }
        *pos += 1;
    }
    let text = std::str::from_utf8(&b[start..*pos])
        .map_err(|_| DnxError::PrimError("fromJSON: invalid number".into()))?;
    if is_float {
        text.parse::<f64>()
            .map(PrimValue::Float)
            .map_err(|_| DnxError::PrimError("fromJSON: invalid number".into()))
    } else {
        text.parse::<i64>()
            .map(PrimValue::Int)
            .map_err(|_| DnxError::PrimError("fromJSON: invalid number".into()))
    }
}

fn json_parse_string(b: &[u8], pos: &mut usize) -> Result<String, DnxError> {
    *pos += 1; // opening quote
    let mut out = String::new();
    loop {
        match b.get(*pos) {
            None => return Err(DnxError::PrimError("fromJSON: unterminated string".into())),
            Some(b'"') => {
                *pos += 1;
                return Ok(out);
            }
            Some(b'\\') => {
                *pos += 1;
                match b.get(*pos) {
                    Some(b'"') => out.push('"'),
                    Some(b'\\') => out.push('\\'),
                    Some(b'/') => out.push('/'),
                    Some(b'n') => out.push('\n'),
                    Some(b't') => out.push('\t'),
                    Some(b'r') => out.push('\r'),
                    Some(b'b') => out.push('\u{0008}'),
                    Some(b'f') => out.push('\u{000C}'),
                    Some(b'u') => {
                        let cp = json_parse_hex4(b, pos)?;
                        out.push(char::from_u32(cp).unwrap_or('\u{FFFD}'));
                    }
                    _ => return Err(DnxError::PrimError("fromJSON: bad escape".into())),
                }
                *pos += 1;
            }
            Some(_) => {
                let cl = b[*pos..]
                    .utf8_chunks()
                    .next()
                    .and_then(|c| c.valid().chars().next())
                    .map(char::len_utf8)
                    .unwrap_or(1);
                let chunk = std::str::from_utf8(&b[*pos..*pos + cl])
                    .map_err(|_| DnxError::PrimError("fromJSON: invalid utf8".into()))?;
                out.push_str(chunk);
                *pos += cl;
            }
        }
    }
}

fn json_parse_hex4(b: &[u8], pos: &mut usize) -> Result<u32, DnxError> {
    let hex = b
        .get(*pos + 1..*pos + 5)
        .ok_or_else(|| DnxError::PrimError("fromJSON: bad \\u escape".into()))?;
    let s = std::str::from_utf8(hex)
        .map_err(|_| DnxError::PrimError("fromJSON: bad \\u escape".into()))?;
    let cp = u32::from_str_radix(s, 16)
        .map_err(|_| DnxError::PrimError("fromJSON: bad \\u escape".into()))?;
    *pos += 4;
    Ok(cp)
}

fn json_parse_array(b: &[u8], pos: &mut usize) -> Result<PrimValue, DnxError> {
    *pos += 1; // '['
    let mut out = Vec::new();
    json_skip_ws(b, pos);
    if b.get(*pos) == Some(&b']') {
        *pos += 1;
        return Ok(PrimValue::List(out));
    }
    loop {
        out.push(json_parse_value(b, pos)?);
        json_skip_ws(b, pos);
        match b.get(*pos) {
            Some(b',') => {
                *pos += 1;
            }
            Some(b']') => {
                *pos += 1;
                return Ok(PrimValue::List(out));
            }
            _ => return Err(DnxError::PrimError("fromJSON: expected ',' or ']'".into())),
        }
    }
}

fn json_parse_object(b: &[u8], pos: &mut usize) -> Result<PrimValue, DnxError> {
    *pos += 1; // '{'
    let mut out: Vec<(Arc<str>, PrimValue)> = Vec::new();
    json_skip_ws(b, pos);
    if b.get(*pos) == Some(&b'}') {
        *pos += 1;
        return Ok(PrimValue::AttrSet(out));
    }
    loop {
        json_skip_ws(b, pos);
        if b.get(*pos) != Some(&b'"') {
            return Err(DnxError::PrimError(
                "fromJSON: object key must be string".into(),
            ));
        }
        let key = json_parse_string(b, pos)?;
        json_skip_ws(b, pos);
        if b.get(*pos) != Some(&b':') {
            return Err(DnxError::PrimError("fromJSON: expected ':'".into()));
        }
        *pos += 1;
        let val = json_parse_value(b, pos)?;
        let key: Arc<str> = Arc::from(key);
        if let Some(slot) = out.iter_mut().find(|(k, _)| *k == key) {
            slot.1 = val; // JSON dup key: last wins
        } else {
            out.push((key, val));
        }
        json_skip_ws(b, pos);
        match b.get(*pos) {
            Some(b',') => {
                *pos += 1;
            }
            Some(b'}') => {
                *pos += 1;
                out.sort_by(|a, b| a.0.as_ref().cmp(b.0.as_ref()));
                return Ok(PrimValue::AttrSet(out));
            }
            _ => return Err(DnxError::PrimError("fromJSON: expected ',' or '}'".into())),
        }
    }
}

/// Nix prim table: arithmetic + comparison prims. Sorted alphabetically for deterministic prim_id.
pub fn nix_prim_table() -> PrimTable {
    let mut t = PrimTable::empty();
    t.register("add", 2, PrimImpl::Pure(prim_add));
    t.register("abort", 1, PrimImpl::Pure(prim_abort));
    t.register("attr_names", 1, PrimImpl::Pure(prim_attr_names));
    t.register("attr_values", 1, PrimImpl::Pure(prim_attr_values));
    t.register("base_name_of", 1, PrimImpl::Pure(prim_base_name_of));
    t.register(
        "derivation_strict",
        1,
        PrimImpl::Pure(prim_derivation_strict),
    );
    t.register("dir_of", 1, PrimImpl::Pure(prim_dir_of));
    t.register("is_attrs", 1, PrimImpl::Pure(prim_is_attrs));
    t.register("is_bool", 1, PrimImpl::Pure(prim_is_bool));
    t.register("is_path", 1, PrimImpl::Pure(prim_is_path));
    t.register("throw", 1, PrimImpl::Pure(prim_throw));
    t.register("to_float", 1, PrimImpl::Pure(prim_to_float));
    t.register("to_json", 1, PrimImpl::Pure(prim_to_json));
    t.register("bit_and", 2, PrimImpl::Pure(prim_bit_and));
    t.register("bit_or", 2, PrimImpl::Pure(prim_bit_or));
    t.register("bit_xor", 2, PrimImpl::Pure(prim_bit_xor));
    t.register("div", 2, PrimImpl::Pure(prim_div));
    t.register("empty_attr_set", 0, PrimImpl::Pure(prim_empty_attr_set));
    t.register("eq", 2, PrimImpl::Pure(prim_eq));
    t.register("ge", 2, PrimImpl::Pure(prim_ge));
    t.register("gt", 2, PrimImpl::Pure(prim_gt));
    t.register("has_attr", 2, PrimImpl::Pure(prim_has_attr));
    t.register("insert", 3, PrimImpl::Pure(prim_insert));
    t.register("is_float", 1, PrimImpl::Pure(prim_is_float));
    t.register("is_function", 1, PrimImpl::Pure(prim_is_function));
    t.register("is_int", 1, PrimImpl::Pure(prim_is_int));
    t.register("is_list", 1, PrimImpl::Pure(prim_is_list));
    t.register("is_null", 1, PrimImpl::Pure(prim_is_null));
    t.register("is_string", 1, PrimImpl::Pure(prim_is_string));
    t.register("le", 2, PrimImpl::Pure(prim_le));
    t.register("lt", 2, PrimImpl::Pure(prim_lt));
    t.register("mk_singleton", 2, PrimImpl::Pure(prim_mk_singleton));
    t.register("mul", 2, PrimImpl::Pure(prim_mul));
    t.register("ne", 2, PrimImpl::Pure(prim_ne));
    t.register("neg", 1, PrimImpl::Pure(prim_neg));
    t.register("select", 2, PrimImpl::Pure(prim_select));
    t.register("select_or", 3, PrimImpl::Pure(prim_select_or));
    t.register("string_length", 1, PrimImpl::Pure(prim_string_length));
    t.register("substring", 3, PrimImpl::Pure(prim_substring));
    t.register("sub", 2, PrimImpl::Pure(prim_sub));
    t.register("to_int", 1, PrimImpl::Pure(prim_to_int));
    t.register("to_string", 1, PrimImpl::Pure(prim_to_string));
    t.register("type_of", 1, PrimImpl::Pure(prim_type_of));
    t.register("update", 2, PrimImpl::Pure(prim_update));
    t.register("cat_attrs", 2, PrimImpl::Pure(prim_cat_attrs));
    t.register("concat_lists", 1, PrimImpl::Pure(prim_concat_lists));
    t.register(
        "concat_strings_sep",
        2,
        PrimImpl::Pure(prim_concat_strings_sep),
    );
    t.register("deep_seq", 2, PrimImpl::Pure(prim_deep_seq));
    t.register("from_json", 1, PrimImpl::Pure(prim_from_json));
    t.register("get_attr", 2, PrimImpl::Pure(prim_get_attr));
    t.register("intersect_attrs", 2, PrimImpl::Pure(prim_intersect_attrs));
    t.register("list_to_attrs", 1, PrimImpl::Pure(prim_list_to_attrs));
    t.register("remove_attrs", 2, PrimImpl::Pure(prim_remove_attrs));
    t.register("replace_strings", 3, PrimImpl::Pure(prim_replace_strings));
    t.register("seq", 2, PrimImpl::Pure(prim_seq));
    t
}

/// Bind a `NixPrimFun` to its engine-side eval entry by table-key lookup.
pub fn nixprimfun_to_entry(f: &NixPrimFun) -> Option<PrimFunEntry> {
    let table = nix_prim_table();
    let name = nixprimfun_name(f)?;
    let id = table.lookup(name)?;
    table.make_entry(id)
}

/// Lift a `NixPrimVal` literal into the engine's `PrimValue`.
pub fn nixprimval_to_value(v: &NixPrimVal) -> Option<PrimValue> {
    Some(match v {
        NixPrimVal::Int(n) => PrimValue::Int(*n),
        NixPrimVal::Float(f) => PrimValue::Float(*f),
        NixPrimVal::Str(s) => PrimValue::Str(s.clone()),
        NixPrimVal::Bool(b) => PrimValue::Bool(*b),
        NixPrimVal::Path(p) => PrimValue::Path(p.clone()),
        NixPrimVal::Null => PrimValue::Null,
    })
}

/// Map a `NixPrimFun` variant (incl. nix-spelled `Builtin` aliases) to its
/// `nix_prim_table` key.
pub fn nixprimfun_name(f: &NixPrimFun) -> Option<&'static str> {
    Some(match f {
        NixPrimFun::Add => "add",
        NixPrimFun::Sub => "sub",
        NixPrimFun::Mul => "mul",
        NixPrimFun::Div => "div",
        NixPrimFun::Neg => "neg",
        NixPrimFun::Eq => "eq",
        NixPrimFun::Ne => "ne",
        NixPrimFun::Lt => "lt",
        NixPrimFun::Le => "le",
        NixPrimFun::Gt => "gt",
        NixPrimFun::Ge => "ge",
        NixPrimFun::Select => "select",
        NixPrimFun::SelectOr => "select_or",
        NixPrimFun::EmptyAttrSet => "empty_attr_set",
        NixPrimFun::HasAttr => "has_attr",
        NixPrimFun::Insert => "insert",
        NixPrimFun::MkSingleton => "mk_singleton",
        NixPrimFun::Update => "update",
        NixPrimFun::TypeOf => "type_of",
        NixPrimFun::IsFunction => "is_function",
        NixPrimFun::IsInt => "is_int",
        NixPrimFun::IsFloat => "is_float",
        NixPrimFun::IsString => "is_string",
        NixPrimFun::IsNull => "is_null",
        NixPrimFun::IsList => "is_list",
        NixPrimFun::StringLength => "string_length",
        NixPrimFun::Substring => "substring",
        NixPrimFun::ToString2 => "to_string",
        NixPrimFun::ToInt => "to_int",
        NixPrimFun::BitAnd => "bit_and",
        NixPrimFun::BitOr => "bit_or",
        NixPrimFun::BitXor => "bit_xor",
        NixPrimFun::DerivationStrict => "derivation_strict",
        NixPrimFun::AttrNames => "attr_names",
        NixPrimFun::AttrValues => "attr_values",
        NixPrimFun::IsAttrs => "is_attrs",
        NixPrimFun::IsBool => "is_bool",
        NixPrimFun::IsPath => "is_path",
        NixPrimFun::ToFloat => "to_float",
        NixPrimFun::ToJSON => "to_json",
        NixPrimFun::Throw => "throw",
        NixPrimFun::Abort => "abort",
        NixPrimFun::Builtin(name) => match name.as_ref() {
            "derivationStrict" => "derivation_strict",
            "attrNames" => "attr_names",
            "attrValues" => "attr_values",
            "isAttrs" => "is_attrs",
            "isBool" => "is_bool",
            "isPath" => "is_path",
            "toFloat" => "to_float",
            "toJSON" => "to_json",
            "throw" => "throw",
            "abort" => "abort",
            "baseNameOf" => "base_name_of",
            "dirOf" => "dir_of",
            "getAttr" => "get_attr",
            "removeAttrs" => "remove_attrs",
            "intersectAttrs" => "intersect_attrs",
            "catAttrs" => "cat_attrs",
            "concatLists" => "concat_lists",
            "concatStringsSep" => "concat_strings_sep",
            "listToAttrs" => "list_to_attrs",
            "seq" => "seq",
            "deepSeq" => "deep_seq",
            "replaceStrings" => "replace_strings",
            "fromJSON" => "from_json",
            "typeOf" => "type_of",
            "isFunction" => "is_function",
            "isInt" => "is_int",
            "isFloat" => "is_float",
            "isString" => "is_string",
            "isNull" => "is_null",
            "isList" => "is_list",
            "stringLength" => "string_length",
            "substring" => "substring",
            "toString" => "to_string",
            "toInt" => "to_int",
            "bitAnd" => "bit_and",
            "bitOr" => "bit_or",
            "bitXor" => "bit_xor",
            _ => return None,
        },
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prim_string_length() {
        let result = prim_string_length(&[PrimValue::Str(Arc::from("hello"))]);
        assert_eq!(result, Ok(PrimValue::Int(5)));
    }

    #[test]
    fn test_prim_string_length_empty() {
        let result = prim_string_length(&[PrimValue::Str(Arc::from(""))]);
        assert_eq!(result, Ok(PrimValue::Int(0)));
    }

    #[test]
    fn test_prim_string_length_error() {
        let result = prim_string_length(&[PrimValue::Int(42)]);
        assert!(result.is_err());
    }

    #[test]
    fn test_prim_substring_basic() {
        let result = prim_substring(&[
            PrimValue::Int(1),
            PrimValue::Int(2),
            PrimValue::Str(Arc::from("hello")),
        ]);
        assert_eq!(result, Ok(PrimValue::Str(Arc::from("el"))));
    }

    #[test]
    fn test_prim_substring_start_zero() {
        let result = prim_substring(&[
            PrimValue::Int(0),
            PrimValue::Int(3),
            PrimValue::Str(Arc::from("hello")),
        ]);
        assert_eq!(result, Ok(PrimValue::Str(Arc::from("hel"))));
    }

    #[test]
    fn test_prim_substring_out_of_bounds() {
        let result = prim_substring(&[
            PrimValue::Int(10),
            PrimValue::Int(5),
            PrimValue::Str(Arc::from("hello")),
        ]);
        assert_eq!(result, Ok(PrimValue::Str(Arc::from(""))));
    }

    #[test]
    fn test_prim_substring_negative_start() {
        let result = prim_substring(&[
            PrimValue::Int(-5),
            PrimValue::Int(3),
            PrimValue::Str(Arc::from("hello")),
        ]);
        assert_eq!(result, Ok(PrimValue::Str(Arc::from("hel"))));
    }

    #[test]
    fn test_prim_substring_negative_len() {
        let result = prim_substring(&[
            PrimValue::Int(1),
            PrimValue::Int(-5),
            PrimValue::Str(Arc::from("hello")),
        ]);
        assert_eq!(result, Ok(PrimValue::Str(Arc::from(""))));
    }

    #[test]
    fn test_prim_to_string_int() {
        let result = prim_to_string(&[PrimValue::Int(42)]);
        assert_eq!(result, Ok(PrimValue::Str(Arc::from("42"))));
    }

    #[test]
    fn test_prim_to_string_float() {
        let result = prim_to_string(&[PrimValue::Float(3.5)]);
        assert_eq!(result, Ok(PrimValue::Str(Arc::from("3.5"))));
    }

    #[test]
    fn test_prim_to_string_str() {
        let result = prim_to_string(&[PrimValue::Str(Arc::from("hello"))]);
        assert_eq!(result, Ok(PrimValue::Str(Arc::from("hello"))));
    }

    #[test]
    fn test_prim_to_string_path() {
        let result = prim_to_string(&[PrimValue::Path(Arc::from("/tmp"))]);
        assert_eq!(result, Ok(PrimValue::Str(Arc::from("/tmp"))));
    }

    #[test]
    fn test_prim_to_string_bool_true() {
        let result = prim_to_string(&[PrimValue::Bool(true)]);
        assert_eq!(result, Ok(PrimValue::Str(Arc::from("1"))));
    }

    #[test]
    fn test_prim_to_string_bool_false() {
        let result = prim_to_string(&[PrimValue::Bool(false)]);
        assert_eq!(result, Ok(PrimValue::Str(Arc::from(""))));
    }

    #[test]
    fn test_prim_to_string_null() {
        let result = prim_to_string(&[PrimValue::Null]);
        assert_eq!(result, Ok(PrimValue::Str(Arc::from(""))));
    }

    #[test]
    fn test_prim_bit_and() {
        let result = prim_bit_and(&[PrimValue::Int(12), PrimValue::Int(10)]);
        assert_eq!(result, Ok(PrimValue::Int(8))); // 12 & 10 = 8
    }

    #[test]
    fn test_prim_bit_or() {
        let result = prim_bit_or(&[PrimValue::Int(12), PrimValue::Int(10)]);
        assert_eq!(result, Ok(PrimValue::Int(14))); // 12 | 10 = 14
    }

    #[test]
    fn test_prim_bit_xor() {
        let result = prim_bit_xor(&[PrimValue::Int(12), PrimValue::Int(10)]);
        assert_eq!(result, Ok(PrimValue::Int(6))); // 12 ^ 10 = 6
    }

    #[test]
    fn test_prim_to_int_valid() {
        let result = prim_to_int(&[PrimValue::Str(Arc::from("42"))]);
        assert_eq!(result, Ok(PrimValue::Int(42)));
    }

    #[test]
    fn test_prim_to_int_negative() {
        let result = prim_to_int(&[PrimValue::Str(Arc::from("-100"))]);
        assert_eq!(result, Ok(PrimValue::Int(-100)));
    }

    #[test]
    fn test_prim_to_int_whitespace() {
        let result = prim_to_int(&[PrimValue::Str(Arc::from("  123  "))]);
        assert_eq!(result, Ok(PrimValue::Int(123)));
    }

    #[test]
    fn test_prim_to_int_invalid() {
        let result = prim_to_int(&[PrimValue::Str(Arc::from("not a number"))]);
        assert!(result.is_err());
    }

    // ------------------------------------------------------------------------
    // Integer overflow: must be a typed PrimError, never a panic. Faithful to
    // Nix (overflow is an error, not silent wrap). See review prim.rs:112-153.
    // ------------------------------------------------------------------------

    fn is_prim_err(r: Result<PrimValue, DnxError>) -> bool {
        matches!(r, Err(DnxError::PrimError(_)))
    }

    #[test]
    fn test_prim_add_overflow_is_typed_error() {
        assert!(is_prim_err(prim_add(&[
            PrimValue::Int(i64::MAX),
            PrimValue::Int(1),
        ])));
    }

    #[test]
    fn test_prim_sub_overflow_is_typed_error() {
        assert!(is_prim_err(prim_sub(&[
            PrimValue::Int(i64::MIN),
            PrimValue::Int(1),
        ])));
    }

    #[test]
    fn test_prim_mul_overflow_is_typed_error() {
        assert!(is_prim_err(prim_mul(&[
            PrimValue::Int(i64::MAX),
            PrimValue::Int(2),
        ])));
    }

    #[test]
    fn test_prim_div_min_by_neg_one_is_typed_error() {
        assert!(is_prim_err(prim_div(&[
            PrimValue::Int(i64::MIN),
            PrimValue::Int(-1),
        ])));
    }

    #[test]
    fn test_prim_div_by_zero_still_typed_error() {
        assert!(is_prim_err(prim_div(&[
            PrimValue::Int(1),
            PrimValue::Int(0),
        ])));
    }

    #[test]
    fn test_prim_neg_min_is_typed_error() {
        assert!(is_prim_err(prim_neg(&[PrimValue::Int(i64::MIN)])));
    }

    #[test]
    fn test_prim_substring_huge_args_no_panic() {
        let result = prim_substring(&[
            PrimValue::Int(i64::MAX),
            PrimValue::Int(i64::MAX),
            PrimValue::Str(Arc::from("hello")),
        ]);
        assert_eq!(result, Ok(PrimValue::Str(Arc::from(""))));
    }

    #[test]
    fn test_prim_substring_start_in_bounds_huge_len_no_panic() {
        // start within string, len so large `start + len` would overflow usize.
        let result = prim_substring(&[
            PrimValue::Int(1),
            PrimValue::Int(i64::MAX),
            PrimValue::Str(Arc::from("hello")),
        ]);
        assert_eq!(result, Ok(PrimValue::Str(Arc::from("ello"))));
    }

    // ------------------------------------------------------------------------
    // Newly-wired pure/scalar builtins (review builtins-coverage.md §1c).
    // ------------------------------------------------------------------------

    fn aset(pairs: &[(&str, PrimValue)]) -> PrimValue {
        PrimValue::AttrSet(
            pairs
                .iter()
                .map(|(k, v)| (Arc::from(*k), v.clone()))
                .collect(),
        )
    }

    #[test]
    fn test_eq_attrset_deep_structural() {
        let a = aset(&[("a", PrimValue::Int(1)), ("b", PrimValue::Int(2))]);
        let b = aset(&[("a", PrimValue::Int(1)), ("b", PrimValue::Int(2))]);
        assert_eq!(prim_eq(&[a, b]), Ok(PrimValue::Bool(true)));
    }

    #[test]
    fn test_eq_attrset_nested_value_differs() {
        let a = aset(&[("a", aset(&[("c", PrimValue::Int(1))]))]);
        let b = aset(&[("a", aset(&[("c", PrimValue::Int(2))]))]);
        assert_eq!(prim_eq(&[a, b]), Ok(PrimValue::Bool(false)));
    }

    #[test]
    fn test_eq_attrset_distinct_keys_unequal() {
        let a = aset(&[("a", PrimValue::Int(1))]);
        let b = aset(&[("b", PrimValue::Int(1))]);
        assert_eq!(prim_eq(&[a, b]), Ok(PrimValue::Bool(false)));
    }

    #[test]
    fn test_eq_list_pairwise_and_length() {
        let same = vec![PrimValue::Int(1), PrimValue::Int(2), PrimValue::Int(3)];
        assert_eq!(
            prim_eq(&[PrimValue::List(same.clone()), PrimValue::List(same)]),
            Ok(PrimValue::Bool(true))
        );
        assert_eq!(
            prim_eq(&[
                PrimValue::List(vec![PrimValue::Int(1), PrimValue::Int(2)]),
                PrimValue::List(vec![
                    PrimValue::Int(1),
                    PrimValue::Int(2),
                    PrimValue::Int(3)
                ]),
            ]),
            Ok(PrimValue::Bool(false))
        );
    }

    #[test]
    fn test_eq_cross_type_is_false_not_error() {
        let a = aset(&[("a", PrimValue::Int(1))]);
        assert_eq!(prim_eq(&[a, PrimValue::Null]), Ok(PrimValue::Bool(false)));
    }

    #[test]
    fn test_eq_function_is_typed_error_never_equal() {
        // cppNix: comparing functions for equality throws. No false-equal: two
        // lambdas must NOT compare equal.
        assert!(is_prim_err(prim_eq(&[
            PrimValue::Lambda,
            PrimValue::Lambda
        ])));
        // A function nested inside an attrset propagates the incomparability.
        let a = aset(&[("f", PrimValue::Lambda)]);
        let b = aset(&[("f", PrimValue::Lambda)]);
        assert!(is_prim_err(prim_eq(&[a, b])));
        // `!=` on functions likewise errors (no false-equal via negation).
        assert!(is_prim_err(prim_ne(&[
            PrimValue::Lambda,
            PrimValue::Lambda
        ])));
    }

    #[test]
    fn test_prim_attr_names() {
        let s = aset(&[("b", PrimValue::Int(2)), ("a", PrimValue::Int(1))]);
        assert_eq!(
            prim_attr_names(&[s]),
            Ok(PrimValue::List(vec![
                PrimValue::Str(Arc::from("b")),
                PrimValue::Str(Arc::from("a")),
            ]))
        );
    }

    #[test]
    fn test_prim_attr_names_empty() {
        assert_eq!(
            prim_attr_names(&[PrimValue::AttrSet(vec![])]),
            Ok(PrimValue::List(vec![]))
        );
    }

    #[test]
    fn test_prim_attr_names_type_error() {
        assert!(is_prim_err(prim_attr_names(&[PrimValue::Int(1)])));
    }

    #[test]
    fn test_prim_attr_values() {
        let s = aset(&[("a", PrimValue::Int(1)), ("b", PrimValue::Int(2))]);
        assert_eq!(
            prim_attr_values(&[s]),
            Ok(PrimValue::List(vec![PrimValue::Int(1), PrimValue::Int(2)]))
        );
    }

    #[test]
    fn test_prim_attr_values_type_error() {
        assert!(is_prim_err(prim_attr_values(&[PrimValue::Str(Arc::from(
            "x"
        ))])));
    }

    #[test]
    fn test_prim_is_attrs() {
        assert_eq!(
            prim_is_attrs(&[PrimValue::AttrSet(vec![])]),
            Ok(PrimValue::Bool(true))
        );
        assert_eq!(
            prim_is_attrs(&[PrimValue::Int(1)]),
            Ok(PrimValue::Bool(false))
        );
    }

    #[test]
    fn test_prim_is_bool() {
        assert_eq!(
            prim_is_bool(&[PrimValue::Bool(true)]),
            Ok(PrimValue::Bool(true))
        );
        assert_eq!(
            prim_is_bool(&[PrimValue::Int(0)]),
            Ok(PrimValue::Bool(false))
        );
    }

    #[test]
    fn test_prim_is_path() {
        assert_eq!(
            prim_is_path(&[PrimValue::Path(Arc::from("/x"))]),
            Ok(PrimValue::Bool(true))
        );
        assert_eq!(
            prim_is_path(&[PrimValue::Str(Arc::from("/x"))]),
            Ok(PrimValue::Bool(false))
        );
    }

    #[test]
    fn test_prim_to_float() {
        assert_eq!(
            prim_to_float(&[PrimValue::Str(Arc::from("3.5"))]),
            Ok(PrimValue::Float(3.5))
        );
        assert_eq!(
            prim_to_float(&[PrimValue::Int(2)]),
            Ok(PrimValue::Float(2.0))
        );
        assert_eq!(
            prim_to_float(&[PrimValue::Float(1.25)]),
            Ok(PrimValue::Float(1.25))
        );
    }

    #[test]
    fn test_prim_to_float_invalid() {
        assert!(is_prim_err(prim_to_float(&[PrimValue::Str(Arc::from(
            "nope"
        ))])));
    }

    #[test]
    fn test_prim_to_json_scalars() {
        assert_eq!(
            prim_to_json(&[PrimValue::Int(42)]),
            Ok(PrimValue::Str(Arc::from("42")))
        );
        assert_eq!(
            prim_to_json(&[PrimValue::Bool(true)]),
            Ok(PrimValue::Str(Arc::from("true")))
        );
        assert_eq!(
            prim_to_json(&[PrimValue::Null]),
            Ok(PrimValue::Str(Arc::from("null")))
        );
        assert_eq!(
            prim_to_json(&[PrimValue::Str(Arc::from("a\"b"))]),
            Ok(PrimValue::Str(Arc::from("\"a\\\"b\"")))
        );
    }

    #[test]
    fn test_prim_to_json_attrset() {
        let s = aset(&[("a", PrimValue::Int(1)), ("b", PrimValue::Bool(false))]);
        assert_eq!(
            prim_to_json(&[s]),
            Ok(PrimValue::Str(Arc::from("{\"a\":1,\"b\":false}")))
        );
    }

    #[test]
    fn test_prim_to_json_list() {
        let l = PrimValue::List(vec![PrimValue::Int(1), PrimValue::Int(2)]);
        assert_eq!(prim_to_json(&[l]), Ok(PrimValue::Str(Arc::from("[1,2]"))));
    }

    #[test]
    fn test_prim_to_json_function_errors() {
        assert!(is_prim_err(prim_to_json(&[PrimValue::Lambda])));
    }

    #[test]
    fn test_prim_throw_is_error() {
        assert!(is_prim_err(prim_throw(&[PrimValue::Str(Arc::from(
            "boom"
        ))])));
    }

    #[test]
    fn test_prim_abort_is_error() {
        assert!(is_prim_err(prim_abort(&[PrimValue::Str(Arc::from(
            "halt"
        ))])));
    }

    #[test]
    fn test_prim_base_name_of() {
        assert_eq!(
            prim_base_name_of(&[PrimValue::Str(Arc::from("/foo/bar/baz.nix"))]),
            Ok(PrimValue::Str(Arc::from("baz.nix")))
        );
        assert_eq!(
            prim_base_name_of(&[PrimValue::Path(Arc::from("/a/b"))]),
            Ok(PrimValue::Str(Arc::from("b")))
        );
        assert_eq!(
            prim_base_name_of(&[PrimValue::Str(Arc::from("/foo/bar/"))]),
            Ok(PrimValue::Str(Arc::from("bar")))
        );
    }

    #[test]
    fn test_prim_dir_of() {
        assert_eq!(
            prim_dir_of(&[PrimValue::Str(Arc::from("/foo/bar/baz.nix"))]),
            Ok(PrimValue::Str(Arc::from("/foo/bar")))
        );
        assert_eq!(
            prim_dir_of(&[PrimValue::Path(Arc::from("/a/b"))]),
            Ok(PrimValue::Path(Arc::from("/a")))
        );
        assert_eq!(
            prim_dir_of(&[PrimValue::Str(Arc::from("noslash"))]),
            Ok(PrimValue::Str(Arc::from(".")))
        );
    }

    #[test]
    fn test_new_builtins_registered() {
        let t = nix_prim_table();
        for key in [
            "attr_names",
            "attr_values",
            "is_attrs",
            "is_bool",
            "is_path",
            "to_float",
            "to_json",
            "throw",
            "abort",
            "base_name_of",
            "dir_of",
        ] {
            assert!(t.lookup(key).is_some(), "missing prim key: {key}");
        }
    }

    #[test]
    fn test_builtin_aliases_resolve() {
        for name in [
            "attrNames",
            "attrValues",
            "isAttrs",
            "isBool",
            "isPath",
            "toFloat",
            "toJSON",
            "throw",
            "abort",
            "baseNameOf",
            "dirOf",
        ] {
            assert!(
                nixprimfun_name(&NixPrimFun::Builtin(Arc::from(name))).is_some(),
                "alias not mapped: {name}"
            );
        }
    }

    #[test]
    fn test_prim_arithmetic_still_works() {
        assert_eq!(
            prim_add(&[PrimValue::Int(2), PrimValue::Int(3)]),
            Ok(PrimValue::Int(5))
        );
        assert_eq!(
            prim_sub(&[PrimValue::Int(10), PrimValue::Int(3)]),
            Ok(PrimValue::Int(7))
        );
        assert_eq!(
            prim_mul(&[PrimValue::Int(2), PrimValue::Int(4)]),
            Ok(PrimValue::Int(8))
        );
        assert_eq!(
            prim_div(&[PrimValue::Int(9), PrimValue::Int(3)]),
            Ok(PrimValue::Int(3))
        );
        assert_eq!(prim_neg(&[PrimValue::Int(5)]), Ok(PrimValue::Int(-5)));
    }

    #[test]
    fn test_prim_int_float_coercion() {
        let i = PrimValue::Int;
        let f = PrimValue::Float;
        assert_eq!(prim_add(&[i(1), f(2.0)]), Ok(f(3.0)));
        assert_eq!(prim_add(&[f(2.0), i(1)]), Ok(f(3.0)));
        assert_eq!(prim_sub(&[i(5), f(1.5)]), Ok(f(3.5)));
        assert_eq!(prim_sub(&[f(1.5), i(5)]), Ok(f(-3.5)));
        assert_eq!(prim_mul(&[i(1), f(2.5)]), Ok(f(2.5)));
        assert_eq!(prim_mul(&[f(2.5), i(2)]), Ok(f(5.0)));
        assert_eq!(prim_div(&[i(5), f(2.0)]), Ok(f(2.5)));
        assert_eq!(prim_div(&[f(5.0), i(2)]), Ok(f(2.5)));
        assert_eq!(prim_lt(&[i(1), f(2.0)]), Ok(PrimValue::Bool(true)));
        assert_eq!(prim_lt(&[f(2.0), i(1)]), Ok(PrimValue::Bool(false)));
        assert_eq!(prim_le(&[i(2), f(2.0)]), Ok(PrimValue::Bool(true)));
        assert_eq!(prim_gt(&[f(2.0), i(1)]), Ok(PrimValue::Bool(true)));
        assert_eq!(prim_ge(&[i(2), f(2.0)]), Ok(PrimValue::Bool(true)));
    }

    // ------------------------------------------------------------------------
    // Group: data-only scalar/string/attrset builtins (nix-effects-deps.md §A,
    // gen-dnx-readiness.md #9). Args arrive already reduced.
    // ------------------------------------------------------------------------

    fn s(x: &str) -> PrimValue {
        PrimValue::Str(Arc::from(x))
    }

    #[test]
    fn test_get_attr() {
        let set = aset(&[("a", PrimValue::Int(1)), ("b", PrimValue::Int(2))]);
        assert_eq!(prim_get_attr(&[s("b"), set.clone()]), Ok(PrimValue::Int(2)));
        assert!(is_prim_err(prim_get_attr(&[s("z"), set])));
    }

    #[test]
    fn test_remove_attrs() {
        let set = aset(&[
            ("a", PrimValue::Int(1)),
            ("b", PrimValue::Int(2)),
            ("c", PrimValue::Int(3)),
        ]);
        assert_eq!(
            prim_remove_attrs(&[set, PrimValue::List(vec![s("b")])]),
            Ok(aset(&[("a", PrimValue::Int(1)), ("c", PrimValue::Int(3))]))
        );
    }

    #[test]
    fn test_intersect_attrs() {
        let a = aset(&[("x", PrimValue::Int(0)), ("y", PrimValue::Int(0))]);
        let b = aset(&[("y", PrimValue::Int(9)), ("z", PrimValue::Int(8))]);
        // keeps names in both, with b's values → only y=9.
        assert_eq!(
            prim_intersect_attrs(&[a, b]),
            Ok(aset(&[("y", PrimValue::Int(9))]))
        );
    }

    #[test]
    fn test_cat_attrs() {
        let s1 = aset(&[("a", PrimValue::Int(1))]);
        let s2 = aset(&[("b", PrimValue::Int(2))]); // no 'a' → skipped
        let s3 = aset(&[("a", PrimValue::Int(3))]);
        assert_eq!(
            prim_cat_attrs(&[s("a"), PrimValue::List(vec![s1, s2, s3])]),
            Ok(PrimValue::List(vec![PrimValue::Int(1), PrimValue::Int(3)]))
        );
    }

    #[test]
    fn test_concat_lists() {
        let ll = PrimValue::List(vec![
            PrimValue::List(vec![PrimValue::Int(1), PrimValue::Int(2)]),
            PrimValue::List(vec![PrimValue::Int(3)]),
        ]);
        assert_eq!(
            prim_concat_lists(&[ll]),
            Ok(PrimValue::List(vec![
                PrimValue::Int(1),
                PrimValue::Int(2),
                PrimValue::Int(3)
            ]))
        );
    }

    #[test]
    fn test_concat_strings_sep() {
        let list = PrimValue::List(vec![s("a"), s("b"), s("c")]);
        assert_eq!(prim_concat_strings_sep(&[s(", "), list]), Ok(s("a, b, c")));
        assert_eq!(
            prim_concat_strings_sep(&[s("-"), PrimValue::List(vec![])]),
            Ok(s(""))
        );
    }

    #[test]
    fn test_list_to_attrs_first_wins() {
        let mk = |n: &str, v: i64| aset(&[("name", s(n)), ("value", PrimValue::Int(v))]);
        // duplicate "a": first (1) wins, NOT 9.
        let items = PrimValue::List(vec![mk("a", 1), mk("b", 2), mk("a", 9)]);
        assert_eq!(
            prim_list_to_attrs(&[items]),
            Ok(aset(&[("a", PrimValue::Int(1)), ("b", PrimValue::Int(2))]))
        );
    }

    #[test]
    fn test_seq_and_deep_seq_return_second() {
        assert_eq!(prim_seq(&[PrimValue::Int(1), s("x")]), Ok(s("x")));
        assert_eq!(
            prim_deep_seq(&[PrimValue::List(vec![PrimValue::Int(1)]), PrimValue::Int(7)]),
            Ok(PrimValue::Int(7))
        );
    }

    #[test]
    fn test_replace_strings_basic() {
        // first-match-wins: at pos 1 "oo"→"a", at pos 3 "a"→"i" ⇒ "fabir".
        assert_eq!(
            prim_replace_strings(&[
                PrimValue::List(vec![s("oo"), s("a")]),
                PrimValue::List(vec![s("a"), s("i")]),
                s("foobar"),
            ]),
            Ok(s("fabir"))
        );
    }

    #[test]
    fn test_replace_strings_empty_pattern() {
        // empty pattern fires at every position incl. end: "_a_b_" .
        assert_eq!(
            prim_replace_strings(&[
                PrimValue::List(vec![s("")]),
                PrimValue::List(vec![s("_")]),
                s("ab"),
            ]),
            Ok(s("_a_b_"))
        );
    }

    #[test]
    fn test_replace_strings_length_mismatch_errors() {
        assert!(is_prim_err(prim_replace_strings(&[
            PrimValue::List(vec![s("a")]),
            PrimValue::List(vec![]),
            s("a"),
        ])));
    }

    #[test]
    fn test_from_json_scalars() {
        assert_eq!(prim_from_json(&[s("42")]), Ok(PrimValue::Int(42)));
        assert_eq!(prim_from_json(&[s("3.5")]), Ok(PrimValue::Float(3.5)));
        assert_eq!(prim_from_json(&[s("true")]), Ok(PrimValue::Bool(true)));
        assert_eq!(prim_from_json(&[s("null")]), Ok(PrimValue::Null));
        assert_eq!(prim_from_json(&[s("\"hi\\n\"")]), Ok(s("hi\n")));
    }

    #[test]
    fn test_from_json_nested() {
        let r = prim_from_json(&[s("{\"b\":1,\"a\":[1,2,{\"c\":true}]}")]);
        assert_eq!(
            r,
            Ok(aset(&[
                (
                    "a",
                    PrimValue::List(vec![
                        PrimValue::Int(1),
                        PrimValue::Int(2),
                        aset(&[("c", PrimValue::Bool(true))]),
                    ])
                ),
                ("b", PrimValue::Int(1)),
            ]))
        );
    }

    #[test]
    fn test_from_json_roundtrip_with_to_json() {
        let v = aset(&[(
            "k",
            PrimValue::List(vec![PrimValue::Int(1), PrimValue::Bool(false)]),
        )]);
        let json = prim_to_json(std::slice::from_ref(&v));
        assert!(
            matches!(&json, Ok(PrimValue::Str(_))),
            "toJSON must return a string"
        );
        if let Ok(PrimValue::Str(j)) = json {
            assert_eq!(prim_from_json(&[PrimValue::Str(j)]), Ok(v));
        }
    }

    #[test]
    fn test_from_json_rejects_trailing() {
        assert!(is_prim_err(prim_from_json(&[s("1 2")])));
        assert!(is_prim_err(prim_from_json(&[s("{")])));
    }

    #[test]
    fn test_new_group_registered() {
        let t = nix_prim_table();
        for key in [
            "get_attr",
            "remove_attrs",
            "intersect_attrs",
            "cat_attrs",
            "concat_lists",
            "concat_strings_sep",
            "list_to_attrs",
            "seq",
            "deep_seq",
            "replace_strings",
            "from_json",
        ] {
            assert!(t.lookup(key).is_some(), "missing prim key: {key}");
        }
    }

    #[test]
    fn test_new_group_aliases_resolve() {
        for name in [
            "getAttr",
            "removeAttrs",
            "intersectAttrs",
            "catAttrs",
            "concatLists",
            "concatStringsSep",
            "listToAttrs",
            "seq",
            "deepSeq",
            "replaceStrings",
            "fromJSON",
        ] {
            assert!(
                nixprimfun_name(&NixPrimFun::Builtin(Arc::from(name))).is_some(),
                "alias not mapped: {name}"
            );
        }
    }
}
