use std::sync::Arc;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ConstId(pub u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct IndId(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Symbol {
    Const(ConstId),
    Ind(IndId),
    Ctor(IndId, u32),
    Elim(IndId),
}

impl Symbol {
    /// Free-var name carried into the net (`free_slots` key). `§` prefix = kernel symbol.
    pub fn encode(&self) -> Arc<str> {
        match self {
            Symbol::Const(c) => format!("§c:{}", c.0),
            Symbol::Ind(i) => format!("§i:{}", i.0),
            Symbol::Ctor(i, k) => format!("§k:{}.{}", i.0, k),
            Symbol::Elim(i) => format!("§e:{}", i.0),
        }
        .into()
    }
    pub fn decode(s: &str) -> Option<Symbol> {
        let body = s.strip_prefix('§')?;
        if body.len() < 2 {
            return None;
        }
        let (tag, rest) = body.split_at(2); // "c:" / "i:" / "k:" / "e:"
        match tag {
            "c:" => Some(Symbol::Const(ConstId(rest.parse().ok()?))),
            "i:" => Some(Symbol::Ind(IndId(rest.parse().ok()?))),
            "e:" => Some(Symbol::Elim(IndId(rest.parse().ok()?))),
            "k:" => {
                let (i, k) = rest.split_once('.')?;
                Some(Symbol::Ctor(IndId(i.parse().ok()?), k.parse().ok()?))
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn symbol_name_roundtrip() {
        for s in [
            Symbol::Const(ConstId(3)),
            Symbol::Ind(IndId(7)),
            Symbol::Ctor(IndId(7), 2),
            Symbol::Elim(IndId(7)),
        ] {
            assert_eq!(Symbol::decode(&s.encode()), Some(s));
        }
        assert_eq!(Symbol::decode("x"), None);
    }
}
