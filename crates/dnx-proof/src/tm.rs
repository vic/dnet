use crate::symbol::{ConstId, IndId};

pub type Level = u32;
pub type Telescope = Vec<Tm>;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Tm {
    Var(u32), // de Bruijn idx; 0 = innermost
    Sort(Level),
    Pi(Box<Tm>, Box<Tm>),  // dom, cod (cod binds 1)
    Lam(Box<Tm>, Box<Tm>), // dom (erased at φ_K), body (binds 1)
    App(Box<Tm>, Box<Tm>),
    Const(ConstId),
    Ind(IndId),
    Ctor(IndId, u32),
    Elim(IndId),
}

/// Add `d` to every Var with index ≥ `cutoff`.
pub fn shift(t: &Tm, d: i64, cutoff: u32) -> Tm {
    match t {
        Tm::Var(i) => Tm::Var(if *i >= cutoff {
            (*i as i64 + d) as u32
        } else {
            *i
        }),
        Tm::Sort(_) | Tm::Const(_) | Tm::Ind(_) | Tm::Ctor(..) | Tm::Elim(_) => t.clone(),
        Tm::Pi(a, b) => Tm::Pi(
            Box::new(shift(a, d, cutoff)),
            Box::new(shift(b, d, cutoff + 1)),
        ),
        Tm::Lam(a, b) => Tm::Lam(
            Box::new(shift(a, d, cutoff)),
            Box::new(shift(b, d, cutoff + 1)),
        ),
        Tm::App(f, x) => Tm::App(Box::new(shift(f, d, cutoff)), Box::new(shift(x, d, cutoff))),
    }
}

/// Substitute `arg` for Var(`j`); used as `subst(body, 0, a)` = `body[0:=a]`.
pub fn subst(t: &Tm, j: u32, arg: &Tm) -> Tm {
    match t {
        Tm::Var(i) if *i == j => shift(arg, j as i64, 0),
        Tm::Var(i) => Tm::Var(if *i > j { *i - 1 } else { *i }),
        Tm::Sort(_) | Tm::Const(_) | Tm::Ind(_) | Tm::Ctor(..) | Tm::Elim(_) => t.clone(),
        Tm::Pi(a, b) => Tm::Pi(Box::new(subst(a, j, arg)), Box::new(subst(b, j + 1, arg))),
        Tm::Lam(a, b) => Tm::Lam(Box::new(subst(a, j, arg)), Box::new(subst(b, j + 1, arg))),
        Tm::App(f, x) => Tm::App(Box::new(subst(f, j, arg)), Box::new(subst(x, j, arg))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn subst_identity_body() {
        let body = Tm::Var(0);
        assert_eq!(subst(&body, 0, &Tm::Var(5)), Tm::Var(5));
    }
    #[test]
    fn subst_shifts_free_under_binder() {
        let body = Tm::Lam(Box::new(Tm::Sort(0)), Box::new(Tm::Var(1)));
        let got = subst(&body, 0, &Tm::Var(9));
        assert_eq!(got, Tm::Lam(Box::new(Tm::Sort(0)), Box::new(Tm::Var(10))));
    }
}
