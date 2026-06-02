use crate::symbol::Symbol;
use crate::tm::Tm;
use dnx_ast::{Ast, Name, NoFun, NoVal};
use dnx_core::{DnxError, LOPath, Net, PortId, Proper, ΔK};
use dnx_elab::{elaborate, pass1};
use std::collections::HashMap;
use std::sync::Arc;

type A = Ast<NoVal, NoFun>;

/// de Bruijn → named (level-based unique names, no capture). `depth` = #enclosing binders.
/// Var(i) refers to binder at level `depth-1-i`; each binder named `v{level}` (unique, nested).
/// Type positions (Sort/Pi) and kernel symbols become free `Ast::Name`s.
pub fn to_ast(t: &Tm, depth: u32) -> A {
    match t {
        // Bound: `Var(i)` (i < depth) resolves to binder level `depth-1-i`. Free: `i ≥ depth`
        // has NO enclosing binder, so we emit a stable free marker (`§fv{i-depth}`) instead of
        // underflowing `depth-1-i`. conv routes open terms away from here (proofs.md:328 D3);
        // this guard keeps `to_ast` total so no input can panic the TCB (defense-in-depth).
        Tm::Var(i) => match depth.checked_sub(1).and_then(|d| d.checked_sub(*i)) {
            Some(level) => Ast::Name(bind_name(level)),
            None => Ast::Name(Arc::from(format!("§fv{}", *i - depth).as_str())),
        },
        Tm::Lam(_, b) => {
            // dom erased; insert ΔK structural nodes (Era for drop, Rep for dup).
            let name = bind_name(depth);
            let body = to_ast(b, depth + 1);
            let uses = count_uses_in(&body, &name);
            Ast::Abs(name.clone(), Box::new(wrap_uses(name, uses, body)))
        }
        Tm::App(f, x) => Ast::App(Box::new(to_ast(f, depth)), Box::new(to_ast(x, depth))),
        Tm::Const(c) => Ast::Name(Symbol::Const(*c).encode()),
        Tm::Ind(i) => Ast::Name(Symbol::Ind(*i).encode()),
        Tm::Ctor(i, k) => Ast::Name(Symbol::Ctor(*i, *k).encode()),
        Tm::Elim(i) => Ast::Name(Symbol::Elim(*i).encode()),
        Tm::Sort(_) | Tm::Pi(..) => Ast::Name(Arc::from("§ty")), // type position, erased
    }
}

fn bind_name(level: u32) -> Name {
    Arc::from(format!("v{level}").as_str())
}

// ─── ΔK structural-node insertion (ported from dnx-lang::parser::helpers) ───
// A bound variable used 0× needs an Era; used n≥2× needs a Rep-chain duplicating it.

fn wrap_uses(name: Name, uses: u32, body: A) -> A {
    match uses {
        0 => Ast::Era(Box::new(Ast::Name(name)), Box::new(body)),
        1 => body,
        n => build_rep_chain(name, n as usize, body),
    }
}

fn build_rep_chain(name: Name, uses: usize, body: A) -> A {
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

fn indexed_rename(expr: A, from: &Name, names: &[Name], idx: &mut usize) -> A {
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
        Ast::Era(e, body) => Ast::Era(
            Box::new(indexed_rename(*e, from, names, idx)),
            Box::new(indexed_rename(*body, from, names, idx)),
        ),
        other => other,
    }
}

fn nest_reps(expr: A, names: &[Name], body: A) -> A {
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

fn count_uses_in(expr: &A, name: &Name) -> u32 {
    match expr {
        Ast::Name(n) if n == name => 1,
        Ast::Name(_) => 0,
        Ast::Abs(x, _) if x == name => 0,
        Ast::Abs(_, body) => count_uses_in(body, name),
        Ast::App(f, x) => count_uses_in(f, name) + count_uses_in(x, name),
        Ast::Era(e, body) => count_uses_in(e, name) + count_uses_in(body, name),
        Ast::Rep(e, a, b, body) => {
            count_uses_in(e, name)
                + if a == name || b == name {
                    0
                } else {
                    count_uses_in(body, name)
                }
        }
        _ => 0,
    }
}

/// φ_K: Tm → (net, root port). Uses ΔK (full structural lambda calculus with weakening+contraction).
pub fn phi_k(t: &Tm) -> Result<(Net<Proper, ΔK>, PortId), DnxError> {
    use dnx_core::PortKind;
    let ast = to_ast(t, 0);
    let r1 = pass1(&ast)?;
    let mut net: Net<Proper, ΔK> = Net::new(4096);
    let mut env: HashMap<Name, (PortId, u32)> = HashMap::new();
    let (rp, _) = elaborate::<ΔK, NoVal, NoFun>(
        &mut net,
        0,
        &mut env,
        LOPath::root(),
        &ast,
        &r1.usage_levels,
    )?;
    // Root convention (dnx-read `elab_norm`): an AUX root port is wired to a free slot
    // so it survives R4; a PRINCIPAL root port is stored directly — connecting it would
    // create a spurious active pair that normalize() cannot drain (ReadbackIncomplete).
    let root_port = if rp.port_kind() != PortKind::Principal {
        let slot = net.alloc_free(0)?;
        net.connect(rp, slot, LOPath::root())?;
        slot
    } else {
        rp
    };
    net.add_root("phi_k".into(), root_port);
    Ok((net, root_port))
}

#[cfg(test)]
mod tests {
    use super::*;
    use dnx_read::{psi_native, ReadbackResult};
    use dnx_sched::{Scheduler, SequentialScheduler};

    #[test]
    fn identity_erases_to_abs() {
        // λx:Sort0. x → λ. 0 ; normal form reads back as a lambda (Abs).
        let t = Tm::Lam(Box::new(Tm::Sort(0)), Box::new(Tm::Var(0)));
        let (net, _root) = phi_k(&t).unwrap();
        let (canon, _) = SequentialScheduler::normalize(net).unwrap();
        match psi_native::<_, NoVal, NoFun>(&canon) {
            ReadbackResult::Lambda(ast) => assert!(matches!(ast, Ast::Abs(_, _))),
            ReadbackResult::Partial(_) => panic!("identity must read back as Abs"),
        }
    }
}
