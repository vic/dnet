//! conv `≡` — definitional equality (§2b). PRECONDITION (§0 invariant): t,u already
//! checked at the SAME type (enforced by T-Conv). Closed terms (value head) take the
//! `ArtifactId` LOCAL fast path (intern(serialize) → O(1) structural-exact eq, NO
//! crypto in the TCB; proofs.md:110, canonical-hash.md:13-17); non-value (Stuck)
//! heads take the readback + α path. Routing (D3): a Stuck head ⇒ never the fast path.

use dnx_ast::{Ast, Name, NoFun, NoVal};
use dnx_core::{Canonical, DnxError, Interner, Net, PortId, ΔK};
use dnx_read::{psi_native, ReadbackResult};
use dnx_sched::{Scheduler, SequentialScheduler};

use crate::driver::nf_tm;
use crate::env::GlobalEnv;
use crate::erase::phi_k;
use crate::infer::Ctx;
use crate::tm::Tm;

type A = Ast<NoVal, NoFun>;

/// Decide `t ≡ u`. PRECONDITION (§0): both already checked at the SAME type.
///
/// Terms mentioning kernel symbols (Const/Ind/Ctor/Elim) are reduced in the typed layer
/// via `nf_tm` (δ/ι OUTSIDE Ω_K, settled §6) and compared structurally — de Bruijn makes
/// structural equality α-equality. Pure-λ terms take the Δ-net β path: normalize to
/// canonical, then route (D3) closed→`ArtifactId` LOCAL eq (A7) / open→de Bruijn α on readback.
pub fn conv(env: &GlobalEnv, ctx: &Ctx, t: &Tm, u: &Tm) -> Result<bool, DnxError> {
    // Routing (proofs.md:328 D3): an OPEN term (a free Var, or any neutral whose head is a
    // free var) must NOT take the net `ArtifactId` fast path — it is compared by structural
    // congruence in the typed layer. Types/data/kernel symbols (needs_typed_conv) likewise
    // erase under the net, so they too convert here. nf_tm does β+δ+ι and de Bruijn structure
    // makes `==` exact α-equality, i.e. congruence (same head + recursively-conv args). Only a
    // CLOSED pure-λ pair reaches the net path below (D1/A7).
    if is_open(t, 0) || is_open(u, 0) || needs_typed_conv(t) || needs_typed_conv(u) {
        return Ok(nf_tm(env, ctx, t) == nf_tm(env, ctx, u));
    }
    let (nt, _rt) = phi_k(t)?;
    let (nu, _ru) = phi_k(u)?;
    let (cnt, _) = SequentialScheduler::normalize(nt)?;
    let (cnu, _) = SequentialScheduler::normalize(nu)?;

    let ra = psi_native::<_, NoVal, NoFun>(&cnt);
    let rb = psi_native::<_, NoVal, NoFun>(&cnu);

    if is_closed_rb(&ra) && is_closed_rb(&rb) {
        // Closed fast path (A7): `ArtifactId` LOCAL equality = intern(serialize) →
        // O(1) byte-exact compare (proofs.md:110). The intern table's bytes are the
        // ground truth (= Lean `is_eqp`, type_checker.cpp:1059); NO cryptographic
        // hash enters this decision. Both nets interned in ONE table → equal id iff
        // byte-identical canonical serialization.
        let mut interner = Interner::new();
        let ia = interner.intern_local(&cnt, root_port(&cnt))?;
        let ib = interner.intern_local(&cnu, root_port(&cnu))?;
        Ok(ia == ib)
    } else {
        Ok(readback_alpha_eq(&ra, &rb)) // open path (D3): never interns
    }
}

/// Open ⇔ a free de Bruijn `Var` occurs (index ≥ enclosing-binder `depth`). Such a term is
/// neutral/open and MUST take the typed congruence path, never the net (proofs.md:328 D3):
/// `to_ast` has no binder to resolve a free var to (it would underflow `depth-1-i` in erase).
fn is_open(t: &Tm, depth: u32) -> bool {
    match t {
        Tm::Var(i) => *i >= depth,
        Tm::Lam(a, b) | Tm::Pi(a, b) => is_open(a, depth) || is_open(b, depth + 1),
        Tm::App(a, b) => is_open(a, depth) || is_open(b, depth),
        Tm::Sort(_) | Tm::Const(_) | Tm::Ind(_) | Tm::Ctor(..) | Tm::Elim(_) => false,
    }
}

/// Terms carrying type structure (Sort/Pi) or kernel symbols (Const/Ind/Ctor/Elim) cannot go
/// through the type-erasing net — they convert in the typed layer via `nf_tm`.
fn needs_typed_conv(t: &Tm) -> bool {
    match t {
        Tm::Sort(_) | Tm::Pi(..) | Tm::Const(_) | Tm::Ind(_) | Tm::Ctor(..) | Tm::Elim(_) => true,
        Tm::Lam(a, b) | Tm::App(a, b) => needs_typed_conv(a) || needs_typed_conv(b),
        _ => false,
    }
}

/// Closed ⇔ readback is a lambda with no free ordinary variables (kernel `§…` symbols allowed).
fn is_closed_rb(r: &ReadbackResult<NoVal, NoFun>) -> bool {
    match r {
        ReadbackResult::Lambda(a) => !has_free_var(a, &mut Vec::new()),
        ReadbackResult::Partial(_) => false,
    }
}

fn has_free_var(a: &A, bound: &mut Vec<Name>) -> bool {
    match a {
        Ast::Name(n) => !n.starts_with('§') && !bound.iter().any(|b| b == n),
        Ast::Abs(x, body) => {
            bound.push(x.clone());
            let r = has_free_var(body, bound);
            bound.pop();
            r
        }
        Ast::App(f, x) => has_free_var(f, bound) || has_free_var(x, bound),
        _ => false,
    }
}

/// Resolve the canonical expression port (mirrors psi_native root resolution): a free
/// root slot dereferences to its peer; otherwise the root is the expression port.
fn root_port(net: &Net<Canonical, ΔK>) -> PortId {
    let root = net.roots().values().next().copied().unwrap_or(PortId::NULL);
    if net.slot_is_live(root) && net.slot_view(root).is_free() {
        net.peer(root)
    } else {
        root
    }
}

fn readback_alpha_eq(a: &ReadbackResult<NoVal, NoFun>, b: &ReadbackResult<NoVal, NoFun>) -> bool {
    match (a, b) {
        (ReadbackResult::Lambda(x), ReadbackResult::Lambda(y)) => {
            alpha(x, y, &mut Vec::new(), &mut Vec::new())
        }
        (ReadbackResult::Partial(x), ReadbackResult::Partial(y)) => x == y,
        _ => false,
    }
}

/// α-equality on readback ASTs: bound vars compared by binding depth (de Bruijn),
/// free vars (incl. kernel `§…` symbols) compared by name. Robust to gensym renaming.
fn alpha(a: &A, b: &A, sa: &mut Vec<Name>, sb: &mut Vec<Name>) -> bool {
    match (a, b) {
        (Ast::Name(x), Ast::Name(y)) => {
            let dx = sa.iter().rposition(|n| n == x);
            let dy = sb.iter().rposition(|n| n == y);
            match (dx, dy) {
                (Some(i), Some(j)) => i == j,
                (None, None) => x == y,
                _ => false,
            }
        }
        (Ast::Abs(x, bx), Ast::Abs(y, by)) => {
            sa.push(x.clone());
            sb.push(y.clone());
            let r = alpha(bx, by, sa, sb);
            sa.pop();
            sb.pop();
            r
        }
        (Ast::App(f1, x1), Ast::App(f2, x2)) => alpha(f1, f2, sa, sb) && alpha(x1, x2, sa, sb),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tm::Tm;

    fn lam(b: Tm) -> Tm {
        Tm::Lam(Box::new(Tm::Sort(0)), Box::new(b))
    }

    #[test]
    fn r9_distinct_projections_differ() {
        let env = GlobalEnv::default();
        let k = lam(lam(Tm::Var(1))); // λλ.1
        let k2 = lam(lam(Tm::Var(0))); // λλ.0
        assert!(
            !conv(&env, &Vec::new(), &k, &k2).unwrap(),
            "λλ.1 must differ from λλ.0 (R9)"
        );
        assert!(
            conv(&env, &Vec::new(), &k, &k.clone()).unwrap(),
            "term ≡ itself"
        );
    }

    #[test]
    fn delta_const_converges_with_body() {
        // c := λx.x ; (c applied to id) ≡ id  via δ-unfold (A3 path, typed layer)
        use crate::symbol::ConstId;
        let mut env = GlobalEnv::default();
        let id = lam(Tm::Var(0));
        env.add_const(ConstId(0), Tm::Sort(0), id.clone()).unwrap();
        let lhs = Tm::App(Box::new(Tm::Const(ConstId(0))), Box::new(id.clone()));
        assert!(
            conv(&env, &Vec::new(), &lhs, &id).unwrap(),
            "δ-unfolded const ≡ its applied value"
        );
    }

    #[test]
    fn beta_equal_terms_converge() {
        let env = GlobalEnv::default();
        // (λx.x) (λy.y)  ≡  λy.y
        let id = lam(Tm::Var(0));
        let app = Tm::App(Box::new(lam(Tm::Var(0))), Box::new(id.clone()));
        assert!(
            conv(&env, &Vec::new(), &app, &id).unwrap(),
            "β-redex ≡ its value (A3/A7)"
        );
    }

    // ── S2: closed conv = `ArtifactId` LOCAL eq (intern(serialize)), NOT a hash.
    // β-equal distinct-source closed terms → SAME id (conv-YES); structurally
    // distinct → distinct id (conv-NO, no false-merge). trusted.md T5/T6. ─────────
    #[test]
    fn s2_beta_equal_distinct_source_same_artifact_local() {
        let env = GlobalEnv::default();
        // (λf.λx. f x) (λy.y)  β→  λx. (λy.y) x  β→  λx.x  ≡  λx.x (distinct source).
        let id = lam(Tm::Var(0));
        let fx = lam(lam(Tm::App(Box::new(Tm::Var(1)), Box::new(Tm::Var(0)))));
        let applied = Tm::App(Box::new(fx), Box::new(id.clone()));
        assert!(
            conv(&env, &Vec::new(), &applied, &id).unwrap(),
            "β-equal closed terms from distinct sources → same ArtifactId-local (conv-YES)"
        );
    }

    #[test]
    fn s2_distinct_closed_terms_no_false_merge() {
        let env = GlobalEnv::default();
        // λx.x  vs  λx.λy.x — structurally distinct closed NFs must NOT merge.
        let id = lam(Tm::Var(0));
        let k = lam(lam(Tm::Var(1)));
        assert!(
            !conv(&env, &Vec::new(), &id, &k).unwrap(),
            "λx.x must NOT convert to λx.λy.x (no false-merge in the LOCAL-eq path)"
        );
    }
}
