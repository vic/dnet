use dnx_ast::{Ast, Name, PrimFun, PrimVal};
use dnx_core::prim::{alloc_prim_fun, alloc_prim_val, PrimFunEntry, PrimState, PrimValue};
use dnx_core::{DnxError, LOPath, Net, NetClassMarker, PortId, Proper};
use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Arc;

static FRESH_CTR: AtomicU32 = AtomicU32::new(0);

fn fresh(prefix: &str) -> Name {
    let n = FRESH_CTR.fetch_add(1, Ordering::Relaxed);
    Arc::from(format!("_{prefix}{n}").as_str())
}

type Env = HashMap<Name, (PortId, u32)>;

/// Optional prim context for elaborate_with_prims.
pub struct PrimCtx<'a, V: PrimVal, F: PrimFun> {
    pub state: &'a mut PrimState,
    pub to_fun: fn(&F) -> Option<PrimFunEntry>,
    pub to_val: fn(&V) -> Option<PrimValue>,
}

/// Pass 2: emit a `Net<Proper, C>` from a resolved, linear-checked Ast.
/// `usage_levels` from Pass 1.
pub fn elaborate<C: NetClassMarker, V: PrimVal, F: PrimFun>(
    net: &mut Net<Proper, C>,
    level: u32,
    env: &mut Env,
    lo: LOPath,
    expr: &Ast<V, F>,
    usage_levels: &HashMap<Name, u32>,
) -> Result<(PortId, u32), DnxError> {
    elab_impl::<C, V, F>(net, None, level, env, lo, expr, usage_levels)
}

/// Pass 2 with prim dispatch: handles Ast::Val and Ast::Fun via ctx.
pub fn elaborate_with_prims<C: NetClassMarker, V: PrimVal, F: PrimFun>(
    net: &mut Net<Proper, C>,
    ctx: &mut PrimCtx<'_, V, F>,
    level: u32,
    env: &mut Env,
    lo: LOPath,
    expr: &Ast<V, F>,
    usage_levels: &HashMap<Name, u32>,
) -> Result<(PortId, u32), DnxError> {
    elab_impl::<C, V, F>(net, Some(ctx), level, env, lo, expr, usage_levels)
}

fn elab_impl<C: NetClassMarker, V: PrimVal, F: PrimFun>(
    net: &mut Net<Proper, C>,
    mut prim: Option<&mut PrimCtx<'_, V, F>>,
    level: u32,
    env: &mut Env,
    lo: LOPath,
    expr: &Ast<V, F>,
    usage_levels: &HashMap<Name, u32>,
) -> Result<(PortId, u32), DnxError> {
    match expr {
        Ast::Name(n) => {
            let (port, stored_level) = env.remove(n).ok_or(DnxError::ReadbackIncomplete)?;
            Ok((port, stored_level))
        }

        Ast::Abs(x, body) => {
            let abs = net.alloc_abs()?;
            env.insert(x.clone(), (abs.aux1, level + 1));
            let lo_body = lo.extend_left()?;
            let (body_p, _) =
                elab_impl(net, prim, level, env, lo_body.clone(), body, usage_levels)?;
            env.remove(x);
            net.connect(abs.aux0, body_p, lo_body)?;
            Ok((abs.principal, level))
        }

        Ast::App(f, x) => {
            let app = net.alloc_app()?;
            let lo_fn = lo.extend_left()?;
            let (f_p, _) = elab_impl(
                net,
                prim.as_deref_mut(),
                level,
                env,
                lo_fn.clone(),
                f,
                usage_levels,
            )?;
            let lo_arg = lo.extend_right()?;
            let (a_p, _) = elab_impl(net, prim, level + 1, env, lo_arg.clone(), x, usage_levels)?;
            net.connect(app.principal, f_p, lo_fn)?;
            net.connect(app.aux1, a_p, lo_arg)?;
            Ok((app.aux0, level))
        }

        Ast::Rep(e, a, b, body) => {
            let la = *usage_levels.get(a).unwrap_or(&level);
            let lb = *usage_levels.get(b).unwrap_or(&level);
            let (e_p, rep_level) = elab_impl(
                net,
                prim.as_deref_mut(),
                level,
                env,
                lo.clone(),
                e,
                usage_levels,
            )?;

            let d0 = (la as i32) - (rep_level as i32);
            let d1 = (lb as i32) - (rep_level as i32);
            let d0 = i16::try_from(d0).map_err(|_| DnxError::DeltaOverflow)?;
            let d1 = i16::try_from(d1).map_err(|_| DnxError::DeltaOverflow)?;

            let rep = net.alloc_rep_in(rep_level as u16, d0, d1)?;
            net.connect(rep.principal, e_p, lo.clone())?;
            env.insert(a.clone(), (rep.aux0, la));
            env.insert(b.clone(), (rep.aux1, lb));

            let (body_p, body_level) = elab_impl(net, prim, level, env, lo, body, usage_levels)?;
            Ok((body_p, body_level))
        }

        Ast::Era(e, body) => {
            let (e_p, _) = elab_impl(
                net,
                prim.as_deref_mut(),
                level,
                env,
                lo.clone(),
                e,
                usage_levels,
            )?;
            net.connect(Net::<Proper, C>::eraser_port(), e_p, lo.clone())?;
            let (body_p, body_level) = elab_impl(net, prim, level, env, lo, body, usage_levels)?;
            Ok((body_p, body_level))
        }

        Ast::Fix(inner) => {
            // Cyclic-net fixpoint (main.tex §Core: 3 agents, Δ-net is a graph → cycles
            // legal; main.tex:264-267). `fix f = f (fix f)`: apply the function and feed
            // its output back as its own argument, so β (r4) ties `self := V`. The output
            // V is shared by one Rep between the external use and the self-feedback — a
            // single flat back-edge at a fixed level (no nested self-application), so
            // copies meet at equal level and annihilate (main.tex:787); no level climb.
            // self-unused → β wires the feedback into self's eraser and the cycle decays
            // to the body (main.tex:789).
            let lo_fn = lo.extend_left()?;
            let (inner_p, _) =
                elab_impl(net, prim, level, env, lo_fn.clone(), inner, usage_levels)?;
            let app = net.alloc_app()?;
            net.connect(app.principal, inner_p, lo_fn)?;
            // V = app.aux0, shared flat (single back-edge, same level both sides → copies
            // meet at equal level and annihilate, main.tex:787; no climb).
            let rep = net.alloc_rep_in(level as u16, 0, 0)?;
            net.connect(rep.principal, app.aux0, lo.extend_right()?)?;
            net.connect(app.aux1, rep.aux0, lo.clone())?;
            Ok((rep.aux1, level))
        }

        Ast::Perform(_, _) => Err(DnxError::ReadbackIncomplete),

        Ast::Handle(comp, branches) => {
            if branches.len() != 1 {
                return Err(DnxError::ReadbackIncomplete);
            }
            let b = &branches[0];
            let r_v = fresh("r");
            let lbl_v = fresh("lbl");
            let desugared = Ast::App(
                Box::new(Ast::App(
                    comp.as_ref().clone().into(),
                    Box::new(Ast::Abs(r_v.clone(), Box::new(Ast::Name(r_v)))),
                )),
                Box::new(Ast::Abs(
                    lbl_v.clone(),
                    Box::new(Ast::Abs(
                        b.arg_name.clone(),
                        Box::new(Ast::Abs(
                            b.k_name.clone(),
                            Box::new(Ast::Era(
                                Box::new(Ast::Name(lbl_v)),
                                Box::new(b.body.as_ref().clone()),
                            )),
                        )),
                    )),
                )),
            );
            elab_impl(net, prim, level, env, lo, &desugared, usage_levels)
        }

        Ast::Val(v) => match prim {
            Some(ctx) => {
                let pv = (ctx.to_val)(v).ok_or(DnxError::ReadbackIncomplete)?;
                let p = alloc_prim_val(net, ctx.state, pv)?;
                Ok((p, level))
            }
            None => {
                let p = net.alloc_free(0)?;
                Ok((p, level))
            }
        },

        Ast::Fun(f) => match prim {
            Some(ctx) => {
                let entry = (ctx.to_fun)(f).ok_or(DnxError::ReadbackIncomplete)?;
                // A nullary pure prim is a constant value (e.g. empty attrset):
                // fire it now, since a 0-arity PrimFun never meets an argument.
                if entry.arity_remaining == 0 {
                    if let dnx_core::prim::PrimImpl::Pure(pf) = entry.impl_ {
                        let v = pf(&entry.captured)?;
                        let p = alloc_prim_val(net, ctx.state, v)?;
                        return Ok((p, level));
                    }
                }
                let p = alloc_prim_fun(net, ctx.state, entry)?;
                Ok((p, level))
            }
            None => {
                let p = net.alloc_free(0)?;
                Ok((p, level))
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pass1::pass1;
    use dnx_core::{normalize, ΔL};

    #[derive(Debug, Clone, PartialEq)]
    struct NoVal;
    #[derive(Debug, Clone, PartialEq)]
    struct NoFun;
    impl dnx_ast::PrimVal for NoVal {}
    impl dnx_ast::PrimFun for NoFun {}

    type E = Ast<NoVal, NoFun>;

    fn nm(s: &str) -> E {
        Ast::Name(Arc::from(s))
    }
    fn ab(x: &str, b: E) -> E {
        Ast::Abs(Arc::from(x), Box::new(b))
    }
    fn ap(f: E, x: E) -> E {
        Ast::App(Box::new(f), Box::new(x))
    }

    fn elab_normalize(
        expr: &E,
    ) -> Result<
        (
            dnx_core::Net<dnx_core::Canonical, ΔL>,
            dnx_core::ReduceStats,
        ),
        DnxError,
    > {
        let r1 = pass1(expr)?;
        let mut net = Net::<Proper, ΔL>::new(64);
        let mut env = Env::new();
        let (result_p, _) = elaborate(
            &mut net,
            0,
            &mut env,
            LOPath::root(),
            expr,
            &r1.usage_levels,
        )?;
        net.add_root("r".into(), result_p);
        normalize(net)
    }

    #[test]
    fn pass2_identity_elaborates() -> Result<(), DnxError> {
        let e = ab("x", nm("x"));
        let (_, stats) = elab_normalize(&e)?;
        assert_eq!(stats.interactions, 0);
        Ok(())
    }

    #[test]
    fn pass2_id_applied_one_beta() -> Result<(), DnxError> {
        let e = ap(ab("x", nm("x")), ab("y", nm("y")));
        let (_, stats) = elab_normalize(&e)?;
        assert_eq!(stats.r4_count, 1);
        assert_eq!(stats.interactions, stats.r4_count);
        Ok(())
    }

    #[test]
    fn pass2_delta_arithmetic_abs_bound_rep() -> Result<(), DnxError> {
        use dnx_core::{normalize, ΔI};
        let sharing: E = ab(
            "x",
            Ast::Rep(
                Box::new(nm("x")),
                Arc::from("a"),
                Arc::from("b"),
                Box::new(ap(nm("a"), nm("b"))),
            ),
        );
        let expr: E = ap(sharing, ab("y", nm("y")));
        let r1 = pass1(&expr)?;
        assert!(r1.rep_used, "rep flag set");
        let mut net = Net::<Proper, ΔI>::new(64);
        let mut env = Env::new();
        let (result_p, _) = elaborate(
            &mut net,
            0,
            &mut env,
            LOPath::root(),
            &expr,
            &r1.usage_levels,
        )?;
        net.add_root("r".into(), result_p);
        let (_, stats) = normalize(net)?;
        assert!(stats.r4_count >= 1, "at least 1 β");
        Ok(())
    }
}
