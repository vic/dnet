//! Lowering: surface `fix`/`match` → core `Tm::Elim` (spec §2-§4). UNTRUSTED — the kernel
//! re-checks the emitted `Tm` (infer + ι). All de-Bruijn arithmetic reuses kernel `shift`
//! (`tm.rs:20`) and mirrors the recursor minor layout (`recursor.rs:43`, spec §3e:111).

use std::collections::BTreeMap;

use dnx_proof::env::GlobalEnv;
use dnx_proof::inductive::Inductive;
use dnx_proof::symbol::IndId;
use dnx_proof::tm::{shift, Tm};

use crate::surface::{Fix, Match, SrcArm, SrcTm};

/// Why a surface term cannot be lowered to a structural `Elim`. A `LowerError` is NOT a
/// soundness failure — it just means this `fix` is not the simple-structural case v1 handles
/// (spec §4:117-125); the kernel never sees a bad term.
#[derive(Debug, PartialEq, Eq)]
pub enum LowerError {
    /// `Match.ind` (or a `Fix`'s scrutinee inductive) is not admitted in the env.
    UnknownInd,
    /// v1 handles no-param NON-INDEXED inductives only — kernel `recursor_type` `recursor.rs:26`
    /// bails on params/indices (spec §7-§8). Parametrised families wait on the RTGT track.
    ParamsOrIndices,
    /// `arms` count ≠ #ctors, or arm/ctor index mismatch (malformed match — spec §4:124, R6).
    ArmCount,
    /// An arm's binder arity ≠ `ctors[k].args` (spec §2:71, §4:124).
    ArmArity,
    /// A self-call's decreasing arg is NOT a recursive sub-term of the current arm — i.e. the
    /// fix is not structural on `rec_arg` (spec §4:122). THE guard, checked syntactically.
    NonStructural,
    /// A self-call's non-decreasing args vary across the recursion (accumulator) — needs a
    /// motive-returns-Pi recursor (Lean `brecOn`), OUT of v1 (spec §3d:108, ⚑V4).
    VaryingArg,
    /// A bare (non-applied) reference to the recursive self escaped rewriting (spec §3c) — the
    /// self is used non-structurally (e.g. passed as a value), which v1 cannot translate.
    BareSelf,
    /// `Fix.rec_arg` is out of range for the fix's argument telescope.
    BadRecArg,
    /// The `Fix.body` is not `λ a₁..aₙ. <match>` with the match directly on the decreasing arg
    /// (nested match / match on ≠ `{struct}` arg — spec §4:125, ⚑V1).
    NotDirectMatch,
}

/// Lower a surface term to a core `Tm`. Pass-through shapes lower 1:1; `Match`/`Fix` lower to
/// `Elim` (spec §2/§3). Top-level (no enclosing fix) `App`/`Lam`/`Var` lower structurally.
pub fn lower(env: &GlobalEnv, src: &SrcTm) -> Result<Tm, LowerError> {
    match src {
        SrcTm::Var(i) => Ok(Tm::Var(*i)),
        SrcTm::Core(t) => Ok(t.clone()),
        SrcTm::App(f, x) => Ok(Tm::App(Box::new(lower(env, f)?), Box::new(lower(env, x)?))),
        SrcTm::Lam(dom, body) => Ok(Tm::Lam(Box::new(dom.clone()), Box::new(lower(env, body)?))),
        SrcTm::Match(m) => lower_match(env, m, None),
        SrcTm::Fix(fx) => lower_fix(env, fx),
    }
}

/// What `lower_match` needs to know about an enclosing structural fix: the decreasing-arg
/// position and the fix arity `n` (spec §3a/§3d). `None` ⇒ a plain (non-recursive) match.
#[derive(Clone, Copy)]
struct FixHead {
    rec_arg: usize,
    n: usize,
}

/// Reject parametrised / indexed families: kernel `recursor_type` `recursor.rs:26` returns None
/// for them, so the emitted `Elim` would not type-check (spec §7-§8). v1 = no-param non-indexed.
fn check_simple(ind: &Inductive) -> Result<(), LowerError> {
    if !ind.params.is_empty() || !ind.indices.is_empty() {
        return Err(LowerError::ParamsOrIndices);
    }
    Ok(())
}

/// True if `ty`'s head (walking Pi cods / App spine) is `Ind id` — a recursive field
/// (mirrors `recursor.rs:14` / `env.rs:72`).
fn head_is_ind(ty: &Tm, id: IndId) -> bool {
    match ty {
        Tm::Ind(j) => *j == id,
        Tm::App(f, _) => head_is_ind(f, id),
        Tm::Pi(_, b) => head_is_ind(b, id),
        _ => false,
    }
}

/// `match → Elim` (spec §2:63). `fix = Some(..)` inside a structural fix (arms may carry
/// self-calls → IHs); `None` for a plain match (IHs are dead binders, spec §2:72).
fn lower_match(env: &GlobalEnv, m: &Match, fix: Option<FixHead>) -> Result<Tm, LowerError> {
    let ind = env.inds.get(&m.ind).ok_or(LowerError::UnknownInd)?;
    check_simple(ind)?;
    let c = ind.ctors.len();
    if m.arms.len() != c {
        return Err(LowerError::ArmCount);
    }

    // Elim I · motive · minor_0..minor_{c-1} · scrut  (no P/X bands: no-param non-indexed, §2).
    let mut elim = Tm::App(Box::new(Tm::Elim(m.ind)), Box::new(m.motive.clone()));
    for k in 0..c {
        let arm = m
            .arms
            .iter()
            .find(|a| a.ctor_ix == k as u32)
            .ok_or(LowerError::ArmCount)?;
        let minor = lower_minor(env, ind, arm, fix)?;
        elim = Tm::App(Box::new(elim), Box::new(minor));
    }
    let scrut = lower_scrut(env, &m.scrut, fix)?;
    Ok(Tm::App(Box::new(elim), Box::new(scrut)))
}

/// The scrutinee lowers in the OUTER context (no field/IH binders). In a fix it is `Var(aᵢ)`,
/// lowered in the `λ a⃗.` context; a non-Var scrutinee under a fix is a nested match (⚑V1).
fn lower_scrut(env: &GlobalEnv, scrut: &SrcTm, fix: Option<FixHead>) -> Result<Tm, LowerError> {
    match fix {
        None => lower(env, scrut),
        Some(_) => match scrut {
            SrcTm::Var(i) => Ok(Tm::Var(*i)),
            _ => Err(LowerError::NotDirectMatch),
        },
    }
}

/// Build `minor_k = λ (A_k fields) λ (ih_0..ih_{r-1}) . rhs'` (spec §2:69-73). The `r` IH
/// binders are inserted even when unused (kernel `minor_type` `recursor.rs:43` requires them).
fn lower_minor(
    env: &GlobalEnv,
    ind: &Inductive,
    arm: &SrcArm,
    fix: Option<FixHead>,
) -> Result<Tm, LowerError> {
    let k = arm.ctor_ix as usize;
    let fields = &ind.ctors[k].args;
    let m = fields.len();
    if arm.binders.len() != m {
        return Err(LowerError::ArmArity);
    }
    let recs: Vec<usize> = (0..m)
        .filter(|&p| head_is_ind(&fields[p], ind.id))
        .collect();
    let r = recs.len() as u32;

    // rhs' relocates source field/outer refs by +r (the IH binders sit between fields and body,
    // spec §3e:111). Plain match: no self-calls ⇒ a single `+r` shift. Fix: relocate + rewrite
    // self-calls → IH vars (spec §3c).
    let body = match fix {
        None => shift(&lower(env, &arm.rhs)?, r as i64, 0),
        Some(fh) => {
            let scope = arm_fix_scope(fh, &recs, m, r);
            lower_rhs(env, &arm.rhs, &scope, 0)?
        }
    };

    // Wrap: r IH binders (inner) then m field binders (outer). The IH binder TYPE is irrelevant
    // to the emitted value (kernel re-derives it via minor_type); reuse the recursive field type.
    let mut t = body;
    for &p in recs.iter().rev() {
        t = Tm::Lam(Box::new(fields[p].clone()), Box::new(t));
    }
    for p in (0..m).rev() {
        t = Tm::Lam(Box::new(fields[p].clone()), Box::new(t));
    }
    Ok(t)
}

/// The fix self + arm recursive-field→IH mapping (spec §3c). All indices stated at the
/// ARM-BODY BASE depth (ctx `[a⃗, field_0..field_{m-1}, ih_0..ih_{r-1}]`, innermost = ih).
struct FixScope {
    /// de-Bruijn index of the recursive self `f` in the SOURCE rhs ctx `[f, a⃗, fields]` base.
    self_src: u32,
    rec_arg: usize,
    /// source-ctx base index of each fix outer arg a⃗ by position (spec §3d uniformity check).
    outer_src: Vec<u32>,
    /// recursive-field SOURCE base index → its IH binder EMITTED base index (spec §3c:99).
    field_to_ih: BTreeMap<u32, u32>,
    /// `r` = #IH binders inserted between fields and body = the +shift for non-self refs.
    r: u32,
}

/// Specialise to one arm (spec §3c/§3e). SOURCE rhs ctx `[f, a⃗, fields]` (innermost field_{m-1}
/// = 0): field_p = m-1-p ; a_t = m+(n-1-t) ; f = m+n. EMITTED minor body ctx `[a⃗, fields, ih]`
/// (innermost ih_{r-1} = 0): ih_j = r-1-j.
fn arm_fix_scope(fh: FixHead, recs: &[usize], m: usize, r: u32) -> FixScope {
    let n = fh.n;
    let self_src = (m + n) as u32;
    let outer_src: Vec<u32> = (0..n).map(|t| (m + (n - 1 - t)) as u32).collect();
    let mut field_to_ih = BTreeMap::new();
    for (j, &p) in recs.iter().enumerate() {
        field_to_ih.insert((m - 1 - p) as u32, r - 1 - j as u32);
    }
    FixScope {
        self_src,
        rec_arg: fh.rec_arg,
        outer_src,
        field_to_ih,
        r,
    }
}

/// Lower an arm rhs (inside a fix), relocating source de-Bruijn refs to the emitted minor body
/// and rewriting structural self-calls → IH vars. `depth` = rhs-internal binders entered.
fn lower_rhs(env: &GlobalEnv, src: &SrcTm, s: &FixScope, depth: u32) -> Result<Tm, LowerError> {
    match src {
        SrcTm::Var(v) => Ok(Tm::Var(relocate_var(s, *v, depth)?)),
        // Core leaf: relocate free refs the same way `relocate_var` does. Drop `f` FIRST (refs
        // strictly above its slot `−1`, original-index cutoff `tm.rs:44`), then shift all free
        // refs `+r` for the inserted IH binders. Net: below-f `+r`, above-f `+r−1`.
        SrcTm::Core(t) => {
            reject_bare_self(t, s, depth)?;
            Ok(shift(
                &shift(t, -1, depth + s.self_src + 1),
                s.r as i64,
                depth,
            ))
        }
        // The domain is a core type in the SAME source ctx as a `Core` leaf — relocate it the
        // SAME split way (NOT a blanket `+r`): drop the self `f` (`−1` above its slot), then
        // `+r` for the inserted IH binders. A domain ref ABOVE `f` thus nets `+r−1` (mirrors
        // `relocate_var` :236 / the `Core` leaf :204). Bare-self in a domain is illegal too.
        SrcTm::Lam(dom, body) => {
            reject_bare_self(dom, s, depth)?;
            Ok(Tm::Lam(
                Box::new(shift(
                    &shift(dom, -1, depth + s.self_src + 1),
                    s.r as i64,
                    depth,
                )),
                Box::new(lower_rhs(env, body, s, depth + 1)?),
            ))
        }
        SrcTm::App(..) => lower_app_or_selfcall(env, src, s, depth),
        // A `match`/`fix` nested INSIDE a structural fix arm = nested recursion, OUT of v1
        // (spec §4:125 / §8, ⚑V1).
        SrcTm::Match(_) | SrcTm::Fix(_) => Err(LowerError::NotDirectMatch),
    }
}

/// Relocate a source `Var(v)` (under `depth` rhs-internal binders) into the emitted minor body.
/// Internal vars pass through; a bare self `f` is illegal (spec §3c, only applied self-calls).
/// The emitted minor DROPS `f` (at `self_src`) and INSERTS `r` IH binders between the fields and
/// the body, so a non-self source ref relocates by:
///   - `+r` if it is BELOW `f` (`v-depth < self_src`): only the inserted IHs sit between it and
///     the body (the dropped `f` is above it, unaffected);
///   - `+r − 1` if it is ABOVE `f` (`v-depth > self_src`): `+r` for the inserted IHs and `−1` for
///     the dropped `f` binder (kernel `subst` drop-shift `tm.rs:44`: `Var(i)` with `i>j ⇒ i-1`).
fn relocate_var(s: &FixScope, v: u32, depth: u32) -> Result<u32, LowerError> {
    if v < depth {
        return Ok(v); // rhs-internal binder
    }
    let src = v - depth;
    if src == s.self_src {
        return Err(LowerError::BareSelf);
    }
    // Compute in i64: an above-`f` ref with `r == 0` (arm has no recursive fields ⇒ no IH
    // binders) nets `−1` (just drop `f`); `s.r - 1` in u32 would underflow.
    let reloc = if src < s.self_src {
        s.r as i64
    } else {
        s.r as i64 - 1
    };
    Ok((v as i64 + reloc) as u32)
}

/// Reject a BARE self `f` buried in a core `Tm` (`Core` leaf / `Lam` domain). The `Var(v)` arm
/// catches a bare self in surface position (`relocate_var` :234), but a core fragment is shifted
/// wholesale — a free `Var` pointing at `f` would be SILENTLY drop-shifted to a different binder.
/// `f` lives at index `depth + self_src` at the fragment root; each Pi/Lam binder lifts the
/// cutoff by 1 (spec §3c: only APPLIED self-calls translate; a bare self ⇒ `BareSelf`).
fn reject_bare_self(t: &Tm, s: &FixScope, depth: u32) -> Result<(), LowerError> {
    fn scan(t: &Tm, f: u32) -> bool {
        match t {
            Tm::Var(i) => *i == f,
            Tm::Sort(_) | Tm::Const(_) | Tm::Ind(_) | Tm::Ctor(..) | Tm::Elim(_) => false,
            Tm::Pi(a, b) | Tm::Lam(a, b) => scan(a, f) || scan(b, f + 1),
            Tm::App(g, x) => scan(g, f) || scan(x, f),
        }
    }
    if scan(t, depth + s.self_src) {
        return Err(LowerError::BareSelf);
    }
    Ok(())
}

/// If the application's spine head is the recursive self `f`, rewrite the whole spine to an IH
/// var (spec §3c); otherwise lower head + args structurally with relocation.
fn lower_app_or_selfcall(
    env: &GlobalEnv,
    src: &SrcTm,
    s: &FixScope,
    depth: u32,
) -> Result<Tm, LowerError> {
    let (head, args) = src_spine(src);
    if let SrcTm::Var(v) = head {
        if *v >= depth && *v - depth == s.self_src {
            return self_call_to_ih(s, &args, depth);
        }
    }
    let mut t = lower_rhs(env, head, s, depth)?;
    for a in &args {
        t = Tm::App(Box::new(t), Box::new(lower_rhs(env, a, s, depth)?));
    }
    Ok(t)
}

/// A self-call `f y₁..(rec_j)..yₙ` becomes the IH binder `ih_j` (spec §3c:99-103), PROVIDED:
/// (a) `args[rec_arg]` is syntactically a recursive field `rec_j` of this arm (else
/// NonStructural — THE guard, spec §4:122); (b) every other arg equals the fix's own outer arg,
/// unchanged (uniform; else VaryingArg, spec §3d:108, ⚑V4).
fn self_call_to_ih(s: &FixScope, args: &[SrcTm], depth: u32) -> Result<Tm, LowerError> {
    if args.len() != s.outer_src.len() {
        return Err(LowerError::NonStructural); // partial / over-applied self-call (⚑V4)
    }
    let dec = args.get(s.rec_arg).ok_or(LowerError::BadRecArg)?;
    let field_src = match dec {
        SrcTm::Var(v) if *v >= depth => *v - depth,
        _ => return Err(LowerError::NonStructural),
    };
    let ih_src = *s
        .field_to_ih
        .get(&field_src)
        .ok_or(LowerError::NonStructural)?;
    for (pos, a) in args.iter().enumerate() {
        if pos == s.rec_arg {
            continue;
        }
        match a {
            SrcTm::Var(v) if *v >= depth && *v - depth == s.outer_src[pos] => {}
            _ => return Err(LowerError::VaryingArg),
        }
    }
    Ok(Tm::Var(ih_src + depth)) // IH binder, lifted past rhs-internal binders
}

/// `fix → Elim` (spec §3). Body `λ a₁..aₙ. <match a_{rec_arg}>`: peel the lambdas (they become
/// the recursor's outer params, spec §3d-uniform), DROP the self `f`, turn the recursive match
/// into the recursor (spec §3b).
fn lower_fix(env: &GlobalEnv, fx: &Fix) -> Result<Tm, LowerError> {
    let mut doms: Vec<Tm> = Vec::new();
    let mut cur = &*fx.body;
    while let SrcTm::Lam(dom, body) = cur {
        doms.push(dom.clone());
        cur = body;
    }
    let n = doms.len();
    if fx.rec_arg >= n {
        return Err(LowerError::BadRecArg);
    }
    let SrcTm::Match(m) = cur else {
        return Err(LowerError::NotDirectMatch);
    };
    // The recursive match must be directly on the decreasing arg `aᵢ` (spec §4:125). At the
    // match site (ctx `[f, a⃗]`, innermost a_n = Var0) a_{rec_arg} sits at Var(n-1-rec_arg).
    let dec_var = (n - 1 - fx.rec_arg) as u32;
    match &*m.scrut {
        SrcTm::Var(v) if *v == dec_var => {}
        _ => return Err(LowerError::NotDirectMatch),
    }
    let ind = env.inds.get(&m.ind).ok_or(LowerError::UnknownInd)?;
    check_simple(ind)?;

    let elim = lower_match(
        env,
        m,
        Some(FixHead {
            rec_arg: fx.rec_arg,
            n,
        }),
    )?;

    // Re-wrap the peeled `λ a⃗.`; `f` is intentionally NOT re-bound (spec §3:94).
    let mut t = elim;
    for dom in doms.into_iter().rev() {
        t = Tm::Lam(Box::new(dom), Box::new(t));
    }
    let _ = &fx.ty; // the full fix type is the kernel's to re-check via `infer`; not needed here.
    Ok(t)
}

/// Flatten a surface application spine: head + args left→right.
fn src_spine(t: &SrcTm) -> (&SrcTm, Vec<SrcTm>) {
    let mut args = Vec::new();
    let mut cur = t;
    while let SrcTm::App(f, x) = cur {
        args.push((**x).clone());
        cur = f;
    }
    args.reverse();
    (cur, args)
}
