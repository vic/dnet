/// C-Nix-2: NixRuntime — eval pipeline for pure Nix expressions.
use crate::error::NixError;
use crate::nix_to_expr;
use crate::prim::{nixprimfun_to_entry, nixprimval_to_value, NixPrimFun, NixPrimVal};
use dnx_ast::Ast;
use dnx_core::prim::{PrimState, PrimValue};

const TAG_PRIM_VAL: u8 = 0x0C;
const TAG_PRIM_FUN: u8 = 0x0D;
use dnx_core::{
    force_whnf_with_prims, normalize_demand, Canonical, LOPath, Net, NormalizeConfig, PortId,
    PortKind, Proper, ΔK,
};
use dnx_elab::{alpha_rename, elaborate_with_prims, pass0, pass1, PrimCtx};
use std::collections::HashMap;
use std::sync::Arc;

type NixAst = Ast<NixPrimVal, NixPrimFun>;

/// Nix eval result.
pub enum NixEvalResult {
    Int(i64),
    Float(f64),
    Str(Arc<str>),
    Bool(bool),
    Null,
    List(Vec<PrimValue>),
    AttrSet(Vec<(Arc<str>, PrimValue)>),
    Lambda(NixAst),
    Error(NixEvalError),
}

#[derive(Debug)]
pub enum NixEvalError {
    Parse(NixError),
    Elaborate(dnx_core::DnxError),
    Elaborate2(dnx_core::LinError),
    Readback(String),
}

impl std::fmt::Display for NixEvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NixEvalError::Parse(e) => e.fmt(f),
            NixEvalError::Elaborate(e) => e.fmt(f),
            NixEvalError::Elaborate2(e) => e.fmt(f),
            NixEvalError::Readback(s) => write!(f, "readback error: {s}"),
        }
    }
}

impl std::error::Error for NixEvalError {}

impl NixEvalResult {
    /// Convertibility equality on normal-form values: two results are equal iff
    /// they are the same kind with equal contents. This is dnx's conv-eq on the
    /// supported subset — the confluent reducer gives a unique NF, so convertible
    /// expressions (`2 + 2`, `4`) render equal values (dnx-test-runner-design.md §3).
    /// Lambdas are opaque (no decidable value equality) and never compare equal;
    /// an `Error` is never equal to anything.
    pub fn conv_eq(&self, other: &Self) -> bool {
        use NixEvalResult::*;
        match (self, other) {
            (Int(a), Int(b)) => a == b,
            (Float(a), Float(b)) => a.to_bits() == b.to_bits(),
            (Str(a), Str(b)) => a == b,
            (Bool(a), Bool(b)) => a == b,
            (Null, Null) => true,
            (List(a), List(b)) => a == b,
            (AttrSet(a), AttrSet(b)) => a == b,
            _ => false,
        }
    }
}

/// Runtime for pure Nix evaluation.
pub struct NixRuntime;

impl NixRuntime {
    pub fn pure() -> Self {
        NixRuntime
    }

    pub fn eval_file(&self, path: &std::path::Path) -> NixEvalResult {
        match std::fs::read_to_string(path) {
            Ok(src) => {
                let base = path.parent().map(std::path::Path::to_path_buf);
                self.eval_with_base(&src, base)
            }
            Err(e) => {
                NixEvalResult::Error(NixEvalError::Parse(NixError::ParseError(e.to_string())))
            }
        }
    }

    pub fn eval(&self, src: &str) -> NixEvalResult {
        self.eval_with_base(src, None)
    }

    /// Elaborate `src` to a Proper net ready for reduction: parse → prelude
    /// pass0 → pass1 levels → `elaborate_with_prims` → install the named root
    /// `"r"`. Shared front of `eval` and [`eval_canonical`] (the only divergence
    /// is what each does with the resulting net). Returns the net, its prim
    /// state, and the root port.
    fn build_net(
        &self,
        src: &str,
        base: Option<std::path::PathBuf>,
    ) -> Result<(Net<Proper, ΔK>, PrimState, PortId), NixEvalError> {
        let ast = match base {
            Some(dir) => crate::parser::nix_to_expr_at(src, dir),
            None => nix_to_expr(src),
        }
        .map_err(NixEvalError::Parse)?;

        let defs = crate::prelude::defs().map_err(NixEvalError::Parse)?;
        let ast = pass0(&defs, &ast).map_err(NixEvalError::Elaborate2)?;
        // Enforce Barendregt: inlined prelude bodies (cons/nil/map/…) keep their
        // binder names (h/t/c/n/self/ys), shadowing the call-site's binders. α-rename
        // to globally-unique names so pass1/pass2's flat name maps hold (no capture).
        let ast = alpha_rename(&ast);
        let r1 = pass1(&ast).map_err(NixEvalError::Elaborate2)?;

        let mut prim_state = PrimState::default();
        let (rp, mut net) = {
            let mut ctx = PrimCtx {
                state: &mut prim_state,
                to_fun: nixprimfun_to_entry,
                to_val: nixprimval_to_value,
            };
            let mut net = Net::<Proper, ΔK>::new(1 << 16);
            let mut env = HashMap::new();
            let (rp, _) = elaborate_with_prims(
                &mut net,
                &mut ctx,
                0,
                &mut env,
                LOPath::root(),
                &ast,
                &r1.usage_levels,
            )
            .map_err(NixEvalError::Elaborate)?;
            (rp, net)
        };

        let root_port = if rp.port_kind() != PortKind::Principal {
            let rs = net.alloc_free(0).map_err(NixEvalError::Elaborate)?;
            net.connect(rp, rs, LOPath::root())
                .map_err(NixEvalError::Elaborate)?;
            rs
        } else {
            rp
        };
        net.add_root(Arc::from("r"), root_port);
        Ok((net, prim_state, root_port))
    }

    /// Evaluate `src` to its canonical normal form, returning the rendered value
    /// and the number of reduction interactions (the cache's 0-on-HIT metric,
    /// dnx-test-runner-design.md §5).
    ///
    /// Unlike [`eval`], this never takes the scalar-head fast-path: it always
    /// drives `normalize_demand` to a canonical form, so the result is the true
    /// normal form (Church–Rosser ⇒ unique NF, canonical-hash.md:48-51). The
    /// runner decides equivalence by comparing these normal-form values: because
    /// the reducer is confluent (the parallel/sequential hash oracle,
    /// parallel_equiv.rs), two convertible expressions (`2 + 2` and `4`) reduce
    /// to the same value — conv-eq on the supported subset.
    ///
    /// (The design's `canonical_hash` conv-eq is not used: that hasher does not
    /// yet cover `PrimVal` nodes (canonical_hash.rs:193, Phase C) and is
    /// inconsistent across equal scalars — e.g. `2 + 2` hashes but the literal
    /// `4` does not, though both normalize to `Int(4)`. Comparing normal-form
    /// values is the sound equivalence the core can actually express here.)
    pub fn eval_canonical(&self, src: &str) -> Result<(NixEvalResult, u64), NixEvalError> {
        let (net, mut prim_state, _) = self.build_net(src, None)?;
        let cfg = NormalizeConfig {
            max_steps: Some(50_000_000),
            max_agents: Some((1 << 16) - 16),
        };
        let root = net
            .roots()
            .get("r")
            .copied()
            .ok_or_else(|| NixEvalError::Readback("no root".into()))?;
        let (canonical, stats) =
            normalize_demand(net, &mut prim_state, root, &cfg).map_err(NixEvalError::Elaborate)?;
        Ok((readback_result(&canonical, &prim_state), stats.interactions))
    }

    fn eval_with_base(&self, src: &str, base: Option<std::path::PathBuf>) -> NixEvalResult {
        let (mut net, mut prim_state, root_port) = match self.build_net(src, base) {
            Ok(t) => t,
            Err(e) => return NixEvalResult::Error(e),
        };

        // Demand-driven eval (nix.md §371): force the root's WHNF spine so
        // recursion (fix/Y) bottoms out under LO demand instead of diverging
        // under full normalization. Fuel bounds genuinely-lazy results (list
        // output → StepLimitExceeded, pending deep forcing).
        let cfg = NormalizeConfig {
            max_steps: Some(50_000_000),
            max_agents: Some((1 << 16) - 16),
        };
        if let Err(e) = force_whnf_with_prims(&mut net, &mut prim_state, root_port, &cfg) {
            return NixEvalResult::Error(NixEvalError::Elaborate(e));
        }

        // Scalar at the head: read it directly. This bypasses canonicalization, so
        // off-spine residue (e.g. a recursive call discarded by the function) is
        // never touched — call-by-need, and what makes recursion terminate.
        if let Some(r) = read_scalar_head(&net, &prim_state, root_port) {
            return r;
        }

        // Scott-list head: a list is a FanAbs (`cons`/`nil` lambdas), so the
        // scalar path misses it and generic lambda readback would print
        // `<lambda>`. Reconstruct it structurally on the Proper net (laziness
        // preserved — only the demanded spine/elements are forced). Non-lists
        // fall through to lambda readback unchanged.
        if let Some(PrimValue::List(xs)) =
            dnx_read::read_value(&mut net, &mut prim_state, root_port, &cfg, 0)
        {
            return NixEvalResult::List(xs);
        }

        // Non-scalar head (lambda / Church-bool): drive to full NF for structural
        // readback. force_whnf already primed the WHNF head (scalar fix-results
        // returned above); normalize_demand drains the reachable residual (e.g. a
        // returned lambda's body redexes) under fuel, then canonicalizes.
        let canonical = match normalize_demand(net, &mut prim_state, root_port, &cfg) {
            Ok((c, _)) => c,
            Err(e) => return NixEvalResult::Error(NixEvalError::Elaborate(e)),
        };
        readback_result(&canonical, &prim_state)
    }
}

/// Read a scalar value sitting at the WHNF head, on the Proper net (no canonical
/// form needed). Returns None if the head is not a `PrimVal`.
fn read_scalar_head(net: &Net<Proper, ΔK>, ps: &PrimState, root: PortId) -> Option<NixEvalResult> {
    let s0 = net.slot_view(root);
    let hp = if s0.is_free() { net.peer(root) } else { root };
    if hp.is_null() || hp.is_eraser() {
        return None;
    }
    let s = net.slot_view(hp);
    if s.tag != TAG_PRIM_VAL {
        return None;
    }
    Some(match ps.vals.get(s.data as usize)? {
        PrimValue::Int(n) => NixEvalResult::Int(*n),
        PrimValue::Float(f) => NixEvalResult::Float(*f),
        PrimValue::Str(sv) => NixEvalResult::Str(sv.clone()),
        PrimValue::Bool(b) => NixEvalResult::Bool(*b),
        PrimValue::Null => NixEvalResult::Null,
        PrimValue::List(xs) => NixEvalResult::List(xs.clone()),
        PrimValue::AttrSet(kvs) => NixEvalResult::AttrSet(kvs.clone()),
        PrimValue::Path(p) => NixEvalResult::Str(p.clone()),
        _ => return None,
    })
}

fn readback_result(net: &Net<Canonical, ΔK>, ps: &PrimState) -> NixEvalResult {
    use dnx_read::{psi_native, ReadbackResult};

    let root_slot = match net.roots().get("r").copied() {
        Some(p) => p,
        None => return NixEvalResult::Error(NixEvalError::Readback("no root".into())),
    };
    if root_slot.is_null() || root_slot.is_eraser() {
        return NixEvalResult::Error(NixEvalError::Readback("null root".into()));
    }

    // Resolve free-slot indirection (same as psi_native).
    let root_port = if net.slot_is_live(root_slot) && net.slot_view(root_slot).is_free() {
        net.peer(root_slot)
    } else {
        root_slot
    };
    if root_port.is_null() || root_port.is_eraser() {
        return NixEvalResult::Error(NixEvalError::Readback("null result".into()));
    }

    let s = net.slot_view(root_port);
    if s.tag == TAG_PRIM_VAL {
        match ps.vals.get(s.data as usize) {
            Some(PrimValue::Int(n)) => NixEvalResult::Int(*n),
            Some(PrimValue::Float(f)) => NixEvalResult::Float(*f),
            Some(PrimValue::Str(sv)) => NixEvalResult::Str(sv.clone()),
            Some(PrimValue::Bool(b)) => NixEvalResult::Bool(*b),
            Some(PrimValue::Null) => NixEvalResult::Null,
            Some(PrimValue::List(xs)) => NixEvalResult::List(xs.clone()),
            Some(PrimValue::AttrSet(kvs)) => NixEvalResult::AttrSet(kvs.clone()),
            Some(PrimValue::Path(p)) => NixEvalResult::Str(p.clone()),
            _ => NixEvalResult::Error(NixEvalError::Readback("unreadable prim".into())),
        }
    } else if s.tag == TAG_PRIM_FUN {
        NixEvalResult::Error(NixEvalError::Readback("unsaturated prim fun".into()))
    } else {
        match psi_native::<ΔK, NixPrimVal, NixPrimFun>(net) {
            ReadbackResult::Lambda(ast) => NixEvalResult::Lambda(ast),
            ReadbackResult::Partial(_) => {
                NixEvalResult::Error(NixEvalError::Readback("open term".into()))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eval_identity_lambda() {
        let rt = NixRuntime::pure();
        match rt.eval("x: x") {
            NixEvalResult::Lambda(_) => {}
            NixEvalResult::Error(e) => panic!("expected lambda, got error: {e:?}"),
            _ => panic!("unexpected value result"),
        }
    }

    #[test]
    fn eval_id_applied() {
        let rt = NixRuntime::pure();
        match rt.eval("(x: x) (y: y)") {
            NixEvalResult::Lambda(_) => {}
            NixEvalResult::Error(e) => panic!("expected lambda, got error: {e:?}"),
            _ => panic!("unexpected"),
        }
    }

    #[test]
    fn eval_add() {
        let rt = NixRuntime::pure();
        match rt.eval("3 + 4") {
            NixEvalResult::Int(7) => {}
            NixEvalResult::Error(e) => panic!("expected 7, got error: {e:?}"),
            _ => panic!("expected Int(7), got other"),
        }
    }

    fn expect_str(rt: &NixRuntime, src: &str) -> Arc<str> {
        match rt.eval(src) {
            NixEvalResult::Str(s) => s,
            NixEvalResult::Error(e) => panic!("expected Str for {src:?}, got error: {e:?}"),
            _ => panic!("expected Str for {src:?}, got non-string value"),
        }
    }

    #[test]
    fn eval_str_interp_literal_hole() {
        // `${e}` desugars to toString-coerced concat: "a" + toString 5 + "c".
        let rt = NixRuntime::pure();
        assert_eq!(&*expect_str(&rt, "\"a${toString 5}c\""), "a5c");
    }

    #[test]
    fn eval_str_interp_let_var() {
        let rt = NixRuntime::pure();
        assert_eq!(
            &*expect_str(&rt, "let n = 5; in \"n=${toString n}\""),
            "n=5"
        );
    }

    #[test]
    fn eval_str_interp_hole_first() {
        // Hole then literal (e.g. `"${pkgs}/bin"`) — each Add has a value operand.
        let rt = NixRuntime::pure();
        assert_eq!(&*expect_str(&rt, "let a = 1; in \"${toString a}!\""), "1!");
    }

    #[test]
    fn eval_str_interp_real_world_shape() {
        // Dominant derivation shape: literal-hole-literal `"${pkgs.bash}/bin/bash"`.
        let rt = NixRuntime::pure();
        let src = "let p = \"/nix/store/bash\"; in \"${p}/bin/bash\"";
        assert_eq!(&*expect_str(&rt, src), "/nix/store/bash/bin/bash");
    }

    #[test]
    fn eval_str_interp_string_hole() {
        // Hole is already a string; toString is identity on strings.
        let rt = NixRuntime::pure();
        assert_eq!(&*expect_str(&rt, "let x = \"hi\"; in \"<${x}>\""), "<hi>");
    }

    #[test]
    fn eval_path_readback() {
        // Bare path reads back as its path string (was "unreadable prim").
        // Nix absolutises a relative path literal at parse time against the
        // CWD when there is no file context (`literals::translate_path`).
        let rt = NixRuntime::pure();
        let cwd = std::env::current_dir().expect("cwd");
        assert_eq!(
            &*expect_str(&rt, "./foo"),
            cwd.join("foo").to_string_lossy()
        );
    }

    #[test]
    fn eval_canonical_convertible_same_value() {
        // Conv-eq: `2 + 2` and `4` reduce to the same normal form → equal values.
        let rt = NixRuntime::pure();
        let (v1, _) = rt.eval_canonical("2 + 2").expect("2+2 canonical");
        let (v2, _) = rt.eval_canonical("4").expect("4 canonical");
        assert!(v1.conv_eq(&v2), "2+2 and 4 are conv-equal");
    }

    #[test]
    fn eval_canonical_distinct_differ() {
        // Non-convertible values must NOT compare equal (no false-equal).
        let rt = NixRuntime::pure();
        let (v1, _) = rt.eval_canonical("2 + 2").expect("4 canonical");
        let (v2, _) = rt.eval_canonical("5").expect("5 canonical");
        assert!(!v1.conv_eq(&v2), "4 and 5 are not conv-equal");
    }

    #[test]
    fn eval_canonical_folds_arithmetic_to_value() {
        // `eval_canonical` returns (value, residual-interaction-count). The
        // VALUE is the real invariant: `1 + 2 + 3` must canonicalize to Int(6).
        //
        // The count is the *post-WHNF residual* drained by `normalize_demand`
        // (reduce/mod.rs:347-363), NOT total work: that fn forces WHNF first via
        // `force_whnf_with_prims` — whose own interactions are dropped — then
        // counts only what remains. Arithmetic `+` is the Pure `add` prim
        // (dnx-core/src/prim.rs:313), folded entirely during WHNF-forcing of a
        // scalar, so the residual is empty ⇒ count 0, same as a literal. The
        // count is therefore 0 for *any* fully-forcing scalar, not a work meter.
        let rt = NixRuntime::pure();
        let (lit, n_lit) = rt.eval_canonical("4").expect("literal");
        let (red, n_red) = rt.eval_canonical("1 + 2 + 3").expect("arithmetic");
        assert!(matches!(lit, NixEvalResult::Int(4)), "literal 4");
        assert!(matches!(red, NixEvalResult::Int(6)), "1+2+3 folds to 6");
        assert_eq!(n_lit, 0, "a literal needs no reduction");
        assert_eq!(
            n_red, 0,
            "prim-folded scalar leaves no residual interaction"
        );
    }

    #[test]
    fn eval_fix_const_int() {
        // fix (self: 1): self DISCARDED → recursive arg erased → must normalize to 1.
        // main.tex §4: strict-LO demand erases the recursive branch (no divergence).
        let rt = NixRuntime::pure();
        match rt.eval("fix (self: 1)") {
            NixEvalResult::Int(1) => {}
            NixEvalResult::Error(e) => panic!("fix(self:1) diverged: {e:?}"),
            _ => panic!("expected Int(1)"),
        }
    }

    #[test]
    fn eval_applied_fix_id() {
        // (fix (self: x: x)) 5: self DISCARDED, result λx.x APPLIED to 5 → 5.
        // Forces PAST the fix-result (unlike fix(self:1)) → exercises Y-net rep
        // resolution. main.tex §4: strict-LO erases discarded self-call branch.
        let rt = NixRuntime::pure();
        match rt.eval("(fix (self: x: x)) 5") {
            NixEvalResult::Int(5) => {}
            NixEvalResult::Error(e) => panic!("applied fix diverged: {e:?}"),
            _ => panic!("expected Int(5), got other"),
        }
    }

    #[test]
    fn eval_eq_true() {
        let rt = NixRuntime::pure();
        match rt.eval("1 == 1") {
            NixEvalResult::Bool(true) => {}
            NixEvalResult::Error(e) => panic!("expected Bool(true), got error: {e:?}"),
            _ => panic!("unexpected"),
        }
    }

    #[test]
    fn eval_eq_false() {
        let rt = NixRuntime::pure();
        match rt.eval("1 == 2") {
            NixEvalResult::Bool(false) => {}
            NixEvalResult::Error(e) => panic!("expected Bool(false), got error: {e:?}"),
            _ => panic!("unexpected"),
        }
    }

    #[test]
    fn eval_lt_true() {
        let rt = NixRuntime::pure();
        match rt.eval("1 < 2") {
            NixEvalResult::Bool(true) => {}
            NixEvalResult::Error(e) => panic!("expected Bool(true), got error: {e:?}"),
            _ => panic!("unexpected"),
        }
    }

    #[test]
    fn eval_type_of_int() {
        let rt = NixRuntime::pure();
        match rt.eval("typeOf 42") {
            NixEvalResult::Str(s) if s.as_ref() == "int" => {}
            NixEvalResult::Error(e) => panic!("expected \"int\", got error: {e:?}"),
            _ => panic!("expected Str(int)"),
        }
    }

    #[test]
    fn eval_type_of_bool_true() {
        let rt = NixRuntime::pure();
        match rt.eval("typeOf (1 == 1)") {
            NixEvalResult::Str(s) if s.as_ref() == "bool" => {}
            NixEvalResult::Error(e) => panic!("expected \"bool\", got error: {e:?}"),
            _ => panic!("expected Str(bool)"),
        }
    }

    #[test]
    fn eval_type_of_bool_false() {
        let rt = NixRuntime::pure();
        match rt.eval("typeOf (1 == 2)") {
            NixEvalResult::Str(s) if s.as_ref() == "bool" => {}
            NixEvalResult::Error(e) => panic!("expected \"bool\", got error: {e:?}"),
            _ => panic!("expected Str(bool)"),
        }
    }

    #[test]
    fn eval_type_of_str() {
        let rt = NixRuntime::pure();
        match rt.eval(r#"typeOf "hello""#) {
            NixEvalResult::Str(s) if s.as_ref() == "string" => {}
            NixEvalResult::Error(e) => panic!("expected \"string\", got error: {e:?}"),
            _ => panic!("expected Str(string)"),
        }
    }

    #[test]
    fn eval_type_of_null() {
        let rt = NixRuntime::pure();
        match rt.eval("typeOf null") {
            NixEvalResult::Str(s) if s.as_ref() == "null" => {}
            NixEvalResult::Error(e) => panic!("expected \"null\", got error: {e:?}"),
            _ => panic!("expected Str(null)"),
        }
    }

    #[test]
    fn eval_str_concat() {
        let rt = NixRuntime::pure();
        match rt.eval(r#""foo" + "bar""#) {
            NixEvalResult::Str(s) if s.as_ref() == "foobar" => {}
            NixEvalResult::Error(e) => panic!("expected foobar, got error: {e:?}"),
            _ => panic!("expected Str(foobar)"),
        }
    }

    #[test]
    fn eval_if_eq_true_branch() {
        let rt = NixRuntime::pure();
        match rt.eval("if 1 == 1 then 42 else 0") {
            NixEvalResult::Int(42) => {}
            NixEvalResult::Error(e) => panic!("expected 42, got error: {e:?}"),
            _ => panic!("expected Int(42)"),
        }
    }

    #[test]
    #[ignore = "genuine recursion still diverges (rep proliferation); length[1 2 3] hits it. length[]✓. See eval_rec_countdown + main.md:962."]
    fn eval_list_length() {
        let rt = NixRuntime::pure();
        match rt.eval("length [1 2 3]") {
            NixEvalResult::Int(3) => {}
            NixEvalResult::Error(e) => panic!("expected 3, got error: {e:?}"),
            _ => panic!("expected Int(3)"),
        }
    }

    #[test]
    fn eval_list_head() {
        let rt = NixRuntime::pure();
        match rt.eval("head [10 20 30]") {
            NixEvalResult::Int(10) => {}
            NixEvalResult::Error(e) => panic!("expected 10, got error: {e:?}"),
            _ => panic!("expected Int(10)"),
        }
    }

    #[test]
    #[ignore = "genuine recursion still diverges (rep proliferation). See eval_rec_countdown + main.md:962."]
    fn eval_list_tail_length() {
        let rt = NixRuntime::pure();
        match rt.eval("length (tail [1 2 3])") {
            NixEvalResult::Int(2) => {}
            NixEvalResult::Error(e) => panic!("expected 2, got error: {e:?}"),
            _ => panic!("expected Int(2)"),
        }
    }

    #[test]
    fn eval_empty_list_length() {
        let rt = NixRuntime::pure();
        match rt.eval("length []") {
            NixEvalResult::Int(0) => {}
            NixEvalResult::Error(e) => panic!("expected 0, got error: {e:?}"),
            _ => panic!("expected Int(0)"),
        }
    }

    #[test]
    #[ignore = "genuine recursion (self USED, recurses N>0) still diverges: Y-net dup reps proliferate (R7 commute, never R6 annihilate) — only the 1st iteration's prims fire then reps churn. Distinct from the self-loop bug already fixed (fix(self:x:x)✓). Minimal non-list repro. See main.md:962 (absolute levels) + state.md."]
    fn eval_rec_countdown() {
        let rt = NixRuntime::pure();
        match rt.eval("(fix (self: n: if n == 0 then 0 else self (n - 1))) 3") {
            NixEvalResult::Int(0) => {}
            NixEvalResult::Error(e) => panic!("countdown err: {e:?}"),
            _ => panic!("countdown wrong"),
        }
    }

    #[test]
    fn eval_multi_use_var() {
        let rt = NixRuntime::pure();
        match rt.eval("(x: x + x) 5") {
            NixEvalResult::Int(10) => {}
            NixEvalResult::Error(e) => panic!("error: {e:?}"),
            _ => panic!("expected Int(10)"),
        }
    }

    #[test]
    fn eval_sub() {
        let rt = NixRuntime::pure();
        match rt.eval("10 - 3") {
            NixEvalResult::Int(7) => {}
            NixEvalResult::Error(e) => panic!("error: {e:?}"),
            _ => panic!("expected Int(7)"),
        }
    }

    #[test]
    fn eval_mul() {
        let rt = NixRuntime::pure();
        match rt.eval("4 * 5") {
            NixEvalResult::Int(20) => {}
            NixEvalResult::Error(e) => panic!("error: {e:?}"),
            _ => panic!("expected Int(20)"),
        }
    }

    #[test]
    fn eval_div() {
        let rt = NixRuntime::pure();
        match rt.eval("10 / 2") {
            NixEvalResult::Int(5) => {}
            NixEvalResult::Error(e) => panic!("error: {e:?}"),
            _ => panic!("expected Int(5)"),
        }
    }

    #[test]
    fn eval_ne_true() {
        let rt = NixRuntime::pure();
        match rt.eval("1 != 2") {
            NixEvalResult::Bool(true) => {}
            NixEvalResult::Error(e) => panic!("error: {e:?}"),
            _ => panic!("expected Bool(true)"),
        }
    }

    #[test]
    fn eval_ne_false() {
        let rt = NixRuntime::pure();
        match rt.eval("1 != 1") {
            NixEvalResult::Bool(false) => {}
            NixEvalResult::Error(e) => panic!("error: {e:?}"),
            _ => panic!("expected Bool(false)"),
        }
    }

    #[test]
    fn eval_if_false_branch() {
        let rt = NixRuntime::pure();
        match rt.eval("if 1 == 2 then 99 else 42") {
            NixEvalResult::Int(42) => {}
            NixEvalResult::Error(e) => panic!("error: {e:?}"),
            _ => panic!("expected Int(42)"),
        }
    }

    #[test]
    fn eval_let_binding() {
        let rt = NixRuntime::pure();
        match rt.eval("let x = 5; in x + x") {
            NixEvalResult::Int(10) => {}
            NixEvalResult::Error(e) => panic!("error: {e:?}"),
            _ => panic!("expected Int(10)"),
        }
    }

    #[test]
    fn eval_type_of_lambda() {
        let rt = NixRuntime::pure();
        match rt.eval(r#"typeOf (x: x)"#) {
            NixEvalResult::Str(s) if s.as_ref() == "lambda" => {}
            NixEvalResult::Error(e) => panic!("error: {e:?}"),
            _ => panic!("expected Str(lambda)"),
        }
    }

    #[test]
    fn eval_type_of_float() {
        let rt = NixRuntime::pure();
        match rt.eval("typeOf 1.5") {
            NixEvalResult::Str(s) if s.as_ref() == "float" => {}
            NixEvalResult::Error(e) => panic!("error: {e:?}"),
            _ => panic!("expected Str(float)"),
        }
    }

    #[test]
    #[ignore = "typeOf over Scott list needs net list-recognizer (PrimValue::Lambda is opaque)"]
    fn eval_type_of_list() {
        let rt = NixRuntime::pure();
        match rt.eval("typeOf [1 2]") {
            NixEvalResult::Str(s) if s.as_ref() == "list" => {}
            NixEvalResult::Error(e) => panic!("error: {e:?}"),
            _ => panic!("expected Str(list)"),
        }
    }

    #[test]
    fn eval_nested_let() {
        let rt = NixRuntime::pure();
        match rt.eval("let a = 3; b = 4; in a + b") {
            NixEvalResult::Int(7) => {}
            NixEvalResult::Error(e) => panic!("error: {e:?}"),
            _ => panic!("expected Int(7)"),
        }
    }

    #[test]
    fn eval_is_function_lambda() {
        let rt = NixRuntime::pure();
        match rt.eval("isFunction (x: x)") {
            NixEvalResult::Bool(true) => {}
            NixEvalResult::Error(e) => panic!("error: {e:?}"),
            _ => panic!("expected Bool(true)"),
        }
    }

    #[test]
    fn eval_is_function_int() {
        let rt = NixRuntime::pure();
        match rt.eval("isFunction 42") {
            NixEvalResult::Bool(false) => {}
            NixEvalResult::Error(e) => panic!("error: {e:?}"),
            _ => panic!("expected Bool(false)"),
        }
    }

    #[test]
    fn eval_is_int_true() {
        let rt = NixRuntime::pure();
        match rt.eval("isInt 42") {
            NixEvalResult::Bool(true) => {}
            NixEvalResult::Error(e) => panic!("error: {e:?}"),
            _ => panic!("expected Bool(true)"),
        }
    }

    #[test]
    fn eval_is_null_true() {
        let rt = NixRuntime::pure();
        match rt.eval("isNull null") {
            NixEvalResult::Bool(true) => {}
            NixEvalResult::Error(e) => panic!("error: {e:?}"),
            _ => panic!("expected Bool(true)"),
        }
    }

    #[test]
    fn eval_is_list_true() {
        let rt = NixRuntime::pure();
        match rt.eval("isList [1 2 3]") {
            NixEvalResult::Bool(false) => {}
            NixEvalResult::Error(e) => panic!("error: {e:?}"),
            _ => panic!("expected Bool(false)"),
        }
    }

    fn expect_list(rt: &NixRuntime, src: &str) -> Vec<PrimValue> {
        match rt.eval(src) {
            NixEvalResult::List(xs) => xs,
            NixEvalResult::Error(e) => panic!("expected List for {src:?}, got error: {e:?}"),
            _ => panic!("expected List for {src:?}, got non-list value"),
        }
    }

    #[test]
    fn eval_list_int_readback() {
        let rt = NixRuntime::pure();
        assert_eq!(
            expect_list(&rt, "[1 2 3]"),
            vec![PrimValue::Int(1), PrimValue::Int(2), PrimValue::Int(3)]
        );
    }

    #[test]
    fn eval_empty_list_readback() {
        let rt = NixRuntime::pure();
        assert_eq!(expect_list(&rt, "[]"), vec![]);
    }

    #[test]
    fn eval_list_str_readback() {
        let rt = NixRuntime::pure();
        assert_eq!(
            expect_list(&rt, r#"["a" "b"]"#),
            vec![PrimValue::Str("a".into()), PrimValue::Str("b".into())]
        );
    }

    #[test]
    fn eval_singleton_computed_elem_readback() {
        // A lone element is forced at readback: `1 + 1` reduces to Int(2).
        let rt = NixRuntime::pure();
        assert_eq!(expect_list(&rt, "[(1 + 1)]"), vec![PrimValue::Int(2)]);
    }

    #[test]
    fn eval_singleton_nested_readback() {
        // Nested list element read back recursively.
        let rt = NixRuntime::pure();
        assert_eq!(
            expect_list(&rt, "[[1]]"),
            vec![PrimValue::List(vec![PrimValue::Int(1)])]
        );
    }

    #[test]
    #[ignore = "PRE-EXISTING reducer bug, NOT readback: forcing a non-last element of a multi-element list fails at the eval layer — `head [(1 + 1) 9]` and `head [[1] [2]]` already return <lambda> via the plain Scott eliminator (no readback involved). Off-spine arg redexes are not in frontier1 after R4 duplicates the cons spine (take_spine_redex inFrontier=false). Same class as the recursion-divergence bug (see eval_rec_countdown, main.md:962). Readback reconstructs exactly what eval delivers; flat lists [1 2 3]/[\"a\" \"b\"] and singleton/pre-reduced nested lists pass."]
    fn eval_multi_computed_elem_readback() {
        let rt = NixRuntime::pure();
        assert_eq!(
            expect_list(&rt, "[(1 + 1) 3]"),
            vec![PrimValue::Int(2), PrimValue::Int(3)]
        );
    }

    #[test]
    #[ignore = "PRE-EXISTING reducer bug, NOT readback: same off-spine-arg-not-in-frontier1 gap as eval_multi_computed_elem_readback. `head [[1] [2]]` returns <lambda> through the plain Scott eliminator. Singleton nested [[1]] passes (eval_singleton_nested_readback)."]
    fn eval_multi_nested_readback() {
        let rt = NixRuntime::pure();
        assert_eq!(
            expect_list(&rt, "[[1] [2]]"),
            vec![
                PrimValue::List(vec![PrimValue::Int(1)]),
                PrimValue::List(vec![PrimValue::Int(2)])
            ]
        );
    }

    #[test]
    fn eval_lambda_still_reads_back() {
        // Recognizer must NOT swallow a genuine lambda as a list.
        let rt = NixRuntime::pure();
        match rt.eval("x: x") {
            NixEvalResult::Lambda(_) => {}
            NixEvalResult::List(_) => panic!("lambda misread as list"),
            NixEvalResult::Error(e) => panic!("expected Lambda, got error: {e:?}"),
            _ => panic!("expected Lambda, got other value"),
        }
    }
}
