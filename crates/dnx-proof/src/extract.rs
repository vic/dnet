//! Proved value extraction (verifyAndExtract analogue, nix-effects-extraction.md §3).
//! Gate with `check`, normalize with `nf_tm`, then decode the constructor spine
//! into a runtime `PrimValue`. `decode` is the ONLY new TCB surface (G3/G5):
//! a refusal is always SAFE (never a wrong-but-typed value).

use dnx_core::prim::PrimValue;

use crate::driver::{head_is_ind, nf_tm, spine};
use crate::env::GlobalEnv;
use crate::inductive::Inductive;
use crate::infer::{check, TypeError};
use crate::symbol::IndId;
use crate::tm::Tm;

/// Why extraction refused. A refusal is always SAFE (never a wrong value).
#[derive(Debug, PartialEq, Eq)]
pub enum ExtractError {
    /// `tm` did not type-check at `ty` (the gate failed). Carries the kernel error.
    TypeCheck(TypeError),
    /// NF head is not a constructor of the goal inductive: open/neutral/stuck term,
    /// a λ (function value), or a ctor of the WRONG inductive. (G4/G5)
    NotAValue,
    /// The goal type's head inductive is not one of the v1 built-ins
    /// (Nat/Bool/List), or is a built-in with an unsupported element type. (G6)
    Unsupported(&'static str),
}

/// The three built-in encodings v1 recognises *structurally* (§2.2), never by id.
enum BuiltIn {
    Nat,
    Bool,
    List,
}

/// Proved extraction. Returns a `PrimValue` ONLY if `tm : ty` checks in the EMPTY
/// context (closed term, closed type). This is the dnx `verifyAndExtract`
/// (nix-effects-extraction.md §1.4): the `check?` is the unbypassed hard gate (G1).
pub fn extract(env: &GlobalEnv, ty: &Tm, tm: &Tm) -> Result<PrimValue, ExtractError> {
    // G1 GATE — unreachable past here unless `check` returns Ok. NO early decode.
    check(env, &Vec::new(), tm, ty).map_err(ExtractError::TypeCheck)?;
    // type-directed: resolve which inductive the (closed) goal type heads with.
    let head = head_inductive(ty).ok_or(ExtractError::Unsupported("non-inductive goal type"))?;
    let ind = env
        .inds
        .get(&head)
        .ok_or(ExtractError::Unsupported("unknown inductive"))?;
    // G4 closed+total NF: reduce the (now well-typed, closed) term to ctor NF.
    let nf = nf_tm(env, &Vec::new(), tm);
    decode(env, ind, &nf)
}

/// Type-directed constructor-spine decoder. PRECONDITION (held by `extract`):
/// `nf` is the β+δ+ι+η normal form of a CLOSED term of type headed by `ind`.
/// Total: every non-ctor / wrong-ctor head ⇒ `Err`, never a fabricated value.
fn decode(env: &GlobalEnv, ind: &Inductive, nf: &Tm) -> Result<PrimValue, ExtractError> {
    match classify(ind) {
        None => Err(ExtractError::Unsupported("not a v1 built-in inductive")),
        Some(BuiltIn::Nat) => decode_nat(ind.id, nf),
        Some(BuiltIn::Bool) => decode_bool(ind.id, nf),
        Some(BuiltIn::List) => decode_list(env, ind, nf),
    }
}

/// Walk the goal type's `App` spine to its `Ind(i)` head. A `Π` goal (function
/// type) is intentionally NOT peeled ⇒ `None` ⇒ `Unsupported` (v1 extracts data).
fn head_inductive(ty: &Tm) -> Option<IndId> {
    match ty {
        Tm::Ind(i) => Some(*i),
        Tm::App(f, _) => head_inductive(f),
        _ => None,
    }
}

/// Structural recognition of the three built-ins (§2.2): recognise by ctor SHAPE,
/// not by id (per §0.1 — IndIds are not canonical). `head_is_ind` (driver.rs:27)
/// tells us whether a field is the recursive self-type.
fn classify(ind: &Inductive) -> Option<BuiltIn> {
    let cs = &ind.ctors;
    // NAT: no params, no indices, exactly 2 ctors;
    //      ctor0 nullary, ctor1 has exactly ONE field and it is recursive (Ind self).
    if ind.params.is_empty()
        && ind.indices.is_empty()
        && cs.len() == 2
        && cs[0].args.is_empty()
        && cs[1].args.len() == 1
        && head_is_ind(&cs[1].args[0], ind.id)
    {
        return Some(BuiltIn::Nat);
    }
    // BOOL: no params, no indices, exactly 2 ctors, BOTH nullary.
    if ind.params.is_empty()
        && ind.indices.is_empty()
        && cs.len() == 2
        && cs[0].args.is_empty()
        && cs[1].args.is_empty()
    {
        return Some(BuiltIn::Bool);
    }
    // LIST: exactly 1 param, no indices, exactly 2 ctors;
    //       ctor0 nullary (nil); ctor1 has 2 fields [elem, recursive-tail].
    if ind.params.len() == 1
        && ind.indices.is_empty()
        && cs.len() == 2
        && cs[0].args.is_empty()
        && cs[1].args.len() == 2
        && head_is_ind(&cs[1].args[1], ind.id)
    {
        return Some(BuiltIn::List);
    }
    None
}

/// Count the `succ` spine iteratively (no deep recursion): `succ n = App(Ctor(id,1), n)`,
/// `zero = Ctor(id,0)`. Overflow-guarded (R-Perf / safety).
fn decode_nat(id: IndId, nf: &Tm) -> Result<PrimValue, ExtractError> {
    let mut n: i64 = 0;
    let mut cur = nf;
    loop {
        match cur {
            Tm::Ctor(j, 0) if *j == id => return Ok(PrimValue::Int(n)), // zero
            Tm::App(f, pred) if matches!(**f, Tm::Ctor(j, 1) if j == id) => {
                n = n
                    .checked_add(1)
                    .ok_or(ExtractError::Unsupported("nat too large"))?;
                cur = pred; // succ ⇒ recurse on predecessor
            }
            _ => return Err(ExtractError::NotAValue), // G4/G5
        }
    }
}

/// Two nullary ctors: ctor0 ⇒ false, ctor1 ⇒ true (fourcolor_coloring.rs:99,126-130).
fn decode_bool(id: IndId, nf: &Tm) -> Result<PrimValue, ExtractError> {
    let (h, a) = spine(nf);
    if !a.is_empty() {
        return Err(ExtractError::NotAValue); // bool ctors are nullary
    }
    match h {
        Tm::Ctor(j, 0) if j == id => Ok(PrimValue::Bool(false)),
        Tm::Ctor(j, 1) if j == id => Ok(PrimValue::Bool(true)),
        _ => Err(ExtractError::NotAValue),
    }
}

/// Walk the `cons`-chain, building a `Vec` in order (G3). `nil A` carries only the
/// `np` params; `cons A hd tl` is `params ++ [hd, tl]` (list_append.rs:100-105).
/// Elements decode type-directed via the element inductive (G5).
fn decode_list(env: &GlobalEnv, ind: &Inductive, nf: &Tm) -> Result<PrimValue, ExtractError> {
    let np = ind.params.len();
    let mut out: Vec<PrimValue> = Vec::new();
    let mut cur = nf.clone();
    loop {
        let (h, a) = spine(&cur);
        match h {
            Tm::Ctor(j, 0) if j == ind.id => {
                // nil A : carries only the params, nothing after.
                if a.len() == np {
                    return Ok(PrimValue::List(out));
                }
                return Err(ExtractError::NotAValue);
            }
            Tm::Ctor(j, 1) if j == ind.id => {
                // cons A hd tl : drop the `np` param prefix (driver.rs:81), leaving [hd, tl].
                // element type is the runtime param `a[0]` (cons A hd tl, list_append.rs:104).
                let elem_ind = element_inductive(env, a.first())?;
                let mut fields = a.into_iter().skip(np);
                let (Some(hd), Some(tl), None) = (fields.next(), fields.next(), fields.next())
                else {
                    return Err(ExtractError::NotAValue);
                };
                out.push(decode(env, elem_ind, &hd)?);
                cur = tl; // tail (owned)
            }
            _ => return Err(ExtractError::NotAValue),
        }
    }
}

/// Resolve the element inductive of a list from its runtime param term (the `A` in
/// `cons A hd tl`). Unsupported if the element type is not a registered inductive.
fn element_inductive<'a>(
    env: &'a GlobalEnv,
    param: Option<&Tm>,
) -> Result<&'a Inductive, ExtractError> {
    let pty = param.ok_or(ExtractError::NotAValue)?;
    let id = head_inductive(pty).ok_or(ExtractError::Unsupported("non-inductive list element"))?;
    env.inds
        .get(&id)
        .ok_or(ExtractError::Unsupported("unknown list element inductive"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inductive::{CtorDecl, Inductive};
    use crate::symbol::ConstId;

    // ── builders (mirror soundness.rs / thm_list_append.rs / fourcolor_coloring.rs) ──
    fn app(f: Tm, x: Tm) -> Tm {
        Tm::App(Box::new(f), Box::new(x))
    }
    fn apps(head: Tm, xs: &[Tm]) -> Tm {
        xs.iter().fold(head, |f, a| app(f, a.clone()))
    }
    fn lam(dom: Tm, b: Tm) -> Tm {
        Tm::Lam(Box::new(dom), Box::new(b))
    }

    const NAT: IndId = IndId(0);
    const BOOL: IndId = IndId(1);
    const LIST: IndId = IndId(2);
    const ATOM: IndId = IndId(3);

    // Nat = zero | succ (_:Nat)   (soundness.rs:27-57)
    fn nat_ind() -> Inductive {
        Inductive {
            id: NAT,
            params: vec![],
            indices: vec![],
            sort: 0,
            ctors: vec![
                CtorDecl {
                    ctor_ix: 0,
                    args: vec![],
                    ret_indices: vec![],
                },
                CtorDecl {
                    ctor_ix: 1,
                    args: vec![Tm::Ind(NAT)],
                    ret_indices: vec![],
                },
            ],
        }
    }
    fn nat() -> Tm {
        Tm::Ind(NAT)
    }
    fn zero() -> Tm {
        Tm::Ctor(NAT, 0)
    }
    fn succ(n: Tm) -> Tm {
        app(Tm::Ctor(NAT, 1), n)
    }
    fn lit(n: u32) -> Tm {
        (0..n).fold(zero(), |a, _| succ(a))
    }

    // Bool = false | true   (fourcolor_coloring.rs:88-130)
    fn bool_ind() -> Inductive {
        Inductive {
            id: BOOL,
            params: vec![],
            indices: vec![],
            sort: 0,
            ctors: vec![
                CtorDecl {
                    ctor_ix: 0,
                    args: vec![],
                    ret_indices: vec![],
                },
                CtorDecl {
                    ctor_ix: 1,
                    args: vec![],
                    ret_indices: vec![],
                },
            ],
        }
    }
    fn bool_ty() -> Tm {
        Tm::Ind(BOOL)
    }
    fn fls() -> Tm {
        Tm::Ctor(BOOL, 0)
    }
    fn tru() -> Tm {
        Tm::Ctor(BOOL, 1)
    }

    // List : Π(A:Type₀). Type₀  (thm_list_append.rs:76-105)
    fn list_ind() -> Inductive {
        Inductive {
            id: LIST,
            params: vec![Tm::Sort(0)],
            indices: vec![],
            sort: 0,
            ctors: vec![
                CtorDecl {
                    ctor_ix: 0,
                    args: vec![],
                    ret_indices: vec![],
                }, // nil
                CtorDecl {
                    ctor_ix: 1,
                    args: vec![Tm::Var(0), app(Tm::Ind(LIST), Tm::Var(1))],
                    ret_indices: vec![],
                }, // cons
            ],
        }
    }
    fn list_ty(a: Tm) -> Tm {
        app(Tm::Ind(LIST), a)
    }
    fn nil(a: Tm) -> Tm {
        app(Tm::Ctor(LIST, 0), a)
    }
    fn cons(a_ty: Tm, hd: Tm, tl: Tm) -> Tm {
        apps(Tm::Ctor(LIST, 1), &[a_ty, hd, tl])
    }

    // Atom = e0 | e1 | e2  (3-nullary-ctor enum; thm_list_append.rs:51-65)
    fn atom_ind() -> Inductive {
        Inductive {
            id: ATOM,
            params: vec![],
            indices: vec![],
            sort: 0,
            ctors: (0..3)
                .map(|k| CtorDecl {
                    ctor_ix: k,
                    args: vec![],
                    ret_indices: vec![],
                })
                .collect(),
        }
    }

    /// env with Nat(0), Bool(1), List(2), Atom(3) all admitted.
    fn env() -> GlobalEnv {
        let mut e = GlobalEnv::default();
        e.add_inductive(nat_ind()).unwrap();
        e.add_inductive(bool_ind()).unwrap();
        e.add_inductive(list_ind()).unwrap();
        e.add_inductive(atom_ind()).unwrap();
        e
    }

    // ── POSITIVE vectors (§4.1) ──
    #[test]
    fn p1_zero() {
        assert_eq!(extract(&env(), &nat(), &zero()), Ok(PrimValue::Int(0)));
    }

    #[test]
    fn p2_lit5() {
        assert_eq!(extract(&env(), &nat(), &lit(5)), Ok(PrimValue::Int(5)));
    }

    #[test]
    fn p3_add_2_3_computes_then_extracts() {
        // add := λm.λn. Nat.rec (λ_.Nat) m (λk.λih. succ ih) n   (soundness.rs:192-214)
        let mut e = env();
        let add_body = lam(
            nat(),
            lam(
                nat(),
                apps(
                    Tm::Elim(NAT),
                    &[
                        lam(nat(), nat()),                        // motive λ_.Nat
                        Tm::Var(1),                               // minor_zero = m
                        lam(nat(), lam(nat(), succ(Tm::Var(0)))), // minor_succ
                        Tm::Var(0),                               // scrutinee = n
                    ],
                ),
            ),
        );
        let add_ty = Tm::Pi(
            Box::new(nat()),
            Box::new(Tm::Pi(Box::new(nat()), Box::new(nat()))),
        );
        e.add_const(ConstId(0), add_ty, add_body).unwrap();
        let add_2_3 = app(app(Tm::Const(ConstId(0)), lit(2)), lit(3));
        // gate + nf_tm reduce add 2 3 to lit(5) BEFORE decode (soundness.rs:219,222).
        assert_eq!(extract(&e, &nat(), &add_2_3), Ok(PrimValue::Int(5)));
    }

    #[test]
    fn p4_bool_true() {
        assert_eq!(
            extract(&env(), &bool_ty(), &tru()),
            Ok(PrimValue::Bool(true))
        );
    }

    #[test]
    fn p5_bool_false() {
        assert_eq!(
            extract(&env(), &bool_ty(), &fls()),
            Ok(PrimValue::Bool(false))
        );
    }

    #[test]
    fn p6_bool_elim_iota_then_extract() {
        // Elim Bool (λ_.Bool) <ifFalse=false> <ifTrue=true> true   ι-reduces to `true`.
        // spine: motive · minor_0(false-case) · minor_1(true-case) · scrutinee.
        let e = env();
        let t = apps(
            Tm::Elim(BOOL),
            &[lam(bool_ty(), bool_ty()), fls(), tru(), tru()],
        );
        assert_eq!(extract(&e, &bool_ty(), &t), Ok(PrimValue::Bool(true)));
    }

    #[test]
    fn p7_list_bool_nil() {
        let e = env();
        assert_eq!(
            extract(&e, &list_ty(bool_ty()), &nil(bool_ty())),
            Ok(PrimValue::List(vec![]))
        );
    }

    #[test]
    fn p8_list_bool_order_preserved() {
        let e = env();
        let v = cons(bool_ty(), tru(), cons(bool_ty(), fls(), nil(bool_ty())));
        assert_eq!(
            extract(&e, &list_ty(bool_ty()), &v),
            Ok(PrimValue::List(vec![
                PrimValue::Bool(true),
                PrimValue::Bool(false)
            ]))
        );
    }

    #[test]
    fn p9_list_nat_nested() {
        let e = env();
        let v = cons(nat(), lit(1), cons(nat(), lit(2), nil(nat())));
        assert_eq!(
            extract(&e, &list_ty(nat()), &v),
            Ok(PrimValue::List(vec![PrimValue::Int(1), PrimValue::Int(2)]))
        );
    }

    #[test]
    fn p10_list_of_list_nat() {
        let e = env();
        let inner = cons(nat(), lit(1), nil(nat()));
        let v = cons(list_ty(nat()), inner, nil(list_ty(nat())));
        assert_eq!(
            extract(&e, &list_ty(list_ty(nat())), &v),
            Ok(PrimValue::List(vec![PrimValue::List(vec![
                PrimValue::Int(1)
            ])]))
        );
    }

    // ── NEGATIVE vectors (§4.2) ──
    #[test]
    fn n1_sort_fails_gate() {
        // Sort(0):Sort(1) ≠ Nat ⇒ gate rejects BEFORE decode (G1).
        let r = extract(&env(), &nat(), &Tm::Sort(0));
        assert!(matches!(r, Err(ExtractError::TypeCheck(_))), "got {r:?}");
    }

    #[test]
    fn n2_wrong_ctor_fails_gate() {
        // true : Bool fails conv at Nat ⇒ TypeCheck (G1+G5).
        let r = extract(&env(), &nat(), &tru());
        assert!(matches!(r, Err(ExtractError::TypeCheck(_))), "got {r:?}");
    }

    #[test]
    fn n3_open_term_fails_gate() {
        // free Var(0) fails the EMPTY-ctx gate (G4 via G1).
        let r = extract(&env(), &nat(), &Tm::Var(0));
        assert_eq!(r, Err(ExtractError::TypeCheck(TypeError::UnboundVar)));
    }

    #[test]
    fn n4_function_goal_unsupported() {
        // identity on Nat : Π(Nat).Nat — a Π goal ⇒ head_inductive=None ⇒ Unsupported (G6).
        let e = env();
        let ty = Tm::Pi(Box::new(nat()), Box::new(nat()));
        let id = lam(nat(), Tm::Var(0));
        assert_eq!(
            extract(&e, &ty, &id),
            Err(ExtractError::Unsupported("non-inductive goal type"))
        );
    }

    #[test]
    fn n5_enum_unsupported() {
        // Atom = 3-nullary-ctor enum ⇒ classify None ⇒ Unsupported (G6).
        let e = env();
        let r = extract(&e, &Tm::Ind(ATOM), &Tm::Ctor(ATOM, 0));
        assert!(matches!(r, Err(ExtractError::Unsupported(_))), "got {r:?}");
    }

    #[test]
    fn n6_stuck_open_fails_gate() {
        // Elim Nat <Sort0> zero zero Var(0) : open (Var0) ⇒ gate fails (G1/G4).
        let e = env();
        let stuck = apps(Tm::Elim(NAT), &[Tm::Sort(0), zero(), zero(), Tm::Var(0)]);
        let r = extract(&e, &nat(), &stuck);
        assert!(matches!(r, Err(ExtractError::TypeCheck(_))), "got {r:?}");
    }

    #[test]
    fn n7_no_false_decode_off_by_one() {
        // CRITICAL (G3): lit(4) must decode to EXACTLY Int(4), never Int(5).
        let v = extract(&env(), &nat(), &lit(4)).unwrap();
        assert_eq!(v, PrimValue::Int(4));
        assert_ne!(v, PrimValue::Int(5));
    }

    // ── round-trip property (§4.3): pins Nat decoder vs the trusted `lit` builder ──
    #[test]
    fn roundtrip_nat_u8() {
        let e = env();
        for n in 0u32..=255 {
            assert_eq!(
                extract(&e, &nat(), &lit(n)),
                Ok(PrimValue::Int(i64::from(n)))
            );
        }
    }
}
