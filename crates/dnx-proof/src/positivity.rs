use crate::driver::whnf_tm;
use crate::env::GlobalEnv;
use crate::symbol::IndId;
use crate::tm::Tm;

/// `i` occurs only strictly-positively in ctor-arg type `t` (Lean `inductive.cpp:393-409`,
/// proofs.md:155 "**whnf arg**; `Ind` in ANY Pi-domain → reject; valid `Ind`-app head →
/// recursive-ok; else reject. Non-nested only, matches v1"). Mirrors `check_positivity`:
/// - **whnf first** (`:393`): a δ-unfoldable `Const`/β-redex can hide a `Pi` whose domain is a
///   NEGATIVE occurrence — invisible to a raw walk (e.g. `g Unit` with `g := λ_. Bad → Type`);
/// - no occurrence ⇒ nonrecursive arg, OK (`:393`);
/// - `Pi`: `i` left of `→` (domain) ⇒ reject, else recurse the codomain (`:395-401`);
/// - non-`Pi` with an occurrence ⇒ OK iff it is a valid `i`-app head (`:402-403`), else
///   the occurrence is buried under a non-spos head ⇒ reject (`:404-407`).
///
/// `whnf_tm` is driven with an empty context: positivity runs at admission BEFORE `i` is
/// registered (env.rs), so β/δ are the only redexes that can fire (ι on `Elim i` is stuck — `i`
/// is unregistered; ι on other inductives needs no local context for its closed scrutinee), and
/// neither β nor δ consults the binder context.
pub fn strictly_positive(env: &GlobalEnv, i: IndId, t: &Tm) -> bool {
    match whnf_tm(env, &Vec::new(), t) {
        Tm::Pi(a, b) => !occurs(env, i, &a) && strictly_positive(env, i, &b),
        w => !occurs(env, i, &w) || valid_ind_app(env, i, &w),
    }
}

/// A valid recursive occurrence: the application spine's head is `Ind i` and `i` does not
/// occur in any spine argument (non-nested, `inductive.cpp:387-391` `is_valid_ind_app`).
fn valid_ind_app(env: &GlobalEnv, i: IndId, t: &Tm) -> bool {
    let mut head = t;
    while let Tm::App(f, x) = head {
        if occurs(env, i, x) {
            return false;
        }
        head = f;
    }
    matches!(head, Tm::Ind(j) if *j == i)
}

/// Does `IndId i` occur anywhere in `t`? Each node is **whnf'd first** so an occurrence hidden
/// behind a δ-`Const`/β-redex (e.g. a domain `h Unit` with `h := λ_. Bad`) is not missed
/// (proofs.md:155). `Ctor`/`Elim` are TERMS, never the *type* `i`, so they are not occurrences
/// of the recursive type — only `Tm::Ind i` is (proofs.md:155 "`Ind` occurs …").
pub fn occurs(env: &GlobalEnv, i: IndId, t: &Tm) -> bool {
    match whnf_tm(env, &Vec::new(), t) {
        Tm::Ind(j) => j == i,
        Tm::Pi(a, b) | Tm::Lam(a, b) | Tm::App(a, b) => occurs(env, i, &a) || occurs(env, i, &b),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::IndId;
    use crate::tm::Tm;

    // Positivity now whnf's via the env (proofs.md:155); the pure-structural cases use an empty
    // env so whnf is the identity and the classifier behaves exactly as the raw walk did.
    fn empty() -> GlobalEnv {
        GlobalEnv::default()
    }

    #[test]
    fn r3_non_positive_rejected() {
        // Bad := mk : (Bad → Bad) → Bad  ; the arg `(Bad→Bad)` has Bad left of →
        let bad_arg = Tm::Pi(
            Box::new(Tm::Pi(
                Box::new(Tm::Ind(IndId(0))),
                Box::new(Tm::Ind(IndId(0))),
            )),
            Box::new(Tm::Ind(IndId(0))),
        );
        assert!(!strictly_positive(&empty(), IndId(0), &bad_arg));
    }

    #[test]
    fn nat_succ_positive() {
        // succ : Nat → Nat ; arg type `Nat` is strictly positive
        assert!(strictly_positive(&empty(), IndId(0), &Tm::Ind(IndId(0))));
    }

    #[test]
    fn buried_occurrence_rejected() {
        // mk : (f Bad) → Bad ; `Bad` buried as an App arg under a non-spos head `Const f`
        // (Lean `inductive.cpp:404-407`). The old `_ => true` arm wrongly accepted this.
        let arg = Tm::App(
            Box::new(Tm::Const(crate::symbol::ConstId(0))),
            Box::new(Tm::Ind(IndId(0))),
        );
        assert!(!strictly_positive(&empty(), IndId(0), &arg));
    }

    #[test]
    fn applied_recursive_arg_positive() {
        // `(Ind self) x` with `self` absent from `x` is a valid recursive app head
        // (`inductive.cpp:402-403`): no-false-green — classifier accepts, not blanket-reject.
        let arg = Tm::App(Box::new(Tm::Ind(IndId(0))), Box::new(Tm::Var(0)));
        assert!(strictly_positive(&empty(), IndId(0), &arg));
    }

    #[test]
    fn self_under_app_arg_of_ind_rejected() {
        // `(Ind self) (Ind self)` — `self` nested inside a spine arg ⇒ rejected (non-nested v1).
        let arg = Tm::App(Box::new(Tm::Ind(IndId(0))), Box::new(Tm::Ind(IndId(0))));
        assert!(!strictly_positive(&empty(), IndId(0), &arg));
    }
}
