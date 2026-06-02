use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::sync::Arc;

pub type Name = Arc<str>;

/// Translation scope: tracks bound vars and usage counts.
///
/// `binders` is a **stack of counts per name** so shadowing is correct: binding
/// a name already in scope pushes a fresh `0` on top, and unbinding pops it,
/// restoring the outer binder's count. A flat name→count map would let an inner
/// `(h: …)` clobber+erase the outer `h`'s use-count (the use of the OUTER `h` is
/// then lost → wrong rep/era insertion / capture). The count consulted is always
/// the innermost (top-of-stack) binder for that name — lexical scoping by
/// construction.
#[derive(Default, Clone)]
pub struct Scope {
    /// Per-name stack of use-counts; one entry per live binder of that name
    /// (innermost on top). Absent / empty ⇒ the name is not bound. `pub(crate)`
    /// only so in-crate test scaffolding can `..Scope::new()` it; mutate via the
    /// `bind`/`unbind`/`use_var` API, never directly.
    pub(crate) binders: HashMap<Name, Vec<u32>>,
    /// Directory of the source file being parsed, if known. `import ./x.nix`
    /// resolves relative paths against it.
    pub base_dir: Option<PathBuf>,
    /// Canonical paths of files whose `import` is currently being resolved up
    /// this chain. Re-entering one means a cycle (`import` cycle-detection,
    /// mirrors pass0 topo_check; vic/plans/imports-design.md:166-167).
    pub in_progress: HashSet<PathBuf>,
    /// Search-path registry: `<name>` / `<name/sub>` import roots → local dir.
    /// Built once from `DNX_PATH` at the top scope (`with_base`) and inherited
    /// by child import scopes via a cheap `Arc` clone (mirrors `in_progress`;
    /// nixpkgs-lib-design.md §1.2). Empty for a bare `Scope::new()`.
    pub search_paths: Arc<HashMap<String, PathBuf>>,
}

impl Scope {
    /// A base-less scope. `import <name>` still resolves through the search-path
    /// registry read from `DNX_PATH` (so a bare `dnx eval 'import <…>'` works);
    /// only relative-path `import`s need a `base_dir` (see [`with_base`]).
    pub fn new() -> Self {
        Scope {
            search_paths: Arc::new(search_paths_from_env()),
            ..Scope::default()
        }
    }

    /// A scope whose relative `import`s resolve against `base_dir`, with the
    /// search-path registry read from the `DNX_PATH` environment variable.
    pub fn with_base(base_dir: PathBuf) -> Self {
        Scope {
            base_dir: Some(base_dir),
            ..Scope::new()
        }
    }

    /// Enter a binder for `name`: push a fresh use-count of `0`. A binder of the
    /// same name already in scope is shadowed (its count saved beneath).
    pub fn bind(&mut self, name: Name) {
        self.binders.entry(name).or_default().push(0);
    }

    /// Leave the innermost binder for `name`, restoring any outer binder's count.
    pub fn unbind(&mut self, name: &Name) {
        if let Some(stack) = self.binders.get_mut(name) {
            stack.pop();
            if stack.is_empty() {
                self.binders.remove(name);
            }
        }
    }

    /// Count one use against the innermost live binder of `name`. Returns `false`
    /// when `name` is not bound (a free name / prim — not use-counted).
    pub fn use_var(&mut self, name: &Name) -> bool {
        match self.binders.get_mut(name).and_then(|s| s.last_mut()) {
            Some(c) => {
                *c += 1;
                true
            }
            None => false,
        }
    }

    /// Use-count of the innermost live binder of `name` (`0` if unbound).
    pub fn use_count(&self, name: &Name) -> u32 {
        self.binders
            .get(name)
            .and_then(|s| s.last())
            .copied()
            .unwrap_or(0)
    }

    pub fn is_bound(&self, name: &str) -> bool {
        self.binders.get(name).is_some_and(|s| !s.is_empty())
    }
}

/// Parse the `DNX_PATH` registry: colon-separated `name=dir` entries, split on
/// the first `=` per entry (a dir may itself contain `=`). First entry for a
/// given name wins. Entries without `=`, or with an empty name, are skipped.
/// Unset/empty `DNX_PATH` yields an empty map. Pure aside from the single env
/// read (the documented config seam; nixpkgs-lib-design.md §1.2).
fn search_paths_from_env() -> HashMap<String, PathBuf> {
    let raw = match std::env::var("DNX_PATH") {
        Ok(v) => v,
        Err(_) => return HashMap::new(),
    };
    let mut map = HashMap::new();
    for entry in raw.split(':').filter(|e| !e.is_empty()) {
        if let Some((name, dir)) = entry.split_once('=') {
            if !name.is_empty() {
                map.entry(name.to_string())
                    .or_insert_with(|| PathBuf::from(dir));
            }
        }
    }
    map
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A shadowing inner binder must NOT clobber the outer binder's use-count.
    /// Mirrors `(h: <use outer h> (h: …))`: use outer, then a nested same-name
    /// binder enters/uses/leaves — the outer's count must survive (was lost with
    /// a flat name→count map, yielding a spurious erase + capture).
    #[test]
    fn shadow_preserves_outer_use_count() {
        let h: Name = Arc::from("h");
        let mut s = Scope::new();
        s.bind(h.clone());
        assert!(s.use_var(&h), "use outer h");
        // inner binder shadows.
        s.bind(h.clone());
        assert_eq!(s.use_count(&h), 0, "inner starts fresh");
        assert!(s.use_var(&h));
        assert_eq!(s.use_count(&h), 1, "inner counts only its own use");
        s.unbind(&h);
        // back to outer: its single use is intact.
        assert_eq!(s.use_count(&h), 1, "outer use-count restored after shadow");
        assert!(s.is_bound("h"));
        s.unbind(&h);
        assert!(!s.is_bound("h"), "fully unbound");
        assert_eq!(s.use_count(&h), 0);
    }
}
