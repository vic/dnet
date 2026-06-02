use std::path::{Path, PathBuf};
use std::sync::Arc;

use dnx_lang::runtime::{NixEvalResult, NixRuntime};
use rnix::ast::{self, HasEntry};
use rowan::ast::AstNode;

use crate::error::FlakeError;
use crate::lock::LockFile;

/// The state of a flake's `flake.lock` relative to its declared `inputs`
/// (`dnx flake metadata`). A lock is current only when it pins exactly the
/// declared input names *and* every pinned content still hashes to its record;
/// any divergence is a single `Stale` state (re-run `flake lock`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LockStatus {
    /// No `flake.lock` beside the flake.
    Absent,
    /// The lock pins exactly the declared inputs and every pin still verifies.
    UpToDate,
    /// The lock's pinned inputs differ from the declared inputs, or a pinned
    /// content no longer matches its hash.
    Stale,
}

/// A loaded flake: its `flake.nix` source text and the directory that contains
/// it (the base for resolving local-path inputs).
pub struct Flake {
    src: String,
    dir: PathBuf,
}

/// The enumerated output attribute paths of a flake (e.g.
/// `packages.x86_64-linux.hello`), sorted, without realizing anything.
#[derive(Debug, PartialEq, Eq)]
pub struct FlakeOutputs {
    paths: Vec<Arc<str>>,
}

impl FlakeOutputs {
    /// The fully-qualified output attribute paths, sorted.
    pub fn paths(&self) -> &[Arc<str>] {
        &self.paths
    }
}

/// One declared input: a name bound to a local-path `url`. Our flakes resolve
/// only local paths (no cppNix flake-URL grammar); this is what a `flake.lock`
/// pins, one content hash per input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FlakeInput {
    name: Arc<str>,
    url: Arc<str>,
}

impl FlakeInput {
    /// The input's binding name (the `inputs.<name>` key).
    pub fn name(&self) -> &str {
        &self.name
    }
    /// The input's local-path `url` (a relative path, verbatim from source).
    pub fn url(&self) -> &str {
        &self.url
    }
}

/// The declared `inputs` of a flake, sorted by name. Empty when no `inputs`
/// attribute is present.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FlakeInputs {
    entries: Vec<FlakeInput>,
}

impl FlakeInputs {
    /// The declared inputs, sorted by name.
    pub fn entries(&self) -> &[FlakeInput] {
        &self.entries
    }
}

impl Flake {
    /// Read and hold a flake's source. `path` is either the `flake.nix` file
    /// itself or its containing directory (in which case `flake.nix` is
    /// appended). Validates the surface shape (a top-level attribute set with an
    /// `outputs` function) but does not evaluate.
    pub fn load(path: &Path) -> Result<Flake, FlakeError> {
        let file = if path.is_dir() {
            path.join("flake.nix")
        } else {
            path.to_path_buf()
        };
        let src = std::fs::read_to_string(&file)
            .map_err(|e| FlakeError::Io(Arc::from(format!("{}: {e}", file.display()))))?;
        let top = parse_top_attrset(&src)?;
        if find_entry(&top, "outputs").is_none() {
            return Err(FlakeError::NotAFlake("missing `outputs`".into()));
        }
        let dir = file
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_else(|| PathBuf::from("."));
        Ok(Flake { src, dir })
    }

    /// Enumerate the output attribute paths (`dnx flake show`) by walking the
    /// surface `flake.nix` `outputs` function body. Evaluation-free.
    pub fn show(&self) -> Result<FlakeOutputs, FlakeError> {
        let top = parse_top_attrset(&self.src)?;
        let outputs = find_entry(&top, "outputs")
            .ok_or_else(|| FlakeError::NotAFlake("missing `outputs`".into()))?;
        let body = lambda_body(&outputs)?;
        let mut paths = Vec::new();
        collect_paths(&body, &mut Vec::new(), &mut paths)?;
        paths.sort();
        paths.dedup();
        Ok(FlakeOutputs { paths })
    }

    /// Enumerate the declared `inputs` (the bridge a `flake.lock` is built
    /// from). Evaluation-free surface walk: each `inputs.<name>` must be an
    /// attribute set with a `url` that is a plain local-path string literal. A
    /// non-local url scheme or a missing `url` is rejected; a dynamic (`${...}`)
    /// url is a parse error. No `inputs` attribute yields an empty set.
    pub fn inputs(&self) -> Result<FlakeInputs, FlakeError> {
        let top = parse_top_attrset(&self.src)?;
        let Some(inputs) = find_entry(&top, "inputs") else {
            return Ok(FlakeInputs::default());
        };
        let ast::Expr::AttrSet(set) = inputs else {
            return Err(FlakeError::NotAFlake(
                "`inputs` is not an attribute set".into(),
            ));
        };
        let mut entries = Vec::new();
        for (name, value) in attrset_fields(&set)? {
            entries.push(FlakeInput {
                url: input_url(&name, &value)?,
                name,
            });
        }
        entries.sort_by(|a, b| a.name.cmp(&b.name));
        Ok(FlakeInputs { entries })
    }

    /// The flake's declared top-level `description` (a plain string literal), or
    /// `None` when absent. Evaluation-free surface walk, like `inputs`/`show`. A
    /// non-string or dynamic (`${...}`) description is a typed error, never a
    /// fabricated partial.
    pub fn description(&self) -> Result<Option<Arc<str>>, FlakeError> {
        let top = parse_top_attrset(&self.src)?;
        match find_entry(&top, "description") {
            Some(value) => string_literal(&value)?
                .map(Some)
                .ok_or_else(|| FlakeError::NotAFlake("`description` is not a string".into())),
            None => Ok(None),
        }
    }

    /// Evaluate one output path to WHNF (the seam a future `dnx-drv` layer
    /// turns into a `Derivation`). Resolves the declared `inputs` (each
    /// local-path input loaded as its own flake, its `outputs` applied to its own
    /// resolved inputs, transitively), applies the `outputs` function to that
    /// resolved-inputs attribute set, and selects `<path>`, then forces the head
    /// via the existing evaluator. Input-of-input resolution terminates at a
    /// directory already on the resolution chain (a `self`-reference or a
    /// back-edge), which resolves to a `{ outPath = "<dir>"; }` source marker.
    /// Applying the lambda by its source text (rather than selecting it out of
    /// the flake attribute set) avoids the evaluator's lambda-valued-field limit;
    /// deep nested-attrset output paths remain an honest eval-seam gap.
    pub fn resolve_attr(&self, path: &str) -> Result<NixEvalResult, FlakeError> {
        // No raw attr-path text reaches the evaluator: validate each segment and
        // re-emit it as a quoted selector, so a path like `x; builtins.foo` or
        // `hello}.x` cannot inject or break the built expression.
        let selector =
            quoted_selector(path).ok_or_else(|| FlakeError::AttrNotFound(Arc::from(path)))?;
        let outputs = self.outputs_source()?;
        let inputs = self.resolved_inputs_expr()?;
        let expr = format!("(({outputs}) ({inputs})).{selector}");
        match NixRuntime::pure().eval(&expr) {
            NixEvalResult::Error(e) => Err(FlakeError::Eval(Arc::from(format!("{e:?}")))),
            ok => Ok(ok),
        }
    }

    /// Build our `flake.lock` from the declared `inputs`: resolve each input's
    /// local path to its `flake.nix` and pin it by BLAKE3 (lock.rs). Our flat
    /// format, not the cppNix node graph (arch.md:70).
    pub fn lock(&self) -> Result<LockFile, FlakeError> {
        let mut lock = LockFile::default();
        for input in self.inputs()?.entries() {
            // Stored path is flake-RELATIVE (the declared url + `flake.nix`), so
            // the lock is identical whether the flake dir was spelled `.` or as
            // an absolute path, and is portable across machines (audit-flake.md
            // MED). The absolute `content` path is what is read to hash.
            let rel = Path::new(input.url()).join("flake.nix");
            let content = self.input_flake_dir(input.url()).join("flake.nix");
            lock.pin(input.name(), &rel, &content)?;
        }
        Ok(lock)
    }

    /// Classify the on-disk `flake.lock` against the declared `inputs`
    /// (`dnx flake metadata`). Absent file → [`LockStatus::Absent`]. Otherwise
    /// the lock is [`LockStatus::UpToDate`] only when its pinned input names
    /// equal the declared input names *and* every pin still verifies; any other
    /// case is [`LockStatus::Stale`]. Reuses `inputs`, `LockFile::from_text`, and
    /// `LockFile::verify` — no new pinning logic.
    pub fn lock_status(&self) -> Result<LockStatus, FlakeError> {
        let file = self.dir.join("flake.lock");
        let text = match std::fs::read_to_string(&file) {
            Ok(text) => text,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(LockStatus::Absent),
            Err(e) => {
                return Err(FlakeError::Io(Arc::from(format!(
                    "{}: {e}",
                    file.display()
                ))))
            }
        };
        let lock = LockFile::from_text(&text)?;
        let inputs = self.inputs()?;
        let mut declared: Vec<&str> = inputs.entries().iter().map(|i| i.name()).collect();
        let mut pinned: Vec<&str> = lock.entries().iter().map(|e| e.name()).collect();
        declared.sort_unstable();
        pinned.sort_unstable();
        if declared != pinned || lock.verify(&self.dir).is_err() {
            return Ok(LockStatus::Stale);
        }
        Ok(LockStatus::UpToDate)
    }

    /// Resolve the declared `inputs` to the Nix attribute set the consuming
    /// `outputs` function receives: `{ "name" = <resolved>; ... }`. A dependency
    /// input resolves to its own `outputs` applied to *its own* resolved inputs,
    /// transitively (input-of-input), so a dependency sees the dependencies it
    /// itself declares. A directory already on the resolution chain (a `self`
    /// reference, or a back-edge `A -> B -> A`) cannot be its own outputs without
    /// circular strict evaluation, so it resolves to a source marker
    /// `{ outPath = "<dir>"; }` (the canonical `self.outPath` use): the visited
    /// chain grows by one distinct directory per level, so resolution always
    /// terminates. Input names are quoted + escaped, so no input name is spliced
    /// as live syntax.
    fn resolved_inputs_expr(&self) -> Result<String, FlakeError> {
        self.resolved_inputs_with(&mut vec![canonical(&self.dir)])
    }

    /// Build the resolved-inputs attribute set, carrying the chain of directories
    /// currently being resolved (each already canonicalized). A dependency whose
    /// directory is on the chain is a cycle: it resolves to a source marker rather
    /// than recursing forever; otherwise its outputs are applied to its own
    /// resolved inputs (one deeper on the chain).
    fn resolved_inputs_with(&self, chain: &mut Vec<PathBuf>) -> Result<String, FlakeError> {
        let mut bindings = String::from("{ ");
        for input in self.inputs()?.entries() {
            let dir = self.input_flake_dir(input.url());
            let canon = canonical(&dir);
            let value = if chain.contains(&canon) {
                format!(
                    "{{ outPath = \"{}\"; }}",
                    escape_nix_string(&dir.to_string_lossy())
                )
            } else {
                let dep = Flake::load(&dir)?;
                chain.push(canon);
                let inner = dep.resolved_inputs_with(chain)?;
                chain.pop();
                format!("({}) ({inner})", dep.outputs_source()?)
            };
            bindings.push('"');
            bindings.push_str(&escape_nix_string(input.name()));
            bindings.push_str("\" = ");
            bindings.push_str(&value);
            bindings.push_str("; ");
        }
        bindings.push('}');
        Ok(bindings)
    }

    /// The directory of a declared local-path input, resolved against this
    /// flake's directory. The url is a local path verbatim from source
    /// (`input_url` already rejected non-local schemes).
    fn input_flake_dir(&self, url: &str) -> PathBuf {
        self.dir.join(url)
    }

    fn outputs_source(&self) -> Result<String, FlakeError> {
        let top = parse_top_attrset(&self.src)?;
        let outputs = find_entry(&top, "outputs")
            .ok_or_else(|| FlakeError::NotAFlake("missing `outputs`".into()))?;
        Ok(outputs.syntax().text().to_string())
    }
}

/// Canonicalize a path for identity comparison (resolving `.`/`..`/symlinks). A
/// path that does not exist falls back to its lexical form, so the self-cycle
/// check never fabricates an error for an absent input — `Flake::load` reports a
/// missing input flake instead.
fn canonical(p: &Path) -> PathBuf {
    p.canonicalize().unwrap_or_else(|_| p.to_path_buf())
}

/// Escape a string for emission inside a double-quoted Nix string: backslash,
/// double-quote, and `$` (the interpolation lead) are the chars that change
/// meaning. Input names are bare identifiers in practice; escaping keeps the
/// built expression injection-proof regardless.
fn escape_nix_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        if matches!(c, '\\' | '"' | '$') {
            out.push('\\');
        }
        out.push(c);
    }
    out
}

fn parse_top_attrset(src: &str) -> Result<ast::AttrSet, FlakeError> {
    let parse = rnix::Root::parse(src);
    if !parse.errors().is_empty() {
        let msg = parse
            .errors()
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join("; ");
        return Err(FlakeError::Parse(Arc::from(msg)));
    }
    let expr = parse
        .tree()
        .expr()
        .ok_or_else(|| FlakeError::Parse("empty flake.nix".into()))?;
    match expr {
        ast::Expr::AttrSet(set) => Ok(set),
        _ => Err(FlakeError::NotAFlake(
            "top-level is not an attribute set".into(),
        )),
    }
}

fn find_entry(set: &ast::AttrSet, key: &str) -> Option<ast::Expr> {
    for entry in set.entries() {
        if let ast::Entry::AttrpathValue(apv) = entry {
            if let Some(segs) = attrpath_segments(&apv) {
                if segs.len() == 1 && segs[0].as_ref() == key {
                    return apv.value();
                }
            }
        }
    }
    None
}

fn lambda_body(outputs: &ast::Expr) -> Result<ast::Expr, FlakeError> {
    match outputs {
        ast::Expr::Lambda(lambda) => lambda
            .body()
            .ok_or_else(|| FlakeError::NotAFlake("`outputs` lambda has no body".into())),
        _ => Err(FlakeError::NotAFlake("`outputs` is not a function".into())),
    }
}

fn collect_paths(
    expr: &ast::Expr,
    prefix: &mut Vec<Arc<str>>,
    out: &mut Vec<Arc<str>>,
) -> Result<(), FlakeError> {
    match expr {
        ast::Expr::AttrSet(set) => {
            for entry in set.entries() {
                match entry {
                    ast::Entry::AttrpathValue(apv) => {
                        let segs = attrpath_segments(&apv).ok_or_else(|| {
                            FlakeError::Parse("dynamic attr key in outputs".into())
                        })?;
                        let value = apv
                            .value()
                            .ok_or_else(|| FlakeError::Parse("attr without value".into()))?;
                        let depth = prefix.len();
                        prefix.extend(segs);
                        collect_paths(&value, prefix, out)?;
                        prefix.truncate(depth);
                    }
                    // `inherit` brings names in from an outer scope; the surface
                    // walk cannot resolve them, so reject rather than drop.
                    ast::Entry::Inherit(_) => {
                        return Err(FlakeError::Parse(
                            "`inherit` in outputs is unsupported".into(),
                        ))
                    }
                }
            }
            Ok(())
        }
        _ => {
            out.push(Arc::from(join_path(prefix)));
            Ok(())
        }
    }
}

/// The single-segment `name = value` fields of a flat attribute set, in source
/// order. A multi-segment attrpath, a dynamic key, or an `inherit` is rejected:
/// each is a shape the input/url walk cannot enumerate, so it is an error rather
/// than a silently dropped or fabricated field.
fn attrset_fields(set: &ast::AttrSet) -> Result<Vec<(Arc<str>, ast::Expr)>, FlakeError> {
    let mut fields = Vec::new();
    for entry in set.entries() {
        match entry {
            ast::Entry::AttrpathValue(apv) => {
                let segs = attrpath_segments(&apv)
                    .ok_or_else(|| FlakeError::Parse("dynamic attr key in inputs".into()))?;
                let [name] = segs.as_slice() else {
                    return Err(FlakeError::NotAFlake(
                        "multi-segment attrpath in inputs".into(),
                    ));
                };
                let value = apv
                    .value()
                    .ok_or_else(|| FlakeError::Parse("attr without value".into()))?;
                fields.push((name.clone(), value));
            }
            ast::Entry::Inherit(_) => {
                return Err(FlakeError::Parse(
                    "`inherit` in inputs is unsupported".into(),
                ))
            }
        }
    }
    Ok(fields)
}

/// Extract and validate the local-path `url` of one input entry. The entry must
/// be an attribute set carrying a string-literal `url`; the path must be local
/// (no `scheme:` prefix such as `github:` or `path:`).
fn input_url(name: &str, value: &ast::Expr) -> Result<Arc<str>, FlakeError> {
    let ast::Expr::AttrSet(set) = value else {
        return Err(FlakeError::NotAFlake(
            format!("input `{name}` is not an attribute set").into(),
        ));
    };
    let url = attrset_fields(set)?
        .into_iter()
        .find(|(k, _)| k.as_ref() == "url")
        .map(|(_, v)| v)
        .ok_or_else(|| FlakeError::NotAFlake(format!("input `{name}` has no `url`").into()))?;
    let url = string_literal(&url)?.ok_or_else(|| {
        FlakeError::NotAFlake(format!("input `{name}` url is not a string").into())
    })?;
    if is_local_path(&url) {
        Ok(url)
    } else {
        Err(FlakeError::NotAFlake(
            format!("input `{name}` url `{url}` is not a local path").into(),
        ))
    }
}

/// The literal text of a string expression, or `None` if it is not a string.
/// A `${...}` interpolation makes the value non-static: that is a parse error
/// (it cannot be enumerated without evaluation), never a fabricated partial.
fn string_literal(expr: &ast::Expr) -> Result<Option<Arc<str>>, FlakeError> {
    let ast::Expr::Str(s) = expr else {
        return Ok(None);
    };
    let mut out = String::new();
    for part in s.normalized_parts() {
        match part {
            ast::InterpolPart::Literal(l) => out.push_str(&l),
            ast::InterpolPart::Interpolation(_) => {
                return Err(FlakeError::Parse("dynamic (`${...}`) input url".into()))
            }
        }
    }
    Ok(Some(Arc::from(out.as_str())))
}

/// Whether a url is a local path (our only supported input kind): no leading
/// `scheme:` segment (e.g. `github:`, `path:`, `git+https:`). A relative path
/// like `.`, `./vendor/dep`, or `../sibling` qualifies; a Nix path containing a
/// `/` before any `:` is local. The check rejects a leading run of url-scheme
/// characters followed by `:`.
fn is_local_path(url: &str) -> bool {
    match url.find(':') {
        None => true,
        Some(i) => {
            let scheme = &url[..i];
            !scheme
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '+' || c == '-' || c == '.')
                || scheme.is_empty()
        }
    }
}

fn attrpath_segments(apv: &ast::AttrpathValue) -> Option<Vec<Arc<str>>> {
    let ap = apv.attrpath()?;
    let mut segs = Vec::new();
    for attr in ap.attrs() {
        match attr {
            ast::Attr::Ident(i) => segs.push(Arc::from(i.ident_token()?.text())),
            ast::Attr::Str(s) => {
                // A `${...}` part makes the key dynamic: it cannot be enumerated
                // statically, so signal "not a static path" rather than fabricate
                // an empty / partial segment from the literal parts alone.
                let mut r = String::new();
                for part in s.normalized_parts() {
                    match part {
                        ast::InterpolPart::Literal(l) => r.push_str(&l),
                        ast::InterpolPart::Interpolation(_) => return None,
                    }
                }
                segs.push(Arc::from(r.as_str()));
            }
            _ => return None,
        }
    }
    Some(segs)
}

fn join_path(segs: &[Arc<str>]) -> String {
    segs.iter()
        .map(|s| s.as_ref())
        .collect::<Vec<_>>()
        .join(".")
}

/// Validate an attr path and re-emit it as a quoted Nix selector
/// (`"seg"."seg"...`). Each segment must match `[A-Za-z_][A-Za-z0-9_'-]*`;
/// anything else (empty, or containing `.` `;` `}` `"` whitespace, etc.) yields
/// `None`. Quoting each validated segment means no path text is ever spliced
/// into the evaluator as live syntax — closing the Nix-source injection seam.
fn quoted_selector(path: &str) -> Option<String> {
    if path.is_empty() {
        return None;
    }
    let mut out = String::new();
    for (i, seg) in path.split('.').enumerate() {
        if !is_valid_attr_segment(seg) {
            return None;
        }
        if i > 0 {
            out.push('.');
        }
        out.push('"');
        out.push_str(seg);
        out.push('"');
    }
    Some(out)
}

/// A bare Nix identifier segment: leading `[A-Za-z_]`, then `[A-Za-z0-9_'-]*`.
fn is_valid_attr_segment(seg: &str) -> bool {
    let mut chars = seg.chars();
    match chars.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' => {}
        _ => return false,
    }
    chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '\'' || c == '-')
}
