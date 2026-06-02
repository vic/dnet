use crate::error::DrvError;
use dnx_core::prim::PrimValue;
use dnx_store::{Store, StorePath};
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

/// The fixed base `PATH` every builder runs with, so a build that calls a
/// bare command name resolves the same way regardless of the host shell.
const DEFAULT_PATH: &str = "/usr/bin:/bin";

/// A `builder` with this prefix names an in-process builtin builder rather than
/// an external program. Mirrors cppNix's `builtin:` URI scheme (e.g.
/// `builtin:fetchurl`). Builtins run inside this process: no `/bin/sh`, no
/// coreutils, no host PATH — fully deterministic in any environment.
const BUILTIN_PREFIX: &str = "builtin:";

/// A Dnx derivation: our own flat, input-addressed build description.
///
/// Not the cppNix ATerm `.drv` format — a plain typed struct serialized to the
/// store as our own bytes. `env` is a `BTreeMap` so its serialization is
/// canonical (sorted keys), which keeps `instantiate` deterministic.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Derivation {
    pub name: Arc<str>,
    pub builder: Arc<str>,
    pub args: Vec<Arc<str>>,
    pub env: BTreeMap<Arc<str>, Arc<str>>,
    pub input_srcs: Vec<StorePath>,
    pub outputs: Vec<Arc<str>>,
}

impl Derivation {
    /// Serialize the derivation deterministically: fixed field order,
    /// length-prefixed fields, sorted `env` (the `BTreeMap` guarantees order).
    /// Same derivation in → same bytes out → same drvPath. This is the wire
    /// form `dnx-daemon` ships in a `Build` request (`dnx-daemon-design.md`
    /// §2.4); `from_bytes` is its inverse.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        push_str(&mut buf, &self.name);
        push_str(&mut buf, &self.builder);
        push_seq(&mut buf, self.args.iter().map(|a| a.as_bytes()));
        push_len(&mut buf, self.env.len());
        for (k, v) in &self.env {
            push_str(&mut buf, k);
            push_str(&mut buf, v);
        }
        let mut srcs: Vec<&StorePath> = self.input_srcs.iter().collect();
        srcs.sort_by(|a, b| a.hash().cmp(b.hash()).then_with(|| a.name().cmp(b.name())));
        push_len(&mut buf, srcs.len());
        for p in &srcs {
            push_len(&mut buf, p.hash().as_slice().len());
            buf.extend_from_slice(p.hash().as_slice());
            push_str(&mut buf, p.name());
        }
        push_seq(&mut buf, self.outputs.iter().map(|o| o.as_bytes()));
        buf
    }

    /// Parse the `to_bytes` encoding back into a `Derivation` — the inverse the
    /// daemon uses to decode a `Build` request's opaque `.drv` bytes
    /// (`dnx-daemon-design.md` §2.4 "the daemon decodes with `dnx-drv`'s own
    /// decoder, the single source of that shape"). Every read is bounds-checked
    /// against the input, so truncated or over-long bytes yield a typed
    /// `DrvError::Decode`, never a panic.
    ///
    /// `to_bytes` emits `input_srcs` in canonical (hash, name)-sorted order, so
    /// `from_bytes` is exact on that canonical form: `to_bytes(from_bytes(b)) ==
    /// b` for any `b` produced by `to_bytes`, and `from_bytes(to_bytes(d)) == d`
    /// whenever `d`'s `input_srcs` are already in canonical order.
    pub fn from_bytes(bytes: &[u8]) -> Result<Derivation, DrvError> {
        let mut r = Reader::new(bytes);
        let name = r.str()?;
        let builder = r.str()?;
        let args = r.seq()?;
        let env_len = r.len()?;
        let mut env = BTreeMap::new();
        for _ in 0..env_len {
            let k = r.str()?;
            let v = r.str()?;
            env.insert(k, v);
        }
        let srcs_len = r.len()?;
        // `srcs_len` is attacker-controlled (from the wire). NEVER pre-reserve
        // from it — a tiny frame claiming a vast count would abort the
        // allocator. Grow on demand: each `r.hash()`/`r.str()` consumes real
        // bytes, so a bogus count runs out of input at once and errors having
        // allocated ~nothing (mirrors dnx-core blob.rs `deserialize`).
        let mut input_srcs = Vec::new();
        for _ in 0..srcs_len {
            let hash = r.hash()?;
            let name = r.str()?;
            input_srcs
                .push(StorePath::new(hash, &name).map_err(|e| DrvError::Decode(e.to_string()))?);
        }
        let outputs = r.seq()?;
        r.finish()?;
        Ok(Derivation {
            name,
            builder,
            args,
            env,
            input_srcs,
            outputs,
        })
    }

    /// Instantiate: store the serialized description, returning its drvPath.
    /// Pure — no builder runs. Deterministic by construction.
    pub fn instantiate(&self, store: &Store) -> Result<StorePath, DrvError> {
        let name = format!("{}.drv", self.name);
        Ok(store.add(&name, &self.to_bytes())?)
    }

    /// Realize: run the builder in a userland temp dir with `env`/`args` and a
    /// `$<output>` variable per output, then capture each produced path into the
    /// store. Returns the realised output paths keyed by output name.
    pub fn realize(&self, store: &Store) -> Result<BTreeMap<String, StorePath>, DrvError> {
        let temp = self.make_temp_dir()?;
        let result = self.realize_in(store, &temp);
        let _ = std::fs::remove_dir_all(&temp);
        result
    }

    /// Run the builder in `temp` and capture its outputs. The caller owns
    /// `temp` and removes it on every path, so this body may fail freely
    /// without leaking the build directory.
    fn realize_in(
        &self,
        store: &Store,
        temp: &std::path::Path,
    ) -> Result<BTreeMap<String, StorePath>, DrvError> {
        let mut out_vars: Vec<(Arc<str>, PathBuf)> = Vec::with_capacity(self.outputs.len());
        for out in &self.outputs {
            out_vars.push((out.clone(), temp.join(out.as_ref())));
        }

        // Either run an in-process builtin or spawn the external builder; both
        // leave their results at the `$<output>` paths under `temp`.
        match self.builder.strip_prefix(BUILTIN_PREFIX) {
            Some(name) => self.run_builtin(store, name, &out_vars)?,
            None => self.run_external(temp, &out_vars)?,
        }

        let mut results = BTreeMap::new();
        for (out, path) in &out_vars {
            let meta = std::fs::symlink_metadata(path)
                .map_err(|_| DrvError::MissingOutput(out.clone()))?;
            if meta.file_type().is_symlink() {
                return Err(DrvError::OutputSymlink(out.clone()));
            }
            let stored = if meta.is_dir() {
                store.add_tree(out, path)?
            } else {
                let bytes = std::fs::read(path).map_err(DrvError::Spawn)?;
                store.add(out, &bytes)?
            };
            results.insert(out.to_string(), stored);
        }
        Ok(results)
    }

    /// Spawn the external builder in `temp` with a minimal fixed environment: a
    /// default PATH, then the derivation's own `env` (which may override PATH),
    /// then the reserved `$<output>` vars last so they always win. Nothing else
    /// from the host leaks in (`env_clear`), keeping builds host-independent.
    fn run_external(
        &self,
        temp: &std::path::Path,
        out_vars: &[(Arc<str>, PathBuf)],
    ) -> Result<(), DrvError> {
        let status = Command::new(self.builder.as_ref())
            .args(self.args.iter().map(|a| a.as_ref()))
            .env_clear()
            .env("PATH", DEFAULT_PATH)
            .envs(self.env.iter().map(|(k, v)| (k.as_ref(), v.as_ref())))
            .envs(out_vars.iter().map(|(k, p)| (k.as_ref(), p.as_os_str())))
            .current_dir(temp)
            .status()
            .map_err(DrvError::Spawn)?;
        if status.success() {
            Ok(())
        } else {
            Err(DrvError::Build {
                code: status.code(),
            })
        }
    }

    /// Run an in-process builtin builder, writing each output file directly.
    /// No external process runs, so the result is byte-identical on every host.
    ///
    /// `builtin:write` writes the `text` env var to every output. It is the
    /// deterministic demo builder: a derivation needs only string attrs
    /// (`name`, `builder`, `text`) — no list-valued `args` — so it round-trips
    /// cleanly from surface Nix.
    ///
    /// `builtin:concat` writes the concatenated bytes of every `input_srcs`
    /// path to every output, joining them in the same canonical (hash, name)
    /// order `to_bytes` serializes (so the result is independent of insertion
    /// order). Each input's content is itself content-addressed, so the output
    /// is a pure function of the inputs — the smallest real "combine sources"
    /// build, with no env, no process, and no host dependence.
    ///
    /// `builtin:json` writes the derivation's `env` to every output as a
    /// canonical JSON object: keys in sorted order (the `BTreeMap` guarantees
    /// it) and every value a JSON string, escaped per RFC 8259. Pure and
    /// in-process, so the output is a deterministic function of the attrs.
    fn run_builtin(
        &self,
        store: &Store,
        name: &str,
        out_vars: &[(Arc<str>, PathBuf)],
    ) -> Result<(), DrvError> {
        match name {
            "write" => {
                let text = self.env.get("text").ok_or_else(|| {
                    DrvError::BadAttrs("builtin:write requires a string `text` attr".into())
                })?;
                self.write_outputs(out_vars, text.as_bytes())
            }
            "concat" => {
                let mut srcs: Vec<&StorePath> = self.input_srcs.iter().collect();
                srcs.sort_by(|a, b| a.hash().cmp(b.hash()).then_with(|| a.name().cmp(b.name())));
                let mut joined = Vec::new();
                for p in srcs {
                    let bytes = store
                        .get(p)?
                        .ok_or_else(|| DrvError::MissingInput(p.clone()))?;
                    joined.extend_from_slice(&bytes);
                }
                self.write_outputs(out_vars, &joined)
            }
            "json" => self.write_outputs(out_vars, json_object(&self.env).as_bytes()),
            other => Err(DrvError::UnknownBuiltin(Arc::from(other))),
        }
    }

    /// Write the same bytes to every `$<output>` path. Shared by the builtins,
    /// which differ only in how they compute those bytes.
    fn write_outputs(
        &self,
        out_vars: &[(Arc<str>, PathBuf)],
        bytes: &[u8],
    ) -> Result<(), DrvError> {
        for (_out, path) in out_vars {
            std::fs::write(path, bytes).map_err(DrvError::Spawn)?;
        }
        Ok(())
    }

    /// Create a fresh userland build directory under the system temp dir.
    /// Uniqueness comes from the process id plus a monotonic counter — the
    /// directory is ephemeral, so its name need not be content-addressed.
    fn make_temp_dir(&self) -> Result<PathBuf, DrvError> {
        if !is_plain_name(&self.name) {
            return Err(DrvError::BadAttrs(format!(
                "name {:?} must be a single normal path component",
                self.name
            )));
        }
        static CTR: AtomicU64 = AtomicU64::new(0);
        let n = CTR.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!(
            "dnx-build-{}-{}-{}",
            std::process::id(),
            n,
            self.name
        ));
        std::fs::create_dir_all(&dir).map_err(DrvError::Spawn)?;
        Ok(dir)
    }
}

/// A name is usable as a store name and a temp-dir component only if it is a
/// single ordinary path component — no `/`, no `.`/`..`, no root or prefix.
/// This is the `StorePath` name rule tightened to forbid traversal.
fn is_plain_name(name: &str) -> bool {
    let mut comps = std::path::Path::new(name).components();
    matches!(
        (comps.next(), comps.next()),
        (Some(std::path::Component::Normal(c)), None) if c == std::ffi::OsStr::new(name)
    )
}

/// Serialize a string→string map as a canonical JSON object: `{` then each
/// `"key":"value"` in the map's (already sorted) order separated by `,` then
/// `}`. A `BTreeMap` iterates in key order, so the bytes are deterministic.
fn json_object(map: &BTreeMap<Arc<str>, Arc<str>>) -> String {
    let mut s = String::from("{");
    for (i, (k, v)) in map.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        push_json_str(&mut s, k);
        s.push(':');
        push_json_str(&mut s, v);
    }
    s.push('}');
    s
}

/// Append `s` as a JSON string literal, escaping per RFC 8259 §7: `"` and `\`
/// are backslash-escaped, the named control characters use their short escape,
/// and any remaining control character below U+0020 uses a `\u00XX` escape.
fn push_json_str(out: &mut String, s: &str) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{08}' => out.push_str("\\b"),
            '\u{0c}' => out.push_str("\\f"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

fn push_len(buf: &mut Vec<u8>, n: usize) {
    buf.extend_from_slice(&(n as u64).to_le_bytes());
}

fn push_str(buf: &mut Vec<u8>, s: &str) {
    push_len(buf, s.len());
    buf.extend_from_slice(s.as_bytes());
}

fn push_seq<'a>(buf: &mut Vec<u8>, items: impl ExactSizeIterator<Item = &'a [u8]>) {
    push_len(buf, items.len());
    for it in items {
        push_len(buf, it.len());
        buf.extend_from_slice(it);
    }
}

/// A bounds-checked cursor over `to_bytes` output: the exact inverse of the
/// `push_*` writers. Every take is validated against the remaining bytes, so a
/// short or over-long encoding is a typed `DrvError::Decode`, never a panic or
/// out-of-bounds read.
struct Reader<'a> {
    buf: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn new(buf: &'a [u8]) -> Self {
        Reader { buf, at: 0 }
    }

    fn take(&mut self, n: usize) -> Result<&'a [u8], DrvError> {
        let end = self
            .at
            .checked_add(n)
            .ok_or_else(|| DrvError::Decode("length overflow".into()))?;
        if end > self.buf.len() {
            return Err(DrvError::Decode("unexpected end of input".into()));
        }
        let s = &self.buf[self.at..end];
        self.at = end;
        Ok(s)
    }

    /// Read a `push_len` field: a little-endian `u64` count, narrowed to a
    /// `usize` (rejected if it cannot fit, so a 64-bit length on a 32-bit host
    /// errors rather than truncating).
    fn len(&mut self) -> Result<usize, DrvError> {
        let s = self.take(8)?;
        let n = u64::from_le_bytes([s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]]);
        usize::try_from(n).map_err(|_| DrvError::Decode("length exceeds usize".into()))
    }

    /// Read a `push_str` field: a length-prefixed UTF-8 string.
    fn str(&mut self) -> Result<Arc<str>, DrvError> {
        let n = self.len()?;
        let s = self.take(n)?;
        std::str::from_utf8(s)
            .map(Arc::from)
            .map_err(|_| DrvError::Decode("invalid utf-8".into()))
    }

    /// Read a `push_seq` field: a count then that many length-prefixed strings.
    fn seq(&mut self) -> Result<Vec<Arc<str>>, DrvError> {
        // `n` is attacker-controlled, so it sizes the loop only — never the
        // allocation. `Vec::new` + push grows on demand; each `str()` consumes
        // real bytes, so a bogus `n` exhausts the input immediately and yields
        // `Err` having allocated ~nothing (no memory-amplification DoS).
        let n = self.len()?;
        let mut out = Vec::new();
        for _ in 0..n {
            out.push(self.str()?);
        }
        Ok(out)
    }

    /// Read a stored hash: a `push_len` that must equal 32, then the 32 bytes.
    fn hash(&mut self) -> Result<[u8; 32], DrvError> {
        let n = self.len()?;
        if n != 32 {
            return Err(DrvError::Decode("hash length is not 32".into()));
        }
        let s = self.take(32)?;
        let mut h = [0u8; 32];
        h.copy_from_slice(s);
        Ok(h)
    }

    /// The whole input must be exactly consumed — trailing bytes are malformed.
    fn finish(self) -> Result<(), DrvError> {
        if self.at == self.buf.len() {
            Ok(())
        } else {
            Err(DrvError::Decode("trailing bytes".into()))
        }
    }
}

/// Lift an evaluated `derivationStrict` attrset into a typed `Derivation`.
///
/// The attrset is the flat form fed to `derivationStrict`
/// (`{ name; builder; args; system; outputs; ... }`); extra keys become build
/// environment variables. This conversion lives here (not in `dnx-lang`)
/// to keep the crate dependency one-directional.
pub fn from_attrs(attrs: &[(Arc<str>, PrimValue)]) -> Result<Derivation, DrvError> {
    let name = require_str(attrs, "name")?;
    if !is_plain_name(&name) {
        return Err(DrvError::BadAttrs(format!(
            "name {name:?} must be a single normal path component"
        )));
    }
    let builder = require_str(attrs, "builder")?;
    let args = match find(attrs, "args") {
        Some(PrimValue::List(xs)) => xs
            .iter()
            .map(as_str)
            .collect::<Result<Vec<_>, _>>()
            .map_err(|_| DrvError::BadAttrs("args must be a list of strings".into()))?,
        Some(_) => return Err(DrvError::BadAttrs("args must be a list".into())),
        None => Vec::new(),
    };
    let outputs = match find(attrs, "outputs") {
        Some(PrimValue::List(xs)) => xs
            .iter()
            .map(as_str)
            .collect::<Result<Vec<_>, _>>()
            .map_err(|_| DrvError::BadAttrs("outputs must be a list of strings".into()))?,
        Some(_) => return Err(DrvError::BadAttrs("outputs must be a list".into())),
        None => vec![Arc::from("out")],
    };

    let mut env = BTreeMap::new();
    for (k, v) in attrs {
        if matches!(k.as_ref(), "args" | "outputs") {
            continue;
        }
        if let Ok(s) = as_str(v) {
            env.insert(k.clone(), s);
        }
    }

    // An output name doubles as the `$<output>` build variable, so it must not
    // also be an explicit env key — that would make the variable ambiguous.
    for out in &outputs {
        if env.contains_key(out) {
            return Err(DrvError::BadAttrs(format!(
                "output {out:?} collides with an environment key"
            )));
        }
    }

    Ok(Derivation {
        name,
        builder,
        args,
        env,
        input_srcs: Vec::new(),
        outputs,
    })
}

fn find<'a>(attrs: &'a [(Arc<str>, PrimValue)], key: &str) -> Option<&'a PrimValue> {
    attrs
        .iter()
        .find(|(k, _)| k.as_ref() == key)
        .map(|(_, v)| v)
}

fn as_str(v: &PrimValue) -> Result<Arc<str>, ()> {
    match v {
        PrimValue::Str(s) => Ok(s.clone()),
        PrimValue::Path(p) => Ok(p.clone()),
        _ => Err(()),
    }
}

fn require_str(attrs: &[(Arc<str>, PrimValue)], key: &str) -> Result<Arc<str>, DrvError> {
    match find(attrs, key) {
        Some(v) => as_str(v).map_err(|_| DrvError::BadAttrs(format!("{key} must be a string"))),
        None => Err(DrvError::BadAttrs(format!("missing required attr {key:?}"))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A derivation exercising every field: name, builder, args, a sorted
    /// `env`, two `input_srcs` already in canonical (hash, name) order, and
    /// multiple outputs.
    fn rich() -> Derivation {
        let mut env = BTreeMap::new();
        env.insert(Arc::from("system"), Arc::from("x86_64-linux"));
        env.insert(Arc::from("text"), Arc::from("hello dnx"));
        Derivation {
            name: Arc::from("rich"),
            builder: Arc::from("builtin:write"),
            args: vec![Arc::from("-c"), Arc::from("echo hi")],
            env,
            input_srcs: vec![
                StorePath::new([1u8; 32], "alpha").expect("path a"),
                StorePath::new([2u8; 32], "beta").expect("path b"),
            ],
            outputs: vec![Arc::from("out"), Arc::from("dev")],
        }
    }

    #[test]
    fn from_bytes_inverts_to_bytes() {
        let d = rich();
        let decoded = Derivation::from_bytes(&d.to_bytes()).expect("decode");
        assert_eq!(decoded, d, "to_bytes → from_bytes is the identity");
    }

    #[test]
    fn roundtrip_is_a_byte_bijection() {
        let bytes = rich().to_bytes();
        let again = Derivation::from_bytes(&bytes).expect("decode").to_bytes();
        assert_eq!(
            again, bytes,
            "from_bytes → to_bytes recovers the exact bytes"
        );
    }

    #[test]
    fn empty_collections_roundtrip() {
        let d = Derivation {
            name: Arc::from("bare"),
            builder: Arc::from("/bin/sh"),
            args: Vec::new(),
            env: BTreeMap::new(),
            input_srcs: Vec::new(),
            outputs: vec![Arc::from("out")],
        };
        assert_eq!(Derivation::from_bytes(&d.to_bytes()).expect("decode"), d);
    }

    #[test]
    fn truncated_input_is_a_typed_error() {
        // Every prefix of a valid encoding that stops mid-field must be a typed
        // Decode error, never a panic or out-of-bounds read.
        let bytes = rich().to_bytes();
        for cut in 0..bytes.len() {
            assert!(
                matches!(
                    Derivation::from_bytes(&bytes[..cut]),
                    Err(DrvError::Decode(_))
                ),
                "a {cut}-byte prefix must be a Decode error"
            );
        }
    }

    #[test]
    fn trailing_bytes_are_rejected() {
        let mut bytes = rich().to_bytes();
        bytes.push(0xff);
        assert!(matches!(
            Derivation::from_bytes(&bytes),
            Err(DrvError::Decode(_))
        ));
    }

    // ── adversarial: untrusted-wire memory-amplification DoS ─────────────────
    // Mirrors `dnx-core` blob.rs `huge_record_count_no_amplification`. A tiny
    // frame whose length prefix claims a vast element count must NOT pre-size a
    // buffer from that unvalidated `n`: it must run out of real bytes at the
    // first element and return `Err(Decode)`, allocating ~nothing. Reachable
    // remotely via the daemon's `Build` payload (`server.rs` `build_wire` →
    // `from_bytes`), so a ~13-byte frame must never trigger an allocator abort.

    #[test]
    fn huge_seq_count_no_amplification() {
        // name="" builder="" then args (a `seq`) claims u64::MAX elements but
        // the frame ends. The old `Vec::with_capacity(n)` in `seq` would try to
        // reserve usize::MAX strings and abort the process. 24 bytes total.
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&0u64.to_le_bytes()); // name len 0
        bytes.extend_from_slice(&0u64.to_le_bytes()); // builder len 0
        bytes.extend_from_slice(&u64::MAX.to_le_bytes()); // args count = MAX
        assert!(
            matches!(Derivation::from_bytes(&bytes), Err(DrvError::Decode(_))),
            "a tiny frame claiming a vast seq count must be a typed Decode error"
        );
    }

    #[test]
    fn huge_srcs_count_no_amplification() {
        // Reach `input_srcs` cheaply (empty name/builder/args/env) then claim
        // u64::MAX sources. The old `Vec::with_capacity(srcs_len)` would reserve
        // usize::MAX `StorePath`s and abort. 40 bytes total.
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&0u64.to_le_bytes()); // name len 0
        bytes.extend_from_slice(&0u64.to_le_bytes()); // builder len 0
        bytes.extend_from_slice(&0u64.to_le_bytes()); // args count 0
        bytes.extend_from_slice(&0u64.to_le_bytes()); // env count 0
        bytes.extend_from_slice(&u64::MAX.to_le_bytes()); // srcs count = MAX
        assert!(
            matches!(Derivation::from_bytes(&bytes), Err(DrvError::Decode(_))),
            "a tiny frame claiming a vast srcs count must be a typed Decode error"
        );
    }
}
