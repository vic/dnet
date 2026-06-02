#![forbid(unsafe_code)]

//! The `dnx` daemon seam: a `Builder` trait with a daemonless `LocalBuilder`
//! stub and a socket-backed `DaemonBuilder`, plus a long-lived server that
//! holds a warm in-memory result cache and serializes concurrent builds so two
//! clients asking for the SAME derivation build it ONCE ("compute once, serve
//! many"). See `vic/plans/dnx-daemon-design.md` (Milestone M1).
//!
//! Design law: the daemon adds only the *serialize + socket* seam. Identity,
//! hashing and canonicity stay in the layers below (`dnx-store`,
//! `dnx-drv`, `dnx-dist`, `dnx-core`); the daemon re-derives no identity.

mod proto;
mod server;

use std::path::{Path, PathBuf};

use dnx_core::Blake3Hash;
use dnx_drv::{Derivation, DrvError};
use dnx_store::{Store, StoreError, StorePath};

pub use proto::PROTO_VERSION;
pub use server::{daemon_status, ping, serve, Daemon, DaemonStatus, Realizer, Shutdown};

/// The build seam (arch §7): a daemonless `LocalBuilder` and a socket-backed
/// `DaemonBuilder` are interchangeable behind this one trait, so a call site
/// (`dnx build`) is identical whether or not a daemon is running.
pub trait Builder {
    /// Realize `drv`, returning its output store path. `LocalBuilder` realizes
    /// inline; `DaemonBuilder` round-trips the request to a running daemon
    /// whose single worker dedups in-flight builds of the same derivation.
    fn enqueue(&self, drv: Derivation) -> Result<StorePath, DaemonError>;

    /// Whether a content hash is already a registered store member (the
    /// store-path registration query, J3).
    fn registered(&self, hash: &Blake3Hash) -> bool;
}

/// Daemonless build: realize a derivation inline against a local store.
/// This is the demo default — `dnx build` works with no daemon at all.
pub struct LocalBuilder {
    store: Store,
}

impl LocalBuilder {
    pub fn new(store: Store) -> Self {
        LocalBuilder { store }
    }

    /// The shared realize-then-select step: run the builder and return the
    /// derivation's primary output path. Used by both `LocalBuilder` and the
    /// daemon worker so there is exactly one realize implementation.
    pub(crate) fn realize_primary(
        store: &Store,
        drv: &Derivation,
    ) -> Result<StorePath, DaemonError> {
        let outs = drv.realize(store)?;
        primary_output(drv, outs).ok_or(DaemonError::NoOutput)
    }
}

impl Builder for LocalBuilder {
    fn enqueue(&self, drv: Derivation) -> Result<StorePath, DaemonError> {
        LocalBuilder::realize_primary(&self.store, &drv)
    }

    fn registered(&self, hash: &Blake3Hash) -> bool {
        store_has_hash(&self.store, hash)
    }
}

/// Socket-backed build: forward each request to a running daemon over the
/// length-prefixed protocol (§2). The daemon's worker is the cross-client lock
/// that makes two identical builds realize once.
pub struct DaemonBuilder {
    sock: PathBuf,
}

impl DaemonBuilder {
    pub fn new(sock: impl Into<PathBuf>) -> Self {
        DaemonBuilder { sock: sock.into() }
    }

    /// The socket path this builder talks to.
    pub fn sock(&self) -> &Path {
        &self.sock
    }

    /// Membership query over the wire (J3): `StoreQuery{hash}` → `StorePresent`.
    pub fn store_query(&self, hash: &Blake3Hash) -> Result<bool, DaemonError> {
        match server::request(&self.sock, proto::Request::StoreQuery(*hash))? {
            proto::Response::StorePresent(p) => Ok(p),
            proto::Response::Failed(k, d) => Err(DaemonError::from_kind(k, d)),
            _ => Err(DaemonError::BadTag),
        }
    }
}

impl Builder for DaemonBuilder {
    fn enqueue(&self, drv: Derivation) -> Result<StorePath, DaemonError> {
        // Build-over-the-wire ships the instantiated `.drv` bytes (`to_bytes`),
        // which the daemon decodes with `dnx-drv`'s own `from_bytes` (design
        // §2.4) and realizes through its one cross-client-deduping worker, so
        // two identical builds realize once. The reply is the output path.
        match server::request(&self.sock, proto::Request::Build(drv.to_bytes()))? {
            proto::Response::Built(p) => Ok(p),
            proto::Response::Failed(k, d) => Err(DaemonError::from_kind(k, d)),
            _ => Err(DaemonError::BadTag),
        }
    }

    fn registered(&self, hash: &Blake3Hash) -> bool {
        self.store_query(hash).unwrap_or(false)
    }
}

/// The per-user socket path (no root, userland): `$XDG_RUNTIME_DIR/dnx/dnx.sock`
/// when the runtime dir is set (its correct per-login home, auto-cleaned), else
/// the arch default `$DNX_STORE/daemon.sock`, else `./dnx.sock` as a last
/// resort. Both primary paths are well under the AF_UNIX length cap.
pub fn default_socket() -> PathBuf {
    if let Some(dir) = std::env::var_os("XDG_RUNTIME_DIR") {
        return PathBuf::from(dir).join("dnx").join("dnx.sock");
    }
    if let Some(dir) = std::env::var_os("DNX_STORE") {
        return PathBuf::from(dir).join("daemon.sock");
    }
    PathBuf::from("dnx.sock")
}

/// Serve-path client (J4): look up a result blob by content hash over the
/// wire. `Ok(Some(blob))` on a warm-cache hit (the client `from_blob`s it with
/// NO `normalize`), `Ok(None)` on a miss.
pub fn client_cache_lookup(sock: &Path, hash: &Blake3Hash) -> Result<Option<Vec<u8>>, DaemonError> {
    match server::request(sock, proto::Request::CacheLookup(*hash))? {
        proto::Response::CacheHit(blob) => Ok(Some(blob)),
        proto::Response::CacheMiss => Ok(None),
        proto::Response::Failed(k, d) => Err(DaemonError::from_kind(k, d)),
        _ => Err(DaemonError::BadTag),
    }
}

/// Ask a running daemon to drain and exit (lifecycle: `dnx daemon stop`).
pub fn client_shutdown(sock: &Path) -> Result<(), DaemonError> {
    match server::request(sock, proto::Request::Shutdown)? {
        proto::Response::Pong { .. } => Ok(()),
        proto::Response::Failed(k, d) => Err(DaemonError::from_kind(k, d)),
        _ => Err(DaemonError::BadTag),
    }
}

/// Pick a derivation's primary output: the conventional `out`, else the first
/// declared output. `None` only if the derivation declares no outputs (which
/// `from_attrs` never produces — it defaults to `["out"]`).
fn primary_output(
    drv: &Derivation,
    mut outs: std::collections::BTreeMap<String, StorePath>,
) -> Option<StorePath> {
    if let Some(p) = outs.remove("out") {
        return Some(p);
    }
    drv.outputs
        .first()
        .and_then(|name| outs.remove(name.as_ref()))
}

/// Hash-only membership over a `Store` whose filenames are `<hex>-<name>`
/// (the name is part of the on-disk path, but a peer asking "do you have this
/// hash?" knows only the hash). Scan the root for a `<hex>-` prefix match; the
/// hex is fixed-width 64 (`path.rs`), so the prefix is unambiguous.
///
/// This is the design's recommended resolution of the `StoreQuery{hash}` vs
/// `Store::has(&StorePath)` gap (§8.5.2a option 1), kept inside the daemon so
/// `dnx-store`'s API is unchanged.
fn store_has_hash(store: &Store, hash: &Blake3Hash) -> bool {
    let mut hex = String::with_capacity(64 + 1);
    for byte in hash {
        use std::fmt::Write;
        if write!(hex, "{byte:02x}").is_err() {
            return false;
        }
    }
    hex.push('-');
    let entries = match std::fs::read_dir(store.root()) {
        Ok(e) => e,
        Err(_) => return false,
    };
    entries.filter_map(Result::ok).any(|e| {
        e.file_name()
            .to_str()
            .is_some_and(|name| name.starts_with(&hex))
    })
}

/// Daemon-layer errors. Typed, never stringly; every fallible path propagates
/// a `Result` (no `unwrap`/`panic`). String detail on `Protocol` is human text
/// for stderr, never load-bearing — clients branch on the variant.
#[derive(Debug)]
pub enum DaemonError {
    /// Socket / framing I/O failure.
    Io(std::io::Error),
    /// A frame's length prefix exceeded `MAX_FRAME` (a hostile-client guard).
    FrameTooLarge,
    /// A byte stream did not parse into a known request/response tag.
    BadTag,
    /// A frame parsed but its body was short, over-long, or otherwise malformed.
    Protocol(String),
    /// An underlying build (realize) failed.
    Build(DrvError),
    /// An underlying store operation failed.
    Store(StoreError),
    /// A realized derivation produced no selectable output path.
    NoOutput,
    /// No daemon answered at the socket.
    NotRunning,
}

/// The closed, `#[repr(u8)]` cause carried by a `Failed` response, so a typed
/// error round-trips the wire (never a stringly error).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum DaemonErrorKind {
    Io = 0,
    FrameTooLarge = 1,
    BadTag = 2,
    Build = 3,
    NotFound = 4,
    Protocol = 5,
    HashMismatch = 6,
}

impl DaemonErrorKind {
    /// Parse a wire byte into a kind (invalid-state-unrepresentable: an
    /// unknown discriminant is a `BadTag`, never a silent default).
    pub(crate) fn from_u8(b: u8) -> Option<Self> {
        Some(match b {
            0 => DaemonErrorKind::Io,
            1 => DaemonErrorKind::FrameTooLarge,
            2 => DaemonErrorKind::BadTag,
            3 => DaemonErrorKind::Build,
            4 => DaemonErrorKind::NotFound,
            5 => DaemonErrorKind::Protocol,
            6 => DaemonErrorKind::HashMismatch,
            _ => return None,
        })
    }
}

impl DaemonError {
    /// The wire kind for this error (the `Failed` discriminant).
    pub(crate) fn kind(&self) -> DaemonErrorKind {
        match self {
            DaemonError::Io(_) => DaemonErrorKind::Io,
            DaemonError::FrameTooLarge => DaemonErrorKind::FrameTooLarge,
            DaemonError::BadTag => DaemonErrorKind::BadTag,
            DaemonError::Protocol(_) => DaemonErrorKind::Protocol,
            DaemonError::Build(_) => DaemonErrorKind::Build,
            DaemonError::Store(_) => DaemonErrorKind::Io,
            DaemonError::NoOutput => DaemonErrorKind::NotFound,
            DaemonError::NotRunning => DaemonErrorKind::Io,
        }
    }

    /// Reconstruct an error from a received `Failed{kind, detail}`.
    pub(crate) fn from_kind(kind: DaemonErrorKind, detail: String) -> Self {
        match kind {
            DaemonErrorKind::FrameTooLarge => DaemonError::FrameTooLarge,
            DaemonErrorKind::BadTag => DaemonError::BadTag,
            DaemonErrorKind::NotFound => DaemonError::NoOutput,
            DaemonErrorKind::HashMismatch => DaemonError::Protocol(detail),
            DaemonErrorKind::Build => DaemonError::Protocol(detail),
            DaemonErrorKind::Protocol => DaemonError::Protocol(detail),
            DaemonErrorKind::Io => DaemonError::Protocol(detail),
        }
    }
}

impl std::fmt::Display for DaemonError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DaemonError::Io(e) => write!(f, "daemon io: {e}"),
            DaemonError::FrameTooLarge => write!(f, "frame exceeds MAX_FRAME"),
            DaemonError::BadTag => write!(f, "unknown protocol tag"),
            DaemonError::Protocol(m) => write!(f, "protocol: {m}"),
            DaemonError::Build(e) => write!(f, "build: {e}"),
            DaemonError::Store(e) => write!(f, "store: {e}"),
            DaemonError::NoOutput => write!(f, "derivation produced no output"),
            DaemonError::NotRunning => write!(f, "no daemon at socket"),
        }
    }
}

impl std::error::Error for DaemonError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            DaemonError::Io(e) => Some(e),
            DaemonError::Build(e) => Some(e),
            DaemonError::Store(e) => Some(e),
            _ => None,
        }
    }
}

impl From<std::io::Error> for DaemonError {
    fn from(e: std::io::Error) -> Self {
        DaemonError::Io(e)
    }
}

impl From<DrvError> for DaemonError {
    fn from(e: DrvError) -> Self {
        DaemonError::Build(e)
    }
}

impl From<StoreError> for DaemonError {
    fn from(e: StoreError) -> Self {
        DaemonError::Store(e)
    }
}
