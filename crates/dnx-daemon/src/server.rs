//! The long-lived daemon: a warm in-memory cache + an in-flight build dedup +
//! a `UnixListener` accept loop over the §2.4 wire.
//!
//! Concurrency model (M1, design §3.2): one accept loop; read-only requests
//! (`StoreQuery`, `CacheLookup`, `Ping`) are answered directly from the
//! content-addressed `Store`/cache (safe — both are append-mostly and
//! immutable). The build queue is serialized by `&mut self`, so two clients
//! asking for the SAME derivation realize it ONCE: the literal "compute once,
//! serve many" (J1).

use std::collections::HashMap;
use std::io::Write;
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::Path;
use std::sync::Arc;

use dnx_core::Blake3Hash;
use dnx_drv::Derivation;
use dnx_store::{Store, StorePath};

use crate::proto::{
    decode_request, decode_response, encode_request, encode_response, read_frame, write_frame,
    Request, Response, PROTO_VERSION,
};
use crate::{store_has_hash, DaemonError, LocalBuilder};

/// The build step the daemon dedups around. Abstracting it lets a test inject
/// a counting realizer (the J1 oracle, design §8.5.4) while production uses the
/// real `realize`-against-a-`Store` path.
pub trait Realizer {
    fn realize(&self, drv: &Derivation) -> Result<StorePath, DaemonError>;
}

/// Production realizer: run the builder against a store (the `LocalBuilder`
/// realize path, shared so there is one realize implementation).
impl Realizer for Store {
    fn realize(&self, drv: &Derivation) -> Result<StorePath, DaemonError> {
        LocalBuilder::realize_primary(self, drv)
    }
}

/// What `serve` returns: why the accept loop stopped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Shutdown {
    /// A client sent a `Shutdown` request.
    Requested,
}

/// The daemon's owned state: the store it serves, a warm blob cache keyed by
/// content hash (the J4 "serve a result by hash" path), and the in-flight
/// build memo keyed by drvPath (the J1 dedup — a second identical build never
/// re-realizes).
pub struct Daemon {
    store: Store,
    /// `canonical_hash -> to_blob bytes`. A hit serves the bytes with zero
    /// work; the client `from_blob`s them with NO `normalize`.
    warm: HashMap<Blake3Hash, Arc<Vec<u8>>>,
    /// `drvPath hash -> realized output`. The serialized-build memo: once a
    /// drv is built, the same drv resolves from here without a second realize.
    /// Keyed by the drvPath's content hash, which uniquely identifies the
    /// derivation (instantiate is pure + deterministic).
    built: HashMap<Blake3Hash, StorePath>,
}

impl Daemon {
    pub fn new(store: Store) -> Self {
        Daemon {
            store,
            warm: HashMap::new(),
            built: HashMap::new(),
        }
    }

    /// The number of distinct derivations realized so far (the build-count
    /// oracle: with dedup it equals the number of *distinct* builds, not the
    /// number of build requests).
    pub fn built_count(&self) -> usize {
        self.built.len()
    }

    /// Seed the warm cache with a precomputed result blob under its content
    /// hash. Idempotent; serving it later is zero-work.
    pub fn warm_insert(&mut self, hash: Blake3Hash, blob: Vec<u8>) {
        self.warm.entry(hash).or_insert_with(|| Arc::new(blob));
    }

    /// Build `drv`, deduping in-flight: instantiate to its (pure, deterministic)
    /// drvPath; if that drvPath was already built, return the memoized output
    /// WITHOUT realizing again; otherwise realize ONCE and memoize. This is the
    /// J1 "compute once, serve many" mechanism — two clients with the same drv
    /// realize it once and both get the same `StorePath`.
    pub fn build<R: Realizer>(
        &mut self,
        drv: &Derivation,
        realizer: &R,
    ) -> Result<StorePath, DaemonError> {
        self.build_memo(drv, |_store, d| realizer.realize(d))
    }

    /// Build a derivation arriving over the wire as `to_bytes`: decode it with
    /// `dnx-drv`'s own `from_bytes`, then realize-and-dedup against the daemon's
    /// own store (the production realize path). One decode site, one realize
    /// site (`LocalBuilder::realize_primary`), shared with `LocalBuilder`.
    fn build_wire(&mut self, drv_bytes: &[u8]) -> Result<StorePath, DaemonError> {
        let drv = Derivation::from_bytes(drv_bytes)?;
        self.build_memo(&drv, LocalBuilder::realize_primary)
    }

    /// The shared dedup core: instantiate to the (pure) drvPath, return the
    /// memoized output if already built, else realize ONCE via `realize` and
    /// memoize. `realize` is passed the store and the derivation, so the store
    /// borrow never overlaps the `built` mutation (no self-aliasing).
    fn build_memo(
        &mut self,
        drv: &Derivation,
        realize: impl FnOnce(&Store, &Derivation) -> Result<StorePath, DaemonError>,
    ) -> Result<StorePath, DaemonError> {
        let key = *drv.instantiate(&self.store)?.hash();
        if let Some(out) = self.built.get(&key) {
            return Ok(out.clone());
        }
        let out = realize(&self.store, drv)?;
        self.built.insert(key, out.clone());
        Ok(out)
    }

    /// The self-report payload (answer to `Ping`/`Shutdown`): wire version, the
    /// serial worker's pending depth (0 at rest, design §3.2), and the
    /// distinct-build count — the wire-observable J1 oracle (§8.5.4 "a
    /// build-count of 1"), so a client proves "compute once" across concurrent
    /// builds without a side-effecting builder.
    fn pong(&self) -> Response {
        Response::Pong {
            version: PROTO_VERSION,
            queue_depth: 0,
            built: self.built_count() as u32,
        }
    }

    /// Answer one decoded request. Read-only requests touch only the
    /// content-addressed store/cache; `Shutdown` signals the loop to stop.
    fn handle(&mut self, req: Request) -> (Response, Option<Shutdown>) {
        match req {
            Request::Build(drv_bytes) => {
                let res = match self.build_wire(&drv_bytes) {
                    Ok(path) => Response::Built(path),
                    Err(e) => Response::Failed(e.kind(), e.to_string()),
                };
                (res, None)
            }
            Request::StoreQuery(hash) => (
                Response::StorePresent(store_has_hash(&self.store, &hash)),
                None,
            ),
            Request::CacheLookup(hash) => match self.warm.get(&hash) {
                Some(blob) => (Response::CacheHit(blob.as_ref().clone()), None),
                None => (Response::CacheMiss, None),
            },
            Request::Ping => (self.pong(), None),
            Request::Shutdown => (self.pong(), Some(Shutdown::Requested)),
        }
    }
}

/// Bind the socket and run the accept loop until a `Shutdown` request, then
/// unlink the socket. Stale-socket recovery (design §3.2): if the path exists
/// but no daemon answers `Ping`, the stale file is removed before binding.
pub fn serve(sock: &Path, daemon: Daemon) -> Result<Shutdown, DaemonError> {
    reclaim_stale(sock);
    if let Some(parent) = sock.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let listener = UnixListener::bind(sock)?;
    let outcome = accept_loop(&listener, daemon);
    let _ = std::fs::remove_file(sock);
    outcome
}

/// The accept loop, split out so `serve` always unlinks the socket on exit
/// regardless of how the loop ends.
fn accept_loop(listener: &UnixListener, mut daemon: Daemon) -> Result<Shutdown, DaemonError> {
    for conn in listener.incoming() {
        let mut stream = conn?;
        match serve_conn(&mut daemon, &mut stream) {
            Ok(Some(shutdown)) => return Ok(shutdown),
            Ok(None) => {}
            // A single bad/dropped connection must not kill the daemon: report
            // the typed error to that client (best-effort) and keep serving.
            Err(e) => {
                let body = encode_response(&Response::Failed(e.kind(), e.to_string()));
                let _ = write_frame(&mut stream, &body);
            }
        }
    }
    Ok(Shutdown::Requested)
}

/// Serve one connection: read a frame, decode, handle, reply. Returns the
/// shutdown signal if this request asked the daemon to stop.
fn serve_conn(
    daemon: &mut Daemon,
    stream: &mut UnixStream,
) -> Result<Option<Shutdown>, DaemonError> {
    let body = read_frame(stream)?;
    let req = decode_request(&body)?;
    let (res, shutdown) = daemon.handle(req);
    write_frame(stream, &encode_response(&res))?;
    stream.flush()?;
    Ok(shutdown)
}

/// Send one request to a running daemon and read its single response.
pub(crate) fn request(sock: &Path, req: Request) -> Result<Response, DaemonError> {
    let mut stream = match UnixStream::connect(sock) {
        Ok(s) => s,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Err(DaemonError::NotRunning),
        Err(e) if e.kind() == std::io::ErrorKind::ConnectionRefused => {
            return Err(DaemonError::NotRunning)
        }
        Err(e) => return Err(DaemonError::Io(e)),
    };
    write_frame(&mut stream, &encode_request(&req))?;
    decode_response(&read_frame(&mut stream)?)
}

/// A daemon's self-report, the typed payload of one `Ping`→`Pong` round-trip.
/// `version` is the wire version; `queue_depth` is the build worker's pending
/// count (0 at rest for M1's serial worker, design §3.2). Backs
/// `dnx daemon status` (design §3.1), which `ping`'s bare version cannot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DaemonStatus {
    pub version: u32,
    pub queue_depth: u32,
    /// Distinct derivations realized so far: the wire-observable build-count
    /// (design §8.5.4), so two concurrent clients of the same drv can prove it
    /// was built once (`built == 1`).
    pub built: u32,
}

/// Status probe: `Some(DaemonStatus)` if a daemon answers `Ping`, else `None`
/// (the connect-or-"not running" branch of `dnx daemon status`, design §3.1).
pub fn daemon_status(sock: &Path) -> Option<DaemonStatus> {
    match request(sock, Request::Ping) {
        Ok(Response::Pong {
            version,
            queue_depth,
            built,
        }) => Some(DaemonStatus {
            version,
            queue_depth,
            built,
        }),
        _ => None,
    }
}

/// Liveness probe: `Some(version)` if a daemon answers `Ping`, else `None`
/// (drives `dnx build`'s builder selection and stale-socket recovery). The
/// version-only projection of [`daemon_status`].
pub fn ping(sock: &Path) -> Option<u32> {
    daemon_status(sock).map(|s| s.version)
}

/// If a socket file exists but no daemon answers `Ping`, it is a stale file
/// from a crashed daemon — remove it so a fresh `bind` succeeds. A live daemon
/// is left untouched (its `bind` will then fail with `AddrInUse`, one daemon
/// per socket).
fn reclaim_stale(sock: &Path) {
    if sock.exists() && ping(sock).is_none() {
        let _ = std::fs::remove_file(sock);
    }
}
