//! Network transport for the content-addressed fetch-by-hash (dist-network-transport.md M1).
//!
//! The transport adds the **wire seam and nothing else**: identity, hashing,
//! canonicity and verify-on-import all stay in the layers below (`disk.rs`).
//! The three already-built cache functions — `missing` (the client's local
//! frontier diff), `export` (server: hash → verbatim bytes) and `import`
//! (client: untrusted bytes → re-hash gate → persist-or-reject) — are the wire
//! boundary; this module only carries their bytes over a socket. A tampered
//! blob in flight is caught by `import`'s re-hash (`disk.rs:185-188`), never
//! stored — the server is outside the TCB and vouches for nothing.
//!
//! ## Framing (reused verbatim from the dnx daemon design, §2.1)
//!
//! ```text
//! FRAME = u32_le LEN  ++  BODY[LEN]          // length-prefixed; LEN = byte count of BODY
//! BODY  = u8 TAG      ++  payload(TAG)       // 1-byte discriminant, then tag-specific bytes
//! ```
//!
//! The reader allocs exactly `LEN` and rejects `LEN > MAX_FRAME` so a remote
//! peer cannot OOM the server. `TAG` parses into the closed [`Msg`] set or it
//! is a hard `InvalidData` error — there is no "unknown message" runtime path
//! (parse-don't-validate at the wire boundary).

use std::io::{self, Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::mpsc::Sender;

use dnx_core::{Blake3Hash, NetClassMarker};

use crate::disk::{CacheError, DiskCache};

/// Upper bound on a single frame's `BODY` length (256 MiB), matching the
/// daemon's OOM guard (dnx-daemon-design.md:68-70). A frame claiming more is
/// rejected before any allocation.
pub const MAX_FRAME: u32 = 256 << 20;

const TAG_WANT: u8 = 0x10;
const TAG_HAVE: u8 = 0x11;
const TAG_BLOBS: u8 = 0x90;
const TAG_HELD: u8 = 0x91;
const TAG_FAILED: u8 = 0x9F;

/// The sync message set (dist-network-transport.md §3.2 + §3.2a). One frame
/// each, over the length-prefixed `u8`-TAG framing above.
#[derive(Debug, PartialEq, Eq)]
pub enum Msg {
    /// B → A: the keys B lacks (the wire form of B's local `missing` output).
    Want(Vec<Blake3Hash>),
    /// A → B: `export(k)` for each present `k`; an absent key is omitted (the
    /// peer can withhold but cannot forge — `import` is still the gate).
    Blobs(Vec<(Blake3Hash, Vec<u8>)>),
    /// B → A: "do you hold these?" — the advertise probe (the `missing` dual).
    Have(Vec<Blake3Hash>),
    /// A → B: per-key `contains`, the complement of `missing`.
    Held(Vec<bool>),
    /// A → B: a typed failure (kind byte + message); never a panic over the wire.
    Failed(u8, String),
}

/// One trait, every byte stream — a blanket impl over [`std::io::Read`] +
/// [`std::io::Write`], so a `UnixStream` AND a `TcpStream` both qualify with
/// zero per-impl code (dist-network-transport.md:348-349). The framing is
/// transport-agnostic; the channel is the only thing that varies.
pub trait Wire: Read + Write {}
impl<T: Read + Write> Wire for T {}

fn io_err(msg: &str) -> CacheError {
    CacheError::Io(io::Error::new(io::ErrorKind::InvalidData, msg.to_owned()))
}

fn put_u32(buf: &mut Vec<u8>, n: u32) {
    buf.extend_from_slice(&n.to_le_bytes());
}

/// Length-check a `usize` count/length down to the `u32` the wire carries.
fn as_u32(n: usize) -> Result<u32, CacheError> {
    u32::try_from(n).map_err(|_| io_err("length exceeds u32"))
}

fn encode_hashes(buf: &mut Vec<u8>, hashes: &[Blake3Hash]) -> Result<(), CacheError> {
    put_u32(buf, as_u32(hashes.len())?);
    for h in hashes {
        buf.extend_from_slice(h);
    }
    Ok(())
}

/// Serialize a message's `BODY` (`u8 TAG ++ payload`).
fn encode_body(m: &Msg) -> Result<Vec<u8>, CacheError> {
    let mut buf = Vec::new();
    match m {
        Msg::Want(keys) => {
            buf.push(TAG_WANT);
            encode_hashes(&mut buf, keys)?;
        }
        Msg::Have(keys) => {
            buf.push(TAG_HAVE);
            encode_hashes(&mut buf, keys)?;
        }
        Msg::Blobs(pairs) => {
            buf.push(TAG_BLOBS);
            put_u32(&mut buf, as_u32(pairs.len())?);
            for (h, blob) in pairs {
                buf.extend_from_slice(h);
                put_u32(&mut buf, as_u32(blob.len())?);
                buf.extend_from_slice(blob);
            }
        }
        Msg::Held(bits) => {
            buf.push(TAG_HELD);
            put_u32(&mut buf, as_u32(bits.len())?);
            buf.extend(bits.iter().map(|&b| u8::from(b)));
        }
        Msg::Failed(kind, why) => {
            buf.push(TAG_FAILED);
            buf.push(*kind);
            let bytes = why.as_bytes();
            put_u32(&mut buf, as_u32(bytes.len())?);
            buf.extend_from_slice(bytes);
        }
    }
    Ok(buf)
}

/// Frame and write a message: `u32_le LEN ++ BODY`.
pub fn write_msg<W: Wire>(w: &mut W, m: &Msg) -> Result<(), CacheError> {
    let body = encode_body(m)?;
    let len = as_u32(body.len())?;
    if len > MAX_FRAME {
        return Err(io_err("frame exceeds MAX_FRAME"));
    }
    w.write_all(&len.to_le_bytes())?;
    w.write_all(&body)?;
    w.flush()?;
    Ok(())
}

/// A cursor over an already-read `BODY`, so payload decoding never reads past
/// the frame (the length prefix is the sole authority on a message's extent).
struct Cursor<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Cursor { bytes, pos: 0 }
    }

    fn take(&mut self, n: usize) -> Result<&'a [u8], CacheError> {
        let end = self
            .pos
            .checked_add(n)
            .ok_or_else(|| io_err("length overflow"))?;
        let slice = self
            .bytes
            .get(self.pos..end)
            .ok_or_else(|| io_err("frame body truncated"))?;
        self.pos = end;
        Ok(slice)
    }

    fn u8(&mut self) -> Result<u8, CacheError> {
        Ok(self.take(1)?[0])
    }

    fn u32(&mut self) -> Result<u32, CacheError> {
        let b = self.take(4)?;
        Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    }

    fn hash(&mut self) -> Result<Blake3Hash, CacheError> {
        let b = self.take(32)?;
        let mut h = [0u8; 32];
        h.copy_from_slice(b);
        Ok(h)
    }

    /// Reject trailing bytes — a frame must decode exactly, no slack.
    fn finish(&self) -> Result<(), CacheError> {
        if self.pos == self.bytes.len() {
            Ok(())
        } else {
            Err(io_err("frame body has trailing bytes"))
        }
    }
}

/// Decode a `u32`-counted run of 32-byte hashes. `n` is PEER-CONTROLLED, so it
/// is used ONLY as a loop bound, never to pre-size the `Vec` — `c.hash()`
/// consumes 32 real bytes per element, so a bogus `n` runs out of frame body at
/// the first iteration and yields `Err`, allocating ~nothing (no amplification;
/// mirrors `dnx-core` `blob.rs` `deserialize`). The frame body was already
/// capped at `MAX_FRAME`, but that bounds the BYTES, not the element COUNT.
fn decode_hashes(c: &mut Cursor<'_>) -> Result<Vec<Blake3Hash>, CacheError> {
    let n = c.u32()?;
    let mut out = Vec::new();
    for _ in 0..n {
        out.push(c.hash()?);
    }
    Ok(out)
}

/// Read and parse one frame into a [`Msg`]. Enforces `MAX_FRAME` before
/// allocating, so a hostile peer cannot OOM the reader.
pub fn read_msg<R: Wire>(r: &mut R) -> Result<Msg, CacheError> {
    let mut len_buf = [0u8; 4];
    r.read_exact(&mut len_buf)?;
    let len = u32::from_le_bytes(len_buf);
    if len > MAX_FRAME {
        return Err(io_err("incoming frame exceeds MAX_FRAME"));
    }
    let mut body = vec![0u8; len as usize];
    r.read_exact(&mut body)?;

    let mut c = Cursor::new(&body);
    let tag = c.u8()?;
    let msg = match tag {
        TAG_WANT => Msg::Want(decode_hashes(&mut c)?),
        TAG_HAVE => Msg::Have(decode_hashes(&mut c)?),
        TAG_BLOBS => {
            // PEER-CONTROLLED `n`: loop bound only, never a pre-size. Each pair
            // consumes ≥36 real bytes (32-byte hash + 4-byte length), so a bogus
            // `n` exhausts the frame body immediately and errors — no GB reserve.
            let n = c.u32()?;
            let mut pairs = Vec::new();
            for _ in 0..n {
                let h = c.hash()?;
                let blen = c.u32()? as usize;
                pairs.push((h, c.take(blen)?.to_vec()));
            }
            Msg::Blobs(pairs)
        }
        TAG_HELD => {
            // PEER-CONTROLLED `n`: loop bound only, never a pre-size. Each bit
            // consumes 1 real byte, so a bogus `n` cannot reserve past the frame.
            let n = c.u32()?;
            let mut bits = Vec::new();
            for _ in 0..n {
                bits.push(c.u8()? != 0);
            }
            Msg::Held(bits)
        }
        TAG_FAILED => {
            let kind = c.u8()?;
            let slen = c.u32()? as usize;
            let why = std::str::from_utf8(c.take(slen)?)
                .map_err(|_| io_err("Failed message is not utf-8"))?
                .to_owned();
            Msg::Failed(kind, why)
        }
        _ => return Err(io_err("unknown wire tag")),
    };
    c.finish()?;
    Ok(msg)
}

/// Node A — the thin publishing harness: bind `addr` and serve blobs by hash
/// over it (dist-network-transport.md §6.5.2:354-355, §6.a:275). This is the
/// addr-binding entry the listener-taking [`serve`] doc promises — the `dnx-dist
/// serve` bin's core, minus CLI parsing. `addr` is the configured loopback
/// endpoint for the demo (§3.3); binding stays inside the harness so the caller
/// passes a string, never a pre-bound socket.
///
/// `ready` receives the bound [`SocketAddr`] ONCE, after the bind and before the
/// blocking accept loop. This is the bin's "listening on {addr}" hook and lets a
/// caller pass `addr` with port `0` (OS-assigned) yet still learn the real port
/// from the SAME binding — no drop-then-rebind, so no fixed-/reused-port flake
/// (§6.5.4). A dropped `ready` receiver is not fatal: the send is best-effort and
/// serving proceeds regardless.
///
/// Blocks forever on the serial accept loop (it never returns `Ok`); a bind
/// failure is reported as `CacheError::Io` before `ready` fires or any
/// connection is served.
pub fn bind_serve(
    addr: &str,
    ready: &Sender<SocketAddr>,
    cache: &DiskCache,
) -> Result<(), CacheError> {
    let listener = TcpListener::bind(addr).map_err(CacheError::Io)?;
    let _ = ready.send(listener.local_addr().map_err(CacheError::Io)?);
    serve(&listener, cache)
}

/// Node A — serve blobs by hash over a bound listener (the publishing side; the
/// server is OUTSIDE the TCB, `disk.rs:162-163`). Accepts connections serially
/// and answers one request per connection: a `Want` with the matching `export`
/// results (absent keys omitted), or a `Have` with the per-key `contains`
/// probe. Any other request is a typed `Failed`, never a panic.
///
/// The caller supplies an already-bound [`TcpListener`] so a test can bind
/// `127.0.0.1:0` and read the OS-assigned port before the client connects (no
/// fixed-port flake); the thin [`bind_serve`] harness binds the configured
/// address from a string and hands it here.
pub fn serve(listener: &TcpListener, cache: &DiskCache) -> Result<(), CacheError> {
    for conn in listener.incoming() {
        let mut s = conn?;
        serve_conn(&mut s, cache)?;
    }
    Ok(())
}

/// Handle exactly one request on an already-accepted stream. Split out so it is
/// reusable over any [`Wire`] (a `UnixStream` is equally valid) and unit-able.
fn serve_conn<S: Wire>(s: &mut S, cache: &DiskCache) -> Result<(), CacheError> {
    match read_msg(s)? {
        Msg::Want(keys) => {
            let mut pairs = Vec::new();
            for k in keys {
                if let Some(blob) = cache.export(&k)? {
                    pairs.push((k, blob));
                }
            }
            write_msg(s, &Msg::Blobs(pairs))
        }
        Msg::Have(keys) => {
            let present = keys.iter().map(|k| cache.contains(k)).collect();
            write_msg(s, &Msg::Held(present))
        }
        _ => write_msg(s, &Msg::Failed(2, "unexpected request".to_owned())),
    }
}

/// Node B — the advertise probe: ask `peer` which of `keys` it holds, the dual
/// of `missing` (dist-network-transport.md:154-159, §3.2a). Sends `Have(keys)`
/// and reads the peer's per-key `Held(present)` (`present[i] == peer.contains(keys[i])`),
/// letting B skip a `Want` for a key A lacks — probe-before-pull, avoiding the
/// withhold-then-error round-trip (distribution-mvp-plan.md:325).
///
/// Carries NO blob bytes, so it is a pure optimization hint OUTSIDE the TCB: an
/// over-advertised `true` is harmless because the later `sync_pull`'s `import`
/// re-hash is still the gate (dist-network-transport.md:165-171). A reply whose
/// length differs from `keys` is a protocol violation — typed error, never a
/// silent truncation.
pub fn probe(peer: &str, keys: &[Blake3Hash]) -> Result<Vec<bool>, CacheError> {
    let mut s = TcpStream::connect(peer).map_err(CacheError::Io)?;
    write_msg(&mut s, &Msg::Have(keys.to_vec()))?;
    match read_msg(&mut s)? {
        Msg::Held(present) if present.len() == keys.len() => Ok(present),
        Msg::Held(_) => Err(io_err("Held length does not match Have")),
        Msg::Failed(_, why) => Err(io_err(&format!("peer refused: {why}"))),
        _ => Err(io_err("peer sent an unexpected reply to Have")),
    }
}

/// Node B — pull the missing blobs from `peer` and verify-on-import
/// (`disk.rs:179`). `want` is the caller's locally-computed `missing` output;
/// each returned blob is `import`ed under its claimed hash, so a tampered or
/// truncated blob fails the re-hash gate (`HashMismatch`) and nothing is
/// stored. A `Failed` reply or an unexpected message is a typed error.
pub fn sync_pull<C: NetClassMarker>(
    peer: &str,
    want: &[Blake3Hash],
    local: &DiskCache,
) -> Result<(), CacheError> {
    let mut s = TcpStream::connect(peer).map_err(CacheError::Io)?;
    write_msg(&mut s, &Msg::Want(want.to_vec()))?;
    match read_msg(&mut s)? {
        Msg::Blobs(pairs) => {
            for (h, blob) in pairs {
                local.import::<C>(h, &blob)?;
            }
            Ok(())
        }
        Msg::Failed(_, why) => Err(io_err(&format!("peer refused: {why}"))),
        _ => Err(io_err("peer sent an unexpected reply to Want")),
    }
}

/// Node B — probe-before-pull: [`probe`] `peer` for `want`, then [`sync_pull`]
/// ONLY the keys it actually holds. This wires §3.2a's skip-optimization into
/// the fetch path — B never sends a `Want` for a key A lacks, avoiding the
/// withhold-then-empty-`Blobs` round-trip (dist-network-transport.md:154-159).
///
/// `want` is already the caller's local `missing` frontier (`disk.rs:199`); the
/// probe narrows it further to the peer's `contains`. If the peer holds none of
/// `want`, no second connection is opened at all — the pull is skipped, not sent
/// empty. The narrowing is a pure optimization hint OUTSIDE the TCB: an
/// over-advertised `true` only costs the `sync_pull`'s `import` re-hash that is
/// the real gate (dist-network-transport.md:165-171, distribution-mvp-plan.md:325).
pub fn probe_then_pull<C: NetClassMarker>(
    peer: &str,
    want: &[Blake3Hash],
    local: &DiskCache,
) -> Result<(), CacheError> {
    let present = probe(peer, want)?;
    let held: Vec<Blake3Hash> = want
        .iter()
        .zip(present)
        .filter_map(|(k, has)| has.then_some(*k))
        .collect();
    if held.is_empty() {
        return Ok(());
    }
    sync_pull::<C>(peer, &held, local)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A [`Wire`] backed by a fixed byte buffer: `Read` drains it, `Write` is a
    /// sink. Lets `read_msg` decode a hand-crafted frame with no socket.
    struct BufWire {
        buf: std::io::Cursor<Vec<u8>>,
    }

    impl Read for BufWire {
        fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
            self.buf.read(out)
        }
    }

    impl Write for BufWire {
        fn write(&mut self, data: &[u8]) -> io::Result<usize> {
            Ok(data.len())
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    /// Frame a `BODY` with its `u32_le` length prefix (the on-wire framing).
    fn frame(body: &[u8]) -> BufWire {
        let mut bytes = (body.len() as u32).to_le_bytes().to_vec();
        bytes.extend_from_slice(body);
        BufWire {
            buf: std::io::Cursor::new(bytes),
        }
    }

    // ── adversarial: untrusted-input memory-amplification DoS ────────────────
    // Mirrors `dnx-core` `blob.rs::huge_record_count_no_amplification`: a tiny
    // frame whose element count is 0xFFFFFFFF must return a typed `Err` (the
    // body runs out at the first element read), NEVER pre-reserve gigabytes from
    // the unvalidated count. `MAX_FRAME` caps the BODY bytes, not the COUNT.

    #[test]
    fn huge_want_count_no_amplification() {
        // BODY = TAG_WANT ++ n=0xFFFFFFFF, but ZERO hashes follow. A pre-sized
        // `Vec::<[u8;32]>::with_capacity(0xFFFFFFFF)` would reserve ~128 GiB and
        // abort the process; the grow-on-demand decoder errors instead.
        let body = [TAG_WANT, 0xFF, 0xFF, 0xFF, 0xFF];
        let r = read_msg(&mut frame(&body));
        assert!(matches!(r, Err(CacheError::Io(_))), "got {r:?}");
    }

    #[test]
    fn huge_have_count_no_amplification() {
        let body = [TAG_HAVE, 0xFF, 0xFF, 0xFF, 0xFF];
        let r = read_msg(&mut frame(&body));
        assert!(matches!(r, Err(CacheError::Io(_))), "got {r:?}");
    }

    #[test]
    fn huge_blobs_count_no_amplification() {
        // BODY = TAG_BLOBS ++ n=0xFFFFFFFF, no pairs. Each pair is ≥36 bytes; a
        // pre-sized `Vec::<(_,_)>::with_capacity(0xFFFFFFFF)` would reserve tens
        // of GiB. The decoder must error on the first missing pair instead.
        let body = [TAG_BLOBS, 0xFF, 0xFF, 0xFF, 0xFF];
        let r = read_msg(&mut frame(&body));
        assert!(matches!(r, Err(CacheError::Io(_))), "got {r:?}");
    }

    #[test]
    fn huge_held_count_no_amplification() {
        let body = [TAG_HELD, 0xFF, 0xFF, 0xFF, 0xFF];
        let r = read_msg(&mut frame(&body));
        assert!(matches!(r, Err(CacheError::Io(_))), "got {r:?}");
    }

    /// Sanity: a WELL-FORMED frame still round-trips after the fix (the
    /// grow-on-demand path must not have broken the happy case).
    #[test]
    fn well_formed_want_round_trips() {
        let h = [7u8; 32];
        let mut body = vec![TAG_WANT];
        body.extend_from_slice(&1u32.to_le_bytes());
        body.extend_from_slice(&h);
        let msg = read_msg(&mut frame(&body)).expect("well-formed frame decodes");
        assert_eq!(msg, Msg::Want(vec![h]));
    }
}
