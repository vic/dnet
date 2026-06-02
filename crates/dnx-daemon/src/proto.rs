//! The on-socket wire: length-prefixed frames over any byte stream
//! (`dnx-daemon-design.md` §2.4). One byte-handling style, mirroring the
//! canonical-net codec: all multi-byte integers little-endian, every read
//! bounds-checked against the frame, malformed input is a typed `Protocol`
//! error (never a panic or out-of-bounds).
//!
//! ```text
//! FRAME = u32_le LEN ++ BODY[LEN]      LEN > MAX_FRAME -> FrameTooLarge
//! BODY  = u8 TAG ++ payload(TAG)       0x0_ = request, 0x8_ = response
//! ```

use std::io::{Read, Write};

use dnx_core::Blake3Hash;
use dnx_store::StorePath;

use crate::{DaemonError, DaemonErrorKind};

/// Wire-format version handed back by `Ping` → `Pong`.
pub const PROTO_VERSION: u32 = 1;

/// Upper bound on a single frame body (256 MiB): a hostile client cannot make
/// the reader allocate without bound.
const MAX_FRAME: u32 = 256 << 20;

// Request tags (top bit clear).
const TAG_BUILD: u8 = 0x01;
const TAG_STORE_QUERY: u8 = 0x03;
const TAG_CACHE_LOOKUP: u8 = 0x04;
const TAG_PING: u8 = 0x05;
const TAG_SHUTDOWN: u8 = 0x06;

// Response tags (top bit set, so a misframed direction is a `BadTag`).
const TAG_BUILT: u8 = 0x81;
const TAG_STORE_PRESENT: u8 = 0x82;
const TAG_CACHE_HIT: u8 = 0x83;
const TAG_CACHE_MISS: u8 = 0x84;
const TAG_PONG: u8 = 0x85;
const TAG_FAILED: u8 = 0x86;

/// A client→daemon message. Closed enum: a byte stream parses into one of
/// these or into `DaemonError::BadTag` — there is no unknown-message path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Request {
    /// J1/J2: realize a derivation, shipped as the opaque `to_bytes` encoding
    /// the daemon decodes with `dnx-drv`'s own `Derivation::from_bytes` (the
    /// single source of that shape, `dnx-daemon-design.md` §2.4). The worker
    /// dedups in-flight builds of the same derivation.
    Build(Vec<u8>),
    /// J3: is this content hash a registered store member?
    StoreQuery(Blake3Hash),
    /// J4: serve the warm result-cache entry for this hash, if any.
    CacheLookup(Blake3Hash),
    /// Lifecycle handshake / status.
    Ping,
    /// Ask the daemon to drain and exit.
    Shutdown,
}

/// A daemon→client message.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Response {
    /// The realized output store path (answer to `Build`).
    Built(StorePath),
    StorePresent(bool),
    /// `blob` = `to_blob(net, root)` bytes; the client `from_blob`s it with NO
    /// `normalize` — the "0 reduction steps" guarantee.
    CacheHit(Vec<u8>),
    CacheMiss,
    Pong {
        version: u32,
        queue_depth: u32,
        built: u32,
    },
    Failed(DaemonErrorKind, String),
}

// ── frame I/O ────────────────────────────────────────────────────────────

/// Write a length-prefixed frame over any stream.
pub(crate) fn write_frame<W: Write>(w: &mut W, body: &[u8]) -> Result<(), DaemonError> {
    let len = u32::try_from(body.len()).map_err(|_| DaemonError::FrameTooLarge)?;
    if len > MAX_FRAME {
        return Err(DaemonError::FrameTooLarge);
    }
    w.write_all(&len.to_le_bytes())?;
    w.write_all(body)?;
    w.flush()?;
    Ok(())
}

/// Read one length-prefixed frame, enforcing `MAX_FRAME`. A clean EOF before
/// any bytes is reported as `NotRunning` (the peer hung up).
pub(crate) fn read_frame<R: Read>(r: &mut R) -> Result<Vec<u8>, DaemonError> {
    let mut len_buf = [0u8; 4];
    if let Err(e) = r.read_exact(&mut len_buf) {
        if e.kind() == std::io::ErrorKind::UnexpectedEof {
            return Err(DaemonError::NotRunning);
        }
        return Err(DaemonError::Io(e));
    }
    let len = u32::from_le_bytes(len_buf);
    if len > MAX_FRAME {
        return Err(DaemonError::FrameTooLarge);
    }
    let mut body = vec![0u8; len as usize];
    r.read_exact(&mut body)?;
    Ok(body)
}

// ── body codec (the §2.4 primitives) ───────────────────────────────────────

fn put_u32(buf: &mut Vec<u8>, n: u32) {
    buf.extend_from_slice(&n.to_le_bytes());
}

fn put_hash(buf: &mut Vec<u8>, h: &Blake3Hash) {
    buf.extend_from_slice(h);
}

fn put_bytes(buf: &mut Vec<u8>, b: &[u8]) {
    // A length-prefixed blob; the prefix is bounded by MAX_FRAME on write.
    put_u32(buf, b.len() as u32);
    buf.extend_from_slice(b);
}

/// A bounds-checked cursor over a frame body: every take is validated against
/// the remaining bytes, so a short or over-long body is a typed `Protocol`
/// error rather than a panic.
struct Cursor<'a> {
    body: &'a [u8],
    at: usize,
}

impl<'a> Cursor<'a> {
    fn new(body: &'a [u8]) -> Self {
        Cursor { body, at: 0 }
    }

    fn tag(&mut self) -> Result<u8, DaemonError> {
        self.take(1).map(|s| s[0])
    }

    fn take(&mut self, n: usize) -> Result<&'a [u8], DaemonError> {
        let end = self.at.checked_add(n).ok_or_else(short)?;
        if end > self.body.len() {
            return Err(short());
        }
        let s = &self.body[self.at..end];
        self.at = end;
        Ok(s)
    }

    fn u32(&mut self) -> Result<u32, DaemonError> {
        let s = self.take(4)?;
        Ok(u32::from_le_bytes([s[0], s[1], s[2], s[3]]))
    }

    fn hash(&mut self) -> Result<Blake3Hash, DaemonError> {
        let s = self.take(32)?;
        let mut h = [0u8; 32];
        h.copy_from_slice(s);
        Ok(h)
    }

    fn bytes(&mut self) -> Result<Vec<u8>, DaemonError> {
        let n = self.u32()? as usize;
        Ok(self.take(n)?.to_vec())
    }

    /// A trailing-bytes check: the body must be exactly consumed.
    fn finish(self) -> Result<(), DaemonError> {
        if self.at == self.body.len() {
            Ok(())
        } else {
            Err(DaemonError::Protocol("trailing bytes in frame".into()))
        }
    }
}

fn short() -> DaemonError {
    DaemonError::Protocol("frame body too short".into())
}

pub(crate) fn encode_request(req: &Request) -> Vec<u8> {
    let mut buf = Vec::new();
    match req {
        Request::Build(drv) => {
            buf.push(TAG_BUILD);
            put_bytes(&mut buf, drv);
        }
        Request::StoreQuery(h) => {
            buf.push(TAG_STORE_QUERY);
            put_hash(&mut buf, h);
        }
        Request::CacheLookup(h) => {
            buf.push(TAG_CACHE_LOOKUP);
            put_hash(&mut buf, h);
        }
        Request::Ping => buf.push(TAG_PING),
        Request::Shutdown => buf.push(TAG_SHUTDOWN),
    }
    buf
}

pub(crate) fn decode_request(body: &[u8]) -> Result<Request, DaemonError> {
    let mut c = Cursor::new(body);
    let req = match c.tag()? {
        TAG_BUILD => Request::Build(c.bytes()?),
        TAG_STORE_QUERY => Request::StoreQuery(c.hash()?),
        TAG_CACHE_LOOKUP => Request::CacheLookup(c.hash()?),
        TAG_PING => Request::Ping,
        TAG_SHUTDOWN => Request::Shutdown,
        _ => return Err(DaemonError::BadTag),
    };
    c.finish()?;
    Ok(req)
}

pub(crate) fn encode_response(res: &Response) -> Vec<u8> {
    let mut buf = Vec::new();
    match res {
        Response::Built(path) => {
            buf.push(TAG_BUILT);
            put_bytes(&mut buf, path.to_string().as_bytes());
        }
        Response::StorePresent(p) => {
            buf.push(TAG_STORE_PRESENT);
            buf.push(u8::from(*p));
        }
        Response::CacheHit(blob) => {
            buf.push(TAG_CACHE_HIT);
            put_bytes(&mut buf, blob);
        }
        Response::CacheMiss => buf.push(TAG_CACHE_MISS),
        Response::Pong {
            version,
            queue_depth,
            built,
        } => {
            buf.push(TAG_PONG);
            put_u32(&mut buf, *version);
            put_u32(&mut buf, *queue_depth);
            put_u32(&mut buf, *built);
        }
        Response::Failed(kind, detail) => {
            buf.push(TAG_FAILED);
            buf.push(*kind as u8);
            put_bytes(&mut buf, detail.as_bytes());
        }
    }
    buf
}

pub(crate) fn decode_response(body: &[u8]) -> Result<Response, DaemonError> {
    let mut c = Cursor::new(body);
    let res = match c.tag()? {
        TAG_BUILT => {
            let s = String::from_utf8(c.bytes()?)
                .map_err(|_| DaemonError::Protocol("store path is not utf-8".into()))?;
            Response::Built(StorePath::parse(&s).map_err(|e| DaemonError::Protocol(e.to_string()))?)
        }
        TAG_STORE_PRESENT => Response::StorePresent(c.take(1)?[0] != 0),
        TAG_CACHE_HIT => Response::CacheHit(c.bytes()?),
        TAG_CACHE_MISS => Response::CacheMiss,
        TAG_PONG => Response::Pong {
            version: c.u32()?,
            queue_depth: c.u32()?,
            built: c.u32()?,
        },
        TAG_FAILED => {
            let kind = DaemonErrorKind::from_u8(c.take(1)?[0]).ok_or(DaemonError::BadTag)?;
            let detail = String::from_utf8_lossy(&c.bytes()?).into_owned();
            Response::Failed(kind, detail)
        }
        _ => return Err(DaemonError::BadTag),
    };
    c.finish()?;
    Ok(res)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn h(b: u8) -> Blake3Hash {
        [b; 32]
    }

    // ── roundtrip: every variant decodes back to itself (the codec is a bijection
    // on valid frames) ─────────────────────────────────────────────────────────

    fn req_roundtrips(req: Request) {
        let decoded = decode_request(&encode_request(&req)).expect("valid request decodes");
        assert_eq!(decoded, req, "request survives encode→decode");
    }

    fn res_roundtrips(res: Response) {
        let decoded = decode_response(&encode_response(&res)).expect("valid response decodes");
        assert_eq!(decoded, res, "response survives encode→decode");
    }

    #[test]
    fn every_request_roundtrips() {
        req_roundtrips(Request::Build(Vec::new()));
        req_roundtrips(Request::Build(vec![0xde, 0xad, 0xbe, 0xef]));
        req_roundtrips(Request::StoreQuery(h(0x11)));
        req_roundtrips(Request::CacheLookup(h(0x22)));
        req_roundtrips(Request::Ping);
        req_roundtrips(Request::Shutdown);
    }

    #[test]
    fn every_response_roundtrips() {
        res_roundtrips(Response::Built(
            StorePath::new([9u8; 32], "hello").expect("valid path"),
        ));
        res_roundtrips(Response::StorePresent(true));
        res_roundtrips(Response::StorePresent(false));
        res_roundtrips(Response::CacheHit(vec![1, 2, 3, 4]));
        res_roundtrips(Response::CacheHit(Vec::new()));
        res_roundtrips(Response::CacheMiss);
        res_roundtrips(Response::Pong {
            version: 1,
            queue_depth: 0,
            built: 0,
        });
        res_roundtrips(Response::Pong {
            version: u32::MAX,
            queue_depth: 7,
            built: 42,
        });
        res_roundtrips(Response::Failed(DaemonErrorKind::Build, "boom".into()));
        res_roundtrips(Response::Failed(DaemonErrorKind::NotFound, String::new()));
    }

    // ── invalid-state-unrepresentable: every malformed byte stream is a TYPED
    // error, never a panic, OOB, or silent mis-decode (proto.rs §2.4 contract) ──

    #[test]
    fn empty_body_is_short_not_panic() {
        assert!(
            matches!(decode_request(&[]), Err(DaemonError::Protocol(_))),
            "an empty body cannot even yield a tag → Protocol"
        );
        assert!(matches!(
            decode_response(&[]),
            Err(DaemonError::Protocol(_))
        ));
    }

    #[test]
    fn unknown_request_tag_is_bad_tag() {
        assert!(matches!(decode_request(&[0x00]), Err(DaemonError::BadTag)));
        assert!(matches!(decode_request(&[0x7f]), Err(DaemonError::BadTag)));
    }

    #[test]
    fn unknown_response_tag_is_bad_tag() {
        assert!(matches!(decode_response(&[0x00]), Err(DaemonError::BadTag)));
        assert!(matches!(decode_response(&[0xff]), Err(DaemonError::BadTag)));
    }

    #[test]
    fn wrong_direction_tag_is_bad_tag() {
        // A response tag (top bit set) in the request decoder, and vice versa:
        // the split TAG space turns a misframed direction into BadTag, not a
        // silent mis-decode.
        assert!(matches!(
            decode_request(&[TAG_PONG]),
            Err(DaemonError::BadTag)
        ));
        assert!(matches!(
            decode_response(&[TAG_PING]),
            Err(DaemonError::BadTag)
        ));
    }

    #[test]
    fn short_hash_payload_is_protocol() {
        // StoreQuery declares a 32-byte hash; a truncated body is Protocol.
        let mut body = vec![TAG_STORE_QUERY];
        body.extend_from_slice(&[0u8; 10]);
        assert!(matches!(
            decode_request(&body),
            Err(DaemonError::Protocol(_))
        ));
    }

    #[test]
    fn trailing_bytes_after_a_complete_message_is_protocol() {
        // A valid Ping followed by junk must be rejected: the body must be
        // exactly consumed (Cursor::finish).
        assert!(matches!(
            decode_request(&[TAG_PING, 0xde, 0xad]),
            Err(DaemonError::Protocol(_))
        ));
    }

    #[test]
    fn cache_hit_with_lying_length_prefix_is_protocol() {
        // A Bytes prefix that claims more bytes than the body holds.
        let mut body = vec![TAG_CACHE_HIT];
        put_u32(&mut body, 9999); // claims 9999 bytes…
        body.extend_from_slice(b"short"); // …but only 5 follow.
        assert!(matches!(
            decode_response(&body),
            Err(DaemonError::Protocol(_))
        ));
    }

    #[test]
    fn failed_with_unknown_err_kind_is_bad_tag() {
        // err_kind 0xff is not a DaemonErrorKind discriminant (closed enum).
        let mut body = vec![TAG_FAILED, 0xff];
        put_bytes(&mut body, b"detail");
        assert!(matches!(decode_response(&body), Err(DaemonError::BadTag)));
    }

    // ── frame I/O: length-prefixed framing roundtrips and bounds a hostile
    // client (proto.rs §2.1) ────────────────────────────────────────────────────

    #[test]
    fn frame_roundtrips_over_a_byte_buffer() {
        let body = encode_request(&Request::StoreQuery(h(0x55)));
        let mut wire = Vec::new();
        write_frame(&mut wire, &body).expect("write frame");
        let read = read_frame(&mut wire.as_slice()).expect("read frame");
        assert_eq!(read, body, "the framed body is recovered byte-for-byte");
        assert_eq!(
            decode_request(&read).expect("decode"),
            Request::StoreQuery(h(0x55)),
        );
    }

    #[test]
    fn read_frame_rejects_an_oversize_length_prefix() {
        // A hand-built header claiming MAX_FRAME+1 bytes must be refused BEFORE
        // allocating (the OOM guard), without reading the body.
        let mut wire = (MAX_FRAME + 1).to_le_bytes().to_vec();
        wire.push(0x00);
        assert!(matches!(
            read_frame(&mut wire.as_slice()),
            Err(DaemonError::FrameTooLarge)
        ));
    }

    #[test]
    fn read_frame_on_clean_eof_is_not_running() {
        // No bytes at all → the peer hung up before sending a length prefix.
        let empty: &[u8] = &[];
        assert!(matches!(
            read_frame(&mut { empty }),
            Err(DaemonError::NotRunning)
        ));
    }

    #[test]
    fn read_frame_on_truncated_length_prefix_is_not_running() {
        // A partial (1-of-4 byte) prefix is still an UnexpectedEof while reading
        // the length word, so — like the zero-byte case — it is reported as the
        // peer having hung up (NotRunning), never a panic or a bogus length.
        let partial: &[u8] = &[0x01];
        assert!(matches!(
            read_frame(&mut { partial }),
            Err(DaemonError::NotRunning)
        ));
    }
}
