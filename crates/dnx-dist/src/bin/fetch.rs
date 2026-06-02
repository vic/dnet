//! `dnx-dist fetch <peer> <cache-dir> <net-hash-hex>` — node B's thin client
//! pull (dist-network-transport.md §6.5.1:326, §6.5.2:376-395).
//!
//! Opens the local result cache at `<cache-dir>`, narrows the request to what
//! it actually lacks (`DiskCache::missing`, disk.rs:199), then runs
//! [`probe_then_pull`] against `<peer>`: probe-before-pull asks A which keys it
//! holds and pulls only those, each landed under its claimed hash by the
//! `import` re-hash gate (disk.rs:179) — a tampered or truncated blob is
//! rejected, nothing stored. A HIT means the artifact arrived by hash, never
//! recomputed (the distribution headline, §6.5.3).

use std::process::ExitCode;

use dnx_core::{Blake3Hash, ΔL};
use dnx_dist::{probe_then_pull, DiskCache};

const USAGE: &str = "usage: fetch <peer> <cache-dir> <net-hash-hex>";

/// Decode a 64-char lower/upper-hex string into a 32-byte content-address.
/// Hand-rolled to avoid a `hex` dependency (matches disk.rs:95).
fn parse_hash(s: &str) -> Result<Blake3Hash, String> {
    let bytes = s.as_bytes();
    if bytes.len() != 64 {
        return Err(format!(
            "net-hash must be 64 hex chars, got {}",
            bytes.len()
        ));
    }
    let nibble = |c: u8| -> Result<u8, String> {
        match c {
            b'0'..=b'9' => Ok(c - b'0'),
            b'a'..=b'f' => Ok(c - b'a' + 10),
            b'A'..=b'F' => Ok(c - b'A' + 10),
            _ => Err(format!("invalid hex char {:?}", c as char)),
        }
    };
    let mut hash = [0u8; 32];
    for (i, pair) in bytes.chunks_exact(2).enumerate() {
        hash[i] = (nibble(pair[0])? << 4) | nibble(pair[1])?;
    }
    Ok(hash)
}

fn run() -> Result<(), String> {
    let mut args = std::env::args().skip(1);
    let peer = args.next().ok_or(USAGE)?;
    let cache_dir = args.next().ok_or(USAGE)?;
    let hash_hex = args.next().ok_or(USAGE)?;
    if args.next().is_some() {
        return Err(USAGE.to_owned());
    }

    let key = parse_hash(&hash_hex)?;
    let local = DiskCache::open(&cache_dir).map_err(|e| e.to_string())?;

    let want = local.missing(&[key]);
    if want.is_empty() {
        println!("already cached {hash_hex} (no fetch needed)");
        return Ok(());
    }

    probe_then_pull::<ΔL>(&peer, &want, &local).map_err(|e| e.to_string())?;

    if local.contains(&key) {
        println!("fetched {hash_hex} from {peer}");
        Ok(())
    } else {
        Err(format!("{peer} does not hold {hash_hex}"))
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(msg) => {
            eprintln!("dnx-dist fetch: {msg}");
            ExitCode::FAILURE
        }
    }
}
