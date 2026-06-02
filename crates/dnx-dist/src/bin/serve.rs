//! `dnx-dist serve <addr> <cache-dir>` — node A's thin publishing harness
//! (dist-network-transport.md §6.5.1:325, §6.5.2:353-355).
//!
//! Opens the on-disk result cache at `<cache-dir>` and binds the loopback
//! `<addr>` via [`bind_serve`], printing the OS-resolved address once the
//! socket is live (port `0` ⇒ the kernel picks a free port, learned from the
//! SAME binding — no drop-then-rebind flake, wire.rs:256-259). It then blocks
//! forever on the serial accept loop, answering `Want`/`Have` by hash. The
//! server is OUTSIDE the TCB: it ships verbatim blob bytes and vouches for
//! nothing — the client's `import` re-hash is the gate (disk.rs:162-163).

use std::process::ExitCode;
use std::sync::mpsc;
use std::thread;

use dnx_dist::{bind_serve, DiskCache};

const USAGE: &str = "usage: serve <addr> <cache-dir>";

fn run() -> Result<(), String> {
    let mut args = std::env::args().skip(1);
    let addr = args.next().ok_or(USAGE)?;
    let cache_dir = args.next().ok_or(USAGE)?;
    if args.next().is_some() {
        return Err(USAGE.to_owned());
    }

    let cache = DiskCache::open(&cache_dir).map_err(|e| e.to_string())?;

    // `bind_serve` binds, sends the bound addr on `ready`, then blocks on the
    // accept loop. Drive it on a worker so the main thread can print the real
    // address before serving begins (mirrors network.rs:466-471).
    let (ready_tx, ready_rx) = mpsc::channel();
    let worker = thread::spawn(move || bind_serve(&addr, &ready_tx, &cache));

    match ready_rx.recv() {
        Ok(bound) => println!("serving on {bound}"),
        // Sender dropped before binding ⇒ the worker failed; surface its error.
        Err(_) => {
            return worker
                .join()
                .map_err(|_| "serve worker panicked".to_owned())?
                .map_err(|e| e.to_string());
        }
    }

    // The accept loop never returns `Ok`; a join only completes on a serve I/O
    // error, which we propagate.
    worker
        .join()
        .map_err(|_| "serve worker panicked".to_owned())?
        .map_err(|e| e.to_string())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(msg) => {
            eprintln!("dnx-dist serve: {msg}");
            ExitCode::FAILURE
        }
    }
}
