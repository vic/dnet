//! Verification fixture (NOT shipped): seed a `DiskCache` with one normalized
//! artifact and print its content-hash, so the `serve`/`fetch` bins can be
//! driven firsthand over a real socket. The net is `(λx.x) arg`, verbatim from
//! tests/network.rs:28 (one β-reduction, pure, ΔL).

use std::sync::Arc;

use dnx_core::{canonical_hash, normalize, LOPath, Net, Proper, ΔL};
use dnx_dist::DiskCache;

const ROOT: &str = "res";

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let dir = std::env::args().nth(1).ok_or("usage: seed <cache-dir>")?;

    let mut n = Net::<Proper, ΔL>::new(16);
    let abs = n.alloc_abs()?;
    let app = n.alloc_app()?;
    let arg = n.alloc_free(0)?;
    let res = n.alloc_free(1)?;
    n.connect(abs.aux0, abs.aux1, LOPath::root())?;
    n.connect(app.aux0, res, LOPath::root())?;
    n.connect(app.aux1, arg, LOPath::root())?;
    n.connect(abs.principal, app.principal, LOPath::root())?;
    n.add_root(Arc::from(ROOT), res);

    let (nf, _) = normalize(n)?;
    let root = nf
        .roots()
        .get(ROOT)
        .copied()
        .ok_or("normalized net lost its root")?;
    let key = canonical_hash(&nf, root)?;

    let cache = DiskCache::open(&dir)?;
    let stored = cache.store(&nf, root)?;

    const LUT: &[u8; 16] = b"0123456789abcdef";
    let mut hex = String::with_capacity(64);
    for &b in &stored {
        hex.push(LUT[(b >> 4) as usize] as char);
        hex.push(LUT[(b & 0x0F) as usize] as char);
    }
    debug_assert_eq!(stored, key);
    println!("{hex}");
    Ok(())
}
