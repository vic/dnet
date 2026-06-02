//! TEMP probe2 (delete): TWO-STAGE C2-in-parallel with ALIASED rep_b.
//! Stage1 batch erases rep_a.aux1 (R2) AND exposes rep_a.principal to ERA (R2->R3 next batch).
//! Stage2 batch: ERA ⊗ rep_a (R3) -> PAR c2_par sees committed erased bit -> merges into rep_b.
//! TWO rep_a share ONE rep_b => two in-batch C2 target same slot (the hazard).
use dnx_core::{canonical_hash, normalize, DnxError, LOPath, Net, PortId, Proper, ΔK};
use dnx_sched::normalize_par;
use std::sync::Arc;

fn dp(i: u64, bits: u32) -> Result<LOPath, DnxError> {
    let mut p = LOPath::root();
    for b in (0..bits).rev() {
        p = if (i >> b) & 1 == 1 {
            p.extend_right()?
        } else {
            p.extend_left()?
        };
    }
    Ok(p)
}

type NetK = Net<Proper, ΔK>;
fn mkn(units: u64, bits: u32) -> Result<NetK, DnxError> {
    let mut n = NetK::new(units as u32 * 64 + 128);
    let lb = 3u16;
    let shared = n.alloc_rep_in(lb, 0, 0)?;
    let bb = dp(0, bits.max(1))?;
    n.connect(PortId::ERA, shared.aux0, bb.extend_left()?)?;
    n.connect(PortId::ERA, shared.aux1, bb.extend_right()?)?;
    let sp = shared.principal;
    for u in 0..units {
        let base = dp(u + 1, bits)?;
        // VARY la per unit so each rep_a computes a DIFFERENT b_mod (data=la, delta+=lb-la).
        // This is the adversarial case: aliased C2 writes to rep_b are NOT idempotent.
        let la = (u % 3) as u16; // 0,1,2 -> different merged data
        emit2(&mut n, &base, la, 5, sp, (u + 1) as u32)?;
    }
    let anchor = n.alloc_free(999_999)?;
    n.add_root(Arc::from("r"), anchor);
    Ok(n)
}

fn emit2(
    n: &mut NetK,
    base: &LOPath,
    la: u16,
    da: i16,
    repb_principal: PortId,
    tag: u32,
) -> Result<(), DnxError> {
    let rep_a = n.alloc_rep_in(la, da, da)?;
    n.connect(rep_a.aux0, repb_principal, base.clone())?;
    let efan = n.alloc_abs()?;
    n.connect(efan.aux0, rep_a.aux1, base.extend_left()?)?;
    let sink = n.alloc_free(tag * 16 + 1)?;
    n.connect(efan.aux1, sink, base.extend_left()?.extend_left()?)?;
    n.connect(
        PortId::ERA,
        efan.principal,
        base.extend_left()?.extend_right()?,
    )?;
    let gfan = n.alloc_abs()?;
    n.connect(gfan.aux0, rep_a.principal, base.extend_right()?)?;
    let gsink = n.alloc_free(tag * 16 + 2)?;
    n.connect(gfan.aux1, gsink, base.extend_right()?.extend_left()?)?;
    n.connect(
        PortId::ERA,
        gfan.principal,
        base.extend_right()?.extend_right()?,
    )?;
    Ok(())
}

#[test]
fn probe2() -> Result<(), DnxError> {
    for units in [2u64, 3, 4] {
        let bits = 64 - ((units + 1).max(2) - 1).leading_zeros();
        eprintln!("=== units={units} SEQ ===");
        let (seq, ss) = normalize(mkn(units, bits)?)?;
        eprintln!("SEQ i={} r4={}", ss.interactions, ss.r4_count);
        eprintln!("=== units={units} PAR2 ===");
        let (par, sp) = normalize_par(mkn(units, bits)?, 2)?;
        eprintln!("PAR i={} r4={}", sp.interactions, sp.r4_count);
        let rs = *seq.roots().get("r").unwrap();
        let rp = *par.roots().get("r").unwrap();
        let m = canonical_hash(&seq, rs)? == canonical_hash(&par, rp)?;
        eprintln!("units={units} HASH seq==par? {m}");
    }
    Ok(())
}
