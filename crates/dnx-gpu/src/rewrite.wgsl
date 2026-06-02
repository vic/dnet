// δ-net GPU rewrite kernel — R1-R7 dispatch (gpu.md settled design).
// Arena is read-only. Output per thread goes to out_buf (flat u32 array).
// CPU coordinator applies GpuOutput (connect/retire/new_agents) after readback.
//
// Slot layout (8 u32 per slot, matching Slot repr(C)):
//   [0]: tag(u8)|claim(u8)|pad(2B) packed as u32
//   [1]: generation (u32)
//   [2]: principal (u32 PortId)
//   [3]: aux0      (u32 PortId)
//   [4]: aux1      (u32 PortId)
//   [5]: data(u16)|delta0(i16) packed as u32
//   [6]: delta1(i16)|epoch(u16) packed as u32
//   [7]: pad (u32)
//
// GpuActivePair layout (8 u32 per pair):
//   [0]: p0 raw PortId
//   [1]: p1 raw PortId
//   [2]: lo_hi  (bits[127..96] of LOPath.hot)
//   [3]: lo_mid1 (bits[95..64])
//   [4]: lo_mid0 (bits[63..32])
//   [5]: lo_lo   (bits[31..0])
//   [6]: lo_len  (u32)
//   [7]: pad
//
// Out buffer per thread i (stride = 96 u32 = OUT_STRIDE):
//   [0]    : na_count
//   [1..4] : na_tag[0..3]
//   [5..8] : na_data[0..3]
//   [9..12]: na_d0[0..3]  (bitcast i32→u32)
//  [13..16]: na_d1[0..3]
//   [17]   : ret_count
//  [18..19]: retired[0..1]
//   [20]   : conn_count
//  [21..84]: conn[j][0..7] for j in 0..8: a_raw,b_raw,lo_hi,lo_mid1,lo_mid0,lo_lo,lo_len,pad
//   [85]   : er_count
//  [86..89]: erasers[0..3]
//   [90]   : has_link_direct
//   [91]   : link_a raw PortId
//   [92]   : link_b raw PortId
//  [93..95]: pad

const ERA_RAW: u32 = 2u;
const OUT_STRIDE: u32 = 96u;
const MAX_NA: u32 = 4u;

struct LO4 { hi: u32, m1: u32, m0: u32, lo: u32, len: u32 }

fn lo_extend(l: LO4, bit: u32) -> LO4 {
    var out = l;
    let n = l.len;
    // bit k goes at hot-limb position 127-k; distribute across 4 u32 chunks
    if n < 32u {
        out.hi |= bit << (31u - n);
    } else if n < 64u {
        out.m1 |= bit << (63u - n);
    } else if n < 96u {
        out.m0 |= bit << (95u - n);
    } else {
        out.lo |= bit << (127u - n);
    }
    out.len += 1u;
    return out;
}
fn lo_left(l: LO4) -> LO4  { return lo_extend(l, 0u); }
fn lo_right(l: LO4) -> LO4 { return lo_extend(l, 1u); }

fn port_is_era(p: u32) -> bool      { return ((p >> 1u) & 1u) == 1u; }
fn port_slot_idx(p: u32) -> u32     { return p >> 4u; }
fn port_kind(p: u32) -> u32         { return (p >> 2u) & 3u; }
fn make_port(slot: u32, kind: u32) -> u32 { return (slot << 4u) | (kind << 2u); }

fn tag_is_fan(t: u32) -> bool       { return (t & 0xCu) == 0x4u; }
fn tag_is_rep(t: u32) -> bool       { return (t & 0xCu) == 0x8u; }
fn tag_fan_is_abs(t: u32) -> bool   { return (t & 0x1u) != 0u; }

fn slot_tag(idx: u32)  -> u32 { return arena[idx * 8u] & 0xFFu; }
fn slot_aux0(idx: u32) -> u32 { return arena[idx * 8u + 3u]; }
fn slot_aux1(idx: u32) -> u32 { return arena[idx * 8u + 4u]; }
fn slot_data(idx: u32) -> u32 { return arena[idx * 8u + 5u] & 0xFFFFu; }

fn slot_d0(idx: u32) -> i32 {
    let raw = (arena[idx * 8u + 5u] >> 16u) & 0xFFFFu;
    return i32(raw) - i32(select(0u, 65536u, (raw & 0x8000u) != 0u));
}
fn slot_d1(idx: u32) -> i32 {
    let raw = arena[idx * 8u + 6u] & 0xFFFFu;
    return i32(raw) - i32(select(0u, 65536u, (raw & 0x8000u) != 0u));
}

fn add_level(level: u32, delta: i32) -> u32 {
    let v = i32(level) + delta;
    if v < 0 || v >= 16384 { return 0xFFFFu; }
    return u32(v);
}

@group(0) @binding(0) var<storage, read>       pairs:   array<u32>;
@group(0) @binding(1) var<storage, read>        arena:   array<u32>;
@group(0) @binding(2) var<storage, read_write>  out_buf: array<u32>;
@group(0) @binding(3) var<uniform>              params:  GpuParams;

struct GpuParams { base_slot: u32, n_pairs: u32, _p0: u32, _p1: u32 }

fn read_p0(i: u32) -> u32  { return pairs[i * 8u]; }
fn read_p1(i: u32) -> u32  { return pairs[i * 8u + 1u]; }
fn read_lo(i: u32) -> LO4 {
    return LO4(pairs[i*8u+2u], pairs[i*8u+3u], pairs[i*8u+4u], pairs[i*8u+5u], pairs[i*8u+6u]);
}

// na_alloc: reserves next new-agent slot, writes tag/data/d0/d1 into out_buf,
// returns (principal, aux0, aux1) raw PortIds.
fn na_alloc(ob: u32, k_ptr: ptr<function, u32>, slot_base: u32,
            tag: u32, data: u32, d0: i32, d1: i32) -> vec3<u32> {
    let k = *k_ptr;
    let slot = slot_base + k;
    out_buf[ob + 1u + k] = tag;
    out_buf[ob + 5u + k] = data;
    out_buf[ob + 9u + k] = bitcast<u32>(d0);
    out_buf[ob + 13u + k] = bitcast<u32>(d1);
    *k_ptr = k + 1u;
    return vec3<u32>(make_port(slot, 0u), make_port(slot, 1u), make_port(slot, 2u));
}

fn do_retire(ob: u32, rc: ptr<function, u32>, idx: u32) {
    let k = *rc;
    out_buf[ob + 18u + k] = idx;
    *rc = k + 1u;
}

fn do_connect(ob: u32, cc: ptr<function, u32>, a: u32, b: u32, l: LO4) {
    let k = *cc;
    let off = ob + 21u + k * 8u;
    out_buf[off]     = a;
    out_buf[off + 1u] = b;
    out_buf[off + 2u] = l.hi;
    out_buf[off + 3u] = l.m1;
    out_buf[off + 4u] = l.m0;
    out_buf[off + 5u] = l.lo;
    out_buf[off + 6u] = l.len;
    out_buf[off + 7u] = 0u;
    *cc = k + 1u;
}

fn do_eraser(ob: u32, ec: ptr<function, u32>, port: u32) {
    let k = *ec;
    out_buf[ob + 86u + k] = port;
    *ec = k + 1u;
}

@compute @workgroup_size(128)
fn rewrite_main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    if i >= params.n_pairs { return; }

    let p0 = read_p0(i);
    let p1 = read_p1(i);
    let lo = read_lo(i);
    let ob = i * OUT_STRIDE;                        // out_buf base for this thread
    let slot_base = params.base_slot + i * MAX_NA;  // pre-reserved slots for this thread

    var na_c: u32 = 0u;
    var ret_c: u32 = 0u;
    var conn_c: u32 = 0u;
    var er_c: u32 = 0u;

    // Zero new-agent fields (unused slots stay zeroed)
    for (var k: u32 = 0u; k < MAX_NA; k++) {
        out_buf[ob + 1u + k]  = 0u;
        out_buf[ob + 5u + k]  = 0u;
        out_buf[ob + 9u + k]  = 0u;
        out_buf[ob + 13u + k] = 0u;
    }
    out_buf[ob + 90u] = 0u; // no link_direct by default

    let e0 = port_is_era(p0);
    let e1 = port_is_era(p1);

    if e0 && e1 {
        // R1: era⊗era — no-op

    } else if e0 || e1 {
        // R2 (era⊗fan) or R3 (era⊗rep): retire live agent, erase its aux ports
        let live_p = select(p0, p1, e0);
        let live_idx = port_slot_idx(live_p);
        let ax0 = slot_aux0(live_idx);
        let ax1 = slot_aux1(live_idx);
        do_retire(ob, &ret_c, live_idx);
        do_eraser(ob, &er_c, ax0);
        do_eraser(ob, &er_c, ax1);
        do_connect(ob, &conn_c, ERA_RAW, ax0, lo_left(lo));
        do_connect(ob, &conn_c, ERA_RAW, ax1, lo_right(lo));

    } else {
        let s0i = port_slot_idx(p0);
        let s1i = port_slot_idx(p1);
        let t0 = slot_tag(s0i);
        let t1 = slot_tag(s1i);
        let f0 = tag_is_fan(t0);
        let f1 = tag_is_fan(t1);
        let r0 = tag_is_rep(t0);
        let r1 = tag_is_rep(t1);

        if f0 && f1 {
            // R4: fan⊗fan (β-reduction)
            let abs_p  = select(p1, p0, tag_fan_is_abs(t0));
            let app_p  = select(p0, p1, tag_fan_is_abs(t0));
            let absi   = port_slot_idx(abs_p);
            let appi   = port_slot_idx(app_p);
            let body   = slot_aux0(absi);
            let var_   = slot_aux1(absi);
            let res    = slot_aux0(appi);
            let arg    = slot_aux1(appi);
            do_retire(ob, &ret_c, absi);
            do_retire(ob, &ret_c, appi);
            if port_slot_idx(body) == absi && port_slot_idx(var_) == absi {
                // Identity self-loop: wire res↔arg without pair detection
                out_buf[ob + 90u] = 1u;
                out_buf[ob + 91u] = res;
                out_buf[ob + 92u] = arg;
            } else {
                do_connect(ob, &conn_c, body, res, lo_left(lo));
                do_connect(ob, &conn_c, var_, arg, lo_right(lo));
            }

        } else if (f0 && r1) || (r0 && f1) {
            // R5: fan⊗rep — C2/C3 already run by CPU coordinator before dispatch
            let fan_p  = select(p1, p0, f0);
            let rep_p  = select(p0, p1, f0);
            let fani   = port_slot_idx(fan_p);
            let repi   = port_slot_idx(rep_p);
            let ft     = slot_tag(fani);
            let is_abs = tag_fan_is_abs(ft);
            let fan_t  = select(0x04u, 0x05u, is_abs);
            let ra_t   = select(0x0Bu, 0x0Au, is_abs);
            let rb_t   = select(0x0Au, 0x0Bu, is_abs);
            let rdata  = slot_data(repi);
            let rd0    = slot_d0(repi);
            let rd1    = slot_d1(repi);
            let f0v = na_alloc(ob, &na_c, slot_base, fan_t, 0u, 0, 0);
            let f1v = na_alloc(ob, &na_c, slot_base, fan_t, 0u, 0, 0);
            let rav = na_alloc(ob, &na_c, slot_base, ra_t, rdata, rd0, rd1);
            let rbv = na_alloc(ob, &na_c, slot_base, rb_t, rdata, rd0, rd1);
            let ea  = slot_aux0(fani); let eb = slot_aux1(fani);
            let ec  = slot_aux0(repi); let ed = slot_aux1(repi);
            do_retire(ob, &ret_c, fani);
            do_retire(ob, &ret_c, repi);
            let lo_00 = lo_left(lo_left(lo));
            let lo_01 = lo_right(lo_left(lo));
            let ra_lo = select(lo_right(lo_right(lo)), lo_left(lo_right(lo)), is_abs);
            let rb_lo = select(lo_left(lo_right(lo)), lo_right(lo_right(lo)), is_abs);
            do_connect(ob, &conn_c, f0v.y, rav.y, lo);
            do_connect(ob, &conn_c, f0v.z, rbv.y, lo);
            do_connect(ob, &conn_c, f1v.y, rav.z, lo);
            do_connect(ob, &conn_c, f1v.z, rbv.z, lo);
            do_connect(ob, &conn_c, f0v.x, ec, lo_00);
            do_connect(ob, &conn_c, f1v.x, ed, lo_01);
            do_connect(ob, &conn_c, rav.x, ea, ra_lo);
            do_connect(ob, &conn_c, rbv.x, eb, rb_lo);

        } else if r0 && r1 {
            // R6 or R7: rep⊗rep — C2/C3 already run by CPU coordinator
            let d0v  = slot_data(s0i);
            let d1v  = slot_data(s1i);
            let d0_0 = slot_d0(s0i);
            let d0_1 = slot_d0(s1i);
            let d1_0 = slot_d1(s0i);
            let d1_1 = slot_d1(s1i);
            if d0v == d1v && d0_0 == d0_1 && d1_0 == d1_1 {
                // R6: annihilation
                do_retire(ob, &ret_c, s0i);
                do_retire(ob, &ret_c, s1i);
                do_connect(ob, &conn_c, slot_aux0(s0i), slot_aux0(s1i), lo_left(lo));
                do_connect(ob, &conn_c, slot_aux1(s0i), slot_aux1(s1i), lo_right(lo));
            } else {
                // R7: commutation (level adjustment)
                let hii  = select(s1i, s0i, d0v > d1v);
                let loi2 = select(s0i, s1i, d0v > d1v);
                let hi_d  = slot_data(hii);
                let lo_d  = slot_data(loi2);
                let hi_t  = slot_tag(hii) & 0xFu;
                let lo_t  = slot_tag(loi2) & 0xFu;
                let hi_d0 = slot_d0(hii); let hi_d1 = slot_d1(hii);
                let lo_d0 = slot_d0(loi2); let lo_d1 = slot_d1(loi2);
                let hc0 = na_alloc(ob, &na_c, slot_base, hi_t, add_level(hi_d, lo_d0), hi_d0, hi_d1);
                let hc1 = na_alloc(ob, &na_c, slot_base, hi_t, add_level(hi_d, lo_d1), hi_d0, hi_d1);
                let lc0 = na_alloc(ob, &na_c, slot_base, lo_t, lo_d, lo_d0, lo_d1);
                let lc1 = na_alloc(ob, &na_c, slot_base, lo_t, lo_d, lo_d0, lo_d1);
                let ha0 = slot_aux0(hii); let ha1 = slot_aux1(hii);
                let la0 = slot_aux0(loi2); let la1 = slot_aux1(loi2);
                do_retire(ob, &ret_c, hii);
                do_retire(ob, &ret_c, loi2);
                do_connect(ob, &conn_c, hc0.y, lc0.y, lo);
                do_connect(ob, &conn_c, hc0.z, lc1.y, lo);
                do_connect(ob, &conn_c, hc1.y, lc0.z, lo);
                do_connect(ob, &conn_c, hc1.z, lc1.z, lo);
                do_connect(ob, &conn_c, hc0.x, la0, lo_left(lo_left(lo)));
                do_connect(ob, &conn_c, hc1.x, la1, lo_left(lo_right(lo)));
                do_connect(ob, &conn_c, lc0.x, ha0, lo_right(lo_left(lo)));
                do_connect(ob, &conn_c, lc1.x, ha1, lo_right(lo_right(lo)));
            }
        }
        // else: unsupported combination → emit nothing (CPU coordinator handles stale/unknown)
    }

    out_buf[ob]       = na_c;
    out_buf[ob + 17u] = ret_c;
    out_buf[ob + 20u] = conn_c;
    out_buf[ob + 85u] = er_c;
}
