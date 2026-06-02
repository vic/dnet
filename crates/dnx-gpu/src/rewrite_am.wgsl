// δ-net amortized GPU kernel — R4 (Fan⊗Fan) direct arena writes.
// GPU writes connections directly to arena (read_write), no CPU apply per round.
// Supports multi-step CommandEncoder: input frontier → fire → output frontier.
// CPU only uploads once (initial arena + frontier) and reads back once at end.
//
// Binding layout:
//   0: frontier_in  — array<u32>, 8 u32 per pair (same layout as rewrite.wgsl pairs buf)
//   1: arena        — array<u32>, read_write, 8 u32 per slot
//   2: frontier_out — array<u32>, read_write, 8 u32 per pair (output pairs for next round)
//   3: counters     — array<atomic<u32>>: [0]=n_pairs_in, [1]=frontier_out_count, [2]=interactions

@group(0) @binding(0) var<storage, read>        frontier_in:  array<u32>;
@group(0) @binding(1) var<storage, read_write>  arena_am:     array<u32>;
@group(0) @binding(2) var<storage, read_write>  frontier_out: array<u32>;
@group(0) @binding(3) var<storage, read_write>  counters:     array<atomic<u32>>;

const MAX_FRONTIER_OUT: u32 = 1u << 20u; // 1M pairs max

// ---- port helpers (shared with rewrite.wgsl) ----
fn am_port_slot_idx(p: u32) -> u32   { return p >> 4u; }
fn am_port_kind(p: u32)    -> u32    { return (p >> 2u) & 3u; }
fn am_port_is_era(p: u32)  -> bool   { return ((p >> 1u) & 1u) == 1u; }
fn am_make_port(slot: u32, kind: u32) -> u32 { return (slot << 4u) | (kind << 2u); }

fn am_slot_tag(idx: u32)  -> u32 { return arena_am[idx * 8u] & 0xFFu; }
fn am_slot_aux0(idx: u32) -> u32 { return arena_am[idx * 8u + 3u]; }
fn am_slot_aux1(idx: u32) -> u32 { return arena_am[idx * 8u + 4u]; }

fn am_tag_is_fan(t: u32) -> bool { return (t & 0xCu) == 0x4u; }
fn am_tag_is_fan_abs(t: u32) -> bool { return (t & 0x1u) != 0u; }

// Write port p's connection field in arena to target.
// No atomics needed: pairs are disjoint, threads write to different slots.
fn am_write_port(p: u32, target: u32) {
    let s = am_port_slot_idx(p);
    let k = am_port_kind(p);
    if k == 0u { arena_am[s * 8u + 2u] = target; }
    else if k == 1u { arena_am[s * 8u + 3u] = target; }
    else { arena_am[s * 8u + 4u] = target; }
}

// Mark slot as retired (tag low byte = 0xFF = RETIRED).
fn am_retire(slot: u32) {
    arena_am[slot * 8u] = (arena_am[slot * 8u] & 0xFFFFFF00u) | 0xFFu;
}

// Emit a new active pair to frontier_out if both ports are real agent principals.
fn am_maybe_emit(a: u32, b: u32) {
    if am_port_kind(a) != 0u { return; }
    if am_port_kind(b) != 0u { return; }
    if am_port_is_era(a) || am_port_is_era(b) { return; }
    let ta = am_slot_tag(am_port_slot_idx(a));
    let tb = am_slot_tag(am_port_slot_idx(b));
    if ta == 0xFFu || tb == 0xFFu { return; } // retired
    if (!am_tag_is_fan(ta) && (ta & 0xCu) != 0x8u) { return; } // not agent
    if (!am_tag_is_fan(tb) && (tb & 0xCu) != 0x8u) { return; }
    let idx = atomicAdd(&counters[1], 1u);
    if idx >= MAX_FRONTIER_OUT { return; }
    frontier_out[idx * 8u]     = a;
    frontier_out[idx * 8u + 1u] = b;
    // LOPath: use root (all zeros) — sufficient for ΔL/R4-only nets
    frontier_out[idx * 8u + 2u] = 0u;
    frontier_out[idx * 8u + 3u] = 0u;
    frontier_out[idx * 8u + 4u] = 0u;
    frontier_out[idx * 8u + 5u] = 0u;
    frontier_out[idx * 8u + 6u] = 0u;
    frontier_out[idx * 8u + 7u] = 0u;
}

@compute @workgroup_size(128)
fn rewrite_am_main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    let n = atomicLoad(&counters[0]);
    if i >= n { return; }

    let p0 = frontier_in[i * 8u];
    let p1 = frontier_in[i * 8u + 1u];

    // Skip era ports (R1/R2/R3 — not handled in this amortized R4 kernel)
    if am_port_is_era(p0) || am_port_is_era(p1) { return; }

    let s0 = am_port_slot_idx(p0);
    let s1 = am_port_slot_idx(p1);
    let t0 = am_slot_tag(s0);
    let t1 = am_slot_tag(s1);

    if !am_tag_is_fan(t0) || !am_tag_is_fan(t1) {
        // R5/R6/R7 not handled in R4-only kernel — skip
        return;
    }

    // R4: fan⊗fan (β-reduction)
    let abs_p = select(p1, p0, am_tag_is_fan_abs(t0));
    let app_p = select(p0, p1, am_tag_is_fan_abs(t0));
    let absi  = am_port_slot_idx(abs_p);
    let appi  = am_port_slot_idx(app_p);

    let body = am_slot_aux0(absi);
    let var_ = am_slot_aux1(absi);
    let res  = am_slot_aux0(appi);
    let arg  = am_slot_aux1(appi);

    am_retire(absi);
    am_retire(appi);
    atomicAdd(&counters[2], 1u); // interaction count

    // Identity self-loop: abs body and var point back to abs itself
    if am_port_slot_idx(body) == absi {
        // Wire res↔arg directly
        am_write_port(res, arg);
        am_write_port(arg, res);
        am_maybe_emit(res, arg);
    } else {
        // General R4: body↔res, var↔arg
        am_write_port(body, res);
        am_write_port(res, body);
        am_write_port(var_, arg);
        am_write_port(arg, var_);
        am_maybe_emit(body, res);
        am_maybe_emit(var_, arg);
    }
}
