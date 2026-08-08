// [PROVER-fri-wgsl] — OUR FRI fold kernel. ADOPTED MATH, OUR SHADER:
// the fold algebra is breadstuffs' deployed hidingfri_fold_ext4.wgsl math
// (BabyBear Montgomery mmul, BabyBear^4 with X^4 = 11, the per-pair fold
// formula, bit-reversed halve-inv-power twiddles), written here from the
// math, not copied as a file, and carrying none of the Plonky3 stack.
//
// Substrate, said out loud: UNVERIFIED COMPUTE following the verified emit
// seam. This kernel must compute exactly fri.rs::fold (the CPU reference,
// vector-conformant to Loom/Proximity.lean's verified fold) — the gate is
// the exact-equality conformance test in tests/gpu_fold_conformance.rs,
// never a proof: there is no formal semantics of WGSL.
//
// Layout: the kernel works on BIT-REVERSED storage (pairs adjacent), the
// deployed convention. Per pair at working length L (round r):
//
//   folded = halve(lo + hi) + base_mul(mul(sub(lo, hi), beta), twiddle)
//
// with beta <- beta^2 each round and twiddle drawn from ONE shared table,
// halve_inv_powers_bitrev(log_n) in Montgomery form: the round-r table
// (1/2 * g_{n>>r}^{-bitrev j}) is exactly the first (n >> (r+1)) entries
// of the round-0 table, because bitrev_{L}(j) = 2*bitrev_{L-1}(j) for
// j < 2^{L-1} and g_{n/2} = g_n^2. Each thread owns one output element:
// it gathers its `arity` contiguous inputs and folds log_arity rounds
// locally. Host side bit-reverses in and out (fri.rs::bit_reverse_permute),
// so the buffer boundary is natural-order canonical u32 lanes.
//
// Montgomery form (a GPU optimization; canonical at the buffer boundary):
// x_mont = x * 2^32 mod P; mmul(a,b) = a*b*2^-32 mod P by 16-bit-split
// hi/lo products and the P^-1 (subtractive) reduction — P * MU = 1 mod 2^32,
// so the low words of a*b and ((a*b mod 2^32) * MU mod 2^32) * P cancel
// EXACTLY and the quotient is hi(ab) - hi(mP) with a single borrow test.

const P: u32 = 2013265921u;        // BabyBear, 2^31 - 2^27 + 1
const MU: u32 = 0x88000001u;       // P^{-1} mod 2^32 (P * MU = 1 mod 2^32)
const R2: u32 = 1172168163u;       // (2^32)^2 mod P — to_mont multiplier
const W_MONT: u32 = 939524073u;    // montgomery(11): the X^4 = 11 constant
const HALF_ONE: u32 = 0x3c000001u; // (P+1)/2 — the odd-case halve adjust
const MAX_ARITY: u32 = 32u;        // local fold window: log_arity <= 5

struct Params {
    n_out: u32,      // output length = n >> log_arity
    log_arity: u32,  // rounds to fold locally (1..=5)
    _pad0: u32,
    _pad1: u32,
    beta: vec4<u32>, // fold challenge, canonical lanes
}

@group(0) @binding(0) var<storage, read> src: array<vec4<u32>>;   // bitrev, canonical
@group(0) @binding(1) var<storage, read> twid: array<u32>;        // bitrev, Montgomery
@group(0) @binding(2) var<uniform> params: Params;
@group(0) @binding(3) var<storage, read_write> dst: array<vec4<u32>>; // bitrev, canonical

// ---- base field: 32-bit Montgomery arithmetic ----

// High 32 bits of the 64-bit product a*b, by 16-bit split (carry-exact).
fn mul_hi(a: u32, b: u32) -> u32 {
    let al = a & 0xffffu;
    let ah = a >> 16u;
    let bl = b & 0xffffu;
    let bh = b >> 16u;
    let ll = al * bl;
    let mid = al * bh + (ll >> 16u);        // < 2^32 - 2^16: no overflow
    let mid2 = ah * bl + (mid & 0xffffu);   // likewise
    return ah * bh + (mid >> 16u) + (mid2 >> 16u);
}

// Montgomery multiply: a*b*2^-32 mod P, inputs/outputs in [0, P).
fn mmul(a: u32, b: u32) -> u32 {
    let prod_lo = a * b; // wrapping = mod 2^32
    let prod_hi = mul_hi(a, b);
    let m = prod_lo * MU;
    let u_hi = mul_hi(m, P);
    // low words cancel exactly (P*MU = 1 mod 2^32): quotient is the hi diff
    let r = prod_hi - u_hi;
    return select(r, r + P, prod_hi < u_hi);
}

fn addp(a: u32, b: u32) -> u32 {
    let s = a + b; // a, b < P so a+b < 2P < 2^32
    return select(s, s - P, s >= P);
}

fn subp(a: u32, b: u32) -> u32 {
    return select(a - b, a - b + P, a < b);
}

// x/2 mod P: even shifts; odd is (x + P)/2 = (x >> 1) + (P+1)/2.
fn halvep(x: u32) -> u32 {
    return select(x >> 1u, (x >> 1u) + HALF_ONE, (x & 1u) == 1u);
}

fn to_mont(x: u32) -> u32 {
    return mmul(x, R2);
}

fn from_mont(x: u32) -> u32 {
    return mmul(x, 1u);
}

// ---- BabyBear^4 = BabyBear[X]/(X^4 - 11), lanes x..w = c0..c3 ----

fn ext_to_mont(a: vec4<u32>) -> vec4<u32> {
    return vec4<u32>(to_mont(a.x), to_mont(a.y), to_mont(a.z), to_mont(a.w));
}

fn ext_from_mont(a: vec4<u32>) -> vec4<u32> {
    return vec4<u32>(from_mont(a.x), from_mont(a.y), from_mont(a.z), from_mont(a.w));
}

fn ext_add(a: vec4<u32>, b: vec4<u32>) -> vec4<u32> {
    return vec4<u32>(addp(a.x, b.x), addp(a.y, b.y), addp(a.z, b.z), addp(a.w, b.w));
}

fn ext_sub(a: vec4<u32>, b: vec4<u32>) -> vec4<u32> {
    return vec4<u32>(subp(a.x, b.x), subp(a.y, b.y), subp(a.z, b.z), subp(a.w, b.w));
}

fn ext_halve(a: vec4<u32>) -> vec4<u32> {
    return vec4<u32>(halvep(a.x), halvep(a.y), halvep(a.z), halvep(a.w));
}

fn ext_base_mul(a: vec4<u32>, s: u32) -> vec4<u32> {
    return vec4<u32>(mmul(a.x, s), mmul(a.y, s), mmul(a.z, s), mmul(a.w, s));
}

// The adopted X^4 = 11 product (same formula field4.rs::Ext4::mul carries,
// tied on the Lean side by ext4Mul_correct), in Montgomery lanes.
fn ext_mul(a: vec4<u32>, b: vec4<u32>) -> vec4<u32> {
    let c0 = addp(
        mmul(a.x, b.x),
        mmul(W_MONT, addp(addp(mmul(a.y, b.w), mmul(a.z, b.z)), mmul(a.w, b.y))),
    );
    let c1 = addp(
        addp(mmul(a.x, b.y), mmul(a.y, b.x)),
        mmul(W_MONT, addp(mmul(a.z, b.w), mmul(a.w, b.z))),
    );
    let c2 = addp(
        addp(addp(mmul(a.x, b.z), mmul(a.y, b.y)), mmul(a.z, b.x)),
        mmul(W_MONT, mmul(a.w, b.w)),
    );
    let c3 = addp(
        addp(addp(mmul(a.x, b.w), mmul(a.y, b.z)), mmul(a.z, b.y)),
        mmul(a.w, b.x),
    );
    return vec4<u32>(c0, c1, c2, c3);
}

// ---- the fold ----

@compute @workgroup_size(256)
fn fold(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    if (i >= params.n_out) {
        return;
    }
    let arity = 1u << params.log_arity;

    // gather this output's `arity` contiguous (bitrev layout) inputs
    var vals: array<vec4<u32>, 32>; // MAX_ARITY
    for (var m = 0u; m < arity; m = m + 1u) {
        vals[m] = ext_to_mont(src[i * arity + m]);
    }

    var beta = ext_to_mont(params.beta);
    var len = arity;
    while (len > 1u) {
        let h = len >> 1u;
        for (var j = 0u; j < h; j = j + 1u) {
            let lo = vals[2u * j];
            let hi = vals[2u * j + 1u];
            let tw = twid[i * h + j]; // shared-prefix bitrev twiddle table
            vals[j] = ext_add(
                ext_halve(ext_add(lo, hi)),
                ext_base_mul(ext_mul(ext_sub(lo, hi), beta), tw),
            );
        }
        beta = ext_mul(beta, beta);
        len = h;
    }

    dst[i] = ext_from_mont(vals[0]);
}
