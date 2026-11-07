// Work 9104 on CUDA: the heavy loops of the Tower256 additive-FRI prover.
//
// - cSHAKE256 Merkle leaves (66 B) and nodes (131 B): one Keccak-f[1600] each, from the
//   customization block's state absorbed once on the host (the "midstate").
// - Tower256 arithmetic in the Fan-Paar coordinates of prover/src/binary_tower_256.rs:
//   Karatsuba (three products per level) from T_8 down to T_3 = GF(2^8), where products use
//   log/exp tables in shared memory; the tables are built on the device from the bit-level
//   recursion (`init_tables`). Inversion by the tower norm, N(a0 + a1 y) = a0^2 + a0 a1 g + a1^2.
// - The Gao-Mateer additive FFT pieces (scale, Taylor step, deinterleave, butterfly), the fold,
//   subspace spans, and the final interpolation (one thread).
//
// Element layout: 4 little-endian u64 limbs, exactly Tower256::limbs. Digests: 4 u64, the
// 32 output bytes little-endian. Every kernel takes its element count n last.
//
// Built two ways: by nvcc (-arch=sm_75 and up) for the device, and as host C++ with
// -DHOST_EMU (every kernel a loop over i) so the Python host can be tested without a GPU.
#ifdef __CUDACC_RTC__
typedef unsigned char uint8_t;
typedef unsigned int uint32_t;
#else
#include <stdint.h>
#endif

typedef unsigned long long u64;

#ifdef HOST_EMU
#define DEV static inline
#define KERNEL extern "C"
#define KBEGIN(n) for (u64 i = 0; i < (u64)(n); ++i) {
#define KEND }
#define TABLES const uint8_t* s_log = g_log; const uint8_t* s_exp = g_exp; const uint8_t* s_gen = g_gen;
#define GLOBAL_TABLE static
#else
#define DEV __device__ __forceinline__
#define KERNEL extern "C" __global__
#define KBEGIN(n) { u64 i = (u64)blockIdx.x * blockDim.x + threadIdx.x; if (i < (u64)(n)) {
#define KEND } }
#define TABLES                                                                           \
    __shared__ uint8_t s_log[256], s_exp[512], s_gen[256];                               \
    for (int j = threadIdx.x; j < 512; j += blockDim.x) {                                \
        s_exp[j] = g_exp[j];                                                             \
        if (j < 256) { s_log[j] = g_log[j]; s_gen[j] = g_gen[j]; }                       \
    }                                                                                    \
    __syncthreads();
#define GLOBAL_TABLE __device__
#endif

#ifdef HOST_EMU
#define FULL_KERNEL extern "C" void
#define FULL_TABLES Full t = {g_prod};
#define GS_BEGIN(n) for (u64 i = 0; i < (u64)(n); ++i) {
#define GS_END }
#else
#define FULL_KERNEL extern "C" __global__ void __launch_bounds__(1024, 1)
#define FULL_TABLES                                                                      \
    extern __shared__ uint4 s_prod4[];                                                   \
    for (int j = threadIdx.x; j < 4096; j += blockDim.x) s_prod4[j] = ((const uint4*)g_prod)[j]; \
    __syncthreads();                                                                     \
    Full t = {(const uint8_t*)s_prod4};
#define GS_BEGIN(n) for (u64 i = (u64)blockIdx.x * blockDim.x + threadIdx.x; i < (u64)(n); i += (u64)gridDim.x * blockDim.x) {
#define GS_END }
#endif

GLOBAL_TABLE uint8_t g_log[256];
GLOBAL_TABLE uint8_t g_exp[512];
GLOBAL_TABLE uint8_t g_gen[256];
GLOBAL_TABLE uint8_t g_prod[65536];

// ------------------------------------------------------------------------------------------
// Bit-level reference recursion (binary_tower_256.rs mul_small / mul_by_generator_small), used
// only to build the tables.

DEV uint32_t bits_gen(int level, uint32_t v);
DEV uint32_t bits_mul(int level, uint32_t a, uint32_t b) {
    if (level == 0) return a & b & 1u;
    int child = level - 1, w = 1 << child;
    uint32_t mask = (1u << w) - 1u;
    uint32_t a0 = a & mask, a1 = (a >> w) & mask, b0 = b & mask, b1 = (b >> w) & mask;
    uint32_t p0 = bits_mul(child, a0, b0), p1 = bits_mul(child, a1, b1);
    uint32_t mixed = bits_mul(child, a0 ^ a1, b0 ^ b1) ^ p0 ^ p1;
    uint32_t pc = child == 0 ? p1 : bits_gen(child, p1);
    return (p0 ^ p1) | ((mixed ^ pc) << w);
}
DEV uint32_t bits_gen(int level, uint32_t v) {
    int child = level - 1, w = 1 << child;
    uint32_t mask = (1u << w) - 1u;
    uint32_t lo = v & mask, hi = (v >> w) & mask;
    uint32_t rh = child == 0 ? (lo ^ hi) : (lo ^ bits_gen(child, hi));
    return hi | (rh << w);
}

KERNEL void init_tables(u64 n) {
    KBEGIN(n)
    if (i == 0) {
        for (int x = 0; x < 256; ++x) g_gen[x] = (uint8_t)bits_gen(3, (uint32_t)x);
        // The smallest generator of T_3^*.
        uint32_t g = 2;
        for (; g < 256; ++g) {
            uint32_t x = 1;
            int e = 1;
            for (; e <= 255; ++e) {
                x = bits_mul(3, x, g);
                if (x == 1) break;
            }
            if (e == 255) break;
        }
        uint32_t x = 1;
        for (int e = 0; e < 510; ++e) {
            g_exp[e] = (uint8_t)x;
            if (e < 255) g_log[x] = (uint8_t)e;
            x = bits_mul(3, x, g);
        }
        g_exp[510] = g_exp[0];
        g_exp[511] = g_exp[1];
        g_log[0] = 0;
    }
    KEND
}

// g_prod[a * 256 + b] = a b in T_3, from the log/exp tables (run after init_tables).
KERNEL void init_prod(u64 n) {
    KBEGIN(n)
    uint32_t a = (uint32_t)(i >> 8), b = (uint32_t)(i & 255);
    g_prod[i] = (a && b) ? g_exp[g_log[a] + g_log[b]] : 0;
    KEND
}

// ------------------------------------------------------------------------------------------
// Packed tower arithmetic. T_3: byte, T_4: u16, T_5: u32, T_6: 2 words, T_7: 4, T_8: 8.

struct Tabs {
    const uint8_t* log;
    const uint8_t* exp;
    const uint8_t* gen;
};

DEV uint32_t mul3(const Tabs& t, uint32_t a, uint32_t b) {
    uint32_t r = t.exp[t.log[a] + t.log[b]];
    return (a && b) ? r : 0u;
}
DEV uint32_t gen3(const Tabs& t, uint32_t x) { return t.gen[x]; }
DEV uint32_t inv3(const Tabs& t, uint32_t a) { return a ? t.exp[255 - t.log[a]] : 0u; }

// The full GF(2^8) product table (64 KiB, dynamic shared memory): one load per product;
// y_2 = 0x10 (bit 2^2 of T_3), so gen3(x) = x * 0x10.
// (Products only: the table fills an sm_75 SM's 64 KiB, so no inversion through it.)
struct Full {
    const uint8_t* prod;
};
DEV uint32_t mul3(const Full& t, uint32_t a, uint32_t b) { return t.prod[(a << 8) | b]; }
DEV uint32_t gen3(const Full& t, uint32_t x) { return t.prod[(x << 8) | 0x10u]; }
template <class T> DEV uint32_t gen4(const T& t, uint32_t x) {  // T_4 times y_3
    uint32_t lo = x & 0xffu, hi = x >> 8;
    return hi | ((lo ^ gen3(t, hi)) << 8);
}
template <class T> DEV uint32_t mul4(const T& t, uint32_t a, uint32_t b) {
    uint32_t a0 = a & 0xffu, a1 = a >> 8, b0 = b & 0xffu, b1 = b >> 8;
    uint32_t p0 = mul3(t, a0, b0), p1 = mul3(t, a1, b1);
    uint32_t mixed = mul3(t, a0 ^ a1, b0 ^ b1) ^ p0 ^ p1;
    return (p0 ^ p1) | ((mixed ^ gen3(t, p1)) << 8);
}
template <class T> DEV uint32_t gen5(const T& t, uint32_t x) {  // T_5 times y_4
    uint32_t lo = x & 0xffffu, hi = x >> 16;
    return hi | ((lo ^ gen4(t, hi)) << 16);
}
template <class T> DEV uint32_t mul5(const T& t, uint32_t a, uint32_t b) {
    uint32_t a0 = a & 0xffffu, a1 = a >> 16, b0 = b & 0xffffu, b1 = b >> 16;
    uint32_t p0 = mul4(t, a0, b0), p1 = mul4(t, a1, b1);
    uint32_t mixed = mul4(t, a0 ^ a1, b0 ^ b1) ^ p0 ^ p1;
    return (p0 ^ p1) | ((mixed ^ gen4(t, p1)) << 16);
}
// T_6: r[0] low word, r[1] high word.
template <class T> DEV void gen6(const T& t, const uint32_t* x, uint32_t* r) {
    uint32_t lo = x[0], hi = x[1];
    r[0] = hi;
    r[1] = lo ^ gen5(t, hi);
}
template <class T> DEV void mul6(const T& t, const uint32_t* a, const uint32_t* b, uint32_t* r) {
    uint32_t p0 = mul5(t, a[0], b[0]), p1 = mul5(t, a[1], b[1]);
    uint32_t mixed = mul5(t, a[0] ^ a[1], b[0] ^ b[1]) ^ p0 ^ p1;
    r[0] = p0 ^ p1;
    r[1] = mixed ^ gen5(t, p1);
}
template <class T> DEV void gen7(const T& t, const uint32_t* x, uint32_t* r) {
    uint32_t g[2];
    gen6(t, x + 2, g);
    r[0] = x[2];
    r[1] = x[3];
    r[2] = x[0] ^ g[0];
    r[3] = x[1] ^ g[1];
}
template <class T> DEV void mul7(const T& t, const uint32_t* a, const uint32_t* b, uint32_t* r) {
    uint32_t p0[2], p1[2], m[2], sa[2] = {a[0] ^ a[2], a[1] ^ a[3]}, sb[2] = {b[0] ^ b[2], b[1] ^ b[3]}, g[2];
    mul6(t, a, b, p0);
    mul6(t, a + 2, b + 2, p1);
    mul6(t, sa, sb, m);
    gen6(t, p1, g);
    r[0] = p0[0] ^ p1[0];
    r[1] = p0[1] ^ p1[1];
    r[2] = m[0] ^ p0[0] ^ p1[0] ^ g[0];
    r[3] = m[1] ^ p0[1] ^ p1[1] ^ g[1];
}
template <class T> DEV void mul8(const T& t, const uint32_t* a, const uint32_t* b, uint32_t* r) {
    uint32_t p0[4], p1[4], m[4], sa[4], sb[4], g[4];
    for (int k = 0; k < 4; ++k) { sa[k] = a[k] ^ a[k + 4]; sb[k] = b[k] ^ b[k + 4]; }
    mul7(t, a, b, p0);
    mul7(t, a + 4, b + 4, p1);
    mul7(t, sa, sb, m);
    gen7(t, p1, g);
    for (int k = 0; k < 4; ++k) {
        r[k] = p0[k] ^ p1[k];
        r[k + 4] = m[k] ^ p0[k] ^ p1[k] ^ g[k];
    }
}

// Inverses by the norm; zero maps to zero (callers test for zero).
template <class T> DEV uint32_t inv4(const T& t, uint32_t a) {
    uint32_t a0 = a & 0xffu, a1 = a >> 8, ga1 = gen3(t, a1);
    uint32_t n = mul3(t, a0, a0) ^ mul3(t, a0, ga1) ^ mul3(t, a1, a1);
    uint32_t ni = inv3(t, n);
    return mul3(t, a0 ^ ga1, ni) | (mul3(t, a1, ni) << 8);
}
template <class T> DEV uint32_t inv5(const T& t, uint32_t a) {
    uint32_t a0 = a & 0xffffu, a1 = a >> 16, ga1 = gen4(t, a1);
    uint32_t n = mul4(t, a0, a0) ^ mul4(t, a0, ga1) ^ mul4(t, a1, a1);
    uint32_t ni = inv4(t, n);
    return mul4(t, a0 ^ ga1, ni) | (mul4(t, a1, ni) << 16);
}
template <class T> DEV void inv6(const T& t, const uint32_t* a, uint32_t* r) {
    uint32_t a0 = a[0], a1 = a[1], ga1 = gen5(t, a1);
    uint32_t n = mul5(t, a0, a0) ^ mul5(t, a0, ga1) ^ mul5(t, a1, a1);
    uint32_t ni = inv5(t, n);
    r[0] = mul5(t, a0 ^ ga1, ni);
    r[1] = mul5(t, a1, ni);
}
template <class T> DEV void inv7(const T& t, const uint32_t* a, uint32_t* r) {
    uint32_t ga1[2], x[2], y[2], z[2], n[2], ni[2], s[2];
    gen6(t, a + 2, ga1);
    mul6(t, a, a, x);
    mul6(t, a, ga1, y);
    mul6(t, a + 2, a + 2, z);
    n[0] = x[0] ^ y[0] ^ z[0];
    n[1] = x[1] ^ y[1] ^ z[1];
    inv6(t, n, ni);
    s[0] = a[0] ^ ga1[0];
    s[1] = a[1] ^ ga1[1];
    mul6(t, s, ni, r);
    mul6(t, a + 2, ni, r + 2);
}
template <class T> DEV void inv8(const T& t, const uint32_t* a, uint32_t* r) {
    uint32_t ga1[4], x[4], y[4], z[4], n[4], ni[4], s[4];
    gen7(t, a + 4, ga1);
    mul7(t, a, a, x);
    mul7(t, a, ga1, y);
    mul7(t, a + 4, a + 4, z);
    for (int k = 0; k < 4; ++k) n[k] = x[k] ^ y[k] ^ z[k];
    inv7(t, n, ni);
    for (int k = 0; k < 4; ++k) s[k] = a[k] ^ ga1[k];
    mul7(t, s, ni, r);
    mul7(t, a + 4, ni, r + 4);
}

DEV void load8(const u64* p, uint32_t* w) {
    for (int k = 0; k < 4; ++k) { u64 v = p[k]; w[2 * k] = (uint32_t)v; w[2 * k + 1] = (uint32_t)(v >> 32); }
}
DEV void store8(u64* p, const uint32_t* w) {
    for (int k = 0; k < 4; ++k) p[k] = (u64)w[2 * k] | ((u64)w[2 * k + 1] << 32);
}
DEV void xor8(uint32_t* a, const uint32_t* b) {
    for (int k = 0; k < 8; ++k) a[k] ^= b[k];
}
DEV bool zero8(const uint32_t* a) {
    uint32_t o = 0;
    for (int k = 0; k < 8; ++k) o |= a[k];
    return o == 0;
}

// ------------------------------------------------------------------------------------------
// Field kernels.

// out[i] = a[i] * b[i] (b_stride 0: one scalar b).
KERNEL void t256_mul(const u64* a, const u64* b, u64* out, u64 b_stride, u64 n) {
    TABLES
    Tabs t = {s_log, s_exp, s_gen};
    KBEGIN(n)
    uint32_t x[8], y[8], r[8];
    load8(a + 4 * i, x);
    load8(b + 4 * i * b_stride, y);
    mul8(t, x, y, r);
    store8(out + 4 * i, r);
    KEND
}

KERNEL void t256_inv(const u64* a, u64* out, u64 n) {
    TABLES
    Tabs t = {s_log, s_exp, s_gen};
    KBEGIN(n)
    uint32_t x[8], r[8];
    load8(a + 4 * i, x);
    inv8(t, x, r);
    store8(out + 4 * i, r);
    KEND
}

// out[i] = x[i]^2 + p * x[i] (the round map y -> y^2 + p y), p one scalar.
KERNEL void t256_pivot_map(const u64* x, const u64* p, u64* out, u64 n) {
    TABLES
    Tabs t = {s_log, s_exp, s_gen};
    KBEGIN(n)
    uint32_t a[8], b[8], s[8], r[8];
    load8(x + 4 * i, a);
    load8(p, b);
    mul8(t, a, a, s);
    mul8(t, b, a, r);
    xor8(r, s);
    store8(out + 4 * i, r);
    KEND
}

// out[i] = base^i for i < n, as hi[i >> h] * lo[i & (2^h - 1)] where lo[j] = base^j,
// hi[j] = base^(j 2^h) are built by `t256_pow_small`.
KERNEL void t256_pow_small(const u64* base, u64* out, u64 stride_log, u64 n) {
    TABLES
    Tabs t = {s_log, s_exp, s_gen};
    KBEGIN(n)
    uint32_t b[8], acc[8] = {1, 0, 0, 0, 0, 0, 0, 0}, tmp[8];
    load8(base, b);
    u64 e = i << stride_log;
    while (e) {
        if (e & 1) { mul8(t, acc, b, tmp); for (int k = 0; k < 8; ++k) acc[k] = tmp[k]; }
        mul8(t, b, b, tmp);
        for (int k = 0; k < 8; ++k) b[k] = tmp[k];
        e >>= 1;
    }
    store8(out + 4 * i, acc);
    KEND
}
KERNEL void t256_pow_combine(const u64* lo, const u64* hi, u64* out, u64 h, u64 n) {
    TABLES
    Tabs t = {s_log, s_exp, s_gen};
    KBEGIN(n)
    uint32_t x[8], y[8], r[8];
    load8(lo + 4 * (i & ((1ull << h) - 1)), x);
    load8(hi + 4 * (i >> h), y);
    mul8(t, x, y, r);
    store8(out + 4 * i, r);
    KEND
}

// out[i] = offset + sum_{bit b of i} basis[b], n = 2^k.
KERNEL void t256_span(const u64* offset, const u64* basis, u64* out, u64 n) {
    KBEGIN(n)
    u64 r0 = offset[0], r1 = offset[1], r2 = offset[2], r3 = offset[3];
    for (int b = 0; (1ull << b) <= i; ++b) {
        if (i >> b & 1) { r0 ^= basis[4 * b]; r1 ^= basis[4 * b + 1]; r2 ^= basis[4 * b + 2]; r3 ^= basis[4 * b + 3]; }
    }
    out[4 * i] = r0; out[4 * i + 1] = r1; out[4 * i + 2] = r2; out[4 * i + 3] = r3;
    KEND
}

// ------------------------------------------------------------------------------------------
// Additive FFT pieces (prover/src/tower256_fri_fast.rs eval_subspace).

// out[g] = a[g] * powers[g mod bsz].
KERNEL void ntt_scale(const u64* a, const u64* powers, u64* out, u64 bsz, u64 n) {
    TABLES
    Tabs t = {s_log, s_exp, s_gen};
    KBEGIN(n)
    uint32_t x[8], y[8], r[8];
    load8(a + 4 * i, x);
    load8(powers + 4 * (i % bsz), y);
    mul8(t, x, y, r);
    store8(out + 4 * i, r);
    KEND
}

// One Taylor step on every sub-block of size s: f2 += f3, then f1 += f2 (q = s/4).
// n = (total / s) * q threads.
KERNEL void ntt_taylor_step(u64* f, u64 s, u64 n) {
    KBEGIN(n)
    u64 q = s >> 2, blk = i / q, j = i % q, base = blk * s;
    u64* f1 = f + 4 * (base + q + j);
    u64* f2 = f + 4 * (base + 2 * q + j);
    const u64* f3 = f + 4 * (base + 3 * q + j);
    for (int k = 0; k < 4; ++k) { u64 v = f2[k] ^ f3[k]; f2[k] = v; f1[k] ^= v; }
    KEND
}

// out block = [even entries | odd entries] of in block (size bsz); n = total / 2 threads.
KERNEL void ntt_deinterleave(const u64* in, u64* out, u64 bsz, u64 n) {
    KBEGIN(n)
    u64 h = bsz >> 1, blk = i / h, j = i % h, base = blk * bsz;
    for (int k = 0; k < 4; ++k) {
        out[4 * (base + j) + k] = in[4 * (base + 2 * j) + k];
        out[4 * (base + h + j) + k] = in[4 * (base + 2 * j + 1) + k];
    }
    KEND
}

// out[i] = a[i / leaf_size].
KERNEL void ntt_fill(const u64* a, u64* out, u64 leaf_size, u64 n) {
    KBEGIN(n)
    for (int k = 0; k < 4; ++k) out[4 * i + k] = a[4 * (i / leaf_size) + k];
    KEND
}

// out[p] = Horner(a[p*len .. (p+1)*len], s): the depth where the basis runs out first.
KERNEL void ntt_horner_blocks(const u64* a, const u64* s, u64* out, u64 len, u64 n) {
    TABLES
    Tabs t = {s_log, s_exp, s_gen};
    KBEGIN(n)
    uint32_t x[8], acc[8] = {0}, tmp[8], c[8];
    load8(s, x);
    for (u64 j = len; j-- > 0;) {
        mul8(t, x, acc, tmp);
        load8(a + 4 * (i * len + j), c);
        xor8(tmp, c);
        for (int k = 0; k < 8; ++k) acc[k] = tmp[k];
    }
    store8(out + 4 * i, acc);
    KEND
}

// out[i] = Horner(coeffs[0..len], xs[i]): the dependent-basis fallback of the encode.
KERNEL void horner_points(const u64* coeffs, const u64* xs, u64* out, u64 len, u64 n) {
    TABLES
    Tabs t = {s_log, s_exp, s_gen};
    KBEGIN(n)
    uint32_t x[8], acc[8] = {0}, tmp[8], c[8];
    load8(xs + 4 * i, x);
    for (u64 j = len; j-- > 0;) {
        mul8(t, x, acc, tmp);
        load8(coeffs + 4 * j, c);
        xor8(tmp, c);
        for (int k = 0; k < 8; ++k) acc[k] = tmp[k];
    }
    store8(out + 4 * i, acc);
    KEND
}

// Pair g: block = g / h, j = g mod h (h = size / 2); e = G0 + z[j] G1, dst = (e, e + G1).
KERNEL void ntt_butterfly(const u64* src, const u64* z, u64* dst, u64 size, u64 n) {
    TABLES
    Tabs t = {s_log, s_exp, s_gen};
    KBEGIN(n)
    u64 h = size >> 1, blk = i / h, j = i % h, base = blk * size;
    uint32_t g0[8], g1[8], zz[8], e[8];
    load8(src + 4 * (base + j), g0);
    load8(src + 4 * (base + h + j), g1);
    load8(z + 4 * j, zz);
    mul8(t, zz, g1, e);
    xor8(e, g0);
    store8(dst + 4 * (base + 2 * j), e);
    xor8(e, g1);
    store8(dst + 4 * (base + 2 * j + 1), e);
    KEND
}

// next[k] = w[k] + c[k] (w[k] + w[k + half]), n = half.
KERNEL void fri_fold(const u64* w, const u64* c, u64* next, u64 n) {
    TABLES
    Tabs t = {s_log, s_exp, s_gen};
    KBEGIN(n)
    uint32_t l[8], r[8], cc[8], p[8];
    load8(w + 4 * i, l);
    load8(w + 4 * (i + n), r);
    load8(c + 4 * i, cc);
    xor8(r, l);
    mul8(t, cc, r, p);
    xor8(p, l);
    store8(next + 4 * i, p);
    KEND
}

// Final polynomial of proof i (one thread each): Gauss-Jordan through (xs[r], ys[i * ys_stride + r]),
// r < d <= 16, then its values at the last level's domain (dom, last_size points, shared).
// status[i] = 1 when singular. Coefficients at coeffs + 4 d i, values at vals + 4 last_size i.
#define MAXD 16
KERNEL void fri_final(const u64* xs, const u64* ys0, const u64* dom, u64* coeffs0, u64* vals0, u64* status0,
                      u64 d, u64 last_size, u64 ys_stride, u64 n) {
    TABLES
    Tabs t = {s_log, s_exp, s_gen};
    KBEGIN(n)
    const u64* ys = ys0 + 4 * ys_stride * i;
    u64* coeffs = coeffs0 + 4 * d * i;
    u64* vals = vals0 + 4 * last_size * i;
    u64* status = status0 + i;
    uint32_t rows[MAXD][MAXD + 1][8];
    status[0] = 0;
    for (u64 r = 0; r < d; ++r) {
        uint32_t x[8], p[8] = {1, 0, 0, 0, 0, 0, 0, 0}, tmp[8];
        load8(xs + 4 * r, x);
        for (u64 c = 0; c < d; ++c) {
            for (int k = 0; k < 8; ++k) rows[r][c][k] = p[k];
            mul8(t, p, x, tmp);
            for (int k = 0; k < 8; ++k) p[k] = tmp[k];
        }
        load8(ys + 4 * r, rows[r][d]);
    }
    for (u64 col = 0; col < d && status[0] == 0; ++col) {
        u64 piv = col;
        while (piv < d && zero8(rows[piv][col])) ++piv;
        if (piv == d) { status[0] = 1; break; }
        if (piv != col) {
            for (u64 c = 0; c <= d; ++c) for (int k = 0; k < 8; ++k) {
                uint32_t v = rows[piv][c][k]; rows[piv][c][k] = rows[col][c][k]; rows[col][c][k] = v;
            }
        }
        uint32_t inv[8], tmp[8];
        inv8(t, rows[col][col], inv);
        for (u64 c = 0; c <= d; ++c) {
            mul8(t, rows[col][c], inv, tmp);
            for (int k = 0; k < 8; ++k) rows[col][c][k] = tmp[k];
        }
        for (u64 r = 0; r < d; ++r) {
            if (r == col || zero8(rows[r][col])) continue;
            uint32_t f[8];
            for (int k = 0; k < 8; ++k) f[k] = rows[r][col][k];
            for (u64 c = 0; c <= d; ++c) {
                mul8(t, f, rows[col][c], tmp);
                xor8(rows[r][c], tmp);
            }
        }
    }
    if (status[0] == 0) {
        for (u64 c = 0; c < d; ++c) store8(coeffs + 4 * c, rows[c][d]);
        for (u64 p = 0; p < last_size; ++p) {
            uint32_t x[8], acc[8] = {0}, tmp[8];
            load8(dom + 4 * p, x);
            for (u64 c = d; c-- > 0;) {
                mul8(t, x, acc, tmp);
                xor8(tmp, rows[c][d]);
                for (int k = 0; k < 8; ++k) acc[k] = tmp[k];
            }
            store8(vals + 4 * p, acc);
        }
    }
    KEND
}

// ------------------------------------------------------------------------------------------
// Keccak-f[1600], 64-bit lanes.

#ifdef HOST_EMU
static const u64 RC[24] = {
#else
__constant__ u64 RC[24] = {
#endif
    0x0000000000000001ull, 0x0000000000008082ull, 0x800000000000808aull, 0x8000000080008000ull,
    0x000000000000808bull, 0x0000000080000001ull, 0x8000000080008081ull, 0x8000000000008009ull,
    0x000000000000008aull, 0x0000000000000088ull, 0x0000000080008009ull, 0x000000008000000aull,
    0x000000008000808bull, 0x800000000000008bull, 0x8000000000008089ull, 0x8000000000008003ull,
    0x8000000000008002ull, 0x8000000000000080ull, 0x000000000000800aull, 0x800000008000000aull,
    0x8000000080008081ull, 0x8000000000008080ull, 0x0000000080000001ull, 0x8000000080008008ull};

#define ROTL(x, s) (((x) << (s)) | ((x) >> (64 - (s))))
// The same rotation as two 32-bit funnel shifts (SHF.L.W on sm_70+).
#ifdef HOST_EMU
#define ROTF(x, s) ROTL(x, s)
#else
DEV u64 rotf(u64 x, int s) {
    uint32_t lo = (uint32_t)x, hi = (uint32_t)(x >> 32);
    if (s >= 32) { uint32_t t = lo; lo = hi; hi = t; s -= 32; }
    uint32_t nh = __funnelshift_l(lo, hi, s), nl = __funnelshift_l(hi, lo, s);
    return ((u64)nh << 32) | nl;
}
#define ROTF(x, s) rotf(x, s)
#endif

// One round on a[25]: theta, then rho + pi into b (b[y][2x+3y] = rot(a[x][y])), chi, iota.
#define KECCAK_ROUND(round, R) do { \
 \
        u64 c0 = a[0] ^ a[5] ^ a[10] ^ a[15] ^ a[20]; \
        u64 c1 = a[1] ^ a[6] ^ a[11] ^ a[16] ^ a[21]; \
        u64 c2 = a[2] ^ a[7] ^ a[12] ^ a[17] ^ a[22]; \
        u64 c3 = a[3] ^ a[8] ^ a[13] ^ a[18] ^ a[23]; \
        u64 c4 = a[4] ^ a[9] ^ a[14] ^ a[19] ^ a[24]; \
        u64 d0 = c4 ^ R(c1, 1), d1 = c0 ^ R(c2, 1), d2 = c1 ^ R(c3, 1); \
        u64 d3 = c2 ^ R(c4, 1), d4 = c3 ^ R(c0, 1); \
        u64 b0 = a[0] ^ d0; \
        u64 b1 = R(a[6] ^ d1, 44); \
        u64 b2 = R(a[12] ^ d2, 43); \
        u64 b3 = R(a[18] ^ d3, 21); \
        u64 b4 = R(a[24] ^ d4, 14); \
        u64 b5 = R(a[3] ^ d3, 28); \
        u64 b6 = R(a[9] ^ d4, 20); \
        u64 b7 = R(a[10] ^ d0, 3); \
        u64 b8 = R(a[16] ^ d1, 45); \
        u64 b9 = R(a[22] ^ d2, 61); \
        u64 b10 = R(a[1] ^ d1, 1); \
        u64 b11 = R(a[7] ^ d2, 6); \
        u64 b12 = R(a[13] ^ d3, 25); \
        u64 b13 = R(a[19] ^ d4, 8); \
        u64 b14 = R(a[20] ^ d0, 18); \
        u64 b15 = R(a[4] ^ d4, 27); \
        u64 b16 = R(a[5] ^ d0, 36); \
        u64 b17 = R(a[11] ^ d1, 10); \
        u64 b18 = R(a[17] ^ d2, 15); \
        u64 b19 = R(a[23] ^ d3, 56); \
        u64 b20 = R(a[2] ^ d2, 62); \
        u64 b21 = R(a[8] ^ d3, 55); \
        u64 b22 = R(a[14] ^ d4, 39); \
        u64 b23 = R(a[15] ^ d0, 41); \
        u64 b24 = R(a[21] ^ d1, 2); \
        a[0] = b0 ^ (~b1 & b2) ^ RC[round]; \
        a[1] = b1 ^ (~b2 & b3); \
        a[2] = b2 ^ (~b3 & b4); \
        a[3] = b3 ^ (~b4 & b0); \
        a[4] = b4 ^ (~b0 & b1); \
        a[5] = b5 ^ (~b6 & b7); \
        a[6] = b6 ^ (~b7 & b8); \
        a[7] = b7 ^ (~b8 & b9); \
        a[8] = b8 ^ (~b9 & b5); \
        a[9] = b9 ^ (~b5 & b6); \
        a[10] = b10 ^ (~b11 & b12); \
        a[11] = b11 ^ (~b12 & b13); \
        a[12] = b12 ^ (~b13 & b14); \
        a[13] = b13 ^ (~b14 & b10); \
        a[14] = b14 ^ (~b10 & b11); \
        a[15] = b15 ^ (~b16 & b17); \
        a[16] = b16 ^ (~b17 & b18); \
        a[17] = b17 ^ (~b18 & b19); \
        a[18] = b18 ^ (~b19 & b15); \
        a[19] = b19 ^ (~b15 & b16); \
        a[20] = b20 ^ (~b21 & b22); \
        a[21] = b21 ^ (~b22 & b23); \
        a[22] = b22 ^ (~b23 & b24); \
        a[23] = b23 ^ (~b24 & b20); \
        a[24] = b24 ^ (~b20 & b21); \
} while (0)

// Rounds loop not unrolled (the dry-run kernel), unrolled by 2, and fully unrolled.
DEV void keccak_f(u64* a) {
#ifndef HOST_EMU
#pragma unroll 1
#endif
    for (int round = 0; round < 24; ++round) KECCAK_ROUND(round, ROTL);
}
DEV void keccak_f_u2(u64* a) {
#ifndef HOST_EMU
#pragma unroll 2
#endif
    for (int round = 0; round < 24; ++round) KECCAK_ROUND(round, ROTL);
}
DEV void keccak_f_shf(u64* a) {
#ifndef HOST_EMU
#pragma unroll 1
#endif
    for (int round = 0; round < 24; ++round) KECCAK_ROUND(round, ROTF);
}

// Leaf: 0 :: (32 zeros, 1) :: v (66 bytes), cSHAKE pad 0x04 at byte 66, 0x80 at byte 135.
KERNEL void merkle_leaves(const u64* vals, const u64* mid, u64* dig, u64 n) {
    KBEGIN(n)
    u64 a[25];
    for (int k = 0; k < 25; ++k) a[k] = mid[k];
    const u64* v = vals + 4 * i;
    a[4] ^= 0x100ull | (v[0] << 16);
    a[5] ^= (v[0] >> 48) | (v[1] << 16);
    a[6] ^= (v[1] >> 48) | (v[2] << 16);
    a[7] ^= (v[2] >> 48) | (v[3] << 16);
    a[8] ^= (v[3] >> 48) | (0x04ull << 16);
    a[16] ^= 0x80ull << 56;
    keccak_f_shf(a);
    for (int k = 0; k < 4; ++k) dig[4 * i + k] = a[k];
    KEND
}

// Node: 1 :: (32 zeros, 1) :: l :: (32 zeros, 1) :: r (131 bytes); pad 0x04 at 131, 0x80 at 135.
// A batch of trees side by side, 2h digests each: next[b h + o] = node(cur[2bh + o], cur[2bh + o + h]).
KERNEL void merkle_nodes(const u64* cur, const u64* mid, u64* next, u64 h, u64 n) {
    KBEGIN(n)
    u64 a[25];
    for (int k = 0; k < 25; ++k) a[k] = mid[k];
    u64 b = i / h, o = i % h;
    const u64* l = cur + 4 * (2 * b * h + o);
    const u64* r = l + 4 * h;
    a[0] ^= 1ull;
    a[4] ^= 0x100ull | (l[0] << 16);
    a[5] ^= (l[0] >> 48) | (l[1] << 16);
    a[6] ^= (l[1] >> 48) | (l[2] << 16);
    a[7] ^= (l[2] >> 48) | (l[3] << 16);
    a[8] ^= (l[3] >> 48);
    a[12] ^= (1ull << 16) | (r[0] << 24);
    a[13] ^= (r[0] >> 40) | (r[1] << 24);
    a[14] ^= (r[1] >> 40) | (r[2] << 24);
    a[15] ^= (r[2] >> 40) | (r[3] << 24);
    a[16] ^= (r[3] >> 40) | (0x04ull << 24) | (0x80ull << 56);
    keccak_f_shf(a);
    for (int k = 0; k < 4; ++k) next[4 * i + k] = a[k];
    KEND
}

// Throughput probe: `iters` Keccak-f per thread on a private state; out[i] = lane 0.
KERNEL void keccak_rate(const u64* mid, u64* out, u64 iters, u64 n) {
    KBEGIN(n)
    u64 a[25];
    for (int k = 0; k < 25; ++k) a[k] = mid[k] ^ (i * 0x9e3779b97f4a7c15ull);
    for (u64 it = 0; it < iters; ++it) keccak_f(a);
    out[i] = a[0];
    KEND
}

KERNEL void keccak_rate_shf(const u64* mid, u64* out, u64 iters, u64 n) {
    KBEGIN(n)
    u64 a[25];
    for (int k = 0; k < 25; ++k) a[k] = mid[k] ^ (i * 0x9e3779b97f4a7c15ull);
    for (u64 it = 0; it < iters; ++it) keccak_f_shf(a);
    out[i] = a[0];
    KEND
}
KERNEL void keccak_rate_u2(const u64* mid, u64* out, u64 iters, u64 n) {
    KBEGIN(n)
    u64 a[25];
    for (int k = 0; k < 25; ++k) a[k] = mid[k] ^ (i * 0x9e3779b97f4a7c15ull);
    for (u64 it = 0; it < iters; ++it) keccak_f_u2(a);
    out[i] = a[0];
    KEND
}
// Throughput probe: `iters` dependent Tower256 products per thread.
KERNEL void t256_mul_rate(const u64* seed, u64* out, u64 iters, u64 n) {
    TABLES
    Tabs t = {s_log, s_exp, s_gen};
    KBEGIN(n)
    uint32_t x[8], y[8], r[8];
    load8(seed, x);
    load8(seed + 4, y);
    x[0] ^= (uint32_t)i;
    for (u64 it = 0; it < iters; ++it) {
        mul8(t, x, y, r);
        for (int k = 0; k < 8; ++k) x[k] = r[k] ^ y[k];
    }
    store8(out + 4 * i, x);
    KEND
}

// ------------------------------------------------------------------------------------------
// The bulk field kernels with the 64 KiB product table (grid-stride; launch with 65536 bytes
// of dynamic shared memory and at most 1024 threads per block).

FULL_KERNEL t256_mul_full(const u64* a, const u64* b, u64* out, u64 b_stride, u64 n) {
    FULL_TABLES
    GS_BEGIN(n)
    uint32_t x[8], y[8], r[8];
    load8(a + 4 * i, x);
    load8(b + 4 * i * b_stride, y);
    mul8(t, x, y, r);
    store8(out + 4 * i, r);
    GS_END
}

FULL_KERNEL ntt_scale_full(const u64* a, const u64* powers, u64* out, u64 bsz, u64 n) {
    FULL_TABLES
    GS_BEGIN(n)
    uint32_t x[8], y[8], r[8];
    load8(a + 4 * i, x);
    load8(powers + 4 * (i % bsz), y);
    mul8(t, x, y, r);
    store8(out + 4 * i, r);
    GS_END
}

FULL_KERNEL ntt_butterfly_full(const u64* src, const u64* z, u64* dst, u64 size, u64 n) {
    FULL_TABLES
    GS_BEGIN(n)
    u64 h = size >> 1, blk = i / h, j = i % h, base = blk * size;
    uint32_t g0[8], g1[8], zz[8], e[8];
    load8(src + 4 * (base + j), g0);
    load8(src + 4 * (base + h + j), g1);
    load8(z + 4 * j, zz);
    mul8(t, zz, g1, e);
    xor8(e, g0);
    store8(dst + 4 * (base + 2 * j), e);
    xor8(e, g1);
    store8(dst + 4 * (base + 2 * j + 1), e);
    GS_END
}

FULL_KERNEL fri_fold_full(const u64* w, const u64* c, u64* next, u64 n) {
    FULL_TABLES
    GS_BEGIN(n)
    uint32_t l[8], r[8], cc[8], p[8];
    load8(w + 4 * i, l);
    load8(w + 4 * (i + n), r);
    load8(c + 4 * i, cc);
    xor8(r, l);
    mul8(t, cc, r, p);
    xor8(p, l);
    store8(next + 4 * i, p);
    GS_END
}

FULL_KERNEL t256_mul_rate_full(const u64* seed, u64* out, u64 iters, u64 n) {
    FULL_TABLES
    GS_BEGIN(n)
    uint32_t x[8], y[8], r[8];
    load8(seed, x);
    load8(seed + 4, y);
    x[0] ^= (uint32_t)i;
    for (u64 it = 0; it < iters; ++it) {
        mul8(t, x, y, r);
        for (int k = 0; k < 8; ++k) x[k] = r[k] ^ y[k];
    }
    store8(out + 4 * i, x);
    GS_END
}

// ------------------------------------------------------------------------------------------
// Bit-sliced Tower256 multiply. A group is 32 elements as 256 bit planes (plane p, bit l = bit p
// of element l). One thread multiplies a group: Karatsuba (three products per level, the
// generator map y_{K-1} as XORs) down to T_4, whose 81 leaf products (16 planes each) run in
// registers by the bit-level recursion (AND at T_0). Resident layout (t256_mul_bs): plane p of
// group g at u32 index p * G + g. (A first version cut at T_5 and recombined through a flat
// table of 166 terms into a 256-word accumulator; it spilled 6.5-11 KB per thread and ran
// 8.0e7 products/s on the T4, accel-tower-bitslice-01 version 1.)

#ifdef HOST_EMU
#define BS_CONST static const
#define SDEV static inline
#define UNROLL
#else
#define BS_CONST __constant__
#define SDEV __device__ __forceinline__ static
#define UNROLL _Pragma("unroll")
#endif

template <int K> struct BS {
    // x <- x * y_{K-1} in T_K (2^K planes), in place.
    SDEV void gen(uint32_t* x) {
        const int h = 1 << (K - 1);
        uint32_t t[h];
        UNROLL for (int i = 0; i < h; ++i) t[i] = x[h + i];
        BS<K - 1>::gen(t);
        UNROLL for (int i = 0; i < h; ++i) { uint32_t lo = x[i]; x[i] = x[h + i]; x[h + i] = lo ^ t[i]; }
    }
    SDEV void mul(const uint32_t* a, const uint32_t* b, uint32_t* r) {
        const int h = 1 << (K - 1);
        uint32_t p0[h], p1[h], m[h], sa[h], sb[h];
        UNROLL for (int i = 0; i < h; ++i) { sa[i] = a[i] ^ a[h + i]; sb[i] = b[i] ^ b[h + i]; }
        BS<K - 1>::mul(a, b, p0);
        BS<K - 1>::mul(a + h, b + h, p1);
        BS<K - 1>::mul(sa, sb, m);
        UNROLL for (int i = 0; i < h; ++i) r[i] = p0[i] ^ p1[i];
        BS<K - 1>::gen(p1);
        UNROLL for (int i = 0; i < h; ++i) r[h + i] = m[i] ^ r[i] ^ p1[i];
    }
};
template <> struct BS<0> {
    SDEV void gen(uint32_t*) {}
    SDEV void mul(const uint32_t* a, const uint32_t* b, uint32_t* r) { r[0] = a[0] & b[0]; }
};

// out[j] bit l = in[l] bit j (32x32, in place): five swap stages with constant masks.
template <int J> DEV void tstage(uint32_t* x, uint32_t m) {
    UNROLL for (int k = 0; k < 32; ++k) {
        if (!(k & J)) {
            uint32_t t = ((x[k] >> J) ^ x[k + J]) & m;
            x[k] ^= t << J;
            x[k + J] ^= t;
        }
    }
}
DEV void transpose32(uint32_t* x) {
    tstage<16>(x, 0x0000FFFFu);
    tstage<8>(x, 0x00FF00FFu);
    tstage<4>(x, 0x0F0F0F0Fu);
    tstage<2>(x, 0x33333333u);
    tstage<1>(x, 0x55555555u);
}

#ifdef HOST_EMU
#define NOINLINE_DEV static __attribute__((noinline))
#else
#define NOINLINE_DEV __device__ __noinline__ static
#endif

// The tree above T_4, depth first: r (2^K planes) = a * b, with plane p of a at a[p * sa].
// Children: p0 into r's low half, p1 into its high half, the middle product from the half-sums
// (materialized in scratch). Combine: low = p0 + p1; high = m + low + y_{K-2} p1. scratch holds
// 3 * 2^(K-1) words for this level plus the levels below (720 words at K = 8). Levels 5..8 are
// out-of-line calls, so the 81 register-resident T_4 leaves are only three inlined copies.
template <int K> struct BT {
    NOINLINE_DEV void mul(const uint32_t* a, u64 sa, const uint32_t* b, u64 sb, uint32_t* r, uint32_t* scratch) {
        const int h = 1 << (K - 1);
        uint32_t* xa = scratch;
        uint32_t* xb = scratch + h;
        uint32_t* m = scratch + 2 * h;
        uint32_t* deeper = scratch + 3 * h;
        BT<K - 1>::mul(a, sa, b, sb, r, deeper);
        BT<K - 1>::mul(a + h * sa, sa, b + h * sb, sb, r + h, deeper);
        for (int i = 0; i < h; ++i) { xa[i] = a[i * sa] ^ a[(h + i) * sa]; xb[i] = b[i * sb] ^ b[(h + i) * sb]; }
        BT<K - 1>::mul(xa, 1, xb, 1, m, deeper);
        for (int i = 0; i < h; ++i) { uint32_t lo = r[i] ^ r[h + i]; r[i] = lo; m[i] ^= lo; }
        BS<K - 1>::gen(r + h);
        for (int i = 0; i < h; ++i) r[h + i] ^= m[i];
    }
};
template <> struct BT<4> {
    SDEV void mul(const uint32_t* a, u64 sa, const uint32_t* b, u64 sb, uint32_t* r, uint32_t*) {
        uint32_t x[16], y[16], z[16];
        UNROLL for (int i = 0; i < 16; ++i) { x[i] = a[i * sa]; y[i] = b[i * sb]; }
        BS<4>::mul(x, y, z);
        UNROLL for (int i = 0; i < 16; ++i) r[i] = z[i];
    }
};

// acc (256 planes) = A * B, with plane p of A at A[p * stride].
DEV void bs_core(const uint32_t* A, const uint32_t* B, u64 stride, uint32_t* acc) {
    uint32_t scratch[720];
    BT<8>::mul(A, stride, B, stride, acc, scratch);
}

// Resident: R = A * B for n groups (interleaved planes).
KERNEL void t256_mul_bs(const u64* A64, const u64* B64, u64* R64, u64 n) {
    KBEGIN(n)
    uint32_t acc[256];
    bs_core((const uint32_t*)A64 + i, (const uint32_t*)B64 + i, n, acc);
    uint32_t* R = (uint32_t*)R64;
    UNROLL for (int k = 0; k < 256; ++k) R[(u64)k * n + i] = acc[k];
    KEND
}

// Elements (4 limbs) of group i -> interleaved planes, and back.
KERNEL void t256_to_sliced(const u64* X, u64* S64, u64 n) {
    KBEGIN(n)
    uint32_t* S = (uint32_t*)S64;
    const uint32_t* Xw = (const uint32_t*)X;
    for (int w = 0; w < 8; ++w) {
        uint32_t rows[32];
        UNROLL for (int l = 0; l < 32; ++l) rows[l] = Xw[8 * (32 * i + l) + w];
        transpose32(rows);
        UNROLL for (int j = 0; j < 32; ++j) S[(u64)(32 * w + j) * n + i] = rows[j];
    }
    KEND
}
KERNEL void t256_from_sliced(const u64* S64, u64* X, u64 n) {
    KBEGIN(n)
    const uint32_t* S = (const uint32_t*)S64;
    uint32_t* Xw = (uint32_t*)X;
    for (int w = 0; w < 8; ++w) {
        uint32_t rows[32];
        UNROLL for (int j = 0; j < 32; ++j) rows[j] = S[(u64)(32 * w + j) * n + i];
        transpose32(rows);
        UNROLL for (int l = 0; l < 32; ++l) Xw[8 * (32 * i + l) + w] = rows[l];
    }
    KEND
}

// Fused: gather 32 elements of each operand (element l at a + 4 * ia(l), b + 4 * ib(l)),
// slice them in registers, multiply, unslice into prod[l][8].
template <class FA, class FB>
DEV void bs_mul32(const u64* a, FA ia, const u64* b, FB ib, uint32_t prod[32][8]) {
    uint32_t As[256], Bs[256], acc[256];
    const uint32_t* aw = (const uint32_t*)a;
    const uint32_t* bw = (const uint32_t*)b;
    for (int w = 0; w < 8; ++w) {
        uint32_t ra[32], rb[32];
        UNROLL for (int l = 0; l < 32; ++l) { ra[l] = aw[8 * ia(l) + w]; rb[l] = bw[8 * ib(l) + w]; }
        transpose32(ra);
        transpose32(rb);
        UNROLL for (int j = 0; j < 32; ++j) { As[32 * w + j] = ra[j]; Bs[32 * w + j] = rb[j]; }
    }
    bs_core(As, Bs, 1, acc);
    for (int w = 0; w < 8; ++w) {
        uint32_t r[32];
        UNROLL for (int j = 0; j < 32; ++j) r[j] = acc[32 * w + j];
        transpose32(r);
        UNROLL for (int l = 0; l < 32; ++l) prod[l][w] = r[l];
    }
}

// The bulk kernels on 32 items per thread (n = items / 32; items a multiple of 32).
KERNEL void t256_mul_bsx(const u64* a, const u64* b, u64* out, u64 b_stride, u64 n) {
    KBEGIN(n)
    uint32_t prod[32][8];
    u64 g0 = 32 * i;
    bs_mul32(a, [&](int l) { return g0 + l; }, b, [&](int l) { return (g0 + l) * b_stride; }, prod);
    uint32_t* ow = (uint32_t*)out;
    for (int l = 0; l < 32; ++l) UNROLL for (int w = 0; w < 8; ++w) ow[8 * (g0 + l) + w] = prod[l][w];
    KEND
}
KERNEL void ntt_scale_bsx(const u64* a, const u64* powers, u64* out, u64 bsz, u64 n) {
    KBEGIN(n)
    uint32_t prod[32][8];
    u64 g0 = 32 * i;
    bs_mul32(a, [&](int l) { return g0 + l; }, powers, [&](int l) { return (g0 + l) % bsz; }, prod);
    uint32_t* ow = (uint32_t*)out;
    for (int l = 0; l < 32; ++l) UNROLL for (int w = 0; w < 8; ++w) ow[8 * (g0 + l) + w] = prod[l][w];
    KEND
}
KERNEL void ntt_butterfly_bsx(const u64* src, const u64* z, u64* dst, u64 size, u64 n) {
    KBEGIN(n)
    uint32_t prod[32][8];
    u64 g0 = 32 * i, h = size >> 1;
    bs_mul32(z, [&](int l) { return (g0 + l) % h; }, src,
             [&](int l) { u64 g = g0 + l; return (g / h) * size + h + g % h; }, prod);
    const uint32_t* sw = (const uint32_t*)src;
    uint32_t* dw = (uint32_t*)dst;
    for (int l = 0; l < 32; ++l) {
        u64 g = g0 + l, blk = g / h, j = g % h, base = blk * size;
        UNROLL for (int w = 0; w < 8; ++w) {
            uint32_t e = prod[l][w] ^ sw[8 * (base + j) + w];
            dw[8 * (base + 2 * j) + w] = e;
            dw[8 * (base + 2 * j + 1) + w] = e ^ sw[8 * (base + h + j) + w];
        }
    }
    KEND
}
// next[k] = w[k] + c[k] (w[k] + w[k + half]); half = 32 n. The sum is formed before slicing.
KERNEL void fri_fold_bsx(const u64* w, const u64* c, u64* next, u64 n) {
    KBEGIN(n)
    uint32_t prod[32][8];
    u64 g0 = 32 * i, half = 32 * n;
    uint32_t sum[32][8];
    const uint32_t* ww = (const uint32_t*)w;
    for (int l = 0; l < 32; ++l) UNROLL for (int k = 0; k < 8; ++k) sum[l][k] = ww[8 * (g0 + l) + k] ^ ww[8 * (g0 + l + half) + k];
    bs_mul32(c, [&](int l) { return g0 + l; }, (const u64*)&sum[0][0], [&](int l) { return (u64)l; }, prod);
    uint32_t* nw = (uint32_t*)next;
    for (int l = 0; l < 32; ++l) UNROLL for (int k = 0; k < 8; ++k) nw[8 * (g0 + l) + k] = prod[l][k] ^ ww[8 * (g0 + l) + k];
    KEND
}

// ------------------------------------------------------------------------------------------
// End-to-end batch: B proofs of one shape side by side (word b of a level at b * size).

// next[b half + k] = w + (S[k] + d[b]) (w + w'), with w = w[2 b half + k], w' = w[2 b half + k + half].
// S is the span shared by the batch (dom_j / pivot); d[b] = alpha_b / pivot.
KERNEL void fri_fold_batch(const u64* w, const u64* S, const u64* dvec, u64* next, u64 half, u64 n) {
    TABLES
    Tabs t = {s_log, s_exp, s_gen};
    KBEGIN(n)
    u64 b = i / half, k = i % half;
    uint32_t l[8], r[8], cc[8], dd[8], p[8];
    load8(w + 4 * (2 * b * half + k), l);
    load8(w + 4 * (2 * b * half + k + half), r);
    load8(S + 4 * k, cc);
    load8(dvec + 4 * b, dd);
    xor8(cc, dd);
    xor8(r, l);
    mul8(t, cc, r, p);
    xor8(p, l);
    store8(next + 4 * i, p);
    KEND
}

// Query seeds. The query prefix of proof i: nb full 136-byte blocks (17 lanes each) absorbed into
// the cSHAKE(MD-FRI-Q) midstate, then a remainder of r bytes. Seed a of proof b is the low
// seed_bits of cSHAKE(prefix || envelope(encodeLength a)); envelope(encodeLength a) is 2a + 3
// bytes, zero but for ones at a + 1 and 2a + 2.
KERNEL void cshake_absorb(const u64* mid, const u64* blocks, u64* states, u64 nb, u64 n) {
    KBEGIN(n)
    u64 a[25];
    for (int k = 0; k < 25; ++k) a[k] = mid[k];
    for (u64 blk = 0; blk < nb; ++blk) {
        for (int l = 0; l < 17; ++l) a[l] ^= blocks[(i * nb + blk) * 17 + l];
        keccak_f_shf(a);
    }
    for (int k = 0; k < 25; ++k) states[25 * i + k] = a[k];
    KEND
}
KERNEL void query_seeds(const u64* states, const u64* rem, u64* seeds, u64 r, u64 q, u64 seed_bits, u64 n) {
    KBEGIN(n)
    u64 b = i / q, aq = i % q;
    u64 a[25];
    for (int k = 0; k < 25; ++k) a[k] = states[25 * b + k];
    const uint8_t* rb = (const uint8_t*)(rem + 17 * b);
    u64 len = r + 2 * aq + 3, nblk = len / 136 + 1;
    for (u64 blk = 0; blk < nblk; ++blk) {
        for (int l = 0; l < 17; ++l) {
            u64 v = 0;
            for (int j = 0; j < 8; ++j) {
                u64 p = blk * 136 + 8 * l + j;
                u64 byte = 0;
                if (p < r) byte = rb[p];
                else if (p < len) { u64 e = p - r; byte = (e == aq + 1 || e == 2 * aq + 2) ? 1 : 0; }
                if (p == len) byte ^= 0x04;
                if (p == nblk * 136 - 1) byte ^= 0x80;
                v |= byte << (8 * j);
            }
            a[l] ^= v;
        }
        keccak_f_shf(a);
    }
    seeds[i] = seed_bits >= 64 ? a[0] : (a[0] & ((1ull << seed_bits) - 1));
    KEND
}

// Openings. Record (b, j, a) = w[k], w[k + half] (32 bytes each), StreamCodec.nat(k_bits - 1), then
// k_bits - 1 sibling digests as StreamCodec.nat of their little-endian value (base-255 digits, then
// 255). Words of round j at wptr[j]; tree level t of round j at lptr[32 j + t] (2^t digests per
// proof); pow255[4 k ..] = 255^k, k = 0..32.
DEV int digits255(const u64* v, const u64* pow255) {
    if ((v[0] | v[1] | v[2] | v[3]) == 0) return 0;
    for (int k = 32; k >= 0; --k) {
        const u64* p = pow255 + 4 * k;
        int ge = 1;
        for (int l = 3; l >= 0; --l) {
            if (v[l] != p[l]) { ge = v[l] > p[l]; break; }
        }
        if (ge) return k + 1;
    }
    return 0;
}
DEV int natlen(u64 v) {
    int c = 1;
    while (v) { ++c; v /= 255; }
    return c;
}
DEV u64 nat_put(uint8_t* o, u64 v) {
    u64 c = 0;
    while (v) { o[c++] = (uint8_t)(v % 255); v /= 255; }
    o[c++] = 255;
    return c;
}
DEV u64 nat256_put(uint8_t* o, const u64* d) {
    uint32_t v[8];
    for (int k = 0; k < 4; ++k) { v[2 * k] = (uint32_t)d[k]; v[2 * k + 1] = (uint32_t)(d[k] >> 32); }
    u64 c = 0;
    for (;;) {
        uint32_t any = 0;
        for (int k = 0; k < 8; ++k) any |= v[k];
        if (!any) break;
        u64 rem = 0;
        for (int k = 7; k >= 0; --k) {
            u64 cur = (rem << 32) | v[k];
            v[k] = (uint32_t)(cur / 255);
            rem = cur % 255;
        }
        o[c++] = (uint8_t)rem;
    }
    o[c++] = 255;
    return c;
}
KERNEL void open_lengths(const u64* seeds, const u64* wptr, const u64* lptr, const u64* pow255, u64* lens,
                         u64 ell, u64 m, u64 q, u64 n) {
    KBEGIN(n)
    u64 a = i % q, j = (i / q) % m, b = i / (q * m);
    u64 k = ell - j, half = 1ull << (k - 1);
    u64 idx = seeds[b * q + a] % half;
    u64 len = 64 + natlen(k - 1);
    for (u64 d = 0; d + 1 < k; ++d) {
        u64 tl = d + 1;
        const u64* lvl = (const u64*)lptr[32 * j + tl];
        u64 o = (idx & ((2ull << d) - 1)) ^ (1ull << d);
        len += digits255(lvl + 4 * ((b << tl) + o), pow255) + 1;
    }
    lens[i] = len;
    KEND
}
// offs[i]: where record i's content starts. Record (b, j, 0) is preceded by hq bytes of
// StreamCodec.nat(q) and record (b, 0, 0) further by hm bytes of StreamCodec.nat(m).
KERNEL void open_write(const u64* seeds, const u64* wptr, const u64* lptr, const u64* offs, u64* out64,
                       u64 ell, u64 m, u64 q, u64 n) {
    KBEGIN(n)
    uint8_t* out = (uint8_t*)out64;
    u64 a = i % q, j = (i / q) % m, b = i / (q * m);
    u64 k = ell - j, half = 1ull << (k - 1);
    u64 idx = seeds[b * q + a] % half;
    uint8_t* o = out + offs[i];
    if (a == 0) {
        uint8_t hq[8];
        u64 lq = nat_put(hq, q);
        uint8_t* oq = o - lq;
        for (u64 c = 0; c < lq; ++c) oq[c] = hq[c];
        if (j == 0) {
            uint8_t hm[8];
            u64 lm = nat_put(hm, m);
            uint8_t* om = oq - lm;
            for (u64 c = 0; c < lm; ++c) om[c] = hm[c];
        }
    }
    const u64* w = (const u64*)wptr[j];
    const u64* lo = w + 4 * ((b << k) + idx);
    const u64* hi = w + 4 * ((b << k) + idx + half);
    for (int c = 0; c < 32; ++c) { o[c] = (uint8_t)(lo[c / 8] >> (8 * (c % 8))); o[32 + c] = (uint8_t)(hi[c / 8] >> (8 * (c % 8))); }
    u64 p = 64 + nat_put(o + 64, k - 1);
    for (u64 d = 0; d + 1 < k; ++d) {
        u64 tl = d + 1;
        const u64* lvl = (const u64*)lptr[32 * j + tl];
        u64 oo = (idx & ((2ull << d) - 1)) ^ (1ull << d);
        p += nat256_put(o + p, lvl + 4 * ((b << tl) + oo));
    }
    KEND
}
