//! Work 9104, the fast honest prover: the same receipt bytes as `crate::tower256_fri_prove`
//! (the conformance kernel pinned to Lean), with the three loops that kernel runs above the
//! counts of `docs/TOWER256-FRI-PROVER-WORK.md` replaced.
//!
//! 1. **Encode.** Gao-Mateer additive FFT of the monomial input word on the affine subspace
//!    `offset + span(beta)`, for an arbitrary basis: per depth, normalize the lowest basis
//!    element to one (`h(z) = f(beta_0 z)`), Taylor-expand at `z^2 + z` (XOR only), and
//!    recurse on `span(gamma_i^2 + gamma_i)` with offset `t^2 + t`. Every subproblem at one
//!    depth shares its basis and offset, so a depth costs one inversion, `L` scalings and
//!    `2^(ell-1)` butterfly multiplications; the recursion stops when the polynomial is a
//!    constant (depth `log2 L`, the rate's cosets for free). Total about
//!    `(ell - lb) 2^(ell-1) + L log L` multiplications against the kernel's `2^ell L`.
//!    A dependent basis (a zero normalizer) falls back to Horner at every point.
//! 2. **Merkle.** Every level of every committed tree is stored once; an opening reads its
//!    siblings (`L_{d+1}[(k mod 2^(d+1)) xor 2^d]`) instead of rebuilding subtrees.
//! 3. **Domains.** `y -> y^2 + p y` is GF(2)-linear, so a level's domain is the XOR span of
//!    the images of the offset and the basis; the fold's factor `(dom_k + alpha) / pivot` is
//!    the span of the images scaled once by the inverse pivot: one multiplication per folded
//!    point.
//!
//! Arithmetic runs in a polynomial basis of GF(2^256), `GF(2)[x] / p(x)`, reached from the
//! Fan-Paar coordinates of `crate::binary_tower_256` by the field isomorphism
//! `y(x) -> y(omega)` for a fixed `omega` of degree 256 (its minimal polynomial is `p`,
//! computed at first use from the reference multiplication). Products are carry-less
//! (PMULL on aarch64, PCLMULQDQ on x86_64 when compiled with it, a portable loop otherwise)
//! with Barrett reduction. Every byte that leaves the prover (leaf hashes, openings,
//! challenges, coefficients) is converted back to Fan-Paar coordinates, so the receipt is
//! the conformance kernel's byte for byte; `tests/tower256_fri_fast_conformance.rs` checks
//! that on the five Lean vectors and on random requests against the conformance kernel.

use std::sync::OnceLock;
use std::time::Instant;

use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    CShake256, CShake256Core,
};

use crate::binary_tower_256::Tower256;
use crate::tower256_fri_prove::{FriProveError, ProveRequest, MAX_ELL};

type Digest = [u8; 32];

// ---------------------------------------------------------------------------------------------
// GF(2^256) in a polynomial basis

/// An element of `GF(2)[x] / p(x)`: bit `i` of the 256-bit little-endian integer is the
/// coefficient of `x^i`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct P256(pub [u64; 4]);

impl P256 {
    pub const ZERO: Self = Self([0; 4]);
    pub const ONE: Self = Self([1, 0, 0, 0]);

    #[inline(always)]
    pub fn add(self, o: Self) -> Self {
        Self([self.0[0] ^ o.0[0], self.0[1] ^ o.0[1], self.0[2] ^ o.0[2], self.0[3] ^ o.0[3]])
    }

    #[inline(always)]
    pub fn is_zero(self) -> bool {
        (self.0[0] | self.0[1] | self.0[2] | self.0[3]) == 0
    }

    #[inline]
    pub fn mul(self, o: Self) -> Self {
        iso().mul(self, o)
    }

    #[inline]
    pub fn square(self) -> Self {
        self.mul(self)
    }

    /// `self^(2^256 - 2)`; `None` at zero.
    pub fn inverse(self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }
        let mut acc = self;
        for _ in 1..255 {
            acc = acc.square().mul(self);
        }
        Some(acc.square())
    }

    pub fn from_tower(t: Tower256) -> Self {
        iso().to_poly(t)
    }

    pub fn to_tower(self) -> Tower256 {
        iso().to_tower(self)
    }

    pub fn tower_bytes(self) -> [u8; 32] {
        self.to_tower().to_le_bytes()
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline(always)]
fn clmul64(a: u64, b: u64) -> (u64, u64) {
    // SAFETY: the `aes` target feature (PMULL) is enabled at compile time.
    let r: u128 = unsafe { core::arch::aarch64::vmull_p64(a, b) };
    (r as u64, (r >> 64) as u64)
}

#[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq", target_feature = "sse2"))]
#[inline(always)]
fn clmul64(a: u64, b: u64) -> (u64, u64) {
    use core::arch::x86_64::*;
    // SAFETY: `pclmulqdq` and `sse2` are enabled at compile time.
    unsafe {
        let r = _mm_clmulepi64_si128(_mm_set_epi64x(0, a as i64), _mm_set_epi64x(0, b as i64), 0);
        let mut out = [0u64; 2];
        _mm_storeu_si128(out.as_mut_ptr() as *mut __m128i, r);
        (out[0], out[1])
    }
}

#[cfg(not(any(
    all(target_arch = "aarch64", target_feature = "aes"),
    all(target_arch = "x86_64", target_feature = "pclmulqdq", target_feature = "sse2")
)))]
#[inline(always)]
fn clmul64(a: u64, b: u64) -> (u64, u64) {
    let (mut lo, mut hi) = (0u64, 0u64);
    for i in 0..64 {
        if b >> i & 1 == 1 {
            lo ^= a << i;
            if i > 0 {
                hi ^= a >> (64 - i);
            }
        }
    }
    (lo, hi)
}

/// Which carry-less multiply this build uses (reported by the benchmark).
pub const CLMUL_BACKEND: &str = if cfg!(all(target_arch = "aarch64", target_feature = "aes")) {
    "aarch64-pmull"
} else if cfg!(all(target_arch = "x86_64", target_feature = "pclmulqdq")) {
    "x86_64-pclmulqdq"
} else {
    "portable-loop"
};

#[inline(always)]
fn clmul256(a: &[u64; 4], b: &[u64; 4]) -> [u64; 8] {
    let mut c = [0u64; 8];
    for i in 0..4 {
        for j in 0..4 {
            let (lo, hi) = clmul64(a[i], b[j]);
            c[i + j] ^= lo;
            c[i + j + 1] ^= hi;
        }
    }
    c
}

/// Bits 256..511 of `a * b`.
#[inline(always)]
fn clmul256_high(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    // Word w of the product lands at c[w - 4].
    let mut c = [0u64; 4];
    for i in 0..4 {
        for j in (3 - i)..4 {
            let (lo, hi) = clmul64(a[i], b[j]);
            if i + j >= 4 {
                c[i + j - 4] ^= lo;
            }
            c[i + j - 3] ^= hi;
        }
    }
    c
}

/// Bits 0..255 of `a * b`.
#[inline(always)]
fn clmul256_low(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    let mut c = [0u64; 4];
    for i in 0..4 {
        for j in 0..(4 - i) {
            let (lo, hi) = clmul64(a[i], b[j]);
            c[i + j] ^= lo;
            if i + j + 1 < 4 {
                c[i + j + 1] ^= hi;
            }
        }
    }
    c
}

/// The isomorphism between Fan-Paar coordinates and `GF(2)[x] / p(x)`.
pub struct Iso {
    /// `p(x) = x^256 + p_low(x)`, the minimal polynomial of `omega`.
    pub p_low: [u64; 4],
    /// `floor(x^512 / p) = x^256 + mu_low`.
    mu_low: [u64; 4],
    /// `to_poly`: byte `c` of the tower coordinates selects `to_poly_tab[c][byte]`.
    to_poly_tab: Vec<[[u64; 4]; 256]>,
    to_tower_tab: Vec<[[u64; 4]; 256]>,
}

/// The fixed element whose powers are the polynomial basis (any element of degree 256 serves;
/// this one is the first four outputs of SplitMix64 from seed 0, as limbs).
pub fn omega() -> Tower256 {
    let mut s = 0u64;
    Tower256::from_limbs([splitmix(&mut s), splitmix(&mut s), splitmix(&mut s), splitmix(&mut s)])
}

fn bit(v: &[u64; 4], i: usize) -> bool {
    v[i / 64] >> (i % 64) & 1 == 1
}

fn xor4(a: &mut [u64; 4], b: &[u64; 4]) {
    for i in 0..4 {
        a[i] ^= b[i];
    }
}

fn byte_tables(columns: &[[u64; 4]; 256]) -> Vec<[[u64; 4]; 256]> {
    (0..32)
        .map(|c| {
            let mut tab = [[0u64; 4]; 256];
            for v in 1..256usize {
                let low = v & v.wrapping_neg();
                let b = low.trailing_zeros() as usize;
                let mut e = tab[v ^ low];
                xor4(&mut e, &columns[8 * c + b]);
                tab[v] = e;
            }
            tab
        })
        .collect()
}

#[inline(always)]
fn apply_tab(tab: &[[[u64; 4]; 256]], v: &[u64; 4]) -> [u64; 4] {
    let mut out = [0u64; 4];
    for (c, t) in tab.iter().enumerate() {
        let byte = (v[c / 8] >> (8 * (c % 8))) as u8;
        xor4(&mut out, &t[byte as usize]);
    }
    out
}

impl Iso {
    fn build() -> Self {
        // Columns of the polynomial-to-tower map: omega^j in tower coordinates.
        let omega = omega();
        let mut cols = [[0u64; 4]; 256];
        let mut pw = Tower256::ONE;
        for col in cols.iter_mut() {
            *col = *pw.limbs();
            pw = pw.mul(omega);
        }
        let omega256 = *pw.limbs();
        // Invert by elimination: vecs[i] (tower vector) = sum over tags[i] of columns.
        let mut vecs = cols;
        let mut tags = [[0u64; 4]; 256];
        for (j, t) in tags.iter_mut().enumerate() {
            t[j / 64] |= 1u64 << (j % 64);
        }
        for i in 0..256 {
            let r = (i..256).find(|&r| bit(&vecs[r], i)).expect("omega has degree 256");
            vecs.swap(i, r);
            tags.swap(i, r);
            for r in 0..256 {
                if r != i && bit(&vecs[r], i) {
                    let (vi, ti) = (vecs[i], tags[i]);
                    xor4(&mut vecs[r], &vi);
                    xor4(&mut tags[r], &ti);
                }
            }
        }
        // Now vecs[i] = e_i, so tags[i] = to_poly(e_i).
        let to_poly_tab = byte_tables(&tags);
        let to_tower_tab = byte_tables(&cols);
        let p_low = apply_tab(&to_poly_tab, &omega256);
        // mu = floor(x^512 / p) by long division; rem is a 513-bit vector.
        let mut rem = [0u64; 9];
        rem[8] = 1;
        let mut mu = [0u64; 5];
        for d in (0..=256usize).rev() {
            let top = 256 + d;
            if rem[top / 64] >> (top % 64) & 1 == 1 {
                mu[d / 64] |= 1u64 << (d % 64);
                // rem ^= p << d, with p = x^256 + p_low.
                rem[top / 64] ^= 1u64 << (top % 64);
                for i in 0..256 {
                    if bit(&p_low, i) {
                        let at = i + d;
                        rem[at / 64] ^= 1u64 << (at % 64);
                    }
                }
            }
        }
        assert_eq!(mu[4], 1, "deg mu = 256");
        let iso = Self { p_low, mu_low: [mu[0], mu[1], mu[2], mu[3]], to_poly_tab, to_tower_tab };
        // Self-check against the reference multiplication.
        let mut s = 0x5eed_u64;
        for _ in 0..4 {
            let a = Tower256::from_limbs([splitmix(&mut s), splitmix(&mut s), splitmix(&mut s), splitmix(&mut s)]);
            let b = Tower256::from_limbs([splitmix(&mut s), splitmix(&mut s), splitmix(&mut s), splitmix(&mut s)]);
            let fast = iso.to_tower(iso.mul(iso.to_poly(a), iso.to_poly(b)));
            assert_eq!(fast, a.mul(b), "polynomial-basis product disagrees with Fan-Paar");
        }
        iso
    }

    #[inline(always)]
    pub fn mul(&self, a: P256, b: P256) -> P256 {
        let c = clmul256(&a.0, &b.0);
        let lo = [c[0], c[1], c[2], c[3]];
        let hi = [c[4], c[5], c[6], c[7]];
        let mut q = clmul256_high(&hi, &self.mu_low);
        xor4(&mut q, &hi);
        let mut r = clmul256_low(&q, &self.p_low);
        xor4(&mut r, &lo);
        P256(r)
    }

    #[inline]
    pub fn to_poly(&self, t: Tower256) -> P256 {
        P256(apply_tab(&self.to_poly_tab, t.limbs()))
    }

    #[inline]
    pub fn to_tower(&self, p: P256) -> Tower256 {
        Tower256::from_limbs(apply_tab(&self.to_tower_tab, &p.0))
    }
}

pub fn iso() -> &'static Iso {
    static ISO: OnceLock<Iso> = OnceLock::new();
    ISO.get_or_init(Iso::build)
}

/// SplitMix64, for the fixed constants and the self-check.
pub fn splitmix(s: &mut u64) -> u64 {
    *s = s.wrapping_add(0x9e3779b97f4a7c15);
    let mut z = *s;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
}

// ---------------------------------------------------------------------------------------------
// Data parallelism: chunks of one output slice over scoped threads.

fn par_fill<T: Send, F: Fn(usize, &mut [T]) + Sync>(dst: &mut [T], threads: usize, f: F) {
    par_fill_aligned(dst, threads, 1, f)
}

/// As `par_fill`, with every chunk start a multiple of `align`.
fn par_fill_aligned<T: Send, F: Fn(usize, &mut [T]) + Sync>(dst: &mut [T], threads: usize, align: usize, f: F) {
    let n = dst.len();
    if threads <= 1 || n < 2048 {
        f(0, dst);
        return;
    }
    let chunk = n.div_ceil(threads).div_ceil(align) * align;
    std::thread::scope(|s| {
        for (i, c) in dst.chunks_mut(chunk).enumerate() {
            let f = &f;
            s.spawn(move || f(i * chunk, c));
        }
    });
}

// ---------------------------------------------------------------------------------------------
// Additive FFT (Gao-Mateer) on offset + span(beta)

/// In place: `f = sum_i (T[2i] + x T[2i+1]) (x^2 + x)^i`, XOR only (`f.len()` a power of two).
/// The recursive form; `taylor_par` is the same steps level by level.
#[cfg(test)]
fn taylor(f: &mut [P256]) {
    let n = f.len();
    if n <= 2 {
        return;
    }
    let q = n / 4;
    for i in 0..q {
        f[2 * q + i] = f[2 * q + i].add(f[3 * q + i]);
    }
    for i in 0..q {
        f[q + i] = f[q + i].add(f[2 * q + i]);
    }
    let (a, b) = f.split_at_mut(n / 2);
    taylor(a);
    taylor(b);
}

/// One Taylor step on a sub-block: f2 += f3, f1 += f2 (quarters of `blk`).
fn taylor_step(blk: &mut [P256]) {
    let q = blk.len() / 4;
    let (_, rest) = blk.split_at_mut(q);
    let (f1, rest) = rest.split_at_mut(q);
    let (f2, f3) = rest.split_at_mut(q);
    for i in 0..q {
        f2[i] = f2[i].add(f3[i]);
        f1[i] = f1[i].add(f2[i]);
    }
}

/// `taylor` on every block of size `bsz` of `f`, level by level (a parent step precedes its
/// children; disjoint sub-blocks commute), parallel over sub-blocks or within one.
fn taylor_par(f: &mut [P256], bsz: usize, threads: usize) {
    let n = f.len();
    let mut sz = bsz;
    while sz >= 4 {
        if threads <= 1 || n / sz >= threads || sz < 8192 {
            par_fill_aligned(f, threads, sz, |_, chunk| {
                for blk in chunk.chunks_mut(sz) {
                    taylor_step(blk);
                }
            });
        } else {
            for blk in f.chunks_mut(sz) {
                let q = sz / 4;
                let (_, rest) = blk.split_at_mut(q);
                let (f1, rest) = rest.split_at_mut(q);
                let (f2, f3) = rest.split_at_mut(q);
                let c = q.div_ceil(threads);
                std::thread::scope(|s| {
                    for ((a, b), d) in f1.chunks_mut(c).zip(f2.chunks_mut(c)).zip(f3.chunks(c)) {
                        s.spawn(move || {
                            for i in 0..a.len() {
                                b[i] = b[i].add(d[i]);
                                a[i] = a[i].add(b[i]);
                            }
                        });
                    }
                });
            }
        }
        sz /= 2;
    }
}

fn horner(cs: &[P256], x: P256) -> P256 {
    cs.iter().rev().fold(P256::ZERO, |acc, &c| c.add(x.mul(acc)))
}

/// `out[i] = offset + sum_{bit b of i} basis[b]`, `2^k` entries (`k = basis.len()`).
fn span(offset: P256, basis: &[P256]) -> Vec<P256> {
    let mut out = vec![P256::ZERO; 1usize << basis.len()];
    out[0] = offset;
    for (b, &v) in basis.iter().enumerate() {
        let h = 1usize << b;
        for i in 0..h {
            out[h + i] = out[i].add(v);
        }
    }
    out
}

/// `f(offset + sum_b c_b basis[b])` at every index `c` (bit `b` of the index is `c_b`),
/// `2^basis.len()` values.
pub fn eval_subspace(coeffs: &[P256], offset: P256, basis: &[P256], threads: usize) -> Vec<P256> {
    let k = basis.len();
    let n = 1usize << k;
    let used = coeffs.iter().rposition(|c| !c.is_zero()).map_or(0, |i| i + 1);
    if used == 0 {
        return vec![P256::ZERO; n];
    }
    let l = used.next_power_of_two();
    // Per-depth parameters, shared by every subproblem at that depth.
    struct Depth {
        powers: Vec<P256>,
        z: Vec<P256>,
    }
    let mut depths: Vec<Depth> = Vec::new();
    let (mut s, mut bs) = (offset, basis.to_vec());
    let mut block = l;
    while block > 1 && !bs.is_empty() {
        let Some(inv) = bs[0].inverse() else {
            return span(offset, basis).iter().map(|&x| horner(coeffs, x)).collect();
        };
        let mut powers = Vec::with_capacity(block);
        let mut p = P256::ONE;
        for _ in 0..block {
            powers.push(p);
            p = p.mul(bs[0]);
        }
        let t = s.mul(inv);
        let gamma: Vec<P256> = bs[1..].iter().map(|b| b.mul(inv)).collect();
        let z = span(t, &gamma);
        s = t.square().add(t);
        bs = gamma.iter().map(|g| g.square().add(*g)).collect();
        depths.push(Depth { powers, z });
        block /= 2;
    }
    let d_end = depths.len();
    // Phase 1: coefficients, top-down. Block p of depth d is a[p*B..(p+1)*B], B = l >> d.
    let mut a = vec![P256::ZERO; l];
    a[..used].copy_from_slice(&coeffs[..used]);
    let mut tmp = vec![P256::ZERO; l];
    for (d, dp) in depths.iter().enumerate() {
        let bsz = l >> d;
        let src = &a;
        par_fill(&mut tmp, threads, |start, chunk| {
            // Scale, then Taylor-expand, block by block (chunks are block-aligned when the
            // block is at least the chunk; otherwise the chunk holds whole blocks).
            for (i, v) in chunk.iter_mut().enumerate() {
                let g = start + i;
                *v = src[g].mul(dp.powers[g % bsz]);
            }
        });
        // Taylor per block, then split even/odd into the two halves.
        taylor_par(&mut tmp, bsz, threads);
        let src = &tmp;
        let h = bsz / 2;
        par_fill(&mut a, threads, |start, chunk| {
            for (i, v) in chunk.iter_mut().enumerate() {
                let g = start + i;
                let (base, j) = (g - g % bsz, g % bsz);
                *v = if j < h { src[base + 2 * j] } else { src[base + 2 * (j - h) + 1] };
            }
        });
    }
    // Phase 2: values, bottom-up. Block p of depth d is out[p*S..(p+1)*S], S = n >> d.
    let leaf_size = n >> d_end;
    let leaf_len = l >> d_end;
    let mut cur = vec![P256::ZERO; n];
    for (p, blk) in cur.chunks_mut(leaf_size).enumerate() {
        let v = if leaf_len == 1 { a[p] } else { horner(&a[p * leaf_len..(p + 1) * leaf_len], s) };
        blk.fill(v);
    }
    let mut nxt = vec![P256::ZERO; n];
    for d in (0..d_end).rev() {
        let size = n >> d;
        let h = size / 2;
        let z = &depths[d].z;
        let src = &cur;
        par_fill_aligned(&mut nxt, threads, 2, |start, chunk| {
            for (pi, pair) in chunk.chunks_mut(2).enumerate() {
                let g = (start / 2) + pi;
                let (blk, i) = (g / h, g % h);
                let g0 = src[blk * size + i];
                let g1 = src[blk * size + h + i];
                let e = g0.add(z[i].mul(g1));
                pair[0] = e;
                pair[1] = e.add(g1);
            }
        });
        std::mem::swap(&mut cur, &mut nxt);
    }
    cur
}

// ---------------------------------------------------------------------------------------------
// Hashing and Merkle trees (`Tower256CshakeMerkleController`)

const LEAF_CUSTOMIZATION: &[u8] = b"\x01MINIDREGG/TOWER256/MERKLE/LEAF/V1";
const NODE_CUSTOMIZATION: &[u8] = b"\x02MINIDREGG/TOWER256/MERKLE/NODE/V1";
const CHALLENGE_CUSTOMIZATION: &[u8] = b"MD-FRI-C";
const QUERY_CUSTOMIZATION: &[u8] = b"MD-FRI-Q";

fn cshake(customization: &[u8]) -> CShake256 {
    CShake256::from_core(CShake256Core::new(customization))
}

fn finish32(h: CShake256) -> Digest {
    let mut out = [0u8; 32];
    h.finalize_xof().read(&mut out);
    out
}

fn xof32(customization: &[u8], input: &[u8]) -> Digest {
    let mut h = cshake(customization);
    h.update(input);
    finish32(h)
}

const KECCAK_RC: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
];

/// Keccak-f[1600] on lanes `a[x + 5y]` (theta, rho and pi fused: `b[y + 5((2x + 3y) mod 5)] =
/// rot(a[x + 5y])`, then chi and iota). Checked against the `sha3` crate by the hashers' test.
#[inline]
pub fn keccak_f1600(a: &mut [u64; 25]) {
    for rc in KECCAK_RC {
        let c: [u64; 5] = core::array::from_fn(|x| a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20]);
        let d: [u64; 5] = core::array::from_fn(|x| c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1));
        let b = [
            a[0] ^ d[0],
            (a[6] ^ d[1]).rotate_left(44),
            (a[12] ^ d[2]).rotate_left(43),
            (a[18] ^ d[3]).rotate_left(21),
            (a[24] ^ d[4]).rotate_left(14),
            (a[3] ^ d[3]).rotate_left(28),
            (a[9] ^ d[4]).rotate_left(20),
            (a[10] ^ d[0]).rotate_left(3),
            (a[16] ^ d[1]).rotate_left(45),
            (a[22] ^ d[2]).rotate_left(61),
            (a[1] ^ d[1]).rotate_left(1),
            (a[7] ^ d[2]).rotate_left(6),
            (a[13] ^ d[3]).rotate_left(25),
            (a[19] ^ d[4]).rotate_left(8),
            (a[20] ^ d[0]).rotate_left(18),
            (a[4] ^ d[4]).rotate_left(27),
            (a[5] ^ d[0]).rotate_left(36),
            (a[11] ^ d[1]).rotate_left(10),
            (a[17] ^ d[2]).rotate_left(15),
            (a[23] ^ d[3]).rotate_left(56),
            (a[2] ^ d[2]).rotate_left(62),
            (a[8] ^ d[3]).rotate_left(55),
            (a[14] ^ d[4]).rotate_left(39),
            (a[15] ^ d[0]).rotate_left(41),
            (a[21] ^ d[1]).rotate_left(2),
        ];
        for y in 0..5 {
            for x in 0..5 {
                a[x + 5 * y] = b[x + 5 * y] ^ (!b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]);
            }
        }
        a[0] ^= rc;
    }
}

fn left_encode(out: &mut Vec<u8>, x: usize) {
    let bytes = x.to_be_bytes();
    let skip = bytes.iter().position(|&b| b != 0).unwrap_or(bytes.len() - 1);
    out.push((bytes.len() - skip) as u8);
    out.extend_from_slice(&bytes[skip..]);
}

/// The Keccak state of cSHAKE256(N = "", S = customization) after its customization block:
/// `bytepad(encode_string("") || encode_string(S), 136)`, one block for `S` under 130 bytes.
pub fn cshake256_midstate(customization: &[u8]) -> [u64; 25] {
    let mut block = Vec::new();
    left_encode(&mut block, 136);
    left_encode(&mut block, 0);
    left_encode(&mut block, 8 * customization.len());
    block.extend_from_slice(customization);
    assert!(block.len() <= 136, "customization fits one block");
    block.resize(136, 0);
    let mut a = [0u64; 25];
    for (i, lane) in block.chunks(8).enumerate() {
        a[i] ^= u64::from_le_bytes(lane.try_into().expect("8 bytes"));
    }
    keccak_f1600(&mut a);
    a
}

#[inline(always)]
fn limbs_of(d: &[u8; 32]) -> [u64; 4] {
    core::array::from_fn(|i| u64::from_le_bytes(d[8 * i..8 * i + 8].try_into().expect("8 bytes")))
}

#[inline(always)]
fn digest_of(a: &[u64; 25]) -> Digest {
    let mut out = [0u8; 32];
    for i in 0..4 {
        out[8 * i..8 * i + 8].copy_from_slice(&a[i].to_le_bytes());
    }
    out
}

/// The two Merkle hashers: one Keccak-f per hash from the customization midstate, the message
/// and the cSHAKE padding (0x04 after the data, 0x80 at byte 135) XORed in as lanes.
pub struct Hashers {
    leaf: [u64; 25],
    node: [u64; 25],
}

impl Default for Hashers {
    fn default() -> Self {
        Self::new()
    }
}

impl Hashers {
    pub fn new() -> Self {
        Self { leaf: cshake256_midstate(LEAF_CUSTOMIZATION), node: cshake256_midstate(NODE_CUSTOMIZATION) }
    }

    /// `xof leaf (0 :: envelope (encodeC v))`: `0, 0^32, 1, v` (66 bytes).
    #[inline]
    pub fn leaf(&self, v: &[u8; 32]) -> Digest {
        self.leaf_limbs(&limbs_of(v))
    }

    #[inline]
    pub fn leaf_limbs(&self, v: &[u64; 4]) -> Digest {
        let mut a = self.leaf;
        a[4] ^= 0x100 | (v[0] << 16);
        a[5] ^= (v[0] >> 48) | (v[1] << 16);
        a[6] ^= (v[1] >> 48) | (v[2] << 16);
        a[7] ^= (v[2] >> 48) | (v[3] << 16);
        a[8] ^= (v[3] >> 48) | (0x04 << 16);
        a[16] ^= 0x80 << 56;
        keccak_f1600(&mut a);
        digest_of(&a)
    }

    /// `xof node (1 :: envelope l ++ envelope r)`: `1, 0^32, 1, l, 0^32, 1, r` (131 bytes).
    #[inline]
    pub fn node(&self, l: &Digest, r: &Digest) -> Digest {
        let (l, r) = (limbs_of(l), limbs_of(r));
        let mut a = self.node;
        a[0] ^= 1;
        a[4] ^= 0x100 | (l[0] << 16);
        a[5] ^= (l[0] >> 48) | (l[1] << 16);
        a[6] ^= (l[1] >> 48) | (l[2] << 16);
        a[7] ^= (l[2] >> 48) | (l[3] << 16);
        a[8] ^= l[3] >> 48;
        a[12] ^= (1 << 16) | (r[0] << 24);
        a[13] ^= (r[0] >> 40) | (r[1] << 24);
        a[14] ^= (r[1] >> 40) | (r[2] << 24);
        a[15] ^= (r[2] >> 40) | (r[3] << 24);
        a[16] ^= (r[3] >> 40) | (0x04 << 24) | (0x80 << 56);
        keccak_f1600(&mut a);
        digest_of(&a)
    }
}

/// A cube tree with every level stored: `levels[t]` has `2^t` digests, `levels[0]` is the root,
/// and `levels[t][o] = node(levels[t+1][o], levels[t+1][o + 2^t])` (the root splits on address
/// bit 0). The leaf-hash level is dropped once its parent level exists unless `keep_leaves`.
pub struct Tree {
    pub levels: Vec<Vec<Digest>>,
}

impl Tree {
    pub fn root(&self) -> Digest {
        self.levels[0][0]
    }

    /// `cubePath` without its last (leaf-level) sibling, for an index below the half.
    pub fn pair_path(&self, k_bits: usize, index: usize) -> Vec<Digest> {
        (0..k_bits.saturating_sub(1))
            .map(|d| self.levels[d + 1][(index & ((2usize << d) - 1)) ^ (1usize << d)])
            .collect()
    }
}

/// Leaf hashes of `values` (tower bytes of each), in parallel.
pub fn leaf_hashes(hs: &Hashers, values: &[P256], threads: usize) -> Vec<Digest> {
    let mut leaves = vec![[0u8; 32]; values.len()];
    par_fill(&mut leaves, threads, |start, chunk| {
        for (i, d) in chunk.iter_mut().enumerate() {
            *d = hs.leaf_limbs(values[start + i].to_tower().limbs());
        }
    });
    leaves
}

/// The tree over leaf hashes (`2^k` of them). `store` keeps the internal levels.
pub fn tree_from_leaves(hs: &Hashers, leaves: Vec<Digest>, store: bool, threads: usize) -> Tree {
    let k = leaves.len().trailing_zeros() as usize;
    assert_eq!(leaves.len(), 1usize << k);
    let mut levels: Vec<Vec<Digest>> = vec![Vec::new(); k + 1];
    let mut cur = leaves;
    for t in (0..k).rev() {
        let h = 1usize << t;
        let mut next = vec![[0u8; 32]; h];
        let src = &cur;
        par_fill(&mut next, threads, |start, chunk| {
            for (i, d) in chunk.iter_mut().enumerate() {
                let o = start + i;
                *d = hs.node(&src[o], &src[o + h]);
            }
        });
        let child = std::mem::replace(&mut cur, next);
        if store && t + 1 < k {
            levels[t + 1] = child;
        }
    }
    levels[0] = cur;
    Tree { levels }
}

// ---------------------------------------------------------------------------------------------
// Codecs (`Theory/StreamCodec.lean`, `Tower256CshakeMerkleController` framing), as in the
// conformance kernel.

fn encode_nat(out: &mut Vec<u8>, mut value: u128) {
    while value > 0 {
        out.push((value % 255) as u8);
        value /= 255;
    }
    out.push(255);
}

fn encode_nat_le32(out: &mut Vec<u8>, bytes: &Digest) {
    let mut limbs: Vec<u32> =
        bytes.chunks(4).map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]])).collect();
    loop {
        while limbs.last() == Some(&0) {
            limbs.pop();
        }
        if limbs.is_empty() {
            break;
        }
        let mut rem: u64 = 0;
        for limb in limbs.iter_mut().rev() {
            let cur = (rem << 32) | u64::from(*limb);
            *limb = (cur / 255) as u32;
            rem = cur % 255;
        }
        out.push(rem as u8);
    }
    out.push(255);
}

fn encode_length(out: &mut Vec<u8>, n: usize) {
    out.resize(out.len() + n, 0);
    out.push(1);
}

fn envelope(out: &mut Vec<u8>, bytes: &[u8]) {
    encode_length(out, bytes.len());
    out.extend_from_slice(bytes);
}

/// `requestStream` encoding (the inverse of `tower256_fri_prove::decode_request`), so
/// benchmarks and the GPU harness can write requests.
pub fn encode_request(req: &ProveRequest) -> Vec<u8> {
    let mut out = Vec::new();
    encode_nat(&mut out, req.statement_bytes.len() as u128);
    out.extend_from_slice(&req.statement_bytes);
    encode_nat(&mut out, req.ell as u128);
    encode_nat(&mut out, req.m as u128);
    encode_nat(&mut out, req.query_count as u128);
    encode_nat(&mut out, req.beta.len() as u128);
    for b in &req.beta {
        out.extend_from_slice(&b.to_le_bytes());
    }
    out.extend_from_slice(&req.offset.to_le_bytes());
    encode_nat(&mut out, req.degree.len() as u128);
    for &d in &req.degree {
        encode_nat(&mut out, d as u128);
    }
    encode_nat(&mut out, req.input_word.len() as u128);
    for c in &req.input_word {
        out.extend_from_slice(&c.to_le_bytes());
    }
    out
}

fn basis_prefix(req: &ProveRequest) -> Vec<u8> {
    let mut out = Vec::new();
    let mut tmp = Vec::new();
    encode_length(&mut tmp, req.ell);
    envelope(&mut out, &tmp);
    tmp.clear();
    encode_length(&mut tmp, req.m);
    envelope(&mut out, &tmp);
    envelope(&mut out, &req.offset.to_le_bytes());
    for (i, b) in req.beta.iter().enumerate() {
        let mut inner = Vec::new();
        tmp.clear();
        encode_length(&mut tmp, i);
        envelope(&mut inner, &tmp);
        envelope(&mut inner, &b.to_le_bytes());
        envelope(&mut out, &inner);
    }
    out
}

fn push_root(out: &mut Vec<u8>, n: usize, root: &Digest) {
    let mut tmp = Vec::new();
    encode_length(&mut tmp, n);
    envelope(out, &tmp);
    envelope(out, root);
}

/// Gauss-Jordan; the solution is unique, so it is the conformance kernel's.
fn interpolate(points: &[(P256, P256)]) -> Result<Vec<P256>, FriProveError> {
    let n = points.len();
    let mut rows: Vec<Vec<P256>> = points
        .iter()
        .map(|&(x, y)| {
            let mut row = Vec::with_capacity(n + 1);
            let mut p = P256::ONE;
            for _ in 0..n {
                row.push(p);
                p = p.mul(x);
            }
            row.push(y);
            row
        })
        .collect();
    for col in 0..n {
        let p = (col..n).find(|&r| !rows[r][col].is_zero()).ok_or(FriProveError::SingularInterpolation)?;
        rows.swap(p, col);
        let inv = rows[col][col].inverse().ok_or(FriProveError::SingularInterpolation)?;
        for x in rows[col].iter_mut() {
            *x = x.mul(inv);
        }
        let pivot_row = rows[col].clone();
        for (r, row) in rows.iter_mut().enumerate() {
            if r != col && !row[col].is_zero() {
                let f = row[col];
                for (x, &y) in row.iter_mut().zip(pivot_row.iter()) {
                    *x = x.add(f.mul(y));
                }
            }
        }
    }
    Ok(rows.into_iter().map(|row| row[n]).collect())
}

// ---------------------------------------------------------------------------------------------
// The prover

/// Wall time of each phase, nanoseconds.
#[derive(Clone, Copy, Debug, Default)]
pub struct Timings {
    pub encode_ns: u128,
    pub merkle_ns: u128,
    pub folds_ns: u128,
    pub openings_ns: u128,
    /// Challenges, seeds, interpolation, final word, receipt framing.
    pub other_ns: u128,
    pub total_ns: u128,
    /// Keccak-f calls in Merkle trees (one per leaf and per node).
    pub merkle_keccak_f: u64,
    /// Tower256 multiplications in the encode, the folds.
    pub encode_mults: u64,
    pub fold_mults: u64,
}

/// What the GPU-assisted prover needs to reproduce, besides the receipt: the level-0 word's
/// root and every committed root, in order.
pub struct Proof {
    pub receipt: Vec<u8>,
    pub roots: Vec<Digest>,
    pub timings: Timings,
}

/// The honest receipt for `req`, the conformance kernel's bytes, with `threads` workers.
pub fn prove_fast(req: &ProveRequest, threads: usize) -> Result<Proof, FriProveError> {
    let t_all = Instant::now();
    let mut tm = Timings::default();
    let (ell, m, q) = (req.ell, req.m, req.query_count);
    if m > ell || ell > MAX_ELL || ell == 0 {
        return Err(FriProveError::Shape { ell, m });
    }
    if req.beta.len() != ell {
        return Err(FriProveError::BasisLength { ell, len: req.beta.len() });
    }
    let final_degree = req.degree.get(m).copied().unwrap_or(0);
    let last_size = 1usize << (ell - m);
    if final_degree > last_size {
        return Err(FriProveError::FinalDegree { degree: final_degree, size: last_size });
    }
    let t0 = Instant::now();
    let beta: Vec<P256> = req.beta.iter().map(|&b| P256::from_tower(b)).collect();
    let offset = P256::from_tower(req.offset);
    // Images of the offset and the basis under A_j = (y -> y^2 + p_{j-1} y) o ... , and the
    // pivots p_j = A_j(beta_{ell-1-j}). A zero pivot is the conformance kernel's error; it
    // depends on no hash, so it is decided first.
    let mut imgs: Vec<Vec<P256>> = Vec::with_capacity(m + 1); // imgs[j] = [A_j(offset), A_j(beta_0..)]
    let mut pivots: Vec<P256> = Vec::with_capacity(m);
    let mut pinvs: Vec<P256> = Vec::with_capacity(m);
    let mut cur: Vec<P256> = std::iter::once(offset).chain(beta.iter().copied()).collect();
    for j in 0..m {
        let p = cur[1 + (ell - 1 - j)];
        let inv = p.inverse().ok_or(FriProveError::ZeroPivot(j))?;
        imgs.push(cur.clone());
        pivots.push(p);
        pinvs.push(inv);
        cur = cur.iter().map(|&y| y.square().add(p.mul(y))).collect();
    }
    imgs.push(cur);
    let hs = Hashers::new();
    let mut head = Vec::new();
    envelope(&mut head, &req.statement_bytes);
    envelope(&mut head, &basis_prefix(req));
    tm.other_ns += t0.elapsed().as_nanos();

    // Encode.
    let t0 = Instant::now();
    let coeffs: Vec<P256> = req.input_word.iter().map(|&c| P256::from_tower(c)).collect();
    let w0 = eval_subspace(&coeffs, offset, &beta, threads);
    tm.encode_ns += t0.elapsed().as_nanos();
    let used = coeffs.iter().rposition(|c| !c.is_zero()).map_or(0, |i| i + 1);
    if used > 1 {
        let l = used.next_power_of_two();
        let depth = (l.trailing_zeros() as usize).min(ell);
        tm.encode_mults = (depth as u64) * ((1u64 << ell) / 2) + (depth as u64) * l as u64;
    }

    let mut words: Vec<Vec<P256>> = vec![w0];
    let mut trees: Vec<Tree> = Vec::with_capacity(m);
    let mut roots: Vec<Digest> = Vec::with_capacity(m + 1);
    let mut challenges: Vec<Tower256> = Vec::with_capacity(m);
    let commit = |w: &[P256], store: bool, tm: &mut Timings| -> Tree {
        let t0 = Instant::now();
        let leaves = leaf_hashes(&hs, w, threads);
        let tree = tree_from_leaves(&hs, leaves, store, threads);
        tm.merkle_ns += t0.elapsed().as_nanos();
        tm.merkle_keccak_f += 2 * w.len() as u64 - 1;
        tree
    };
    // Level 0 is committed and (when m > 0) opened.
    let tree0 = commit(&words[0], m > 0, &mut tm);
    roots.push(tree0.root());
    trees.push(tree0);
    for j in 0..m {
        let t0 = Instant::now();
        let mut input = head.clone();
        for (n, r) in roots.iter().enumerate().take(j + 1) {
            push_root(&mut input, n, r);
        }
        let alpha_t = Tower256::from_le_bytes(xof32(CHALLENGE_CUSTOMIZATION, &input));
        let alpha = P256::from_tower(alpha_t);
        tm.other_ns += t0.elapsed().as_nanos();
        let t0 = Instant::now();
        let k = ell - j;
        let half = 1usize << (k - 1);
        // c_i = (dom_j[i] + alpha) / p_j over i < half: the span of the scaled images.
        let pinv = pinvs[j];
        let im = &imgs[j];
        let scaled: Vec<P256> = im[1..k].iter().map(|&b| b.mul(pinv)).collect();
        let c = span(im[0].add(alpha).mul(pinv), &scaled);
        let w = &words[j];
        let mut next = vec![P256::ZERO; half];
        par_fill(&mut next, threads, |start, chunk| {
            for (i, v) in chunk.iter_mut().enumerate() {
                let g = start + i;
                let (l, r) = (w[g], w[g + half]);
                *v = l.add(c[g].mul(l.add(r)));
            }
        });
        tm.fold_mults += half as u64;
        tm.folds_ns += t0.elapsed().as_nanos();
        challenges.push(alpha_t);
        if j + 1 < m {
            let tree = commit(&next, true, &mut tm);
            roots.push(tree.root());
            trees.push(tree);
        }
        words.push(next);
    }
    let t0 = Instant::now();
    let im = &imgs[m];
    let dom_m = span(im[0], &im[1..1 + (ell - m)]);
    let wm = &words[m];
    let points: Vec<(P256, P256)> = (0..final_degree).map(|n| (dom_m[n % last_size], wm[n])).collect();
    let fcoeffs = interpolate(&points)?;
    tm.other_ns += t0.elapsed().as_nanos();
    if m > 0 {
        let last: Vec<P256> = dom_m.iter().map(|&x| horner(&fcoeffs, x)).collect();
        let tree = commit(&last, false, &mut tm);
        roots.push(tree.root());
    }

    let t0 = Instant::now();
    let mut prefix = head;
    for (n, r) in roots.iter().enumerate().take(m + 1) {
        push_root(&mut prefix, n, r);
    }
    for c in &challenges {
        envelope(&mut prefix, &c.to_le_bytes());
    }
    let mut seed_base = cshake(QUERY_CUSTOMIZATION);
    seed_base.update(&prefix);
    let seed_bits = ell - 1;
    let seeds: Vec<usize> = (0..q)
        .map(|a| {
            let mut tmp = Vec::new();
            encode_length(&mut tmp, a);
            let mut env = Vec::new();
            envelope(&mut env, &tmp);
            let mut h = seed_base.clone();
            h.update(&env);
            let d = finish32(h);
            let v = u64::from_le_bytes(d[..8].try_into().expect("8 bytes"));
            (if seed_bits >= 64 { v } else { v & ((1u64 << seed_bits) - 1) }) as usize
        })
        .collect();
    let mut out = Vec::new();
    encode_nat(&mut out, (m + 1) as u128);
    for r in roots.iter().take(m + 1) {
        encode_nat_le32(&mut out, r);
    }
    encode_nat(&mut out, m as u128);
    for c in &challenges {
        out.extend_from_slice(&c.to_le_bytes());
    }
    encode_nat(&mut out, q as u128);
    for &s in &seeds {
        encode_nat(&mut out, s as u128);
    }
    tm.other_ns += t0.elapsed().as_nanos();
    let t0 = Instant::now();
    encode_nat(&mut out, m as u128);
    for j in 0..m {
        encode_nat(&mut out, q as u128);
        let w = &words[j];
        let k = ell - j;
        let half = 1usize << (k - 1);
        for &s in &seeds {
            let i = s % half;
            out.extend_from_slice(&w[i].tower_bytes());
            out.extend_from_slice(&w[i + half].tower_bytes());
            let path = trees[j].pair_path(k, i);
            encode_nat(&mut out, path.len() as u128);
            for d in &path {
                encode_nat_le32(&mut out, d);
            }
        }
    }
    tm.openings_ns += t0.elapsed().as_nanos();
    let t0 = Instant::now();
    encode_nat(&mut out, fcoeffs.len() as u128);
    for c in &fcoeffs {
        out.extend_from_slice(&c.tower_bytes());
    }
    tm.other_ns += t0.elapsed().as_nanos();
    tm.total_ns = t_all.elapsed().as_nanos();
    Ok(Proof { receipt: out, roots, timings: tm })
}

/// Work 9104's byte entry through the fast prover (one thread).
pub fn tower256_additive_fri_prove_bytes_fast(request: &[u8]) -> Result<Vec<u8>, FriProveError> {
    let req = crate::tower256_fri_prove::decode_request(request)?;
    prove_fast(&req, 1).map(|p| p.receipt)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rnd(s: &mut u64) -> Tower256 {
        Tower256::from_limbs([splitmix(s), splitmix(s), splitmix(s), splitmix(s)])
    }

    #[test]
    fn poly_basis_is_a_field_isomorphism() {
        let mut s = 7u64;
        for _ in 0..64 {
            let (a, b) = (rnd(&mut s), rnd(&mut s));
            let (pa, pb) = (P256::from_tower(a), P256::from_tower(b));
            assert_eq!(pa.to_tower(), a);
            assert_eq!(pa.mul(pb).to_tower(), a.mul(b));
            assert_eq!(pa.add(pb).to_tower(), a.add(b));
        }
        assert_eq!(P256::from_tower(Tower256::ONE), P256::ONE);
    }

    #[test]
    fn raw_keccak_hashers_match_sha3_crate() {
        let hs = Hashers::new();
        let mut s = 3u64;
        for _ in 0..64 {
            let v = rnd(&mut s).to_le_bytes();
            let w = rnd(&mut s).to_le_bytes();
            let mut leaf_in = vec![0u8];
            envelope(&mut leaf_in, &v);
            assert_eq!(hs.leaf(&v), xof32(LEAF_CUSTOMIZATION, &leaf_in));
            let mut node_in = vec![1u8];
            envelope(&mut node_in, &v);
            envelope(&mut node_in, &w);
            assert_eq!(hs.node(&v, &w), xof32(NODE_CUSTOMIZATION, &node_in));
        }
    }

    #[test]
    fn taylor_expansion_is_exact() {
        let mut s = 11u64;
        for logn in 0..7 {
            let n = 1usize << logn;
            let f: Vec<P256> = (0..n).map(|_| P256::from_tower(rnd(&mut s))).collect();
            let mut t = f.clone();
            taylor(&mut t);
            let x = P256::from_tower(rnd(&mut s));
            let y = x.square().add(x);
            let g0: Vec<P256> = t.iter().step_by(2).copied().collect();
            let g1: Vec<P256> = t.iter().skip(1).step_by(2).copied().collect();
            assert_eq!(horner(&f, x), horner(&g0, y).add(x.mul(horner(&g1, y))));
            let mut tp = f.clone();
            taylor_par(&mut tp, n, 3);
            assert_eq!(tp, t);
        }
    }
}
