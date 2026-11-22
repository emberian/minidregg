//! Real Succinct Zero-Knowledge Sensory Provenance, Box-Blur & Ambient-Envelope Certificates
//! (*Rainbows End* Wearable SHE Organ #4 — "Epiphany Lens" v2).
//!
//! Mirrors `/Users/ember/dev/minidregg/Assurance/SensoryRoiZeroKnowledge.lean`:
//! - **ZERO Capture-Time `sumCommit` / ZERO Symmetric `hw_key` / ZERO Cleartext `tile_sum`:**
//!   The sensor enclave commits ONLY to raw salted per-tile commitments (`tile_merkle_root`, for
//!   `O(|U| log N)` zero-bystander-leakage ROI reveals) and the salted HVZK coset Reed-Solomon
//!   multilinear table commitment (`rt_raw`, `rate = 1/4` over `BabyBear`), signing the frame header
//!   with **asymmetric post-quantum `WotsCshake256`** (`crate::pq_biscuit`, single-key or XMSS tree)
//!   so verifiers hold ONLY `EnclavePublicKey` and CANNOT forge headers.
//! - **Real `BabyBearExt4` (`u^4 = 11`, `|Ext4| ≈ 2^{123.63}`) HVZK Sumcheck + `UD-100` BaseFold/FRI:**
//!   - `BlurDownscaleZkProof`: Untrusted-worker ZK proof against `rt_raw` that every blurred tile
//!     `t ∈ S_blur` satisfies `sum_{u=0}^{tile_len-1} Raw[t, u] = tile_len * B[t] + rem[t]` with
//!     `B[t] ∈ [0, 256)` public and `rem[t] ∈ [0, tile_len)` committed via `log2(tile_len)` Boolean
//!     bit columns `b_k (1 - b_k) = 0`, zero intra-tile pixel leakage on the ideal sumcheck view.
//!   - `AmbientEnvelopeZkProof`: True zero-tile-leakage ambient threshold proof against `rt_raw`
//!     proving `sum_{t ∈ S, u} Raw[t, u] = claimed_total <= threshold` with ZERO per-tile sums on
//!     the wire (revealing strictly `claimed_total`; note singleton subsets reveal that tile's sum).
//!   - Both proofs use `rate = 1/4`, `q = 148` distinct coset-pair queries, and `16`-bit PoW grinding:
//!     bare single-trial UDR query term `(5/8)^{148} < 2^{-100.35}` (WITHOUT relying on PoW), and
//!     `(21/32)^{148} / 2^{16} < 2^{-105.94}` under `η = 1/32` slack + 16-bit grinding work
//!     (`SensoryRoiZeroKnowledge.ud100_query_arithmetic_rate4_q148_pow16`).
//!   - **Enforced Lifetime Privacy & Explicit `[OPEN]` Seams:** `RawPcsCommitment` enforces an atomic
//!     cumulative column-opening budget (`<= shape.c` opened columns across all proofs against one
//!     `rt_raw`). Full composed ROM/FS/FRI/correlated-agreement (`[BCIKS20]` Thm 1.7) verifier
//!     soundness, full-wire joint HVZK + seeded CSPRNG reduction, and RFC 8391 §4.1.9 durable NVM
//!     OTS-index persistence remain explicit `[OPEN]` seams.

#![deny(warnings)]

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fmt;
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};
use std::sync::Arc;

use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    CShake256, CShake256Core,
};

use crate::babybear::P as BABYBEAR_P;
use crate::pq_biscuit::{PqSigBackend, WotsCshake256, WOTS_SIG_LEN};

/// 32-byte SP 800-185 `cSHAKE256` digest.
pub type Digest = [u8; 32];

/// 256-bit (32-byte) per-tile hardware TRNG salt.
pub type Salt256 = [u8; 32];

/// 128-bit (16-byte) per-column PCS leaf salt.
pub type Salt128 = [u8; 16];

/// BabyBear prime `p = 2^31 - 2^27 + 1 = 2,013,265,921`.
pub const P_U32: u32 = BABYBEAR_P as u32;
/// Primitive generator `g = 31` of `F_p^*`.
pub const G_PRIM: u32 = 31;
/// `2^{-1} mod p`.
pub const INV2_BB: u32 = ((BABYBEAR_P + 1) / 2) as u32;
/// Quartic non-residue `W = 11` for irreducible `X^4 - 11` (`Selvage/BabyBearExt4.lean`).
pub const W_EXT4: u32 = 11;

/// Reed-Solomon blowup factor (`rate = 1/4`).
pub const PCS_BLOWUP: usize = 4;
/// Distinct coset-pair queries: bare UDR `(5/8)^{148} < 2^{-100.35}` (WITHOUT PoW),
/// and `(21/32)^{148} / 2^{16} < 2^{-105.94}` under `η = 1/32` slack + 16-bit grinding work.
pub const UD100_QUERIES: usize = 148;
/// Grinding PoW bits (`16` leading zero bits on `CUST_POW` digest).
pub const POW_GRIND_BITS: u32 = 16;
/// Minimum data columns per PCS row (`C >= 1024 > 3 * 296 = 888` opened columns across 3 proofs).
pub const MIN_PCS_COLS: usize = 1024;
/// Maximum samples per tile/window (`≤ 65,536`, power of two).
pub const MAX_TILE_SAMPLES: usize = 65_536;
/// Shared maximum tiles per frame across sealing, proving, wire decoding, and verification.
pub const MAX_FRAME_TILES: usize = 65_536;
/// Shared maximum raw PCS rows (`r_d <= 2048`, capping raw samples at `<= 8,388,608` so every
/// valid shape cleanly round-trips through the wire decoder).
pub const MAX_RAW_PCS_ROWS: usize = 2048;

const MAX_WIRE_RAW_COL_VALS: usize = 2 * UD100_QUERIES * MAX_RAW_PCS_ROWS;
const MAX_WIRE_AUX_BB_VALS: usize = 2 * UD100_QUERIES * 1024;
const MAX_WIRE_AUX_EXT_VALS: usize = 2 * UD100_QUERIES * 16;

/// Domain-separation customization strings (v2, byte-identical to `SensoryRoiZeroKnowledge.lean`).
pub const CUST_RAW_TILE: &[u8] = b"MINIDREGG/SENSORY_ROI/RAW_TILE/V2";
pub const CUST_EMPTY_LEAF: &[u8] = b"MINIDREGG/SENSORY_ROI/EMPTY_LEAF/V2";
pub const CUST_MERKLE_NODE: &[u8] = b"MINIDREGG/SENSORY_ROI/MERKLE_NODE/V2";
pub const CUST_XMSS_LEAF: &[u8] = b"MINIDREGG/SENSORY_ROI/XMSS_LEAF/V2";
pub const CUST_FRAME_SEAL: &[u8] = b"MINIDREGG/SENSORY_ROI/FRAME_SEAL/V2";

/// PCS, BaseFold/FRI, Fiat-Shamir, and PoW domain-separation customization strings.
pub const CUST_RAW_PCS_LEAF: &[u8] = b"MINIDREGG/SENSORY_ROI/RAW_PCS_LEAF/V2";
pub const CUST_RAW_PCS_NODE: &[u8] = b"MINIDREGG/SENSORY_ROI/RAW_PCS_NODE/V2";
pub const CUST_AUX_PCS_LEAF: &[u8] = b"MINIDREGG/SENSORY_ROI/AUX_PCS_LEAF/V2";
pub const CUST_AUX_PCS_NODE: &[u8] = b"MINIDREGG/SENSORY_ROI/AUX_PCS_NODE/V2";
pub const CUST_FRI_PAIR_LEAF: &[u8] = b"MINIDREGG/SENSORY_ROI/FRI_PAIR_LEAF/V2";
pub const CUST_FRI_NODE: &[u8] = b"MINIDREGG/SENSORY_ROI/FRI_NODE/V2";
pub const CUST_FS_INIT: &[u8] = b"MINIDREGG/SENSORY_ROI/FS_INIT/V2";
pub const CUST_FS_ABSORB: &[u8] = b"MINIDREGG/SENSORY_ROI/FS_ABSORB/V2";
pub const CUST_FS_SQUEEZE: &[u8] = b"MINIDREGG/SENSORY_ROI/FS_SQUEEZE/V2";
pub const CUST_POW: &[u8] = b"MINIDREGG/SENSORY_ROI/POW/V2";
pub const CUST_PROTO_AMBIENT: &[u8] = b"MINIDREGG/SENSORY_ROI/AMBIENT_ZK/V2";
pub const CUST_PROTO_BLUR: &[u8] = b"MINIDREGG/SENSORY_ROI/BLUR_ZK/V2";
pub const CUST_RNG_ENCLAVE: &[u8] = b"MINIDREGG/SENSORY_ROI/ENCLAVE_RNG/V2";
pub const CUST_RNG_PROVER_AMBIENT: &[u8] = b"MINIDREGG/SENSORY_ROI/PROVER_RNG_AMBIENT/V2";
pub const CUST_RNG_PROVER_BLUR: &[u8] = b"MINIDREGG/SENSORY_ROI/PROVER_RNG_BLUR/V2";
pub const CUST_XMSS_DERIVE: &[u8] = b"MINIDREGG/SENSORY_ROI/XMSS_DERIVE/V2";

const AMBIENT_WIRE_MAGIC: &[u8; 8] = b"SLVAMB02";
const BLUR_WIRE_MAGIC: &[u8; 8] = b"SLVBLR02";

/// Error returned when a sensor frame, ROI reveal, or ZK blur/ambient proof is refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SensoryRoiError {
    InvalidGeometry(&'static str),
    EmptyTile(usize),
    OversizedTile { tile_idx: usize, len: usize },
    SaltReuseDetected { tile_idx: usize },
    OtsBudgetExhausted,
    RawCommitmentOpeningBudgetExhausted { opened_cols: usize, capacity_cols: usize },
    EnclaveKeyMismatch,
    InvalidEnclaveSignature,
    TileIndexOutOfBounds { tile_idx: usize, max_tiles: usize },
    DuplicateTileIndex(usize),
    MerklePathLengthMismatch { expected: usize, actual: usize },
    MerklePathMismatch { tile_idx: usize },
    MerkleMultiProofInvalid(&'static str),
    BabyBearWrapRisk { total_samples: u64 },
    ThresholdExceeded { claimed: u64, threshold: u64 },
    ClaimedTotalOutOfRange { claimed: u64, max_possible: u64 },
    InvalidBlurPublicArray(&'static str),
    SumcheckRoundFailed { stage: &'static str, round: usize },
    SumcheckTerminalFailed(&'static str),
    InvalidPowGrinding,
    FriConsistencyFailed { round: usize, query_idx: usize },
    NonCanonicalFieldElement,
    MalformedWireProof(&'static str),
}

impl fmt::Display for SensoryRoiError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for SensoryRoiError {}

#[inline]
fn ct_eq_digest(a: &Digest, b: &Digest) -> bool {
    let mut diff = 0u8;
    for i in 0..32 {
        diff |= a[i] ^ b[i];
    }
    diff == 0
}

// ============================================================================
// §1. `BabyBear` (`u32`), `BabyBearExt4` (`u^4 = 11`), Coset NTT, & Transcript
// ============================================================================

#[inline(always)]
pub fn bb_add(a: u32, b: u32) -> u32 {
    let s = (a as u64) + (b as u64);
    if s >= BABYBEAR_P {
        (s - BABYBEAR_P) as u32
    } else {
        s as u32
    }
}

#[inline(always)]
pub fn bb_sub(a: u32, b: u32) -> u32 {
    if a >= b {
        a - b
    } else {
        (P_U32 - b) + a
    }
}

#[inline(always)]
pub fn bb_neg(a: u32) -> u32 {
    if a == 0 {
        0
    } else {
        P_U32 - a
    }
}

#[inline(always)]
pub fn bb_mul(a: u32, b: u32) -> u32 {
    (((a as u64) * (b as u64)) % BABYBEAR_P) as u32
}

#[inline]
pub fn bb_pow(mut base: u32, mut exp: u64) -> u32 {
    let mut acc = 1u32;
    base = ((base as u64) % BABYBEAR_P) as u32;
    while exp > 0 {
        if (exp & 1) != 0 {
            acc = bb_mul(acc, base);
        }
        base = bb_mul(base, base);
        exp >>= 1;
    }
    acc
}

#[inline]
pub fn bb_inv(a: u32) -> Option<u32> {
    let c = ((a as u64) % BABYBEAR_P) as u32;
    if c == 0 {
        None
    } else {
        Some(bb_pow(c, BABYBEAR_P - 2))
    }
}

/// Principal `n`-th root of unity in BabyBear (`n` power of two `<= 2^27`).
pub fn root_of_unity_bb(n: usize) -> u32 {
    assert!(n.is_power_of_two());
    let lg = n.trailing_zeros();
    assert!(lg <= 27);
    bb_pow(G_PRIM, (BABYBEAR_P - 1) >> lg)
}

/// Canonical coset shift `ζ_ν = 31^{2^{23 - ν}} mod P` (strictly disjoint from the `2^ν` subgroup).
#[inline]
pub fn canonical_coset_shift_bb(log_n: usize) -> u32 {
    assert!(log_n <= 23);
    bb_pow(G_PRIM, 1u64 << (23 - log_n))
}

/// Element `c_0 + c_1 u + c_2 u^2 + c_3 u^3` in `BabyBear[u] / (u^4 - 11)` (`|Ext4| ≈ 2^{123.63}`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Ext4(pub [u32; 4]);

impl Ext4 {
    pub const ZERO: Self = Self([0, 0, 0, 0]);
    pub const ONE: Self = Self([1, 0, 0, 0]);

    #[inline(always)]
    pub const fn from_bb(x: u32) -> Self {
        Self([x, 0, 0, 0])
    }

    #[inline(always)]
    pub fn from_u64(x: u64) -> Self {
        Self([(x % BABYBEAR_P) as u32, 0, 0, 0])
    }

    #[inline(always)]
    pub fn is_zero(self) -> bool {
        self.0 == [0, 0, 0, 0]
    }

    #[inline(always)]
    pub fn is_canonical(self) -> bool {
        self.0[0] < P_U32 && self.0[1] < P_U32 && self.0[2] < P_U32 && self.0[3] < P_U32
    }

    #[inline(always)]
    pub fn add(self, rhs: Self) -> Self {
        Self([
            bb_add(self.0[0], rhs.0[0]),
            bb_add(self.0[1], rhs.0[1]),
            bb_add(self.0[2], rhs.0[2]),
            bb_add(self.0[3], rhs.0[3]),
        ])
    }

    #[inline(always)]
    pub fn sub(self, rhs: Self) -> Self {
        Self([
            bb_sub(self.0[0], rhs.0[0]),
            bb_sub(self.0[1], rhs.0[1]),
            bb_sub(self.0[2], rhs.0[2]),
            bb_sub(self.0[3], rhs.0[3]),
        ])
    }

    #[inline(always)]
    pub fn neg(self) -> Self {
        Self([
            bb_neg(self.0[0]),
            bb_neg(self.0[1]),
            bb_neg(self.0[2]),
            bb_neg(self.0[3]),
        ])
    }

    #[inline(always)]
    pub fn scale_bb(self, c: u32) -> Self {
        Self([
            bb_mul(self.0[0], c),
            bb_mul(self.0[1], c),
            bb_mul(self.0[2], c),
            bb_mul(self.0[3], c),
        ])
    }

    #[inline]
    pub fn mul(self, rhs: Self) -> Self {
        #[inline(always)]
        fn k2_mul(x: [u32; 2], y: [u32; 2]) -> [u32; 2] {
            let m0 = bb_mul(x[0], y[0]);
            let m1 = bb_mul(x[1], y[1]);
            let m2 = bb_mul(bb_add(x[0], x[1]), bb_add(y[0], y[1]));
            [
                bb_add(m0, bb_mul(W_EXT4, m1)),
                bb_sub(m2, bb_add(m0, m1)),
            ]
        }
        let a0 = [self.0[0], self.0[2]];
        let a1 = [self.0[1], self.0[3]];
        let b0 = [rhs.0[0], rhs.0[2]];
        let b1 = [rhs.0[1], rhs.0[3]];
        let p0 = k2_mul(a0, b0);
        let p1 = k2_mul(a1, b1);
        let p_sum = k2_mul(
            [bb_add(a0[0], a1[0]), bb_add(a0[1], a1[1])],
            [bb_add(b0[0], b1[0]), bb_add(b0[1], b1[1])],
        );
        let odd = [
            bb_sub(p_sum[0], bb_add(p0[0], p1[0])),
            bb_sub(p_sum[1], bb_add(p0[1], p1[1])),
        ];
        let even = [bb_add(p0[0], bb_mul(W_EXT4, p1[1])), bb_add(p0[1], p1[0])];
        Self([even[0], odd[0], even[1], odd[1]])
    }

    #[inline]
    pub fn sq(self) -> Self {
        self.mul(self)
    }

    pub fn inv(self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }
        let a0 = [self.0[0], self.0[2]];
        let a1 = [self.0[1], self.0[3]];
        let a0_sq = [
            bb_add(bb_mul(a0[0], a0[0]), bb_mul(W_EXT4, bb_mul(a0[1], a0[1]))),
            bb_mul(2, bb_mul(a0[0], a0[1])),
        ];
        let a1_sq = [
            bb_add(bb_mul(a1[0], a1[0]), bb_mul(W_EXT4, bb_mul(a1[1], a1[1]))),
            bb_mul(2, bb_mul(a1[0], a1[1])),
        ];
        let n0 = bb_sub(a0_sq[0], bb_mul(W_EXT4, a1_sq[1]));
        let n1 = bb_sub(a0_sq[1], a1_sq[0]);
        let n_bb = bb_sub(bb_mul(n0, n0), bb_mul(W_EXT4, bb_mul(n1, n1)));
        let inv_n = bb_inv(n_bb)?;
        let ni = [bb_mul(n0, inv_n), bb_mul(bb_neg(n1), inv_n)];
        let even = [
            bb_add(bb_mul(a0[0], ni[0]), bb_mul(W_EXT4, bb_mul(a0[1], ni[1]))),
            bb_add(bb_mul(a0[0], ni[1]), bb_mul(a0[1], ni[0])),
        ];
        let odd = [
            bb_neg(bb_add(
                bb_mul(a1[0], ni[0]),
                bb_mul(W_EXT4, bb_mul(a1[1], ni[1])),
            )),
            bb_neg(bb_add(bb_mul(a1[0], ni[1]), bb_mul(a1[1], ni[0]))),
        ];
        Some(Self([even[0], odd[0], even[1], odd[1]]))
    }

    #[inline(always)]
    pub fn to_bytes(self) -> [u8; 16] {
        let mut out = [0u8; 16];
        for i in 0..4 {
            out[4 * i..4 * (i + 1)].copy_from_slice(&self.0[i].to_le_bytes());
        }
        out
    }

    pub fn from_bytes(bytes: &[u8; 16]) -> Result<Self, SensoryRoiError> {
        let mut c = [0u32; 4];
        for i in 0..4 {
            let v = u32::from_le_bytes(bytes[4 * i..4 * (i + 1)].try_into().unwrap());
            if v >= P_U32 {
                return Err(SensoryRoiError::NonCanonicalFieldElement);
            }
            c[i] = v;
        }
        Ok(Self(c))
    }
}

#[inline]
fn eval_poly_ext4(coeffs: &[Ext4], x: Ext4) -> Ext4 {
    let mut acc = Ext4::ZERO;
    for &c in coeffs.iter().rev() {
        acc = acc.mul(x).add(c);
    }
    acc
}

#[inline]
fn eq_lin_ext4(r: Ext4, x: Ext4) -> Ext4 {
    Ext4::ONE.sub(r).mul(Ext4::ONE.sub(x)).add(r.mul(x))
}

fn eq_mle_ext4(z: &[Ext4], x: &[Ext4]) -> Ext4 {
    assert_eq!(z.len(), x.len());
    z.iter()
        .zip(x.iter())
        .fold(Ext4::ONE, |acc, (&zj, &xj)| acc.mul(eq_lin_ext4(zj, xj)))
}

fn build_eq_table_lsb_ext4(r: &[Ext4]) -> Vec<Ext4> {
    if r.is_empty() {
        return vec![Ext4::ONE];
    }
    let mut tbl = Vec::with_capacity(1usize << r.len());
    tbl.push(Ext4::ONE.sub(r[0]));
    tbl.push(r[0]);
    for &ri in &r[1..] {
        let cur = tbl.len();
        for idx in 0..cur {
            let base = tbl[idx];
            let hi = base.mul(ri);
            tbl[idx] = base.sub(hi);
            tbl.push(hi);
        }
    }
    tbl
}

fn fold_ext4_vec(v: &[Ext4], r: Ext4) -> Vec<Ext4> {
    v.chunks_exact(2)
        .map(|p| p[0].add(r.mul(p[1].sub(p[0]))))
        .collect()
}

/// Convert values `[P(0), P(1), ..., P(d)]` (`d <= 5`) into exact monomial coefficients `[c_0..=c_d]`
/// via Newton forward differences over `BabyBear` (zero `Ext4` inversions).
fn interpolate_monomial_0_to_d(vals: &[Ext4]) -> Vec<Ext4> {
    let n = vals.len();
    assert!(n >= 1 && n <= 6);
    let mut diff = vals.to_vec();
    for k in 1..n {
        for j in (k..n).rev() {
            diff[j] = diff[j].sub(diff[j - 1]);
        }
    }
    let inv_facts = [
        1u32,
        1u32,
        bb_inv(2).unwrap(),
        bb_inv(6).unwrap(),
        bb_inv(24).unwrap(),
        bb_inv(120).unwrap(),
    ];
    let mut mono = vec![Ext4::ZERO; n];
    // Basis polynomial `basis(X) = X(X-1)...(X-k+1)` stored as BabyBear monomials.
    let mut basis = vec![0u32; n];
    basis[0] = 1;
    for k in 0..n {
        let ak = diff[k].scale_bb(inv_facts[k]);
        for j in 0..=k {
            if basis[j] != 0 {
                mono[j] = mono[j].add(ak.scale_bb(basis[j]));
            }
        }
        if k + 1 < n {
            // Multiply `basis(X)` by `(X - k)`.
            let neg_k = bb_neg(k as u32);
            for j in (1..=k + 1).rev() {
                basis[j] = bb_add(basis[j - 1], bb_mul(basis[j], neg_k));
            }
            basis[0] = bb_mul(basis[0], neg_k);
        }
    }
    mono
}

fn precompute_twiddles_bb(n: usize) -> Vec<u32> {
    if n <= 1 {
        return Vec::new();
    }
    let omega = root_of_unity_bb(n);
    let mut tw = Vec::with_capacity(n / 2);
    let mut cur = 1u32;
    for _ in 0..(n / 2) {
        tw.push(cur);
        cur = bb_mul(cur, omega);
    }
    tw
}

fn ntt_bb_in_place(a: &mut [u32], tw: &[u32]) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    let lg = n.trailing_zeros();
    for i in 0..n {
        let r = i.reverse_bits() >> (usize::BITS - lg);
        if i < r {
            a.swap(i, r);
        }
    }
    let mut len = 2;
    while len <= n {
        let half = len / 2;
        let step = n / len;
        for st in (0..n).step_by(len) {
            for j in 0..half {
                let u = a[st + j];
                let v = bb_mul(a[st + j + half], tw[j * step]);
                a[st + j] = bb_add(u, v);
                a[st + j + half] = bb_sub(u, v);
            }
        }
        len <<= 1;
    }
}

fn ntt_ext4_in_place(a: &mut [Ext4], tw: &[u32]) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    let lg = n.trailing_zeros();
    for i in 0..n {
        let r = i.reverse_bits() >> (usize::BITS - lg);
        if i < r {
            a.swap(i, r);
        }
    }
    let mut len = 2;
    while len <= n {
        let half = len / 2;
        let step = n / len;
        for st in (0..n).step_by(len) {
            for j in 0..half {
                let u = a[st + j];
                let v = a[st + j + half].scale_bb(tw[j * step]);
                a[st + j] = u.add(v);
                a[st + j + half] = u.sub(v);
            }
        }
        len <<= 1;
    }
}

fn coset_eval_bb(coeffs: &[u32], n0: usize, shift_pows: &[u32], tw: &[u32]) -> Vec<u32> {
    let mut buf = vec![0u32; n0];
    for (k, &c) in coeffs.iter().enumerate() {
        buf[k] = bb_mul(c, shift_pows[k]);
    }
    ntt_bb_in_place(&mut buf, tw);
    buf
}

fn coset_eval_ext4(coeffs: &[Ext4], n0: usize, shift_pows: &[u32], tw: &[u32]) -> Vec<Ext4> {
    let mut buf = vec![Ext4::ZERO; n0];
    for (k, &c) in coeffs.iter().enumerate() {
        buf[k] = c.scale_bb(shift_pows[k]);
    }
    ntt_ext4_in_place(&mut buf, tw);
    buf
}

/// Deterministic `cSHAKE256` XOF CSPRNG for exact uniform BabyBear & `Ext4` sampling.
pub struct CShakeRng {
    reader: sha3::CShake256Reader,
}

impl CShakeRng {
    pub fn from_seed(customization: &[u8], seed: &[u8]) -> Self {
        let mut h = CShake256::from_core(CShake256Core::new(customization));
        h.update(seed);
        Self {
            reader: h.finalize_xof(),
        }
    }

    /// Length-prefixed multi-part domain-separated CSPRNG derivation (mixes protocol/frame context
    /// into caller-supplied high-entropy seed to prevent cross-protocol/cross-frame stream reuse).
    pub fn from_parts(customization: &[u8], parts: &[&[u8]]) -> Self {
        let mut h = CShake256::from_core(CShake256Core::new(customization));
        for p in parts {
            h.update(&(p.len() as u64).to_le_bytes());
            h.update(p);
        }
        Self {
            reader: h.finalize_xof(),
        }
    }

    pub fn fill_bytes(&mut self, dst: &mut [u8]) {
        XofReader::read(&mut self.reader, dst);
    }

    pub fn next_bb(&mut self) -> u32 {
        let mut buf = [0u8; 4];
        loop {
            XofReader::read(&mut self.reader, &mut buf);
            let cand = u32::from_le_bytes(buf) & 0x7FFF_FFFF;
            if cand < P_U32 {
                return cand;
            }
        }
    }

    pub fn next_ext4(&mut self) -> Ext4 {
        Ext4([
            self.next_bb(),
            self.next_bb(),
            self.next_bb(),
            self.next_bb(),
        ])
    }
}

/// Domain-separated `cSHAKE256` Fiat-Shamir transcript with 16-bit PoW grinding.
#[derive(Clone)]
struct FsTranscript {
    state: Digest,
    squeeze_ctr: u64,
    absorb_core: CShake256Core,
    squeeze_core: CShake256Core,
    pow_core: CShake256Core,
}

impl FsTranscript {
    fn new(protocol_label: &[u8]) -> Self {
        let mut h = CShake256::from_core(CShake256Core::new(CUST_FS_INIT));
        h.update(protocol_label);
        let mut state = [0u8; 32];
        h.finalize_xof().read(&mut state);
        Self {
            state,
            squeeze_ctr: 0,
            absorb_core: CShake256Core::new(CUST_FS_ABSORB),
            squeeze_core: CShake256Core::new(CUST_FS_SQUEEZE),
            pow_core: CShake256Core::new(CUST_POW),
        }
    }

    fn absorb_bytes(&mut self, label: &[u8], payload: &[u8]) {
        let mut h = CShake256::from_core(self.absorb_core.clone());
        h.update(&self.state);
        h.update(&(label.len() as u32).to_le_bytes());
        h.update(label);
        h.update(&(payload.len() as u64).to_le_bytes());
        h.update(payload);
        h.finalize_xof().read(&mut self.state);
        self.squeeze_ctr = 0;
    }

    fn absorb_u64(&mut self, label: &[u8], v: u64) {
        self.absorb_bytes(label, &v.to_le_bytes());
    }

    fn absorb_root(&mut self, label: &[u8], root: &Digest) {
        self.absorb_bytes(label, root);
    }

    fn absorb_ext4(&mut self, label: &[u8], x: Ext4) {
        self.absorb_bytes(label, &x.to_bytes());
    }

    fn absorb_ext4_slice(&mut self, label: &[u8], xs: &[Ext4]) {
        let mut buf = Vec::with_capacity(xs.len() * 16);
        for &x in xs {
            buf.extend_from_slice(&x.to_bytes());
        }
        self.absorb_bytes(label, &buf);
    }

    fn xof_reader(&mut self, label: &[u8]) -> sha3::CShake256Reader {
        let mut h = CShake256::from_core(self.squeeze_core.clone());
        h.update(&self.state);
        h.update(&self.squeeze_ctr.to_le_bytes());
        h.update(&(label.len() as u32).to_le_bytes());
        h.update(label);
        self.squeeze_ctr += 1;
        h.finalize_xof()
    }

    fn squeeze_ext4(&mut self, label: &[u8], nonzero: bool) -> Ext4 {
        let mut reader = self.xof_reader(label);
        let mut buf = [0u8; 4];
        loop {
            let mut limbs = [0u32; 4];
            for item in &mut limbs {
                loop {
                    XofReader::read(&mut reader, &mut buf);
                    let cand = u32::from_le_bytes(buf) & 0x7FFF_FFFF;
                    if cand < P_U32 {
                        *item = cand;
                        break;
                    }
                }
            }
            let elem = Ext4(limbs);
            if !nonzero || !elem.is_zero() {
                return elem;
            }
        }
    }

    fn squeeze_non_binary_ext4(&mut self, label: &[u8]) -> Ext4 {
        loop {
            let e = self.squeeze_ext4(label, true);
            if e != Ext4::ONE {
                return e;
            }
        }
    }

    fn verify_pow(&self, nonce: u64) -> bool {
        let mut h = CShake256::from_core(self.pow_core.clone());
        h.update(&self.state);
        h.update(&nonce.to_le_bytes());
        let mut out = [0u8; 4];
        h.finalize_xof().read(&mut out);
        // Check `POW_GRIND_BITS = 16` leading zero bits.
        out[0] == 0 && out[1] == 0
    }

    fn mine_pow(&self) -> u64 {
        let mut nonce = 0u64;
        loop {
            if self.verify_pow(nonce) {
                return nonce;
            }
            nonce = nonce.wrapping_add(1);
        }
    }

    fn squeeze_distinct_indices(&mut self, label: &[u8], domain_size: usize, count: usize) -> Vec<usize> {
        assert!(domain_size.is_power_of_two() && count <= domain_size);
        let mask = domain_size - 1;
        let mut reader = self.xof_reader(label);
        let mut chosen = Vec::with_capacity(count);
        let mut seen = vec![false; domain_size];
        let mut buf = [0u8; 4];
        while chosen.len() < count {
            XofReader::read(&mut reader, &mut buf);
            let idx = (u32::from_le_bytes(buf) as usize) & mask;
            if !seen[idx] {
                seen[idx] = true;
                chosen.push(idx);
            }
        }
        chosen.sort_unstable();
        chosen
    }
}

/// Bounds-checked binary cursor for canonical proof deserialization.
struct ByteCursor<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> ByteCursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, pos: 0 }
    }

    fn remaining(&self) -> usize {
        self.bytes.len().saturating_sub(self.pos)
    }

    fn read_exact(&mut self, n: usize) -> Result<&'a [u8], SensoryRoiError> {
        let end = self
            .pos
            .checked_add(n)
            .ok_or(SensoryRoiError::MalformedWireProof("cursor overflow"))?;
        if end > self.bytes.len() {
            return Err(SensoryRoiError::MalformedWireProof("unexpected EOF"));
        }
        let s = &self.bytes[self.pos..end];
        self.pos = end;
        Ok(s)
    }

    fn read_u8(&mut self) -> Result<u8, SensoryRoiError> {
        Ok(self.read_exact(1)?[0])
    }

    fn read_u32(&mut self) -> Result<u32, SensoryRoiError> {
        Ok(u32::from_le_bytes(self.read_exact(4)?.try_into().unwrap()))
    }

    fn read_u64(&mut self) -> Result<u64, SensoryRoiError> {
        Ok(u64::from_le_bytes(self.read_exact(8)?.try_into().unwrap()))
    }

    fn read_bb(&mut self) -> Result<u32, SensoryRoiError> {
        let v = self.read_u32()?;
        if v >= P_U32 {
            return Err(SensoryRoiError::NonCanonicalFieldElement);
        }
        Ok(v)
    }

    fn read_digest(&mut self) -> Result<Digest, SensoryRoiError> {
        Ok(self.read_exact(32)?.try_into().unwrap())
    }

    fn read_salt128(&mut self) -> Result<Salt128, SensoryRoiError> {
        Ok(self.read_exact(16)?.try_into().unwrap())
    }

    fn read_ext4(&mut self) -> Result<Ext4, SensoryRoiError> {
        let arr: [u8; 16] = self.read_exact(16)?.try_into().unwrap();
        Ext4::from_bytes(&arr)
    }
}

// ============================================================================
// §2. Pre-Absorbed `cSHAKE256` Cores, Merkle Trees & Deduplicated Multi-Proofs
// ============================================================================

/// Pre-absorbed `CShake256Core` handles for raw-tile ROI trees, PCS trees, and FRI trees.
#[derive(Clone)]
pub struct CachedCshakeCores {
    raw_tile: CShake256Core,
    merkle_node: CShake256Core,
    xmss_leaf: CShake256Core,
    raw_pcs_leaf: CShake256Core,
    raw_pcs_node: CShake256Core,
    aux_pcs_leaf: CShake256Core,
    aux_pcs_node: CShake256Core,
    fri_pair_leaf: CShake256Core,
    fri_node: CShake256Core,
    empty_leaf: Digest,
}

impl CachedCshakeCores {
    pub fn new() -> Self {
        let mut empty_leaf = [0u8; 32];
        CShake256::from_core(CShake256Core::new(CUST_EMPTY_LEAF))
            .finalize_xof()
            .read(&mut empty_leaf);
        Self {
            raw_tile: CShake256Core::new(CUST_RAW_TILE),
            merkle_node: CShake256Core::new(CUST_MERKLE_NODE),
            xmss_leaf: CShake256Core::new(CUST_XMSS_LEAF),
            raw_pcs_leaf: CShake256Core::new(CUST_RAW_PCS_LEAF),
            raw_pcs_node: CShake256Core::new(CUST_RAW_PCS_NODE),
            aux_pcs_leaf: CShake256Core::new(CUST_AUX_PCS_LEAF),
            aux_pcs_node: CShake256Core::new(CUST_AUX_PCS_NODE),
            fri_pair_leaf: CShake256Core::new(CUST_FRI_PAIR_LEAF),
            fri_node: CShake256Core::new(CUST_FRI_NODE),
            empty_leaf,
        }
    }

    #[inline]
    pub fn empty_leaf(&self) -> Digest {
        self.empty_leaf
    }

    #[inline]
    pub fn raw_tile_commit(
        &self,
        ctx_bytes: &[u8; 24],
        tile_idx: u32,
        raw_salt: &Salt256,
        pixels: &[u8],
    ) -> Digest {
        let mut h = CShake256::from_core(self.raw_tile.clone());
        h.update(ctx_bytes);
        h.update(&tile_idx.to_le_bytes());
        h.update(raw_salt);
        h.update(&(pixels.len() as u32).to_le_bytes());
        h.update(pixels);
        let mut out = [0u8; 32];
        h.finalize_xof().read(&mut out);
        out
    }

    #[inline]
    pub fn xmss_leaf(&self, tree_depth: u8, ots_index: u32, ots_pk: &Digest) -> Digest {
        let mut h = CShake256::from_core(self.xmss_leaf.clone());
        h.update(&[tree_depth]);
        h.update(&ots_index.to_le_bytes());
        h.update(ots_pk);
        let mut out = [0u8; 32];
        h.finalize_xof().read(&mut out);
        out
    }

    #[inline]
    pub fn merkle_parent(&self, lvl: u8, idx: u32, left: &Digest, right: &Digest) -> Digest {
        merkle_parent_with_core(&self.merkle_node, lvl, idx, left, right)
    }

    #[inline]
    fn raw_pcs_leaf(&self, ctx_bytes: &[u8; 24], col_idx: u32, salt: &Salt128, col: &[u32]) -> Digest {
        let mut h = CShake256::from_core(self.raw_pcs_leaf.clone());
        h.update(ctx_bytes);
        h.update(&col_idx.to_le_bytes());
        h.update(salt);
        for &v in col {
            h.update(&v.to_le_bytes());
        }
        let mut out = [0u8; 32];
        h.finalize_xof().read(&mut out);
        out
    }

    #[inline]
    fn aux_pcs_leaf(
        &self,
        col_idx: u32,
        salt: &Salt128,
        bb_vals: &[u32],
        ext_vals: &[Ext4],
    ) -> Digest {
        let mut h = CShake256::from_core(self.aux_pcs_leaf.clone());
        h.update(&col_idx.to_le_bytes());
        h.update(salt);
        for &v in bb_vals {
            h.update(&v.to_le_bytes());
        }
        for &e in ext_vals {
            h.update(&e.to_bytes());
        }
        let mut out = [0u8; 32];
        h.finalize_xof().read(&mut out);
        out
    }

    #[inline]
    fn fri_pair_leaf(&self, round: u8, pair_idx: u32, left: Ext4, right: Ext4) -> Digest {
        let mut h = CShake256::from_core(self.fri_pair_leaf.clone());
        h.update(&[round]);
        h.update(&pair_idx.to_le_bytes());
        h.update(&left.to_bytes());
        h.update(&right.to_bytes());
        let mut out = [0u8; 32];
        h.finalize_xof().read(&mut out);
        out
    }
}

impl Default for CachedCshakeCores {
    fn default() -> Self {
        Self::new()
    }
}

#[inline]
fn merkle_parent_with_core(
    core: &CShake256Core,
    lvl: u8,
    idx: u32,
    left: &Digest,
    right: &Digest,
) -> Digest {
    let mut h = CShake256::from_core(core.clone());
    h.update(&[lvl]);
    h.update(&idx.to_le_bytes());
    h.update(left);
    h.update(right);
    let mut out = [0u8; 32];
    h.finalize_xof().read(&mut out);
    out
}

/// Minimal Merkle depth `d` such that `2^d >= tile_count` (`d >= 0`).
pub fn merkle_depth_for(tile_count: usize) -> u32 {
    if tile_count <= 1 {
        return 0;
    }
    (usize::BITS - (tile_count - 1).leading_zeros()) as u32
}

fn build_merkle_layers_with_core(
    node_core: &CShake256Core,
    empty_leaf: Digest,
    depth: u32,
    leaves: &[Digest],
) -> Vec<Vec<Digest>> {
    let cap = 1usize << depth;
    let mut layer0 = vec![empty_leaf; cap];
    let copy_len = leaves.len().min(cap);
    layer0[..copy_len].copy_from_slice(&leaves[..copy_len]);

    let mut layers = Vec::with_capacity(depth as usize + 1);
    layers.push(layer0);

    let threads = std::thread::available_parallelism()
        .map(|n| n.get().min(8))
        .unwrap_or(1);

    for lvl in 0..(depth as usize) {
        let prev = &layers[lvl];
        let next_len = prev.len() / 2;
        let mut next = vec![[0u8; 32]; next_len];
        let lvl_u8 = (lvl & 0xFF) as u8;
        if next_len >= 256 && threads > 1 {
            let chunk = next_len.div_ceil(threads);
            std::thread::scope(|s| {
                for (t_idx, dst) in next.chunks_mut(chunk).enumerate() {
                    let start = t_idx * chunk;
                    s.spawn(move || {
                        for (off, slot) in dst.iter_mut().enumerate() {
                            let idx = start + off;
                            *slot = merkle_parent_with_core(
                                node_core,
                                lvl_u8,
                                idx as u32,
                                &prev[2 * idx],
                                &prev[2 * idx + 1],
                            );
                        }
                    });
                }
            });
        } else {
            for (idx, slot) in next.iter_mut().enumerate() {
                *slot = merkle_parent_with_core(
                    node_core,
                    lvl_u8,
                    idx as u32,
                    &prev[2 * idx],
                    &prev[2 * idx + 1],
                );
            }
        }
        layers.push(next);
    }
    layers
}

pub fn build_merkle_layers(
    cores: &CachedCshakeCores,
    depth: u32,
    leaves: &[Digest],
) -> Vec<Vec<Digest>> {
    build_merkle_layers_with_core(&cores.merkle_node, cores.empty_leaf(), depth, leaves)
}

pub fn extract_merkle_path(layers: &[Vec<Digest>], mut idx: usize) -> Vec<Digest> {
    let depth = layers.len().saturating_sub(1);
    let mut path = Vec::with_capacity(depth);
    for layer in &layers[..depth] {
        let sib = idx ^ 1;
        path.push(layer[sib]);
        idx >>= 1;
    }
    path
}

pub fn verify_merkle_path(
    cores: &CachedCshakeCores,
    root: &Digest,
    depth: u32,
    tile_idx: u32,
    leaf: &Digest,
    siblings: &[Digest],
) -> Result<(), SensoryRoiError> {
    if siblings.len() != depth as usize {
        return Err(SensoryRoiError::MerklePathLengthMismatch {
            expected: depth as usize,
            actual: siblings.len(),
        });
    }
    if (tile_idx as u64) >= (1u64 << depth) {
        return Err(SensoryRoiError::TileIndexOutOfBounds {
            tile_idx: tile_idx as usize,
            max_tiles: 1usize << depth,
        });
    }
    let mut cur = *leaf;
    let mut pos = tile_idx;
    for (lvl, sib) in siblings.iter().enumerate() {
        let parent_idx = pos >> 1;
        cur = if (pos & 1) == 0 {
            cores.merkle_parent((lvl & 0xFF) as u8, parent_idx, &cur, sib)
        } else {
            cores.merkle_parent((lvl & 0xFF) as u8, parent_idx, sib, &cur)
        };
        pos = parent_idx;
    }
    if !ct_eq_digest(&cur, root) {
        return Err(SensoryRoiError::MerklePathMismatch {
            tile_idx: tile_idx as usize,
        });
    }
    Ok(())
}

/// Deduplicated binary Merkle multi-proof for a strictly-sorted list of leaf indices.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerkleMultiProof {
    pub siblings: Vec<Digest>,
}

impl MerkleMultiProof {
    fn build(layers: &[Vec<Digest>], sorted_indices: &[usize]) -> Self {
        let depth = layers.len().saturating_sub(1);
        let mut active: Vec<usize> = sorted_indices.to_vec();
        let mut siblings = Vec::new();
        for lvl in 0..depth {
            let mut next = Vec::with_capacity(active.len());
            let mut i = 0usize;
            while i < active.len() {
                let idx = active[i];
                let par = idx >> 1;
                if i + 1 < active.len() && (active[i + 1] >> 1) == par {
                    i += 2;
                } else {
                    siblings.push(layers[lvl][idx ^ 1]);
                    i += 1;
                }
                next.push(par);
            }
            active = next;
        }
        Self { siblings }
    }

    fn verify(
        &self,
        node_core: &CShake256Core,
        root: &Digest,
        depth: usize,
        sorted_indices: &[usize],
        leaf_digests: &[Digest],
    ) -> Result<(), SensoryRoiError> {
        if sorted_indices.is_empty() || sorted_indices.len() != leaf_digests.len() {
            return Err(SensoryRoiError::MerkleMultiProofInvalid("empty or len mismatch"));
        }
        let max_leaves = 1usize << depth;
        for w in sorted_indices.windows(2) {
            if w[0] >= w[1] {
                return Err(SensoryRoiError::MerkleMultiProofInvalid("unsorted or duplicate index"));
            }
        }
        if *sorted_indices.last().unwrap() >= max_leaves {
            return Err(SensoryRoiError::MerkleMultiProofInvalid("index out of range"));
        }

        let mut cur: Vec<(usize, Digest)> = sorted_indices
            .iter()
            .copied()
            .zip(leaf_digests.iter().copied())
            .collect();
        let mut sib_pos = 0usize;

        for lvl in 0..depth {
            let lvl_u8 = (lvl & 0xFF) as u8;
            let mut next = Vec::with_capacity(cur.len());
            let mut i = 0usize;
            while i < cur.len() {
                let (idx, d) = cur[i];
                let par = idx >> 1;
                let (left, right) = if i + 1 < cur.len() && (cur[i + 1].0 >> 1) == par {
                    let pair = (d, cur[i + 1].1);
                    i += 2;
                    pair
                } else {
                    if sib_pos >= self.siblings.len() {
                        return Err(SensoryRoiError::MerkleMultiProofInvalid("missing sibling"));
                    }
                    let sib = self.siblings[sib_pos];
                    sib_pos += 1;
                    i += 1;
                    if (idx & 1) == 0 {
                        (d, sib)
                    } else {
                        (sib, d)
                    }
                };
                let p_dig = merkle_parent_with_core(node_core, lvl_u8, par as u32, &left, &right);
                next.push((par, p_dig));
            }
            cur = next;
        }
        if sib_pos != self.siblings.len() {
            return Err(SensoryRoiError::MerkleMultiProofInvalid("unused trailing siblings"));
        }
        if cur.len() != 1 || cur[0].0 != 0 || !ct_eq_digest(&cur[0].1, root) {
            return Err(SensoryRoiError::MerkleMultiProofInvalid("root mismatch"));
        }
        Ok(())
    }

    fn write_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&(self.siblings.len() as u32).to_le_bytes());
        for s in &self.siblings {
            out.extend_from_slice(s);
        }
    }

    fn read_from(cur: &mut ByteCursor<'_>, max_siblings: usize) -> Result<Self, SensoryRoiError> {
        let len = cur.read_u32()? as usize;
        if len > max_siblings {
            return Err(SensoryRoiError::MalformedWireProof("multiproof sibling overflow"));
        }
        let mut siblings = Vec::with_capacity(len);
        for _ in 0..len {
            siblings.push(cur.read_digest()?);
        }
        Ok(Self { siblings })
    }
}

// ============================================================================
// §3. Asymmetric Post-Quantum Enclave Keys (`WotsCshake256` / XMSS) & Headers
// ============================================================================

/// Sensor modality tag matching Lean `SensorModality`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SensorModality {
    Csi2Tile16x16,
    I2sAudioWindow,
}

impl SensorModality {
    #[inline]
    pub fn tag(self) -> u8 {
        match self {
            Self::Csi2Tile16x16 => 1,
            Self::I2sAudioWindow => 2,
        }
    }
}

/// Hardware-capture frame context bound into every raw tile commit, PCS leaf, and header signature.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FrameContext {
    pub sensor_id: u64,
    pub frame_seq: u64,
    pub timestamp_ns: u64,
}

impl FrameContext {
    #[inline]
    pub fn encode(&self) -> [u8; 24] {
        let mut out = [0u8; 24];
        out[0..8].copy_from_slice(&self.sensor_id.to_le_bytes());
        out[8..16].copy_from_slice(&self.frame_seq.to_le_bytes());
        out[16..24].copy_from_slice(&self.timestamp_ns.to_le_bytes());
        out
    }
}

/// Public verification key held by verifiers (ZERO secret key material; CANNOT forge headers!).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EnclavePublicKey {
    pub root: Digest,
    pub tree_depth: u8,
}

/// Enclave-only asymmetric PQ signing key (`WotsCshake256`, single-key or XMSS tree preventing OTS reuse).
pub struct EnclaveSigningKey {
    pk: EnclavePublicKey,
    ots_seeds: Vec<Vec<u8>>,
    ots_pks: Vec<Digest>,
    xmss_layers: Vec<Vec<Digest>>,
    next_idx: AtomicU32,
}

impl EnclaveSigningKey {
    /// Single-frame `WotsCshake256` keypair (`tree_depth = 0`, byte-identical to Lean `sealSensorFrameWots`).
    pub fn from_wots_seed(seed: Vec<u8>) -> Self {
        let pk_vec = WotsCshake256.pk_of(&seed);
        let root: Digest = pk_vec.try_into().expect("32-byte WOTS pk");
        Self {
            pk: EnclavePublicKey { root, tree_depth: 0 },
            ots_seeds: vec![seed],
            ots_pks: vec![root],
            xmss_layers: Vec::new(),
            next_idx: AtomicU32::new(0),
        }
    }

    /// Multi-frame stateful XMSS-style Merkle tree of `2^{tree_depth}` independent `WotsCshake256`
    /// one-time keys (`1 <= tree_depth <= 8`), preventing one-time-key reuse across frames.
    pub fn from_xmss_master_seed(cores: &CachedCshakeCores, master_seed: &[u8; 32], tree_depth: u8) -> Self {
        assert!((1..=8).contains(&tree_depth), "XMSS tree_depth must be in 1..=8");
        let count = 1usize << tree_depth;
        let mut ots_seeds = Vec::with_capacity(count);
        for k in 0..count {
            let mut h = CShake256::from_core(CShake256Core::new(CUST_XMSS_DERIVE));
            h.update(master_seed);
            h.update(&[tree_depth]);
            h.update(&(k as u32).to_le_bytes());
            let mut s = vec![0u8; 32];
            h.finalize_xof().read(&mut s);
            ots_seeds.push(s);
        }
        let mut ots_pks = vec![[0u8; 32]; count];
        let threads = std::thread::available_parallelism()
            .map(|n| n.get().min(8))
            .unwrap_or(1);
        if count >= 4 && threads > 1 {
            let chunk = count.div_ceil(threads);
            std::thread::scope(|s| {
                let mut rest = ots_pks.as_mut_slice();
                let mut start = 0usize;
                while !rest.is_empty() {
                    let take = chunk.min(rest.len());
                    let (cur, tail) = rest.split_at_mut(take);
                    rest = tail;
                    let seeds_slice = &ots_seeds[start..start + take];
                    s.spawn(move || {
                        for (off, dst) in cur.iter_mut().enumerate() {
                            let pk_v = WotsCshake256.pk_of(&seeds_slice[off]);
                            *dst = pk_v.try_into().unwrap();
                        }
                    });
                    start += take;
                }
            });
        } else {
            for (k, seed) in ots_seeds.iter().enumerate() {
                ots_pks[k] = WotsCshake256.pk_of(seed).try_into().unwrap();
            }
        }
        let leaves: Vec<Digest> = ots_pks
            .iter()
            .enumerate()
            .map(|(k, pk)| cores.xmss_leaf(tree_depth, k as u32, pk))
            .collect();
        let xmss_layers = build_merkle_layers(cores, tree_depth as u32, &leaves);
        let root = xmss_layers[tree_depth as usize][0];
        Self {
            pk: EnclavePublicKey { root, tree_depth },
            ots_seeds,
            ots_pks,
            xmss_layers,
            next_idx: AtomicU32::new(0),
        }
    }

    pub fn public_key(&self) -> EnclavePublicKey {
        self.pk
    }

    /// Consume the next unused one-time `WotsCshake256` key and sign `header` using a bounded
    /// compare-and-swap reservation (never increments past `ots_seeds.len()` or wraps `u32`).
    /// Note: production enclaves must persist the monotonic OTS index to durable NVM before
    /// releasing any signature (RFC 8391 §4.1.9; `[OPEN]` hardware-enclave persistence seam).
    fn sign_header(&self, header: &mut SensorFrameHeader) -> Result<(), SensoryRoiError> {
        let limit = self.ots_seeds.len();
        let mut cur = self.next_idx.load(Ordering::SeqCst);
        let idx = loop {
            if (cur as usize) >= limit {
                return Err(SensoryRoiError::OtsBudgetExhausted);
            }
            match self.next_idx.compare_exchange(
                cur,
                cur + 1,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => break cur as usize,
                Err(actual) => cur = actual,
            }
        };
        header.enclave_pk = self.pk;
        header.ots_index = idx as u32;
        header.ots_pk = self.ots_pks[idx];
        header.ots_auth_path = if self.pk.tree_depth == 0 {
            Vec::new()
        } else {
            extract_merkle_path(&self.xmss_layers, idx)
        };
        let payload = header.signing_payload();
        header.wots_sig = WotsCshake256.sign(&self.ots_seeds[idx], &payload);
        Ok(())
    }
}

/// Enclave-signed sensor frame header binding raw tile Merkle root & PCS `rt_raw` via `WotsCshake256`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SensorFrameHeader {
    pub ctx: FrameContext,
    pub grid_width: u32,
    pub grid_height: u32,
    pub tile_len: u32,
    pub merkle_depth: u32,
    pub modality: SensorModality,
    pub tile_merkle_root: Digest,
    pub rt_raw: Digest,
    pub enclave_pk: EnclavePublicKey,
    pub ots_index: u32,
    pub ots_pk: Digest,
    pub wots_sig: Vec<u8>,
    pub ots_auth_path: Vec<Digest>,
}

impl SensorFrameHeader {
    /// Canonical signing payload (byte-identical to Lean `headerSigningPayload`).
    pub fn signing_payload(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(CUST_FRAME_SEAL.len() + 174);
        out.extend_from_slice(CUST_FRAME_SEAL);
        out.extend_from_slice(&self.ctx.encode());
        out.extend_from_slice(&self.grid_width.to_le_bytes());
        out.extend_from_slice(&self.grid_height.to_le_bytes());
        out.extend_from_slice(&self.tile_len.to_le_bytes());
        out.extend_from_slice(&self.merkle_depth.to_le_bytes());
        out.push(self.modality.tag());
        out.extend_from_slice(&self.tile_merkle_root);
        out.extend_from_slice(&self.rt_raw);
        out.extend_from_slice(&self.enclave_pk.root);
        out.push(self.enclave_pk.tree_depth);
        out.extend_from_slice(&self.ots_index.to_le_bytes());
        out.extend_from_slice(&self.ots_pk);
        out
    }

    pub fn num_tiles(&self) -> Result<usize, SensoryRoiError> {
        (self.grid_width as usize)
            .checked_mul(self.grid_height as usize)
            .filter(|&n| n > 0)
            .ok_or(SensoryRoiError::InvalidGeometry("invalid tile grid"))
    }
}

/// Asymmetric header verifier: holds ONLY `expected_pk: &EnclavePublicKey` (ZERO secret key!).
pub fn verify_frame_header(
    cores: &CachedCshakeCores,
    expected_pk: &EnclavePublicKey,
    header: &SensorFrameHeader,
) -> Result<(), SensoryRoiError> {
    if header.enclave_pk != *expected_pk {
        return Err(SensoryRoiError::EnclaveKeyMismatch);
    }
    if expected_pk.tree_depth >= 32 {
        return Err(SensoryRoiError::InvalidGeometry("tree_depth >= 32"));
    }
    let cap = 1u64
        .checked_shl(header.merkle_depth)
        .filter(|_| header.merkle_depth < 31)
        .ok_or(SensoryRoiError::InvalidGeometry("merkle_depth overflow"))?;
    let total = (header.grid_width as u64) * (header.grid_height as u64);
    if total == 0 || total > cap {
        return Err(SensoryRoiError::InvalidGeometry(
            "grid exceeds 2^merkle_depth",
        ));
    }
    let tl = header.tile_len as usize;
    if tl == 0 || tl > MAX_TILE_SAMPLES || !tl.is_power_of_two() {
        return Err(SensoryRoiError::InvalidGeometry(
            "tile_len must be a power of two in 1..=65536",
        ));
    }
    if header.ots_auth_path.len() != expected_pk.tree_depth as usize
        || header.wots_sig.len() != WOTS_SIG_LEN
    {
        return Err(SensoryRoiError::InvalidEnclaveSignature);
    }
    if expected_pk.tree_depth == 0 {
        if header.ots_index != 0 || !ct_eq_digest(&header.ots_pk, &expected_pk.root) {
            return Err(SensoryRoiError::InvalidEnclaveSignature);
        }
    } else {
        let leaf = cores.xmss_leaf(expected_pk.tree_depth, header.ots_index, &header.ots_pk);
        verify_merkle_path(
            cores,
            &expected_pk.root,
            expected_pk.tree_depth as u32,
            header.ots_index,
            &leaf,
            &header.ots_auth_path,
        )
        .map_err(|_| SensoryRoiError::InvalidEnclaveSignature)?;
    }
    let payload = header.signing_payload();
    if !WotsCshake256.verify(&header.ots_pk, &payload, &header.wots_sig) {
        return Err(SensoryRoiError::InvalidEnclaveSignature);
    }
    Ok(())
}

// ============================================================================
// §4. Raw-Only Sensor Frame Sealer (`tile_merkle_root` + HVZK Coset-RS `rt_raw`)
// ============================================================================

/// Hardware-captured raw tile paired with ONE 256-bit TRNG salt (ZERO `sum_salt`, ZERO `sumCommit`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawSensorTile {
    pub pixels: Vec<u8>,
    pub raw_salt: Salt256,
}

/// Exact integer byte sum (`0 ..= 255 * pixels.len()`, accumulated in `u64` without overflow).
#[inline]
pub fn sum_bytes(pixels: &[u8]) -> u64 {
    let mut acc = 0u64;
    for &b in pixels {
        acc += b as u64;
    }
    acc
}

/// Verify frame-wide 256-bit TRNG `raw_salt` uniqueness.
pub fn verify_fresh_salts(tiles: &[RawSensorTile]) -> Result<(), SensoryRoiError> {
    let mut seen: HashSet<Salt256> = HashSet::with_capacity(tiles.len());
    for (idx, t) in tiles.iter().enumerate() {
        if !seen.insert(t.raw_salt) {
            return Err(SensoryRoiError::SaltReuseDetected { tile_idx: idx });
        }
    }
    Ok(())
}

/// Deterministic HVZK coset Reed-Solomon matrix PCS shape for `rt_raw` (`rate = 1/4`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RawPcsShape {
    pub num_tiles: usize,
    pub tile_len: usize,
    pub m_u: usize,
    pub m_t: usize,
    pub n_tiles_pow2: usize,
    pub m_c: usize,
    pub m_r: usize,
    pub c: usize,
    pub r_d: usize,
    pub w0: usize,
    pub n0: usize,
    pub log_n0: usize,
    pub r_bit: usize,
}

impl RawPcsShape {
    pub fn for_frame(num_tiles: usize, tile_len: usize) -> Result<Self, SensoryRoiError> {
        if num_tiles == 0 || num_tiles > MAX_FRAME_TILES {
            return Err(SensoryRoiError::InvalidGeometry(
                "num_tiles must be in 1..=65536",
            ));
        }
        if tile_len == 0 || tile_len > MAX_TILE_SAMPLES || !tile_len.is_power_of_two() {
            return Err(SensoryRoiError::InvalidGeometry(
                "tile_len must be a power of two in 1..=65536",
            ));
        }
        let m_u = tile_len.trailing_zeros() as usize;
        let m_t = (num_tiles.next_power_of_two().trailing_zeros() as usize).max(1);
        let n_tiles_pow2 = 1usize << m_t;
        let m_raw = m_u + m_t;
        let m_c = if m_raw <= 14 {
            10 // C = 1024
        } else if m_raw <= 18 {
            11 // C = 2048
        } else {
            12 // C = 4096
        };
        let c = 1usize << m_c;
        assert!(c >= MIN_PCS_COLS);
        let m_r = m_raw.saturating_sub(m_c);
        if m_r > 11 {
            return Err(SensoryRoiError::InvalidGeometry(
                "frame sample capacity exceeds supported PCS row cap (r_d <= 2048)",
            ));
        }
        let r_d = 1usize << m_r;
        debug_assert!(r_d <= MAX_RAW_PCS_ROWS);
        let w0 = 2 * c;
        let n0 = PCS_BLOWUP * w0;
        let log_n0 = n0.trailing_zeros() as usize;
        let r_bit = if m_t > m_c { 1usize << (m_t - m_c) } else { 1 };
        Ok(Self {
            num_tiles,
            tile_len,
            m_u,
            m_t,
            n_tiles_pow2,
            m_c,
            m_r,
            c,
            r_d,
            w0,
            n0,
            log_n0,
            r_bit,
        })
    }

    fn tag_bytes(&self) -> [u8; 24] {
        let mut out = [0u8; 24];
        out[0..4].copy_from_slice(&(self.num_tiles as u32).to_le_bytes());
        out[4..8].copy_from_slice(&(self.tile_len as u32).to_le_bytes());
        out[8] = self.m_u as u8;
        out[9] = self.m_t as u8;
        out[10] = self.m_c as u8;
        out[11] = self.m_r as u8;
        out[12..16].copy_from_slice(&(self.w0 as u32).to_le_bytes());
        out[16..20].copy_from_slice(&(self.n0 as u32).to_le_bytes());
        out[20..22].copy_from_slice(&(UD100_QUERIES as u16).to_le_bytes());
        out[22..24].copy_from_slice(&(POW_GRIND_BITS as u16).to_le_bytes());
        out
    }
}

/// Prover-side committed HVZK coset-RS matrix of raw sensor pixels (`rt_raw`).
///
/// Enforces a shared atomic lifetime opening budget (`opened_columns_used <= shape.c`) across all
/// proofs (blur and ambient) and clones of this commitment, ensuring the row-wise degree-`[C..2C)`
/// uniform blinding tail is never exhausted by repeated openings.
#[derive(Clone)]
pub struct RawPcsCommitment {
    pub shape: RawPcsShape,
    /// `r_d * w0` row-major BabyBear monomial coefficients (`[0..c)` data, `[c..2c)` uniform random blinding).
    pub coeffs: Vec<u32>,
    /// `n0 * r_d` column-major coset evaluations on `D_0`.
    pub cw_cols: Vec<u32>,
    /// Fresh 128-bit per-column salts.
    pub col_salts: Vec<Salt128>,
    /// Binary Merkle tree layers over `n0` salted column leaves.
    pub merkle_layers: Vec<Vec<Digest>>,
    pub root: Digest,
    /// Shared cumulative count of codeword columns disclosed across all proofs against `rt_raw`.
    opened_columns_used: Arc<AtomicUsize>,
}

impl RawPcsCommitment {
    /// Cumulative number of `rt_raw` codeword columns opened across all proofs so far.
    pub fn opened_columns_used(&self) -> usize {
        self.opened_columns_used.load(Ordering::SeqCst)
    }

    /// Atomically reserve `cols` opened columns against the row blinding tail capacity `shape.c`.
    /// Refuses once `used + cols > shape.c` so Vandermonde tail privacy cannot be exhausted.
    fn reserve_opening_columns(&self, cols: usize) -> Result<(), SensoryRoiError> {
        let cap = self.shape.c;
        let mut cur = self.opened_columns_used.load(Ordering::SeqCst);
        loop {
            let next = cur.checked_add(cols).ok_or(
                SensoryRoiError::RawCommitmentOpeningBudgetExhausted {
                    opened_cols: cur,
                    capacity_cols: cap,
                },
            )?;
            if next > cap {
                return Err(SensoryRoiError::RawCommitmentOpeningBudgetExhausted {
                    opened_cols: cur,
                    capacity_cols: cap,
                });
            }
            match self.opened_columns_used.compare_exchange(
                cur,
                next,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => return Ok(()),
                Err(actual) => cur = actual,
            }
        }
    }
    fn commit(
        cores: &CachedCshakeCores,
        ctx_bytes: &[u8; 24],
        shape: RawPcsShape,
        raw_pixels_flat: &[u8],
        enclave_rng_seed: &[u8; 32],
    ) -> Self {
        let mut coeffs = vec![0u32; shape.r_d * shape.w0];
        // Copy raw pixels into `0 .. num_tiles * tile_len` (zero-padded to `r_d * c`).
        for (idx, &px) in raw_pixels_flat.iter().enumerate() {
            let r = idx >> shape.m_c;
            let c = idx & (shape.c - 1);
            coeffs[r * shape.w0 + c] = px as u32;
        }

        let mut rng = CShakeRng::from_seed(CUST_RNG_ENCLAVE, enclave_rng_seed);
        // Independent uniform BabyBear blinding tail `[c .. 2c)` on EVERY row (`c >= 1024 > 3 * 280`).
        for r in 0..shape.r_d {
            let row = &mut coeffs[r * shape.w0..(r + 1) * shape.w0];
            for slot in &mut row[shape.c..shape.w0] {
                *slot = rng.next_bb();
            }
        }
        let mut col_salts = vec![[0u8; 16]; shape.n0];
        for s in &mut col_salts {
            rng.fill_bytes(s);
        }

        let shift = canonical_coset_shift_bb(shape.log_n0);
        let tw = precompute_twiddles_bb(shape.n0);
        let mut shift_pows = Vec::with_capacity(shape.w0);
        let mut cur = 1u32;
        for _ in 0..shape.w0 {
            shift_pows.push(cur);
            cur = bb_mul(cur, shift);
        }

        let threads = std::thread::available_parallelism()
            .map(|n| n.get().min(8))
            .unwrap_or(1);

        // Parallel coset-NTT encoding of `r_d` rows.
        let mut row_evals: Vec<Vec<u32>> = vec![Vec::new(); shape.r_d];
        if shape.r_d >= 4 && threads > 1 {
            let chunk = shape.r_d.div_ceil(threads);
            std::thread::scope(|s| {
                let mut rest = row_evals.as_mut_slice();
                let mut start = 0usize;
                while !rest.is_empty() {
                    let take = chunk.min(rest.len());
                    let (dst, tail) = rest.split_at_mut(take);
                    rest = tail;
                    let c_ref = &coeffs;
                    let sp_ref = &shift_pows;
                    let tw_ref = &tw;
                    s.spawn(move || {
                        for (off, slot) in dst.iter_mut().enumerate() {
                            let r = start + off;
                            *slot = coset_eval_bb(
                                &c_ref[r * shape.w0..(r + 1) * shape.w0],
                                shape.n0,
                                sp_ref,
                                tw_ref,
                            );
                        }
                    });
                    start += take;
                }
            });
        } else {
            for (r, slot) in row_evals.iter_mut().enumerate() {
                *slot = coset_eval_bb(
                    &coeffs[r * shape.w0..(r + 1) * shape.w0],
                    shape.n0,
                    &shift_pows,
                    &tw,
                );
            }
        }

        // Transpose into column-major `cw_cols[j * r_d .. (j+1) * r_d]` and hash leaves in parallel.
        let mut cw_cols = vec![0u32; shape.n0 * shape.r_d];
        let mut leaves = vec![[0u8; 32]; shape.n0];
        if threads > 1 {
            let chunk = shape.n0.div_ceil(threads);
            std::thread::scope(|s| {
                let mut cw_rest = cw_cols.as_mut_slice();
                let mut lf_rest = leaves.as_mut_slice();
                let mut start = 0usize;
                while !lf_rest.is_empty() {
                    let take = chunk.min(lf_rest.len());
                    let (cw_c, cw_r) = cw_rest.split_at_mut(take * shape.r_d);
                    let (lf_c, lf_r) = lf_rest.split_at_mut(take);
                    cw_rest = cw_r;
                    lf_rest = lf_r;
                    let re_ref = &row_evals;
                    let salt_ref = &col_salts;
                    s.spawn(move || {
                        for off in 0..take {
                            let j = start + off;
                            let col = &mut cw_c[off * shape.r_d..(off + 1) * shape.r_d];
                            for r in 0..shape.r_d {
                                col[r] = re_ref[r][j];
                            }
                            lf_c[off] = cores.raw_pcs_leaf(ctx_bytes, j as u32, &salt_ref[j], col);
                        }
                    });
                    start += take;
                }
            });
        } else {
            for j in 0..shape.n0 {
                let col = &mut cw_cols[j * shape.r_d..(j + 1) * shape.r_d];
                for r in 0..shape.r_d {
                    col[r] = row_evals[r][j];
                }
                leaves[j] = cores.raw_pcs_leaf(ctx_bytes, j as u32, &col_salts[j], col);
            }
        }

        let merkle_layers = build_merkle_layers_with_core(
            &cores.raw_pcs_node,
            cores.empty_leaf(),
            shape.log_n0 as u32,
            &leaves,
        );
        let root = merkle_layers[shape.log_n0][0];
        Self {
            shape,
            coeffs,
            cw_cols,
            col_salts,
            merkle_layers,
            root,
            opened_columns_used: Arc::new(AtomicUsize::new(0)),
        }
    }
}

/// Full enclave-sealed frame holding raw tiles, raw-only tile Merkle layers, and PCS commitment `rt_raw`.
#[derive(Clone)]
pub struct SealedSensorFrame {
    pub header: SensorFrameHeader,
    pub tiles: Vec<RawSensorTile>,
    pub raw_commits: Vec<Digest>,
    pub tile_merkle_layers: Vec<Vec<Digest>>,
    pub raw_pcs: RawPcsCommitment,
}

/// Seal a generic list of uniform-length `RawSensorTile`s with `WotsCshake256` asymmetric signing,
/// raw-only tile Merkle tree (ZERO `sumCommit`), and HVZK coset-RS PCS commitment `rt_raw`.
#[allow(clippy::too_many_arguments)]
pub fn seal_sensor_frame(
    cores: &CachedCshakeCores,
    enclave_sk: &EnclaveSigningKey,
    ctx: FrameContext,
    grid_width: u32,
    grid_height: u32,
    merkle_depth: u32,
    modality: SensorModality,
    tiles: Vec<RawSensorTile>,
    enclave_rng_seed: &[u8; 32],
) -> Result<SealedSensorFrame, SensoryRoiError> {
    let expected = (grid_width as usize)
        .checked_mul(grid_height as usize)
        .ok_or(SensoryRoiError::InvalidGeometry("grid overflow"))?;
    if expected == 0 || tiles.len() != expected {
        return Err(SensoryRoiError::InvalidGeometry(
            "tile count != grid_width * grid_height",
        ));
    }
    if merkle_depth >= 31 || expected > (1usize << merkle_depth) {
        return Err(SensoryRoiError::InvalidGeometry(
            "tile count exceeds 2^merkle_depth",
        ));
    }
    let tile_len = tiles[0].pixels.len();
    if tile_len == 0 || tile_len > MAX_TILE_SAMPLES || !tile_len.is_power_of_two() {
        return Err(SensoryRoiError::InvalidGeometry(
            "tile_len must be a power of two in 1..=65536",
        ));
    }
    for (idx, t) in tiles.iter().enumerate() {
        if t.pixels.is_empty() {
            return Err(SensoryRoiError::EmptyTile(idx));
        }
        if t.pixels.len() > MAX_TILE_SAMPLES {
            return Err(SensoryRoiError::OversizedTile {
                tile_idx: idx,
                len: t.pixels.len(),
            });
        }
        if t.pixels.len() != tile_len {
            return Err(SensoryRoiError::InvalidGeometry(
                "all tiles in a frame must have uniform power-of-two length",
            ));
        }
    }
    let n = tiles.len();
    let shape = RawPcsShape::for_frame(n, tile_len)?;
    verify_fresh_salts(&tiles)?;

    let ctx_bytes = ctx.encode();
    let mut raw_commits = vec![[0u8; 32]; n];
    for (i, t) in tiles.iter().enumerate() {
        raw_commits[i] = cores.raw_tile_commit(&ctx_bytes, i as u32, &t.raw_salt, &t.pixels);
    }
    let tile_merkle_layers = build_merkle_layers(cores, merkle_depth, &raw_commits);
    let tile_merkle_root = tile_merkle_layers[merkle_depth as usize][0];

    let mut raw_flat = Vec::with_capacity(n * tile_len);
    for t in &tiles {
        raw_flat.extend_from_slice(&t.pixels);
    }
    let raw_pcs = RawPcsCommitment::commit(cores, &ctx_bytes, shape, &raw_flat, enclave_rng_seed);

    let mut header = SensorFrameHeader {
        ctx,
        grid_width,
        grid_height,
        tile_len: tile_len as u32,
        merkle_depth,
        modality,
        tile_merkle_root,
        rt_raw: raw_pcs.root,
        enclave_pk: enclave_sk.public_key(),
        ots_index: 0,
        ots_pk: [0u8; 32],
        wots_sig: Vec::new(),
        ots_auth_path: Vec::new(),
    };
    enclave_sk.sign_header(&mut header)?;

    Ok(SealedSensorFrame {
        header,
        tiles,
        raw_commits,
        tile_merkle_layers,
        raw_pcs,
    })
}

/// High-throughput streaming CSI-2 `16x16`-tile frame sealer directly from a raw luminance plane
/// (`width % 16 == 0`, `height % 16 == 0`, e.g. `1280x720` -> `80x45 = 3,600` tiles, `921,600` px).
#[allow(clippy::too_many_arguments)]
pub fn seal_csi2_plane_streaming(
    cores: &CachedCshakeCores,
    enclave_sk: &EnclaveSigningKey,
    ctx: FrameContext,
    width: usize,
    height: usize,
    y_plane: &[u8],
    raw_salts: &[Salt256],
    enclave_rng_seed: &[u8; 32],
) -> Result<SealedPlaneHandle, SensoryRoiError> {
    if width == 0 || height == 0 || width % 16 != 0 || height % 16 != 0 {
        return Err(SensoryRoiError::InvalidGeometry(
            "CSI-2 plane dimensions must be positive multiples of 16",
        ));
    }
    let expected_px = width
        .checked_mul(height)
        .ok_or(SensoryRoiError::InvalidGeometry("plane pixel count overflow"))?;
    if y_plane.len() != expected_px {
        return Err(SensoryRoiError::InvalidGeometry(
            "y_plane.len() != width * height",
        ));
    }
    let grid_w = width / 16;
    let grid_h = height / 16;
    let grid_w_u32 = u32::try_from(grid_w)
        .map_err(|_| SensoryRoiError::InvalidGeometry("grid_width exceeds u32"))?;
    let grid_h_u32 = u32::try_from(grid_h)
        .map_err(|_| SensoryRoiError::InvalidGeometry("grid_height exceeds u32"))?;
    let n = grid_w
        .checked_mul(grid_h)
        .ok_or(SensoryRoiError::InvalidGeometry("tile grid count overflow"))?;
    let shape = RawPcsShape::for_frame(n, 256)?;
    if raw_salts.len() != n {
        return Err(SensoryRoiError::InvalidGeometry(
            "raw_salts length != tile count",
        ));
    }
    let mut seen: HashSet<Salt256> = HashSet::with_capacity(n);
    for (i, &s) in raw_salts.iter().enumerate() {
        if !seen.insert(s) {
            return Err(SensoryRoiError::SaltReuseDetected { tile_idx: i });
        }
    }

    let merkle_depth = merkle_depth_for(n);
    let ctx_bytes = ctx.encode();
    let mut raw_commits = vec![[0u8; 32]; n];
    let mut raw_flat = vec![0u8; n * 256];

    let threads = std::thread::available_parallelism()
        .map(|k| k.get().min(8))
        .unwrap_or(1);
    let chunk = n.div_ceil(threads.max(1));

    std::thread::scope(|s| {
        let mut rc_rest = raw_commits.as_mut_slice();
        let mut flat_rest = raw_flat.as_mut_slice();
        let mut start = 0usize;
        while !rc_rest.is_empty() {
            let take = chunk.min(rc_rest.len());
            let (rc_c, rc_r) = rc_rest.split_at_mut(take);
            let (fl_c, fl_r) = flat_rest.split_at_mut(take * 256);
            rc_rest = rc_r;
            flat_rest = fl_r;
            let base = start;
            s.spawn(move || {
                for off in 0..take {
                    let idx = base + off;
                    let ty = idx / grid_w;
                    let tx = idx % grid_w;
                    let row_base = ty * 16 * width + tx * 16;
                    let tile_dst = &mut fl_c[off * 256..(off + 1) * 256];
                    for r in 0..16 {
                        let src = &y_plane[row_base + r * width..row_base + r * width + 16];
                        tile_dst[r * 16..r * 16 + 16].copy_from_slice(src);
                    }
                    rc_c[off] = cores.raw_tile_commit(&ctx_bytes, idx as u32, &raw_salts[idx], tile_dst);
                }
            });
            start += take;
        }
    });

    let tile_merkle_layers = build_merkle_layers(cores, merkle_depth, &raw_commits);
    let tile_merkle_root = tile_merkle_layers[merkle_depth as usize][0];
    let raw_pcs = RawPcsCommitment::commit(cores, &ctx_bytes, shape, &raw_flat, enclave_rng_seed);

    let mut header = SensorFrameHeader {
        ctx,
        grid_width: grid_w_u32,
        grid_height: grid_h_u32,
        tile_len: 256,
        merkle_depth,
        modality: SensorModality::Csi2Tile16x16,
        tile_merkle_root,
        rt_raw: raw_pcs.root,
        enclave_pk: enclave_sk.public_key(),
        ots_index: 0,
        ots_pk: [0u8; 32],
        wots_sig: Vec::new(),
        ots_auth_path: Vec::new(),
    };
    enclave_sk.sign_header(&mut header)?;

    Ok(SealedPlaneHandle {
        header,
        width,
        raw_commits,
        tile_merkle_layers,
        raw_pcs,
        raw_flat,
    })
}

/// Handle produced by `seal_csi2_plane_streaming` (supports ROI opens AND untrusted-worker ZK proofs).
#[derive(Clone)]
pub struct SealedPlaneHandle {
    pub header: SensorFrameHeader,
    pub width: usize,
    pub raw_commits: Vec<Digest>,
    pub tile_merkle_layers: Vec<Vec<Digest>>,
    pub raw_pcs: RawPcsCommitment,
    pub raw_flat: Vec<u8>,
}

impl SealedPlaneHandle {
    pub fn open_merkle_path(&self, tile_idx: usize) -> Vec<Digest> {
        extract_merkle_path(&self.tile_merkle_layers, tile_idx)
    }

    pub fn open_roi_cert(&self, raw_salts: &[Salt256], roi_indices: &[u32]) -> RoiRevealCert {
        let openings = roi_indices
            .iter()
            .map(|&idx| {
                let i = idx as usize;
                RoiTileOpening {
                    tile_idx: idx,
                    pixels: self.raw_flat[i * 256..(i + 1) * 256].to_vec(),
                    raw_salt: raw_salts[i],
                    merkle_path: self.open_merkle_path(i),
                }
            })
            .collect();
        RoiRevealCert { openings }
    }
}

// ============================================================================
// §5. Raw-Only Zero-Bystander-Leakage ROI Reveal Certificates
// ============================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RoiTileItem {
    Opened { pixels: Vec<u8>, raw_salt: Salt256 },
    Sealed { leaf: Digest },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoiTileOpening {
    pub tile_idx: u32,
    pub pixels: Vec<u8>,
    pub raw_salt: Salt256,
    pub merkle_path: Vec<Digest>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoiRevealCert {
    pub openings: Vec<RoiTileOpening>,
}

impl RoiRevealCert {
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&(self.openings.len() as u32).to_le_bytes());
        for o in &self.openings {
            out.extend_from_slice(&o.tile_idx.to_le_bytes());
            out.extend_from_slice(&(o.pixels.len() as u32).to_le_bytes());
            out.extend_from_slice(&o.pixels);
            out.extend_from_slice(&o.raw_salt);
            out.extend_from_slice(&(o.merkle_path.len() as u32).to_le_bytes());
            for sib in &o.merkle_path {
                out.extend_from_slice(sib);
            }
        }
        out
    }
}

impl SealedSensorFrame {
    pub fn open_merkle_path(&self, tile_idx: usize) -> Vec<Digest> {
        extract_merkle_path(&self.tile_merkle_layers, tile_idx)
    }

    pub fn roi_view(&self, in_frustum: impl Fn(usize) -> bool) -> (Digest, Vec<RoiTileItem>) {
        let items = self
            .tiles
            .iter()
            .enumerate()
            .map(|(i, t)| {
                if in_frustum(i) {
                    RoiTileItem::Opened {
                        pixels: t.pixels.clone(),
                        raw_salt: t.raw_salt,
                    }
                } else {
                    RoiTileItem::Sealed {
                        leaf: self.tile_merkle_layers[0][i],
                    }
                }
            })
            .collect();
        (self.header.tile_merkle_root, items)
    }

    pub fn open_roi_cert(&self, roi_indices: &[u32]) -> RoiRevealCert {
        let openings = roi_indices
            .iter()
            .map(|&idx| {
                let i = idx as usize;
                let t = &self.tiles[i];
                RoiTileOpening {
                    tile_idx: idx,
                    pixels: t.pixels.clone(),
                    raw_salt: t.raw_salt,
                    merkle_path: self.open_merkle_path(i),
                }
            })
            .collect();
        RoiRevealCert { openings }
    }

    pub fn raw_pixels_flat(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.tiles.len() * self.header.tile_len as usize);
        for t in &self.tiles {
            out.extend_from_slice(&t.pixels);
        }
        out
    }
}

/// Verify an ROI reveal certificate using ONLY `expected_pk: &EnclavePublicKey`.
pub fn verify_roi_reveal_cert(
    cores: &CachedCshakeCores,
    expected_pk: &EnclavePublicKey,
    header: &SensorFrameHeader,
    cert: &RoiRevealCert,
) -> Result<(), SensoryRoiError> {
    verify_frame_header(cores, expected_pk, header)?;
    let max_tiles = header.num_tiles()?;
    let ctx_bytes = header.ctx.encode();
    let mut seen = HashSet::with_capacity(cert.openings.len());
    for o in &cert.openings {
        let idx = o.tile_idx as usize;
        if idx >= max_tiles {
            return Err(SensoryRoiError::TileIndexOutOfBounds {
                tile_idx: idx,
                max_tiles,
            });
        }
        if !seen.insert(o.tile_idx) {
            return Err(SensoryRoiError::DuplicateTileIndex(idx));
        }
        if o.pixels.len() != header.tile_len as usize {
            return Err(SensoryRoiError::InvalidGeometry("opened tile len != header.tile_len"));
        }
        let leaf = cores.raw_tile_commit(&ctx_bytes, o.tile_idx, &o.raw_salt, &o.pixels);
        verify_merkle_path(
            cores,
            &header.tile_merkle_root,
            header.merkle_depth,
            o.tile_idx,
            &leaf,
            &o.merkle_path,
        )?;
    }
    Ok(())
}

// ============================================================================
// §6. `GMaskExt4` Separable Univariate Blinding & Shared `UD-100` BaseFold/FRI
// ============================================================================

/// Separable univariate `GMaskExt4` supporting per-round degrees (e.g. `[2, 2, ...]` or `[5, 3, 3, ...]`).
struct MixedGMaskExt4 {
    round_degs: Vec<usize>,
    offsets: Vec<usize>,
    coeffs: Vec<Ext4>,
}

impl MixedGMaskExt4 {
    fn sample(round_degs: Vec<usize>, rng: &mut CShakeRng) -> Self {
        assert!(!round_degs.is_empty());
        let mut offsets = Vec::with_capacity(round_degs.len());
        let mut total = 0usize;
        for &d in &round_degs {
            assert!(d >= 1);
            offsets.push(total);
            total += d + 1;
        }
        let coeffs: Vec<Ext4> = (0..total).map(|_| rng.next_ext4()).collect();
        Self {
            round_degs,
            offsets,
            coeffs,
        }
    }

    fn slice(&self, j: usize) -> &[Ext4] {
        let st = self.offsets[j];
        &self.coeffs[st..st + self.round_degs[j] + 1]
    }

    fn hypercube_sum(&self) -> Ext4 {
        let l = self.round_degs.len();
        let scale = bb_pow(2, (l - 1) as u64);
        let mut acc = Ext4::ZERO;
        for j in 0..l {
            let c = self.slice(j);
            let mut gj1 = Ext4::ZERO;
            for &ck in c {
                gj1 = gj1.add(ck);
            }
            acc = acc.add(c[0]).add(gj1);
        }
        acc.scale_bb(scale)
    }

    fn round_poly(&self, i: usize, r_prefix: &[Ext4]) -> Vec<Ext4> {
        let l = self.round_degs.len();
        let deg = self.round_degs[i];
        let a_scale = bb_pow(2, (l - 1 - i) as u64);
        let mut pref = Ext4::ZERO;
        for (j, &rj) in r_prefix.iter().enumerate() {
            pref = pref.add(eval_poly_ext4(self.slice(j), rj));
        }
        let ci = self.slice(i);
        let mut k0 = pref.add(ci[0]).scale_bb(a_scale);
        if i + 1 < l {
            let b_scale = bb_pow(2, (l - 2 - i) as u64);
            let mut rem = Ext4::ZERO;
            for j in (i + 1)..l {
                let cj = self.slice(j);
                let mut gj1 = Ext4::ZERO;
                for &ck in cj {
                    gj1 = gj1.add(ck);
                }
                rem = rem.add(cj[0]).add(gj1);
            }
            k0 = k0.add(rem.scale_bb(b_scale));
        }
        let mut out = Vec::with_capacity(deg + 1);
        out.push(k0);
        for &ck in &ci[1..] {
            out.push(ck.scale_bb(a_scale));
        }
        out
    }

    fn build_weights(round_degs: &[usize], r_challenges: &[Ext4]) -> (Vec<Ext4>, Vec<Ext4>) {
        let l = round_degs.len();
        assert_eq!(r_challenges.len(), l);
        let total: usize = round_degs.iter().map(|&d| d + 1).sum();
        let sc = bb_pow(2, (l - 1) as u64);
        let two_sc = bb_mul(2, sc);
        let mut w_sum = vec![Ext4::ZERO; total];
        let mut w_at = vec![Ext4::ZERO; total];
        let mut off = 0usize;
        for (j, (&deg, &rj)) in round_degs.iter().zip(r_challenges.iter()).enumerate() {
            let _ = j;
            w_sum[off] = Ext4::from_bb(two_sc);
            for k in 1..=deg {
                w_sum[off + k] = Ext4::from_bb(sc);
            }
            let mut pw = Ext4::ONE;
            for k in 0..=deg {
                w_at[off + k] = pw;
                pw = pw.mul(rj);
            }
            off += deg + 1;
        }
        (w_sum, w_at)
    }
}

/// Prover-committed auxiliary HVZK coset-RS matrix on the EXACT SAME coset `D_0` as `rt_raw`.
struct AuxPcsCommitment {
    /// Optional basefield bit-column polynomials (`n_bb_rows * w0`, each with `[c..2c)` random tail).
    bb_coeffs: Vec<u32>,
    n_bb_rows: usize,
    /// `Ext4` polynomials (`n_ext_rows * w0`: `[G_poly, Z_0..Z_{K-1}, B_prox]`).
    ext_coeffs: Vec<Ext4>,
    n_ext_rows: usize,
    /// Column-major coset evaluations: `n0 * n_bb_rows` and `n0 * n_ext_rows`.
    bb_cw_cols: Vec<u32>,
    ext_cw_cols: Vec<Ext4>,
    col_salts: Vec<Salt128>,
    merkle_layers: Vec<Vec<Digest>>,
    root: Digest,
}

impl AuxPcsCommitment {
    fn commit(
        cores: &CachedCshakeCores,
        shape: RawPcsShape,
        bb_coeffs: Vec<u32>,
        n_bb_rows: usize,
        ext_coeffs: Vec<Ext4>,
        n_ext_rows: usize,
        rng: &mut CShakeRng,
    ) -> Self {
        assert_eq!(bb_coeffs.len(), n_bb_rows * shape.w0);
        assert_eq!(ext_coeffs.len(), n_ext_rows * shape.w0);

        let mut col_salts = vec![[0u8; 16]; shape.n0];
        for s in &mut col_salts {
            rng.fill_bytes(s);
        }

        let shift = canonical_coset_shift_bb(shape.log_n0);
        let tw = precompute_twiddles_bb(shape.n0);
        let mut shift_pows = Vec::with_capacity(shape.w0);
        let mut cur = 1u32;
        for _ in 0..shape.w0 {
            shift_pows.push(cur);
            cur = bb_mul(cur, shift);
        }

        let bb_evals: Vec<Vec<u32>> = (0..n_bb_rows)
            .map(|r| coset_eval_bb(&bb_coeffs[r * shape.w0..(r + 1) * shape.w0], shape.n0, &shift_pows, &tw))
            .collect();
        let ext_evals: Vec<Vec<Ext4>> = (0..n_ext_rows)
            .map(|r| coset_eval_ext4(&ext_coeffs[r * shape.w0..(r + 1) * shape.w0], shape.n0, &shift_pows, &tw))
            .collect();

        let mut bb_cw_cols = vec![0u32; shape.n0 * n_bb_rows];
        let mut ext_cw_cols = vec![Ext4::ZERO; shape.n0 * n_ext_rows];
        let mut leaves = vec![[0u8; 32]; shape.n0];

        let threads = std::thread::available_parallelism()
            .map(|n| n.get().min(8))
            .unwrap_or(1);
        if threads > 1 {
            let chunk = shape.n0.div_ceil(threads);
            std::thread::scope(|s| {
                let mut bb_rest = bb_cw_cols.as_mut_slice();
                let mut ext_rest = ext_cw_cols.as_mut_slice();
                let mut lf_rest = leaves.as_mut_slice();
                let mut start = 0usize;
                while !lf_rest.is_empty() {
                    let take = chunk.min(lf_rest.len());
                    let (bb_c, bb_r) = bb_rest.split_at_mut(take * n_bb_rows);
                    let (ex_c, ex_r) = ext_rest.split_at_mut(take * n_ext_rows);
                    let (lf_c, lf_r) = lf_rest.split_at_mut(take);
                    bb_rest = bb_r;
                    ext_rest = ex_r;
                    lf_rest = lf_r;
                    let b_ref = &bb_evals;
                    let e_ref = &ext_evals;
                    let salt_ref = &col_salts;
                    s.spawn(move || {
                        for off in 0..take {
                            let j = start + off;
                            let bc = &mut bb_c[off * n_bb_rows..(off + 1) * n_bb_rows];
                            for r in 0..n_bb_rows {
                                bc[r] = b_ref[r][j];
                            }
                            let ec = &mut ex_c[off * n_ext_rows..(off + 1) * n_ext_rows];
                            for r in 0..n_ext_rows {
                                ec[r] = e_ref[r][j];
                            }
                            lf_c[off] = cores.aux_pcs_leaf(j as u32, &salt_ref[j], bc, ec);
                        }
                    });
                    start += take;
                }
            });
        } else {
            for j in 0..shape.n0 {
                let bc = &mut bb_cw_cols[j * n_bb_rows..(j + 1) * n_bb_rows];
                for r in 0..n_bb_rows {
                    bc[r] = bb_evals[r][j];
                }
                let ec = &mut ext_cw_cols[j * n_ext_rows..(j + 1) * n_ext_rows];
                for r in 0..n_ext_rows {
                    ec[r] = ext_evals[r][j];
                }
                leaves[j] = cores.aux_pcs_leaf(j as u32, &col_salts[j], bc, ec);
            }
        }

        let merkle_layers = build_merkle_layers_with_core(
            &cores.aux_pcs_node,
            cores.empty_leaf(),
            shape.log_n0 as u32,
            &leaves,
        );
        let root = merkle_layers[shape.log_n0][0];
        Self {
            bb_coeffs,
            n_bb_rows,
            ext_coeffs,
            n_ext_rows,
            bb_cw_cols,
            ext_cw_cols,
            col_salts,
            merkle_layers,
            root,
        }
    }
}

/// One folded FRI level's Merkle root and deduplicated opened sibling pairs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FriLevelOpening {
    pub root: Digest,
    pub opened_pairs: Vec<[Ext4; 2]>,
    pub multiproof: MerkleMultiProof,
}

/// Shared `UD-100` HVZK linear-batch + BaseFold/FRI PCS opening proof against `(rt_raw, rt_aux)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkBaseFoldPcsOpening {
    pub y_z: Ext4,
    pub coeff_sc_rounds: Vec<[Ext4; 3]>,
    pub e_hat: Vec<Ext4>,
    pub e_prox: Ext4,
    pub bf_sc_rounds: Vec<[Ext4; 3]>,
    pub fri_levels: Vec<FriLevelOpening>,
    pub final_const: Ext4,
    pub pow_nonce: u64,
    pub raw_col_vals: Vec<u32>,
    pub raw_col_salts: Vec<Salt128>,
    pub raw_multiproof: MerkleMultiProof,
    pub aux_bb_vals: Vec<u32>,
    pub aux_ext_vals: Vec<Ext4>,
    pub aux_col_salts: Vec<Salt128>,
    pub aux_multiproof: MerkleMultiProof,
}

impl ZkBaseFoldPcsOpening {
    /// Reject any non-canonical BabyBear limb `>= P_U32` on direct Rust struct inputs before
    /// hashing or field arithmetic.
    pub fn validate_canonical(&self) -> Result<(), SensoryRoiError> {
        if !self.y_z.is_canonical()
            || !self.e_prox.is_canonical()
            || !self.final_const.is_canonical()
        {
            return Err(SensoryRoiError::NonCanonicalFieldElement);
        }
        for r in &self.coeff_sc_rounds {
            if !r.iter().all(|e| e.is_canonical()) {
                return Err(SensoryRoiError::NonCanonicalFieldElement);
            }
        }
        if !self.e_hat.iter().all(|e| e.is_canonical()) {
            return Err(SensoryRoiError::NonCanonicalFieldElement);
        }
        for r in &self.bf_sc_rounds {
            if !r.iter().all(|e| e.is_canonical()) {
                return Err(SensoryRoiError::NonCanonicalFieldElement);
            }
        }
        for lv in &self.fri_levels {
            for pair in &lv.opened_pairs {
                if !pair[0].is_canonical() || !pair[1].is_canonical() {
                    return Err(SensoryRoiError::NonCanonicalFieldElement);
                }
            }
        }
        if !self.raw_col_vals.iter().all(|&v| v < P_U32)
            || !self.aux_bb_vals.iter().all(|&v| v < P_U32)
            || !self.aux_ext_vals.iter().all(|e| e.is_canonical())
        {
            return Err(SensoryRoiError::NonCanonicalFieldElement);
        }
        Ok(())
    }

    fn write_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.y_z.to_bytes());
        out.push(self.coeff_sc_rounds.len() as u8);
        for r in &self.coeff_sc_rounds {
            for e in r {
                out.extend_from_slice(&e.to_bytes());
            }
        }
        out.push(self.e_hat.len() as u8);
        for e in &self.e_hat {
            out.extend_from_slice(&e.to_bytes());
        }
        out.extend_from_slice(&self.e_prox.to_bytes());
        out.push(self.bf_sc_rounds.len() as u8);
        for r in &self.bf_sc_rounds {
            for e in r {
                out.extend_from_slice(&e.to_bytes());
            }
        }
        out.push(self.fri_levels.len() as u8);
        for lv in &self.fri_levels {
            out.extend_from_slice(&lv.root);
            out.extend_from_slice(&(lv.opened_pairs.len() as u32).to_le_bytes());
            for p in &lv.opened_pairs {
                out.extend_from_slice(&p[0].to_bytes());
                out.extend_from_slice(&p[1].to_bytes());
            }
            lv.multiproof.write_to(out);
        }
        out.extend_from_slice(&self.final_const.to_bytes());
        out.extend_from_slice(&self.pow_nonce.to_le_bytes());

        out.extend_from_slice(&(self.raw_col_vals.len() as u32).to_le_bytes());
        for &v in &self.raw_col_vals {
            out.extend_from_slice(&v.to_le_bytes());
        }
        out.extend_from_slice(&(self.raw_col_salts.len() as u32).to_le_bytes());
        for s in &self.raw_col_salts {
            out.extend_from_slice(s);
        }
        self.raw_multiproof.write_to(out);

        out.extend_from_slice(&(self.aux_bb_vals.len() as u32).to_le_bytes());
        for &v in &self.aux_bb_vals {
            out.extend_from_slice(&v.to_le_bytes());
        }
        out.extend_from_slice(&(self.aux_ext_vals.len() as u32).to_le_bytes());
        for e in &self.aux_ext_vals {
            out.extend_from_slice(&e.to_bytes());
        }
        out.extend_from_slice(&(self.aux_col_salts.len() as u32).to_le_bytes());
        for s in &self.aux_col_salts {
            out.extend_from_slice(s);
        }
        self.aux_multiproof.write_to(out);
    }

    fn read_from(cur: &mut ByteCursor<'_>) -> Result<Self, SensoryRoiError> {
        let y_z = cur.read_ext4()?;
        let n_csc = cur.read_u8()? as usize;
        if n_csc == 0 || n_csc > 24 {
            return Err(SensoryRoiError::MalformedWireProof("invalid coeff_sc_rounds len"));
        }
        let mut coeff_sc_rounds = Vec::with_capacity(n_csc);
        for _ in 0..n_csc {
            coeff_sc_rounds.push([cur.read_ext4()?, cur.read_ext4()?, cur.read_ext4()?]);
        }
        let n_ehat = cur.read_u8()? as usize;
        if n_ehat == 0 || n_ehat > 8 {
            return Err(SensoryRoiError::MalformedWireProof("invalid e_hat len"));
        }
        let mut e_hat = Vec::with_capacity(n_ehat);
        for _ in 0..n_ehat {
            e_hat.push(cur.read_ext4()?);
        }
        let e_prox = cur.read_ext4()?;
        let n_bf = cur.read_u8()? as usize;
        if n_bf == 0 || n_bf > 25 {
            return Err(SensoryRoiError::MalformedWireProof("invalid bf_sc_rounds len"));
        }
        let mut bf_sc_rounds = Vec::with_capacity(n_bf);
        for _ in 0..n_bf {
            bf_sc_rounds.push([cur.read_ext4()?, cur.read_ext4()?, cur.read_ext4()?]);
        }
        let n_fri = cur.read_u8()? as usize;
        if n_fri > 24 {
            return Err(SensoryRoiError::MalformedWireProof("invalid fri_levels len"));
        }
        let mut fri_levels = Vec::with_capacity(n_fri);
        for _ in 0..n_fri {
            let root = cur.read_digest()?;
            let np = cur.read_u32()? as usize;
            if np > UD100_QUERIES * 2 {
                return Err(SensoryRoiError::MalformedWireProof("fri opened_pairs overflow"));
            }
            let mut opened_pairs = Vec::with_capacity(np);
            for _ in 0..np {
                opened_pairs.push([cur.read_ext4()?, cur.read_ext4()?]);
            }
            let multiproof = MerkleMultiProof::read_from(cur, UD100_QUERIES * 24)?;
            fri_levels.push(FriLevelOpening {
                root,
                opened_pairs,
                multiproof,
            });
        }
        let final_const = cur.read_ext4()?;
        let pow_nonce = cur.read_u64()?;

        let n_rv = cur.read_u32()? as usize;
        if n_rv > MAX_WIRE_RAW_COL_VALS {
            return Err(SensoryRoiError::MalformedWireProof("raw_col_vals overflow"));
        }
        let mut raw_col_vals = Vec::with_capacity(n_rv);
        for _ in 0..n_rv {
            raw_col_vals.push(cur.read_bb()?);
        }
        let n_rs = cur.read_u32()? as usize;
        if n_rs > UD100_QUERIES * 2 {
            return Err(SensoryRoiError::MalformedWireProof("raw_col_salts overflow"));
        }
        let mut raw_col_salts = Vec::with_capacity(n_rs);
        for _ in 0..n_rs {
            raw_col_salts.push(cur.read_salt128()?);
        }
        let raw_multiproof = MerkleMultiProof::read_from(cur, UD100_QUERIES * 32)?;

        let n_ab = cur.read_u32()? as usize;
        if n_ab > MAX_WIRE_AUX_BB_VALS {
            return Err(SensoryRoiError::MalformedWireProof("aux_bb_vals overflow"));
        }
        let mut aux_bb_vals = Vec::with_capacity(n_ab);
        for _ in 0..n_ab {
            aux_bb_vals.push(cur.read_bb()?);
        }
        let n_ae = cur.read_u32()? as usize;
        if n_ae > MAX_WIRE_AUX_EXT_VALS {
            return Err(SensoryRoiError::MalformedWireProof("aux_ext_vals overflow"));
        }
        let mut aux_ext_vals = Vec::with_capacity(n_ae);
        for _ in 0..n_ae {
            aux_ext_vals.push(cur.read_ext4()?);
        }
        let n_as = cur.read_u32()? as usize;
        if n_as > UD100_QUERIES * 2 {
            return Err(SensoryRoiError::MalformedWireProof("aux_col_salts overflow"));
        }
        let mut aux_col_salts = Vec::with_capacity(n_as);
        for _ in 0..n_as {
            aux_col_salts.push(cur.read_salt128()?);
        }
        let aux_multiproof = MerkleMultiProof::read_from(cur, UD100_QUERIES * 32)?;

        Ok(Self {
            y_z,
            coeff_sc_rounds,
            e_hat,
            e_prox,
            bf_sc_rounds,
            fri_levels,
            final_const,
            pow_nonce,
            raw_col_vals,
            raw_col_salts,
            raw_multiproof,
            aux_bb_vals,
            aux_ext_vals,
            aux_col_salts,
            aux_multiproof,
        })
    }
}

/// Linear combination spec for one `Q_s` polynomial inside `ZkBaseFoldPcsOpening`.
struct LinearPolySpec {
    /// Weight vector of length `C` (supported on `[0..C)`).
    w_col: Vec<Ext4>,
    /// Polynomial coefficients of length `W_0 = 2C`.
    poly_coeffs: Vec<Ext4>,
    /// Coset evaluation of `Q_s` on `D_0` (length `N_0`).
    poly_cw: Vec<Ext4>,
}

/// Shared prover for `sum_{s=0}^{K-1} <w_s, Q_s[0..C)> == y_batch` with `TVD = 0` Z-padding + BaseFold/FRI.
/// `aux` layout: `ext_coeffs[0]` = `G_poly`, `ext_coeffs[1..1+K]` = `Z_0..Z_{K-1}`, `ext_coeffs[1+K]` = `B_prox`.
fn prove_zk_basefold_opening(
    cores: &CachedCshakeCores,
    raw_pcs: &RawPcsCommitment,
    aux_pcs: &AuxPcsCommitment,
    q_specs: &[LinearPolySpec],
    tr: &mut FsTranscript,
) -> ZkBaseFoldPcsOpening {
    let sh = raw_pcs.shape;
    let k_cnt = q_specs.len();
    assert_eq!(aux_pcs.n_ext_rows, k_cnt + 2);

    // 1. One-time-pad inner product `y_z = sum_s <w_s, Z_s[0..C)>`.
    let mut y_z = Ext4::ZERO;
    for (s, qs) in q_specs.iter().enumerate() {
        let z_row = &aux_pcs.ext_coeffs[(1 + s) * sh.w0..(2 + s) * sh.w0];
        for c in 0..sh.c {
            if !qs.w_col[c].is_zero() {
                y_z = y_z.add(qs.w_col[c].mul(z_row[c]));
            }
        }
    }
    tr.absorb_ext4(b"pcs_yz", y_z);
    let lambda = tr.squeeze_ext4(b"pcs_lambda", true);

    // Build masked polynomials `Q_hat[s] = Z_s + lambda * Q_s` (both coeffs and coset evaluations!).
    let mut q_hat_coeffs: Vec<Vec<Ext4>> = Vec::with_capacity(k_cnt);
    let mut q_hat_cws: Vec<Vec<Ext4>> = Vec::with_capacity(k_cnt);
    for (s, qs) in q_specs.iter().enumerate() {
        let z_row = &aux_pcs.ext_coeffs[(1 + s) * sh.w0..(2 + s) * sh.w0];
        let coeffs: Vec<Ext4> = (0..sh.w0)
            .map(|u| z_row[u].add(lambda.mul(qs.poly_coeffs[u])))
            .collect();
        let cw: Vec<Ext4> = (0..sh.n0)
            .map(|j| {
                let zj = aux_pcs.ext_cw_cols[j * aux_pcs.n_ext_rows + (1 + s)];
                zj.add(lambda.mul(qs.poly_cw[j]))
            })
            .collect();
        q_hat_coeffs.push(coeffs);
        q_hat_cws.push(cw);
    }

    // 2. `m_c`-round degree-2 coefficient sumcheck on `sum_c sum_s w_s[c] * Q_hat[s][c]`.
    let mut w_cur: Vec<Vec<Ext4>> = q_specs.iter().map(|q| q.w_col.clone()).collect();
    let mut q_cur: Vec<Vec<Ext4>> = q_hat_coeffs.iter().map(|c| c[..sh.c].to_vec()).collect();
    let mut coeff_sc_rounds = Vec::with_capacity(sh.m_c);
    let mut zeta = Vec::with_capacity(sh.m_c);
    let mut len_c = sh.c;
    for _ in 0..sh.m_c {
        let half = len_c / 2;
        let (mut c0, mut c1, mut c2) = (Ext4::ZERO, Ext4::ZERO, Ext4::ZERO);
        for s in 0..k_cnt {
            for u in 0..half {
                let (w0, w1) = (w_cur[s][2 * u], w_cur[s][2 * u + 1]);
                let (p0, p1) = (q_cur[s][2 * u], q_cur[s][2 * u + 1]);
                let dw = w1.sub(w0);
                let dp = p1.sub(p0);
                c0 = c0.add(w0.mul(p0));
                c1 = c1.add(w0.mul(dp).add(dw.mul(p0)));
                c2 = c2.add(dw.mul(dp));
            }
        }
        let poly = [c0, c1, c2];
        tr.absorb_ext4_slice(b"pcs_csc", &poly);
        let zi = tr.squeeze_ext4(b"pcs_zeta", true);
        coeff_sc_rounds.push(poly);
        zeta.push(zi);
        for s in 0..k_cnt {
            w_cur[s] = fold_ext4_vec(&w_cur[s], zi);
            q_cur[s] = fold_ext4_vec(&q_cur[s], zi);
        }
        len_c = half;
    }

    let e_hat: Vec<Ext4> = q_cur.iter().map(|v| v[0]).collect();
    tr.absorb_ext4_slice(b"pcs_ehat", &e_hat);

    // 3. Independent-challenge `[BCIKS20]` Thm 1.7 affine-space proximity RLC `U_prox` masked by `B_prox`.
    let g_raw: Vec<Ext4> = (0..sh.r_d)
        .map(|_| tr.squeeze_ext4(b"pcs_g_raw", true))
        .collect();
    let g_aux_bb: Vec<Ext4> = (0..aux_pcs.n_bb_rows)
        .map(|_| tr.squeeze_ext4(b"pcs_g_abb", true))
        .collect();
    let b_prox_idx = aux_pcs.n_ext_rows - 1;
    let g_aux_ext: Vec<Ext4> = (0..b_prox_idx)
        .map(|_| tr.squeeze_ext4(b"pcs_g_aex", true))
        .collect();

    let mut u_prox_coeffs = aux_pcs.ext_coeffs[b_prox_idx * sh.w0..(b_prox_idx + 1) * sh.w0].to_vec();
    for r in 0..sh.r_d {
        let gr = g_raw[r];
        let row = &raw_pcs.coeffs[r * sh.w0..(r + 1) * sh.w0];
        for u in 0..sh.w0 {
            if row[u] != 0 {
                u_prox_coeffs[u] = u_prox_coeffs[u].add(gr.scale_bb(row[u]));
            }
        }
    }
    for r in 0..aux_pcs.n_bb_rows {
        let gb = g_aux_bb[r];
        let row = &aux_pcs.bb_coeffs[r * sh.w0..(r + 1) * sh.w0];
        for u in 0..sh.w0 {
            if row[u] != 0 {
                u_prox_coeffs[u] = u_prox_coeffs[u].add(gb.scale_bb(row[u]));
            }
        }
    }
    for r in 0..b_prox_idx {
        let ge = g_aux_ext[r];
        let row = &aux_pcs.ext_coeffs[r * sh.w0..(r + 1) * sh.w0];
        for u in 0..sh.w0 {
            u_prox_coeffs[u] = u_prox_coeffs[u].add(ge.mul(row[u]));
        }
    }

    let eq_zeta = build_eq_table_lsb_ext4(&zeta);
    let mut e_prox = Ext4::ZERO;
    for u in 0..sh.c {
        e_prox = e_prox.add(eq_zeta[u].mul(u_prox_coeffs[u]));
    }
    tr.absorb_ext4(b"pcs_eprox", e_prox);
    let theta = tr.squeeze_ext4(b"pcs_theta", true);

    // Combine into `F_0 = U_prox + sum_{s=0}^{K-1} theta^{s+1} * Q_hat[s]`.
    let mut theta_pows = Vec::with_capacity(k_cnt);
    let mut tp = theta;
    for _ in 0..k_cnt {
        theta_pows.push(tp);
        tp = tp.mul(theta);
    }

    let mut cur_poly = u_prox_coeffs;
    for s in 0..k_cnt {
        let ts = theta_pows[s];
        for u in 0..sh.w0 {
            cur_poly[u] = cur_poly[u].add(ts.mul(q_hat_coeffs[s][u]));
        }
    }

    let mut cur_cw = vec![Ext4::ZERO; sh.n0];
    for j in 0..sh.n0 {
        let mut v = aux_pcs.ext_cw_cols[j * aux_pcs.n_ext_rows + b_prox_idx];
        let raw_col = &raw_pcs.cw_cols[j * sh.r_d..(j + 1) * sh.r_d];
        for r in 0..sh.r_d {
            v = v.add(g_raw[r].scale_bb(raw_col[r]));
        }
        let abb_col = &aux_pcs.bb_cw_cols[j * aux_pcs.n_bb_rows..(j + 1) * aux_pcs.n_bb_rows];
        for r in 0..aux_pcs.n_bb_rows {
            v = v.add(g_aux_bb[r].scale_bb(abb_col[r]));
        }
        let aex_col = &aux_pcs.ext_cw_cols[j * aux_pcs.n_ext_rows..(j + 1) * aux_pcs.n_ext_rows];
        for r in 0..b_prox_idx {
            v = v.add(g_aux_ext[r].mul(aex_col[r]));
        }
        for s in 0..k_cnt {
            v = v.add(theta_pows[s].mul(q_hat_cws[s][j]));
        }
        cur_cw[j] = v;
    }

    // 4. `w = m_c + 1` Lockstep BaseFold / FRI Folding Rounds down to constant `final_const`.
    let w_rounds = sh.m_c + 1;
    let mut v_bf = vec![Ext4::ZERO; sh.w0];
    v_bf[..sh.c].copy_from_slice(&eq_zeta);

    let mut bf_sc_rounds = Vec::with_capacity(w_rounds);
    struct FriTreeState {
        cw: Vec<Ext4>,
        layers: Vec<Vec<Digest>>,
        root: Digest,
    }
    let mut fri_states: Vec<FriTreeState> = Vec::with_capacity(w_rounds - 1);

    let mut cur_shift = canonical_coset_shift_bb(sh.log_n0);
    let mut cur_omega = root_of_unity_bb(sh.n0);

    for rd in 0..w_rounds {
        let half_p = cur_poly.len() / 2;
        let (mut c0, mut c1, mut c2) = (Ext4::ZERO, Ext4::ZERO, Ext4::ZERO);
        for u in 0..half_p {
            let (v0, v1) = (v_bf[2 * u], v_bf[2 * u + 1]);
            let (f0, f1) = (cur_poly[2 * u], cur_poly[2 * u + 1]);
            let dv = v1.sub(v0);
            let df = f1.sub(f0);
            c0 = c0.add(v0.mul(f0));
            c1 = c1.add(v0.mul(df).add(dv.mul(f0)));
            c2 = c2.add(dv.mul(df));
        }
        let poly = [c0, c1, c2];
        tr.absorb_ext4_slice(b"bf_sc", &poly);
        let alpha = tr.squeeze_ext4(b"bf_alpha", true);
        let one_m_alpha = Ext4::ONE.sub(alpha);
        bf_sc_rounds.push(poly);

        v_bf = fold_ext4_vec(&v_bf, alpha);
        cur_poly = fold_ext4_vec(&cur_poly, alpha);

        // Coset FRI fold: `f'(x^2) = (1 - α)(f(x) + f(-x))/2 + α(f(x) - f(-x))/(2x)`.
        let half_d = cur_cw.len() / 2;
        let inv_shift = bb_inv(cur_shift).unwrap();
        let inv_omega = bb_inv(cur_omega).unwrap();
        let mut next_cw = Vec::with_capacity(half_d);
        let mut inv_x = inv_shift;
        for j in 0..half_d {
            let a = cur_cw[j];
            let b = cur_cw[j + half_d];
            let even = a.add(b).scale_bb(INV2_BB);
            let odd = a.sub(b).scale_bb(bb_mul(INV2_BB, inv_x));
            next_cw.push(one_m_alpha.mul(even).add(alpha.mul(odd)));
            inv_x = bb_mul(inv_x, inv_omega);
        }
        cur_cw = next_cw;
        cur_shift = bb_mul(cur_shift, cur_shift);
        cur_omega = bb_mul(cur_omega, cur_omega);

        if rd + 1 < w_rounds {
            let n_pairs = cur_cw.len() / 2;
            let leaves: Vec<Digest> = (0..n_pairs)
                .map(|p| cores.fri_pair_leaf(rd as u8, p as u32, cur_cw[p], cur_cw[p + n_pairs]))
                .collect();
            let depth = n_pairs.trailing_zeros();
            let layers = build_merkle_layers_with_core(
                &cores.fri_node,
                cores.empty_leaf(),
                depth,
                &leaves,
            );
            let root = layers[depth as usize][0];
            tr.absorb_root(b"fri_root", &root);
            fri_states.push(FriTreeState {
                cw: cur_cw.clone(),
                layers,
                root,
            });
        }
    }

    let final_const = cur_poly[0];
    tr.absorb_ext4(b"bf_final", final_const);

    // 5. 16-bit PoW grinding + `q = 148` distinct coset-pair queries.
    let pow_nonce = tr.mine_pow();
    tr.absorb_u64(b"bf_pow", pow_nonce);
    let pair_qs = tr.squeeze_distinct_indices(b"bf_queries", sh.n0 / 2, UD100_QUERIES);

    // Build deduplicated sorted Stage-0 column indices `{ j, j + n0/2 }`.
    let half0 = sh.n0 / 2;
    let mut stage0_cols = Vec::with_capacity(pair_qs.len() * 2);
    for &j in &pair_qs {
        stage0_cols.push(j);
    }
    for &j in &pair_qs {
        stage0_cols.push(j + half0);
    }

    let mut raw_col_vals = Vec::with_capacity(stage0_cols.len() * sh.r_d);
    let mut raw_col_salts = Vec::with_capacity(stage0_cols.len());
    let mut aux_bb_vals = Vec::with_capacity(stage0_cols.len() * aux_pcs.n_bb_rows);
    let mut aux_ext_vals = Vec::with_capacity(stage0_cols.len() * aux_pcs.n_ext_rows);
    let mut aux_col_salts = Vec::with_capacity(stage0_cols.len());

    for &col_idx in &stage0_cols {
        raw_col_vals.extend_from_slice(&raw_pcs.cw_cols[col_idx * sh.r_d..(col_idx + 1) * sh.r_d]);
        raw_col_salts.push(raw_pcs.col_salts[col_idx]);
        aux_bb_vals.extend_from_slice(
            &aux_pcs.bb_cw_cols[col_idx * aux_pcs.n_bb_rows..(col_idx + 1) * aux_pcs.n_bb_rows],
        );
        aux_ext_vals.extend_from_slice(
            &aux_pcs.ext_cw_cols[col_idx * aux_pcs.n_ext_rows..(col_idx + 1) * aux_pcs.n_ext_rows],
        );
        aux_col_salts.push(aux_pcs.col_salts[col_idx]);
    }
    let raw_multiproof = MerkleMultiProof::build(&raw_pcs.merkle_layers, &stage0_cols);
    let aux_multiproof = MerkleMultiProof::build(&aux_pcs.merkle_layers, &stage0_cols);

    // Extract deduplicated FRI pair openings for rounds `0 .. w_rounds - 1`.
    let mut cur_idxs = pair_qs;
    let mut fri_levels = Vec::with_capacity(fri_states.len());
    for st in &fri_states {
        let n_pairs = st.cw.len() / 2;
        let mask = n_pairs - 1;
        let uniq: Vec<usize> = cur_idxs
            .iter()
            .map(|&idx| idx & mask)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let opened_pairs: Vec<[Ext4; 2]> = uniq
            .iter()
            .map(|&p| [st.cw[p], st.cw[p + n_pairs]])
            .collect();
        let multiproof = MerkleMultiProof::build(&st.layers, &uniq);
        fri_levels.push(FriLevelOpening {
            root: st.root,
            opened_pairs,
            multiproof,
        });
        cur_idxs = uniq;
    }

    ZkBaseFoldPcsOpening {
        y_z,
        coeff_sc_rounds,
        e_hat,
        e_prox,
        bf_sc_rounds,
        fri_levels,
        final_const,
        pow_nonce,
        raw_col_vals,
        raw_col_salts,
        raw_multiproof,
        aux_bb_vals,
        aux_ext_vals,
        aux_col_salts,
        aux_multiproof,
    }
}

/// Verifier-side description of how each `Q_s` evaluates on a column `j` and at `zeta`.
enum VerifierQSpec<'a> {
    RawRows {
        z_col: &'a [Ext4],
        scale: Ext4,
        row_eq: &'a [Ext4],
    },
    AuxBbRows {
        z_col: &'a [Ext4],
        row_weights: &'a [Ext4],
    },
    AuxExt0Sparse {
        sparse_weights: &'a [Ext4],
    },
}

impl<'a> VerifierQSpec<'a> {
    fn eval_weight_at_zeta(&self, zeta: &[Ext4]) -> Ext4 {
        match self {
            Self::RawRows { z_col, scale, .. } => scale.mul(eq_mle_ext4(z_col, zeta)),
            Self::AuxBbRows { z_col, .. } => eq_mle_ext4(z_col, zeta),
            Self::AuxExt0Sparse { sparse_weights } => {
                // Evaluate sparse prefix `<sparse_weights, eq(zeta)[0..len]>` in `O(len)` without building 2^m_c!
                let len = sparse_weights.len();
                if len == 0 {
                    return Ext4::ZERO;
                }
                let k_lo = len.next_power_of_two().trailing_zeros() as usize;
                let eq_lo = build_eq_table_lsb_ext4(&zeta[..k_lo]);
                let mut hi_zero = Ext4::ONE;
                for &z in &zeta[k_lo..] {
                    hi_zero = hi_zero.mul(Ext4::ONE.sub(z));
                }
                let mut acc = Ext4::ZERO;
                for (u, &w) in sparse_weights.iter().enumerate() {
                    if !w.is_zero() {
                        acc = acc.add(w.mul(eq_lo[u]));
                    }
                }
                acc.mul(hi_zero)
            }
        }
    }

    fn eval_at_col(&self, raw_col: &[u32], aux_bb_col: &[u32], aux_ext_col: &[Ext4]) -> Ext4 {
        match self {
            Self::RawRows { row_eq, .. } => {
                let mut acc = Ext4::ZERO;
                for (&rw, &v) in row_eq.iter().zip(raw_col.iter()) {
                    acc = acc.add(rw.scale_bb(v));
                }
                acc
            }
            Self::AuxBbRows { row_weights, .. } => {
                let mut acc = Ext4::ZERO;
                for (&rw, &v) in row_weights.iter().zip(aux_bb_col.iter()) {
                    acc = acc.add(rw.scale_bb(v));
                }
                acc
            }
            Self::AuxExt0Sparse { .. } => aux_ext_col[0],
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn verify_zk_basefold_opening(
    cores: &CachedCshakeCores,
    ctx_bytes: &[u8; 24],
    sh: RawPcsShape,
    rt_raw: &Digest,
    rt_aux: &Digest,
    n_aux_bb_rows: usize,
    q_specs: &[VerifierQSpec<'_>],
    y_batch: Ext4,
    prf: &ZkBaseFoldPcsOpening,
    tr: &mut FsTranscript,
) -> Result<(), SensoryRoiError> {
    let k_cnt = q_specs.len();
    let n_aux_ext_rows = k_cnt + 2;
    let w_rounds = sh.m_c + 1;
    let n_cols = 2 * UD100_QUERIES;

    prf.validate_canonical()?;
    if prf.coeff_sc_rounds.len() != sh.m_c
        || prf.e_hat.len() != k_cnt
        || prf.bf_sc_rounds.len() != w_rounds
        || prf.fri_levels.len() != w_rounds - 1
    {
        return Err(SensoryRoiError::MalformedWireProof("BaseFold round/vector count mismatch"));
    }
    // Reject impossible Stage-0 opening lengths BEFORE squeezing/allocating shape-sized challenge vectors.
    if prf.raw_col_vals.len() != n_cols * sh.r_d
        || prf.raw_col_salts.len() != n_cols
        || prf.aux_bb_vals.len() != n_cols * n_aux_bb_rows
        || prf.aux_ext_vals.len() != n_cols * n_aux_ext_rows
        || prf.aux_col_salts.len() != n_cols
    {
        return Err(SensoryRoiError::MalformedWireProof("Stage-0 opened column count mismatch"));
    }

    // 1. Replay Z-padding challenge `lambda`.
    tr.absorb_ext4(b"pcs_yz", prf.y_z);
    let lambda = tr.squeeze_ext4(b"pcs_lambda", true);

    // 2. Verify `m_c`-round degree-2 coefficient sumcheck.
    let mut csc_running = prf.y_z.add(lambda.mul(y_batch));
    let mut zeta = Vec::with_capacity(sh.m_c);
    for (rd, poly) in prf.coeff_sc_rounds.iter().enumerate() {
        let p0 = poly[0];
        let p1 = poly[0].add(poly[1]).add(poly[2]);
        if p0.add(p1) != csc_running {
            return Err(SensoryRoiError::SumcheckRoundFailed {
                stage: "coeff_sc",
                round: rd,
            });
        }
        tr.absorb_ext4_slice(b"pcs_csc", poly);
        let zi = tr.squeeze_ext4(b"pcs_zeta", true);
        zeta.push(zi);
        csc_running = eval_poly_ext4(poly, zi);
    }

    let mut want_csc = Ext4::ZERO;
    for (s, qs) in q_specs.iter().enumerate() {
        want_csc = want_csc.add(qs.eval_weight_at_zeta(&zeta).mul(prf.e_hat[s]));
    }
    if want_csc != csc_running {
        return Err(SensoryRoiError::SumcheckTerminalFailed("coeff_sc"));
    }
    tr.absorb_ext4_slice(b"pcs_ehat", &prf.e_hat);

    // 3. Replay proximity RLC challenges + BaseFold lockstep sumcheck.
    let g_raw: Vec<Ext4> = (0..sh.r_d)
        .map(|_| tr.squeeze_ext4(b"pcs_g_raw", true))
        .collect();
    let g_aux_bb: Vec<Ext4> = (0..n_aux_bb_rows)
        .map(|_| tr.squeeze_ext4(b"pcs_g_abb", true))
        .collect();
    let b_prox_idx = n_aux_ext_rows - 1;
    let g_aux_ext: Vec<Ext4> = (0..b_prox_idx)
        .map(|_| tr.squeeze_ext4(b"pcs_g_aex", true))
        .collect();

    tr.absorb_ext4(b"pcs_eprox", prf.e_prox);
    let theta = tr.squeeze_ext4(b"pcs_theta", true);
    let mut theta_pows = Vec::with_capacity(k_cnt);
    let mut tp = theta;
    let mut bf_running = prf.e_prox;
    for s in 0..k_cnt {
        theta_pows.push(tp);
        bf_running = bf_running.add(tp.mul(prf.e_hat[s]));
        tp = tp.mul(theta);
    }

    let mut alphas = Vec::with_capacity(w_rounds);
    for (rd, poly) in prf.bf_sc_rounds.iter().enumerate() {
        let p0 = poly[0];
        let p1 = poly[0].add(poly[1]).add(poly[2]);
        if p0.add(p1) != bf_running {
            return Err(SensoryRoiError::SumcheckRoundFailed {
                stage: "basefold_sc",
                round: rd,
            });
        }
        tr.absorb_ext4_slice(b"bf_sc", poly);
        let alpha = tr.squeeze_ext4(b"bf_alpha", true);
        alphas.push(alpha);
        bf_running = eval_poly_ext4(poly, alpha);
        if rd + 1 < w_rounds {
            tr.absorb_root(b"fri_root", &prf.fri_levels[rd].root);
        }
    }
    tr.absorb_ext4(b"bf_final", prf.final_const);

    // Terminal BaseFold check: `v_bf(alphas) = eq(zeta, alphas[0..m_c]) * (1 - alphas[m_c])`.
    let v_final = eq_mle_ext4(&zeta, &alphas[..sh.m_c]).mul(Ext4::ONE.sub(alphas[sh.m_c]));
    if bf_running != v_final.mul(prf.final_const) {
        return Err(SensoryRoiError::SumcheckTerminalFailed("basefold_sc"));
    }

    // 4. Verify 16-bit PoW grinding & squeeze `q = 148` distinct coset-pair queries.
    if !tr.verify_pow(prf.pow_nonce) {
        return Err(SensoryRoiError::InvalidPowGrinding);
    }
    tr.absorb_u64(b"bf_pow", prf.pow_nonce);
    let pair_qs = tr.squeeze_distinct_indices(b"bf_queries", sh.n0 / 2, UD100_QUERIES);

    let half0 = sh.n0 / 2;
    let mut stage0_cols = Vec::with_capacity(n_cols);
    for &j in &pair_qs {
        stage0_cols.push(j);
    }
    for &j in &pair_qs {
        stage0_cols.push(j + half0);
    }
    debug_assert_eq!(stage0_cols.len(), n_cols);

    // Verify Merkle multi-proofs on `rt_raw` and `rt_aux`.
    let mut raw_leaves = Vec::with_capacity(n_cols);
    let mut aux_leaves = Vec::with_capacity(n_cols);
    for (pos, &col_idx) in stage0_cols.iter().enumerate() {
        let rc = &prf.raw_col_vals[pos * sh.r_d..(pos + 1) * sh.r_d];
        raw_leaves.push(cores.raw_pcs_leaf(ctx_bytes, col_idx as u32, &prf.raw_col_salts[pos], rc));
        let ab = &prf.aux_bb_vals[pos * n_aux_bb_rows..(pos + 1) * n_aux_bb_rows];
        let ae = &prf.aux_ext_vals[pos * n_aux_ext_rows..(pos + 1) * n_aux_ext_rows];
        aux_leaves.push(cores.aux_pcs_leaf(col_idx as u32, &prf.aux_col_salts[pos], ab, ae));
    }
    prf.raw_multiproof
        .verify(&cores.raw_pcs_node, rt_raw, sh.log_n0, &stage0_cols, &raw_leaves)?;
    prf.aux_multiproof
        .verify(&cores.aux_pcs_node, rt_aux, sh.log_n0, &stage0_cols, &aux_leaves)?;

    // Compute `F_0(x_j)` and `F_0(-x_j)` and verify round-0 FRI fold.
    let eval_f0 = |pos: usize| -> Ext4 {
        let rc = &prf.raw_col_vals[pos * sh.r_d..(pos + 1) * sh.r_d];
        let ab = &prf.aux_bb_vals[pos * n_aux_bb_rows..(pos + 1) * n_aux_bb_rows];
        let ae = &prf.aux_ext_vals[pos * n_aux_ext_rows..(pos + 1) * n_aux_ext_rows];
        let mut v = ae[b_prox_idx];
        for r in 0..sh.r_d {
            v = v.add(g_raw[r].scale_bb(rc[r]));
        }
        for r in 0..n_aux_bb_rows {
            v = v.add(g_aux_bb[r].scale_bb(ab[r]));
        }
        for r in 0..b_prox_idx {
            v = v.add(g_aux_ext[r].mul(ae[r]));
        }
        for s in 0..k_cnt {
            let qs_val = q_specs[s].eval_at_col(rc, ab, ae);
            let qhat = ae[1 + s].add(lambda.mul(qs_val));
            v = v.add(theta_pows[s].mul(qhat));
        }
        v
    };

    let shift0 = canonical_coset_shift_bb(sh.log_n0);
    let omega0 = root_of_unity_bb(sh.n0);
    let one_m_a0 = Ext4::ONE.sub(alphas[0]);
    let mut cur_vals: Vec<(usize, Ext4)> = Vec::with_capacity(pair_qs.len());
    for (qi, &j) in pair_qs.iter().enumerate() {
        let a = eval_f0(qi);
        let b = eval_f0(qi + pair_qs.len());
        let xj = bb_mul(shift0, bb_pow(omega0, j as u64));
        let inv_xj = bb_inv(xj).unwrap();
        let even = a.add(b).scale_bb(INV2_BB);
        let odd = a.sub(b).scale_bb(bb_mul(INV2_BB, inv_xj));
        let folded = one_m_a0.mul(even).add(alphas[0].mul(odd));
        cur_vals.push((j, folded));
    }

    // Verify FRI levels `0 .. w_rounds - 1` and final equality to `final_const`.
    let mut cur_shift = bb_mul(shift0, shift0);
    let mut cur_omega = bb_mul(omega0, omega0);
    let mut cur_domain = half0;

    for (rd, lv) in prf.fri_levels.iter().enumerate() {
        let n_pairs = cur_domain / 2;
        let mask = n_pairs - 1;
        let uniq: Vec<usize> = cur_vals
            .iter()
            .map(|&(idx, _)| idx & mask)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        if lv.opened_pairs.len() != uniq.len() {
            return Err(SensoryRoiError::MalformedWireProof("FRI opened_pairs count mismatch"));
        }
        let leaves: Vec<Digest> = uniq
            .iter()
            .zip(lv.opened_pairs.iter())
            .map(|(&p, pair)| cores.fri_pair_leaf(rd as u8, p as u32, pair[0], pair[1]))
            .collect();
        lv.multiproof.verify(
            &cores.fri_node,
            &lv.root,
            n_pairs.trailing_zeros() as usize,
            &uniq,
            &leaves,
        )?;
        let pair_map: BTreeMap<usize, [Ext4; 2]> = uniq
            .iter()
            .copied()
            .zip(lv.opened_pairs.iter().copied())
            .collect();

        for (qi, &(idx, expected_val)) in cur_vals.iter().enumerate() {
            let p = idx & mask;
            let side = if idx < n_pairs { 0 } else { 1 };
            let got = pair_map[&p][side];
            if got != expected_val {
                return Err(SensoryRoiError::FriConsistencyFailed {
                    round: rd + 1,
                    query_idx: qi,
                });
            }
        }

        let alpha = alphas[rd + 1];
        let one_m_a = Ext4::ONE.sub(alpha);
        let mut next_vals = Vec::with_capacity(uniq.len());
        for &p in &uniq {
            let pair = pair_map[&p];
            let xp = bb_mul(cur_shift, bb_pow(cur_omega, p as u64));
            let inv_xp = bb_inv(xp).unwrap();
            let even = pair[0].add(pair[1]).scale_bb(INV2_BB);
            let odd = pair[0].sub(pair[1]).scale_bb(bb_mul(INV2_BB, inv_xp));
            let folded = one_m_a.mul(even).add(alpha.mul(odd));
            next_vals.push((p, folded));
        }
        cur_vals = next_vals;
        cur_shift = bb_mul(cur_shift, cur_shift);
        cur_omega = bb_mul(cur_omega, cur_omega);
        cur_domain = n_pairs;
    }

    for (qi, &(_, v)) in cur_vals.iter().enumerate() {
        if v != prf.final_const {
            return Err(SensoryRoiError::FriConsistencyFailed {
                round: w_rounds,
                query_idx: qi,
            });
        }
    }
    Ok(())
}

// ============================================================================
// §7. Public Tile Subset Specification (Zero Per-Tile Sums!)
// ============================================================================

/// Public subset of tiles `S ⊆ [0, num_tiles)` (strictly canonicalized).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TileSubsetSpec {
    AllTiles,
    ExcludeRoi(Vec<u32>),
    ExplicitTiles(Vec<u32>),
}

impl TileSubsetSpec {
    fn validate(&self, num_tiles: usize) -> Result<usize, SensoryRoiError> {
        match self {
            Self::AllTiles => Ok(num_tiles),
            Self::ExcludeRoi(roi) => {
                let mut seen = HashSet::with_capacity(roi.len());
                for &idx in roi {
                    if (idx as usize) >= num_tiles {
                        return Err(SensoryRoiError::TileIndexOutOfBounds {
                            tile_idx: idx as usize,
                            max_tiles: num_tiles,
                        });
                    }
                    if !seen.insert(idx) {
                        return Err(SensoryRoiError::DuplicateTileIndex(idx as usize));
                    }
                }
                Ok(num_tiles - roi.len())
            }
            Self::ExplicitTiles(tiles) => {
                let mut seen = HashSet::with_capacity(tiles.len());
                for &idx in tiles {
                    if (idx as usize) >= num_tiles {
                        return Err(SensoryRoiError::TileIndexOutOfBounds {
                            tile_idx: idx as usize,
                            max_tiles: num_tiles,
                        });
                    }
                    if !seen.insert(idx) {
                        return Err(SensoryRoiError::DuplicateTileIndex(idx as usize));
                    }
                }
                Ok(tiles.len())
            }
        }
    }

    fn canonical_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        match self {
            Self::AllTiles => out.push(0),
            Self::ExcludeRoi(roi) => {
                out.push(1);
                let mut sorted = roi.clone();
                sorted.sort_unstable();
                out.extend_from_slice(&(sorted.len() as u32).to_le_bytes());
                for &idx in &sorted {
                    out.extend_from_slice(&idx.to_le_bytes());
                }
            }
            Self::ExplicitTiles(tiles) => {
                out.push(2);
                let mut sorted = tiles.clone();
                sorted.sort_unstable();
                out.extend_from_slice(&(sorted.len() as u32).to_le_bytes());
                for &idx in &sorted {
                    out.extend_from_slice(&idx.to_le_bytes());
                }
            }
        }
        out
    }

    fn indicator_table(&self, num_tiles: usize, n_tiles_pow2: usize) -> Vec<u8> {
        let mut tbl = vec![0u8; n_tiles_pow2];
        match self {
            Self::AllTiles => {
                for slot in &mut tbl[..num_tiles] {
                    *slot = 1;
                }
            }
            Self::ExcludeRoi(roi) => {
                for slot in &mut tbl[..num_tiles] {
                    *slot = 1;
                }
                for &idx in roi {
                    tbl[idx as usize] = 0;
                }
            }
            Self::ExplicitTiles(tiles) => {
                for &idx in tiles {
                    tbl[idx as usize] = 1;
                }
            }
        }
        tbl
    }

    /// Evaluate the multilinear extension `M_S~(r_t)` in `O(m_t)` for `AllTiles`, `O(|U| m_t)` for
    /// `ExcludeRoi`, or `O(|S| m_t)` for `ExplicitTiles`.
    fn eval_mle(&self, num_tiles: usize, r_t: &[Ext4]) -> Ext4 {
        fn eval_eq_at_idx(r: &[Ext4], idx: usize) -> Ext4 {
            let mut acc = Ext4::ONE;
            for (b, &rb) in r.iter().enumerate() {
                acc = acc.mul(if ((idx >> b) & 1) == 1 { rb } else { Ext4::ONE.sub(rb) });
            }
            acc
        }
        /// Exact `O(m_t)` MLE of `1_{[0, count)}` on `{0, 1}^{m_t}` via binary prefix decomposition.
        fn eval_prefix_mle(count: usize, r: &[Ext4]) -> Ext4 {
            let m = r.len();
            if count == 0 {
                return Ext4::ZERO;
            }
            if count >= (1usize << m) {
                return Ext4::ONE;
            }
            // Decompose `[0, count)` into disjoint aligned subcubes from MSB down to LSB.
            let mut acc = Ext4::ZERO;
            let mut prefix_prod = Ext4::ONE;
            for b in (0..m).rev() {
                if ((count >> b) & 1) == 1 {
                    // Subcube where bit `b = 0` and bits `< b` are free (sum = 1!).
                    acc = acc.add(prefix_prod.mul(Ext4::ONE.sub(r[b])));
                    prefix_prod = prefix_prod.mul(r[b]);
                } else {
                    prefix_prod = prefix_prod.mul(Ext4::ONE.sub(r[b]));
                }
            }
            acc
        }
        match self {
            Self::AllTiles => eval_prefix_mle(num_tiles, r_t),
            Self::ExcludeRoi(roi) => {
                let mut v = eval_prefix_mle(num_tiles, r_t);
                for &idx in roi {
                    v = v.sub(eval_eq_at_idx(r_t, idx as usize));
                }
                v
            }
            Self::ExplicitTiles(tiles) => {
                let mut v = Ext4::ZERO;
                for &idx in tiles {
                    v = v.add(eval_eq_at_idx(r_t, idx as usize));
                }
                v
            }
        }
    }
}

/// Build the full `(m_c + m_r)`-bit evaluation point `z_full = (1/2, ..., 1/2, r_t, 0, ..., 0)`
/// corresponding to `Raw~(1/2^{m_u}, r_t)` inside `RawPcsCommitment`.
fn build_raw_half_point(sh: RawPcsShape, r_t: &[Ext4]) -> Vec<Ext4> {
    assert_eq!(r_t.len(), sh.m_t);
    let mut z = Vec::with_capacity(sh.m_c + sh.m_r);
    let half = Ext4::from_bb(INV2_BB);
    for _ in 0..sh.m_u {
        z.push(half);
    }
    z.extend_from_slice(r_t);
    while z.len() < sh.m_c + sh.m_r {
        z.push(Ext4::ZERO);
    }
    z
}

fn combine_raw_rows_for_point(
    raw_pcs: &RawPcsCommitment,
    z_row: &[Ext4],
) -> (Vec<Ext4>, Vec<Ext4>, Vec<Ext4>) {
    let sh = raw_pcs.shape;
    let eq_row = build_eq_table_lsb_ext4(z_row);
    let mut coeffs = vec![Ext4::ZERO; sh.w0];
    for r in 0..sh.r_d {
        let rw = eq_row[r];
        let row = &raw_pcs.coeffs[r * sh.w0..(r + 1) * sh.w0];
        for u in 0..sh.w0 {
            if row[u] != 0 {
                coeffs[u] = coeffs[u].add(rw.scale_bb(row[u]));
            }
        }
    }
    let mut cw = vec![Ext4::ZERO; sh.n0];
    for j in 0..sh.n0 {
        let col = &raw_pcs.cw_cols[j * sh.r_d..(j + 1) * sh.r_d];
        let mut acc = Ext4::ZERO;
        for r in 0..sh.r_d {
            acc = acc.add(eq_row[r].scale_bb(col[r]));
        }
        cw[j] = acc;
    }
    (eq_row, coeffs, cw)
}

// ============================================================================
// §8. Proof (b): True Zero-Tile-Leakage `AmbientEnvelopeZkProof`
// ============================================================================

/// Succinct `UD-100` HVZK Ambient Threshold Proof against `rt_raw`:
/// proves `sum_{t ∈ S, u} Raw[t, u] == claimed_total <= threshold` with **ZERO per-tile sums on the wire**!
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AmbientEnvelopeZkProof {
    pub claimed_total: u64,
    pub threshold: u64,
    pub rt_aux: Digest,
    pub gmask_sum: Ext4,
    pub sumcheck_rounds: Vec<[Ext4; 3]>,
    pub pcs_opening: ZkBaseFoldPcsOpening,
}

impl AmbientEnvelopeZkProof {
    /// Reject any non-canonical BabyBear limb `>= P_U32` on direct Rust struct inputs.
    pub fn validate_canonical(&self) -> Result<(), SensoryRoiError> {
        if !self.gmask_sum.is_canonical() {
            return Err(SensoryRoiError::NonCanonicalFieldElement);
        }
        for r in &self.sumcheck_rounds {
            if !r.iter().all(|e| e.is_canonical()) {
                return Err(SensoryRoiError::NonCanonicalFieldElement);
            }
        }
        self.pcs_opening.validate_canonical()
    }

    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(AMBIENT_WIRE_MAGIC);
        out.extend_from_slice(&self.claimed_total.to_le_bytes());
        out.extend_from_slice(&self.threshold.to_le_bytes());
        out.extend_from_slice(&self.rt_aux);
        out.extend_from_slice(&self.gmask_sum.to_bytes());
        out.push(self.sumcheck_rounds.len() as u8);
        for r in &self.sumcheck_rounds {
            for e in r {
                out.extend_from_slice(&e.to_bytes());
            }
        }
        self.pcs_opening.write_to(&mut out);
        out
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, SensoryRoiError> {
        let mut cur = ByteCursor::new(bytes);
        if cur.read_exact(8)? != AMBIENT_WIRE_MAGIC {
            return Err(SensoryRoiError::MalformedWireProof("bad ambient magic"));
        }
        let claimed_total = cur.read_u64()?;
        let threshold = cur.read_u64()?;
        let rt_aux = cur.read_digest()?;
        let gmask_sum = cur.read_ext4()?;
        let n_sc = cur.read_u8()? as usize;
        if n_sc == 0 || n_sc > 24 {
            return Err(SensoryRoiError::MalformedWireProof("invalid ambient sumcheck rounds"));
        }
        let mut sumcheck_rounds = Vec::with_capacity(n_sc);
        for _ in 0..n_sc {
            sumcheck_rounds.push([cur.read_ext4()?, cur.read_ext4()?, cur.read_ext4()?]);
        }
        let pcs_opening = ZkBaseFoldPcsOpening::read_from(&mut cur)?;
        if cur.remaining() != 0 {
            return Err(SensoryRoiError::MalformedWireProof("trailing bytes in ambient proof"));
        }
        Ok(Self {
            claimed_total,
            threshold,
            rt_aux,
            gmask_sum,
            sumcheck_rounds,
            pcs_opening,
        })
    }
}

/// Untrusted-worker prover for `AmbientEnvelopeZkProof` (`TVD = 0`, `UD-100`, ZERO per-tile sums!).
#[allow(clippy::too_many_arguments)]
pub fn prove_ambient_envelope_zk(
    cores: &CachedCshakeCores,
    header: &SensorFrameHeader,
    raw_pcs: &RawPcsCommitment,
    raw_pixels_flat: &[u8],
    subset: &TileSubsetSpec,
    threshold: u64,
    prover_rng_seed: &[u8; 32],
) -> Result<AmbientEnvelopeZkProof, SensoryRoiError> {
    let num_tiles = header.num_tiles()?;
    let tile_len = header.tile_len as usize;
    let sh = raw_pcs.shape;
    if sh != RawPcsShape::for_frame(num_tiles, tile_len)? {
        return Err(SensoryRoiError::InvalidGeometry("raw_pcs shape mismatch"));
    }
    if raw_pixels_flat.len() != num_tiles * tile_len {
        return Err(SensoryRoiError::InvalidGeometry("raw_pixels_flat length mismatch"));
    }
    let subset_count = subset.validate(num_tiles)?;
    let total_samples = (subset_count as u64) * (tile_len as u64);
    if total_samples.saturating_mul(255) >= BABYBEAR_P {
        return Err(SensoryRoiError::BabyBearWrapRisk { total_samples });
    }

    let mask_tbl = subset.indicator_table(num_tiles, sh.n_tiles_pow2);
    let mut tile_sums_bb = vec![Ext4::ZERO; sh.n_tiles_pow2];
    let mut claimed_total: u64 = 0;
    for t in 0..num_tiles {
        let sm = sum_bytes(&raw_pixels_flat[t * tile_len..(t + 1) * tile_len]);
        tile_sums_bb[t] = Ext4::from_u64(sm);
        if mask_tbl[t] == 1 {
            claimed_total += sm;
        }
    }
    if claimed_total > threshold {
        return Err(SensoryRoiError::ThresholdExceeded {
            claimed: claimed_total,
            threshold,
        });
    }
    // Enforce cumulative `rt_raw` Vandermonde blinding budget (`<= shape.c` opened columns).
    raw_pcs.reserve_opening_columns(2 * UD100_QUERIES)?;

    let hdr_payload = header.signing_payload();
    let subset_bytes = subset.canonical_bytes();
    let mut rng = CShakeRng::from_parts(
        CUST_RNG_PROVER_AMBIENT,
        &[
            prover_rng_seed,
            &hdr_payload,
            &subset_bytes,
            &claimed_total.to_le_bytes(),
            &threshold.to_le_bytes(),
        ],
    );
    let round_degs = vec![2usize; sh.m_t];
    let gmask = MixedGMaskExt4::sample(round_degs.clone(), &mut rng);
    let gmask_sum = gmask.hypercube_sum();

    // Commit `rt_aux`: `4` Ext4 rows `[G_poly, Z_0, Z_1, B_prox]`.
    let n_ext_rows = 4usize;
    let mut aux_ext = vec![Ext4::ZERO; n_ext_rows * sh.w0];
    assert!(gmask.coeffs.len() < sh.c);
    for (u, &c) in gmask.coeffs.iter().enumerate() {
        aux_ext[u] = c;
    }
    for slot in &mut aux_ext[gmask.coeffs.len()..sh.w0] {
        *slot = rng.next_ext4();
    }
    for slot in &mut aux_ext[sh.w0..n_ext_rows * sh.w0] {
        *slot = rng.next_ext4();
    }
    let aux_pcs = AuxPcsCommitment::commit(cores, sh, Vec::new(), 0, aux_ext, n_ext_rows, &mut rng);

    // Initialize Fiat-Shamir transcript binding full header, shape, subset, claimed_total, threshold, rt_aux.
    let mut tr = FsTranscript::new(CUST_PROTO_AMBIENT);
    tr.absorb_bytes(b"hdr", &hdr_payload);
    tr.absorb_bytes(b"pcs_sh", &sh.tag_bytes());
    tr.absorb_bytes(b"subset", &subset_bytes);
    tr.absorb_u64(b"claimed", claimed_total);
    tr.absorb_u64(b"thresh", threshold);
    tr.absorb_root(b"rt_aux", &aux_pcs.root);
    tr.absorb_ext4(b"gmask_sum", gmask_sum);
    let rho = tr.squeeze_ext4(b"amb_rho", true);

    // Run `m_t`-round degree-2 HVZK sumcheck on `sum_t M_S(t) * tile_sum(t) + rho * g(t)`.
    let mut m_cur: Vec<Ext4> = mask_tbl.iter().map(|&b| Ext4::from_bb(b as u32)).collect();
    let mut s_cur = tile_sums_bb;
    let mut sumcheck_rounds = Vec::with_capacity(sh.m_t);
    let mut r_t = Vec::with_capacity(sh.m_t);

    for rd in 0..sh.m_t {
        let half = m_cur.len() / 2;
        let (mut c0, mut c1, mut c2) = (Ext4::ZERO, Ext4::ZERO, Ext4::ZERO);
        for u in 0..half {
            let (m0, m1) = (m_cur[2 * u], m_cur[2 * u + 1]);
            let (s0, s1) = (s_cur[2 * u], s_cur[2 * u + 1]);
            let dm = m1.sub(m0);
            let ds = s1.sub(s0);
            c0 = c0.add(m0.mul(s0));
            c1 = c1.add(m0.mul(ds).add(dm.mul(s0)));
            c2 = c2.add(dm.mul(ds));
        }
        let gm_p = gmask.round_poly(rd, &r_t);
        let blinded = [
            c0.add(rho.mul(gm_p[0])),
            c1.add(rho.mul(gm_p[1])),
            c2.add(rho.mul(gm_p[2])),
        ];
        tr.absorb_ext4_slice(b"amb_sc", &blinded);
        let ch = tr.squeeze_ext4(b"amb_rt", true);
        sumcheck_rounds.push(blinded);
        r_t.push(ch);
        m_cur = fold_ext4_vec(&m_cur, ch);
        s_cur = fold_ext4_vec(&s_cur, ch);
    }

    // Batch terminal claim `a_S * Raw~(1/2, r_t) + rho * g(r_t) == T_term` and `gmask_sum` with `beta_g`.
    let beta_g = tr.squeeze_ext4(b"amb_beta_g", true);
    let a_s = Ext4::from_bb(tile_len as u32).mul(subset.eval_mle(num_tiles, &r_t));
    let z_full = build_raw_half_point(sh, &r_t);
    let (_, u_raw_coeffs, u_raw_cw) = combine_raw_rows_for_point(raw_pcs, &z_full[sh.m_c..]);

    let eq_zcol = build_eq_table_lsb_ext4(&z_full[..sh.m_c]);
    let w0: Vec<Ext4> = eq_zcol.iter().map(|&e| a_s.mul(e)).collect();

    let (w_gsum, w_geval) = MixedGMaskExt4::build_weights(&round_degs, &r_t);
    let mut w1 = vec![Ext4::ZERO; sh.c];
    for u in 0..w_gsum.len() {
        w1[u] = rho.mul(w_geval[u]).add(beta_g.mul(w_gsum[u]));
    }
    let g_poly_coeffs = aux_pcs.ext_coeffs[..sh.w0].to_vec();
    let g_poly_cw: Vec<Ext4> = (0..sh.n0)
        .map(|j| aux_pcs.ext_cw_cols[j * aux_pcs.n_ext_rows])
        .collect();

    let q_specs = vec![
        LinearPolySpec {
            w_col: w0,
            poly_coeffs: u_raw_coeffs,
            poly_cw: u_raw_cw,
        },
        LinearPolySpec {
            w_col: w1,
            poly_coeffs: g_poly_coeffs,
            poly_cw: g_poly_cw,
        },
    ];
    let pcs_opening = prove_zk_basefold_opening(cores, raw_pcs, &aux_pcs, &q_specs, &mut tr);

    Ok(AmbientEnvelopeZkProof {
        claimed_total,
        threshold,
        rt_aux: aux_pcs.root,
        gmask_sum,
        sumcheck_rounds,
        pcs_opening,
    })
}

/// Standalone zero-witness verifier for `AmbientEnvelopeZkProof` (holds ONLY `expected_pk`!).
pub fn verify_ambient_envelope_zk(
    cores: &CachedCshakeCores,
    expected_pk: &EnclavePublicKey,
    header: &SensorFrameHeader,
    subset: &TileSubsetSpec,
    expected_threshold: u64,
    prf: &AmbientEnvelopeZkProof,
) -> Result<(), SensoryRoiError> {
    prf.validate_canonical()?;
    verify_frame_header(cores, expected_pk, header)?;
    let num_tiles = header.num_tiles()?;
    let tile_len = header.tile_len as usize;
    let sh = RawPcsShape::for_frame(num_tiles, tile_len)?;
    let subset_count = subset.validate(num_tiles)?;
    let total_samples = (subset_count as u64) * (tile_len as u64);
    let max_possible = total_samples.saturating_mul(255);
    if max_possible >= BABYBEAR_P {
        return Err(SensoryRoiError::BabyBearWrapRisk { total_samples });
    }
    if prf.threshold != expected_threshold || prf.claimed_total > expected_threshold {
        return Err(SensoryRoiError::ThresholdExceeded {
            claimed: prf.claimed_total,
            threshold: expected_threshold,
        });
    }
    if prf.claimed_total > max_possible {
        return Err(SensoryRoiError::ClaimedTotalOutOfRange {
            claimed: prf.claimed_total,
            max_possible,
        });
    }
    if prf.sumcheck_rounds.len() != sh.m_t {
        return Err(SensoryRoiError::MalformedWireProof("ambient sumcheck round count mismatch"));
    }

    let mut tr = FsTranscript::new(CUST_PROTO_AMBIENT);
    tr.absorb_bytes(b"hdr", &header.signing_payload());
    tr.absorb_bytes(b"pcs_sh", &sh.tag_bytes());
    tr.absorb_bytes(b"subset", &subset.canonical_bytes());
    tr.absorb_u64(b"claimed", prf.claimed_total);
    tr.absorb_u64(b"thresh", prf.threshold);
    tr.absorb_root(b"rt_aux", &prf.rt_aux);
    tr.absorb_ext4(b"gmask_sum", prf.gmask_sum);
    let rho = tr.squeeze_ext4(b"amb_rho", true);

    let mut running = Ext4::from_u64(prf.claimed_total).add(rho.mul(prf.gmask_sum));
    let mut r_t = Vec::with_capacity(sh.m_t);
    for (rd, poly) in prf.sumcheck_rounds.iter().enumerate() {
        let p0 = poly[0];
        let p1 = poly[0].add(poly[1]).add(poly[2]);
        if p0.add(p1) != running {
            return Err(SensoryRoiError::SumcheckRoundFailed {
                stage: "ambient_sc",
                round: rd,
            });
        }
        tr.absorb_ext4_slice(b"amb_sc", poly);
        let ch = tr.squeeze_ext4(b"amb_rt", true);
        r_t.push(ch);
        running = eval_poly_ext4(poly, ch);
    }

    let beta_g = tr.squeeze_ext4(b"amb_beta_g", true);
    let a_s = Ext4::from_bb(tile_len as u32).mul(subset.eval_mle(num_tiles, &r_t));
    let z_full = build_raw_half_point(sh, &r_t);
    let row_eq = build_eq_table_lsb_ext4(&z_full[sh.m_c..]);

    let round_degs = vec![2usize; sh.m_t];
    let (w_gsum, w_geval) = MixedGMaskExt4::build_weights(&round_degs, &r_t);
    let w_g_sparse: Vec<Ext4> = w_gsum
        .iter()
        .zip(w_geval.iter())
        .map(|(&ws, &we)| rho.mul(we).add(beta_g.mul(ws)))
        .collect();
    let y_batch = running.add(beta_g.mul(prf.gmask_sum));

    let v_specs = [
        VerifierQSpec::RawRows {
            z_col: &z_full[..sh.m_c],
            scale: a_s,
            row_eq: &row_eq,
        },
        VerifierQSpec::AuxExt0Sparse {
            sparse_weights: &w_g_sparse,
        },
    ];
    verify_zk_basefold_opening(
        cores,
        &header.ctx.encode(),
        sh,
        &header.rt_raw,
        &prf.rt_aux,
        0,
        &v_specs,
        y_batch,
        &prf.pcs_opening,
        &mut tr,
    )
}

// ============================================================================
// §9. Proof (a): Untrusted-Worker Zero-Raw-Pixel `BlurDownscaleZkProof`
// ============================================================================

/// Succinct `UD-100` HVZK Box-Blur / Downscale Proof against `rt_raw`:
/// proves for every `t ∈ blur_subset` that `sum_u Raw[t, u] == tile_len * B[t] + rem[t]` with
/// public `B[t] ∈ [0, 256)` and committed `rem[t] ∈ [0, tile_len)` (proved via `m_u = log2(tile_len)`
/// Boolean bit columns `b_k (1 - b_k) = 0`), with ZERO intra-tile pixel leakage (`TVD = 0`)!
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlurDownscaleZkProof {
    pub blurred_pixels: Vec<u8>,
    pub rt_aux: Digest,
    pub gmask_sum: Ext4,
    /// Round 0 has degree 5 (`[Ext4; 6]`), rounds `1..m_t` have degree 3 (`[Ext4; 4]`).
    pub round0_poly: [Ext4; 6],
    pub rest_rounds: Vec<[Ext4; 4]>,
    /// Zero-on-hypercube blinded evaluations `Raw~(1/2, r_t) + delta_0 * c_raw` and `bit_k~(r_t) + delta_0 * c_k`.
    pub hat_v_raw: Ext4,
    pub hat_v_bits: Vec<Ext4>,
    pub pcs_opening: ZkBaseFoldPcsOpening,
}

impl BlurDownscaleZkProof {
    /// Reject any non-canonical BabyBear limb `>= P_U32` on direct Rust struct inputs.
    pub fn validate_canonical(&self) -> Result<(), SensoryRoiError> {
        if !self.gmask_sum.is_canonical()
            || !self.round0_poly.iter().all(|e| e.is_canonical())
            || !self.hat_v_raw.is_canonical()
            || !self.hat_v_bits.iter().all(|e| e.is_canonical())
        {
            return Err(SensoryRoiError::NonCanonicalFieldElement);
        }
        for r in &self.rest_rounds {
            if !r.iter().all(|e| e.is_canonical()) {
                return Err(SensoryRoiError::NonCanonicalFieldElement);
            }
        }
        self.pcs_opening.validate_canonical()
    }

    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(BLUR_WIRE_MAGIC);
        out.extend_from_slice(&(self.blurred_pixels.len() as u32).to_le_bytes());
        out.extend_from_slice(&self.blurred_pixels);
        out.extend_from_slice(&self.rt_aux);
        out.extend_from_slice(&self.gmask_sum.to_bytes());
        for e in &self.round0_poly {
            out.extend_from_slice(&e.to_bytes());
        }
        out.push(self.rest_rounds.len() as u8);
        for r in &self.rest_rounds {
            for e in r {
                out.extend_from_slice(&e.to_bytes());
            }
        }
        out.extend_from_slice(&self.hat_v_raw.to_bytes());
        out.push(self.hat_v_bits.len() as u8);
        for e in &self.hat_v_bits {
            out.extend_from_slice(&e.to_bytes());
        }
        self.pcs_opening.write_to(&mut out);
        out
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, SensoryRoiError> {
        let mut cur = ByteCursor::new(bytes);
        if cur.read_exact(8)? != BLUR_WIRE_MAGIC {
            return Err(SensoryRoiError::MalformedWireProof("bad blur magic"));
        }
        let n_b = cur.read_u32()? as usize;
        if n_b == 0 || n_b > MAX_FRAME_TILES {
            return Err(SensoryRoiError::MalformedWireProof("invalid blurred_pixels len"));
        }
        let blurred_pixels = cur.read_exact(n_b)?.to_vec();
        let rt_aux = cur.read_digest()?;
        let gmask_sum = cur.read_ext4()?;
        let round0_poly = [
            cur.read_ext4()?,
            cur.read_ext4()?,
            cur.read_ext4()?,
            cur.read_ext4()?,
            cur.read_ext4()?,
            cur.read_ext4()?,
        ];
        let n_rest = cur.read_u8()? as usize;
        if n_rest > 24 {
            return Err(SensoryRoiError::MalformedWireProof("invalid blur rest_rounds len"));
        }
        let mut rest_rounds = Vec::with_capacity(n_rest);
        for _ in 0..n_rest {
            rest_rounds.push([
                cur.read_ext4()?,
                cur.read_ext4()?,
                cur.read_ext4()?,
                cur.read_ext4()?,
            ]);
        }
        let hat_v_raw = cur.read_ext4()?;
        let n_bits = cur.read_u8()? as usize;
        if n_bits > 16 {
            return Err(SensoryRoiError::MalformedWireProof("invalid hat_v_bits len"));
        }
        let mut hat_v_bits = Vec::with_capacity(n_bits);
        for _ in 0..n_bits {
            hat_v_bits.push(cur.read_ext4()?);
        }
        let pcs_opening = ZkBaseFoldPcsOpening::read_from(&mut cur)?;
        if cur.remaining() != 0 {
            return Err(SensoryRoiError::MalformedWireProof("trailing bytes in blur proof"));
        }
        Ok(Self {
            blurred_pixels,
            rt_aux,
            gmask_sum,
            round0_poly,
            rest_rounds,
            hat_v_raw,
            hat_v_bits,
            pcs_opening,
        })
    }
}

/// Evaluate the multilinear extension of public `blurred_pixels` (`0`-padded to `2^{m_t}`) at `r_t`.
fn eval_public_blur_mle(blurred_pixels: &[u8], r_t: &[Ext4]) -> Ext4 {
    let eq_t = build_eq_table_lsb_ext4(r_t);
    let mut acc = Ext4::ZERO;
    for (t, &b) in blurred_pixels.iter().enumerate() {
        if b != 0 {
            acc = acc.add(eq_t[t].scale_bb(b as u32));
        }
    }
    acc
}

/// Untrusted-worker prover for `BlurDownscaleZkProof` (`TVD = 0`, `UD-100`, Boolean `rem[t] < tile_len`!).
#[allow(clippy::too_many_arguments)]
pub fn prove_blur_downscale_zk(
    cores: &CachedCshakeCores,
    header: &SensorFrameHeader,
    raw_pcs: &RawPcsCommitment,
    raw_pixels_flat: &[u8],
    blur_subset: &TileSubsetSpec,
    prover_rng_seed: &[u8; 32],
) -> Result<BlurDownscaleZkProof, SensoryRoiError> {
    let num_tiles = header.num_tiles()?;
    let tile_len = header.tile_len as usize;
    let sh = raw_pcs.shape;
    if sh != RawPcsShape::for_frame(num_tiles, tile_len)? {
        return Err(SensoryRoiError::InvalidGeometry("raw_pcs shape mismatch"));
    }
    if raw_pixels_flat.len() != num_tiles * tile_len {
        return Err(SensoryRoiError::InvalidGeometry("raw_pixels_flat length mismatch"));
    }
    let _ = blur_subset.validate(num_tiles)?;
    // Enforce cumulative `rt_raw` Vandermonde blinding budget (`<= shape.c` opened columns).
    raw_pcs.reserve_opening_columns(2 * UD100_QUERIES)?;
    let mask_tbl = blur_subset.indicator_table(num_tiles, sh.n_tiles_pow2);

    // Compute public blurred pixels `B[t] = sum(Raw[t]) / tile_len ∈ [0, 256)` and secret remainders `rem[t]`.
    let mut blurred_pixels = vec![0u8; num_tiles];
    let mut raw_half_tbl = vec![Ext4::ZERO; sh.n_tiles_pow2];
    let inv_tile_len = bb_inv(tile_len as u32).unwrap();
    let mut bit_tables = vec![vec![0u32; sh.n_tiles_pow2]; sh.m_u];

    for t in 0..num_tiles {
        let sm = sum_bytes(&raw_pixels_flat[t * tile_len..(t + 1) * tile_len]) as u32;
        // `Raw~(1/2^{m_u}, t) = sum(Raw[t]) / tile_len` in `BabyBear`.
        raw_half_tbl[t] = Ext4::from_bb(bb_mul(sm, inv_tile_len));
        if mask_tbl[t] == 1 {
            let mean = sm / (tile_len as u32);
            let rem = sm % (tile_len as u32);
            debug_assert!(mean < 256 && rem < tile_len as u32);
            blurred_pixels[t] = mean as u8;
            for k in 0..sh.m_u {
                bit_tables[k][t] = (rem >> k) & 1;
            }
        }
    }

    let hdr_payload = header.signing_payload();
    let subset_bytes = blur_subset.canonical_bytes();
    let mut rng = CShakeRng::from_parts(
        CUST_RNG_PROVER_BLUR,
        &[prover_rng_seed, &hdr_payload, &subset_bytes, &blurred_pixels],
    );
    let mut round_degs = vec![3usize; sh.m_t];
    round_degs[0] = 5;
    let gmask = MixedGMaskExt4::sample(round_degs.clone(), &mut rng);
    let gmask_sum = gmask.hypercube_sum();
    let n_g = gmask.coeffs.len();

    // Sample zero-on-hypercube blinding scalars `c_raw, c_0..c_{m_u-1}` (multiplied by `t_0(1 - t_0)`).
    let c_raw = rng.next_ext4();
    let c_bits: Vec<Ext4> = (0..sh.m_u).map(|_| rng.next_ext4()).collect();

    // Build `rt_aux`:
    // - `n_bb_rows = m_u * r_bit` basefield bit-column polynomials (each with `[c..2c)` uniform random tail)
    // - `n_ext_rows = 5` `Ext4` polynomials: `[G_poly, Z_0, Z_1, Z_2, B_prox]`
    let n_bb_rows = sh.m_u * sh.r_bit;
    let mut aux_bb = vec![0u32; n_bb_rows * sh.w0];
    for k in 0..sh.m_u {
        for rb in 0..sh.r_bit {
            let row_idx = k * sh.r_bit + rb;
            let dst = &mut aux_bb[row_idx * sh.w0..(row_idx + 1) * sh.w0];
            let base = rb * sh.c;
            let take = sh.n_tiles_pow2.saturating_sub(base).min(sh.c);
            dst[..take].copy_from_slice(&bit_tables[k][base..base + take]);
            for slot in &mut dst[sh.c..sh.w0] {
                *slot = rng.next_bb();
            }
        }
    }

    let n_ext_rows = 5usize; // G_poly, Z_0, Z_1, Z_2, B_prox
    let mut aux_ext = vec![Ext4::ZERO; n_ext_rows * sh.w0];
    assert!(n_g + 1 + sh.m_u < sh.c);
    aux_ext[..n_g].copy_from_slice(&gmask.coeffs);
    aux_ext[n_g] = c_raw;
    aux_ext[n_g + 1..n_g + 1 + sh.m_u].copy_from_slice(&c_bits);
    for slot in &mut aux_ext[n_g + 1 + sh.m_u..sh.w0] {
        *slot = rng.next_ext4();
    }
    for slot in &mut aux_ext[sh.w0..n_ext_rows * sh.w0] {
        *slot = rng.next_ext4();
    }

    let aux_pcs =
        AuxPcsCommitment::commit(cores, sh, aux_bb, n_bb_rows, aux_ext, n_ext_rows, &mut rng);

    // Initialize Fiat-Shamir transcript.
    let mut tr = FsTranscript::new(CUST_PROTO_BLUR);
    tr.absorb_bytes(b"hdr", &hdr_payload);
    tr.absorb_bytes(b"pcs_sh", &sh.tag_bytes());
    tr.absorb_bytes(b"subset", &subset_bytes);
    tr.absorb_bytes(b"blur_px", &blurred_pixels);
    tr.absorb_root(b"rt_aux", &aux_pcs.root);
    tr.absorb_ext4(b"gmask_sum", gmask_sum);

    let tau: Vec<Ext4> = (0..sh.m_t)
        .map(|_| tr.squeeze_ext4(b"blr_tau", true))
        .collect();
    let alpha_batch = tr.squeeze_ext4(b"blr_alpha", true);
    let rho = tr.squeeze_ext4(b"blr_rho", true);

    let mut alpha_pows = Vec::with_capacity(sh.m_u);
    let mut ap = alpha_batch;
    for _ in 0..sh.m_u {
        alpha_pows.push(ap);
        ap = ap.mul(alpha_batch);
    }

    let mut eq_cur = build_eq_table_lsb_ext4(&tau);
    let mut m_cur: Vec<Ext4> = mask_tbl.iter().map(|&b| Ext4::from_bb(b as u32)).collect();
    let mut b_cur: Vec<Ext4> = vec![Ext4::ZERO; sh.n_tiles_pow2];
    for t in 0..num_tiles {
        b_cur[t] = Ext4::from_bb(blurred_pixels[t] as u32);
    }
    let mut raw_cur = raw_half_tbl;
    let mut bit_cur: Vec<Vec<Ext4>> = bit_tables
        .iter()
        .map(|col| col.iter().map(|&v| Ext4::from_bb(v)).collect())
        .collect();

    let tile_len_u32 = tile_len as u32;
    let mut r_t = Vec::with_capacity(sh.m_t);

    // Round 0 (degree 5 due to `t_0(1 - t_0)` blinding on `raw_cur` and `bit_cur`).
    let half0 = sh.n_tiles_pow2 / 2;
    let mut evals0 = [Ext4::ZERO; 6];
    for x_int in 0u32..6 {
        let x_m_x2 = bb_mul(x_int, bb_sub(1, x_int)); // x(1 - x)
        let raw_shift = c_raw.scale_bb(x_m_x2);
        let bit_shifts: Vec<Ext4> = c_bits.iter().map(|&ck| ck.scale_bb(x_m_x2)).collect();
        let mut acc = Ext4::ZERO;
        for u in 0..half0 {
            let eq_x = eq_cur[2 * u].add(eq_cur[2 * u + 1].sub(eq_cur[2 * u]).scale_bb(x_int));
            let m_x = m_cur[2 * u].add(m_cur[2 * u + 1].sub(m_cur[2 * u]).scale_bb(x_int));
            let b_x = b_cur[2 * u].add(b_cur[2 * u + 1].sub(b_cur[2 * u]).scale_bb(x_int));
            let raw_x = raw_cur[2 * u]
                .add(raw_cur[2 * u + 1].sub(raw_cur[2 * u]).scale_bb(x_int))
                .add(raw_shift);
            let mut rem_x = Ext4::ZERO;
            let mut bool_x = Ext4::ZERO;
            for k in 0..sh.m_u {
                let bk_x = bit_cur[k][2 * u]
                    .add(bit_cur[k][2 * u + 1].sub(bit_cur[k][2 * u]).scale_bb(x_int))
                    .add(bit_shifts[k]);
                rem_x = rem_x.add(bk_x.scale_bb(1u32 << k));
                bool_x = bool_x.add(alpha_pows[k].mul(bk_x.mul(Ext4::ONE.sub(bk_x))));
            }
            let diff = raw_x.scale_bb(tile_len_u32).sub(b_x.scale_bb(tile_len_u32)).sub(rem_x);
            acc = acc.add(eq_x.mul(m_x.mul(diff).add(bool_x)));
        }
        evals0[x_int as usize] = acc;
    }
    let unm0 = interpolate_monomial_0_to_d(&evals0);
    let gm0 = gmask.round_poly(0, &[]);
    let round0_poly = [
        unm0[0].add(rho.mul(gm0[0])),
        unm0[1].add(rho.mul(gm0[1])),
        unm0[2].add(rho.mul(gm0[2])),
        unm0[3].add(rho.mul(gm0[3])),
        unm0[4].add(rho.mul(gm0[4])),
        unm0[5].add(rho.mul(gm0[5])),
    ];
    tr.absorb_ext4_slice(b"blr_rd0", &round0_poly);
    let r0 = tr.squeeze_non_binary_ext4(b"blr_r0");
    r_t.push(r0);

    // Fold round 0 (including constant `delta_0 * c_*` shift into `raw_cur` and `bit_cur`).
    let delta0 = r0.mul(Ext4::ONE.sub(r0));
    eq_cur = fold_ext4_vec(&eq_cur, r0);
    m_cur = fold_ext4_vec(&m_cur, r0);
    b_cur = fold_ext4_vec(&b_cur, r0);
    raw_cur = fold_ext4_vec(&raw_cur, r0)
        .into_iter()
        .map(|v| v.add(delta0.mul(c_raw)))
        .collect();
    for k in 0..sh.m_u {
        let sh_k = delta0.mul(c_bits[k]);
        bit_cur[k] = fold_ext4_vec(&bit_cur[k], r0)
            .into_iter()
            .map(|v| v.add(sh_k))
            .collect();
    }

    // Rounds `1 .. m_t - 1` (pure degree 3!).
    let mut rest_rounds = Vec::with_capacity(sh.m_t - 1);
    for rd in 1..sh.m_t {
        let half = eq_cur.len() / 2;
        let mut evals = [Ext4::ZERO; 4];
        for x_int in 0u32..4 {
            let mut acc = Ext4::ZERO;
            for u in 0..half {
                let eq_x = eq_cur[2 * u].add(eq_cur[2 * u + 1].sub(eq_cur[2 * u]).scale_bb(x_int));
                let m_x = m_cur[2 * u].add(m_cur[2 * u + 1].sub(m_cur[2 * u]).scale_bb(x_int));
                let b_x = b_cur[2 * u].add(b_cur[2 * u + 1].sub(b_cur[2 * u]).scale_bb(x_int));
                let raw_x =
                    raw_cur[2 * u].add(raw_cur[2 * u + 1].sub(raw_cur[2 * u]).scale_bb(x_int));
                let mut rem_x = Ext4::ZERO;
                let mut bool_x = Ext4::ZERO;
                for k in 0..sh.m_u {
                    let bk_x = bit_cur[k][2 * u]
                        .add(bit_cur[k][2 * u + 1].sub(bit_cur[k][2 * u]).scale_bb(x_int));
                    rem_x = rem_x.add(bk_x.scale_bb(1u32 << k));
                    bool_x = bool_x.add(alpha_pows[k].mul(bk_x.mul(Ext4::ONE.sub(bk_x))));
                }
                let diff = raw_x
                    .scale_bb(tile_len_u32)
                    .sub(b_x.scale_bb(tile_len_u32))
                    .sub(rem_x);
                acc = acc.add(eq_x.mul(m_x.mul(diff).add(bool_x)));
            }
            evals[x_int as usize] = acc;
        }
        let unm = interpolate_monomial_0_to_d(&evals);
        let gm = gmask.round_poly(rd, &r_t);
        let poly = [
            unm[0].add(rho.mul(gm[0])),
            unm[1].add(rho.mul(gm[1])),
            unm[2].add(rho.mul(gm[2])),
            unm[3].add(rho.mul(gm[3])),
        ];
        tr.absorb_ext4_slice(b"blr_rd", &poly);
        let ri = tr.squeeze_ext4(b"blr_ri", true);
        rest_rounds.push(poly);
        r_t.push(ri);

        eq_cur = fold_ext4_vec(&eq_cur, ri);
        m_cur = fold_ext4_vec(&m_cur, ri);
        b_cur = fold_ext4_vec(&b_cur, ri);
        raw_cur = fold_ext4_vec(&raw_cur, ri);
        for col in &mut bit_cur {
            *col = fold_ext4_vec(col, ri);
        }
    }

    let hat_v_raw = raw_cur[0];
    let hat_v_bits: Vec<Ext4> = bit_cur.iter().map(|c| c[0]).collect();
    tr.absorb_ext4(b"blr_hv_raw", hat_v_raw);
    tr.absorb_ext4_slice(b"blr_hv_bits", &hat_v_bits);

    // Batch `K = 3` linear claims (`U_raw`, `U_bits`, `G_poly`) via `beta_bits`, `beta_gsum`, `beta_geval`.
    let beta_bits: Vec<Ext4> = (0..sh.m_u)
        .map(|_| tr.squeeze_ext4(b"blr_bb", true))
        .collect();
    let beta_gsum = tr.squeeze_ext4(b"blr_bgs", true);
    let beta_geval = tr.squeeze_ext4(b"blr_bge", true);

    // Q_0 = U_raw
    let z_full = build_raw_half_point(sh, &r_t);
    let (_, u_raw_coeffs, u_raw_cw) = combine_raw_rows_for_point(raw_pcs, &z_full[sh.m_c..]);
    let w_raw = build_eq_table_lsb_ext4(&z_full[..sh.m_c]);

    // Q_1 = U_bits = sum_{k, rb} (beta_bits[k] * eq_hi[rb]) * Bit_row[k * r_bit + rb]
    let mut z_bits_col = Vec::with_capacity(sh.m_c);
    let lo_bits = sh.m_t.min(sh.m_c);
    z_bits_col.extend_from_slice(&r_t[..lo_bits]);
    while z_bits_col.len() < sh.m_c {
        z_bits_col.push(Ext4::ZERO);
    }
    let eq_bits_hi = if sh.m_t > sh.m_c {
        build_eq_table_lsb_ext4(&r_t[sh.m_c..])
    } else {
        vec![Ext4::ONE]
    };
    let mut bit_row_weights = Vec::with_capacity(n_bb_rows);
    for k in 0..sh.m_u {
        for rb in 0..sh.r_bit {
            bit_row_weights.push(beta_bits[k].mul(eq_bits_hi[rb]));
        }
    }
    let mut u_bits_coeffs = vec![Ext4::ZERO; sh.w0];
    for r in 0..n_bb_rows {
        let rw = bit_row_weights[r];
        let row = &aux_pcs.bb_coeffs[r * sh.w0..(r + 1) * sh.w0];
        for u in 0..sh.w0 {
            if row[u] != 0 {
                u_bits_coeffs[u] = u_bits_coeffs[u].add(rw.scale_bb(row[u]));
            }
        }
    }
    let mut u_bits_cw = vec![Ext4::ZERO; sh.n0];
    for j in 0..sh.n0 {
        let col = &aux_pcs.bb_cw_cols[j * n_bb_rows..(j + 1) * n_bb_rows];
        let mut acc = Ext4::ZERO;
        for r in 0..n_bb_rows {
            acc = acc.add(bit_row_weights[r].scale_bb(col[r]));
        }
        u_bits_cw[j] = acc;
    }
    let w_bits = build_eq_table_lsb_ext4(&z_bits_col);

    // Q_2 = G_poly (holds `gmask` at `0..n_g`, `c_raw` at `n_g`, `c_bits` at `n_g+1..n_g+1+m_u`).
    let (w_gsum, w_geval) = MixedGMaskExt4::build_weights(&round_degs, &r_t);
    let mut w_g = vec![Ext4::ZERO; sh.c];
    for u in 0..n_g {
        w_g[u] = beta_gsum.mul(w_gsum[u]).add(beta_geval.mul(w_geval[u]));
    }
    w_g[n_g] = delta0;
    for k in 0..sh.m_u {
        w_g[n_g + 1 + k] = beta_bits[k].mul(delta0);
    }
    let g_poly_coeffs = aux_pcs.ext_coeffs[..sh.w0].to_vec();
    let g_poly_cw: Vec<Ext4> = (0..sh.n0)
        .map(|j| aux_pcs.ext_cw_cols[j * aux_pcs.n_ext_rows])
        .collect();

    let q_specs = vec![
        LinearPolySpec {
            w_col: w_raw,
            poly_coeffs: u_raw_coeffs,
            poly_cw: u_raw_cw,
        },
        LinearPolySpec {
            w_col: w_bits,
            poly_coeffs: u_bits_coeffs,
            poly_cw: u_bits_cw,
        },
        LinearPolySpec {
            w_col: w_g,
            poly_coeffs: g_poly_coeffs,
            poly_cw: g_poly_cw,
        },
    ];
    let pcs_opening = prove_zk_basefold_opening(cores, raw_pcs, &aux_pcs, &q_specs, &mut tr);

    Ok(BlurDownscaleZkProof {
        blurred_pixels,
        rt_aux: aux_pcs.root,
        gmask_sum,
        round0_poly,
        rest_rounds,
        hat_v_raw,
        hat_v_bits,
        pcs_opening,
    })
}

/// Standalone zero-witness verifier for `BlurDownscaleZkProof` (holds ONLY `expected_pk`!).
pub fn verify_blur_downscale_zk(
    cores: &CachedCshakeCores,
    expected_pk: &EnclavePublicKey,
    header: &SensorFrameHeader,
    blur_subset: &TileSubsetSpec,
    prf: &BlurDownscaleZkProof,
) -> Result<(), SensoryRoiError> {
    prf.validate_canonical()?;
    verify_frame_header(cores, expected_pk, header)?;
    let num_tiles = header.num_tiles()?;
    let tile_len = header.tile_len as usize;
    let sh = RawPcsShape::for_frame(num_tiles, tile_len)?;
    let _ = blur_subset.validate(num_tiles)?;

    if prf.blurred_pixels.len() != num_tiles {
        return Err(SensoryRoiError::InvalidBlurPublicArray(
            "blurred_pixels.len() != num_tiles",
        ));
    }
    // Enforce zero in non-blurred slots so unverified metadata cannot be smuggled in `blurred_pixels`.
    let mask_tbl = blur_subset.indicator_table(num_tiles, sh.n_tiles_pow2);
    for t in 0..num_tiles {
        if mask_tbl[t] == 0 && prf.blurred_pixels[t] != 0 {
            return Err(SensoryRoiError::InvalidBlurPublicArray(
                "non-zero blurred_pixels entry outside blur_subset",
            ));
        }
    }
    if prf.rest_rounds.len() != sh.m_t - 1 || prf.hat_v_bits.len() != sh.m_u {
        return Err(SensoryRoiError::MalformedWireProof("blur round/bit count mismatch"));
    }

    let mut tr = FsTranscript::new(CUST_PROTO_BLUR);
    tr.absorb_bytes(b"hdr", &header.signing_payload());
    tr.absorb_bytes(b"pcs_sh", &sh.tag_bytes());
    tr.absorb_bytes(b"subset", &blur_subset.canonical_bytes());
    tr.absorb_bytes(b"blur_px", &prf.blurred_pixels);
    tr.absorb_root(b"rt_aux", &prf.rt_aux);
    tr.absorb_ext4(b"gmask_sum", prf.gmask_sum);

    let tau: Vec<Ext4> = (0..sh.m_t)
        .map(|_| tr.squeeze_ext4(b"blr_tau", true))
        .collect();
    let alpha_batch = tr.squeeze_ext4(b"blr_alpha", true);
    let rho = tr.squeeze_ext4(b"blr_rho", true);

    // Round 0 check (`claim_0 = 0 + rho * gmask_sum`).
    let mut running = rho.mul(prf.gmask_sum);
    let p0_0 = prf.round0_poly[0];
    let p0_1 = prf
        .round0_poly
        .iter()
        .fold(Ext4::ZERO, |acc, &c| acc.add(c));
    if p0_0.add(p0_1) != running {
        return Err(SensoryRoiError::SumcheckRoundFailed {
            stage: "blur_sc",
            round: 0,
        });
    }
    tr.absorb_ext4_slice(b"blr_rd0", &prf.round0_poly);
    let r0 = tr.squeeze_non_binary_ext4(b"blr_r0");
    running = eval_poly_ext4(&prf.round0_poly, r0);

    let mut r_t = Vec::with_capacity(sh.m_t);
    r_t.push(r0);
    for (idx, poly) in prf.rest_rounds.iter().enumerate() {
        let p0 = poly[0];
        let p1 = poly[0].add(poly[1]).add(poly[2]).add(poly[3]);
        if p0.add(p1) != running {
            return Err(SensoryRoiError::SumcheckRoundFailed {
                stage: "blur_sc",
                round: idx + 1,
            });
        }
        tr.absorb_ext4_slice(b"blr_rd", poly);
        let ri = tr.squeeze_ext4(b"blr_ri", true);
        r_t.push(ri);
        running = eval_poly_ext4(poly, ri);
    }

    tr.absorb_ext4(b"blr_hv_raw", prf.hat_v_raw);
    tr.absorb_ext4_slice(b"blr_hv_bits", &prf.hat_v_bits);

    // Compute exact required `v_g = g(r_t)` from terminal sumcheck identity!
    let eq_val = eq_mle_ext4(&tau, &r_t);
    let m_val = blur_subset.eval_mle(num_tiles, &r_t);
    let b_val = eval_public_blur_mle(&prf.blurred_pixels, &r_t);
    let mut rem_val = Ext4::ZERO;
    let mut bool_val = Ext4::ZERO;
    let mut ap = alpha_batch;
    for (k, &bk) in prf.hat_v_bits.iter().enumerate() {
        rem_val = rem_val.add(bk.scale_bb(1u32 << k));
        bool_val = bool_val.add(ap.mul(bk.mul(Ext4::ONE.sub(bk))));
        ap = ap.mul(alpha_batch);
    }
    let tile_len_u32 = tile_len as u32;
    let diff = prf
        .hat_v_raw
        .scale_bb(tile_len_u32)
        .sub(b_val.scale_bb(tile_len_u32))
        .sub(rem_val);
    let q_val = eq_val.mul(m_val.mul(diff).add(bool_val));
    let rho_inv = rho.inv().ok_or(SensoryRoiError::SumcheckTerminalFailed("zero rho"))?;
    let v_g = running.sub(q_val).mul(rho_inv);

    // Batch `K = 3` linear claims (`U_raw`, `U_bits`, `G_poly`).
    let beta_bits: Vec<Ext4> = (0..sh.m_u)
        .map(|_| tr.squeeze_ext4(b"blr_bb", true))
        .collect();
    let beta_gsum = tr.squeeze_ext4(b"blr_bgs", true);
    let beta_geval = tr.squeeze_ext4(b"blr_bge", true);

    let z_full = build_raw_half_point(sh, &r_t);
    let raw_row_eq = build_eq_table_lsb_ext4(&z_full[sh.m_c..]);

    let mut z_bits_col = Vec::with_capacity(sh.m_c);
    let lo_bits = sh.m_t.min(sh.m_c);
    z_bits_col.extend_from_slice(&r_t[..lo_bits]);
    while z_bits_col.len() < sh.m_c {
        z_bits_col.push(Ext4::ZERO);
    }
    let eq_bits_hi = if sh.m_t > sh.m_c {
        build_eq_table_lsb_ext4(&r_t[sh.m_c..])
    } else {
        vec![Ext4::ONE]
    };
    let mut bit_row_weights = Vec::with_capacity(sh.m_u * sh.r_bit);
    for k in 0..sh.m_u {
        for rb in 0..sh.r_bit {
            bit_row_weights.push(beta_bits[k].mul(eq_bits_hi[rb]));
        }
    }

    let mut round_degs = vec![3usize; sh.m_t];
    round_degs[0] = 5;
    let (w_gsum, w_geval) = MixedGMaskExt4::build_weights(&round_degs, &r_t);
    let n_g = w_gsum.len();
    let delta0 = r0.mul(Ext4::ONE.sub(r0));
    let mut w_g_sparse = Vec::with_capacity(n_g + 1 + sh.m_u);
    for u in 0..n_g {
        w_g_sparse.push(beta_gsum.mul(w_gsum[u]).add(beta_geval.mul(w_geval[u])));
    }
    w_g_sparse.push(delta0);
    for k in 0..sh.m_u {
        w_g_sparse.push(beta_bits[k].mul(delta0));
    }

    let mut y_batch = prf
        .hat_v_raw
        .add(beta_gsum.mul(prf.gmask_sum))
        .add(beta_geval.mul(v_g));
    for k in 0..sh.m_u {
        y_batch = y_batch.add(beta_bits[k].mul(prf.hat_v_bits[k]));
    }

    let v_specs = [
        VerifierQSpec::RawRows {
            z_col: &z_full[..sh.m_c],
            scale: Ext4::ONE,
            row_eq: &raw_row_eq,
        },
        VerifierQSpec::AuxBbRows {
            z_col: &z_bits_col,
            row_weights: &bit_row_weights,
        },
        VerifierQSpec::AuxExt0Sparse {
            sparse_weights: &w_g_sparse,
        },
    ];
    verify_zk_basefold_opening(
        cores,
        &header.ctx.encode(),
        sh,
        &header.rt_raw,
        &prf.rt_aux,
        sh.m_u * sh.r_bit,
        &v_specs,
        y_batch,
        &prf.pcs_opening,
        &mut tr,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk_salt(tag: u8, idx: usize) -> Salt256 {
        let mut s = [0u8; 32];
        s[0] = tag;
        s[1..9].copy_from_slice(&(idx as u64).to_le_bytes());
        s
    }

    #[test]
    fn ext4_field_and_newton_interpolation_exact() {
        let mut rng = CShakeRng::from_seed(b"TEST-EXT4", &[7u8; 32]);
        for _ in 0..32 {
            let a = rng.next_ext4();
            let b = rng.next_ext4();
            let inv_a = a.inv().expect("nonzero ext4 invertible");
            assert_eq!(a.mul(inv_a), Ext4::ONE);
            assert_eq!(a.mul(b), b.mul(a));
        }
        // Degree-5 exact Newton interpolation roundtrip
        let coeffs: Vec<Ext4> = (0..6).map(|_| rng.next_ext4()).collect();
        let vals: Vec<Ext4> = (0u32..6)
            .map(|x| eval_poly_ext4(&coeffs, Ext4::from_bb(x)))
            .collect();
        assert_eq!(interpolate_monomial_0_to_d(&vals), coeffs);
    }

    #[test]
    fn roundtrip_roi_blur_zk_and_ambient_zk() {
        let cores = CachedCshakeCores::new();
        let sk = EnclaveSigningKey::from_wots_seed(vec![0x42u8; 32]);
        let pk = sk.public_key();
        let ctx = FrameContext {
            sensor_id: 7,
            frame_seq: 1,
            timestamp_ns: 1_000_000,
        };
        let tiles: Vec<RawSensorTile> = (0..4)
            .map(|i| RawSensorTile {
                pixels: (0..256).map(|k| ((20 + i * 30 + k) % 256) as u8).collect(),
                raw_salt: mk_salt(1, i),
            })
            .collect();
        let frame = seal_sensor_frame(
            &cores,
            &sk,
            ctx,
            2,
            2,
            2,
            SensorModality::Csi2Tile16x16,
            tiles,
            &[0x11u8; 32],
        )
        .expect("seal ok");

        // 1. ROI reveal verified with ONLY public key
        let roi = frame.open_roi_cert(&[0, 3]);
        verify_roi_reveal_cert(&cores, &pk, &frame.header, &roi).expect("roi verify ok");

        // 2. BlurDownscaleZkProof on non-ROI tiles [1, 2]
        let raw_flat = frame.raw_pixels_flat();
        let blur_sub = TileSubsetSpec::ExcludeRoi(vec![0, 3]);
        let blur_prf = prove_blur_downscale_zk(
            &cores,
            &frame.header,
            &frame.raw_pcs,
            &raw_flat,
            &blur_sub,
            &[0x22u8; 32],
        )
        .expect("blur prove ok");
        verify_blur_downscale_zk(&cores, &pk, &frame.header, &blur_sub, &blur_prf)
            .expect("blur verify ok");
        let bw = blur_prf.to_wire_bytes();
        let blur_rt = BlurDownscaleZkProof::from_wire_bytes(&bw).expect("blur wire rt");
        assert_eq!(blur_rt, blur_prf);

        // 3. AmbientEnvelopeZkProof on same sensor-signed rt_raw (ZERO per-tile sums!)
        let amb_prf = prove_ambient_envelope_zk(
            &cores,
            &frame.header,
            &frame.raw_pcs,
            &raw_flat,
            &blur_sub,
            200_000,
            &[0x33u8; 32],
        )
        .expect("ambient prove ok");
        verify_ambient_envelope_zk(&cores, &pk, &frame.header, &blur_sub, 200_000, &amb_prf)
            .expect("ambient verify ok");
        let aw = amb_prf.to_wire_bytes();
        let amb_rt = AmbientEnvelopeZkProof::from_wire_bytes(&aw).expect("ambient wire rt");
        assert_eq!(amb_rt, amb_prf);
    }
}
