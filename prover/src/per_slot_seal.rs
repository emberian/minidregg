//! Per-slot hybrid `X25519 + ML-KEM-768` key confinement (`CAP-21` fix) and statement-pinned
//! keyless sealed-`Hyperdocument` ciphertext-to-`saltedPatchRoot` weld (`G7`, `L8`, `F4`).
//!
//! Mirrors the kernel-verified Lean 4.35.0 formalization in
//! `Assurance/PerSlotKeyConfinement.lean` bit-for-bit:
//! - Pure-Rust constant-time RFC 7748 `X25519` (zero external crates beyond `sha3`),
//! - Pure-Rust FIPS 203 `ML-KEM-768` (`k=3, n=256, q=3329, eta1=2, eta2=2, du=10, dv=4`,
//!   `ek=1184B, dk=2400B, ct=1088B, ss=32B`) with constant-time FO implicit rejection,
//! - Per-slot `cSHAKE256` secret derivation & `AttenuatedSlotCap` envelopes that NEVER carry
//!   the root `ViewKey` (`CAP-21`),
//! - Statement-pinned `key_commit_i = cSHAKE256("SLOT_KEY_COMMIT", u64LE(i) || slot_secret(i))`
//!   (`L8`) and keyless `Tower256` blinded-XOR + Merkle/sponge `PublicCiphertextWeld` (`F4`)
//!   rejecting forged/unsealed ciphertexts (`PerSlotError::CiphertextRootMismatch`) without
//!   ever learning `slot_secret(i)` or plaintext bytes.

use std::fmt;
use std::hash::Hash;

use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Digest as Sha3DigestTrait, Sha3_256, Sha3_512, Shake128, Shake256,
};

use crate::binary_tower_256::Tower256;
use crate::grammar_capability::{
    fast_salted_content_commit, verify_sealed_hyperdoc_patch, GateRejection,
    SealedHyperdocPatchStmt, SealedHyperdocPatchWitness,
};
use crate::hash_kernels::cshake256_xof;
use crate::tower256_private_cert::{pack_salted_leaf, Digest, Salt248};

// ============================================================================
// §1. Errors, Constant-Time Helpers, & Domain-Separated Customizations
// ============================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PerSlotError {
    LowOrderX25519Point,
    InvalidMlkemKey(&'static str),
    InvalidMlkemCiphertext,
    SlotNotAuthorized(u64),
    AmplificationRefused(u64),
    WrapTagMismatch,
    KeyCommitMismatch,
    LegacyRootKeyCopyForbidden,
    CiphertextRootMismatch(&'static str),
    AeadTagMismatch,
    BaseGateRejected(GateRejection),
}

impl fmt::Display for PerSlotError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LowOrderX25519Point => write!(f, "low-order X25519 public key (all-zero DH)"),
            Self::InvalidMlkemKey(m) => write!(f, "invalid ML-KEM-768 key: {m}"),
            Self::InvalidMlkemCiphertext => write!(f, "invalid ML-KEM-768 ciphertext"),
            Self::SlotNotAuthorized(s) => write!(f, "slot {s} not authorized in AttenuatedSlotCap"),
            Self::AmplificationRefused(s) => write!(f, "attenuation refused: slot {s} not held"),
            Self::WrapTagMismatch => write!(f, "hybrid slot-key wrap MAC tag mismatch"),
            Self::KeyCommitMismatch => write!(f, "slot secret does not match pinned key_commit"),
            Self::LegacyRootKeyCopyForbidden => {
                write!(f, "CAP-21 refused: legacy ReadCap carries raw root ViewKey")
            }
            Self::CiphertextRootMismatch(m) => write!(f, "CiphertextRootMismatch: {m}"),
            Self::AeadTagMismatch => write!(f, "slot AEAD authentication tag mismatch"),
            Self::BaseGateRejected(e) => write!(f, "base sealed hyperdoc gate rejected: {e:?}"),
        }
    }
}

impl std::error::Error for PerSlotError {}

#[inline]
fn ct_eq_bytes(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut diff = 0u8;
    for (&x, &y) in a.iter().zip(b.iter()) {
        diff |= x ^ y;
    }
    diff == 0
}

#[inline]
fn ct_is_all_zero(a: &[u8]) -> bool {
    let mut acc = 0u8;
    for &x in a {
        acc |= x;
    }
    acc == 0
}

#[inline]
fn xor_digest(a: &Digest, b: &Digest) -> Digest {
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = a[i] ^ b[i];
    }
    out
}

fn cshake32(cust: &[u8], input: &[u8]) -> Digest {
    cshake256_xof(cust, input, 32)
        .try_into()
        .expect("32-byte digest")
}

fn sha3_256_bytes(data: &[u8]) -> Digest {
    let mut h = Sha3_256::new();
    Sha3DigestTrait::update(&mut h, data);
    h.finalize().into()
}

fn sha3_512_bytes(a: &[u8], b: &[u8]) -> [u8; 64] {
    let mut h = Sha3_512::new();
    Sha3DigestTrait::update(&mut h, a);
    Sha3DigestTrait::update(&mut h, b);
    h.finalize().into()
}

const SLOT_SECRET_CUST: &[u8] = b"\x0CMINIDREGG/PERSLOT/SLOT_SECRET/V1";
const SLOT_KEY_COMMIT_CUST: &[u8] = b"SLOT_KEY_COMMIT";
const HYBRID_WRAP_KDF_CUST: &[u8] = b"\x0DMINIDREGG/PERSLOT/X25519_MLKEM768_WRAP_KDF/V1";
const HYBRID_WRAP_TAG_CUST: &[u8] = b"\x0EMINIDREGG/PERSLOT/X25519_MLKEM768_WRAP_TAG/V1";
const SLOT_AAD_CUST: &[u8] = b"\x0FMINIDREGG/PERSLOT/SEALED_PATCH_AAD/V1";
const PUBLIC_WELD_CUST: &[u8] = b"\x10MINIDREGG/PERSLOT/KEYLESS_CT_ROOT_WELD/V1";
const WELD_CHALLENGE_CUST: &[u8] = b"\x11MINIDREGG/PERSLOT/WELD_CHALLENGE/V1";
const BLIND_PAD_CUST: &[u8] = b"\x12MINIDREGG/PERSLOT/BLIND_PAD_COMMIT/V1";
const SLOT_STREAM_CUST: &[u8] = b"\x13MINIDREGG/PERSLOT/AEAD_STREAM/V1";
const SLOT_SALTS_CUST: &[u8] = b"\x14MINIDREGG/PERSLOT/AEAD_SALTS/V1";
const SLOT_AEAD_TAG_CUST: &[u8] = b"\x15MINIDREGG/PERSLOT/AEAD_TAG/V1";

// ============================================================================
// §2. Constant-Time Pure-Rust RFC 7748 X25519
// ============================================================================

type Fe25519 = [i64; 16];

const FE_ZERO: Fe25519 = [0; 16];
const FE_ONE: Fe25519 = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
const FE_121665: Fe25519 = [0xDB41, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];

fn fe_carry(o: &mut Fe25519) {
    for i in 0..16 {
        o[i] += 1i64 << 16;
        let c = o[i] >> 16;
        if i < 15 {
            o[i + 1] += c - 1;
        } else {
            o[0] += (c - 1) * 38;
        }
        o[i] -= c << 16;
    }
}

fn fe_cswap(p: &mut Fe25519, q: &mut Fe25519, b: u8) {
    let mask = !((b as i64).wrapping_sub(1));
    for i in 0..16 {
        let t = mask & (p[i] ^ q[i]);
        p[i] ^= t;
        q[i] ^= t;
    }
}

fn fe_from_bytes(s: &[u8; 32]) -> Fe25519 {
    let mut o = [0i64; 16];
    for i in 0..16 {
        o[i] = (s[2 * i] as i64) + ((s[2 * i + 1] as i64) << 8);
    }
    o[15] &= 0x7FFF;
    o
}

fn fe_to_bytes(n: &Fe25519) -> [u8; 32] {
    let mut t = *n;
    fe_carry(&mut t);
    fe_carry(&mut t);
    fe_carry(&mut t);
    let mut m = [0i64; 16];
    for _ in 0..2 {
        m[0] = t[0] - 0xFFED;
        for i in 1..15 {
            m[i] = t[i] - 0xFFFF - ((m[i - 1] >> 16) & 1);
            m[i - 1] &= 0xFFFF;
        }
        m[15] = t[15] - 0x7FFF - ((m[14] >> 16) & 1);
        let b = ((m[15] >> 16) & 1) as u8;
        m[14] &= 0xFFFF;
        fe_cswap(&mut t, &mut m, 1 - b);
    }
    let mut out = [0u8; 32];
    for i in 0..16 {
        out[2 * i] = (t[i] & 0xFF) as u8;
        out[2 * i + 1] = ((t[i] >> 8) & 0xFF) as u8;
    }
    out
}

fn fe_add(a: &Fe25519, b: &Fe25519) -> Fe25519 {
    let mut o = [0i64; 16];
    for i in 0..16 {
        o[i] = a[i] + b[i];
    }
    o
}

fn fe_sub(a: &Fe25519, b: &Fe25519) -> Fe25519 {
    let mut o = [0i64; 16];
    for i in 0..16 {
        o[i] = a[i] - b[i];
    }
    o
}

fn fe_mul(a: &Fe25519, b: &Fe25519) -> Fe25519 {
    let mut t = [0i64; 31];
    for i in 0..16 {
        for j in 0..16 {
            t[i + j] += a[i] * b[j];
        }
    }
    for i in 0..15 {
        t[i] += 38 * t[i + 16];
    }
    let mut o = [0i64; 16];
    o.copy_from_slice(&t[..16]);
    fe_carry(&mut o);
    fe_carry(&mut o);
    o
}

fn fe_sq(a: &Fe25519) -> Fe25519 {
    fe_mul(a, a)
}

fn fe_inv(i: &Fe25519) -> Fe25519 {
    let mut c = *i;
    for a in (0..=253).rev() {
        c = fe_sq(&c);
        if a != 2 && a != 4 {
            c = fe_mul(&c, i);
        }
    }
    c
}

/// RFC 7748 X25519 scalar multiplication `X25519(k, u)`.
pub fn x25519_scalar_mult(scalar: &[u8; 32], u_coord: &[u8; 32]) -> [u8; 32] {
    let mut z = *scalar;
    z[0] &= 248;
    z[31] &= 127;
    z[31] |= 64;

    let x = fe_from_bytes(u_coord);
    let mut a = FE_ONE;
    let mut b = x;
    let mut c = FE_ZERO;
    let mut d = FE_ONE;

    for i in (0..=254).rev() {
        let r = (z[i >> 3] >> (i & 7)) & 1;
        fe_cswap(&mut a, &mut b, r);
        fe_cswap(&mut c, &mut d, r);
        let e = fe_add(&a, &c);
        let a2 = fe_sub(&a, &c);
        let c2 = fe_add(&b, &d);
        let b2 = fe_sub(&b, &d);
        let d2 = fe_sq(&e);
        let f = fe_sq(&a2);
        let a3 = fe_mul(&c2, &a2);
        let c3 = fe_mul(&b2, &e);
        let e2 = fe_add(&a3, &c3);
        let a4 = fe_sub(&a3, &c3);
        let b3 = fe_sq(&a4);
        let c4 = fe_sub(&d2, &f);
        let a5 = fe_mul(&c4, &FE_121665);
        let a6 = fe_add(&a5, &d2);
        c = fe_mul(&c4, &a6);
        a = fe_mul(&d2, &f);
        d = fe_mul(&b3, &x);
        b = fe_sq(&e2);
        fe_cswap(&mut a, &mut b, r);
        fe_cswap(&mut c, &mut d, r);
    }

    let inv_c = fe_inv(&c);
    let res = fe_mul(&a, &inv_c);
    fe_to_bytes(&res)
}

/// RFC 7748 X25519 public key from 32-byte secret scalar (`X25519(sk, 9)`).
pub fn x25519_public_key(secret: &[u8; 32]) -> [u8; 32] {
    let mut base = [0u8; 32];
    base[0] = 9;
    x25519_scalar_mult(secret, &base)
}

/// Checked X25519 DH rejecting low-order public keys (all-zero output).
pub fn x25519_dh_checked(secret: &[u8; 32], peer_pk: &[u8; 32]) -> Result<[u8; 32], PerSlotError> {
    let ss = x25519_scalar_mult(secret, peer_pk);
    if ct_is_all_zero(&ss) {
        return Err(PerSlotError::LowOrderX25519Point);
    }
    Ok(ss)
}

// ============================================================================
// §3. Pure-Rust FIPS 203 ML-KEM-768 (`k=3, n=256, q=3329, du=10, dv=4`)
// ============================================================================

pub const MLKEM768_K: usize = 3;
pub const MLKEM768_EK_BYTES: usize = 1184;
pub const MLKEM768_DK_BYTES: usize = 2400;
pub const MLKEM768_CT_BYTES: usize = 1088;
const MLKEM_Q: i32 = 3329;
const MLKEM_N: usize = 256;
const MLKEM_INV128: i32 = 3303; // 128 * 3303 = 1 (mod 3329)

type Poly = [i32; MLKEM_N];
type PolyVec = [Poly; MLKEM768_K];

const fn bitrev7(x: usize) -> usize {
    ((x & 1) << 6)
        | ((x & 2) << 4)
        | ((x & 4) << 2)
        | (x & 8)
        | ((x & 16) >> 2)
        | ((x & 32) >> 4)
        | ((x & 64) >> 6)
}

const fn pow_mod_q(mut base: i32, mut exp: usize) -> i32 {
    let mut acc = 1i32;
    while exp > 0 {
        if (exp & 1) != 0 {
            acc = (acc * base) % MLKEM_Q;
        }
        base = (base * base) % MLKEM_Q;
        exp >>= 1;
    }
    acc
}

const fn compute_ntt_zetas() -> [i32; 128] {
    let mut out = [0i32; 128];
    let mut i = 0;
    while i < 128 {
        out[i] = pow_mod_q(17, bitrev7(i));
        i += 1;
    }
    out
}

const fn compute_base_gammas() -> [i32; 128] {
    let mut out = [0i32; 128];
    let mut i = 0;
    while i < 128 {
        out[i] = pow_mod_q(17, 2 * bitrev7(i) + 1);
        i += 1;
    }
    out
}

const NTT_ZETAS: [i32; 128] = compute_ntt_zetas();
const BASE_GAMMAS: [i32; 128] = compute_base_gammas();

#[inline]
fn mod_q(x: i32) -> i32 {
    let r = x % MLKEM_Q;
    if r < 0 {
        r + MLKEM_Q
    } else {
        r
    }
}

fn poly_add(a: &Poly, b: &Poly) -> Poly {
    let mut out = [0i32; MLKEM_N];
    for i in 0..MLKEM_N {
        out[i] = mod_q(a[i] + b[i]);
    }
    out
}

fn poly_sub(a: &Poly, b: &Poly) -> Poly {
    let mut out = [0i32; MLKEM_N];
    for i in 0..MLKEM_N {
        out[i] = mod_q(a[i] + MLKEM_Q - b[i]);
    }
    out
}

fn poly_ntt(f: &mut Poly) {
    let mut len = 128usize;
    let mut i = 1usize;
    while len >= 2 {
        let mut start = 0usize;
        while start < MLKEM_N {
            let zeta = NTT_ZETAS[i];
            i += 1;
            for j in start..(start + len) {
                let t = (zeta * f[j + len]) % MLKEM_Q;
                f[j + len] = mod_q(f[j] + MLKEM_Q - t);
                f[j] = mod_q(f[j] + t);
            }
            start += 2 * len;
        }
        len /= 2;
    }
}

fn poly_inv_ntt(f: &mut Poly) {
    let mut len = 2usize;
    let mut i = 127usize;
    while len <= 128 {
        let mut start = 0usize;
        while start < MLKEM_N {
            let zeta = NTT_ZETAS[i];
            i = i.saturating_sub(1);
            for j in start..(start + len) {
                let t = f[j];
                f[j] = mod_q(t + f[j + len]);
                f[j + len] = (zeta * mod_q(f[j + len] + MLKEM_Q - t)) % MLKEM_Q;
            }
            start += 2 * len;
        }
        len *= 2;
    }
    for coeff in f.iter_mut() {
        *coeff = (*coeff * MLKEM_INV128) % MLKEM_Q;
    }
}

fn poly_mul_ntt(a: &Poly, b: &Poly) -> Poly {
    let mut c = [0i32; MLKEM_N];
    for i in 0..128 {
        let gamma = BASE_GAMMAS[i];
        let a0 = a[2 * i];
        let a1 = a[2 * i + 1];
        let b0 = b[2 * i];
        let b1 = b[2 * i + 1];
        let p = (a1 * b1) % MLKEM_Q;
        c[2 * i] = mod_q(a0 * b0 + p * gamma);
        c[2 * i + 1] = mod_q(a0 * b1 + a1 * b0);
    }
    c
}

fn sample_ntt(rho: &[u8; 32], j_byte: u8, i_byte: u8) -> Poly {
    let mut xof = Shake128::default();
    xof.update(rho);
    xof.update(&[j_byte, i_byte]);
    let mut reader = xof.finalize_xof();
    let mut poly = [0i32; MLKEM_N];
    let mut idx = 0usize;
    let mut buf = [0u8; 3];
    while idx < MLKEM_N {
        reader.read(&mut buf);
        let d1 = (buf[0] as i32) | (((buf[1] & 0x0F) as i32) << 8);
        let d2 = ((buf[1] >> 4) as i32) | ((buf[2] as i32) << 4);
        if d1 < MLKEM_Q {
            poly[idx] = d1;
            idx += 1;
        }
        if d2 < MLKEM_Q && idx < MLKEM_N {
            poly[idx] = d2;
            idx += 1;
        }
    }
    poly
}

/// FIPS 203 `SamplePolyCBD_2` (`eta = 2`, 128 PRF bytes).
fn sample_cbd2(sigma: &[u8; 32], nonce: u8) -> Poly {
    let mut xof = Shake256::default();
    xof.update(sigma);
    xof.update(&[nonce]);
    let mut reader = xof.finalize_xof();
    let mut bytes = [0u8; 128];
    reader.read(&mut bytes);
    let mut poly = [0i32; MLKEM_N];
    for i in 0..MLKEM_N {
        let bit_base = 4 * i;
        let bit = |k: usize| -> i32 { ((bytes[k >> 3] >> (k & 7)) & 1) as i32 };
        let x = bit(bit_base) + bit(bit_base + 1);
        let y = bit(bit_base + 2) + bit(bit_base + 3);
        poly[i] = mod_q(x - y);
    }
    poly
}

#[inline]
fn compress_d(x: i32, d: u32) -> u32 {
    let num = ((mod_q(x) as u64) << (d + 1)) + (MLKEM_Q as u64);
    let q2 = (2 * MLKEM_Q) as u64;
    ((num / q2) as u32) & ((1u32 << d) - 1)
}

#[inline]
fn decompress_d(y: u32, d: u32) -> i32 {
    (((y as u64) * (MLKEM_Q as u64) + (1u64 << (d - 1))) >> d) as i32
}

fn byte_encode(coeffs: &[u32; MLKEM_N], d: usize) -> Vec<u8> {
    let mut out = vec![0u8; 32 * d];
    for (i, &c) in coeffs.iter().enumerate() {
        for b in 0..d {
            if ((c >> b) & 1) != 0 {
                let bit_pos = i * d + b;
                out[bit_pos >> 3] |= 1u8 << (bit_pos & 7);
            }
        }
    }
    out
}

fn byte_decode(bytes: &[u8], d: usize) -> [u32; MLKEM_N] {
    let mut out = [0u32; MLKEM_N];
    for i in 0..MLKEM_N {
        let mut v = 0u32;
        for b in 0..d {
            let bit_pos = i * d + b;
            let bit = ((bytes[bit_pos >> 3] >> (bit_pos & 7)) & 1) as u32;
            v |= bit << b;
        }
        out[i] = v;
    }
    out
}

fn encode_poly12(p: &Poly) -> Vec<u8> {
    let mut c = [0u32; MLKEM_N];
    for i in 0..MLKEM_N {
        c[i] = mod_q(p[i]) as u32;
    }
    byte_encode(&c, 12)
}

fn decode_poly12_checked(bytes: &[u8]) -> Result<Poly, PerSlotError> {
    if bytes.len() != 384 {
        return Err(PerSlotError::InvalidMlkemKey("bad poly12 length"));
    }
    let raw = byte_decode(bytes, 12);
    let mut p = [0i32; MLKEM_N];
    for i in 0..MLKEM_N {
        if raw[i] >= MLKEM_Q as u32 {
            return Err(PerSlotError::InvalidMlkemKey("non-canonical coefficient >= 3329"));
        }
        p[i] = raw[i] as i32;
    }
    Ok(p)
}

fn kpke_keygen(d_seed: &[u8; 32]) -> (Vec<u8>, Vec<u8>) {
    let g = sha3_512_bytes(d_seed, &[MLKEM768_K as u8]);
    let rho: [u8; 32] = g[0..32].try_into().unwrap();
    let sigma: [u8; 32] = g[32..64].try_into().unwrap();

    let mut a_hat = [[[0i32; MLKEM_N]; MLKEM768_K]; MLKEM768_K];
    for i in 0..MLKEM768_K {
        for j in 0..MLKEM768_K {
            a_hat[i][j] = sample_ntt(&rho, j as u8, i as u8);
        }
    }
    let mut s_hat: PolyVec = [[0; MLKEM_N]; MLKEM768_K];
    let mut e_hat: PolyVec = [[0; MLKEM_N]; MLKEM768_K];
    let mut n = 0u8;
    for i in 0..MLKEM768_K {
        s_hat[i] = sample_cbd2(&sigma, n);
        poly_ntt(&mut s_hat[i]);
        n += 1;
    }
    for i in 0..MLKEM768_K {
        e_hat[i] = sample_cbd2(&sigma, n);
        poly_ntt(&mut e_hat[i]);
        n += 1;
    }

    let mut t_hat: PolyVec = [[0; MLKEM_N]; MLKEM768_K];
    for i in 0..MLKEM768_K {
        let mut acc = e_hat[i];
        for j in 0..MLKEM768_K {
            let prod = poly_mul_ntt(&a_hat[i][j], &s_hat[j]);
            acc = poly_add(&acc, &prod);
        }
        t_hat[i] = acc;
    }

    let mut ek_pke = Vec::with_capacity(MLKEM768_EK_BYTES);
    let mut dk_pke = Vec::with_capacity(384 * MLKEM768_K);
    for i in 0..MLKEM768_K {
        ek_pke.extend_from_slice(&encode_poly12(&t_hat[i]));
        dk_pke.extend_from_slice(&encode_poly12(&s_hat[i]));
    }
    ek_pke.extend_from_slice(&rho);
    (ek_pke, dk_pke)
}

fn kpke_encrypt(ek_pke: &[u8], msg: &[u8; 32], r_seed: &[u8; 32]) -> Result<Vec<u8>, PerSlotError> {
    if ek_pke.len() != MLKEM768_EK_BYTES {
        return Err(PerSlotError::InvalidMlkemKey("ek length != 1184"));
    }
    let mut t_hat: PolyVec = [[0; MLKEM_N]; MLKEM768_K];
    for i in 0..MLKEM768_K {
        t_hat[i] = decode_poly12_checked(&ek_pke[384 * i..384 * (i + 1)])?;
    }
    let rho: [u8; 32] = ek_pke[384 * MLKEM768_K..MLKEM768_EK_BYTES].try_into().unwrap();

    let mut a_hat = [[[0i32; MLKEM_N]; MLKEM768_K]; MLKEM768_K];
    for i in 0..MLKEM768_K {
        for j in 0..MLKEM768_K {
            a_hat[i][j] = sample_ntt(&rho, j as u8, i as u8);
        }
    }

    let mut y_hat: PolyVec = [[0; MLKEM_N]; MLKEM768_K];
    let mut e1: PolyVec = [[0; MLKEM_N]; MLKEM768_K];
    let mut n = 0u8;
    for i in 0..MLKEM768_K {
        y_hat[i] = sample_cbd2(r_seed, n);
        poly_ntt(&mut y_hat[i]);
        n += 1;
    }
    for i in 0..MLKEM768_K {
        e1[i] = sample_cbd2(r_seed, n);
        n += 1;
    }
    let e2 = sample_cbd2(r_seed, n);

    let mut u_vec: PolyVec = [[0; MLKEM_N]; MLKEM768_K];
    for i in 0..MLKEM768_K {
        let mut acc = [0i32; MLKEM_N];
        for j in 0..MLKEM768_K {
            let prod = poly_mul_ntt(&a_hat[j][i], &y_hat[j]);
            acc = poly_add(&acc, &prod);
        }
        poly_inv_ntt(&mut acc);
        u_vec[i] = poly_add(&acc, &e1[i]);
    }

    let msg_bits = byte_decode(msg, 1);
    let mut mu = [0i32; MLKEM_N];
    for i in 0..MLKEM_N {
        mu[i] = decompress_d(msg_bits[i], 1);
    }

    let mut v_acc = [0i32; MLKEM_N];
    for i in 0..MLKEM768_K {
        let prod = poly_mul_ntt(&t_hat[i], &y_hat[i]);
        v_acc = poly_add(&v_acc, &prod);
    }
    poly_inv_ntt(&mut v_acc);
    let v = poly_add(&poly_add(&v_acc, &e2), &mu);

    let mut ct = Vec::with_capacity(MLKEM768_CT_BYTES);
    for u_poly in &u_vec {
        let mut c1 = [0u32; MLKEM_N];
        for k in 0..MLKEM_N {
            c1[k] = compress_d(u_poly[k], 10);
        }
        ct.extend_from_slice(&byte_encode(&c1, 10));
    }
    let mut c2 = [0u32; MLKEM_N];
    for k in 0..MLKEM_N {
        c2[k] = compress_d(v[k], 4);
    }
    ct.extend_from_slice(&byte_encode(&c2, 4));
    Ok(ct)
}

fn kpke_decrypt(dk_pke: &[u8], ct: &[u8]) -> Result<[u8; 32], PerSlotError> {
    if ct.len() != MLKEM768_CT_BYTES {
        return Err(PerSlotError::InvalidMlkemCiphertext);
    }
    let mut u_hat: PolyVec = [[0; MLKEM_N]; MLKEM768_K];
    for i in 0..MLKEM768_K {
        let raw = byte_decode(&ct[320 * i..320 * (i + 1)], 10);
        for k in 0..MLKEM_N {
            u_hat[i][k] = decompress_d(raw[k], 10);
        }
        poly_ntt(&mut u_hat[i]);
    }
    let v_raw = byte_decode(&ct[320 * MLKEM768_K..MLKEM768_CT_BYTES], 4);
    let mut v = [0i32; MLKEM_N];
    for k in 0..MLKEM_N {
        v[k] = decompress_d(v_raw[k], 4);
    }
    let mut s_hat: PolyVec = [[0; MLKEM_N]; MLKEM768_K];
    for i in 0..MLKEM768_K {
        s_hat[i] = decode_poly12_checked(&dk_pke[384 * i..384 * (i + 1)])?;
    }
    let mut inner = [0i32; MLKEM_N];
    for i in 0..MLKEM768_K {
        let prod = poly_mul_ntt(&s_hat[i], &u_hat[i]);
        inner = poly_add(&inner, &prod);
    }
    poly_inv_ntt(&mut inner);
    let w = poly_sub(&v, &inner);
    let mut bits = [0u32; MLKEM_N];
    for k in 0..MLKEM_N {
        bits[k] = compress_d(w[k], 1);
    }
    let encoded = byte_encode(&bits, 1);
    Ok(encoded.try_into().expect("32-byte message"))
}

/// FIPS 203 `ML-KEM-768` encapsulation key (`1,184 B`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mlkem768EncapKey(pub Vec<u8>);

/// FIPS 203 `ML-KEM-768` decapsulation key (`2,400 B`).
#[derive(Clone, PartialEq, Eq)]
pub struct Mlkem768DecapKey(pub Vec<u8>);

impl fmt::Debug for Mlkem768DecapKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Mlkem768DecapKey(<redacted>)")
    }
}

/// FIPS 203 `ML-KEM-768` ciphertext (`1,088 B`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mlkem768Ciphertext(pub Vec<u8>);

/// FIPS 203 `ML-KEM.KeyGen_internal(d, z)` for `ML-KEM-768`.
pub fn mlkem768_keygen_internal(d: &[u8; 32], z: &[u8; 32]) -> (Mlkem768EncapKey, Mlkem768DecapKey) {
    let (ek_pke, dk_pke) = kpke_keygen(d);
    let h_ek = sha3_256_bytes(&ek_pke);
    let mut dk = Vec::with_capacity(MLKEM768_DK_BYTES);
    dk.extend_from_slice(&dk_pke);
    dk.extend_from_slice(&ek_pke);
    dk.extend_from_slice(&h_ek);
    dk.extend_from_slice(z);
    (Mlkem768EncapKey(ek_pke), Mlkem768DecapKey(dk))
}

/// FIPS 203 `ML-KEM.Encaps_internal(ek, m)` for `ML-KEM-768`.
pub fn mlkem768_encaps_internal(
    ek: &Mlkem768EncapKey,
    m: &[u8; 32],
) -> Result<(Mlkem768Ciphertext, Digest), PerSlotError> {
    if ek.0.len() != MLKEM768_EK_BYTES {
        return Err(PerSlotError::InvalidMlkemKey("ek length != 1184"));
    }
    let h_ek = sha3_256_bytes(&ek.0);
    let g = sha3_512_bytes(m, &h_ek);
    let k_ss: Digest = g[0..32].try_into().unwrap();
    let r_seed: [u8; 32] = g[32..64].try_into().unwrap();
    let ct = kpke_encrypt(&ek.0, m, &r_seed)?;
    Ok((Mlkem768Ciphertext(ct), k_ss))
}

/// FIPS 203 `ML-KEM.Decaps_internal(dk, c)` with constant-time implicit rejection (`J(z || c)`).
pub fn mlkem768_decaps_internal(
    dk: &Mlkem768DecapKey,
    ct: &Mlkem768Ciphertext,
) -> Result<Digest, PerSlotError> {
    if dk.0.len() != MLKEM768_DK_BYTES {
        return Err(PerSlotError::InvalidMlkemKey("dk length != 2400"));
    }
    if ct.0.len() != MLKEM768_CT_BYTES {
        return Err(PerSlotError::InvalidMlkemCiphertext);
    }
    let dk_pke = &dk.0[0..1152];
    let ek_pke = &dk.0[1152..2336];
    let h_ek = &dk.0[2336..2368];
    let z = &dk.0[2368..2400];

    let m_prime = kpke_decrypt(dk_pke, &ct.0)?;
    let g = sha3_512_bytes(&m_prime, h_ek);
    let k_prime: Digest = g[0..32].try_into().unwrap();
    let r_prime: [u8; 32] = g[32..64].try_into().unwrap();

    // Implicit rejection key `k_bar = SHAKE256(z || c, 32)`.
    let mut j = Shake256::default();
    j.update(z);
    j.update(&ct.0);
    let mut k_bar = [0u8; 32];
    j.finalize_xof().read(&mut k_bar);

    let c_prime = kpke_encrypt(ek_pke, &m_prime, &r_prime)?;
    let eq = ct_eq_bytes(&ct.0, &c_prime);
    let mask = if eq { 0xFFu8 } else { 0x00u8 };
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = (k_prime[i] & mask) | (k_bar[i] & !mask);
    }
    Ok(out)
}

// ============================================================================
// §4. Per-Slot Key Derivation & Hybrid `X25519 + ML-KEM-768` Confinement (`CAP-21`)
// ============================================================================

/// Derive per-slot secret `slot_secret(i)` from `root_view_key` (held ONLY by the root custodian!).
pub fn derive_slot_secret(
    root_view_key: &Digest,
    cell_id: u64,
    slot_idx: u64,
    key_epoch: u64,
) -> Digest {
    let mut input = Vec::with_capacity(32 + 24);
    input.extend_from_slice(root_view_key);
    input.extend_from_slice(&cell_id.to_le_bytes());
    input.extend_from_slice(&slot_idx.to_le_bytes());
    input.extend_from_slice(&key_epoch.to_le_bytes());
    cshake32(SLOT_SECRET_CUST, &input)
}

/// Public statement-pinned commitment to `slot_secret(i)`:
/// `key_commit_i = cSHAKE256("SLOT_KEY_COMMIT", u64LE(i) || slot_secret(i))`.
pub fn slot_key_commit(slot_idx: u64, slot_secret: &Digest) -> Digest {
    let mut input = Vec::with_capacity(8 + 32);
    input.extend_from_slice(&slot_idx.to_le_bytes());
    input.extend_from_slice(slot_secret);
    cshake32(SLOT_KEY_COMMIT_CUST, &input)
}

/// Hybrid `X25519 + ML-KEM-768` recipient public key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HybridPublicKey {
    pub x25519_pk: [u8; 32],
    pub mlkem768_ek: Mlkem768EncapKey,
    pub mlkem768_ek_digest: Digest,
}

impl HybridPublicKey {
    pub fn from_components(x25519_pk: [u8; 32], mlkem768_ek: Mlkem768EncapKey) -> Self {
        let mlkem768_ek_digest = sha3_256_bytes(&mlkem768_ek.0);
        Self {
            x25519_pk,
            mlkem768_ek,
            mlkem768_ek_digest,
        }
    }
}

/// Hybrid `X25519 + ML-KEM-768` recipient secret key.
#[derive(Clone)]
pub struct HybridSecretKey {
    pub x25519_sk: [u8; 32],
    pub mlkem768_dk: Mlkem768DecapKey,
    pub public: HybridPublicKey,
}

impl fmt::Debug for HybridSecretKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("HybridSecretKey")
            .field("public", &self.public)
            .field("secret", &"<redacted>")
            .finish()
    }
}

/// Deterministic hybrid `X25519 + ML-KEM-768` keygen from a 32-byte seed.
pub fn hybrid_keygen_from_seed(seed: &[u8; 32]) -> HybridSecretKey {
    let x25519_sk = cshake32(b"MINIDREGG/HYBRID_KEYGEN/X25519", seed);
    let mlkem_d = cshake32(b"MINIDREGG/HYBRID_KEYGEN/MLKEM_D", seed);
    let mlkem_z = cshake32(b"MINIDREGG/HYBRID_KEYGEN/MLKEM_Z", seed);
    let x25519_pk = x25519_public_key(&x25519_sk);
    let (ek, dk) = mlkem768_keygen_internal(&mlkem_d, &mlkem_z);
    let public = HybridPublicKey::from_components(x25519_pk, ek);
    HybridSecretKey {
        x25519_sk,
        mlkem768_dk: dk,
        public,
    }
}

/// Hybrid `X25519 + ML-KEM-768` KEM ciphertext (full 32B X25519 ephemeral pk + 1088B ML-KEM ct).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HybridKemCiphertext {
    pub x25519_eph_pk: [u8; 32],
    pub mlkem768_ct: Mlkem768Ciphertext,
    pub mlkem768_ct_digest: Digest,
}

/// Associated data binding a wrapped slot key to `(cell_id, slot_idx, key_epoch, key_commit)`.
pub fn wrap_slot_aad(cell_id: u64, slot_idx: u64, key_epoch: u64, key_commit: &Digest) -> Vec<u8> {
    let mut aad = Vec::with_capacity(24 + 32);
    aad.extend_from_slice(&cell_id.to_le_bytes());
    aad.extend_from_slice(&slot_idx.to_le_bytes());
    aad.extend_from_slice(&key_epoch.to_le_bytes());
    aad.extend_from_slice(key_commit);
    aad
}

/// Hybrid KEK combiner (`hybridWrapKek` in `Assurance/PerSlotKeyConfinement.lean`).
pub fn hybrid_wrap_kek(
    ss_x25519: &Digest,
    ss_mlkem: &Digest,
    x25519_eph_pk: &Digest,
    mlkem_ct_digest: &Digest,
    pk_x25519: &Digest,
    pk_mlkem_ek_digest: &Digest,
    aad: &[u8],
) -> Digest {
    let mut inp = Vec::with_capacity(6 * 32 + aad.len());
    inp.extend_from_slice(ss_x25519);
    inp.extend_from_slice(ss_mlkem);
    inp.extend_from_slice(x25519_eph_pk);
    inp.extend_from_slice(mlkem_ct_digest);
    inp.extend_from_slice(pk_x25519);
    inp.extend_from_slice(pk_mlkem_ek_digest);
    inp.extend_from_slice(aad);
    cshake32(HYBRID_WRAP_KDF_CUST, &inp)
}

/// Hybrid wrap authentication MAC (`hybridWrapTag` in Lean).
pub fn hybrid_wrap_tag(kek: &Digest, wrapped_secret: &Digest, aad: &[u8]) -> Digest {
    let mut inp = Vec::with_capacity(64 + aad.len());
    inp.extend_from_slice(kek);
    inp.extend_from_slice(wrapped_secret);
    inp.extend_from_slice(aad);
    cshake32(HYBRID_WRAP_TAG_CUST, &inp)
}

/// One wrapped per-slot secret entry inside an `AttenuatedSlotCap`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WrappedSlotKey {
    pub slot_index: u64,
    pub key_commit: Digest,
    pub kem_ct: HybridKemCiphertext,
    pub wrapped_secret: Digest,
    pub wrap_tag: Digest,
}

/// Wrap `slot_secret` to `delegate_pk` using real `X25519 + ML-KEM-768` encapsulation.
pub fn wrap_slot_secret_hybrid(
    cell_id: u64,
    slot_index: u64,
    key_epoch: u64,
    delegate_pk: &HybridPublicKey,
    slot_secret: &Digest,
    encaps_seed: &[u8; 32],
) -> Result<WrappedSlotKey, PerSlotError> {
    let eph_sk = cshake32(b"MINIDREGG/HYBRID_ENCAPS/X25519_EPH", encaps_seed);
    let mlkem_m = cshake32(b"MINIDREGG/HYBRID_ENCAPS/MLKEM_M", encaps_seed);
    let x25519_eph_pk = x25519_public_key(&eph_sk);
    let ss_x25519 = x25519_dh_checked(&eph_sk, &delegate_pk.x25519_pk)?;
    let (mlkem768_ct, ss_mlkem) = mlkem768_encaps_internal(&delegate_pk.mlkem768_ek, &mlkem_m)?;
    let mlkem768_ct_digest = sha3_256_bytes(&mlkem768_ct.0);

    let key_commit = slot_key_commit(slot_index, slot_secret);
    let aad = wrap_slot_aad(cell_id, slot_index, key_epoch, &key_commit);
    let kek = hybrid_wrap_kek(
        &ss_x25519,
        &ss_mlkem,
        &x25519_eph_pk,
        &mlkem768_ct_digest,
        &delegate_pk.x25519_pk,
        &delegate_pk.mlkem768_ek_digest,
        &aad,
    );
    let wrapped_secret = xor_digest(slot_secret, &kek);
    let wrap_tag = hybrid_wrap_tag(&kek, &wrapped_secret, &aad);

    Ok(WrappedSlotKey {
        slot_index,
        key_commit,
        kem_ct: HybridKemCiphertext {
            x25519_eph_pk,
            mlkem768_ct,
            mlkem768_ct_digest,
        },
        wrapped_secret,
        wrap_tag,
    })
}

/// Unwrap a `WrappedSlotKey` using `delegate_sk` (real `X25519 + ML-KEM-768` decapsulation,
/// constant-time MAC check, and `slot_key_commit` check).
pub fn unwrap_slot_secret_hybrid(
    cell_id: u64,
    key_epoch: u64,
    delegate_sk: &HybridSecretKey,
    entry: &WrappedSlotKey,
) -> Result<Digest, PerSlotError> {
    let ct_digest_actual = sha3_256_bytes(&entry.kem_ct.mlkem768_ct.0);
    if !ct_eq_bytes(&ct_digest_actual, &entry.kem_ct.mlkem768_ct_digest) {
        return Err(PerSlotError::InvalidMlkemCiphertext);
    }
    let ss_x25519 = x25519_dh_checked(&delegate_sk.x25519_sk, &entry.kem_ct.x25519_eph_pk)?;
    let ss_mlkem = mlkem768_decaps_internal(&delegate_sk.mlkem768_dk, &entry.kem_ct.mlkem768_ct)?;

    let aad = wrap_slot_aad(cell_id, entry.slot_index, key_epoch, &entry.key_commit);
    let kek = hybrid_wrap_kek(
        &ss_x25519,
        &ss_mlkem,
        &entry.kem_ct.x25519_eph_pk,
        &entry.kem_ct.mlkem768_ct_digest,
        &delegate_sk.public.x25519_pk,
        &delegate_sk.public.mlkem768_ek_digest,
        &aad,
    );
    let expected_tag = hybrid_wrap_tag(&kek, &entry.wrapped_secret, &aad);
    if !ct_eq_bytes(&entry.wrap_tag, &expected_tag) {
        return Err(PerSlotError::WrapTagMismatch);
    }
    let recovered = xor_digest(&entry.wrapped_secret, &kek);
    let recomputed_kc = slot_key_commit(entry.slot_index, &recovered);
    if !ct_eq_bytes(&recomputed_kc, &entry.key_commit) {
        return Err(PerSlotError::KeyCommitMismatch);
    }
    Ok(recovered)
}

/// **Per-Slot Attenuated Capability Envelope (`AttenuatedSlotCap`) — Kills `CAP-21`:**
/// carries **NO `root_view_key`**! Distributes ONLY hybrid-wrapped per-slot secrets for `granted_slots`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttenuatedSlotCap {
    pub cell_id: u64,
    pub key_epoch: u64,
    pub delegate_pk: HybridPublicKey,
    pub granted_slots: Vec<u64>,
    pub wrapped_keys: Vec<WrappedSlotKey>,
}

impl AttenuatedSlotCap {
    /// Mint an `AttenuatedSlotCap` from the root custodian's `root_view_key`, exposing ONLY
    /// wrapped per-slot secrets `{wrap(pk_delegate, slot_secret(i)) | i ∈ granted_slots}`.
    pub fn mint_from_root(
        root_view_key: &Digest,
        cell_id: u64,
        key_epoch: u64,
        delegate_pk: &HybridPublicKey,
        granted_slots: &[u64],
        encaps_nonce_seed: &[u8; 32],
    ) -> Result<Self, PerSlotError> {
        let mut wrapped_keys = Vec::with_capacity(granted_slots.len());
        for &slot in granted_slots {
            let slot_sec = derive_slot_secret(root_view_key, cell_id, slot, key_epoch);
            let mut seed_in = Vec::with_capacity(40);
            seed_in.extend_from_slice(encaps_nonce_seed);
            seed_in.extend_from_slice(&slot.to_le_bytes());
            let slot_seed = cshake32(b"MINIDREGG/PERSLOT/MINT_ENCAPS_SEED", &seed_in);
            wrapped_keys.push(wrap_slot_secret_hybrid(
                cell_id,
                slot,
                key_epoch,
                delegate_pk,
                &slot_sec,
                &slot_seed,
            )?);
        }
        Ok(Self {
            cell_id,
            key_epoch,
            delegate_pk: delegate_pk.clone(),
            granted_slots: granted_slots.to_vec(),
            wrapped_keys,
        })
    }

    pub fn lookup_wrapped(&self, slot_index: u64) -> Option<&WrappedSlotKey> {
        self.wrapped_keys.iter().find(|w| w.slot_index == slot_index)
    }

    /// Unwrap `slot_secret(slot_index)` iff `slot_index ∈ granted_slots`.
    pub fn unwrap_slot(
        &self,
        slot_index: u64,
        holder_sk: &HybridSecretKey,
    ) -> Result<Digest, PerSlotError> {
        if !self.granted_slots.contains(&slot_index) {
            return Err(PerSlotError::SlotNotAuthorized(slot_index));
        }
        let entry = self
            .lookup_wrapped(slot_index)
            .ok_or(PerSlotError::SlotNotAuthorized(slot_index))?;
        unwrap_slot_secret_hybrid(self.cell_id, self.key_epoch, holder_sk, entry)
    }

    /// Re-attenuate to `sub_slots ⊆ self.granted_slots` for `next_delegate_pk`:
    /// refuses amplification and omits every `j ∉ sub_slots`.
    pub fn attenuate(
        &self,
        holder_sk: &HybridSecretKey,
        next_delegate_pk: &HybridPublicKey,
        sub_slots: &[u64],
        re_encaps_seed: &[u8; 32],
    ) -> Result<Self, PerSlotError> {
        for &s in sub_slots {
            if !self.granted_slots.contains(&s) {
                return Err(PerSlotError::AmplificationRefused(s));
            }
        }
        let mut next_wrapped = Vec::with_capacity(sub_slots.len());
        for &slot in sub_slots {
            let slot_sec = self.unwrap_slot(slot, holder_sk)?;
            let mut seed_in = Vec::with_capacity(40);
            seed_in.extend_from_slice(re_encaps_seed);
            seed_in.extend_from_slice(&slot.to_le_bytes());
            let slot_seed = cshake32(b"MINIDREGG/PERSLOT/ATTENUATE_ENCAPS_SEED", &seed_in);
            next_wrapped.push(wrap_slot_secret_hybrid(
                self.cell_id,
                slot,
                self.key_epoch,
                next_delegate_pk,
                &slot_sec,
                &slot_seed,
            )?);
        }
        Ok(Self {
            cell_id: self.cell_id,
            key_epoch: self.key_epoch,
            delegate_pk: next_delegate_pk.clone(),
            granted_slots: sub_slots.to_vec(),
            wrapped_keys: next_wrapped,
        })
    }
}

/// `#tooth` regression model of legacy `breadstuffs/cell-crypto/src/read_cap.rs:334-345` (`CAP-21`),
/// used strictly to demonstrate and reject root-key copying in `verify_read_cap_confinement`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LegacyReadCap {
    pub cell_id: u64,
    pub key_epoch: u64,
    pub granted_slots: Vec<u64>,
    pub leaked_root_view_key: Digest,
}

impl LegacyReadCap {
    pub fn attenuate_buggy(&self, sub_slots: &[u64]) -> Option<Self> {
        if sub_slots.iter().all(|s| self.granted_slots.contains(s)) {
            Some(Self {
                cell_id: self.cell_id,
                key_epoch: self.key_epoch,
                granted_slots: sub_slots.to_vec(),
                leaked_root_view_key: self.leaked_root_view_key, // CAP-21 bug!
            })
        } else {
            None
        }
    }
}

pub enum ReadCapEnvelope<'a> {
    LegacyRootCopy(&'a LegacyReadCap),
    ConfinedPerSlot(&'a AttenuatedSlotCap),
}

pub fn verify_read_cap_confinement(env: ReadCapEnvelope<'_>) -> Result<(), PerSlotError> {
    match env {
        ReadCapEnvelope::LegacyRootCopy(_) => Err(PerSlotError::LegacyRootKeyCopyForbidden),
        ReadCapEnvelope::ConfinedPerSlot(cap) => {
            for w in &cap.wrapped_keys {
                if !cap.granted_slots.contains(&w.slot_index) {
                    return Err(PerSlotError::SlotNotAuthorized(w.slot_index));
                }
            }
            Ok(())
        }
    }
}

// ============================================================================
// §5. Statement-Pinned `key_commit_i` & Keyless Ciphertext -> `saltedPatchRoot` Weld (`L8` + `F4`)
// ============================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SlotAadMeta {
    pub document_id: u64,
    pub atom_id: u64,
    pub schema: Digest,
    pub operation_id: u64,
    pub slot_index: u64,
    pub key_epoch: u64,
    pub extra_aad: Vec<u8>,
}

pub fn compute_slot_aad_digest(m: &SlotAadMeta) -> Digest {
    let mut inp = Vec::with_capacity(8 * 6 + 32 + m.extra_aad.len());
    inp.extend_from_slice(&m.document_id.to_le_bytes());
    inp.extend_from_slice(&m.atom_id.to_le_bytes());
    inp.extend_from_slice(&m.schema);
    inp.extend_from_slice(&m.operation_id.to_le_bytes());
    inp.extend_from_slice(&m.slot_index.to_le_bytes());
    inp.extend_from_slice(&m.key_epoch.to_le_bytes());
    inp.extend_from_slice(&(m.extra_aad.len() as u64).to_le_bytes());
    inp.extend_from_slice(&m.extra_aad);
    cshake32(SLOT_AAD_CUST, &inp)
}

pub fn derive_slot_keystream(
    slot_secret: &Digest,
    slot_index: u64,
    nonce: &[u8; 32],
    aad_digest: &Digest,
    len: usize,
) -> Vec<u8> {
    let blocks = len.div_ceil(32);
    let mut seed = Vec::with_capacity(32 + 8 + 32 + 32 + 8);
    seed.extend_from_slice(slot_secret);
    seed.extend_from_slice(&slot_index.to_le_bytes());
    seed.extend_from_slice(nonce);
    seed.extend_from_slice(aad_digest);
    let base_len = seed.len();
    seed.resize(base_len + 8, 0);

    let mut out = Vec::with_capacity(blocks * 32);
    for b in 0..blocks {
        seed[base_len..].copy_from_slice(&(b as u64).to_le_bytes());
        out.extend_from_slice(&cshake32(SLOT_STREAM_CUST, &seed));
    }
    out.truncate(len);
    out
}

pub fn derive_slot_salts(
    slot_secret: &Digest,
    slot_index: u64,
    nonce: &[u8; 32],
    aad_digest: &Digest,
    len: usize,
) -> Vec<Salt248> {
    let mut base_seed = Vec::with_capacity(32 + 8 + 32 + 32);
    base_seed.extend_from_slice(slot_secret);
    base_seed.extend_from_slice(&slot_index.to_le_bytes());
    base_seed.extend_from_slice(nonce);
    base_seed.extend_from_slice(aad_digest);

    if len < 256 {
        let mut seed = base_seed;
        let base_len = seed.len();
        seed.resize(base_len + 8, 0);
        let mut salts = Vec::with_capacity(len);
        for pos in 0..len {
            seed[base_len..].copy_from_slice(&(pos as u64).to_le_bytes());
            let d = cshake32(SLOT_SALTS_CUST, &seed);
            let mut s = [0u8; 31];
            s.copy_from_slice(&d[0..31]);
            salts.push(s);
        }
        return salts;
    }

    let mut salts = vec![[0u8; 31]; len];
    let chunk_size = len.div_ceil(8);
    let seed_ref = &base_seed;
    std::thread::scope(|scope| {
        for (chunk_idx, out_chunk) in salts.chunks_mut(chunk_size).enumerate() {
            let start_pos = chunk_idx * chunk_size;
            scope.spawn(move || {
                let mut seed = Vec::with_capacity(seed_ref.len() + 8);
                seed.extend_from_slice(seed_ref);
                let base_len = seed.len();
                seed.resize(base_len + 8, 0);
                for (offset, dst) in out_chunk.iter_mut().enumerate() {
                    seed[base_len..].copy_from_slice(&((start_pos + offset) as u64).to_le_bytes());
                    let d = cshake32(SLOT_SALTS_CUST, &seed);
                    dst.copy_from_slice(&d[0..31]);
                }
            });
        }
    });
    salts
}

#[allow(clippy::too_many_arguments)]
pub fn compute_slot_aead_tag(
    slot_secret: &Digest,
    key_commit: &Digest,
    nonce: &[u8; 32],
    aad_digest: &Digest,
    salted_patch_root: &Digest,
    ct_merkle_root: &Digest,
    mask_merkle_root: &Digest,
    patch_len: usize,
) -> Digest {
    let mut inp = Vec::with_capacity(7 * 32 + 8);
    inp.extend_from_slice(slot_secret);
    inp.extend_from_slice(key_commit);
    inp.extend_from_slice(nonce);
    inp.extend_from_slice(aad_digest);
    inp.extend_from_slice(salted_patch_root);
    inp.extend_from_slice(ct_merkle_root);
    inp.extend_from_slice(mask_merkle_root);
    inp.extend_from_slice(&(patch_len as u64).to_le_bytes());
    cshake32(SLOT_AEAD_TAG_CUST, &inp)
}

pub fn ciphertext_merkle_root(ciphertext: &[u8]) -> Result<Digest, PerSlotError> {
    let zero_salts = vec![[0u8; 31]; ciphertext.len()];
    fast_salted_content_commit(ciphertext, &zero_salts)
        .map_err(|_| PerSlotError::CiphertextRootMismatch("ciphertext Merkle root failed"))
}

pub fn mask_merkle_root(keystream: &[u8], salts: &[Salt248]) -> Result<Digest, PerSlotError> {
    fast_salted_content_commit(keystream, salts)
        .map_err(|_| PerSlotError::CiphertextRootMismatch("mask Merkle root failed"))
}

fn tower_pow(mut base: Tower256, mut exp: usize) -> Tower256 {
    let mut acc = Tower256::ONE;
    while exp > 0 {
        if (exp & 1) != 0 {
            acc = acc.mul(base);
        }
        base = base.mul(base);
        exp >>= 1;
    }
    acc
}

/// Horner evaluation `∑_{i=0}^{n-1} γ^i * leaves[i]` in `Tower256` (`towerPolyEval` in Lean),
/// parallelized across 8 chunks for `leaves.len() >= 512` (bit-for-bit identical).
pub fn tower_poly_eval(gamma: Tower256, leaves: &[Tower256]) -> Tower256 {
    if leaves.len() < 512 {
        let mut acc = Tower256::ZERO;
        for &leaf in leaves.iter().rev() {
            acc = leaf.add(gamma.mul(acc));
        }
        return acc;
    }
    let chunk_size = leaves.len().div_ceil(8);
    let mut partials = [Tower256::ZERO; 8];
    let mut chunk_starts = [0usize; 8];
    let mut active = 0usize;
    std::thread::scope(|scope| {
        for (idx, (chunk, dst)) in leaves
            .chunks(chunk_size)
            .zip(partials.iter_mut())
            .enumerate()
        {
            chunk_starts[idx] = idx * chunk_size;
            active = idx + 1;
            scope.spawn(move || {
                let mut acc = Tower256::ZERO;
                for &leaf in chunk.iter().rev() {
                    acc = leaf.add(gamma.mul(acc));
                }
                *dst = acc;
            });
        }
    });
    let mut total = Tower256::ZERO;
    for idx in 0..active {
        let weight = tower_pow(gamma, chunk_starts[idx]);
        total = total.add(weight.mul(partials[idx]));
    }
    total
}

fn salted_leaves_t256(bytes: &[u8], salts: &[Salt248]) -> Vec<Tower256> {
    bytes
        .iter()
        .zip(salts.iter())
        .map(|(&b, s)| pack_salted_leaf(b, s))
        .collect()
}

fn ct_leaves_t256(ct: &[u8]) -> Vec<Tower256> {
    let z = [0u8; 31];
    ct.iter().map(|&b| pack_salted_leaf(b, &z)).collect()
}

/// Public keyless sponge/Merkle + `Tower256` blinded-XOR weld artifact (ZERO secrets or plaintext!).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicCiphertextWeld {
    pub ct_merkle_root: Digest,
    pub mask_merkle_root: Digest,
    pub blind_pad_commit: Digest,
    pub aead_tag: Digest,
    pub weld_digest: Digest,
    pub blind_eval_s: Digest,
    pub blind_eval_m: Digest,
}

/// Keyless public consensus statement (`KeylessPublicPatchStmt` in Lean).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KeylessPublicPatchStmt {
    pub aad_meta: SlotAadMeta,
    pub key_commit: Digest,
    pub nonce: [u8; 32],
    pub patch_len: usize,
    pub salted_patch_root: Digest,
    pub ciphertext: Vec<u8>,
    pub weld: PublicCiphertextWeld,
}

#[allow(clippy::too_many_arguments)]
pub fn compute_weld_digest(
    salted_patch_root: &Digest,
    mask_merkle_root: &Digest,
    ct_merkle_root: &Digest,
    key_commit: &Digest,
    nonce: &[u8; 32],
    aad_digest: &Digest,
    patch_len: usize,
    aead_tag: &Digest,
    blind_pad_commit: &Digest,
) -> Digest {
    let mut inp = Vec::with_capacity(8 * 32 + 8);
    inp.extend_from_slice(salted_patch_root);
    inp.extend_from_slice(mask_merkle_root);
    inp.extend_from_slice(ct_merkle_root);
    inp.extend_from_slice(key_commit);
    inp.extend_from_slice(nonce);
    inp.extend_from_slice(aad_digest);
    inp.extend_from_slice(&(patch_len as u64).to_le_bytes());
    inp.extend_from_slice(aead_tag);
    inp.extend_from_slice(blind_pad_commit);
    cshake32(PUBLIC_WELD_CUST, &inp)
}

pub fn compute_weld_challenge(weld_digest: &Digest) -> Tower256 {
    let d = cshake32(WELD_CHALLENGE_CUST, weld_digest);
    Tower256::from_le_bytes(d)
}

pub fn compute_blind_pad_commit(
    blind_pad: &Digest,
    salted_patch_root: &Digest,
    nonce: &[u8; 32],
) -> Digest {
    let mut inp = Vec::with_capacity(96);
    inp.extend_from_slice(blind_pad);
    inp.extend_from_slice(salted_patch_root);
    inp.extend_from_slice(nonce);
    cshake32(BLIND_PAD_CUST, &inp)
}

/// Seal `plaintext` under statement-pinned `slot_secret` (with caller-supplied or derived `salts`)
/// and produce the keyless `KeylessPublicPatchStmt` containing the authenticated sponge/Merkle
/// + `Tower256` blinded-XOR weld.
#[allow(clippy::too_many_arguments)]
pub fn seal_pinned_slot_patch(
    aad_meta: SlotAadMeta,
    slot_secret: &Digest,
    nonce: [u8; 32],
    plaintext: &[u8],
    opt_salts: Option<&[Salt248]>,
    blind_pad: &Digest,
) -> Result<(KeylessPublicPatchStmt, Vec<Salt248>), PerSlotError> {
    if plaintext.is_empty() {
        return Err(PerSlotError::CiphertextRootMismatch("empty plaintext"));
    }
    let aad_digest = compute_slot_aad_digest(&aad_meta);
    let salts: Vec<Salt248> = match opt_salts {
        Some(s) => {
            if s.len() != plaintext.len() {
                return Err(PerSlotError::CiphertextRootMismatch("salts length mismatch"));
            }
            s.to_vec()
        }
        None => derive_slot_salts(slot_secret, aad_meta.slot_index, &nonce, &aad_digest, plaintext.len()),
    };
    let keystream =
        derive_slot_keystream(slot_secret, aad_meta.slot_index, &nonce, &aad_digest, plaintext.len());
    let ciphertext: Vec<u8> = plaintext
        .iter()
        .zip(keystream.iter())
        .map(|(&p, &k)| p ^ k)
        .collect();

    let salted_patch_root = fast_salted_content_commit(plaintext, &salts)
        .map_err(|_| PerSlotError::CiphertextRootMismatch("salted_patch_root failed"))?;
    let ct_root = ciphertext_merkle_root(&ciphertext)?;
    let mask_root = mask_merkle_root(&keystream, &salts)?;
    let key_commit = slot_key_commit(aad_meta.slot_index, slot_secret);
    let aead_tag = compute_slot_aead_tag(
        slot_secret,
        &key_commit,
        &nonce,
        &aad_digest,
        &salted_patch_root,
        &ct_root,
        &mask_root,
        plaintext.len(),
    );
    let blind_pad_commit = compute_blind_pad_commit(blind_pad, &salted_patch_root, &nonce);
    let weld_digest = compute_weld_digest(
        &salted_patch_root,
        &mask_root,
        &ct_root,
        &key_commit,
        &nonce,
        &aad_digest,
        plaintext.len(),
        &aead_tag,
        &blind_pad_commit,
    );
    let gamma = compute_weld_challenge(&weld_digest);
    let pad_t256 = Tower256::from_le_bytes(*blind_pad);
    let eval_s = tower_poly_eval(gamma, &salted_leaves_t256(plaintext, &salts));
    let eval_m = tower_poly_eval(gamma, &salted_leaves_t256(&keystream, &salts));
    let blind_eval_s = eval_s.add(pad_t256).to_le_bytes();
    let blind_eval_m = eval_m.add(pad_t256).to_le_bytes();

    Ok((
        KeylessPublicPatchStmt {
            aad_meta,
            key_commit,
            nonce,
            patch_len: plaintext.len(),
            salted_patch_root,
            ciphertext,
            weld: PublicCiphertextWeld {
                ct_merkle_root: ct_root,
                mask_merkle_root: mask_root,
                blind_pad_commit,
                aead_tag,
                weld_digest,
                blind_eval_s,
                blind_eval_m,
            },
        },
        salts,
    ))
}

/// **Keyless Public Consensus Verifier (`verifyKeylessCiphertextWeld` in Lean):**
/// rejects forged/unsealed/swapped ciphertexts (`PerSlotError::CiphertextRootMismatch`)
/// WITHOUT ever learning `slot_secret(i)` or plaintext bytes!
pub fn verify_keyless_ciphertext_weld(stmt: &KeylessPublicPatchStmt) -> Result<(), PerSlotError> {
    if stmt.patch_len == 0 || stmt.ciphertext.len() != stmt.patch_len {
        return Err(PerSlotError::CiphertextRootMismatch(
            "ciphertext length mismatch",
        ));
    }
    let ct_root = ciphertext_merkle_root(&stmt.ciphertext)?;
    if !ct_eq_bytes(&ct_root, &stmt.weld.ct_merkle_root) {
        return Err(PerSlotError::CiphertextRootMismatch(
            "ciphertext Merkle root mismatch",
        ));
    }
    let aad_digest = compute_slot_aad_digest(&stmt.aad_meta);
    let expected_weld = compute_weld_digest(
        &stmt.salted_patch_root,
        &stmt.weld.mask_merkle_root,
        &stmt.weld.ct_merkle_root,
        &stmt.key_commit,
        &stmt.nonce,
        &aad_digest,
        stmt.patch_len,
        &stmt.weld.aead_tag,
        &stmt.weld.blind_pad_commit,
    );
    if !ct_eq_bytes(&expected_weld, &stmt.weld.weld_digest) {
        return Err(PerSlotError::CiphertextRootMismatch(
            "authenticated sponge weld digest mismatch",
        ));
    }
    let gamma = compute_weld_challenge(&stmt.weld.weld_digest);
    let eval_c = tower_poly_eval(gamma, &ct_leaves_t256(&stmt.ciphertext));
    let lhs = Tower256::from_le_bytes(stmt.weld.blind_eval_s)
        .add(Tower256::from_le_bytes(stmt.weld.blind_eval_m));
    if lhs != eval_c {
        return Err(PerSlotError::CiphertextRootMismatch(
            "Tower256 blinded XOR evaluation mismatch",
        ));
    }
    Ok(())
}

/// Authorized slot-key-holder decryptor: verifies `slot_key_commit`, keyless weld, constant-time
/// AEAD tag, decrypts `ciphertext`, and verifies `salted_content_commit(plaintext, salts) == salted_patch_root`.
pub fn unseal_pinned_slot_patch(
    slot_secret: &Digest,
    stmt: &KeylessPublicPatchStmt,
    opt_salts: Option<&[Salt248]>,
) -> Result<Vec<u8>, PerSlotError> {
    let kc = slot_key_commit(stmt.aad_meta.slot_index, slot_secret);
    if !ct_eq_bytes(&kc, &stmt.key_commit) {
        return Err(PerSlotError::KeyCommitMismatch);
    }
    verify_keyless_ciphertext_weld(stmt)?;
    let aad_digest = compute_slot_aad_digest(&stmt.aad_meta);
    let expected_tag = compute_slot_aead_tag(
        slot_secret,
        &stmt.key_commit,
        &stmt.nonce,
        &aad_digest,
        &stmt.salted_patch_root,
        &stmt.weld.ct_merkle_root,
        &stmt.weld.mask_merkle_root,
        stmt.patch_len,
    );
    if !ct_eq_bytes(&stmt.weld.aead_tag, &expected_tag) {
        return Err(PerSlotError::AeadTagMismatch);
    }
    let keystream = derive_slot_keystream(
        slot_secret,
        stmt.aad_meta.slot_index,
        &stmt.nonce,
        &aad_digest,
        stmt.patch_len,
    );
    let plaintext: Vec<u8> = stmt
        .ciphertext
        .iter()
        .zip(keystream.iter())
        .map(|(&c, &k)| c ^ k)
        .collect();
    let owned_salts;
    let salts: &[Salt248] = match opt_salts {
        Some(s) => s,
        None => {
            owned_salts = derive_slot_salts(
                slot_secret,
                stmt.aad_meta.slot_index,
                &stmt.nonce,
                &aad_digest,
                stmt.patch_len,
            );
            &owned_salts
        }
    };
    let recomputed_mask = mask_merkle_root(&keystream, salts)?;
    if !ct_eq_bytes(&recomputed_mask, &stmt.weld.mask_merkle_root) {
        return Err(PerSlotError::CiphertextRootMismatch("mask root mismatch"));
    }
    let recomputed_root = fast_salted_content_commit(&plaintext, salts)
        .map_err(|_| PerSlotError::CiphertextRootMismatch("salted root recompute failed"))?;
    if !ct_eq_bytes(&recomputed_root, &stmt.salted_patch_root) {
        return Err(PerSlotError::CiphertextRootMismatch(
            "decrypted plaintext does not match salted_patch_root",
        ));
    }
    Ok(plaintext)
}

/// **Full Statement-Pinned + Keyless-Welded Sealed `Hyperdocument` Patch Gate**
/// (`verifyConfinedSealedHyperdocPatch` in `Assurance/PerSlotKeyConfinement.lean`).
pub fn verify_confined_sealed_hyperdoc_patch<NT, SemOp, Val>(
    base_stmt: &SealedHyperdocPatchStmt<'_, NT, SemOp, Val>,
    pub_stmt: &KeylessPublicPatchStmt,
    base_wit: &SealedHyperdocPatchWitness<'_, NT, SemOp, Val>,
    wit_slot_secret: &Digest,
) -> Result<(), PerSlotError>
where
    NT: Eq + Hash + Copy + fmt::Debug,
    SemOp: PartialEq + Clone,
    Val: PartialEq,
{
    verify_sealed_hyperdoc_patch(base_stmt, base_wit).map_err(PerSlotError::BaseGateRejected)?;

    if pub_stmt.aad_meta.document_id != base_stmt.document_id
        || pub_stmt.aad_meta.atom_id != base_stmt.atom_id
        || pub_stmt.aad_meta.schema != base_stmt.schema
        || pub_stmt.aad_meta.operation_id != base_stmt.operation_id
        || pub_stmt.patch_len != base_stmt.patch_len
        || pub_stmt.salted_patch_root != base_stmt.salted_patch_root
    {
        return Err(PerSlotError::CiphertextRootMismatch(
            "public statement metadata disagrees with base SealedHyperdocPatchStmt",
        ));
    }
    let kc = slot_key_commit(pub_stmt.aad_meta.slot_index, wit_slot_secret);
    if !ct_eq_bytes(&kc, &pub_stmt.key_commit) {
        return Err(PerSlotError::KeyCommitMismatch);
    }

    let aad_digest = compute_slot_aad_digest(&pub_stmt.aad_meta);
    let ks = derive_slot_keystream(
        wit_slot_secret,
        pub_stmt.aad_meta.slot_index,
        &pub_stmt.nonce,
        &aad_digest,
        base_stmt.patch_len,
    );
    let expected_ct: Vec<u8> = base_wit
        .patch_bytes
        .iter()
        .zip(ks.iter())
        .map(|(&p, &k)| p ^ k)
        .collect();
    if !ct_eq_bytes(&pub_stmt.ciphertext, &expected_ct) {
        return Err(PerSlotError::CiphertextRootMismatch(
            "ciphertext disagrees with keystream encryption of patch_bytes",
        ));
    }
    let expected_mask = mask_merkle_root(&ks, &base_wit.patch_salts)?;
    if !ct_eq_bytes(&pub_stmt.weld.mask_merkle_root, &expected_mask) {
        return Err(PerSlotError::CiphertextRootMismatch("mask root mismatch"));
    }
    let expected_tag = compute_slot_aead_tag(
        wit_slot_secret,
        &pub_stmt.key_commit,
        &pub_stmt.nonce,
        &aad_digest,
        &base_stmt.salted_patch_root,
        &pub_stmt.weld.ct_merkle_root,
        &expected_mask,
        base_stmt.patch_len,
    );
    if !ct_eq_bytes(&pub_stmt.weld.aead_tag, &expected_tag) {
        return Err(PerSlotError::AeadTagMismatch);
    }
    verify_keyless_ciphertext_weld(pub_stmt)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex_decode(s: &str) -> Vec<u8> {
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
            .collect()
    }

    #[test]
    fn rfc7748_x25519_official_test_vectors() {
        // RFC 7748 §6.1 Alice & Bob DH vector:
        let alice_sk: [u8; 32] =
            hex_decode("77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a")
                .try_into()
                .unwrap();
        let alice_pk_exp: [u8; 32] =
            hex_decode("8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a")
                .try_into()
                .unwrap();
        let bob_sk: [u8; 32] =
            hex_decode("5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb")
                .try_into()
                .unwrap();
        let bob_pk_exp: [u8; 32] =
            hex_decode("de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f")
                .try_into()
                .unwrap();
        let ss_exp: [u8; 32] =
            hex_decode("4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742")
                .try_into()
                .unwrap();

        assert_eq!(x25519_public_key(&alice_sk), alice_pk_exp);
        assert_eq!(x25519_public_key(&bob_sk), bob_pk_exp);
        assert_eq!(x25519_dh_checked(&alice_sk, &bob_pk_exp).unwrap(), ss_exp);
        assert_eq!(x25519_dh_checked(&bob_sk, &alice_pk_exp).unwrap(), ss_exp);
        // Low-order all-zero point must be rejected:
        assert_eq!(
            x25519_dh_checked(&alice_sk, &[0u8; 32]),
            Err(PerSlotError::LowOrderX25519Point)
        );
    }

    #[test]
    fn fips203_mlkem768_roundtrip_and_implicit_rejection() {
        let d = [0x11u8; 32];
        let z = [0x22u8; 32];
        let m = [0x33u8; 32];
        let (ek, dk) = mlkem768_keygen_internal(&d, &z);
        assert_eq!(ek.0.len(), MLKEM768_EK_BYTES);
        assert_eq!(dk.0.len(), MLKEM768_DK_BYTES);

        let (mut ct, ss_enc) = mlkem768_encaps_internal(&ek, &m).unwrap();
        assert_eq!(ct.0.len(), MLKEM768_CT_BYTES);
        let ss_dec = mlkem768_decaps_internal(&dk, &ct).unwrap();
        assert_eq!(ss_enc, ss_dec);

        // Tampering 1 bit of ciphertext triggers FIPS 203 FO implicit rejection (distinct key != ss_enc):
        ct.0[17] ^= 0x01;
        let ss_rej = mlkem768_decaps_internal(&dk, &ct).unwrap();
        assert_ne!(ss_rej, ss_enc);
    }
}
