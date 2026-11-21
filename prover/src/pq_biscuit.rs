//! Post-quantum issuer-root-isolated `ZkBiscuit` selective-disclosure credentials
//! (`D8`, closing `CAP-01`, `CAP-10`, `CAP-12`, and `CAP-13`).
//!
//! Byte-exact native counterpart of `Theory/PqSelectiveBiscuit.lean`:
//! - **100% post-quantum:** SP 800-185 `cSHAKE256` + pluggable `PqSigBackend` (concrete
//!   256-bit pure-hash `WotsCshake256` built in; compatible with `dregg-pq` Hybrid
//!   Ed25519+ML-DSA-65; zero elliptic-curve pairings or Pedersen commitments).
//! - **`CAP-01` Root-Key Isolation:** `IssuerSecret` never enters `HolderToken` or its
//!   serialized wire form; holders attenuate tokens using only their own delegated key.
//! - **`CAP-12` Block-0 Authority Pin:** `extract_subject` and `extract_issuer_authority`
//!   read exclusively from block `0`, and `verify_token` enforces monotone narrowing of
//!   `rights` and `expires_at` across all holder-appended blocks `1..k`.
//! - **`CAP-10` Canonical Sorted / Ancestor-Cone Revocation:** `RevocationSet::from_raw`
//!   deduplicates and strictly sorts 256-bit `chain_id` nullifiers before binary search;
//!   `RevocationSet::from_verified_witness` rejects unsorted witnesses before searching;
//!   `verify_token` checks every prefix `0..=k` so appending hops cannot evade revocation.
//! - **Salted Selective Attribute Disclosure:** `cSHAKE256` Merkle tree with 256-bit
//!   per-leaf salts lets holders open any subset `S ⊆ [0, m)` while keeping unrevealed
//!   attributes hidden behind 32-byte salted digests.

use crate::hash_kernels::cshake256_xof;

pub type Digest32 = [u8; 32];

pub const CUST_ATTR_LEAF: &[u8] = b"MINIDREGG.PQ_BISCUIT.ATTR_LEAF/v1";
pub const CUST_ATTR_NODE: &[u8] = b"MINIDREGG.PQ_BISCUIT.ATTR_NODE/v1";
pub const CUST_LINEAGE: &[u8] = b"MINIDREGG.PQ_BISCUIT.LINEAGE/v1";
pub const CUST_NULLIFIER: &[u8] = b"MINIDREGG.PQ_BISCUIT.NULLIFIER/v1";
pub const CUST_REV_ROOT: &[u8] = b"MINIDREGG.PQ_BISCUIT.REV_ROOT/v1";
pub const CUST_BLOCK_SIG: &[u8] = b"MINIDREGG.PQ_BISCUIT.BLOCK_SIG/v1";
pub const CUST_WOTS_CHAIN: &[u8] = b"MINIDREGG.PQ_BISCUIT.WOTS_CHAIN/v1";

pub const WOTS_CHAINS: usize = 67;
pub const WOTS_SIG_LEN: usize = WOTS_CHAINS * 32;

/// Constant-time equality over byte slices.
pub fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut diff = 0u8;
    for (&x, &y) in a.iter().zip(b.iter()) {
        diff |= x ^ y;
    }
    diff == 0
}

/// Domain-separated 32-byte SP 800-185 `cSHAKE256`.
pub fn cshake32(cust: &[u8], input: &[u8]) -> Digest32 {
    let out = cshake256_xof(cust, input, 32);
    let mut d = [0u8; 32];
    d.copy_from_slice(&out);
    d
}

/// Standard unsigned LEB128 encoding for `usize` (matches Lean `leb128`).
pub fn encode_leb128(mut n: usize, out: &mut Vec<u8>) {
    loop {
        let lo = (n & 0x7f) as u8;
        n >>= 7;
        if n == 0 {
            out.push(lo);
            break;
        }
        out.push(0x80 | lo);
    }
}

/// Exact unsigned LEB128 encoding for a 256-bit big-endian integer (matches Lean `leb128 (ofBE bs)`).
pub fn encode_leb128_u256(be32: &Digest32, out: &mut Vec<u8>) {
    let mut limbs = [
        u64::from_be_bytes(be32[24..32].try_into().unwrap()),
        u64::from_be_bytes(be32[16..24].try_into().unwrap()),
        u64::from_be_bytes(be32[8..16].try_into().unwrap()),
        u64::from_be_bytes(be32[0..8].try_into().unwrap()),
    ];
    loop {
        let lo = (limbs[0] & 0x7f) as u8;
        limbs[0] = (limbs[0] >> 7) | (limbs[1] << 57);
        limbs[1] = (limbs[1] >> 7) | (limbs[2] << 57);
        limbs[2] = (limbs[2] >> 7) | (limbs[3] << 57);
        limbs[3] >>= 7;
        if (limbs[0] | limbs[1] | limbs[2] | limbs[3]) == 0 {
            out.push(lo);
            break;
        }
        out.push(0x80 | lo);
    }
}

/// Prefix-free length-delimited byte field (`leb128(bs.len()) || bs`).
pub fn encode_field(bs: &[u8], out: &mut Vec<u8>) {
    encode_leb128(bs.len(), out);
    out.extend_from_slice(bs);
}

/// Prefix-free encoding of a list of 256-bit big-endian naturals (`encodeNats`).
pub fn encode_nats_u256(ns: &[Digest32], out: &mut Vec<u8>) {
    encode_leb128(ns.len(), out);
    for n in ns {
        encode_leb128_u256(n, out);
    }
}

// ---------------------------------------------------------------------------
// Post-Quantum Signature Interface & Concrete Pure-Hash cSHAKE256 WOTS+
// ---------------------------------------------------------------------------

/// Abstract post-quantum signature backend (zero elliptic-curve pairings or Pedersen).
pub trait PqSigBackend {
    type SecKey;
    fn pk_of(&self, sk: &Self::SecKey) -> Vec<u8>;
    fn sign(&self, sk: &Self::SecKey, msg: &[u8]) -> Vec<u8>;
    fn verify(&self, pk: &[u8], msg: &[u8], sig: &[u8]) -> bool;
}

/// Concrete 256-bit post-quantum hash-based WOTS+ (`w = 16`, `67` chains over `cSHAKE256`).
#[derive(Clone, Copy, Debug, Default)]
pub struct WotsCshake256;

impl WotsCshake256 {
    fn sk_elem(seed: &[u8], idx: u32) -> Digest32 {
        let mut buf = Vec::with_capacity(1 + 4 + seed.len());
        buf.push(0x00);
        buf.extend_from_slice(&idx.to_be_bytes());
        buf.extend_from_slice(seed);
        cshake32(CUST_WOTS_CHAIN, &buf)
    }

    fn chain_step(idx: u32, step: u32, val: &Digest32) -> Digest32 {
        let mut buf = [0u8; 1 + 4 + 4 + 32];
        buf[0] = 0x01;
        buf[1..5].copy_from_slice(&idx.to_be_bytes());
        buf[5..9].copy_from_slice(&step.to_be_bytes());
        buf[9..41].copy_from_slice(val);
        cshake32(CUST_WOTS_CHAIN, &buf)
    }

    fn chain_iter(idx: u32, start: u32, steps: u32, mut val: Digest32) -> Digest32 {
        for off in 0..steps {
            val = Self::chain_step(idx, start + off, &val);
        }
        val
    }

    pub fn digits(msg: &[u8]) -> [u8; WOTS_CHAINS] {
        let digest = cshake32(CUST_BLOCK_SIG, msg);
        let mut ds = [0u8; WOTS_CHAINS];
        let mut csum: u32 = 0;
        for (i, &b) in digest.iter().enumerate() {
            let hi = b >> 4;
            let lo = b & 0x0f;
            ds[2 * i] = hi;
            ds[2 * i + 1] = lo;
            csum += (15 - hi as u32) + (15 - lo as u32);
        }
        ds[64] = ((csum / 256) % 16) as u8;
        ds[65] = ((csum / 16) % 16) as u8;
        ds[66] = (csum % 16) as u8;
        ds
    }
}

impl PqSigBackend for WotsCshake256 {
    type SecKey = Vec<u8>;

    fn pk_of(&self, sk: &Self::SecKey) -> Vec<u8> {
        let mut buf = Vec::with_capacity(1 + WOTS_SIG_LEN);
        buf.push(0x02);
        for idx in 0..(WOTS_CHAINS as u32) {
            let tip = Self::chain_iter(idx, 0, 15, Self::sk_elem(sk, idx));
            buf.extend_from_slice(&tip);
        }
        cshake32(CUST_WOTS_CHAIN, &buf).to_vec()
    }

    fn sign(&self, sk: &Self::SecKey, msg: &[u8]) -> Vec<u8> {
        let ds = Self::digits(msg);
        let mut sig = Vec::with_capacity(WOTS_SIG_LEN);
        for (idx, &d) in ds.iter().enumerate() {
            let elem = Self::chain_iter(idx as u32, 0, d as u32, Self::sk_elem(sk, idx as u32));
            sig.extend_from_slice(&elem);
        }
        sig
    }

    fn verify(&self, pk: &[u8], msg: &[u8], sig: &[u8]) -> bool {
        if sig.len() != WOTS_SIG_LEN || pk.len() != 32 {
            return false;
        }
        let ds = Self::digits(msg);
        let mut buf = Vec::with_capacity(1 + WOTS_SIG_LEN);
        buf.push(0x02);
        for (idx, &d) in ds.iter().enumerate() {
            let mut chunk = [0u8; 32];
            chunk.copy_from_slice(&sig[idx * 32..(idx + 1) * 32]);
            let tip = Self::chain_iter(idx as u32, d as u32, (15 - d) as u32, chunk);
            buf.extend_from_slice(&tip);
        }
        let recovered = cshake32(CUST_WOTS_CHAIN, &buf);
        constant_time_eq(&recovered, pk)
    }
}

// ---------------------------------------------------------------------------
// CAP-10: Canonical Sorted RevocationSet & Witness Verification
// ---------------------------------------------------------------------------

/// Strictly ascending check on 256-bit big-endian revocation IDs.
pub fn is_strictly_sorted(ids: &[Digest32]) -> bool {
    ids.windows(2).all(|w| w[0] < w[1])
}

/// Canonical deduplicated strictly-sorted revocation set (`CAP-10`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RevocationSet {
    keys: Vec<Digest32>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RevocationWitnessError {
    UnsortedOrDuplicateWitness,
    RootMismatch,
}

impl RevocationSet {
    pub fn empty() -> Self {
        Self { keys: Vec::new() }
    }

    /// Canonicalizes any raw list in arbitrary insertion order (`dedupSort`).
    pub fn from_raw(raw: &[Digest32]) -> Self {
        let mut keys = raw.to_vec();
        keys.sort();
        keys.dedup();
        Self { keys }
    }

    pub fn insert(&mut self, id: Digest32) {
        if let Err(pos) = self.keys.binary_search(&id) {
            self.keys.insert(pos, id);
        }
    }

    pub fn keys(&self) -> &[Digest32] {
        &self.keys
    }

    pub fn contains(&self, id: &Digest32) -> bool {
        self.keys.binary_search(id).is_ok()
    }

    pub fn root(&self) -> Digest32 {
        let mut buf = Vec::with_capacity(8 + self.keys.len() * 37);
        encode_nats_u256(&self.keys, &mut buf);
        cshake32(CUST_REV_ROOT, &buf)
    }

    /// Fail-closed witness verification (`CAP-10`): rejects unsorted/duplicate witnesses
    /// BEFORE hashing or binary search.
    pub fn from_verified_witness(
        raw: &[Digest32],
        expected_root: &Digest32,
    ) -> Result<Self, RevocationWitnessError> {
        if !is_strictly_sorted(raw) {
            return Err(RevocationWitnessError::UnsortedOrDuplicateWitness);
        }
        let rs = Self { keys: raw.to_vec() };
        if !constant_time_eq(&rs.root(), expected_root) {
            return Err(RevocationWitnessError::RootMismatch);
        }
        Ok(rs)
    }
}

// ---------------------------------------------------------------------------
// Salted cSHAKE256 Selective-Disclosure Attribute Merkle Tree
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SaltedAttribute {
    pub key: Vec<u8>,
    pub value: Vec<u8>,
    pub salt: Digest32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SelectiveOpening {
    pub idx: usize,
    pub key: Vec<u8>,
    pub value: Vec<u8>,
    pub salt: Digest32,
    pub path: Vec<(bool, Digest32)>,
}

pub fn attr_empty_leaf() -> Digest32 {
    cshake32(CUST_ATTR_LEAF, &[0x02])
}

pub fn attr_leaf_commit(idx: usize, key: &[u8], value: &[u8], salt: &Digest32) -> Digest32 {
    let mut buf = Vec::with_capacity(1 + 8 + key.len() + value.len() + 36);
    buf.push(0x00);
    encode_leb128(idx, &mut buf);
    encode_field(key, &mut buf);
    encode_field(value, &mut buf);
    encode_field(salt, &mut buf);
    cshake32(CUST_ATTR_LEAF, &buf)
}

pub fn attr_node_hash(left: &Digest32, right: &Digest32) -> Digest32 {
    let mut buf = [0u8; 65];
    buf[0] = 0x01;
    buf[1..33].copy_from_slice(left);
    buf[33..65].copy_from_slice(right);
    cshake32(CUST_ATTR_NODE, &buf)
}

fn merkle_pair_layer(nodes: &[Digest32], empty: &Digest32) -> Vec<Digest32> {
    let mut out = Vec::with_capacity(nodes.len().div_ceil(2));
    let mut i = 0;
    while i < nodes.len() {
        let left = &nodes[i];
        let right = if i + 1 < nodes.len() { &nodes[i + 1] } else { empty };
        out.push(attr_node_hash(left, right));
        i += 2;
    }
    out
}

pub fn build_attr_leaves(height: usize, attrs: &[SaltedAttribute]) -> Vec<Digest32> {
    let n = 1usize << height;
    let empty = attr_empty_leaf();
    let mut leaves = Vec::with_capacity(n);
    for i in 0..n {
        if let Some(a) = attrs.get(i) {
            leaves.push(attr_leaf_commit(i, &a.key, &a.value, &a.salt));
        } else {
            leaves.push(empty);
        }
    }
    leaves
}

pub fn merkle_root(height: usize, leaves: &[Digest32]) -> Digest32 {
    let empty = attr_empty_leaf();
    let mut layer = leaves.to_vec();
    for _ in 0..height {
        layer = merkle_pair_layer(&layer, &empty);
    }
    layer.first().copied().unwrap_or(empty)
}

pub fn merkle_path(height: usize, mut idx: usize, leaves: &[Digest32]) -> Vec<(bool, Digest32)> {
    let empty = attr_empty_leaf();
    let mut layer = leaves.to_vec();
    let mut path = Vec::with_capacity(height);
    for _ in 0..height {
        let is_right = idx % 2 == 0;
        let sib_idx = if is_right { idx + 1 } else { idx - 1 };
        let sib = layer.get(sib_idx).copied().unwrap_or(empty);
        path.push((is_right, sib));
        layer = merkle_pair_layer(&layer, &empty);
        idx /= 2;
    }
    path
}

pub fn verify_merkle_opening(root: &Digest32, leaf: &Digest32, path: &[(bool, Digest32)]) -> bool {
    let mut cur = *leaf;
    for &(is_right, ref sib) in path {
        cur = if is_right {
            attr_node_hash(&cur, sib)
        } else {
            attr_node_hash(sib, &cur)
        };
    }
    constant_time_eq(&cur, root)
}

pub fn build_selective_openings(
    height: usize,
    attrs: &[SaltedAttribute],
    disclosed_indices: &[usize],
) -> Vec<SelectiveOpening> {
    let leaves = build_attr_leaves(height, attrs);
    let mut out = Vec::with_capacity(disclosed_indices.len());
    for &i in disclosed_indices {
        if let Some(a) = attrs.get(i) {
            out.push(SelectiveOpening {
                idx: i,
                key: a.key.clone(),
                value: a.value.clone(),
                salt: a.salt,
                path: merkle_path(height, i, &leaves),
            });
        }
    }
    out
}

pub fn verify_selective_disclosure(root: &Digest32, openings: &[SelectiveOpening]) -> bool {
    openings.iter().all(|op| {
        let leaf = attr_leaf_commit(op.idx, &op.key, &op.value, &op.salt);
        verify_merkle_opening(root, &leaf, &op.path)
    })
}

// ---------------------------------------------------------------------------
// CAP-01 Root-Key Isolation & CAP-12 Block-0 Authority Pin
// ---------------------------------------------------------------------------

/// Issuer-side secret container (`CAP-01`): NEVER placed inside `HolderToken` or serialized.
pub struct IssuerSecret<S: PqSigBackend> {
    sk: S::SecKey,
}

impl<S: PqSigBackend> IssuerSecret<S> {
    pub fn new(sk: S::SecKey) -> Self {
        Self { sk }
    }

    pub fn public_key(&self, scheme: &S) -> Vec<u8> {
        scheme.pk_of(&self.sk)
    }
}

/// Issuer-signed Block `0` — the sole source of `subject`, `issuer_pk`, and `attr_merkle_root`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuthorityBlock0 {
    pub subject: Vec<u8>,
    pub issuer_pk: Vec<u8>,
    pub holder_pk: Vec<u8>,
    pub rights: u64,
    pub expires_at: u64,
    pub attr_merkle_root: Digest32,
    pub nonce: Digest32,
}

impl AuthorityBlock0 {
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(
            64 + self.subject.len() + self.issuer_pk.len() + self.holder_pk.len(),
        );
        encode_field(&self.subject, &mut out);
        encode_field(&self.issuer_pk, &mut out);
        encode_field(&self.holder_pk, &mut out);
        out.extend_from_slice(&self.rights.to_be_bytes());
        out.extend_from_slice(&self.expires_at.to_be_bytes());
        encode_field(&self.attr_merkle_root, &mut out);
        encode_field(&self.nonce, &mut out);
        out
    }

    pub fn sign_msg(&self) -> Vec<u8> {
        let enc = self.encode();
        let mut out = Vec::with_capacity(1 + enc.len());
        out.push(0x00);
        out.extend_from_slice(&enc);
        out
    }
}

/// Holder-appended attenuation block `1..k`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttenuationBlock {
    pub rights: u64,
    pub expires_at: u64,
    pub next_holder_pk: Vec<u8>,
    pub caveat_tag: Vec<u8>,
    pub sig_bytes: Vec<u8>,
}

impl AttenuationBlock {
    pub fn payload_encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(24 + self.next_holder_pk.len() + self.caveat_tag.len());
        out.extend_from_slice(&self.rights.to_be_bytes());
        out.extend_from_slice(&self.expires_at.to_be_bytes());
        encode_field(&self.next_holder_pk, &mut out);
        encode_field(&self.caveat_tag, &mut out);
        out
    }
}

/// Serialized holder token (`CAP-01`): structurally holds ONLY public keys, chained PQ
/// signatures, and salted attribute Merkle root — ZERO `IssuerSecret` witness bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HolderToken {
    pub block0: AuthorityBlock0,
    pub block0_sig: Vec<u8>,
    pub hops: Vec<AttenuationBlock>,
}

impl HolderToken {
    /// Canonical wire serialization of a `HolderToken` (contains zero secret-key material).
    pub fn serialize_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        encode_field(&self.block0.encode(), &mut out);
        encode_field(&self.block0_sig, &mut out);
        encode_leb128(self.hops.len(), &mut out);
        for h in &self.hops {
            encode_field(&h.payload_encode(), &mut out);
            encode_field(&h.sig_bytes, &mut out);
        }
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IssuerAuthority {
    pub issuer_pk: Vec<u8>,
    pub subject: Vec<u8>,
    pub root_rights: u64,
    pub root_expires_at: u64,
    pub attr_merkle_root: Digest32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedAuthority {
    pub subject: Vec<u8>,
    pub rights: u64,
    pub expires_at: u64,
    pub attr_merkle_root: Digest32,
    pub tail_lineage: Digest32,
    pub tail_holder_pk: Vec<u8>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifyError {
    IssuerKeyMismatch,
    InvalidBlock0Signature,
    RevokedAtDepth(usize),
    RightsEscalation { hop: usize },
    ExpiryEscalation { hop: usize },
    InvalidHopSignature { hop: usize },
    Expired,
    InvalidSelectiveDisclosure,
}

pub fn sub_mask(child: u64, parent: u64) -> bool {
    (child & parent) == child
}

pub fn hop_sign_msg(prev_lineage: &Digest32, hop: &AttenuationBlock) -> Vec<u8> {
    let payload = hop.payload_encode();
    let mut out = Vec::with_capacity(1 + 36 + payload.len());
    out.push(0x01);
    encode_field(prev_lineage, &mut out);
    out.extend_from_slice(&payload);
    out
}

pub fn root_lineage(b0: &AuthorityBlock0) -> Digest32 {
    cshake32(CUST_LINEAGE, &b0.sign_msg())
}

pub fn step_lineage(prev: &Digest32, hop: &AttenuationBlock) -> Digest32 {
    cshake32(CUST_LINEAGE, &hop_sign_msg(prev, hop))
}

pub fn lineage_of(b0: &AuthorityBlock0, hops: &[AttenuationBlock]) -> Digest32 {
    let mut cur = root_lineage(b0);
    for h in hops {
        cur = step_lineage(&cur, h);
    }
    cur
}

pub fn lineage_nullifier(lineage: &Digest32) -> Digest32 {
    let mut buf = [0u8; 33];
    buf[0] = 0x01;
    buf[1..33].copy_from_slice(lineage);
    cshake32(CUST_NULLIFIER, &buf)
}

/// 256-bit `cSHAKE256` nullifier of prefix `0..=depth` (`depth <= hops.len()`).
pub fn chain_id(b0: &AuthorityBlock0, hops: &[AttenuationBlock], depth: usize) -> Digest32 {
    let take = depth.min(hops.len());
    lineage_nullifier(&lineage_of(b0, &hops[..take]))
}

/// **`CAP-12` Block-0 Authority Pin:** extracts subject EXCLUSIVELY from block `0`.
pub fn extract_subject(tok: &HolderToken) -> &[u8] {
    &tok.block0.subject
}

/// **`CAP-12` Block-0 Authority Pin:** extracts issuer authority EXCLUSIVELY from block `0`.
pub fn extract_issuer_authority(tok: &HolderToken) -> IssuerAuthority {
    IssuerAuthority {
        issuer_pk: tok.block0.issuer_pk.clone(),
        subject: tok.block0.subject.clone(),
        root_rights: tok.block0.rights,
        root_expires_at: tok.block0.expires_at,
        attr_merkle_root: tok.block0.attr_merkle_root,
    }
}

/// Issue a root `HolderToken` using `IssuerSecret` (which stays strictly on the issuer).
#[allow(clippy::too_many_arguments)]
pub fn issue_root_token<S: PqSigBackend>(
    scheme: &S,
    issuer: &IssuerSecret<S>,
    subject: Vec<u8>,
    holder_pk: Vec<u8>,
    attr_merkle_root: Digest32,
    nonce: Digest32,
    rights: u64,
    expires_at: u64,
) -> HolderToken {
    let block0 = AuthorityBlock0 {
        subject,
        issuer_pk: scheme.pk_of(&issuer.sk),
        holder_pk,
        rights,
        expires_at,
        attr_merkle_root,
        nonce,
    };
    let block0_sig = scheme.sign(&issuer.sk, &block0.sign_msg());
    HolderToken {
        block0,
        block0_sig,
        hops: Vec::new(),
    }
}

/// Attenuate an existing `HolderToken` using ONLY the current holder's `holder_sk` (`CAP-01`).
pub fn attenuate_token<S: PqSigBackend>(
    scheme: &S,
    tok: &HolderToken,
    holder_sk: &S::SecKey,
    new_rights: u64,
    new_expires_at: u64,
    next_holder_pk: Vec<u8>,
    caveat_tag: Vec<u8>,
) -> HolderToken {
    let prev_lin = lineage_of(&tok.block0, &tok.hops);
    let mut hop = AttenuationBlock {
        rights: new_rights,
        expires_at: new_expires_at,
        next_holder_pk,
        caveat_tag,
        sig_bytes: Vec::new(),
    };
    hop.sig_bytes = scheme.sign(holder_sk, &hop_sign_msg(&prev_lin, &hop));
    let mut out = tok.clone();
    out.hops.push(hop);
    out
}

/// Verify `HolderToken` against pinned `issuer_pk`, canonical `RevocationSet` (checking every
/// ancestor prefix `0..=k`), and wall-clock `now`.
pub fn verify_token<S: PqSigBackend>(
    scheme: &S,
    issuer_pk: &[u8],
    rev_set: &RevocationSet,
    now: u64,
    tok: &HolderToken,
) -> Result<VerifiedAuthority, VerifyError> {
    if !constant_time_eq(&tok.block0.issuer_pk, issuer_pk) {
        return Err(VerifyError::IssuerKeyMismatch);
    }
    if !scheme.verify(issuer_pk, &tok.block0.sign_msg(), &tok.block0_sig) {
        return Err(VerifyError::InvalidBlock0Signature);
    }
    let mut cur_lineage = root_lineage(&tok.block0);
    if rev_set.contains(&lineage_nullifier(&cur_lineage)) {
        return Err(VerifyError::RevokedAtDepth(0));
    }
    let mut cur_holder_pk = tok.block0.holder_pk.as_slice();
    let mut cur_rights = tok.block0.rights;
    let mut cur_expires_at = tok.block0.expires_at;

    for (idx, hop) in tok.hops.iter().enumerate() {
        let depth = idx + 1;
        if !sub_mask(hop.rights, cur_rights) {
            return Err(VerifyError::RightsEscalation { hop: depth });
        }
        if hop.expires_at > cur_expires_at {
            return Err(VerifyError::ExpiryEscalation { hop: depth });
        }
        if !scheme.verify(cur_holder_pk, &hop_sign_msg(&cur_lineage, hop), &hop.sig_bytes) {
            return Err(VerifyError::InvalidHopSignature { hop: depth });
        }
        cur_lineage = step_lineage(&cur_lineage, hop);
        if rev_set.contains(&lineage_nullifier(&cur_lineage)) {
            return Err(VerifyError::RevokedAtDepth(depth));
        }
        cur_holder_pk = hop.next_holder_pk.as_slice();
        cur_rights = hop.rights;
        cur_expires_at = hop.expires_at;
    }

    if now > cur_expires_at {
        return Err(VerifyError::Expired);
    }

    Ok(VerifiedAuthority {
        subject: tok.block0.subject.clone(),
        rights: cur_rights,
        expires_at: cur_expires_at,
        attr_merkle_root: tok.block0.attr_merkle_root,
        tail_lineage: cur_lineage,
        tail_holder_pk: cur_holder_pk.to_vec(),
    })
}

/// Verify both the `HolderToken` chain and the selective attribute openings against
/// `block0.attr_merkle_root`.
pub fn verify_presentation<S: PqSigBackend>(
    scheme: &S,
    issuer_pk: &[u8],
    rev_set: &RevocationSet,
    now: u64,
    tok: &HolderToken,
    openings: &[SelectiveOpening],
) -> Result<VerifiedAuthority, VerifyError> {
    let va = verify_token(scheme, issuer_pk, rev_set, now, tok)?;
    if !verify_selective_disclosure(&va.attr_merkle_root, openings) {
        return Err(VerifyError::InvalidSelectiveDisclosure);
    }
    Ok(va)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wots_cshake256_roundtrip_and_tamper_rejection() {
        let scheme = WotsCshake256;
        let sk = b"test-pq-wots-seed-32-bytes-00001".to_vec();
        let pk = scheme.pk_of(&sk);
        let msg = b"hello post-quantum biscuit";
        let sig = scheme.sign(&sk, msg);
        assert_eq!(sig.len(), WOTS_SIG_LEN);
        assert!(scheme.verify(&pk, msg, &sig));
        assert!(!scheme.verify(&pk, b"hello post-quantum biscuiT", &sig));
        let mut bad_sig = sig.clone();
        bad_sig[0] ^= 0x01;
        assert!(!scheme.verify(&pk, msg, &bad_sig));
    }

    #[test]
    fn leb128_u256_matches_u64_for_small_values() {
        for v in [0u64, 1, 127, 128, 16383, 16384, u32::MAX as u64, u64::MAX] {
            let mut a = Vec::new();
            encode_leb128(v as usize, &mut a);
            let mut be = [0u8; 32];
            be[24..32].copy_from_slice(&v.to_be_bytes());
            let mut b = Vec::new();
            encode_leb128_u256(&be, &mut b);
            assert_eq!(a, b);
        }
    }
}
