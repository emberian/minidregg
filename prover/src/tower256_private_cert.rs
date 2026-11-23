//! Private-witness succinct `Tower256` + `cSHAKE256` content-bound DFA/count/bound certificates.
//!
//! Mirrors `Compiler/Tower256PrivateContentCert.lean` byte-for-byte on:
//! - `saltedContentCommit`: 248-bit random salt (`bytes[1..32]`) + record byte (`bytes[0]`) inside a
//!   `Tower256` (`Coordinate 8`) leaf under `cSHAKE256` `cubeRoot merkleDomainsC codecC`,
//! - `DfaTable::run_count` and all three `ClaimData` modes (`.accept`, `.count`, `.bound`),
//! - Masked execution trace `traceCommit` (`byte | state16 | next16 | cumCount32 | mask184`) and
//!   `cSHAKE256`-one-time-padded FRI level-0 evaluations (`blindTraceEval`),
//! - $O(N \log N)$ `Tower256` LCH Additive NTT low-degree extension (`ntt_inverse_in_place` +
//!   `ntt_forward_in_place`, matching `crate::additive_ntt` lifted to `Tower256`),
//! - `Tower256SuccinctCheck` (`receiptStream`) additive-FRI proving and standalone verification,
//! - Boundary + Fiat–Shamir sampled step/content/transition openings (`checkPrivate`), and
//! - Exact SP 800-185 `cSHAKE256` `Keccak-f[1600]` permutation accounting.

use std::sync::atomic::{AtomicU64, Ordering};

use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    CShake256, CShake256Core,
};

use crate::binary_tower_256::Tower256;
use crate::hash_kernels::cshake256_xof;

pub type Digest = [u8; 32];
pub type Salt248 = [u8; 31];
pub type RowMask = [u8; 23];

const LEAF_PREFIX: u8 = 0x01;
const LEAF_NAME: &[u8] = b"MINIDREGG/TOWER256/MERKLE/LEAF/V1";
const NODE_PREFIX: u8 = 0x02;
const NODE_NAME: &[u8] = b"MINIDREGG/TOWER256/MERKLE/NODE/V1";
const AUTOMATON_PREFIX: u8 = 0x05;
const AUTOMATON_NAME: &[u8] = b"MINIDREGG/TOWER256/CONTENTCERT/AUTOMATON/V1";
const ROWMASK_PREFIX: u8 = 0x06;
const ROWMASK_NAME: &[u8] = b"MINIDREGG/TOWER256/PRIVATECERT/ROWMASK/V1";
const STEPQ_PREFIX: u8 = 0x07;
const STEPQ_NAME: &[u8] = b"MINIDREGG/TOWER256/PRIVATECERT/STEPQ/V1";
const CHALLENGE_CUSTOMIZATION: &[u8] = b"MD-FRI-C";
const QUERY_CUSTOMIZATION: &[u8] = b"MD-FRI-Q";

const RECEIPT_MAGIC: &[u8; 8] = b"MDPCRT01";
const CSHAKE256_RATE: usize = 136;

static KECCAK_F_CALLS: AtomicU64 = AtomicU64::new(0);

/// Reset and read the global `Keccak-f[1600]` permutation counter.
pub fn reset_keccak_counter() {
    KECCAK_F_CALLS.store(0, Ordering::SeqCst);
}

pub fn keccak_f_count() -> u64 {
    KECCAK_F_CALLS.load(Ordering::SeqCst)
}

#[inline]
fn record_cshake256_keccak_blocks(customization_len: usize, input_len: usize) {
    // SP 800-185 cSHAKE256 with N="", non-empty S of length <= 130:
    // bytepad(encode_string("") || encode_string(S), 136) occupies exactly 1 block (136 bytes),
    // and `input` + 0x04..0x80 padding occupies `(input_len / 136) + 1` blocks; output is 32B <= 136B.
    let cust_blocks = if customization_len == 0 {
        0
    } else {
        let hdr = 2 + if customization_len * 8 < 256 { 2 } else { 3 } + customization_len;
        hdr.div_ceil(CSHAKE256_RATE).max(1)
    };
    let msg_blocks = (input_len / CSHAKE256_RATE) + 1;
    KECCAK_F_CALLS.fetch_add((cust_blocks + msg_blocks) as u64, Ordering::Relaxed);
}

#[inline]
fn xof32(customization: &[u8], input: &[u8]) -> Digest {
    record_cshake256_keccak_blocks(customization.len(), input.len());
    cshake256_xof(customization, input, 32)
        .try_into()
        .expect("32-byte digest")
}

fn prefixed_customization(prefix: u8, name: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(1 + name.len());
    out.push(prefix);
    out.extend_from_slice(name);
    out
}

/// Canonical `Nat.clog 2 n` (`depthOf` in Lean).
#[inline]
pub fn depth_of(n: usize) -> usize {
    if n <= 1 {
        0
    } else {
        (usize::BITS - (n - 1).leading_zeros()) as usize
    }
}

#[inline]
pub fn private_degree_schedule(record_length: usize, round: usize) -> usize {
    let td = depth_of(record_length).max(1);
    (1usize << td.saturating_sub(round)).max(1)
}

// ---------------------------------------------------------------------------------------------
// Errors & Core Data Types

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateCertError {
    EmptyRecord,
    InvalidDfa(&'static str),
    InvalidShape(&'static str),
    RandomnessLengthMismatch,
    ClaimNotSatisfied {
        claim: ClaimData,
        final_accepted: bool,
        run_count: usize,
    },
    SingularInterpolation,
    ZeroPivot(usize),
    MalformedWire(&'static str),
    VerificationFailed(&'static str),
}

impl core::fmt::Display for PrivateCertError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::EmptyRecord => write!(f, "record must be non-empty"),
            Self::InvalidDfa(msg) => write!(f, "invalid DFA table: {msg}"),
            Self::InvalidShape(msg) => write!(f, "invalid certificate shape: {msg}"),
            Self::RandomnessLengthMismatch => {
                write!(f, "salts and row_masks must match record length")
            }
            Self::ClaimNotSatisfied {
                claim,
                final_accepted,
                run_count,
            } => write!(
                f,
                "claim {claim:?} not satisfied (final_accepted={final_accepted}, run_count={run_count})"
            ),
            Self::SingularInterpolation => write!(f, "singular final polynomial interpolation"),
            Self::ZeroPivot(r) => write!(f, "zero FRI pivot at round {r}"),
            Self::MalformedWire(msg) => write!(f, "malformed receipt wire bytes: {msg}"),
            Self::VerificationFailed(msg) => write!(f, "private certificate verification failed: {msg}"),
        }
    }
}

impl std::error::Error for PrivateCertError {}

/// Mirrors `Tower256ContentCert.ClaimData`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClaimData {
    Accept(bool),
    Count(u64),
    Bound { lo: u64, hi: u64 },
}

impl ClaimData {
    #[inline]
    pub fn decide(self, final_accepted: bool, total_count: u64) -> bool {
        match self {
            Self::Accept(b) => final_accepted == b,
            Self::Count(n) => total_count == n,
            Self::Bound { lo, hi } => lo <= total_count && total_count <= hi,
        }
    }
}

/// Mirrors `Tower256ContentCert.DfaTable`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DfaTable {
    pub states: usize,
    pub initial: usize,
    pub accepting: Vec<bool>,
    pub delta: Vec<usize>,
}

impl DfaTable {
    pub fn validate(&self) -> Result<(), PrivateCertError> {
        if self.states == 0 || self.states > (1 << 16) {
            return Err(PrivateCertError::InvalidDfa("states out of 1..=65536"));
        }
        if self.initial >= self.states {
            return Err(PrivateCertError::InvalidDfa("initial >= states"));
        }
        if self.accepting.len() != self.states {
            return Err(PrivateCertError::InvalidDfa("accepting.len() != states"));
        }
        if self.delta.len() != self.states * 256 {
            return Err(PrivateCertError::InvalidDfa("delta.len() != states * 256"));
        }
        if self.delta.iter().any(|&nx| nx >= self.states) {
            return Err(PrivateCertError::InvalidDfa("transition target >= states"));
        }
        Ok(())
    }

    #[inline]
    pub fn step(&self, state: usize, byte: u8) -> usize {
        self.delta
            .get(256 * state + usize::from(byte))
            .copied()
            .unwrap_or(0)
    }

    #[inline]
    pub fn step_hit(&self, next_state: usize) -> u64 {
        u64::from(self.accepting.get(next_state).copied().unwrap_or(false))
    }

    /// Joint `(final_state, run_count)` execution over `word`.
    pub fn run_state_and_count(&self, word: &[u8]) -> (usize, u64) {
        let mut s = self.initial;
        let mut count = 0u64;
        for &b in word {
            s = self.step(s, b);
            count += self.step_hit(s);
        }
        (s, count)
    }

    pub fn run(&self, word: &[u8]) -> usize {
        self.run_state_and_count(word).0
    }

    pub fn accepts(&self, word: &[u8]) -> bool {
        let s = self.run(word);
        self.accepting.get(s).copied().unwrap_or(false)
    }

    pub fn run_count(&self, word: &[u8]) -> u64 {
        self.run_state_and_count(word).1
    }

    pub fn satisfies_claim(&self, claim: ClaimData, word: &[u8]) -> bool {
        let (final_s, count) = self.run_state_and_count(word);
        let acc = self.accepting.get(final_s).copied().unwrap_or(false);
        claim.decide(acc, count)
    }

    /// 4-state padded-complement DFA `neg(any* · "sk-" · any*)` (`noSkDash` in Lean).
    pub fn no_sk_dash() -> Self {
        let states = 4;
        let mut delta = vec![0usize; states * 256];
        for s in 0..states {
            for b in 0..256usize {
                delta[256 * s + b] = if s == 3 {
                    3
                } else if s == 2 && b == usize::from(b'-') {
                    3
                } else if s == 1 && b == usize::from(b'k') {
                    2
                } else if b == usize::from(b's') {
                    1
                } else {
                    0
                };
            }
        }
        Self {
            states,
            initial: 0,
            accepting: vec![true, true, true, false],
            delta,
        }
    }

    /// 5-state non-overlapping `"TODO"` matcher (`countTodo` in Lean).
    pub fn count_todo() -> Self {
        let states = 5;
        let mut delta = vec![0usize; states * 256];
        for s0 in 0..states {
            let s = if s0 == 4 { 0 } else { s0 };
            for b in 0..256usize {
                delta[256 * s0 + b] = if s == 3 && b == usize::from(b'O') {
                    4
                } else if s == 2 && b == usize::from(b'D') {
                    3
                } else if s == 1 && b == usize::from(b'O') {
                    2
                } else if b == usize::from(b'T') {
                    1
                } else {
                    0
                };
            }
        }
        Self {
            states,
            initial: 0,
            accepting: vec![false, false, false, false, true],
            delta,
        }
    }

    /// 9-state non-overlapping `"TODO"`-or-`"RULE"` governance marker counter.
    pub fn count_todo_or_rule() -> Self {
        // States:
        // 0: start
        // 1: "T", 2: "TO", 3: "TOD", 4: "TODO" (accept)
        // 5: "R", 6: "RU", 7: "RUL", 8: "RULE" (accept)
        let states = 9;
        let mut delta = vec![0usize; states * 256];
        for s0 in 0..states {
            let s = if s0 == 4 || s0 == 8 { 0 } else { s0 };
            for b in 0..256usize {
                delta[256 * s0 + b] = if s == 3 && b == usize::from(b'O') {
                    4
                } else if s == 2 && b == usize::from(b'D') {
                    3
                } else if s == 1 && b == usize::from(b'O') {
                    2
                } else if s == 7 && b == usize::from(b'E') {
                    8
                } else if s == 6 && b == usize::from(b'L') {
                    7
                } else if s == 5 && b == usize::from(b'U') {
                    6
                } else if b == usize::from(b'T') {
                    1
                } else if b == usize::from(b'R') {
                    5
                } else {
                    0
                };
            }
        }
        Self {
            states,
            initial: 0,
            accepting: vec![false, false, false, false, true, false, false, false, true],
            delta,
        }
    }
}

/// Public statement (`PrivateContentCert` in Lean).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateContentCert {
    pub content_root: Digest,
    pub record_length: usize,
    pub automaton_root: Digest,
    pub claim: ClaimData,
    pub fri_ell: usize,
    pub fri_rounds: usize,
    pub fri_queries: usize,
    pub step_queries: usize,
}

/// Compact automaton header carried in the receipt (`AutomatonHeader` in Lean).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AutomatonHeader {
    pub states: usize,
    pub initial: usize,
    pub accepting: Vec<bool>,
    pub delta_root: Digest,
}

/// Masked execution trace row (`TraceRow` in Lean).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TraceRow {
    pub byte: u8,
    pub state: u16,
    pub next: u16,
    pub cum_count: u32,
    pub mask: RowMask,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundaryOpenings {
    pub first_row: TraceRow,
    pub first_trace_path: Vec<Digest>,
    pub first_salt: Salt248,
    pub first_content_path: Vec<Digest>,
    pub first_delta_path: Vec<Digest>,
    pub first_fri_path: Vec<Digest>,
    pub last_row: TraceRow,
    pub last_trace_path: Vec<Digest>,
    pub last_salt: Salt248,
    pub last_content_path: Vec<Digest>,
    pub last_delta_path: Vec<Digest>,
    pub last_fri_path: Vec<Digest>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StepOpening {
    pub salt: Salt248,
    pub content_path: Vec<Digest>,
    pub row: TraceRow,
    pub trace_path: Vec<Digest>,
    pub delta_path: Vec<Digest>,
    pub fri_path: Vec<Digest>,
    pub next_row: TraceRow,
    pub next_trace_path: Vec<Digest>,
}

/// Succinct private-witness receipt (`PrivateReceipt` in Lean).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateReceipt {
    pub header: AutomatonHeader,
    pub trace_root: Digest,
    pub fri_initial_root: Digest,
    /// Canonical `Tower256SuccinctReceiptCodec` (`receiptStream`) wire bytes.
    pub fri_receipt_bytes: Vec<u8>,
    pub boundary: BoundaryOpenings,
    pub step_openings: Vec<StepOpening>,
}

// ---------------------------------------------------------------------------------------------
// Framing, Leaf Packing, & Dense Cube-Merkle Trees

#[inline]
fn encode_length(out: &mut Vec<u8>, n: usize) {
    out.resize(out.len() + n, 0);
    out.push(1);
}

#[inline]
fn envelope(out: &mut Vec<u8>, payload: &[u8]) {
    encode_length(out, payload.len());
    out.extend_from_slice(payload);
}

#[inline]
pub fn leaf_of_u64(v: u64) -> Tower256 {
    Tower256::from_limbs([v, 0, 0, 0])
}

#[inline]
pub fn pack_salted_leaf(byte: u8, salt: &Salt248) -> Tower256 {
    let mut buf = [0u8; 32];
    buf[0] = byte;
    buf[1..32].copy_from_slice(salt);
    Tower256::from_le_bytes(buf)
}

#[inline]
pub fn unpack_salted_leaf(c: Tower256) -> (u8, Salt248) {
    let bytes = c.to_le_bytes();
    let mut salt = [0u8; 31];
    salt.copy_from_slice(&bytes[1..32]);
    (bytes[0], salt)
}

#[inline]
pub fn pack_trace_row(r: &TraceRow) -> Tower256 {
    let mut buf = [0u8; 32];
    buf[0] = r.byte;
    buf[1..3].copy_from_slice(&r.state.to_le_bytes());
    buf[3..5].copy_from_slice(&r.next.to_le_bytes());
    buf[5..9].copy_from_slice(&r.cum_count.to_le_bytes());
    buf[9..32].copy_from_slice(&r.mask);
    Tower256::from_le_bytes(buf)
}

#[inline]
pub fn unpack_trace_row(c: Tower256) -> TraceRow {
    let buf = c.to_le_bytes();
    let byte = buf[0];
    let state = u16::from_le_bytes([buf[1], buf[2]]);
    let next = u16::from_le_bytes([buf[3], buf[4]]);
    let cum_count = u32::from_le_bytes([buf[5], buf[6], buf[7], buf[8]]);
    let mut mask = [0u8; 23];
    mask.copy_from_slice(&buf[9..32]);
    TraceRow {
        byte,
        state,
        next,
        cum_count,
        mask,
    }
}

#[inline]
pub fn row_payload_c8(r: &TraceRow) -> Tower256 {
    let mut buf = [0u8; 32];
    buf[0] = r.byte;
    buf[1..3].copy_from_slice(&r.state.to_le_bytes());
    buf[3..5].copy_from_slice(&r.next.to_le_bytes());
    buf[5..9].copy_from_slice(&r.cum_count.to_le_bytes());
    Tower256::from_le_bytes(buf)
}

pub fn blind_trace_eval(r: &TraceRow, rowmask_cust: &[u8]) -> Tower256 {
    let mut mask_buf = [0u8; 32];
    mask_buf[0..23].copy_from_slice(&r.mask);
    let pad = Tower256::from_le_bytes(xof32(rowmask_cust, &mask_buf));
    row_payload_c8(r).add(pad)
}

/// Precomputed bottom-up/strided `cubeRoot` Merkle tree matching Lean's `cubeRoot merkleDomainsC codecC`
/// in $O(N)$ leaf hashes + $O(N)$ node hashes (replacing $O(N \log N)$ repeated `root_at` calls!).
pub struct CubeMerkleTree {
    depth: usize,
    /// `layers[d]` has size `1 << d` in canonical strided order (`layers[depth]` = leaf digests,
    /// `layers[0][0]` = root). Wait: remember `cubeRoot` splits on bit 0 at the root!
    /// We store the exact `stride`-indexed subtree table so `path(idx)` is $O(\text{depth})$ lookups
    /// with ZERO extra hashing!
    nodes_by_level: Vec<Vec<Digest>>,
}

/// Compatibility entry points for callers of the private-certificate arithmetic API.
#[inline]
pub fn fast_mul256(lhs: Tower256, rhs: Tower256) -> Tower256 {
    lhs.mul(rhs)
}

#[inline]
pub fn fast_square256(x: Tower256) -> Tower256 {
    x.square()
}

#[inline]
pub fn fast_inverse256(x: Tower256) -> Result<Tower256, PrivateCertError> {
    x.inverse().map_err(|_| PrivateCertError::SingularInterpolation)
}

pub struct MerkleHasher {
    leaf_cust_len: usize,
    node_cust_len: usize,
    leaf_core: CShake256Core,
    node_core: CShake256Core,
}

impl MerkleHasher {
    pub fn new() -> Self {
        let leaf_cust = prefixed_customization(LEAF_PREFIX, LEAF_NAME);
        let node_cust = prefixed_customization(NODE_PREFIX, NODE_NAME);
        Self {
            leaf_cust_len: leaf_cust.len(),
            node_cust_len: node_cust.len(),
            leaf_core: CShake256Core::new(&leaf_cust),
            node_core: CShake256Core::new(&node_cust),
        }
    }

    #[inline]
    pub fn hash_leaf(&self, value: Tower256) -> Digest {
        // `0 :: encodeLength(32) ++ value.to_le_bytes()` = 1 + 33 + 32 = 66 stack bytes
        let mut input = [0u8; 66];
        input[33] = 1u8;
        input[34..66].copy_from_slice(&value.to_le_bytes());
        record_cshake256_keccak_blocks(self.leaf_cust_len, 66);
        let mut hasher = CShake256::from_core(self.leaf_core.clone());
        hasher.update(&input);
        let mut out = [0u8; 32];
        hasher.finalize_xof().read(&mut out);
        out
    }

    #[inline]
    pub fn hash_node(&self, left: &Digest, right: &Digest) -> Digest {
        // `1 :: (encodeLength(32) ++ left) ++ (encodeLength(32) ++ right)` = 1 + 65 + 65 = 131 stack bytes
        let mut input = [0u8; 131];
        input[0] = 1u8;
        input[33] = 1u8;
        input[34..66].copy_from_slice(left);
        input[98] = 1u8;
        input[99..131].copy_from_slice(right);
        record_cshake256_keccak_blocks(self.node_cust_len, 131);
        let mut hasher = CShake256::from_core(self.node_core.clone());
        hasher.update(&input);
        let mut out = [0u8; 32];
        hasher.finalize_xof().read(&mut out);
        out
    }

    /// Build the complete cube-Merkle tree over `1 << depth` leaves in exact `2^(depth+1) - 1` hashes.
    ///
    /// At level `lvl` (`0 <= lvl <= depth`, `stride = 1 << lvl`), `nodes_by_level[lvl]` has length
    /// `1 << lvl` and entry `offset < stride` equals `root_at(values, offset, stride)`!
    pub fn build_tree(&self, values: &[Tower256], depth: usize) -> CubeMerkleTree {
        let size = 1usize << depth;
        debug_assert_eq!(values.len(), size);
        let mut nodes_by_level: Vec<Vec<Digest>> = vec![Vec::new(); depth + 1];
        nodes_by_level[depth] = values.iter().map(|&v| self.hash_leaf(v)).collect();
        for lvl in (0..depth).rev() {
            let stride = 1usize << lvl;
            let mut cur = Vec::with_capacity(stride);
            let child = &nodes_by_level[lvl + 1];
            for offset in 0..stride {
                let l = &child[offset];
                let r = &child[offset + stride];
                cur.push(self.hash_node(l, r));
            }
            nodes_by_level[lvl] = cur;
        }
        CubeMerkleTree {
            depth,
            nodes_by_level,
        }
    }

    /// Verify `recompute merkleDomainsC (hashLeaf value) (binaryAddressBits depth idx) path == some root`.
    pub fn verify_leaf(
        &self,
        depth: usize,
        root: &Digest,
        idx: usize,
        value: Tower256,
        path: &[Digest],
    ) -> bool {
        if path.len() != depth || (depth < usize::BITS as usize && idx >= (1usize << depth)) {
            return false;
        }
        let mut acc = self.hash_leaf(value);
        for (bit_pos, sib) in path.iter().enumerate().rev() {
            acc = if (idx >> bit_pos) & 1 == 0 {
                self.hash_node(&acc, sib)
            } else {
                self.hash_node(sib, &acc)
            };
        }
        &acc == root
    }
}

impl Default for MerkleHasher {
    fn default() -> Self {
        Self::new()
    }
}

impl CubeMerkleTree {
    #[inline]
    pub fn root(&self) -> Digest {
        self.nodes_by_level[0][0]
    }

    /// Exact `cubePath` for `idx < (1 << depth)` in $O(\text{depth})$ array reads (zero hashes).
    pub fn path(&self, idx: usize) -> Vec<Digest> {
        let mut out = Vec::with_capacity(self.depth);
        let mut offset = 0usize;
        for lvl in 0..self.depth {
            let stride = 1usize << lvl;
            let child = &self.nodes_by_level[lvl + 1];
            if (idx & stride) == 0 {
                out.push(child[offset + stride]);
            } else {
                out.push(child[offset]);
                offset += stride;
            }
        }
        out
    }
}

fn build_dense_tree(hasher: &MerkleHasher, leaves: &[Tower256]) -> CubeMerkleTree {
    let d = depth_of(leaves.len());
    let size = 1usize << d;
    let mut padded = Vec::with_capacity(size);
    padded.extend_from_slice(leaves);
    padded.resize(size, Tower256::ZERO);
    hasher.build_tree(&padded, d)
}

/// Compute `saltedContentCommit(word, salts)` matching Lean's `saltedContentCommit`.
pub fn salted_content_commit(
    word: &[u8],
    salts: &[Salt248],
) -> Result<Digest, PrivateCertError> {
    if word.len() != salts.len() {
        return Err(PrivateCertError::RandomnessLengthMismatch);
    }
    let hasher = MerkleHasher::new();
    let leaves: Vec<Tower256> = word
        .iter()
        .zip(salts.iter())
        .map(|(&b, s)| pack_salted_leaf(b, s))
        .collect();
    Ok(build_dense_tree(&hasher, &leaves).root())
}

/// Compute `deltaCommit(dfa)` matching Lean's `deltaCommit`.
pub fn delta_commit(dfa: &DfaTable) -> Digest {
    let hasher = MerkleHasher::new();
    let leaves: Vec<Tower256> = dfa.delta.iter().map(|&nx| leaf_of_u64(nx as u64)).collect();
    build_dense_tree(&hasher, &leaves).root()
}

/// Compute `automatonHeaderCommit(hdr)` matching Lean's `automatonHeaderCommit`.
pub fn automaton_header_commit(hdr: &AutomatonHeader) -> Digest {
    let cust = prefixed_customization(AUTOMATON_PREFIX, AUTOMATON_NAME);
    let mut meta = Vec::new();
    envelope(&mut meta, &leaf_of_u64(hdr.states as u64).to_le_bytes());
    envelope(&mut meta, &leaf_of_u64(hdr.initial as u64).to_le_bytes());

    let accept_bytes: Vec<u8> = hdr
        .accepting
        .iter()
        .map(|&b| if b { 1u8 } else { 0u8 })
        .collect();
    let mut body = Vec::new();
    envelope(&mut body, &accept_bytes);
    envelope(&mut body, &hdr.delta_root);

    let mut input = Vec::new();
    envelope(&mut input, &meta);
    envelope(&mut input, &body);
    xof32(&cust, &input)
}

/// Compute `automatonCommit(dfa)` matching Lean's `automatonCommit`.
pub fn automaton_commit(dfa: &DfaTable) -> Digest {
    let hdr = AutomatonHeader {
        states: dfa.states,
        initial: dfa.initial,
        accepting: dfa.accepting.clone(),
        delta_root: delta_commit(dfa),
    };
    automaton_header_commit(&hdr)
}

// ---------------------------------------------------------------------------------------------
// $O(N \log N)$ Tower256 LCH Novel-Basis Additive NTT (lifted from `crate::additive_ntt`)

/// Canonical unit basis `beta[j] = Coord.ofNat 8 (2^j)` (`unitBasis` in Lean).
pub fn unit_basis(ell: usize) -> Vec<Tower256> {
    (0..ell)
        .map(|j| {
            let mut limbs = [0u64; 4];
            limbs[j / 64] = 1u64 << (j % 64);
            Tower256::from_limbs(limbs)
        })
        .collect()
}

#[inline]
fn subspace_vanishing_eval(gamma: &[Tower256], mut x: Tower256) -> Tower256 {
    for &coeff in gamma {
        x = x.square().add(coeff.mul(x));
    }
    x
}

fn compute_vanishing_constants(basis: &[Tower256]) -> Result<Vec<Tower256>, PrivateCertError> {
    let mut gamma = Vec::with_capacity(basis.len());
    for (i, &beta) in basis.iter().enumerate() {
        let v = subspace_vanishing_eval(&gamma, beta);
        if v.is_zero() {
            return Err(PrivateCertError::ZeroPivot(i));
        }
        gamma.push(v);
    }
    Ok(gamma)
}

fn ntt_forward_rec(data: &mut [Tower256], basis: &[Tower256], gamma: &[Tower256], offset: Tower256) {
    let Some(last) = basis.len().checked_sub(1) else {
        return;
    };
    let half = data.len() / 2;
    let at_offset = if offset.is_zero() {
        Tower256::ZERO
    } else {
        subspace_vanishing_eval(&gamma[..last], offset)
    };
    let at_right = at_offset.add(gamma[last]);
    if at_offset.is_zero() {
        for i in 0..half {
            let low = data[i];
            let high = data[half + i];
            data[half + i] = low.add(at_right.mul(high));
        }
    } else {
        for i in 0..half {
            let low = data[i];
            let high = data[half + i];
            let prod_l = at_offset.mul(high);
            data[i] = low.add(prod_l);
            data[half + i] = low.add(prod_l).add(gamma[last].mul(high));
        }
    }
    let right_offset = offset.add(basis[last]);
    let (left, right) = data.split_at_mut(half);
    ntt_forward_rec(left, &basis[..last], &gamma[..last], offset);
    ntt_forward_rec(right, &basis[..last], &gamma[..last], right_offset);
}

fn ntt_inverse_rec(
    data: &mut [Tower256],
    basis: &[Tower256],
    gamma: &[Tower256],
    inv_gamma: &[Tower256],
    offset: Tower256,
) {
    let Some(last) = basis.len().checked_sub(1) else {
        return;
    };
    let half = data.len() / 2;
    let right_offset = offset.add(basis[last]);
    let (left, right) = data.split_at_mut(half);
    ntt_inverse_rec(left, &basis[..last], &gamma[..last], &inv_gamma[..last], offset);
    ntt_inverse_rec(
        right,
        &basis[..last],
        &gamma[..last],
        &inv_gamma[..last],
        right_offset,
    );
    let at_offset = if offset.is_zero() {
        Tower256::ZERO
    } else {
        subspace_vanishing_eval(&gamma[..last], offset)
    };
    let inv_g = inv_gamma[last];
    if at_offset.is_zero() {
        for i in 0..half {
            let lv = left[i];
            let rv = right[i];
            right[i] = lv.add(rv).mul(inv_g);
        }
    } else {
        for i in 0..half {
            let lv = left[i];
            let rv = right[i];
            let high = lv.add(rv).mul(inv_g);
            left[i] = lv.add(at_offset.mul(high));
            right[i] = high;
        }
    }
}

/// Evaluate LCH novel-basis `Tower256` coefficients on `offset + span(basis)` in $O(N \log N)$.
pub fn ntt_forward_in_place(
    coeffs: &mut [Tower256],
    basis: &[Tower256],
    offset: Tower256,
) -> Result<(), PrivateCertError> {
    let gamma = compute_vanishing_constants(basis)?;
    ntt_forward_rec(coeffs, basis, &gamma, offset);
    Ok(())
}

/// Interpolate evaluations on `offset + span(basis)` into LCH novel-basis coefficients in $O(N \log N)$.
pub fn ntt_inverse_in_place(
    evals: &mut [Tower256],
    basis: &[Tower256],
    offset: Tower256,
) -> Result<(), PrivateCertError> {
    let gamma = compute_vanishing_constants(basis)?;
    let inv_gamma = gamma
        .iter()
        .enumerate()
        .map(|(i, &g)| g.inverse().map_err(|_| PrivateCertError::ZeroPivot(i)))
        .collect::<Result<Vec<_>, _>>()?;
    ntt_inverse_rec(evals, basis, &gamma, &inv_gamma, offset);
    Ok(())
}

/// Low-degree extend `base_evals` (length `1 << td` on `span(beta[..td])`) to `1 << fri_ell` on
/// `span(beta[..fri_ell])` in $O(2^{\text{fri\_ell}} \cdot \text{fri\_ell})$ operations.
pub fn low_degree_extend_unit_basis(
    base_evals: &[Tower256],
    td: usize,
    fri_ell: usize,
) -> Result<Vec<Tower256>, PrivateCertError> {
    let beta = unit_basis(fri_ell);
    let mut coeffs = base_evals.to_vec();
    ntt_inverse_in_place(&mut coeffs, &beta[..td], Tower256::ZERO)?;
    coeffs.resize(1usize << fri_ell, Tower256::ZERO);
    ntt_forward_in_place(&mut coeffs, &beta[..fri_ell], Tower256::ZERO)?;
    Ok(coeffs)
}

// ---------------------------------------------------------------------------------------------
// StreamCodec Wire Helpers (`Theory/StreamCodec.lean` + `Tower256SuccinctReceiptCodec.lean`)

fn encode_nat_255(out: &mut Vec<u8>, mut value: u128) {
    while value > 0 {
        out.push((value % 255) as u8);
        value /= 255;
    }
    out.push(255);
}

fn encode_digest_stream(out: &mut Vec<u8>, bytes: &Digest) {
    let mut limbs: Vec<u32> = bytes
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect();
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

struct StreamReader<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> StreamReader<'a> {
    fn byte(&mut self) -> Result<u8, PrivateCertError> {
        let b = *self
            .bytes
            .get(self.pos)
            .ok_or(PrivateCertError::MalformedWire("truncated"))?;
        self.pos += 1;
        Ok(b)
    }

    fn take(&mut self, n: usize) -> Result<&'a [u8], PrivateCertError> {
        let end = self
            .pos
            .checked_add(n)
            .ok_or(PrivateCertError::MalformedWire("length overflow"))?;
        let s = self
            .bytes
            .get(self.pos..end)
            .ok_or(PrivateCertError::MalformedWire("truncated slice"))?;
        self.pos = end;
        Ok(s)
    }

    fn nat_usize(&mut self) -> Result<usize, PrivateCertError> {
        let mut digits = Vec::new();
        loop {
            let b = self.byte()?;
            if b == 255 {
                break;
            }
            digits.push(b);
        }
        if digits.last() == Some(&0) {
            return Err(PrivateCertError::MalformedWire("non-canonical base-255 nat"));
        }
        let mut val: usize = 0;
        for &d in digits.iter().rev() {
            val = val
                .checked_mul(255)
                .and_then(|v| v.checked_add(usize::from(d)))
                .ok_or(PrivateCertError::MalformedWire("nat overflow"))?;
        }
        Ok(val)
    }

    fn digest_stream(&mut self) -> Result<Digest, PrivateCertError> {
        let mut digits = Vec::new();
        loop {
            let b = self.byte()?;
            if b == 255 {
                break;
            }
            digits.push(b);
        }
        if digits.last() == Some(&0) {
            return Err(PrivateCertError::MalformedWire("non-canonical digest nat"));
        }
        // Accumulate into 8 u32 limbs (256-bit LE).
        let mut limbs = [0u32; 8];
        for &d in digits.iter().rev() {
            let mut carry = u64::from(d);
            for limb in &mut limbs {
                let cur = u64::from(*limb) * 255 + carry;
                *limb = cur as u32;
                carry = cur >> 32;
            }
            if carry != 0 {
                return Err(PrivateCertError::MalformedWire("digest >= 2^256"));
            }
        }
        let mut out = [0u8; 32];
        for (chunk, &limb) in out.chunks_exact_mut(4).zip(limbs.iter()) {
            chunk.copy_from_slice(&limb.to_le_bytes());
        }
        Ok(out)
    }

    fn c8(&mut self) -> Result<Tower256, PrivateCertError> {
        let s = self.take(32)?;
        Ok(Tower256::from_le_bytes(s.try_into().expect("32B")))
    }

    fn merkle_path_stream(&mut self) -> Result<Vec<Digest>, PrivateCertError> {
        let n = self.nat_usize()?;
        if n > 256 {
            return Err(PrivateCertError::MalformedWire("merkle path too deep"));
        }
        (0..n).map(|_| self.digest_stream()).collect()
    }
}

// ---------------------------------------------------------------------------------------------
// Decoded `CReceipt` & Fast $O(N \log N)$ Additive-FRI Prover / Standalone Verifier

#[derive(Clone, Debug, PartialEq, Eq)]
struct CPairOpening {
    left: Tower256,
    right: Tower256,
    pair_path: Vec<Digest>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct DecodedFriReceipt {
    roots: Vec<Digest>,
    challenges: Vec<Tower256>,
    query_seeds: Vec<usize>,
    openings: Vec<Vec<CPairOpening>>,
    final_coeffs: Vec<Tower256>,
}

fn decode_fri_receipt(
    bytes: &[u8],
    ell: usize,
    m: usize,
    query_count: usize,
) -> Result<DecodedFriReceipt, PrivateCertError> {
    let mut r = StreamReader { bytes, pos: 0 };
    let n_roots = r.nat_usize()?;
    if n_roots != m + 1 {
        return Err(PrivateCertError::MalformedWire("wrong FRI roots count"));
    }
    let roots = (0..n_roots)
        .map(|_| r.digest_stream())
        .collect::<Result<Vec<_>, _>>()?;
    let n_ch = r.nat_usize()?;
    if n_ch != m {
        return Err(PrivateCertError::MalformedWire("wrong FRI challenges count"));
    }
    let challenges = (0..m).map(|_| r.c8()).collect::<Result<Vec<_>, _>>()?;
    let n_seeds = r.nat_usize()?;
    if n_seeds != query_count {
        return Err(PrivateCertError::MalformedWire("wrong FRI seeds count"));
    }
    let seed_bound = 1usize << ell.saturating_sub(1);
    let mut query_seeds = Vec::with_capacity(query_count);
    for _ in 0..query_count {
        let s = r.nat_usize()?;
        if s >= seed_bound {
            return Err(PrivateCertError::MalformedWire("FRI seed out of bounds"));
        }
        query_seeds.push(s);
    }
    let n_rounds = r.nat_usize()?;
    if n_rounds != m {
        return Err(PrivateCertError::MalformedWire("wrong FRI opening rounds"));
    }
    let mut openings = Vec::with_capacity(m);
    for _ in 0..m {
        let n_q = r.nat_usize()?;
        if n_q != query_count {
            return Err(PrivateCertError::MalformedWire("wrong FRI round query count"));
        }
        let mut round_ops = Vec::with_capacity(query_count);
        for _ in 0..query_count {
            let left = r.c8()?;
            let right = r.c8()?;
            let pair_path = r.merkle_path_stream()?;
            round_ops.push(CPairOpening {
                left,
                right,
                pair_path,
            });
        }
        openings.push(round_ops);
    }
    let n_final = r.nat_usize()?;
    if n_final > (1usize << (ell - m)) {
        return Err(PrivateCertError::MalformedWire("too many final coeffs"));
    }
    let final_coeffs = (0..n_final).map(|_| r.c8()).collect::<Result<Vec<_>, _>>()?;
    if r.pos != bytes.len() {
        return Err(PrivateCertError::MalformedWire("trailing bytes in FRI receipt"));
    }
    Ok(DecodedFriReceipt {
        roots,
        challenges,
        query_seeds,
        openings,
        final_coeffs,
    })
}

fn eval_monomial_coeffs(cs: &[Tower256], x: Tower256) -> Tower256 {
    cs.iter()
        .rev()
        .fold(Tower256::ZERO, |acc, &c| c.add(x.mul(acc)))
}

fn gauss_interpolate(points: &[(Tower256, Tower256)]) -> Result<Vec<Tower256>, PrivateCertError> {
    let n = points.len();
    let mut rows: Vec<Vec<Tower256>> = points
        .iter()
        .map(|&(x, y)| {
            let mut row = Vec::with_capacity(n + 1);
            let mut p = Tower256::ONE;
            for _ in 0..n {
                row.push(p);
                p = p.mul(x);
            }
            row.push(y);
            row
        })
        .collect();
    for col in 0..n {
        let p = (col..n)
            .find(|&r| !rows[r][col].is_zero())
            .ok_or(PrivateCertError::SingularInterpolation)?;
        rows.swap(p, col);
        let inv = rows[col][col]
            .inverse()
            .map_err(|_| PrivateCertError::SingularInterpolation)?;
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

#[inline]
fn apply_pivots(pivots: &[Tower256], x: Tower256) -> Tower256 {
    pivots
        .iter()
        .fold(x, |y, &p| y.square().add(p.mul(y)))
}

#[inline]
fn raw_domain_point(beta: &[Tower256], offset: Tower256, k: usize, index: usize) -> Tower256 {
    (0..k)
        .filter(|&i| (index >> i) & 1 == 1)
        .fold(offset, |acc, i| acc.add(beta[i]))
}

#[inline]
fn dom_point(
    beta: &[Tower256],
    offset: Tower256,
    ell: usize,
    round: usize,
    pivots: &[Tower256],
    index: usize,
) -> Tower256 {
    apply_pivots(pivots, raw_domain_point(beta, offset, ell - round, index))
}

/// Tabulate `dom_point(0..1 << bits)` in `1 << bits` XORs (`0` multiplications per element!) via
/// $\mathbb{F}_2$-linearity of `apply_pivots`.
fn tabulate_subspace_domain(
    beta: &[Tower256],
    offset: Tower256,
    bits: usize,
    pivots: &[Tower256],
) -> Vec<Tower256> {
    let size = 1usize << bits;
    let mut dom = Vec::with_capacity(size);
    dom.push(apply_pivots(pivots, offset));
    for b in 0..bits {
        let img = apply_pivots(pivots, beta[b]);
        let cur_len = dom.len();
        for idx in 0..cur_len {
            dom.push(dom[idx].add(img));
        }
    }
    dom
}

fn basis_prefix_bytes(ell: usize, m: usize, beta: &[Tower256], offset: Tower256) -> Vec<u8> {
    let mut out = Vec::new();
    let mut tmp = Vec::new();
    encode_length(&mut tmp, ell);
    envelope(&mut out, &tmp);
    tmp.clear();
    encode_length(&mut tmp, m);
    envelope(&mut out, &tmp);
    envelope(&mut out, &offset.to_le_bytes());
    for (i, b) in beta.iter().enumerate() {
        let mut inner = Vec::new();
        tmp.clear();
        encode_length(&mut tmp, i);
        envelope(&mut inner, &tmp);
        envelope(&mut inner, &b.to_le_bytes());
        envelope(&mut out, &inner);
    }
    out
}

fn roots_transcript_bytes(head: &[u8], roots: &[Digest], upto: usize) -> Vec<u8> {
    let mut out = head.to_vec();
    let mut tmp = Vec::new();
    for (n, root) in roots.iter().enumerate().take(upto + 1) {
        tmp.clear();
        encode_length(&mut tmp, n);
        envelope(&mut out, &tmp);
        envelope(&mut out, root);
    }
    out
}

struct FriProveOutput {
    word0_tree: CubeMerkleTree,
    initial_root: Digest,
    roots: Vec<Digest>,
    challenges: Vec<Tower256>,
    receipt_bytes: Vec<u8>,
}

/// Fast $O(2^\ell)$ additive-FRI prover directly over an already-evaluated level-0 word `word0`
/// (produced by our $O(N \log N)$ `Tower256` LCH Additive NTT), emitting canonical `receiptStream`
/// bytes identical to `Tower256SuccinctProver.prove` + `Tower256SuccinctReceiptCodec`.
fn prove_fri_from_word0(
    hasher: &MerkleHasher,
    statement_bytes: &[u8],
    ell: usize,
    m: usize,
    query_count: usize,
    final_degree: usize,
    word0: Vec<Tower256>,
) -> Result<FriProveOutput, PrivateCertError> {
    let beta = unit_basis(ell);
    let offset = Tower256::ZERO;
    let last_size = 1usize << (ell - m);
    if final_degree > last_size {
        return Err(PrivateCertError::InvalidShape("final_degree > last_size"));
    }

    let mut head = Vec::new();
    envelope(&mut head, statement_bytes);
    envelope(&mut head, &basis_prefix_bytes(ell, m, &beta, offset));

    let word0_tree = hasher.build_tree(&word0, ell);
    let root0 = word0_tree.root();

    let mut words: Vec<Vec<Tower256>> = Vec::with_capacity(m + 1);
    words.push(word0);
    let mut trees: Vec<Option<CubeMerkleTree>> = Vec::with_capacity(m);
    let mut roots: Vec<Digest> = Vec::with_capacity(m + 2);
    roots.push(root0);
    let mut challenges: Vec<Tower256> = Vec::with_capacity(m);
    let mut pivots: Vec<Tower256> = Vec::with_capacity(m);

    for j in 0..m {
        let input = roots_transcript_bytes(&head, &roots, j);
        let alpha = Tower256::from_le_bytes(xof32(CHALLENGE_CUSTOMIZATION, &input));
        let pivot = apply_pivots(&pivots, beta[(ell - 1).saturating_sub(j)]);
        let pinv = pivot.inverse().map_err(|_| PrivateCertError::ZeroPivot(j))?;
        let half = 1usize << (ell - j - 1);
        let dom_lo = tabulate_subspace_domain(&beta, offset, ell - j - 1, &pivots);
        let w = &words[j];
        let mut next = Vec::with_capacity(half);
        for k in 0..half {
            let (left, right) = (w[k], w[k + half]);
            let t1 = dom_lo[k].add(alpha).mul(left.add(right));
            next.push(left.add(t1.mul(pinv)));
        }
        challenges.push(alpha);
        pivots.push(pivot);
        if j + 1 < m {
            let t = hasher.build_tree(&next, ell - (j + 1));
            roots.push(t.root());
            trees.push(Some(t));
        } else {
            trees.push(None);
        }
        words.push(next);
    }

    let wm = &words[m];
    let dom_last = tabulate_subspace_domain(&beta, offset, ell - m, &pivots);
    let points: Vec<(Tower256, Tower256)> = (0..final_degree)
        .map(|n| (dom_last[n % last_size], wm[n]))
        .collect();
    let final_coeffs = gauss_interpolate(&points)?;
    let last_word: Vec<Tower256> = (0..last_size)
        .map(|i| eval_monomial_coeffs(&final_coeffs, dom_last[i]))
        .collect();
    let last_tree = hasher.build_tree(&last_word, ell - m);
    roots.push(last_tree.root());

    let mut prefix = roots_transcript_bytes(&head, &roots, m);
    for c in &challenges {
        envelope(&mut prefix, &c.to_le_bytes());
    }
    let seed_bits = ell - 1;
    let seeds: Vec<usize> = (0..query_count)
        .map(|a| {
            let mut input = prefix.clone();
            let mut tmp = Vec::new();
            encode_length(&mut tmp, a);
            envelope(&mut input, &tmp);
            let d = xof32(QUERY_CUSTOMIZATION, &input);
            let mut low = [0u8; 8];
            low.copy_from_slice(&d[..8]);
            let v = u64::from_le_bytes(low);
            (if seed_bits >= 64 {
                v
            } else {
                v & ((1u64 << seed_bits) - 1)
            }) as usize
        })
        .collect();

    let mut out = Vec::new();
    let receipt_roots: Vec<Digest> = roots.iter().copied().take(m + 1).collect();
    encode_nat_255(&mut out, (m + 1) as u128);
    for r in &receipt_roots {
        encode_digest_stream(&mut out, r);
    }
    encode_nat_255(&mut out, m as u128);
    for c in &challenges {
        out.extend_from_slice(&c.to_le_bytes());
    }
    encode_nat_255(&mut out, query_count as u128);
    for &s in &seeds {
        encode_nat_255(&mut out, s as u128);
    }
    encode_nat_255(&mut out, m as u128);
    for j in 0..m {
        encode_nat_255(&mut out, query_count as u128);
        let w = &words[j];
        let half = 1usize << (ell - j - 1);
        for &s in &seeds {
            let k = s % half;
            out.extend_from_slice(&w[k].to_le_bytes());
            out.extend_from_slice(&w[k + half].to_le_bytes());
            let mut path = if j == 0 {
                word0_tree.path(k)
            } else {
                trees[j - 1].as_ref().expect("tree j").path(k)
            };
            path.pop();
            encode_nat_255(&mut out, path.len() as u128);
            for d in &path {
                encode_digest_stream(&mut out, d);
            }
        }
    }
    encode_nat_255(&mut out, final_coeffs.len() as u128);
    for c in &final_coeffs {
        out.extend_from_slice(&c.to_le_bytes());
    }

    Ok(FriProveOutput {
        word0_tree,
        initial_root: root0,
        roots: receipt_roots,
        challenges,
        receipt_bytes: out,
    })
}

/// Standalone Rust mirror of `Tower256SuccinctCheck.check`.
fn verify_fri_receipt(
    hasher: &MerkleHasher,
    statement_bytes: &[u8],
    ell: usize,
    m: usize,
    _query_count: usize,
    initial_root: &Digest,
    final_degree_bound: usize,
    decoded: &DecodedFriReceipt,
) -> Result<(), PrivateCertError> {
    if &decoded.roots[0] != initial_root {
        return Err(PrivateCertError::VerificationFailed("FRI root[0] != friInitialRoot"));
    }
    if decoded.final_coeffs.len() > final_degree_bound {
        return Err(PrivateCertError::VerificationFailed("FRI finalCoeffs exceeds degree bound"));
    }
    let beta = unit_basis(ell);
    let offset = Tower256::ZERO;
    let mut head = Vec::new();
    envelope(&mut head, statement_bytes);
    envelope(&mut head, &basis_prefix_bytes(ell, m, &beta, offset));

    let mut pivots = Vec::with_capacity(m);
    for j in 0..m {
        let input = roots_transcript_bytes(&head, &decoded.roots, j);
        let expected_alpha = Tower256::from_le_bytes(xof32(CHALLENGE_CUSTOMIZATION, &input));
        if decoded.challenges[j] != expected_alpha {
            return Err(PrivateCertError::VerificationFailed("FRI Fiat-Shamir challenge mismatch"));
        }
        let pivot = apply_pivots(&pivots, beta[(ell - 1).saturating_sub(j)]);
        pivots.push(pivot);
    }

    // Recompute lastRootC from `final_coeffs`
    let last_size = 1usize << (ell - m);
    let last_word: Vec<Tower256> = (0..last_size)
        .map(|i| eval_monomial_coeffs(&decoded.final_coeffs, dom_point(&beta, offset, ell, m, &pivots, i)))
        .collect();
    let expected_last_root = hasher.build_tree(&last_word, ell - m).root();
    if decoded.roots[m] != expected_last_root {
        return Err(PrivateCertError::VerificationFailed("FRI lastRootC mismatch"));
    }

    // Verify query seeds
    let mut prefix = roots_transcript_bytes(&head, &decoded.roots, m);
    for c in &decoded.challenges {
        envelope(&mut prefix, &c.to_le_bytes());
    }
    let seed_bits = ell - 1;
    for (a, &seed) in decoded.query_seeds.iter().enumerate() {
        let mut input = prefix.clone();
        let mut tmp = Vec::new();
        encode_length(&mut tmp, a);
        envelope(&mut input, &tmp);
        let d = xof32(QUERY_CUSTOMIZATION, &input);
        let mut low = [0u8; 8];
        low.copy_from_slice(&d[..8]);
        let v = u64::from_le_bytes(low);
        let expected_seed = (if seed_bits >= 64 {
            v
        } else {
            v & ((1u64 << seed_bits) - 1)
        }) as usize;
        if seed != expected_seed {
            return Err(PrivateCertError::VerificationFailed("FRI query seed mismatch"));
        }
    }

    // Verify per-round pair openings and multiplied-out fold equation (`openedC`)
    let mut round_pivots: Vec<Tower256> = Vec::with_capacity(m);
    for j in 0..m {
        let pivot_j = apply_pivots(&round_pivots, beta[(ell - 1).saturating_sub(j)]);
        let half = 1usize << (ell - j - 1);
        for (a, &seed) in decoded.query_seeds.iter().enumerate() {
            let k = seed % half;
            let op = &decoded.openings[j][a];
            let mut left_full = op.pair_path.clone();
            left_full.push(hasher.hash_leaf(op.right));
            if !hasher.verify_leaf(ell - j, &decoded.roots[j], k, op.left, &left_full) {
                return Err(PrivateCertError::VerificationFailed("FRI pair Merkle path invalid"));
            }
            let next_val = if j + 1 < m {
                let half_next = 1usize << (ell - (j + 1) - 1);
                let top_bit = (k >> (ell - (j + 1) - 1)) & 1;
                let next_op = &decoded.openings[j + 1][a];
                debug_assert_eq!(k % half_next, seed % half_next);
                if top_bit == 0 {
                    next_op.left
                } else {
                    next_op.right
                }
            } else {
                last_word[k]
            };
            let dom_lo = dom_point(&beta, offset, ell, j, &round_pivots, k);
            let lhs = next_val.add(op.left).mul(pivot_j);
            let rhs = dom_lo
                .add(decoded.challenges[j])
                .mul(op.left.add(op.right));
            if lhs != rhs {
                return Err(PrivateCertError::VerificationFailed("FRI fold equation failed"));
            }
        }
        round_pivots.push(pivot_j);
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// Private Certificate Transcript, Prover, & Verifier

fn claim_bytes(claim: ClaimData) -> Vec<u8> {
    let mut out = Vec::new();
    match claim {
        ClaimData::Accept(b) => {
            out.push(0);
            out.push(if b { 1 } else { 0 });
        }
        ClaimData::Count(n) => {
            out.push(1);
            out.extend_from_slice(&leaf_of_u64(n).to_le_bytes());
        }
        ClaimData::Bound { lo, hi } => {
            out.push(2);
            out.extend_from_slice(&leaf_of_u64(lo).to_le_bytes());
            out.extend_from_slice(&leaf_of_u64(hi).to_le_bytes());
        }
    }
    out
}

pub fn private_statement_bytes(stmt: &PrivateContentCert, trace_root: &Digest) -> Vec<u8> {
    let mut out = Vec::with_capacity(640);
    envelope(&mut out, &stmt.content_root);
    envelope(&mut out, &leaf_of_u64(stmt.record_length as u64).to_le_bytes());
    envelope(&mut out, &stmt.automaton_root);
    envelope(&mut out, &claim_bytes(stmt.claim));
    envelope(&mut out, &leaf_of_u64(stmt.fri_ell as u64).to_le_bytes());
    envelope(&mut out, &leaf_of_u64(stmt.fri_rounds as u64).to_le_bytes());
    envelope(&mut out, &leaf_of_u64(stmt.fri_queries as u64).to_le_bytes());
    envelope(&mut out, &leaf_of_u64(stmt.step_queries as u64).to_le_bytes());
    envelope(&mut out, trace_root);
    out
}

fn step_transcript_prefix(
    stmt: &PrivateContentCert,
    trace_root: &Digest,
    fri_roots: &[Digest],
    fri_challenges: &[Tower256],
) -> Vec<u8> {
    let mut out = Vec::new();
    envelope(&mut out, &private_statement_bytes(stmt, trace_root));
    let mut roots_buf = Vec::new();
    for r in fri_roots {
        envelope(&mut roots_buf, r);
    }
    envelope(&mut out, &roots_buf);
    let mut ch_buf = Vec::new();
    for c in fri_challenges {
        envelope(&mut ch_buf, &c.to_le_bytes());
    }
    envelope(&mut out, &ch_buf);
    out
}

fn derive_step_index(
    stepq_cust: &[u8],
    prefix: &[u8],
    record_length: usize,
    u: usize,
) -> usize {
    if record_length == 0 {
        return 0;
    }
    let mut input = Vec::with_capacity(prefix.len() + 66);
    input.extend_from_slice(prefix);
    envelope(&mut input, &leaf_of_u64(u as u64).to_le_bytes());
    let d = xof32(stepq_cust, &input);
    // `d.value % record_length` where `d.value` is the 256-bit LE integer of `d`.
    let mut rem: u128 = 0;
    let m = record_length as u128;
    for chunk in d.chunks_exact(8).rev() {
        let limb = u64::from_le_bytes(chunk.try_into().expect("8B")) as u128;
        rem = (((rem << 64) % m) + (limb % m)) % m;
    }
    rem as usize
}

/// Deterministic cSHAKE256 CSPRNG stream for generating 248-bit salts and 184-bit row masks from a 32-byte seed.
pub fn expand_randomness(seed: &Digest, len: usize) -> (Vec<Salt248>, Vec<RowMask>) {
    let cust_s = b"MINIDREGG/PRIVATECERT/SALTGEN/V1";
    let cust_m = b"MINIDREGG/PRIVATECERT/MASKGEN/V1";
    let mut salts = Vec::with_capacity(len);
    let mut masks = Vec::with_capacity(len);
    for i in 0..len {
        let mut inp = [0u8; 40];
        inp[..32].copy_from_slice(seed);
        inp[32..40].copy_from_slice(&(i as u64).to_le_bytes());
        let ds: Digest = cshake256_xof(cust_s, &inp, 32).try_into().expect("32B");
        let dm: Digest = cshake256_xof(cust_m, &inp, 32).try_into().expect("32B");
        let mut s = [0u8; 31];
        s.copy_from_slice(&ds[..31]);
        let mut m = [0u8; 23];
        m.copy_from_slice(&dm[..23]);
        salts.push(s);
        masks.push(m);
    }
    (salts, masks)
}

/// Build the canonical masked execution trace rows (`buildTraceRows` in Lean).
pub fn build_trace_rows(dfa: &DfaTable, word: &[u8], row_masks: &[RowMask]) -> Vec<TraceRow> {
    let mut s = dfa.initial;
    let mut cum_count = 0u32;
    let mut out = Vec::with_capacity(word.len());
    for (i, &b) in word.iter().enumerate() {
        let nx = dfa.step(s, b);
        let mask = row_masks.get(i).copied().unwrap_or([0u8; 23]);
        out.push(TraceRow {
            byte: b,
            state: s as u16,
            next: nx as u16,
            cum_count,
            mask,
        });
        cum_count = cum_count.saturating_add(dfa.step_hit(nx) as u32);
        s = nx;
    }
    out
}

/// Prove a private content certificate with explicit `(salts, row_masks)` (used both in production
/// after `expand_randomness` and in Lean bit-exact conformance tests).
pub fn prove_private_with_randomness(
    dfa: &DfaTable,
    word: &[u8],
    salts: &[Salt248],
    row_masks: &[RowMask],
    claim: ClaimData,
    fri_ell: usize,
    fri_rounds: usize,
    fri_queries: usize,
    step_queries: usize,
) -> Result<(PrivateContentCert, PrivateReceipt), PrivateCertError> {
    dfa.validate()?;
    if word.is_empty() {
        return Err(PrivateCertError::EmptyRecord);
    }
    if (word.len() as u64) > (1u64 << 32) {
        return Err(PrivateCertError::InvalidShape("record_length > 2^32"));
    }
    if salts.len() != word.len() || row_masks.len() != word.len() {
        return Err(PrivateCertError::RandomnessLengthMismatch);
    }
    let rec_depth = depth_of(word.len());
    let td = rec_depth.max(1);
    if fri_rounds > fri_ell
        || fri_ell > 24
        || td >= fri_ell
        || fri_queries > 4096
        || step_queries > 4096
    {
        return Err(PrivateCertError::InvalidShape(
            "require fri_rounds <= fri_ell <= 24, max(1, depth_of(record_length)) < fri_ell, queries <= 4096",
        ));
    }
    let (final_s, run_cnt) = dfa.run_state_and_count(word);
    let final_acc = dfa.accepting[final_s];
    if !claim.decide(final_acc, run_cnt) {
        return Err(PrivateCertError::ClaimNotSatisfied {
            claim,
            final_accepted: final_acc,
            run_count: run_cnt as usize,
        });
    }

    let hasher = MerkleHasher::new();
    let rowmask_cust = prefixed_customization(ROWMASK_PREFIX, ROWMASK_NAME);
    let stepq_cust = prefixed_customization(STEPQ_PREFIX, STEPQ_NAME);

    let rows = build_trace_rows(dfa, word, row_masks);

    let salted_leaves: Vec<Tower256> = word
        .iter()
        .zip(salts.iter())
        .map(|(&b, s)| pack_salted_leaf(b, s))
        .collect();
    let content_tree = build_dense_tree(&hasher, &salted_leaves);
    let content_root = content_tree.root();

    let trace_leaves: Vec<Tower256> = rows.iter().map(pack_trace_row).collect();
    let trace_tree = build_dense_tree(&hasher, &trace_leaves);
    let trace_root = trace_tree.root();

    let delta_leaves: Vec<Tower256> = dfa.delta.iter().map(|&nx| leaf_of_u64(nx as u64)).collect();
    let delta_tree = build_dense_tree(&hasher, &delta_leaves);
    let header = AutomatonHeader {
        states: dfa.states,
        initial: dfa.initial,
        accepting: dfa.accepting.clone(),
        delta_root: delta_tree.root(),
    };
    let automaton_root = automaton_header_commit(&header);

    // Build blinded level-0 trace evaluations on `0..2^td` and LDE to `0..2^fri_ell` via $O(N \log N)$ Additive NTT!
    let base_len = 1usize << td;
    let mut base_evals = Vec::with_capacity(base_len);
    for row in &rows {
        base_evals.push(blind_trace_eval(row, &rowmask_cust));
    }
    base_evals.resize(base_len, Tower256::ZERO);
    let word0 = low_degree_extend_unit_basis(&base_evals, td, fri_ell)?;

    let stmt = PrivateContentCert {
        content_root,
        record_length: word.len(),
        automaton_root,
        claim,
        fri_ell,
        fri_rounds,
        fri_queries,
        step_queries,
    };
    let stmt_bytes = private_statement_bytes(&stmt, &trace_root);
    let final_degree = private_degree_schedule(word.len(), fri_rounds);
    let fri_out = prove_fri_from_word0(
        &hasher,
        &stmt_bytes,
        fri_ell,
        fri_rounds,
        fri_queries,
        final_degree,
        word0,
    )?;

    let last_idx = word.len() - 1;
    let first_row = rows[0];
    let first_delta_idx = 256 * usize::from(first_row.state) + usize::from(first_row.byte);
    let last_row = rows[last_idx];
    let last_delta_idx = 256 * usize::from(last_row.state) + usize::from(last_row.byte);
    let boundary = BoundaryOpenings {
        first_row,
        first_trace_path: trace_tree.path(0),
        first_salt: salts[0],
        first_content_path: content_tree.path(0),
        first_delta_path: delta_tree.path(first_delta_idx),
        first_fri_path: fri_out.word0_tree.path(0),
        last_row,
        last_trace_path: trace_tree.path(last_idx),
        last_salt: salts[last_idx],
        last_content_path: content_tree.path(last_idx),
        last_delta_path: delta_tree.path(last_delta_idx),
        last_fri_path: fri_out.word0_tree.path(last_idx),
    };

    let step_prefix = step_transcript_prefix(
        &stmt,
        &trace_root,
        &fri_out.roots,
        &fri_out.challenges,
    );
    let default_row = TraceRow {
        byte: 0,
        state: 0,
        next: 0,
        cum_count: 0,
        mask: [0u8; 23],
    };
    let mut step_openings = Vec::with_capacity(step_queries);
    for u in 0..step_queries {
        let idx = derive_step_index(&stepq_cust, &step_prefix, word.len(), u);
        let row = rows[idx];
        let delta_idx = 256 * usize::from(row.state) + usize::from(row.byte);
        let (next_row, next_trace_path) = if idx + 1 < word.len() {
            (rows[idx + 1], trace_tree.path(idx + 1))
        } else {
            (default_row, Vec::new())
        };
        step_openings.push(StepOpening {
            salt: salts[idx],
            content_path: content_tree.path(idx),
            row,
            trace_path: trace_tree.path(idx),
            delta_path: delta_tree.path(delta_idx),
            fri_path: fri_out.word0_tree.path(idx),
            next_row,
            next_trace_path,
        });
    }

    let receipt = PrivateReceipt {
        header,
        trace_root,
        fri_initial_root: fri_out.initial_root,
        fri_receipt_bytes: fri_out.receipt_bytes,
        boundary,
        step_openings,
    };
    Ok((stmt, receipt))
}

/// High-level prover choosing canonical succinct FRI parameters (`blowup = 2`, folding down to
/// `final_degree = 4`) from `(dfa, word, claim, seed, fri_queries, step_queries)`.
pub fn prove_private_document(
    dfa: &DfaTable,
    word: &[u8],
    claim: ClaimData,
    seed: &Digest,
    fri_queries: usize,
    step_queries: usize,
) -> Result<(PrivateContentCert, PrivateReceipt), PrivateCertError> {
    if word.is_empty() {
        return Err(PrivateCertError::EmptyRecord);
    }
    let td = depth_of(word.len()).max(1);
    let fri_ell = td + 1; // rate 1/2 LDE
    let fri_rounds = td.saturating_sub(2); // fold down to <= 4 final coefficients
    let (salts, masks) = expand_randomness(seed, word.len());
    prove_private_with_randomness(
        dfa,
        word,
        &salts,
        &masks,
        claim,
        fri_ell,
        fri_rounds,
        fri_queries,
        step_queries,
    )
}

/// Return the Fiat–Shamir step query indices derived for `(stmt, receipt)`.
pub fn derived_step_indices(
    stmt: &PrivateContentCert,
    receipt: &PrivateReceipt,
) -> Result<Vec<usize>, PrivateCertError> {
    if stmt.fri_rounds > stmt.fri_ell || stmt.fri_ell > 24 || stmt.fri_ell == 0 {
        return Err(PrivateCertError::InvalidShape("invalid FRI shape"));
    }
    let decoded = decode_fri_receipt(
        &receipt.fri_receipt_bytes,
        stmt.fri_ell,
        stmt.fri_rounds,
        stmt.fri_queries,
    )?;
    let stepq_cust = prefixed_customization(STEPQ_PREFIX, STEPQ_NAME);
    let prefix = step_transcript_prefix(
        stmt,
        &receipt.trace_root,
        &decoded.roots,
        &decoded.challenges,
    );
    Ok((0..stmt.step_queries)
        .map(|u| derive_step_index(&stepq_cust, &prefix, stmt.record_length, u))
        .collect())
}

/// Standalone verifier mirroring `Compiler/Tower256PrivateContentCert.lean`'s `checkPrivate`.
pub fn verify_private_cert(
    stmt: &PrivateContentCert,
    receipt: &PrivateReceipt,
) -> Result<(), PrivateCertError> {
    if stmt.record_length == 0 || (stmt.record_length as u64) > (1u64 << 32) {
        return Err(PrivateCertError::VerificationFailed(
            "record_length out of 1..=2^32",
        ));
    }
    let d_rec = depth_of(stmt.record_length);
    let td = d_rec.max(1);
    if stmt.fri_rounds > stmt.fri_ell
        || stmt.fri_ell > 24
        || td >= stmt.fri_ell
        || stmt.fri_queries > 4096
        || stmt.step_queries > 4096
    {
        return Err(PrivateCertError::VerificationFailed("invalid FRI/query shape"));
    }
    let hdr = &receipt.header;
    if hdr.states == 0
        || hdr.states > (1 << 16)
        || hdr.initial >= hdr.states
        || hdr.accepting.len() != hdr.states
    {
        return Err(PrivateCertError::VerificationFailed("malformed AutomatonHeader"));
    }
    if automaton_header_commit(hdr) != stmt.automaton_root {
        return Err(PrivateCertError::VerificationFailed("automatonHeaderCommit != automatonRoot"));
    }
    if receipt.step_openings.len() != stmt.step_queries {
        return Err(PrivateCertError::VerificationFailed("step_openings.len != step_queries"));
    }

    let hasher = MerkleHasher::new();
    let rowmask_cust = prefixed_customization(ROWMASK_PREFIX, ROWMASK_NAME);
    let stepq_cust = prefixed_customization(STEPQ_PREFIX, STEPQ_NAME);

    // 1. Decode and verify `Tower256SuccinctCheck.check` on `fri_receipt_bytes`
    let decoded_fri = decode_fri_receipt(
        &receipt.fri_receipt_bytes,
        stmt.fri_ell,
        stmt.fri_rounds,
        stmt.fri_queries,
    )?;
    let stmt_bytes = private_statement_bytes(stmt, &receipt.trace_root);
    let final_deg_bound = private_degree_schedule(stmt.record_length, stmt.fri_rounds);
    verify_fri_receipt(
        &hasher,
        &stmt_bytes,
        stmt.fri_ell,
        stmt.fri_rounds,
        stmt.fri_queries,
        &receipt.fri_initial_root,
        final_deg_bound,
        &decoded_fri,
    )?;

    // 2. Verify `checkBoundary`
    let b = &receipt.boundary;
    let d_delta = depth_of(hdr.states * 256);
    if usize::from(b.first_row.state) != hdr.initial
        || b.first_row.cum_count != 0
        || usize::from(b.first_row.next) >= hdr.states
    {
        return Err(PrivateCertError::VerificationFailed("initial boundary state/count mismatch"));
    }
    if !hasher.verify_leaf(
        d_rec,
        &stmt.content_root,
        0,
        pack_salted_leaf(b.first_row.byte, &b.first_salt),
        &b.first_content_path,
    ) {
        return Err(PrivateCertError::VerificationFailed("firstContentPath invalid"));
    }
    if !hasher.verify_leaf(
        d_rec,
        &receipt.trace_root,
        0,
        pack_trace_row(&b.first_row),
        &b.first_trace_path,
    ) {
        return Err(PrivateCertError::VerificationFailed("firstTracePath invalid"));
    }
    let first_delta_idx = 256 * usize::from(b.first_row.state) + usize::from(b.first_row.byte);
    if !hasher.verify_leaf(
        d_delta,
        &hdr.delta_root,
        first_delta_idx,
        leaf_of_u64(u64::from(b.first_row.next)),
        &b.first_delta_path,
    ) {
        return Err(PrivateCertError::VerificationFailed("firstDeltaPath invalid"));
    }
    if !hasher.verify_leaf(
        stmt.fri_ell,
        &receipt.fri_initial_root,
        0,
        blind_trace_eval(&b.first_row, &rowmask_cust),
        &b.first_fri_path,
    ) {
        return Err(PrivateCertError::VerificationFailed("firstFriPath invalid"));
    }

    let last_idx = stmt.record_length - 1;
    if usize::from(b.last_row.state) >= hdr.states || usize::from(b.last_row.next) >= hdr.states {
        return Err(PrivateCertError::VerificationFailed("lastRow state out of bounds"));
    }
    if !hasher.verify_leaf(
        d_rec,
        &stmt.content_root,
        last_idx,
        pack_salted_leaf(b.last_row.byte, &b.last_salt),
        &b.last_content_path,
    ) {
        return Err(PrivateCertError::VerificationFailed("lastContentPath invalid"));
    }
    if !hasher.verify_leaf(
        d_rec,
        &receipt.trace_root,
        last_idx,
        pack_trace_row(&b.last_row),
        &b.last_trace_path,
    ) {
        return Err(PrivateCertError::VerificationFailed("lastTracePath invalid"));
    }
    let last_delta_idx = 256 * usize::from(b.last_row.state) + usize::from(b.last_row.byte);
    if !hasher.verify_leaf(
        d_delta,
        &hdr.delta_root,
        last_delta_idx,
        leaf_of_u64(u64::from(b.last_row.next)),
        &b.last_delta_path,
    ) {
        return Err(PrivateCertError::VerificationFailed("lastDeltaPath invalid"));
    }
    if !hasher.verify_leaf(
        stmt.fri_ell,
        &receipt.fri_initial_root,
        last_idx,
        blind_trace_eval(&b.last_row, &rowmask_cust),
        &b.last_fri_path,
    ) {
        return Err(PrivateCertError::VerificationFailed("lastFriPath invalid"));
    }

    let last_hit = u64::from(hdr.accepting[usize::from(b.last_row.next)]);
    let final_acc = hdr.accepting[usize::from(b.last_row.next)];
    let final_count = u64::from(b.last_row.cum_count) + last_hit;
    if !stmt.claim.decide(final_acc, final_count) {
        return Err(PrivateCertError::VerificationFailed("terminal ClaimData check failed"));
    }

    // 3. Verify all `step_queries` Fiat–Shamir sampled step openings (`checkStepOpening`)
    let prefix = step_transcript_prefix(
        stmt,
        &receipt.trace_root,
        &decoded_fri.roots,
        &decoded_fri.challenges,
    );
    let default_row = TraceRow {
        byte: 0,
        state: 0,
        next: 0,
        cum_count: 0,
        mask: [0u8; 23],
    };
    for (u, op) in receipt.step_openings.iter().enumerate() {
        let idx = derive_step_index(&stepq_cust, &prefix, stmt.record_length, u);
        if usize::from(op.row.state) >= hdr.states || usize::from(op.row.next) >= hdr.states {
            return Err(PrivateCertError::VerificationFailed("step row state out of bounds"));
        }
        if !hasher.verify_leaf(
            d_rec,
            &stmt.content_root,
            idx,
            pack_salted_leaf(op.row.byte, &op.salt),
            &op.content_path,
        ) {
            return Err(PrivateCertError::VerificationFailed("step contentPath invalid"));
        }
        if !hasher.verify_leaf(
            d_rec,
            &receipt.trace_root,
            idx,
            pack_trace_row(&op.row),
            &op.trace_path,
        ) {
            return Err(PrivateCertError::VerificationFailed("step tracePath invalid"));
        }
        let delta_idx = 256 * usize::from(op.row.state) + usize::from(op.row.byte);
        if !hasher.verify_leaf(
            d_delta,
            &hdr.delta_root,
            delta_idx,
            leaf_of_u64(u64::from(op.row.next)),
            &op.delta_path,
        ) {
            return Err(PrivateCertError::VerificationFailed("step deltaPath invalid"));
        }
        if !hasher.verify_leaf(
            stmt.fri_ell,
            &receipt.fri_initial_root,
            idx,
            blind_trace_eval(&op.row, &rowmask_cust),
            &op.fri_path,
        ) {
            return Err(PrivateCertError::VerificationFailed("step friPath invalid"));
        }
        if idx + 1 < stmt.record_length {
            if !hasher.verify_leaf(
                d_rec,
                &receipt.trace_root,
                idx + 1,
                pack_trace_row(&op.next_row),
                &op.next_trace_path,
            ) {
                return Err(PrivateCertError::VerificationFailed("step nextTracePath invalid"));
            }
            let hit = u32::from(hdr.accepting[usize::from(op.row.next)]);
            let expected_cc = op
                .row
                .cum_count
                .checked_add(hit)
                .ok_or(PrivateCertError::VerificationFailed("cum_count overflow"))?;
            if op.next_row.state != op.row.next || op.next_row.cum_count != expected_cc {
                return Err(PrivateCertError::VerificationFailed("step chaining failed"));
            }
        } else if op.next_row != default_row || !op.next_trace_path.is_empty() {
            return Err(PrivateCertError::VerificationFailed(
                "non-canonical trailing nextRow at idx == record_length - 1",
            ));
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// Canonical Binary Wire Codec for `PrivateReceipt` & `PrivateContentCert`

fn write_path_raw(out: &mut Vec<u8>, path: &[Digest]) {
    out.push(path.len() as u8);
    for d in path {
        out.extend_from_slice(d);
    }
}

fn read_path_raw(r: &mut StreamReader<'_>) -> Result<Vec<Digest>, PrivateCertError> {
    let len = usize::from(r.byte()?);
    let mut out = Vec::with_capacity(len);
    for _ in 0..len {
        let s = r.take(32)?;
        out.push(s.try_into().expect("32B"));
    }
    Ok(out)
}

pub fn encode_private_receipt(receipt: &PrivateReceipt) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(RECEIPT_MAGIC);
    out.extend_from_slice(&(receipt.header.states as u32).to_le_bytes());
    out.extend_from_slice(&(receipt.header.initial as u32).to_le_bytes());
    for &acc in &receipt.header.accepting {
        out.push(if acc { 1 } else { 0 });
    }
    out.extend_from_slice(&receipt.header.delta_root);
    out.extend_from_slice(&receipt.trace_root);
    out.extend_from_slice(&receipt.fri_initial_root);
    out.extend_from_slice(&(receipt.fri_receipt_bytes.len() as u32).to_le_bytes());
    out.extend_from_slice(&receipt.fri_receipt_bytes);

    let b = &receipt.boundary;
    out.extend_from_slice(&pack_trace_row(&b.first_row).to_le_bytes());
    write_path_raw(&mut out, &b.first_trace_path);
    out.extend_from_slice(&b.first_salt);
    write_path_raw(&mut out, &b.first_content_path);
    write_path_raw(&mut out, &b.first_delta_path);
    write_path_raw(&mut out, &b.first_fri_path);
    out.extend_from_slice(&pack_trace_row(&b.last_row).to_le_bytes());
    write_path_raw(&mut out, &b.last_trace_path);
    out.extend_from_slice(&b.last_salt);
    write_path_raw(&mut out, &b.last_content_path);
    write_path_raw(&mut out, &b.last_delta_path);
    write_path_raw(&mut out, &b.last_fri_path);

    out.extend_from_slice(&(receipt.step_openings.len() as u32).to_le_bytes());
    for op in &receipt.step_openings {
        out.extend_from_slice(&op.salt);
        write_path_raw(&mut out, &op.content_path);
        out.extend_from_slice(&pack_trace_row(&op.row).to_le_bytes());
        write_path_raw(&mut out, &op.trace_path);
        write_path_raw(&mut out, &op.delta_path);
        write_path_raw(&mut out, &op.fri_path);
        let has_next = !op.next_trace_path.is_empty();
        out.push(if has_next { 1 } else { 0 });
        if has_next {
            out.extend_from_slice(&pack_trace_row(&op.next_row).to_le_bytes());
            write_path_raw(&mut out, &op.next_trace_path);
        }
    }
    out
}

pub fn decode_private_receipt(bytes: &[u8]) -> Result<PrivateReceipt, PrivateCertError> {
    let mut r = StreamReader { bytes, pos: 0 };
    if r.take(8)? != RECEIPT_MAGIC {
        return Err(PrivateCertError::MalformedWire("bad receipt magic"));
    }
    let states = u32::from_le_bytes(r.take(4)?.try_into().expect("4B")) as usize;
    if states == 0 || states > (1 << 16) {
        return Err(PrivateCertError::MalformedWire("states out of range"));
    }
    let initial = u32::from_le_bytes(r.take(4)?.try_into().expect("4B")) as usize;
    let acc_raw = r.take(states)?;
    let mut accepting = Vec::with_capacity(states);
    for &b in acc_raw {
        match b {
            0 => accepting.push(false),
            1 => accepting.push(true),
            _ => return Err(PrivateCertError::MalformedWire("non-boolean accepting byte")),
        }
    }
    let delta_root: Digest = r.take(32)?.try_into().expect("32B");
    let trace_root: Digest = r.take(32)?.try_into().expect("32B");
    let fri_initial_root: Digest = r.take(32)?.try_into().expect("32B");
    let fri_len = u32::from_le_bytes(r.take(4)?.try_into().expect("4B")) as usize;
    let fri_receipt_bytes = r.take(fri_len)?.to_vec();

    let first_row = unpack_trace_row(r.c8()?);
    let first_trace_path = read_path_raw(&mut r)?;
    let first_salt: Salt248 = r.take(31)?.try_into().expect("31B");
    let first_content_path = read_path_raw(&mut r)?;
    let first_delta_path = read_path_raw(&mut r)?;
    let first_fri_path = read_path_raw(&mut r)?;
    let last_row = unpack_trace_row(r.c8()?);
    let last_trace_path = read_path_raw(&mut r)?;
    let last_salt: Salt248 = r.take(31)?.try_into().expect("31B");
    let last_content_path = read_path_raw(&mut r)?;
    let last_delta_path = read_path_raw(&mut r)?;
    let last_fri_path = read_path_raw(&mut r)?;

    let n_steps = u32::from_le_bytes(r.take(4)?.try_into().expect("4B")) as usize;
    if n_steps > 4096 {
        return Err(PrivateCertError::MalformedWire("too many step openings"));
    }
    let mut step_openings = Vec::with_capacity(n_steps);
    for _ in 0..n_steps {
        let salt: Salt248 = r.take(31)?.try_into().expect("31B");
        let content_path = read_path_raw(&mut r)?;
        let row = unpack_trace_row(r.c8()?);
        let trace_path = read_path_raw(&mut r)?;
        let delta_path = read_path_raw(&mut r)?;
        let fri_path = read_path_raw(&mut r)?;
        let has_next = r.byte()?;
        let (next_row, next_trace_path) = match has_next {
            0 => (
                TraceRow {
                    byte: 0,
                    state: 0,
                    next: 0,
                    cum_count: 0,
                    mask: [0u8; 23],
                },
                Vec::new(),
            ),
            1 => (unpack_trace_row(r.c8()?), read_path_raw(&mut r)?),
            _ => return Err(PrivateCertError::MalformedWire("invalid has_next tag")),
        };
        step_openings.push(StepOpening {
            salt,
            content_path,
            row,
            trace_path,
            delta_path,
            fri_path,
            next_row,
            next_trace_path,
        });
    }
    if r.pos != bytes.len() {
        return Err(PrivateCertError::MalformedWire("trailing bytes in PrivateReceipt"));
    }
    Ok(PrivateReceipt {
        header: AutomatonHeader {
            states,
            initial,
            accepting,
            delta_root,
        },
        trace_root,
        fri_initial_root,
        fri_receipt_bytes,
        boundary: BoundaryOpenings {
            first_row,
            first_trace_path,
            first_salt,
            first_content_path,
            first_delta_path,
            first_fri_path,
            last_row,
            last_trace_path,
            last_salt,
            last_content_path,
            last_delta_path,
            last_fri_path,
        },
        step_openings,
    })
}

pub fn verify_private_cert_bytes(
    stmt: &PrivateContentCert,
    receipt_bytes: &[u8],
) -> Result<(), PrivateCertError> {
    let receipt = decode_private_receipt(receipt_bytes)?;
    verify_private_cert(stmt, &receipt)
}

pub fn encode_private_cert(stmt: &PrivateContentCert) -> Vec<u8> {
    let mut out = Vec::with_capacity(112);
    out.extend_from_slice(b"MDPSTM01");
    out.extend_from_slice(&stmt.content_root);
    out.extend_from_slice(&(stmt.record_length as u64).to_le_bytes());
    out.extend_from_slice(&stmt.automaton_root);
    match stmt.claim {
        ClaimData::Accept(b) => {
            out.push(0);
            out.push(if b { 1 } else { 0 });
        }
        ClaimData::Count(n) => {
            out.push(1);
            out.extend_from_slice(&n.to_le_bytes());
        }
        ClaimData::Bound { lo, hi } => {
            out.push(2);
            out.extend_from_slice(&lo.to_le_bytes());
            out.extend_from_slice(&hi.to_le_bytes());
        }
    }
    out.extend_from_slice(&(stmt.fri_ell as u32).to_le_bytes());
    out.extend_from_slice(&(stmt.fri_rounds as u32).to_le_bytes());
    out.extend_from_slice(&(stmt.fri_queries as u32).to_le_bytes());
    out.extend_from_slice(&(stmt.step_queries as u32).to_le_bytes());
    out
}

pub fn decode_private_cert(bytes: &[u8]) -> Result<PrivateContentCert, PrivateCertError> {
    let mut r = StreamReader { bytes, pos: 0 };
    if r.take(8)? != b"MDPSTM01" {
        return Err(PrivateCertError::MalformedWire("bad statement magic"));
    }
    let content_root: Digest = r.take(32)?.try_into().expect("32B");
    let record_length = u64::from_le_bytes(r.take(8)?.try_into().expect("8B")) as usize;
    let automaton_root: Digest = r.take(32)?.try_into().expect("32B");
    let claim = match r.byte()? {
        0 => match r.byte()? {
            0 => ClaimData::Accept(false),
            1 => ClaimData::Accept(true),
            _ => return Err(PrivateCertError::MalformedWire("bad accept bool")),
        },
        1 => ClaimData::Count(u64::from_le_bytes(r.take(8)?.try_into().expect("8B"))),
        2 => {
            let lo = u64::from_le_bytes(r.take(8)?.try_into().expect("8B"));
            let hi = u64::from_le_bytes(r.take(8)?.try_into().expect("8B"));
            ClaimData::Bound { lo, hi }
        }
        _ => return Err(PrivateCertError::MalformedWire("bad claim tag")),
    };
    let fri_ell = u32::from_le_bytes(r.take(4)?.try_into().expect("4B")) as usize;
    let fri_rounds = u32::from_le_bytes(r.take(4)?.try_into().expect("4B")) as usize;
    let fri_queries = u32::from_le_bytes(r.take(4)?.try_into().expect("4B")) as usize;
    let step_queries = u32::from_le_bytes(r.take(4)?.try_into().expect("4B")) as usize;
    if r.pos != bytes.len() {
        return Err(PrivateCertError::MalformedWire("trailing bytes in statement"));
    }
    Ok(PrivateContentCert {
        content_root,
        record_length,
        automaton_root,
        claim,
        fri_ell,
        fri_rounds,
        fri_queries,
        step_queries,
    })
}

/// Zero-leakage audit helper: scans `receipt_bytes` for any occurrence of every contiguous slice
/// of `document` of length `min_slice_len` (and any explicit `secret_markers`), returning the count
/// of leaked slices found (`0` means complete absence from the receipt buffer).
pub fn scan_receipt_for_document_slices(
    document: &[u8],
    receipt_bytes: &[u8],
    min_slice_len: usize,
) -> usize {
    if document.len() < min_slice_len || receipt_bytes.len() < min_slice_len {
        return 0;
    }
    let mut hits = 0usize;
    for window in document.windows(min_slice_len) {
        if receipt_bytes.windows(min_slice_len).any(|rw| rw == window) {
            hits += 1;
        }
    }
    hits
}

/// Generate a realistic private Hermes agent transcript + `.env`-guarded config document of exact
/// byte length `target_bytes` containing sensitive private credentials/PII (DB passwords, bearer
/// tokens, internal hostnames, CoT reasoning) and `TODO`/`RULE` markers, with optional `"sk-live-..."`
/// OpenAI key injection for adversarial testing.
pub fn synthesize_realistic_hermes_document(target_bytes: usize, inject_sk_key: bool) -> Vec<u8> {
    let header = b"# Hermes Guarded Session & .env Policy Bundle\n\
DB_DSN=postgres://hermes_admin:Pr1v4t3_Pg_S3cr3t_9941!@10.42.0.19:5432/custody\n\
INTERNAL_BEARER=br_internal_8842_alpha_bravo_charlie_delta_echo_9921\n\
CUSTOMER_SSN_REDACTED_NOTE=pii_vault_ref_7731_do_not_disclose_outside_enclave\n\
RULE: outbound_tool_calls_must_never_contain_openai_secret_keys\n\
TODO: rotate_ephemeral_hmac_signing_subkey_after_epoch_4096\n";
    let cot_block = b"[hermes/turn] thought: checking tool call arguments {\"tool\":\"http_post\",\"endpoint\":\"https://api.internal.corp/v2/audit\"}; \
private_workspace_secret=\"vault_master_phrase_amber_cobalt_7719_xenon\"; \
RULE: verify_content_certificate_before_egress; \
TODO: attach_succinct_tower256_cshake_receipt;\n";

    let mut doc = Vec::with_capacity(target_bytes + 256);
    doc.extend_from_slice(header);
    let mut idx = 0usize;
    while doc.len() < target_bytes {
        doc.extend_from_slice(cot_block);
        // Add non-repeating per-block private nonce text so blocks are distinct.
        let line = format!(
            "PRIVATE_CTX_ROW_{idx:04}=enclave_mem_word_{:016x}_confidential\n",
            0x9e37_79b9_7f4a_7c15u64.wrapping_mul((idx + 1) as u64)
        );
        doc.extend_from_slice(line.as_bytes());
        idx += 1;
    }
    doc.truncate(target_bytes);
    if inject_sk_key && target_bytes >= 32 {
        let secret = b"sk-live-7f9a2c4e8b1d0356";
        let pos = (target_bytes / 2).min(target_bytes - secret.len());
        doc[pos..pos + secret.len()].copy_from_slice(secret);
    }
    doc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::additive_ntt;
    use crate::binary_tower::TowerElem;

    #[test]
    fn tower256_ntt_agrees_with_gf2_64_additive_ntt_and_monomial_lde() {
        // 1. Cross-check against `crate::additive_ntt` embedded from GF(2^64) into Tower256.
        let k = 4usize;
        let n = 1usize << k;
        let basis64: Vec<TowerElem> = (0..k)
            .map(|i| TowerElem::new(6, 1u64 << i).unwrap())
            .collect();
        let offset64 = TowerElem::zero(6).unwrap();
        let coeffs64: Vec<TowerElem> = (0..n)
            .map(|i| TowerElem::new(6, (i as u64) * 19 + 5).unwrap())
            .collect();
        let evals64 = additive_ntt::forward(&coeffs64, &basis64, offset64).unwrap();

        let basis256 = unit_basis(k);
        let mut coeffs256: Vec<Tower256> = coeffs64
            .iter()
            .map(|&c| Tower256::embed_gf2_64(c).unwrap())
            .collect();
        ntt_forward_in_place(&mut coeffs256, &basis256, Tower256::ZERO).unwrap();
        for (got, &exp) in coeffs256.iter().zip(evals64.iter()) {
            assert_eq!(*got, Tower256::embed_gf2_64(exp).unwrap());
        }
        ntt_inverse_in_place(&mut coeffs256, &basis256, Tower256::ZERO).unwrap();
        for (got, &exp) in coeffs256.iter().zip(coeffs64.iter()) {
            assert_eq!(*got, Tower256::embed_gf2_64(exp).unwrap());
        }

        // 2. Cross-check LDE (`td = 4 -> fri_ell = 6`) against dense monomial `gauss_interpolate`.
        let ell = 6usize;
        let beta_ell = unit_basis(ell);
        let base_vals: Vec<Tower256> = (0..n)
            .map(|i| Tower256::from_limbs([(i as u64) * 31 + 7, (i as u64) ^ 0x55aa, 99, 1]))
            .collect();
        let lde_ntt = low_degree_extend_unit_basis(&base_vals, k, ell).unwrap();
        let pts: Vec<(Tower256, Tower256)> = (0..n)
            .map(|i| (raw_domain_point(&beta_ell, Tower256::ZERO, ell, i), base_vals[i]))
            .collect();
        let mono = gauss_interpolate(&pts).unwrap();
        for idx in 0..(1usize << ell) {
            let x = raw_domain_point(&beta_ell, Tower256::ZERO, ell, idx);
            assert_eq!(lde_ntt[idx], eval_monomial_coeffs(&mono, x));
        }
    }

    #[test]
    fn depth_of_matches_lean_clog2() {
        assert_eq!(depth_of(0), 0);
        assert_eq!(depth_of(1), 0);
        assert_eq!(depth_of(2), 1);
        assert_eq!(depth_of(3), 2);
        assert_eq!(depth_of(4), 2);
        assert_eq!(depth_of(5), 3);
        assert_eq!(depth_of(4096), 12);
        assert_eq!(depth_of(4097), 13);
        assert_eq!(depth_of(16384), 14);
    }
}
