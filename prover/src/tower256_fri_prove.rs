//! Work 9104: the Tower256 additive-FRI honest prover, as unverified native compute.
//!
//! Request (codec 9011, `Compiler/Tower256FriNativeDeployment.lean` `requestStream`) in,
//! succinct receipt bytes (codec 9013, `Compiler/Tower256SuccinctReceiptCodec.lean`
//! `receiptStream`) out. The reference is the Lean prover
//! `Compiler/Tower256SuccinctProver.lean` `prove`; `lake exe tower256-prover-run --vectors`
//! writes the request/response pairs `tests/tower256_fri_prove_conformance.rs` reproduces byte
//! for byte. A reply has authority only through Lean's `checkBytes` (`acceptResponse_iff`).
//!
//! Index conventions (all as in Lean): a level-`j` coordinate `c : Fin (ell - j) -> ZMod 2` is
//! the integer `sum c_i 2^i`; a Merkle address is the same integer, and the cube tree splits on
//! address bit 0 at the root, so the leaf-level split is the top bit. `liftBit` appends the
//! folded coordinate as the top bit.

use crate::binary_tower_256::Tower256;
use crate::hash_kernels::cshake256_xof;

/// `0x01 :: "MINIDREGG/TOWER256/MERKLE/LEAF/V1"` (`Tower256ConcreteBackend.leafCustomization`).
const LEAF_PREFIX: u8 = 0x01;
const LEAF_NAME: &[u8] = b"MINIDREGG/TOWER256/MERKLE/LEAF/V1";
/// `0x02 :: "MINIDREGG/TOWER256/MERKLE/NODE/V1"`.
const NODE_PREFIX: u8 = 0x02;
const NODE_NAME: &[u8] = b"MINIDREGG/TOWER256/MERKLE/NODE/V1";
/// `bootstrapPins.challengeCustomization` and `queryCustomization`.
const CHALLENGE_CUSTOMIZATION: &[u8] = b"MD-FRI-C";
const QUERY_CUSTOMIZATION: &[u8] = b"MD-FRI-Q";

/// The largest `ell` this kernel tabulates (a level-0 word has `2^ell` entries).
pub const MAX_ELL: usize = 24;

type Digest = [u8; 32];

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FriProveError {
    /// The request bytes are not one `requestStream` encoding.
    Request(&'static str),
    /// `m > ell`, or `ell` above `MAX_ELL`.
    Shape { ell: usize, m: usize },
    /// The basis has a length other than `ell`.
    BasisLength { ell: usize, len: usize },
    /// The final degree exceeds the last level's size.
    FinalDegree { degree: usize, size: usize },
    /// A round pivot is zero (the basis is dependent).
    ZeroPivot(usize),
    /// The interpolation points repeat.
    SingularInterpolation,
}

impl core::fmt::Display for FriProveError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Request(what) => write!(f, "malformed 9104 request: {what}"),
            Self::Shape { ell, m } => write!(f, "unsupported shape ell = {ell}, m = {m}"),
            Self::BasisLength { ell, len } => write!(f, "basis has {len} entries, ell = {ell}"),
            Self::FinalDegree { degree, size } => {
                write!(f, "final degree {degree} exceeds the last level's {size} points")
            }
            Self::ZeroPivot(r) => write!(f, "round {r} pivot is zero"),
            Self::SingularInterpolation => write!(f, "interpolation points repeat"),
        }
    }
}

impl std::error::Error for FriProveError {}

/// A decoded 9104 request.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProveRequest {
    pub statement_bytes: Vec<u8>,
    pub ell: usize,
    pub m: usize,
    pub query_count: usize,
    pub beta: Vec<Tower256>,
    pub offset: Tower256,
    pub degree: Vec<usize>,
    pub input_word: Vec<Tower256>,
}

// ---------------------------------------------------------------------------------------------
// Stream codecs (`Theory/StreamCodec.lean`)

/// `StreamCodec.nat`: base-255 digits, least significant first, then `255`.
fn encode_nat(out: &mut Vec<u8>, mut value: u128) {
    while value > 0 {
        out.push((value % 255) as u8);
        value /= 255;
    }
    out.push(255);
}

/// `StreamCodec.nat` of a value given as 32 little-endian bytes (a digest).
fn encode_nat_le32(out: &mut Vec<u8>, bytes: &Digest) {
    // Repeated division of the 256-bit little-endian integer by 255.
    let mut limbs: Vec<u32> = bytes
        .chunks(4)
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

struct Reader<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn byte(&mut self) -> Result<u8, FriProveError> {
        let b = *self.bytes.get(self.pos).ok_or(FriProveError::Request("truncated"))?;
        self.pos += 1;
        Ok(b)
    }

    /// `decodeNatPrefix`, canonical: no most-significant zero digit.
    fn nat(&mut self) -> Result<usize, FriProveError> {
        let mut digits = Vec::new();
        loop {
            let b = self.byte()?;
            if b == 255 {
                break;
            }
            digits.push(b);
        }
        if digits.last() == Some(&0) {
            return Err(FriProveError::Request("non-canonical natural"));
        }
        let mut value: usize = 0;
        for &d in digits.iter().rev() {
            value = value
                .checked_mul(255)
                .and_then(|v| v.checked_add(usize::from(d)))
                .ok_or(FriProveError::Request("natural too large"))?;
        }
        Ok(value)
    }

    fn take(&mut self, n: usize) -> Result<&'a [u8], FriProveError> {
        let end = self.pos.checked_add(n).ok_or(FriProveError::Request("length overflow"))?;
        let slice = self.bytes.get(self.pos..end).ok_or(FriProveError::Request("truncated"))?;
        self.pos = end;
        Ok(slice)
    }

    fn c8(&mut self) -> Result<Tower256, FriProveError> {
        let slice = self.take(32)?;
        Ok(Tower256::from_le_bytes(slice.try_into().expect("32 bytes")))
    }

    fn c8_list(&mut self) -> Result<Vec<Tower256>, FriProveError> {
        let n = self.nat()?;
        if n > self.bytes.len() {
            return Err(FriProveError::Request("list longer than the request"));
        }
        (0..n).map(|_| self.c8()).collect()
    }
}

/// Decode `requestStream`: statement bytes, ell, m, queryCount, basis, offset, degrees, word.
pub fn decode_request(bytes: &[u8]) -> Result<ProveRequest, FriProveError> {
    let mut r = Reader { bytes, pos: 0 };
    let n = r.nat()?;
    let statement_bytes = r.take(n)?.to_vec();
    let ell = r.nat()?;
    let m = r.nat()?;
    let query_count = r.nat()?;
    let beta = r.c8_list()?;
    let offset = r.c8()?;
    let dn = r.nat()?;
    if dn > bytes.len() {
        return Err(FriProveError::Request("list longer than the request"));
    }
    let degree = (0..dn).map(|_| r.nat()).collect::<Result<Vec<_>, _>>()?;
    let input_word = r.c8_list()?;
    if r.pos != bytes.len() {
        return Err(FriProveError::Request("trailing bytes"));
    }
    Ok(ProveRequest { statement_bytes, ell, m, query_count, beta, offset, degree, input_word })
}

// ---------------------------------------------------------------------------------------------
// Framing (`Tower256CshakeMerkleController`)

/// `encodeLength n`: `n` zeros, then `1`.
fn encode_length(out: &mut Vec<u8>, n: usize) {
    out.resize(out.len() + n, 0);
    out.push(1);
}

/// `envelope bytes = encodeLength bytes.length ++ bytes`.
fn envelope(out: &mut Vec<u8>, bytes: &[u8]) {
    encode_length(out, bytes.len());
    out.extend_from_slice(bytes);
}

fn customization(prefix: u8, name: &[u8]) -> Vec<u8> {
    let mut c = Vec::with_capacity(name.len() + 1);
    c.push(prefix);
    c.extend_from_slice(name);
    c
}

fn xof32(customization: &[u8], input: &[u8]) -> Digest {
    cshake256_xof(customization, input, 32).try_into().expect("32 bytes")
}

struct Merkle {
    leaf: Vec<u8>,
    node: Vec<u8>,
}

impl Merkle {
    fn new() -> Self {
        Self { leaf: customization(LEAF_PREFIX, LEAF_NAME), node: customization(NODE_PREFIX, NODE_NAME) }
    }

    /// `hashLeaf codecC v = xof leaf (0 :: envelope (encodeC v))`.
    fn hash_leaf(&self, value: Tower256) -> Digest {
        let mut input = vec![0u8];
        envelope(&mut input, &value.to_le_bytes());
        xof32(&self.leaf, &input)
    }

    /// `hashNode l r = xof node (1 :: envelope l ++ envelope r)`.
    fn hash_node(&self, left: &Digest, right: &Digest) -> Digest {
        let mut input = vec![1u8];
        envelope(&mut input, left);
        envelope(&mut input, right);
        xof32(&self.node, &input)
    }

    /// `cubeRoot` of the column `values` (indexed by address integer), over the addresses
    /// congruent to `offset` modulo `stride`.
    fn root_at(&self, values: &[Tower256], offset: usize, stride: usize) -> Digest {
        if stride >= values.len() {
            self.hash_leaf(values[offset])
        } else {
            let l = self.root_at(values, offset, stride * 2);
            let r = self.root_at(values, offset + stride, stride * 2);
            self.hash_node(&l, &r)
        }
    }

    fn root(&self, values: &[Tower256]) -> Digest {
        self.root_at(values, 0, 1)
    }

    /// `cubePath`: top-down sibling roots of address `index`.
    fn path(&self, values: &[Tower256], index: usize) -> Vec<Digest> {
        let mut out = Vec::new();
        let (mut offset, mut stride) = (0usize, 1usize);
        while stride < values.len() {
            if index & stride == 0 {
                out.push(self.root_at(values, offset + stride, stride * 2));
            } else {
                out.push(self.root_at(values, offset, stride * 2));
                offset += stride;
            }
            stride *= 2;
        }
        out
    }
}

// ---------------------------------------------------------------------------------------------
// The tower over the basis (`Tower256SuccinctCheck`, section Tower)

struct Tower {
    ell: usize,
    beta: Vec<Tower256>,
    offset: Tower256,
}

impl Tower {
    fn beta_n(&self, n: usize) -> Tower256 {
        self.beta.get(n).copied().unwrap_or(Tower256::ZERO)
    }

    /// `applyPivots ps x`: fold `y ↦ y² + p·y` over the pivots.
    fn apply_pivots(ps: &[Tower256], x: Tower256) -> Tower256 {
        ps.iter().fold(x, |y, &p| y.square().add(p.mul(y)))
    }

    /// `rawC k c = offset + sum_{i<k} c_i beta_i`, with `c` the integer `index`.
    fn raw(&self, k: usize, index: usize) -> Tower256 {
        (0..k).filter(|i| index >> i & 1 == 1).fold(self.offset, |acc, i| acc.add(self.beta_n(i)))
    }

    /// `domC j c` for every level-`j` index, given `pivots j`.
    fn domain(&self, j: usize, ps: &[Tower256]) -> Vec<Tower256> {
        let k = self.ell - j;
        (0..1usize << k).map(|i| Self::apply_pivots(ps, self.raw(k, i))).collect()
    }
}

/// `evalCoeffs cs x`: Horner, constant coefficient first.
fn eval_coeffs(cs: &[Tower256], x: Tower256) -> Tower256 {
    cs.iter().rev().fold(Tower256::ZERO, |acc, &c| c.add(x.mul(acc)))
}

/// The coefficients through `points` (Gauss–Jordan; the solution is unique, so any pivot order
/// agrees with Lean's `gaussSolve`).
fn interpolate(points: &[(Tower256, Tower256)]) -> Result<Vec<Tower256>, FriProveError> {
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
        let p = (col..n).find(|&r| !rows[r][col].is_zero()).ok_or(FriProveError::SingularInterpolation)?;
        rows.swap(p, col);
        let inv = rows[col][col].inverse().map_err(|_| FriProveError::SingularInterpolation)?;
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
// Transcript (`challengeInputC`, `queryPrefixC`, `seedC`)

fn basis_prefix(t: &Tower, m: usize) -> Vec<u8> {
    let mut out = Vec::new();
    let mut tmp = Vec::new();
    encode_length(&mut tmp, t.ell);
    envelope(&mut out, &tmp);
    tmp.clear();
    encode_length(&mut tmp, m);
    envelope(&mut out, &tmp);
    envelope(&mut out, &t.offset.to_le_bytes());
    for (i, b) in t.beta.iter().enumerate() {
        let mut inner = Vec::new();
        tmp.clear();
        encode_length(&mut tmp, i);
        envelope(&mut inner, &tmp);
        envelope(&mut inner, &b.to_le_bytes());
        envelope(&mut out, &inner);
    }
    out
}

/// `envelope statementBytes ++ envelope basisPrefix ++ (roots 0..=upto, each with its index)`.
fn roots_transcript(head: &[u8], roots: &[Digest], upto: usize) -> Vec<u8> {
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

// ---------------------------------------------------------------------------------------------
// The prover

/// The honest receipt for `req`, as `receiptStream` bytes.
pub fn prove(req: &ProveRequest) -> Result<Vec<u8>, FriProveError> {
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
    let tower = Tower { ell, beta: req.beta.clone(), offset: req.offset };
    let merkle = Merkle::new();
    let mut head = Vec::new();
    envelope(&mut head, &req.statement_bytes);
    envelope(&mut head, &basis_prefix(&tower, m));

    let mut ps: Vec<Tower256> = Vec::new();
    let dom0 = tower.domain(0, &ps);
    let mut words: Vec<Vec<Tower256>> = vec![dom0.iter().map(|&x| eval_coeffs(&req.input_word, x)).collect()];
    let mut roots: Vec<Digest> = vec![merkle.root(&words[0])];
    let mut challenges: Vec<Tower256> = Vec::with_capacity(m);
    let mut dom = dom0;
    for j in 0..m {
        let input = roots_transcript(&head, &roots, j);
        let alpha = Tower256::from_le_bytes(xof32(CHALLENGE_CUSTOMIZATION, &input));
        let pivot = Tower::apply_pivots(&ps, tower.beta_n((ell - 1).saturating_sub(j)));
        let pinv = pivot.inverse().map_err(|_| FriProveError::ZeroPivot(j))?;
        let half = 1usize << (ell - j - 1);
        let w = &words[j];
        let next: Vec<Tower256> = (0..half)
            .map(|k| {
                let (left, right) = (w[k], w[k + half]);
                left.add(dom[k].add(alpha).mul(left.add(right)).mul(pinv))
            })
            .collect();
        challenges.push(alpha);
        ps.push(pivot);
        dom = tower.domain(j + 1, &ps);
        if j + 1 < m {
            roots.push(merkle.root(&next));
        }
        words.push(next);
    }
    let wm = &words[m];
    let points: Vec<(Tower256, Tower256)> = (0..final_degree).map(|n| (dom[n % last_size], wm[n])).collect();
    let coeffs = interpolate(&points)?;
    let last: Vec<Tower256> = dom.iter().map(|&x| eval_coeffs(&coeffs, x)).collect();
    roots.push(merkle.root(&last));

    // Seeds: the query prefix, then each query's index.
    let mut prefix = roots_transcript(&head, &roots, m);
    for c in &challenges {
        envelope(&mut prefix, &c.to_le_bytes());
    }
    let seed_bits = ell - 1;
    let seeds: Vec<usize> = (0..q)
        .map(|a| {
            let mut input = prefix.clone();
            let mut tmp = Vec::new();
            encode_length(&mut tmp, a);
            envelope(&mut input, &tmp);
            let d = xof32(QUERY_CUSTOMIZATION, &input);
            let mut low = [0u8; 8];
            low.copy_from_slice(&d[..8]);
            let v = u64::from_le_bytes(low);
            (if seed_bits >= 64 { v } else { v & ((1u64 << seed_bits) - 1) }) as usize
        })
        .collect();

    // The receipt (`receiptStream`).
    let mut out = Vec::new();
    // `roots : Fin (m + 1) -> Digest`. At `m = 0` the prover's list also holds the final
    // polynomial's root after the level-0 root; the receipt carries index 0 only, as Lean's.
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
    encode_nat(&mut out, m as u128);
    for j in 0..m {
        encode_nat(&mut out, q as u128);
        let w = &words[j];
        let half = 1usize << (ell - j - 1);
        for &s in &seeds {
            let k = s % half;
            out.extend_from_slice(&w[k].to_le_bytes());
            out.extend_from_slice(&w[k + half].to_le_bytes());
            let mut path = merkle.path(w, k);
            path.pop();
            encode_nat(&mut out, path.len() as u128);
            for d in &path {
                encode_nat_le32(&mut out, d);
            }
        }
    }
    encode_nat(&mut out, coeffs.len() as u128);
    for c in &coeffs {
        out.extend_from_slice(&c.to_le_bytes());
    }
    Ok(out)
}

/// Work 9104's byte entry: decode the request, prove, encode the receipt.
pub fn tower256_additive_fri_prove_bytes(request: &[u8]) -> Result<Vec<u8>, FriProveError> {
    prove(&decode_request(request)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nat_encoding_matches_lean_digits() {
        let mut out = Vec::new();
        encode_nat(&mut out, 0);
        assert_eq!(out, [255]);
        out.clear();
        encode_nat(&mut out, 254);
        assert_eq!(out, [254, 255]);
        out.clear();
        encode_nat(&mut out, 255);
        assert_eq!(out, [0, 1, 255]);
        let mut a = Vec::new();
        let mut b = Vec::new();
        let mut le = [0u8; 32];
        le[..8].copy_from_slice(&123_456_789u64.to_le_bytes());
        encode_nat(&mut a, 123_456_789);
        encode_nat_le32(&mut b, &le);
        assert_eq!(a, b);
    }

    #[test]
    fn path_recomputes_root() {
        let merkle = Merkle::new();
        let values: Vec<Tower256> = (0..8u64).map(|i| Tower256::from_limbs([i * 7 + 1, 0, 0, 0])).collect();
        let root = merkle.root(&values);
        for index in 0..8 {
            let path = merkle.path(&values, index);
            // Recompute bottom-up: the last sibling is the leaf level (address top bit).
            let mut acc = merkle.hash_leaf(values[index]);
            for (depth, sib) in path.iter().enumerate().rev() {
                acc = if index >> depth & 1 == 0 { merkle.hash_node(&acc, sib) } else { merkle.hash_node(sib, &acc) };
            }
            assert_eq!(acc, root);
        }
    }
}
