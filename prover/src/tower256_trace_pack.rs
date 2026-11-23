//! Trace-dual openings of packed bytes in the little-endian Fan–Paar basis.
//! Table DFAs compile to Boolean mux constraints. A tensor specialization proves
//! the two-state DFA that toggles when both selected byte predicates hold.
//! Figure 2 opens the terminal linear claim against masked additive RS codewords.
#![deny(warnings)]

use crate::binary_tower_256::Tower256 as F;
use crate::hash_kernels::cshake256_xof;
use crate::tower256_private_cert::{automaton_commit, DfaTable};
use crate::tower256_private_cert::{
    leaf_of_u64 as small, ntt_forward_in_place, ntt_inverse_in_place, unit_basis, CubeMerkleTree,
    Digest, MerkleHasher,
};
use std::{collections::HashMap, sync::OnceLock};

const ZERO: F = F::ZERO;
const ONE: F = F::ONE;
const RHO: F = F::from_limbs([0, 0, 1, 0]);
const QUERIES: usize = 148;
type Result<T> = std::result::Result<T, &'static str>;

pub fn pack_32_bytes_bijective(bytes: [u8; 32]) -> F {
    F::from_le_bytes(bytes)
}

pub fn trace(x: F) -> bool {
    let l = x.limbs();
    ((l[2] & 0xc63a6da56da5a557).count_ones() + (l[3] & 0x26c6636dc63a6da5).count_ones()) % 2 == 1
}

fn beta(j: usize) -> F {
    let mut limbs = [0; 4];
    limbs[j / 64] = 1 << (j % 64);
    F::from_limbs(limbs)
}

pub fn dual_basis() -> &'static [F; 256] {
    static DUAL: OnceLock<[F; 256]> = OnceLock::new();
    DUAL.get_or_init(|| {
        let mut prev = vec![ONE];
        for level in 0..8 {
            let width = 1 << level;
            let g = if level == 0 { ONE } else { beta(width / 2) };
            let inv = g.inverse().expect("nonzero tower generator");
            let mut next = vec![ZERO; 2 * width];
            for (j, a) in prev.into_iter().enumerate() {
                let scaled = inv.mul(a);
                next[j] = a.add(beta(width).mul(scaled));
                next[width + j] = scaled;
            }
            prev = next;
        }
        prev.try_into().unwrap()
    })
}

pub fn pluck_bit_via_dual(x: F, bit: u8) -> bool {
    trace(x.mul(dual_basis()[usize::from(bit)]))
}

pub fn artin_schreier(t: F) -> F {
    t.square().add(t)
}

fn dot(a: &[F], b: &[F]) -> F {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b).fold(ZERO, |s, (&x, &y)| s.add(x.mul(y)))
}

/// Equation (6): column l is the XOR of X_i whose C_i has bit l set.
/// Accumulate once per input byte, then reduce the 256 buckets per byte position.
pub fn transpose_bit_matrix_256(coefficients: &[F], words: &[F]) -> Result<[F; 256]> {
    if coefficients.len() != words.len() {
        return Err("transpose length");
    }
    let mut buckets = vec![[ZERO; 256]; 32];
    for (&c, &x) in coefficients.iter().zip(words) {
        for (row, byte) in buckets.iter_mut().zip(c.to_le_bytes()) {
            row[usize::from(byte)] = row[usize::from(byte)].add(x);
        }
    }
    let mut out = [ZERO; 256];
    for (pos, row) in buckets.iter_mut().enumerate() {
        for bit in (0..8).rev() {
            let half = 1 << bit;
            for i in 0..half {
                out[8 * pos + bit] = out[8 * pos + bit].add(row[half + i]);
                row[i] = row[i].add(row[half + i]);
            }
        }
    }
    Ok(out)
}

struct ByteMap(Vec<[F; 256]>);
impl ByteMap {
    fn new(columns: &[F]) -> Self {
        assert_eq!(columns.len(), 256);
        Self(
            columns
                .chunks_exact(8)
                .map(|bits| {
                    let mut row = [ZERO; 256];
                    for j in 1usize..256 {
                        row[j] = row[j & (j - 1)].add(bits[j.trailing_zeros() as usize]);
                    }
                    row
                })
                .collect(),
        )
    }
    fn apply(&self, x: F) -> F {
        self.0
            .iter()
            .zip(x.to_le_bytes())
            .fold(ZERO, |s, (row, b)| s.add(row[usize::from(b)]))
    }
}

// For each l, form all 256 coefficients mu[k,l] by transposing the
// coordinate columns of beta_l * D_j and applying the dual-basis linear map.
fn tensor_matrix(d: &[F]) -> Vec<[F; 256]> {
    (0..256)
        .map(|l| {
            let products: Vec<_> = d.iter().map(|&v| beta(l).mul(v)).collect();
            dual_coefficients(&products)
        })
        .collect()
}
fn dual_coefficients(products: &[F]) -> [F; 256] {
    static MAP: OnceLock<ByteMap> = OnceLock::new();
    let dual_map = MAP.get_or_init(|| ByteMap::new(dual_basis()));
    let mut cols = [[0u8; 32]; 256];
    for (j, x) in products.iter().enumerate() {
        for (p, mut byte) in x.to_le_bytes().into_iter().enumerate() {
            while byte != 0 {
                let k = p * 8 + byte.trailing_zeros() as usize;
                cols[k][j / 8] |= 1 << (j % 8);
                byte &= byte - 1;
            }
        }
    }
    cols.map(|c| dual_map.apply(F::from_le_bytes(c)))
}

fn fields(bytes: &[u8]) -> Vec<F> {
    bytes
        .chunks_exact(32)
        .map(|b| F::from_le_bytes(b.try_into().unwrap()))
        .collect()
}
fn enc(values: &[F]) -> Vec<u8> {
    values.iter().flat_map(|x| x.to_le_bytes()).collect()
}
fn xof(tag: &[u8], data: &[u8], n: usize) -> Vec<u8> {
    let mut domain = b"MINIDREGG/W11/T256/V1/".to_vec();
    domain.extend_from_slice(tag);
    cshake256_xof(&domain, data, n)
}
struct Transcript(Vec<u8>);
impl Transcript {
    fn absorb(&mut self, data: &[u8]) {
        self.0.extend_from_slice(&(data.len() as u64).to_le_bytes());
        self.0.extend_from_slice(data);
    }
    fn draw(&mut self, label: &[u8], n: usize) -> Vec<F> {
        self.absorb(label);
        let out = xof(b"challenge", &self.0, 32 * n);
        self.absorb(&out);
        fields(&out)
    }
}
fn random(tag: &[u8], seed: &Digest, n: usize) -> Vec<F> {
    fields(&xof(tag, seed, 32 * n))
}

struct Reader<'a>(&'a [u8]);
impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8]> {
        let (head, tail) = self.0.split_at_checked(n).ok_or("truncated proof")?;
        self.0 = tail;
        Ok(head)
    }
    fn digest(&mut self) -> Result<Digest> {
        Ok(self.take(32)?.try_into().unwrap())
    }
    fn field(&mut self) -> Result<F> {
        Ok(F::from_le_bytes(self.digest()?))
    }
}
fn send(wire: &mut Vec<u8>, tr: &mut Transcript, values: &[F]) {
    let bytes = enc(values);
    tr.absorb(&bytes);
    wire.extend_from_slice(&bytes);
}
fn receive(rd: &mut Reader<'_>, tr: &mut Transcript, n: usize) -> Result<Vec<F>> {
    let b = rd.take(32 * n)?;
    tr.absorb(b);
    Ok(fields(b))
}

fn width(n: usize) -> Result<usize> {
    if !(1..=1 << 22).contains(&n) {
        return Err("payload length outside 1..=2^22");
    }
    Ok(n.div_ceil(32).next_power_of_two().max(512))
}
// Each systematic row uses k data symbols and k random symbols at rate 1/4.
fn code_len(k: usize) -> usize {
    8 * k
}

pub fn witness_codeword_symbols(payload_bytes: usize) -> Result<usize> {
    width(payload_bytes).map(code_len)
}

fn packed(bytes: &[u8]) -> Vec<F> {
    bytes
        .chunks(32)
        .map(|chunk| {
            let mut b = [0; 32];
            b[..chunk.len()].copy_from_slice(chunk);
            pack_32_bytes_bijective(b)
        })
        .collect()
}
fn evaluate(coeff: &[F], size: usize, offset: F) -> Vec<F> {
    let mut out = coeff.to_vec();
    out.resize(size, ZERO);
    ntt_forward_in_place(&mut out, &unit_basis(size.ilog2() as usize), offset).expect("unit basis");
    out
}
fn interpolate(mut values: Vec<F>) -> Vec<F> {
    let d = values.len().ilog2() as usize;
    ntt_inverse_in_place(&mut values, &unit_basis(d), ZERO).expect("unit basis");
    values
}
struct Oracle {
    word: Vec<F>,
    tree: CubeMerkleTree,
}
impl Oracle {
    fn new(word: Vec<F>) -> Self {
        let tree = MerkleHasher::new().build_tree(&word, word.len().ilog2() as usize);
        Self { word, tree }
    }
    fn from_coeff(coeff: &[F], k: usize) -> Self {
        Self::new(evaluate(coeff, code_len(k), small(code_len(k) as u64)))
    }
    fn root(&self) -> Digest {
        self.tree.root()
    }
}

// Canonical batch paths. At each level of the strided tree, the child addresses
// differ in the highest remaining bit. Send each missing sibling exactly once.
struct OpenPlan {
    indices: Vec<usize>,
    levels: Vec<Vec<(usize, Option<usize>, Option<usize>)>>,
}
impl OpenPlan {
    fn new(size: usize, mut indices: Vec<usize>) -> Self {
        indices.sort_unstable();
        indices.dedup();
        let mut current = indices.clone();
        let mut levels = Vec::new();
        let mut half = size / 2;
        while half > 0 {
            let mut parents: Vec<_> = current.iter().map(|i| i & (half - 1)).collect();
            parents.sort_unstable();
            parents.dedup();
            levels.push(
                parents
                    .iter()
                    .map(|&p| {
                        (
                            p,
                            current.binary_search(&p).ok(),
                            current.binary_search(&(p + half)).ok(),
                        )
                    })
                    .collect(),
            );
            current = parents;
            half /= 2;
        }
        Self { indices, levels }
    }
    fn write(&self, row: &Oracle, wire: &mut Vec<u8>) {
        for &i in &self.indices {
            wire.extend_from_slice(&row.word[i].to_le_bytes());
        }
        for (step, level) in self.levels.iter().enumerate() {
            let d = self.levels.len() - step - 1;
            for &(p, lo, hi) in level {
                if lo.is_none() || hi.is_none() {
                    let known = if hi.is_none() { p } else { p + (1 << d) };
                    wire.extend_from_slice(&row.tree.path(known)[d]);
                }
            }
        }
    }
    fn read(
        &self,
        rd: &mut Reader<'_>,
        hasher: &MerkleHasher,
        root: Digest,
    ) -> Result<HashMap<usize, F>> {
        let mut values = HashMap::new();
        let mut nodes = Vec::with_capacity(self.indices.len());
        for &i in &self.indices {
            let x = rd.field()?;
            values.insert(i, x);
            nodes.push(hasher.hash_leaf(x));
        }
        for level in &self.levels {
            let mut parents = Vec::with_capacity(level.len());
            for &(_, lo, hi) in level {
                let left = match lo {
                    Some(j) => nodes[j],
                    None => rd.digest()?,
                };
                let right = match hi {
                    Some(j) => nodes[j],
                    None => rd.digest()?,
                };
                parents.push(hasher.hash_node(&left, &right));
            }
            nodes = parents;
        }
        if nodes != [root] {
            return Err("Merkle authentication");
        }
        Ok(values)
    }
}
fn layer_plan(size: usize, queries: &[usize]) -> OpenPlan {
    let half = size / 2;
    OpenPlan::new(
        size,
        queries
            .iter()
            .flat_map(|i| {
                let lo = i & (half - 1);
                [lo, lo + half]
            })
            .collect(),
    )
}

struct Shared {
    coeff: Vec<F>,
    oracle: Oracle,
}
impl Shared {
    fn new(values: &[F], k: usize, seed: &Digest, tag: &[u8]) -> Self {
        let mut table = values.to_vec();
        table.resize(k, ZERO);
        table.extend(random(tag, seed, k));
        let coeff = interpolate(table);
        let oracle = Oracle::from_coeff(&coeff, k);
        Self { coeff, oracle }
    }
}

/// The externally pinned document commitment for a single proof. Generate fresh
/// secret content and proof seeds for each proof. Repeated openings of the same
/// sharing accumulate linear observations of its random half.
pub fn content_commitment(bytes: &[u8], seed: &Digest) -> Result<Digest> {
    let k = width(bytes.len())?;
    Ok(Shared::new(&packed(bytes), k, seed, b"content")
        .oracle
        .root())
}

#[derive(Clone, Copy, Debug)]
pub struct ByteAndDfa {
    pub left: u8,
    pub right: u8,
}
impl ByteAndDfa {
    pub fn accepts(self, bytes: &[u8]) -> bool {
        bytes.iter().fold(false, |s, &x| {
            s ^ (parity(x & self.left) && parity(x & self.right))
        })
    }
}
fn parity(b: u8) -> bool {
    b.count_ones() % 2 == 1
}
fn bit(v: bool) -> F {
    if v {
        ONE
    } else {
        ZERO
    }
}
fn affine(a: F, b: F, x: F) -> F {
    a.add(x.mul(a.add(b)))
}
fn horner(p: &[F], x: F) -> F {
    p.iter().rev().fold(ZERO, |y, &c| y.mul(x).add(c))
}
fn diff(x: F) -> F {
    x.square().add(x)
}
fn eq_table(point: &[F]) -> Vec<F> {
    let mut t = vec![ONE];
    for &r in point {
        let n = t.len();
        t.resize(2 * n, ZERO);
        for i in 0..n {
            t[n + i] = t[i].mul(r);
            t[i] = t[i].add(t[n + i]);
        }
    }
    t
}
fn tr_init(n: usize, dfa: ByteAndDfa, claim: bool, root: &Digest, aux: &Digest) -> Transcript {
    let mut t = Transcript(Vec::new());
    t.absorb(&(n as u64).to_le_bytes());
    t.absorb(&[dfa.left, dfa.right, claim as u8]);
    t.absorb(root);
    t.absorb(aux);
    t
}

// Aux slots: t_1..t_255, r, b, two terminal blinders, then sumcheck masks.
// g_j has degree d and vanishing Boolean sum: basis 1, X^2+X, ..., X^d+X.
const R: usize = 255;
const B: usize = 256;
const RA: usize = 257;
const RB: usize = 258;
const MASK: usize = 259;
fn degree(j: usize) -> usize {
    if j == 0 {
        5
    } else {
        3
    }
}
fn mask_at(j: usize) -> usize {
    if j == 0 {
        MASK
    } else {
        MASK + 5 + 3 * (j - 1)
    }
}
fn table_len(n: usize) -> usize {
    n.next_power_of_two().max(32)
}
fn g_poly(aux: &[F], j: usize) -> Vec<F> {
    let d = degree(j);
    let g = &aux[mask_at(j)..mask_at(j) + d];
    let mut p = vec![ZERO; d + 1];
    p[0] = g[0];
    for i in 2..=d {
        p[i] = g[i - 1];
        p[1] = p[1].add(p[i]);
    }
    p
}

struct Closing {
    point: Vec<F>,
    a: F,
    b: F,
    g: F,
}
fn sum_prove(
    bytes: &[u8],
    dfa: ByteAndDfa,
    aux: &[F],
    wire: &mut Vec<u8>,
    tr: &mut Transcript,
) -> Closing {
    let n = table_len(bytes.len());
    let mut rows = vec![[ZERO; 3]; n];
    for (row, &x) in rows.iter_mut().zip(bytes) {
        *row = [bit(parity(x & dfa.left)), bit(parity(x & dfa.right)), ONE];
    }
    sum_rows(rows, aux, wire, tr)
}

fn sum_rows(mut rows: Vec<[F; 3]>, aux: &[F], wire: &mut Vec<u8>, tr: &mut Transcript) -> Closing {
    let n = rows.len();
    let mut point = Vec::new();
    let mut g = ZERO;
    for j in 0..n.ilog2() as usize {
        let blind = if j == 0 {
            [aux[RA], aux[RB]]
        } else {
            [ZERO; 2]
        };
        let mut p = g_poly(aux, j);
        p[1] = p[1].add(g);
        for pair in rows.chunks_exact(2) {
            let lo = pair[0];
            let hi = pair[1];
            let a = [lo[0], lo[0].add(hi[0]).add(blind[0]), blind[0]];
            let b = [lo[1], lo[1].add(hi[1]).add(blind[1]), blind[1]];
            let v = [lo[2], lo[2].add(hi[2])];
            let terms = if j == 0 { 3 } else { 2 };
            for u in 0..terms {
                for w in 0..terms {
                    let ab = a[u].mul(b[w]);
                    for (s, &valid) in v.iter().enumerate() {
                        p[u + w + s] = p[u + w + s].add(ab.mul(valid));
                    }
                }
            }
        }
        send(wire, tr, &p);
        let x = tr.draw(b"sumcheck", 1)[0];
        point.push(x);
        g = horner(&g_poly(aux, j), x).add(g.mul(x));
        for i in 0..rows.len() / 2 {
            let lo = rows[2 * i];
            let hi = rows[2 * i + 1];
            rows[i] = std::array::from_fn(|s| affine(lo[s], hi[s], x));
            if j == 0 {
                rows[i][0] = rows[i][0].add(diff(x).mul(blind[0]));
                rows[i][1] = rows[i][1].add(diff(x).mul(blind[1]));
            }
        }
        rows.truncate(rows.len() / 2);
    }
    send(wire, tr, &rows[0][..2]);
    Closing {
        point,
        a: rows[0][0],
        b: rows[0][1],
        g,
    }
}
fn sum_verify(n: usize, claim: bool, rd: &mut Reader<'_>, tr: &mut Transcript) -> Result<Closing> {
    let mut current = bit(claim);
    let mut point = Vec::new();
    for j in 0..table_len(n).ilog2() as usize {
        let p = receive(rd, tr, degree(j) + 1)?;
        if p[0].add(horner(&p, ONE)) != current {
            return Err("sumcheck Boolean sum");
        }
        let x = tr.draw(b"sumcheck", 1)[0];
        if j == 0 && diff(x).is_zero() {
            return Err("degenerate blinding coordinate");
        }
        point.push(x);
        current = horner(&p, x);
    }
    let ab = receive(rd, tr, 2)?;
    let valid = eq_table(&point)[..n].iter().fold(ZERO, |s, &v| s.add(v));
    Ok(Closing {
        point,
        a: ab[0],
        b: ab[1],
        g: current.add(valid.mul(ab[0].mul(ab[1]))),
    })
}

enum Projection {
    Tensor { c: Vec<F>, mu: Vec<[F; 256]> },
    // One vector of bit coefficients per systematic polynomial.
    General(Vec<Vec<F>>),
}
struct Tensor {
    projection: Projection,
    aux_weights: Vec<F>,
    y: F,
}
impl Tensor {
    fn new(end: &Closing, dfa: ByteAndDfa, k: usize, tr: &mut Transcript) -> Self {
        let mix = tr.draw(b"terminal linear combination", 3);
        let y = dot(&mix, &[end.a, end.b, end.g]);
        let small_eq = eq_table(&end.point[..5]);
        let c = eq_table(&end.point[5..]);
        let d: Vec<_> = (0..256)
            .map(|j| {
                let h = 1 << (j % 8);
                let a = if dfa.left & h != 0 { mix[0] } else { ZERO };
                let b = if dfa.right & h != 0 { mix[1] } else { ZERO };
                a.add(b).mul(small_eq[j / 8])
            })
            .collect();
        Self {
            projection: Projection::Tensor {
                c,
                mu: tensor_matrix(&d),
            },
            aux_weights: mask_weights(end, k, &mix),
            y,
        }
    }
}
fn mask_weights(end: &Closing, k: usize, mix: &[F]) -> Vec<F> {
    let mut aux_weights = vec![ZERO; k];
    aux_weights[RA] = mix[0].mul(diff(end.point[0]));
    aux_weights[RB] = mix[1].mul(diff(end.point[0]));
    let mut suffix = mix[2];
    for (j, &x) in end.point.iter().enumerate().rev() {
        let at = mask_at(j);
        aux_weights[at] = suffix;
        let mut power = x;
        for i in 2..=degree(j) {
            power = power.mul(x);
            aux_weights[at + i - 1] = suffix.mul(power.add(x));
        }
        suffix = suffix.mul(x);
    }
    aux_weights
}
fn pads(aux: &[F]) -> [F; 256] {
    let t0 = (1..256).fold(ZERO, |v, j| v.add(beta(j).mul(aux[j - 1])));
    std::array::from_fn(|j| if j == 0 { t0 } else { aux[j - 1] })
}
fn rho_bit(x: F, j: usize) -> F {
    if x.limbs()[j / 64] & (1 << (j % 64)) == 0 {
        ZERO
    } else {
        RHO
    }
}
fn masked_trace_claims(tensor: &Tensor, words: &[&[F]], aux: &[F], pad: &[F; 256]) -> Vec<F> {
    let v = dot(&tensor.aux_weights, aux);
    let mut u: Vec<_> = (0..256)
        .map(|j| {
            dual_basis()[j]
                .mul(v)
                .add(rho_bit(tensor.y, j))
                .add(artin_schreier(pad[j]))
        })
        .collect();
    match &tensor.projection {
        Projection::Tensor { c, mu } => {
            let mut padded = words[0].to_vec();
            padded.resize(c.len(), ZERO);
            let w = transpose_bit_matrix_256(c, &padded).unwrap();
            for (col, &x) in mu.iter().zip(&w) {
                for j in 0..256 {
                    u[j] = u[j].add(col[j].mul(x));
                }
            }
        }
        Projection::General(rows) => {
            for (coeff, words) in rows.iter().zip(words) {
                for (bits, &x) in coeff.chunks(256).zip(*words) {
                    let q = dual_coefficients(bits);
                    for j in 0..256 {
                        u[j] = u[j].add(q[j].mul(x));
                    }
                }
            }
        }
    }
    u
}

struct Equation {
    weights: Vec<Vec<F>>,
    value: F,
}
fn linear_equation(tensor: Tensor, u: &[F], delta: &[F], a: F, eta: F) -> Equation {
    let gamma: Vec<_> = delta.iter().copied().map(F::square).collect();
    let k = tensor.aux_weights.len();
    let mut weights = match tensor.projection {
        Projection::Tensor { c, mu } => {
            let cols: Vec<_> = mu.iter().map(|col| dot(col, &gamma)).collect();
            let map = ByteMap::new(&cols);
            vec![c.iter().map(|&c| map.apply(c)).collect::<Vec<_>>()]
        }
        Projection::General(rows) => rows
            .iter()
            .map(|row| {
                row.chunks(256)
                    .map(|bits| dot(&dual_coefficients(bits), &gamma))
                    .collect()
            })
            .collect(),
    };
    for row in &mut weights {
        row.resize(k, ZERO);
    }
    let weight = dot(dual_basis(), &gamma);
    let mut aux: Vec<_> = tensor.aux_weights.iter().map(|&w| weight.mul(w)).collect();
    for j in 1..256 {
        let w9 = gamma[j].add(gamma[0].mul(beta(j)));
        let w8 = delta[j].add(delta[0].mul(beta(j)));
        aux[j - 1] = aux[j - 1].add(w9).add(eta.mul(w8));
    }
    aux[B] = aux[B].add(ONE);
    aux[R] = aux[R].add(eta);
    let mut value = a.square().add(eta.mul(a));
    for j in 0..256 {
        value = value.add(gamma[j].mul(u[j].add(rho_bit(tensor.y, j))));
    }
    weights.push(aux);
    Equation { weights, value }
}

// A hiding linear opening. On the systematic additive subspace H (size k),
// the sum of S = W*F + V*A + van_H*Q + R equals the claimed dot product.
// Q has degree <2k; R has degree <k-1, so its sum on H vanishes. Together
// they span every degree-<3k polynomial with zero sum on H.
fn vanish(k: usize, size: usize, offset: F) -> Vec<F> {
    let mut basis_poly = vec![ZERO; k + 1];
    basis_poly[k] = ONE;
    evaluate(&basis_poly, size, offset)
}
fn shifted_rem_weight(x: F, k: usize) -> F {
    let mut p = x;
    for _ in 0..k.ilog2() {
        p = p.square();
    }
    p.mul(x)
}
fn combo(v: &[F], mix: &[F], x: F, k: usize) -> F {
    let last = v.len() - 1;
    v[last]
        .add(dot(&v[..last], &mix[..last]))
        .add(mix[last].mul(shifted_rem_weight(x, k).mul(v[last - 1])))
}
fn pcs_polynomial(eq: &Equation, witnesses: &[&Shared], q: &[F], r: &[F]) -> Vec<F> {
    let k = eq.weights[0].len();
    let size = 4 * k;
    let mut s = evaluate(r, size, ZERO);
    let vh = vanish(k, size, ZERO);
    let vq = evaluate(q, size, ZERO);
    for i in 0..size {
        s[i] = s[i].add(vh[i].mul(vq[i]));
    }
    for (weight, row) in eq.weights.iter().zip(witnesses) {
        let w = evaluate(&interpolate(weight.clone()), size, ZERO);
        let f = evaluate(&row.coeff, size, ZERO);
        for i in 0..size {
            s[i] = s[i].add(w[i].mul(f[i]));
        }
    }
    let mut coeff = interpolate(s);
    debug_assert!(coeff[3 * k..].iter().all(|x| x.is_zero()));
    coeff.truncate(3 * k);
    coeff
}

// Each fold pairs x and x+p, then maps both to x^2+p*x. The affine
// interpolation through that pair is evaluated at the transcript challenge.
fn quotient(x: F, p: F) -> F {
    x.mul(x.add(p))
}
fn folded(lo: F, hi: F, x: F, alpha: F, inv: F) -> F {
    lo.add(x.add(alpha).mul(inv).mul(lo.add(hi)))
}
fn root_send(wire: &mut Vec<u8>, tr: &mut Transcript, root: Digest) {
    wire.extend_from_slice(&root);
    tr.absorb(&root);
}
fn root_receive(rd: &mut Reader<'_>, tr: &mut Transcript) -> Result<Digest> {
    let root = rd.digest()?;
    tr.absorb(&root);
    Ok(root)
}
fn positions(tr: &mut Transcript, size: usize) -> Vec<usize> {
    tr.draw(b"queries with replacement", QUERIES)
        .iter()
        .map(|x| x.limbs()[0] as usize & (size - 1))
        .collect()
}

fn pcs_prove(
    eq: Equation,
    witnesses: &[&Shared],
    seed: &Digest,
    wire: &mut Vec<u8>,
    tr: &mut Transcript,
) {
    let k = eq.weights[0].len();
    let size = code_len(k);
    let offset = small(size as u64);
    let q = random(b"quotient mask", seed, 2 * k);
    let r = random(b"remainder mask", seed, k - 1);
    let q_oracle = Oracle::from_coeff(&q, k);
    let r_oracle = Oracle::from_coeff(&r, k);
    let fri_mask = Oracle::from_coeff(&random(b"fri mask", seed, 2 * k), k);
    let mut rows: Vec<_> = witnesses.iter().map(|w| &w.oracle).collect();
    rows.extend([&q_oracle, &r_oracle, &fri_mask]);
    for row in &rows[witnesses.len()..] {
        root_send(wire, tr, row.root());
    }
    send(wire, tr, &pcs_polynomial(&eq, witnesses, &q, &r));
    let mix = tr.draw(b"proximity row combination", rows.len());
    let mut dom: Vec<_> = (0..size).map(|i| offset.add(small(i as u64))).collect();
    let mut values = vec![ZERO; rows.len()];
    let word = (0..size)
        .map(|i| {
            for (v, row) in values.iter_mut().zip(&rows) {
                *v = row.word[i];
            }
            combo(&values, &mix, dom[i], k)
        })
        .collect();
    let mut layers = vec![Oracle::new(word)];
    while layers.last().unwrap().word.len() > 4 {
        let layer = layers.last().unwrap();
        root_send(wire, tr, layer.root());
        let alpha = tr.draw(b"basefold", 1)[0];
        let half = dom.len() / 2;
        let p = dom[0].add(dom[half]);
        let inv = p.inverse().unwrap();
        let word = (0..half)
            .map(|i| folded(layer.word[i], layer.word[i + half], dom[i], alpha, inv))
            .collect();
        dom.truncate(half);
        for x in &mut dom {
            *x = quotient(*x, p);
        }
        layers.push(Oracle::new(word));
    }
    let last = &layers.last().unwrap().word;
    debug_assert!(last.iter().all(|x| x == &last[0]));
    send(wire, tr, &last[..1]);
    let queries = positions(tr, size);
    let main = OpenPlan::new(size, queries.clone());
    for row in &rows {
        main.write(row, wire);
    }
    for layer in &layers[..layers.len() - 1] {
        layer_plan(layer.word.len(), &queries).write(layer, wire);
    }
}

fn pcs_verify(
    eq: Equation,
    roots: &[Digest],
    rd: &mut Reader<'_>,
    tr: &mut Transcript,
) -> Result<()> {
    let k = eq.weights[0].len();
    let size = code_len(k);
    let off = small(size as u64);
    let mut rows = roots.to_vec();
    for _ in 0..3 {
        rows.push(root_receive(rd, tr)?);
    }
    let coeff = receive(rd, tr, 3 * k)?;
    // All higher novel-basis terms vanish on H.
    let sum = evaluate(&coeff[..k], k, ZERO)
        .into_iter()
        .fold(ZERO, F::add);
    if sum != eq.value {
        return Err("linear opening systematic sum");
    }
    let s = evaluate(&coeff, size, off);
    let weights: Vec<_> = eq
        .weights
        .into_iter()
        .map(|w| evaluate(&interpolate(w), size, off))
        .collect();
    let van = vanish(k, size, off);
    let mix = tr.draw(b"proximity row combination", rows.len());
    let mut layers = Vec::new();
    let mut betas = unit_basis(size.ilog2() as usize);
    let mut len = size;
    while len > 4 {
        let root = root_receive(rd, tr)?;
        let alpha = tr.draw(b"basefold", 1)[0];
        let pivot = betas.pop().unwrap();
        let inv = pivot.inverse().map_err(|_| "zero fold pivot")?;
        layers.push((len, root, alpha, pivot, inv));
        for b in &mut betas {
            *b = quotient(*b, pivot);
        }
        len /= 2;
    }
    let final_value = receive(rd, tr, 1)?[0];
    let hasher = MerkleHasher::new();
    let queries = positions(tr, size);
    let main = OpenPlan::new(size, queries.clone());
    let shares = rows
        .iter()
        .map(|&root| main.read(rd, &hasher, root))
        .collect::<Result<Vec<_>>>()?;
    let folds = layers
        .iter()
        .map(|&(len, root, _, _, _)| layer_plan(len, &queries).read(rd, &hasher, root))
        .collect::<Result<Vec<_>>>()?;
    for idx in queries {
        let v: Vec<_> = shares.iter().map(|row| row[&idx]).collect();
        let mut check = van[idx].mul(v[roots.len()]).add(v[roots.len() + 1]);
        for (w, &value) in weights.iter().zip(&v) {
            check = check.add(w[idx].mul(value));
        }
        if check != s[idx] {
            return Err("linear opening coset identity");
        }
        let mut x = off.add(small(idx as u64));
        let mut expected = combo(&v, &mix, x, k);
        for (&(len, _, alpha, pivot, inv), fold) in layers.iter().zip(&folds) {
            let half = len / 2;
            let lo = idx & (half - 1);
            let left = fold[&lo];
            let right = fold[&(lo + half)];
            let high = idx & half != 0;
            if expected != if high { right } else { left } {
                return Err("BaseFold chain");
            }
            if high {
                x = x.add(pivot);
            }
            expected = folded(left, right, x, alpha, inv);
            x = quotient(x, pivot);
        }
        if expected != final_value {
            return Err("BaseFold terminal constant");
        }
    }
    Ok(())
}

/// A fresh secret proof seed supplies independent cSHAKE streams for each mask.
/// The verifier pins the expected content root, length, DFA, and acceptance bit.
pub fn prove(
    bytes: &[u8],
    dfa: ByteAndDfa,
    claim: bool,
    content_seed: &Digest,
    proof_seed: &Digest,
) -> Result<(Digest, Vec<u8>)> {
    prove_inner(bytes, dfa, claim, content_seed, proof_seed, ZERO)
}
fn prove_inner(
    bytes: &[u8],
    dfa: ByteAndDfa,
    claim: bool,
    content_seed: &Digest,
    proof_seed: &Digest,
    b_error: F,
) -> Result<(Digest, Vec<u8>)> {
    let k = width(bytes.len())?;
    if dfa.accepts(bytes) != claim {
        return Err("incorrect DFA claim");
    }
    let words = packed(bytes);
    let f = Shared::new(&words, k, content_seed, b"content");
    let mut aux = random(b"trace and sumcheck masks", proof_seed, k);
    aux[B] = aux[R].square().add(b_error);
    let a = Shared::new(&aux, k, proof_seed, b"aux sharing");
    let root = f.oracle.root();
    let mut tr = tr_init(bytes.len(), dfa, claim, &root, &a.oracle.root());
    let mut wire = a.oracle.root().to_vec();
    let end = sum_prove(bytes, dfa, &aux, &mut wire, &mut tr);
    if diff(end.point[0]).is_zero() {
        return Err("degenerate blinding coordinate");
    }
    let tensor = Tensor::new(&end, dfa, k, &mut tr);
    finish_proof(
        tensor,
        &[&words],
        &aux,
        &[&f, &a],
        proof_seed,
        &mut wire,
        &mut tr,
    );
    Ok((root, wire))
}

fn finish_proof(
    tensor: Tensor,
    words: &[&[F]],
    aux: &[F],
    witnesses: &[&Shared],
    seed: &Digest,
    wire: &mut Vec<u8>,
    tr: &mut Transcript,
) {
    let pad = pads(aux);
    let u = masked_trace_claims(&tensor, words, aux, &pad);
    send(wire, tr, &u);
    let delta = tr.draw(b"independent square weights", 256);
    let blinded = aux[R].add(dot(&delta, &pad));
    send(wire, tr, &[blinded]);
    let eta = tr.draw(b"merge linear checks", 1)[0];
    pcs_prove(
        linear_equation(tensor, &u, &delta, blinded, eta),
        witnesses,
        seed,
        wire,
        tr,
    );
}

pub fn verify(root: &Digest, n: usize, dfa: ByteAndDfa, claim: bool, proof: &[u8]) -> Result<()> {
    let k = width(n)?;
    let mut rd = Reader(proof);
    let aux = rd.digest()?;
    let mut tr = tr_init(n, dfa, claim, root, &aux);
    let end = sum_verify(n, claim, &mut rd, &mut tr)?;
    let tensor = Tensor::new(&end, dfa, k, &mut tr);
    finish_verify(tensor, &[*root, aux], &mut rd, &mut tr)
}

fn finish_verify(
    tensor: Tensor,
    roots: &[Digest],
    rd: &mut Reader<'_>,
    tr: &mut Transcript,
) -> Result<()> {
    let u = receive(rd, tr, 256)?;
    if u.iter().copied().any(trace) {
        return Err("trace-one masked claim");
    }
    let delta = tr.draw(b"independent square weights", 256);
    let a = receive(rd, tr, 1)?[0];
    let eta = tr.draw(b"merge linear checks", 1)[0];
    pcs_verify(linear_equation(tensor, &u, &delta, a, eta), roots, rd, tr)?;
    if !rd.0.is_empty() {
        return Err("trailing proof bytes");
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn committed_wrong_state_transition() {
        let bytes = b"sk-";
        let dfa = DfaTable::no_sk_dash();
        let c = Circuit::compile(&dfa, bytes.len()).unwrap();
        let claim = dfa.accepts(bytes);
        let mut words = c.witness(&dfa, bytes);
        // State plane zero at time one, after reading 's'. Recommit the
        // erroneous plane, derive fresh challenges, and complete the proof.
        words[1][0] = words[1][0].add(beta(1));
        let (root, wire) = prove_dfa_trace(&c, &words, &dfa, claim, &[3; 32], &[4; 32]).unwrap();
        assert_eq!(
            verify_dfa(&root, bytes.len(), &dfa, claim, &wire),
            Err("sumcheck Boolean sum")
        );
    }

    #[test]
    fn forged_square_committed_before_challenges() {
        let bytes = b"not a multiple of thirty two";
        let dfa = ByteAndDfa {
            left: 1,
            right: 128,
        };
        let claim = dfa.accepts(bytes);
        let (root, proof) = prove_inner(bytes, dfa, claim, &[33; 32], &[34; 32], ONE).unwrap();
        assert_eq!(
            verify(&root, bytes.len(), dfa, claim, &proof),
            Err("linear opening systematic sum")
        );
    }
}

// Compile an arbitrary public byte transition table into shared Boolean multiplexers.
// Each node y = select(s,lo,hi) contributes one AND equation s*(lo+hi) = y+lo.
// Its truth value and the state bits are committed in packed private bit planes.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum Wire {
    Const(bool),
    Byte(usize),
    Plane(usize),
}
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
struct Mux {
    selector: Wire,
    low: Wire,
    high: Wire,
}

struct Circuit {
    state_bits: usize,
    nodes: Vec<Mux>,
    next: Vec<Wire>,
    hit: Wire,
    initial: usize,
    n: usize,
    times: usize,
    gates: usize,
    k: usize,
}
#[derive(Clone, Copy)]
enum Site {
    Const(bool),
    Bit(usize, usize),
}
const Z: Site = Site::Const(false);
const I: Site = Site::Const(true);
type Pair = [Site; 2];

impl Circuit {
    fn compile(dfa: &DfaTable, n: usize) -> Result<Self> {
        let k = width(n)?;
        dfa.validate().map_err(|_| "malformed DFA")?;
        let state_bits = dfa.states.next_power_of_two().ilog2() as usize;
        let mut nodes = Vec::new();
        let mut intern = HashMap::new();
        let mut outputs = Vec::new();
        for out in 0..=state_bits {
            let mut layer: Vec<_> = (0..(256 << state_bits))
                .map(|i| {
                    // Unreachable state encodings take transition to state zero.
                    let next = dfa.delta.get(i).copied().unwrap_or(0);
                    Wire::Const(if out == state_bits {
                        dfa.accepting[next]
                    } else {
                        next & (1 << out) != 0
                    })
                })
                .collect();
            for j in 0..8 + state_bits {
                let selector = if j < 8 {
                    Wire::Byte(j)
                } else {
                    Wire::Plane(j - 8)
                };
                for i in 0..layer.len() / 2 {
                    let low = layer[2 * i];
                    let high = layer[2 * i + 1];
                    layer[i] = if low == high {
                        low
                    } else if low == Wire::Const(false) && high == Wire::Const(true) {
                        selector
                    } else {
                        let gate = Mux {
                            selector,
                            low,
                            high,
                        };
                        let id = *intern.entry(gate).or_insert_with(|| {
                            let id = state_bits + nodes.len();
                            nodes.push(gate);
                            id
                        });
                        Wire::Plane(id)
                    };
                }
                layer.truncate(layer.len() / 2);
            }
            outputs.push(layer[0]);
        }
        let hit = outputs.pop().unwrap();
        let times = n.next_power_of_two();
        let gates = (nodes.len() + state_bits + 1).next_power_of_two();
        if times
            .checked_mul(gates)
            .is_none_or(|cells| cells > (1 << 21))
        {
            return Err("DFA sumcheck exceeds 2^22 product rows");
        }
        Ok(Self {
            state_bits,
            nodes,
            next: outputs,
            hit,
            initial: dfa.initial,
            n,
            times,
            gates,
            k,
        })
    }
    fn private_bits(&self) -> usize {
        (self.state_bits + self.nodes.len()) * self.n
    }
    fn extra_rows(&self) -> usize {
        self.private_bits().div_ceil(self.k * 256)
    }
    fn cube(&self) -> usize {
        (2 * self.times * self.gates).max(32)
    }
    fn site(&self, w: Wire, t: usize) -> Site {
        match w {
            Wire::Const(c) => Site::Const(c),
            Wire::Byte(j) => Site::Bit(0, 8 * t + j),
            Wire::Plane(j) => {
                let i = j * self.n + t;
                let cap = 256 * self.k;
                Site::Bit(1 + i / cap, i % cap)
            }
        }
    }
    fn visit(&self, claim: bool, mut term: impl FnMut(usize, Pair, Pair)) {
        for t in 0..self.n {
            for (g, node) in self.nodes.iter().enumerate() {
                let i = 2 * (g * self.times + t);
                let lo = self.site(node.low, t);
                term(
                    i,
                    [self.site(node.selector, t), Z],
                    [lo, self.site(node.high, t)],
                );
                term(
                    i + 1,
                    [self.site(Wire::Plane(self.state_bits + g), t), lo],
                    [I, Z],
                );
            }
            for (j, &next) in self.next.iter().enumerate() {
                let expected = if t == 0 {
                    Site::Const(self.initial & (1 << j) != 0)
                } else {
                    self.site(next, t - 1)
                };
                let i = 2 * ((self.nodes.len() + j) * self.times + t);
                term(i, [self.site(Wire::Plane(j), t), expected], [I, Z]);
            }
        }
        let t = self.n - 1;
        let i = 2 * ((self.nodes.len() + self.state_bits) * self.times + t);
        term(i, [self.site(self.hit, t), Site::Const(claim)], [I, Z]);
    }
    fn witness(&self, dfa: &DfaTable, bytes: &[u8]) -> Vec<Vec<F>> {
        let mut raw = vec![0u8; self.private_bits().div_ceil(8)];
        let mut state = dfa.initial;
        let mut planes = vec![false; self.state_bits + self.nodes.len()];
        for (t, &b) in bytes.iter().enumerate() {
            for (j, plane) in planes[..self.state_bits].iter_mut().enumerate() {
                *plane = state & (1 << j) != 0;
            }
            for (g, node) in self.nodes.iter().enumerate() {
                let read = |w| match w {
                    Wire::Const(c) => c,
                    Wire::Byte(j) => b & (1u8 << j) != 0,
                    Wire::Plane(j) => planes[j],
                };
                planes[self.state_bits + g] = if read(node.selector) {
                    read(node.high)
                } else {
                    read(node.low)
                };
            }
            for (j, v) in planes.iter().enumerate() {
                if *v {
                    let i = j * self.n + t;
                    raw[i / 8] |= 1 << (i % 8);
                }
            }
            state = dfa.step(state, b);
        }
        let mut words = vec![packed(bytes)];
        words.extend(raw.chunks(32 * self.k).map(packed));
        words
    }
    fn tensor(&self, end: &Closing, claim: bool, checks: &[F], tr: &mut Transcript) -> Tensor {
        let mix = tr.draw(b"terminal linear combination", 3);
        let mut y = dot(&mix, &[end.a, end.b, end.g]);
        let mut weights = vec![vec![ZERO; 8 * self.n]];
        let cap = 256 * self.k;
        for start in (0..self.private_bits()).step_by(cap) {
            weights.push(vec![ZERO; cap.min(self.private_bits() - start)]);
        }
        let eq = eq_table(&end.point);
        self.visit(claim, |i, left, right| {
            let w = eq[i].mul(mix[0]);
            let a = w.mul(checks[i / 2]);
            let b = eq[i].mul(mix[1]);
            for (pair, weight) in [(left, a), (right, b)] {
                for site in pair {
                    match site {
                        Site::Const(true) => y = y.add(weight),
                        Site::Const(false) => {}
                        Site::Bit(row, j) => weights[row][j] = weights[row][j].add(weight),
                    }
                }
            }
        });
        Tensor {
            projection: Projection::General(weights),
            aux_weights: mask_weights(end, self.k, &mix),
            y,
        }
    }
}
fn dfa_transcript(n: usize, dfa: &DfaTable, claim: bool, roots: &[Digest]) -> Transcript {
    let mut tr = Transcript(Vec::new());
    tr.absorb(b"table DFA");
    tr.absorb(&(n as u64).to_le_bytes());
    tr.absorb(&automaton_commit(dfa));
    tr.absorb(&[claim as u8]);
    for root in roots {
        tr.absorb(root);
    }
    tr
}
fn constraint_weights(c: &Circuit, tr: &mut Transcript) -> Vec<F> {
    let point = tr.draw(
        b"DFA gate and time equality weight",
        (c.times * c.gates).ilog2() as usize,
    );
    eq_table(&point)
}

/// Prove acceptance or rejection of a public transition table on the committed
/// bytes. Shared multiplexers check byte lookup, initial state, every transition,
/// and the final acceptance bit. The content root is independent of the DFA.
pub fn prove_dfa(
    bytes: &[u8],
    dfa: &DfaTable,
    claim: bool,
    content_seed: &Digest,
    proof_seed: &Digest,
) -> Result<(Digest, Vec<u8>)> {
    let c = Circuit::compile(dfa, bytes.len())?;
    if dfa.accepts(bytes) != claim {
        return Err("incorrect DFA claim");
    }
    let words = c.witness(dfa, bytes);
    prove_dfa_trace(&c, &words, dfa, claim, content_seed, proof_seed)
}

fn prove_dfa_trace(
    c: &Circuit,
    words: &[Vec<F>],
    dfa: &DfaTable,
    claim: bool,
    content_seed: &Digest,
    proof_seed: &Digest,
) -> Result<(Digest, Vec<u8>)> {
    let mut shares = vec![Shared::new(&words[0], c.k, content_seed, b"content")];
    for (j, row) in words.iter().enumerate().skip(1) {
        let mut tag = b"dfa private plane sharing".to_vec();
        tag.extend_from_slice(&(j as u64).to_le_bytes());
        shares.push(Shared::new(row, c.k, proof_seed, &tag));
    }
    let mut aux = random(b"trace and sumcheck masks", proof_seed, c.k);
    aux[B] = aux[R].square();
    shares.push(Shared::new(&aux, c.k, proof_seed, b"aux sharing"));
    let roots: Vec<_> = shares.iter().map(|s| s.oracle.root()).collect();
    let mut tr = dfa_transcript(c.n, dfa, claim, &roots);
    let mut wire = roots[1..].concat();
    let checks = constraint_weights(c, &mut tr);
    let mut rows = vec![[ZERO, ZERO, ONE]; c.cube()];
    c.visit(claim, |i, left, right| {
        let read = |s| match s {
            Site::Const(v) => v,
            Site::Bit(r, j) => words[r][j / 256].limbs()[(j / 64) % 4] & (1 << (j % 64)) != 0,
        };
        rows[i][0] = if read(left[0]) ^ read(left[1]) {
            checks[i / 2]
        } else {
            ZERO
        };
        rows[i][1] = bit(read(right[0]) ^ read(right[1]));
    });
    let end = sum_rows(rows, &aux, &mut wire, &mut tr);
    if diff(end.point[0]).is_zero() {
        return Err("degenerate blinding coordinate");
    }
    let tensor = c.tensor(&end, claim, &checks, &mut tr);
    finish_proof(
        tensor,
        &words.iter().map(Vec::as_slice).collect::<Vec<_>>(),
        &aux,
        &shares.iter().collect::<Vec<_>>(),
        proof_seed,
        &mut wire,
        &mut tr,
    );
    Ok((roots[0], wire))
}
pub fn verify_dfa(
    root: &Digest,
    n: usize,
    dfa: &DfaTable,
    claim: bool,
    proof: &[u8],
) -> Result<()> {
    let c = Circuit::compile(dfa, n)?;
    let mut rd = Reader(proof);
    let mut roots = vec![*root];
    for _ in 0..1 + c.extra_rows() {
        roots.push(rd.digest()?);
    }
    let mut tr = dfa_transcript(n, dfa, claim, &roots);
    let checks = constraint_weights(&c, &mut tr);
    let end = sum_verify(c.cube(), false, &mut rd, &mut tr)?;
    let tensor = c.tensor(&end, claim, &checks, &mut tr);
    finish_verify(tensor, &roots, &mut rd, &mut tr)
}
