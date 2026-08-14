//! `[PROVER-rank1]` — the rank-1 gradient check, mirroring
//! `Selvage/Rank1GradientCheck.lean`.
//!
//! Substrate, said out loud: UNVERIFIED COMPUTE with the Lean file as its
//! specification. Lean proves the check's completeness (`rank1_complete`), its
//! soundness (`rank1_sound`, `(mi+mj)/|F|`), the batch generalization
//! (`rankK_sound`) and the whole optimizer step (`sgd_step_sound`) about ITS
//! objects; this file re-computes the same shapes so the prover produces the
//! claim the Lean proved sound. There is no formal semantics of Rust, so the
//! agreement is established by the F₅ vectors the Lean side `decide`s
//! (`prover/tests/rank1_gradient.rs`) — never called refinement or verification.
//!
//! ## What the check IS
//!
//! For a linear layer `y = Wx`, backprop's weight gradient is a rank-1 outer
//! product `∇W = δ·xᵀ`. Its multilinear extension FACTORS,
//!
//! ```text
//!     (δ ⊗ x)^(r) = δ̂(r_row) · x̂(r_col)
//! ```
//!
//! so a claimed gradient is checked by ONE multiplication of TWO single-variable
//! openings at a common random point. There is no sum over an inner index, hence
//! **no sumcheck round at all** — strictly cheaper than the matmul boundary
//! `Ĉ(r) = Σ_k Â(r_i,k)·B̂(k,r_j)`, which needs a sumcheck over `k`.
//!
//! ## Index convention (pinned by the Lean side)
//!
//! A matrix entry is ONE hypercube index on `mi + mj` bits. Lean's `rowHalf` is
//! coordinates `0 … mi−1` and `colHalf` is `mi … mi+mj−1`; the crate's LSB-first
//! table convention then puts the ROW index in the LOW bits:
//!
//! ```text
//!     g[k] = d[k & ((1 << mi) − 1)] * x[k >> mi]
//! ```
//!
//! and a challenge point splits as `point[..mi]` (row) and `point[mi..]` (column).
//! `rank1_refuses_the_transpose` on the Lean side is the tooth that makes this
//! convention load-bearing rather than decorative: swapping the halves is a
//! different matrix and the check rejects it.
//!
//! ## What this does NOT establish
//!
//! The check is entirely relative to the committed `δ` and `x`. That `δ` is the
//! correct backpropagated error is a SEPARATE obligation (the chain rule); the
//! nonlinearity's derivative is not mentioned; and the data being in-distribution
//! is not a proof-system property at all. `Selvage/Rank1GradientCheck.lean` states
//! the first two as theorems (`rank1_blind_to_the_error`, `outerTable_rescale`).

use crate::sumcheck::{add_mod, fold_table, mul_mod, sub_mod, Fp};

/// `m` from a table of length `2^m`; panics if the length is not a power of two.
fn cube_dim(f: &[Fp]) -> usize {
    assert!(
        !f.is_empty() && f.len().is_power_of_two(),
        "table length {} is not a power of two",
        f.len()
    );
    f.len().trailing_zeros() as usize
}

/// **The MLE at a point by table folding** — `O(2^m)` total, against the literal
/// chi-basis sum's `O(m·2^m)`. Binds coordinate `0` first, exactly the LSB
/// recurrence `f̂(x ∷ xs) = Â(xs) + x·Δ̂(xs)` that
/// `Selvage/MultilinearZeroTest.lean`'s `mle_lsb_halves` states.
///
/// Pinned to the literal mirror by `folded_mle_agrees_with_the_literal_chi_sum`;
/// without that test this would REPLACE the Lean-mirroring path rather than
/// accelerate it.
pub fn mle_eval_folded(f: &[Fp], point: &[Fp], p: u64) -> Fp {
    let m = cube_dim(f);
    assert_eq!(
        point.len(),
        m,
        "point dimension {} != table dimension {m}",
        point.len()
    );
    if m == 0 {
        return f[0] % p;
    }
    let mut table: Vec<Fp> = f.iter().map(|v| v % p).collect();
    for &r in point {
        table = fold_table(&table, r, p);
    }
    table[0]
}

/// **The rank-1 outer product table** `(δ ⊗ x)(i,j) = δ(i)·x(j)` — for a linear
/// layer, the weight gradient `∇W = δ·xᵀ`. This is the `2^{mi+mj}`-element object
/// the check exists to AVOID materializing; it is built here only so tests and the
/// baseline measurement have something to compare against.
pub fn outer_table(d: &[Fp], x: &[Fp], p: u64) -> Vec<Fp> {
    let mi = cube_dim(d);
    let _ = cube_dim(x);
    let mask = (1usize << mi) - 1;
    let mut out = Vec::with_capacity(d.len() * x.len());
    for k in 0..(d.len() * x.len()) {
        out.push(mul_mod(d[k & mask] % p, x[k >> mi] % p, p));
    }
    out
}

/// **The batch gradient table** `Σ_k δ_k·x_kᵀ` — rank at most `K`.
pub fn outer_sum_table(ds: &[Vec<Fp>], xs: &[Vec<Fp>], p: u64) -> Vec<Fp> {
    assert_eq!(ds.len(), xs.len(), "one δ per x");
    assert!(!ds.is_empty(), "empty batch has no dimensions");
    let mi = cube_dim(&ds[0]);
    let mask = (1usize << mi) - 1;
    let n = ds[0].len() * xs[0].len();
    let mut out = vec![0u64; n];
    for (d, x) in ds.iter().zip(xs.iter()) {
        assert_eq!(cube_dim(d), mi, "batch shares one row dimension");
        assert_eq!(d.len() * x.len(), n, "batch shares one matrix shape");
        for (k, slot) in out.iter_mut().enumerate() {
            *slot = add_mod(*slot, mul_mod(d[k & mask] % p, x[k >> mi] % p, p), p);
        }
    }
    out
}

/// **The optimizer step** `W' = W − η·(δ ⊗ x)`, materialized. The point of
/// `sgd_step_accepts` is that a verifier never needs this.
pub fn sgd_step_table(w: &[Fp], eta: Fp, d: &[Fp], x: &[Fp], p: u64) -> Vec<Fp> {
    let mi = cube_dim(d);
    assert_eq!(w.len(), d.len() * x.len(), "weights match the layer shape");
    let mask = (1usize << mi) - 1;
    w.iter()
        .enumerate()
        .map(|(k, &wk)| {
            let g = mul_mod(d[k & mask] % p, x[k >> mi] % p, p);
            sub_mod(wk % p, mul_mod(eta % p, g, p), p)
        })
        .collect()
}

/// The three openings the rank-1 check consumes, at a common challenge point.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rank1Openings {
    /// `Ĝ(r)` — the claimed gradient's opening.
    pub g: Fp,
    /// `δ̂(r_row)` — a `mi`-variable opening.
    pub d: Fp,
    /// `x̂(r_col)` — a `mj`-variable opening.
    pub x: Fp,
}

/// Split a challenge point into its row and column halves — Lean's
/// `rowHalf`/`colHalf`.
pub fn split_point(point: &[Fp], mi: usize) -> (&[Fp], &[Fp]) {
    assert!(mi <= point.len(), "row dimension exceeds the point");
    point.split_at(mi)
}

/// Produce the three openings from the tables. **The prover's incremental work
/// for the gradient claim is the last two lines**: two MLE evaluations on tables
/// of size `2^mi` and `2^mj`, never on the `2^{mi+mj}` matrix. `g` is whatever the
/// weight commitment already opens to; here it is computed from a supplied table
/// so tests can feed a LIE.
pub fn rank1_openings(g: &[Fp], d: &[Fp], x: &[Fp], point: &[Fp], p: u64) -> Rank1Openings {
    let mi = cube_dim(d);
    let (row, col) = split_point(point, mi);
    Rank1Openings {
        g: mle_eval_folded(g, point, p),
        d: mle_eval_folded(d, row, p),
        x: mle_eval_folded(x, col, p),
    }
}

/// **The check**: `Ĝ(r) = δ̂(r_row)·x̂(r_col)`. One multiplication and one
/// comparison — the verifier's entire arithmetic on top of the openings.
pub fn rank1_accepts(o: &Rank1Openings, p: u64) -> bool {
    o.g % p == mul_mod(o.d, o.x, p)
}

/// **The batch check**: `Ĝ(r) = Σ_k δ̂_k(r_row)·x̂_k(r_col)` — `K` verifier
/// multiplications, and (per the Lean `rankK_sound`) the SAME soundness bound: no
/// round is added, so the error does not grow with the batch.
pub fn rank_k_accepts(g_open: Fp, d_opens: &[Fp], x_opens: &[Fp], p: u64) -> bool {
    assert_eq!(d_opens.len(), x_opens.len(), "one δ per x");
    let rhs = d_opens
        .iter()
        .zip(x_opens.iter())
        .fold(0, |acc, (&dk, &xk)| add_mod(acc, mul_mod(dk, xk, p), p));
    g_open % p == rhs
}

/// **The whole SGD step for a linear layer**:
/// `Ŵ'(r) = Ŵ(r) − η·δ̂(r_row)·x̂(r_col)`.
///
/// Three openings at ONE common point and zero rounds. The gradient is never
/// committed and never materialized — which is the piece that makes the rank-1
/// factorization worth having rather than merely true.
pub fn sgd_step_accepts(w_open: Fp, w_prime_open: Fp, eta: Fp, d_open: Fp, x_open: Fp, p: u64) -> bool {
    let g = mul_mod(d_open, x_open, p);
    w_prime_open % p == sub_mod(w_open % p, mul_mod(eta % p, g, p), p)
}

/// The five cubic-sumcheck tables for the SAME statement proved as a CIRCUIT:
/// the zerocheck `Σ_b eq(z,b)·(δ(b_row)·x(b_col) − G(b)) = 0`, i.e. the Lean
/// `cubicForm E A B C D = Ê·(Â·B̂ + Ĉ·D̂)` at `A = δ` broadcast over rows,
/// `B = x` broadcast over columns, `C = G`, `D = −1`.
///
/// This is the BASELINE the rank-1 check is measured against, and it is the
/// repo's own landed degree-3 engine rather than an invented number: every table
/// is `2^{mi+mj}` long, so the prover touches the whole matrix five times.
pub fn zerocheck_tables(
    g: &[Fp],
    d: &[Fp],
    x: &[Fp],
    z: &[Fp],
    p: u64,
) -> crate::sumcheck::CubicTables {
    let mi = cube_dim(d);
    let n = g.len();
    assert_eq!(n, d.len() * x.len(), "gradient matches the layer shape");
    assert_eq!(z.len(), cube_dim(g), "zerocheck point has one entry per bit");
    let mask = (1usize << mi) - 1;
    let e = eq_table(z, p);
    let a: Vec<Fp> = (0..n).map(|k| d[k & mask] % p).collect();
    let b: Vec<Fp> = (0..n).map(|k| x[k >> mi] % p).collect();
    let c: Vec<Fp> = g.iter().map(|v| v % p).collect();
    let dd: Vec<Fp> = vec![sub_mod(0, 1 % p, p); n];
    crate::sumcheck::CubicTables { e, a, b, c, d: dd }
}

/// The equality table `b ↦ eq(z, b)` — Lean's `eqMle z (cubePt b)`, built in
/// `O(2^m)` by the standard doubling recurrence.
///
/// The doubling APPENDS blocks rather than interleaving them, which is what keeps
/// the table LSB-first (coordinate `i` is index bit `i`) and so consistent with
/// every other table in the crate; interleaving would silently reverse the bit
/// order and the zerocheck baseline would be weighting the wrong corners.
pub fn eq_table(z: &[Fp], p: u64) -> Vec<Fp> {
    let mut out = vec![1 % p];
    for &zi in z {
        let lo: Vec<Fp> = out
            .iter()
            .map(|&w| mul_mod(w, sub_mod(1 % p, zi % p, p), p))
            .collect();
        let hi: Vec<Fp> = out.iter().map(|&w| mul_mod(w, zi % p, p)).collect();
        out = lo;
        out.extend(hi);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sumcheck::mle_eval;

    /// A small deterministic table generator — no rand dependency in the crate.
    fn table(len: usize, seed: u64, p: u64) -> Vec<Fp> {
        let mut s = seed | 1;
        (0..len)
            .map(|_| {
                s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                (s >> 17) % p
            })
            .collect()
    }

    /// The fast path is an ACCELERATION of the Lean-mirroring literal sum, not a
    /// replacement for it: the two agree at every dimension up to 10.
    #[test]
    fn folded_mle_agrees_with_the_literal_chi_sum() {
        let p = 97;
        for m in 0..=10 {
            let f = table(1 << m, 12345 + m as u64, p);
            let point = table(m, 777 + m as u64, p);
            assert_eq!(
                mle_eval_folded(&f, &point, p),
                mle_eval(&f, &point, p),
                "folded vs literal at m = {m}"
            );
        }
    }

    /// `mle_outerTable`, on data: the MLE of an outer product is the product of
    /// the two factors' MLEs — the identity the whole check rests on.
    #[test]
    fn outer_product_mle_factors() {
        let p = crate::babybear::P;
        for (mi, mj) in [(1, 1), (2, 3), (4, 4), (5, 2)] {
            let d = table(1 << mi, 11 * mi as u64 + 1, p);
            let x = table(1 << mj, 29 * mj as u64 + 5, p);
            let g = outer_table(&d, &x, p);
            let point = table(mi + mj, 4242, p);
            let (row, col) = split_point(&point, mi);
            assert_eq!(
                mle_eval_folded(&g, &point, p),
                mul_mod(
                    mle_eval_folded(&d, row, p),
                    mle_eval_folded(&x, col, p),
                    p
                ),
                "factorization at ({mi}, {mj})"
            );
        }
    }

    /// Completeness: the true gradient is accepted at every point tried.
    #[test]
    fn true_gradient_is_accepted() {
        let p = crate::babybear::P;
        let (mi, mj) = (4, 4);
        let d = table(1 << mi, 7, p);
        let x = table(1 << mj, 13, p);
        let g = outer_table(&d, &x, p);
        for seed in 0..32 {
            let point = table(mi + mj, 1000 + seed, p);
            assert!(rank1_accepts(&rank1_openings(&g, &d, &x, &point, p), p));
        }
    }

    /// A gradient wrong in ONE entry of 256 is refused at every point tried —
    /// the cheapest possible lie, and the check is not fooled by sparsity.
    #[test]
    fn a_one_entry_lie_is_refused() {
        let p = crate::babybear::P;
        let (mi, mj) = (4, 4);
        let d = table(1 << mi, 7, p);
        let x = table(1 << mj, 13, p);
        let mut g = outer_table(&d, &x, p);
        g[137] = add_mod(g[137], 1, p);
        let mut refused = 0;
        for seed in 0..64 {
            let point = table(mi + mj, 5000 + seed, p);
            if !rank1_accepts(&rank1_openings(&g, &d, &x, &point, p), p) {
                refused += 1;
            }
        }
        assert_eq!(refused, 64, "every sampled challenge must refuse the lie");
    }

    /// ⚑ The sharp one: a genuinely DIFFERENT rank-1 matrix is refused. A check
    /// that certified "the claim is rank 1" rather than "the claim is THIS
    /// gradient" would accept here — that is the vacuity this test exists to
    /// exclude, and it is `rank1_refuses_other_outer_products` in Lean.
    #[test]
    fn another_rank_one_matrix_is_refused() {
        let p = crate::babybear::P;
        let (mi, mj) = (4, 4);
        let d = table(1 << mi, 7, p);
        let x = table(1 << mj, 13, p);
        let d_other = table(1 << mi, 8, p);
        assert_ne!(d, d_other, "the other error really is different");
        let g_other = outer_table(&d_other, &x, p);
        for seed in 0..64 {
            let point = table(mi + mj, 9000 + seed, p);
            assert!(
                !rank1_accepts(&rank1_openings(&g_other, &d, &x, &point, p), p),
                "an arbitrary outer product must not pass as the gradient"
            );
        }
    }

    /// The row/column split is load-bearing: the TRANSPOSE `x⊗δ` is refused. An
    /// index-order bug survives every symmetric test, so this one is asymmetric
    /// by construction.
    #[test]
    fn the_transpose_is_refused() {
        let p = crate::babybear::P;
        let m = 4;
        let d = table(1 << m, 7, p);
        let x = table(1 << m, 13, p);
        let g_t = outer_table(&x, &d, p);
        let mut refused = 0;
        for seed in 0..64 {
            let point = table(2 * m, 3000 + seed, p);
            if !rank1_accepts(&rank1_openings(&g_t, &d, &x, &point, p), p) {
                refused += 1;
            }
        }
        assert_eq!(refused, 64, "the transpose is a different matrix");
    }

    /// The check pins the MATRIX, not the pair: rescaling `(δ, x) ↦ (c·δ, c⁻¹·x)`
    /// leaves every verdict unchanged. Lean's `outerTable_rescale`, on data — this
    /// is a SCOPE fact, not a defect.
    #[test]
    fn rescaling_the_pair_is_invisible() {
        let p = crate::babybear::P;
        let (mi, mj) = (3, 3);
        let d = table(1 << mi, 21, p);
        let x = table(1 << mj, 22, p);
        let c = 5u64;
        let cinv = crate::sumcheck::inv_mod(c, p).expect("5 is invertible mod BabyBear");
        let d_scaled: Vec<Fp> = d.iter().map(|&v| mul_mod(c, v, p)).collect();
        let x_scaled: Vec<Fp> = x.iter().map(|&v| mul_mod(cinv, v, p)).collect();
        assert_eq!(
            outer_table(&d, &x, p),
            outer_table(&d_scaled, &x_scaled, p),
            "the outer product is invariant under the rescaling"
        );
    }

    /// The batch check: a rank-`K` gradient passes, and dropping one sample from
    /// the batch is caught.
    #[test]
    fn batch_gradient_is_checked_and_a_dropped_sample_is_caught() {
        let p = crate::babybear::P;
        let (mi, mj, k) = (4, 4, 8);
        let ds: Vec<Vec<Fp>> = (0..k).map(|i| table(1 << mi, 100 + i as u64, p)).collect();
        let xs: Vec<Vec<Fp>> = (0..k).map(|i| table(1 << mj, 200 + i as u64, p)).collect();
        let g = outer_sum_table(&ds, &xs, p);
        let point = table(mi + mj, 31337, p);
        let (row, col) = split_point(&point, mi);
        let d_opens: Vec<Fp> = ds.iter().map(|d| mle_eval_folded(d, row, p)).collect();
        let x_opens: Vec<Fp> = xs.iter().map(|x| mle_eval_folded(x, col, p)).collect();
        let g_open = mle_eval_folded(&g, &point, p);
        assert!(rank_k_accepts(g_open, &d_opens, &x_opens, p));
        assert!(
            !rank_k_accepts(g_open, &d_opens[..k - 1], &x_opens[..k - 1], p),
            "a dropped sample must be caught"
        );
    }

    /// The SGD step: the honest update passes, a wrong learning rate fails, and a
    /// tampered weight fails.
    #[test]
    fn sgd_step_binds_the_gradient_the_rate_and_the_weights() {
        let p = crate::babybear::P;
        let (mi, mj) = (4, 4);
        let d = table(1 << mi, 41, p);
        let x = table(1 << mj, 43, p);
        let w = table(1 << (mi + mj), 47, p);
        let eta = 3;
        let w_prime = sgd_step_table(&w, eta, &d, &x, p);
        let point = table(mi + mj, 6060, p);
        let (row, col) = split_point(&point, mi);
        let d_open = mle_eval_folded(&d, row, p);
        let x_open = mle_eval_folded(&x, col, p);
        let w_open = mle_eval_folded(&w, &point, p);
        let w_prime_open = mle_eval_folded(&w_prime, &point, p);
        assert!(sgd_step_accepts(w_open, w_prime_open, eta, d_open, x_open, p));
        assert!(
            !sgd_step_accepts(w_open, w_prime_open, eta + 1, d_open, x_open, p),
            "a wrong learning rate must be caught"
        );
        let mut w_tampered = w_prime.clone();
        w_tampered[99] = add_mod(w_tampered[99], 1, p);
        let tampered_open = mle_eval_folded(&w_tampered, &point, p);
        assert!(
            !sgd_step_accepts(w_open, tampered_open, eta, d_open, x_open, p),
            "a tampered weight must be caught"
        );
    }

    /// The circuit baseline computes the SAME statement: the zerocheck claim is
    /// `0` exactly when the gradient is the outer product, and nonzero when it is
    /// not (at a random `z`). Without this the measured comparison would be
    /// between two different statements.
    #[test]
    fn the_zerocheck_baseline_states_the_same_thing() {
        let p = crate::babybear::P;
        let (mi, mj) = (3, 3);
        let d = table(1 << mi, 61, p);
        let x = table(1 << mj, 67, p);
        let g = outer_table(&d, &x, p);
        let z = table(mi + mj, 8080, p);
        assert_eq!(zerocheck_tables(&g, &d, &x, &z, p).claim(p), 0);
        let mut g_bad = g.clone();
        g_bad[5] = add_mod(g_bad[5], 1, p);
        assert_ne!(zerocheck_tables(&g_bad, &d, &x, &z, p).claim(p), 0);
    }

    /// `eq_table` is the Lean `eqMle z (cubePt ·)`: it sums to one and is the
    /// corner indicator at a corner.
    #[test]
    fn eq_table_is_the_equality_polynomial() {
        let p = 97;
        let z = table(4, 5150, p);
        let e = eq_table(&z, p);
        assert_eq!(e.len(), 16);
        // Pinned to the crate's `chi_eval`, which the sumcheck conformance vector
        // binds to Lean's `chiEval`: `eqMle z (cubePt b) = chiEval b z`.
        for (b, &value) in e.iter().enumerate() {
            assert_eq!(value, crate::sumcheck::chi_eval(b, &z, p), "eq table at {b}");
        }
        let total = e.iter().fold(0, |a, &v| add_mod(a, v, p));
        assert_eq!(total, 1 % p, "the eq table sums to one");
        let corner = vec![0, 1, 1, 0];
        let e_corner = eq_table(&corner, p);
        assert_eq!(e_corner[0b0110], 1 % p);
        assert_eq!(e_corner.iter().filter(|&&v| v != 0).count(), 1);
    }
}
