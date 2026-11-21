//! Gruen (`ePrint 2024/108` §3.2–3.3 & App. A.3; `ePrint 2025/1117` §5.1) `eq`-factored
//! Mode-2 `EinSumcheck` and delayed block-bind (`b -> j -> k`) 7-bucket 0-mul E2M1 MXFP4 Horner
//! compute kernels.
//!
//! Substrate, said out loud: UNVERIFIED NATIVE COMPUTE bound to Lean-authored conformance vectors
//! (`prover/testdata/gruen_einsumcheck_conformance.json`, emitted by `#eval` in
//! `Compiler/GruenEinSumcheckConformance.lean` over `Assurance/ZkmlGruenSumcheck.lean` and
//! `Assurance/ZkmlEinSumcheck.lean`). Rust never authors protocol semantics; agreement on the
//! Lean-decided vectors and literal-vs-folded cross-checks is the whole claim.

use crate::babybear::{badd, binv, bmul, bsub, P};
use crate::sumcheck::{add_mod, chi_eval, fold_table, inv_mod, mle_eval, mul_mod, sub_mod, Fp};

/// Evaluate `eqLinPoly(r)(x) = (1 - r)(1 - x) + r·x mod p`, mirroring
/// `Assurance/ZkmlGruenSumcheck.eqLinPoly`.
#[inline]
pub fn eq_lin_eval(r: Fp, x: Fp, p: u64) -> Fp {
    let one = 1 % p;
    add_mod(
        mul_mod(sub_mod(one, r % p, p), sub_mod(one, x % p, p), p),
        mul_mod(r % p, x % p, p),
        p,
    )
}

/// BabyBear-specialized `eqLinPoly(r)(x)`.
#[inline]
pub fn eq_lin_eval_bb(r: u64, x: u64) -> u64 {
    badd(bmul(bsub(1, r), bsub(1, x)), bmul(r, x))
}

/// Evaluate `eqMle(z, x) = ∏_j eqLinPoly(z_j)(x_j) mod p`.
pub fn eq_mle_eval(z: &[Fp], x: &[Fp], p: u64) -> Fp {
    assert_eq!(z.len(), x.len(), "eqMle point lengths must match");
    z.iter()
        .zip(x.iter())
        .fold(1 % p, |acc, (&zj, &xj)| mul_mod(acc, eq_lin_eval(zj, xj, p), p))
}

/// Evaluate a degree-`≤ 2` polynomial reconstructed from `{q(0), q(1), q(∞)}` (`q.coeff 2`),
/// mirroring `Assurance/ZkmlGruenSumcheck.quadFromZeroOneInf`:
/// `q(x) = q0 + (q1 - q0 - q_inf)·x + q_inf·x²`.
#[inline]
pub fn eval_quad_zero_one_inf(q0: Fp, q1: Fp, q_inf: Fp, x: Fp, p: u64) -> Fp {
    let c1 = sub_mod(sub_mod(q1 % p, q0 % p, p), q_inf % p, p);
    let x_mod = x % p;
    let x2 = mul_mod(x_mod, x_mod, p);
    add_mod(
        q0 % p,
        add_mod(mul_mod(c1, x_mod, p), mul_mod(q_inf % p, x2, p), p),
        p,
    )
}

/// Evaluate a degree-`≤ 3` polynomial given `{p(0), p(1), p(2), p(∞)}` (`p.coeff 3`) at `x`
/// (`p > 2` required so `2` is invertible).
pub fn eval_cubic_zero_one_two_inf(
    p0: Fp,
    p1: Fp,
    p2: Fp,
    p_inf: Fp,
    x: Fp,
    p: u64,
) -> Option<Fp> {
    let inv2 = inv_mod(2 % p, p)?;
    let six_c3 = mul_mod(6 % p, p_inf % p, p);
    let two_p1 = add_mod(p1 % p, p1 % p, p);
    let two_c2 = sub_mod(add_mod(sub_mod(p2 % p, two_p1, p), p0 % p, p), six_c3, p);
    let c2 = mul_mod(two_c2, inv2, p);
    let c1 = sub_mod(sub_mod(sub_mod(p1 % p, p0 % p, p), c2, p), p_inf % p, p);
    let xm = x % p;
    let x2 = mul_mod(xm, xm, p);
    let x3 = mul_mod(x2, xm, p);
    let lo = add_mod(p0 % p, mul_mod(c1, xm, p), p);
    let hi = add_mod(mul_mod(c2, x2, p), mul_mod(p_inf % p, x3, p), p);
    Some(add_mod(lo, hi, p))
}

/// Build MSB-to-LSB suffix equality tables for LSB-first Gruen `F_{>=2}` elimination (`2025/1117` §5.1).
///
/// For `ell = z_s.len()`, returns `suf` of length `ell` where `suf[m]` (`m = 0..ell-1`) has length
/// `2^m` representing `eq(z_s[ell - m .. ell], h_rest)` with `z_s[ell - m]` at LSB stride 1.
/// Round `u` (`0..ell-1`) reads `suf[ell - 1 - u]`. Note `z_s[0]` is never multiplied into any
/// table; total multiplications are `max(0, 2^{ell - 1} - 2)`.
pub fn build_eq_suffix_tables(z_s: &[Fp], p: u64) -> Vec<Vec<Fp>> {
    let ell = z_s.len();
    if ell == 0 {
        return Vec::new();
    }
    let one = 1 % p;
    let mut suf = Vec::with_capacity(ell);
    suf.push(vec![one]);
    if ell >= 2 {
        let z_last = z_s[ell - 1] % p;
        suf.push(vec![sub_mod(one, z_last, p), z_last]);
        for m in 2..ell {
            let prev = &suf[m - 1];
            let z_cur = z_s[ell - m] % p;
            let mut next = Vec::with_capacity(1usize << m);
            for &v in prev.iter() {
                let hi = mul_mod(v, z_cur, p);
                let lo = sub_mod(v, hi, p);
                next.push(lo);
                next.push(hi);
            }
            suf.push(next);
        }
    }
    suf
}

/// BabyBear-specialized suffix `eq` table builder.
pub fn build_eq_suffix_tables_bb(z_s: &[u64]) -> Vec<Vec<u64>> {
    let ell = z_s.len();
    if ell == 0 {
        return Vec::new();
    }
    let mut suf = Vec::with_capacity(ell);
    suf.push(vec![1]);
    if ell >= 2 {
        let z_last = z_s[ell - 1];
        suf.push(vec![bsub(1, z_last), z_last]);
        for m in 2..ell {
            let prev = &suf[m - 1];
            let z_cur = z_s[ell - m];
            let mut next = Vec::with_capacity(1usize << m);
            for &v in prev.iter() {
                let hi = bmul(v, z_cur);
                let lo = bsub(v, hi);
                next.push(lo);
                next.push(hi);
            }
            suf.push(next);
        }
    }
    suf
}

/// Build full LSB-first `eq(r, ·)` hypercube table of length `2^k` in `max(0, 2^k - 2)` muls
/// (`index` bit `i` corresponds to `r[i]`).
pub fn build_eq_table_lsb_bb(r: &[u64]) -> Vec<u64> {
    let k = r.len();
    if k == 0 {
        return vec![1];
    }
    let mut tbl = Vec::with_capacity(1usize << k);
    tbl.push(bsub(1, r[0]));
    tbl.push(r[0]);
    for &ri in &r[1..] {
        let cur_len = tbl.len();
        for idx in 0..cur_len {
            let base = tbl[idx];
            let hi = bmul(base, ri);
            let lo = bsub(base, hi);
            tbl[idx] = lo;
            tbl.push(hi);
        }
    }
    tbl
}

/// Fold adjacent LSB pairs of a BabyBear value table in-place or into a half-length `Vec<u64>`.
#[inline]
pub fn fold_table_bb(f: &[u64], r: u64) -> Vec<u64> {
    debug_assert!(f.len() >= 2 && f.len().is_power_of_two());
    f.chunks_exact(2)
        .map(|pair| badd(pair[0], bmul(r, bsub(pair[1], pair[0]))))
        .collect()
}

// ===========================================================================
// §1. Two-Operand `EinSumcheck` Instance & Literal Mirror
// ===========================================================================

/// Two-operand Einsum contraction `Z[aL][aR][h] = Σ_p A[aL][h][p] · B[aR][h][p]` mirroring
/// `Assurance/ZkmlEinSumcheck.lean` (`aL ∈ {0,1}^{mu_l}`, `aR ∈ {0,1}^{mu_r}`, shared free
/// `h ∈ {0,1}^{mu_s}`, shared summation `p ∈ {0,1}^{kappa}`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EinSumcheckInstance {
    pub mu_l: usize,
    pub mu_r: usize,
    pub mu_s: usize,
    pub kappa: usize,
    /// Shape `[2^mu_l][2^mu_s][2^kappa]`, LSB-first corner indexing on each axis.
    pub a: Vec<Vec<Vec<Fp>>>,
    /// Shape `[2^mu_r][2^mu_s][2^kappa]`, LSB-first corner indexing on each axis.
    pub b: Vec<Vec<Vec<Fp>>>,
}

impl EinSumcheckInstance {
    pub fn check_shape(&self) {
        assert_eq!(self.a.len(), 1usize << self.mu_l);
        for ah in &self.a {
            assert_eq!(ah.len(), 1usize << self.mu_s);
            for ap in ah {
                assert_eq!(ap.len(), 1usize << self.kappa);
            }
        }
        assert_eq!(self.b.len(), 1usize << self.mu_r);
        for bh in &self.b {
            assert_eq!(bh.len(), 1usize << self.mu_s);
            for bp in bh {
                assert_eq!(bp.len(), 1usize << self.kappa);
            }
        }
    }

    /// True output tensor `Z[aL][aR][h] = Σ_p A[aL][h][p] · B[aR][h][p]` (`einsumTable`).
    pub fn einsum_output(&self, p: u64) -> Vec<Vec<Vec<Fp>>> {
        self.check_shape();
        let nl = 1usize << self.mu_l;
        let nr = 1usize << self.mu_r;
        let ns = 1usize << self.mu_s;
        let nk = 1usize << self.kappa;
        (0..nl)
            .map(|al| {
                (0..nr)
                    .map(|ar| {
                        (0..ns)
                            .map(|h| {
                                (0..nk).fold(0, |acc, q| {
                                    add_mod(
                                        acc,
                                        mul_mod(self.a[al][h][q] % p, self.b[ar][h][q] % p, p),
                                        p,
                                    )
                                })
                            })
                            .collect()
                    })
                    .collect()
            })
            .collect()
    }

    /// Flattened `(mu_s + kappa)`-variable `einsumLeftTable` (`bits 0..mu_s-1` = `h`,
    /// `bits mu_s..mu_s+kappa-1` = `p`).
    pub fn left_table(&self, x_l: &[Fp], p: u64) -> Vec<Fp> {
        self.check_shape();
        assert_eq!(x_l.len(), self.mu_l);
        let nl = 1usize << self.mu_l;
        let ns = 1usize << self.mu_s;
        let nk = 1usize << self.kappa;
        let chi_l: Vec<Fp> = (0..nl).map(|al| chi_eval(al, x_l, p)).collect();
        let mut out = vec![0u64; ns * nk];
        for q in 0..nk {
            for h in 0..ns {
                let mut acc = 0;
                for al in 0..nl {
                    acc = add_mod(acc, mul_mod(self.a[al][h][q] % p, chi_l[al], p), p);
                }
                out[h + (q << self.mu_s)] = acc;
            }
        }
        out
    }

    /// Flattened `(mu_s + kappa)`-variable `einsumRightTable`.
    pub fn right_table(&self, x_r: &[Fp], p: u64) -> Vec<Fp> {
        self.check_shape();
        assert_eq!(x_r.len(), self.mu_r);
        let nr = 1usize << self.mu_r;
        let ns = 1usize << self.mu_s;
        let nk = 1usize << self.kappa;
        let chi_r: Vec<Fp> = (0..nr).map(|ar| chi_eval(ar, x_r, p)).collect();
        let mut out = vec![0u64; ns * nk];
        for q in 0..nk {
            for h in 0..ns {
                let mut acc = 0;
                for ar in 0..nr {
                    acc = add_mod(acc, mul_mod(self.b[ar][h][q] % p, chi_r[ar], p), p);
                }
                out[h + (q << self.mu_s)] = acc;
            }
        }
        out
    }
}

/// Mirror of `Assurance/ZkmlEinSumcheck.mle₃` on a `[2^mu_l][2^mu_r][2^mu_s]` tensor.
pub fn mle3_eval(z_tab: &[Vec<Vec<Fp>>], x_l: &[Fp], x_r: &[Fp], z_s: &[Fp], p: u64) -> Fp {
    assert_eq!(z_tab.len(), 1usize << x_l.len());
    let mut acc = 0;
    for (al, z_al) in z_tab.iter().enumerate() {
        assert_eq!(z_al.len(), 1usize << x_r.len());
        let cl = chi_eval(al, x_l, p);
        for (ar, z_alar) in z_al.iter().enumerate() {
            assert_eq!(z_alar.len(), 1usize << z_s.len());
            let clr = mul_mod(cl, chi_eval(ar, x_r, p), p);
            for (h, &val) in z_alar.iter().enumerate() {
                let weight = mul_mod(clr, chi_eval(h, z_s, p), p);
                acc = add_mod(acc, mul_mod(val % p, weight, p), p);
            }
        }
    }
    acc
}

/// **Literal mirror (`O(4^m)`)** of the Mode-2 Gruen quotient polynomial `q_i(t)` at round `i`
/// (`0 ≤ i < mu_s + kappa`):
/// `q_i(t) = Σ_{b_suf ∈ {0,1}^{m-1-i}} (∏_{j=i+1}^{mu_s-1} ℓ_{z_j}(b_j)) · L̂(c_{<i}, t, b_suf) · R̂(c_{<i}, t, b_suf)`.
pub fn gruen_quotient_literal(
    left_tab: &[Fp],
    right_tab: &[Fp],
    mu_s: usize,
    kappa: usize,
    z_s: &[Fp],
    challenges: &[Fp],
    round_i: usize,
    t: Fp,
    p: u64,
) -> Fp {
    let m = mu_s + kappa;
    assert_eq!(left_tab.len(), 1usize << m);
    assert_eq!(right_tab.len(), 1usize << m);
    assert_eq!(z_s.len(), mu_s);
    assert_eq!(challenges.len(), m);
    assert!(round_i < m);

    let rem = m - 1 - round_i;
    let mut pt = Vec::with_capacity(m);
    let mut acc = 0;
    for mask in 0..(1usize << rem) {
        pt.clear();
        pt.extend_from_slice(&challenges[..round_i]);
        pt.push(t % p);
        for bit in 0..rem {
            pt.push(((mask >> bit) & 1) as u64);
        }
        let mut suf_eq = 1 % p;
        for j in (round_i + 1)..mu_s {
            suf_eq = mul_mod(suf_eq, eq_lin_eval(z_s[j], pt[j], p), p);
        }
        let l_val = mle_eval(left_tab, &pt, p);
        let r_val = mle_eval(right_tab, &pt, p);
        acc = add_mod(acc, mul_mod(suf_eq, mul_mod(l_val, r_val, p), p), p);
    }
    acc
}

// ===========================================================================
// §2. Fast Folded `O(2^m)` Gruen `{0, ∞}` Mode-2 Prover & Verifier
// ===========================================================================

/// Wire message for one round of Mode-2 `Gruen` `EinSumcheck` (`ePrint 2024/108` §3.3 & fn. 23).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GruenRoundMsg {
    /// Standard 2-element `{q(0), q(∞)}` message (`z_u != 0` in `F_{>=2}`, and all `S` rounds).
    TwoPoint { q0: Fp, q_inf: Fp },
    /// Deterministic `z_u == 0` fallback (`2024/108` fn. 23): because `ℓ_0(1) = 0` annihilates
    /// `q(1)` in `ℓ_0(0)q(0) + ℓ_0(1)q(1) = σ`, the prover evaluates `q(1)` directly (zero
    /// inversions) and includes it on the wire.
    ZeroEqFallback { q0: Fp, q_inf: Fp, q1: Fp },
}

impl GruenRoundMsg {
    pub fn wire_slice(&self) -> Vec<Fp> {
        match *self {
            Self::TwoPoint { q0, q_inf } => vec![q0, q_inf],
            Self::ZeroEqFallback { q0, q_inf, q1 } => vec![q0, q_inf, q1],
        }
    }
}

/// Complete Mode-2 Gruen `EinSumcheck` transcript.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GruenEinSumcheckProof {
    pub claim: Fp,
    pub mu_s: usize,
    pub kappa: usize,
    pub z_s: Vec<Fp>,
    pub rounds: Vec<GruenRoundMsg>,
    pub challenges: Vec<Fp>,
    /// Intermediate stripped claim `σ_{mu_s} = q_{mu_s - 1}(c_{mu_s - 1})` entering Phase 2 (`S`),
    /// recorded for audit/conformance inspection (verifier recomputes it from `claim` + `rounds`).
    pub s_phase_entry_claim: Fp,
    /// Terminal folded operand evaluations `(Â(xL, c_S, c_κ), B̂(xR, c_S, c_κ))`.
    pub terminal_openings: (Fp, Fp),
}

/// Single-round `{q(0), q(∞)}` evaluator on `F_{>=2}` with runtime modulus `p` (2 inner-product
/// points per pair vs 4 in `sumcheck::cubic_round_evals`).
///
/// Layout: `left` and `right` have length `2^{rem_s + 1 + kappa}` where the low `rem_s + 1` bits
/// index the remaining `F_{>=2}` coordinates (`bit 0` = current round variable) and the high
/// `kappa` bits index `S`. `suf_eq` has length `2^{rem_s}`.
pub fn gruen_f2_round_evals_p(
    left: &[Fp],
    right: &[Fp],
    suf_eq: &[Fp],
    kappa: usize,
    p: u64,
) -> [Fp; 2] {
    let rem_h_pairs = suf_eq.len();
    let nk = 1usize << kappa;
    let stride_p = rem_h_pairs * 2;
    debug_assert_eq!(left.len(), stride_p * nk);
    debug_assert_eq!(right.len(), stride_p * nk);

    let mut q0_by_h = vec![0u64; rem_h_pairs];
    let mut qinf_by_h = vec![0u64; rem_h_pairs];

    for q in 0..nk {
        let base = q * stride_p;
        for h_rem in 0..rem_h_pairs {
            let idx0 = base + 2 * h_rem;
            let a0 = left[idx0] % p;
            let a1 = left[idx0 + 1] % p;
            let b0 = right[idx0] % p;
            let b1 = right[idx0 + 1] % p;
            let da = sub_mod(a1, a0, p);
            let db = sub_mod(b1, b0, p);
            q0_by_h[h_rem] = add_mod(q0_by_h[h_rem], mul_mod(a0, b0, p), p);
            qinf_by_h[h_rem] = add_mod(qinf_by_h[h_rem], mul_mod(da, db, p), p);
        }
    }

    let mut q0 = 0;
    let mut q_inf = 0;
    for h_rem in 0..rem_h_pairs {
        let w = suf_eq[h_rem] % p;
        q0 = add_mod(q0, mul_mod(w, q0_by_h[h_rem], p), p);
        q_inf = add_mod(q_inf, mul_mod(w, qinf_by_h[h_rem], p), p);
    }
    [q0, q_inf]
}

/// BabyBear-specialized single-round `{q(0), q(∞)}` evaluator on `F_{>=2}`.
pub fn gruen_f2_round_evals_bb(
    left: &[u64],
    right: &[u64],
    suf_eq: &[u64],
    kappa: usize,
) -> [u64; 2] {
    let rem_h_pairs = suf_eq.len();
    let nk = 1usize << kappa;
    let stride_p = rem_h_pairs * 2;
    debug_assert_eq!(left.len(), stride_p * nk);
    debug_assert_eq!(right.len(), stride_p * nk);

    if rem_h_pairs == 1 {
        let mut acc0 = 0u128;
        let mut acc_inf = 0u128;
        for q in 0..nk {
            let idx0 = 2 * q;
            let a0 = left[idx0];
            let a1 = left[idx0 + 1];
            let b0 = right[idx0];
            let b1 = right[idx0 + 1];
            let da = bsub(a1, a0);
            let db = bsub(b1, b0);
            acc0 += (a0 as u128) * (b0 as u128);
            acc_inf += (da as u128) * (db as u128);
            if (q & 15) == 15 {
                acc0 %= P as u128;
                acc_inf %= P as u128;
            }
        }
        let w = suf_eq[0];
        let q0 = bmul((acc0 % P as u128) as u64, w);
        let q_inf = bmul((acc_inf % P as u128) as u64, w);
        return [q0, q_inf];
    }

    let mut q0_by_h = vec![0u64; rem_h_pairs];
    let mut qinf_by_h = vec![0u64; rem_h_pairs];

    for q in 0..nk {
        let base = q * stride_p;
        for h_rem in 0..rem_h_pairs {
            let idx0 = base + 2 * h_rem;
            let a0 = left[idx0];
            let a1 = left[idx0 + 1];
            let b0 = right[idx0];
            let b1 = right[idx0 + 1];
            let da = bsub(a1, a0);
            let db = bsub(b1, b0);
            q0_by_h[h_rem] = badd(q0_by_h[h_rem], bmul(a0, b0));
            qinf_by_h[h_rem] = badd(qinf_by_h[h_rem], bmul(da, db));
        }
    }

    let mut acc0 = 0u128;
    let mut acc_inf = 0u128;
    for h_rem in 0..rem_h_pairs {
        let w = suf_eq[h_rem] as u128;
        acc0 += w * (q0_by_h[h_rem] as u128);
        acc_inf += w * (qinf_by_h[h_rem] as u128);
        if (h_rem & 15) == 15 {
            acc0 %= P as u128;
            acc_inf %= P as u128;
        }
    }
    [(acc0 % P as u128) as u64, (acc_inf % P as u128) as u64]
}

/// Evaluate `q(1)` directly on `F_{>=2}` when `z_s[u] == 0` (`2024/108` fn. 23 fallback; 0 inversions).
fn gruen_f2_direct_q1_p(
    left: &[Fp],
    right: &[Fp],
    suf_eq: &[Fp],
    kappa: usize,
    p: u64,
) -> Fp {
    let rem_h_pairs = suf_eq.len();
    let nk = 1usize << kappa;
    let stride_p = rem_h_pairs * 2;
    let mut q1_by_h = vec![0u64; rem_h_pairs];
    for q in 0..nk {
        let base = q * stride_p;
        for h_rem in 0..rem_h_pairs {
            let idx1 = base + 2 * h_rem + 1;
            q1_by_h[h_rem] = add_mod(
                q1_by_h[h_rem],
                mul_mod(left[idx1] % p, right[idx1] % p, p),
                p,
            );
        }
    }
    let mut q1 = 0;
    for h_rem in 0..rem_h_pairs {
        q1 = add_mod(q1, mul_mod(suf_eq[h_rem] % p, q1_by_h[h_rem], p), p);
    }
    q1
}

/// Honest folded `O(2^m)` Mode-2 Gruen `EinSumcheck` prover over prime `p` (**zero prover inversions**).
pub fn prove_gruen_einsum_mode2(
    left_tab: &[Fp],
    right_tab: &[Fp],
    mu_s: usize,
    kappa: usize,
    z_s: &[Fp],
    challenges: &[Fp],
    p: u64,
) -> GruenEinSumcheckProof {
    let m = mu_s + kappa;
    assert_eq!(left_tab.len(), 1usize << m);
    assert_eq!(right_tab.len(), 1usize << m);
    assert_eq!(z_s.len(), mu_s);
    assert_eq!(challenges.len(), m);
    assert!(z_s.iter().all(|&z| z < p) && challenges.iter().all(|&c| c < p));

    // Compute initial claim H = Σ_{h, p} eqMle(z_s, h) · left_tab[h, p] · right_tab[h, p]
    let ns = 1usize << mu_s;
    let nk = 1usize << kappa;
    let eq_h: Vec<Fp> = (0..ns).map(|h| chi_eval(h, z_s, p)).collect();
    let mut claim = 0;
    for q in 0..nk {
        let base = q << mu_s;
        let mut inner = 0;
        for h in 0..ns {
            inner = add_mod(
                inner,
                mul_mod(
                    eq_h[h],
                    mul_mod(left_tab[base + h] % p, right_tab[base + h] % p, p),
                    p,
                ),
                p,
            );
        }
        claim = add_mod(claim, inner, p);
    }

    let suf_tables = build_eq_suffix_tables(z_s, p);
    let mut l_cur = left_tab.to_vec();
    let mut r_cur = right_tab.to_vec();
    let mut rounds = Vec::with_capacity(m);

    // Phase 1: `mu_s` Gruen `F_{>=2}` rounds (zero prover inversions!)
    for u in 0..mu_s {
        let suf = &suf_tables[mu_s - 1 - u];
        let [q0, q_inf] = gruen_f2_round_evals_p(&l_cur, &r_cur, suf, kappa, p);
        if z_s[u] % p == 0 {
            let q1 = gruen_f2_direct_q1_p(&l_cur, &r_cur, suf, kappa, p);
            rounds.push(GruenRoundMsg::ZeroEqFallback { q0, q_inf, q1 });
        } else {
            rounds.push(GruenRoundMsg::TwoPoint { q0, q_inf });
        }
        l_cur = fold_table(&l_cur, challenges[u], p);
        r_cur = fold_table(&r_cur, challenges[u], p);
    }

    // At `u = mu_s`, `l_cur` and `r_cur` have length `2^kappa` and their inner product IS
    // the stripped Phase-2 entry claim `σ_{mu_s}` (with `eqMle(z_s, c_s)` already stripped!).
    let s_phase_entry_claim = l_cur
        .iter()
        .zip(r_cur.iter())
        .fold(0, |acc, (&a, &b)| add_mod(acc, mul_mod(a % p, b % p, p), p));

    // Phase 2: `kappa` quadratic `S` rounds (`{0, ∞}`, zero prover inversions!)
    for v in 0..kappa {
        let half = l_cur.len() / 2;
        let mut q0 = 0;
        let mut q_inf = 0;
        for idx in 0..half {
            let a0 = l_cur[2 * idx] % p;
            let a1 = l_cur[2 * idx + 1] % p;
            let b0 = r_cur[2 * idx] % p;
            let b1 = r_cur[2 * idx + 1] % p;
            let da = sub_mod(a1, a0, p);
            let db = sub_mod(b1, b0, p);
            q0 = add_mod(q0, mul_mod(a0, b0, p), p);
            q_inf = add_mod(q_inf, mul_mod(da, db, p), p);
        }
        rounds.push(GruenRoundMsg::TwoPoint { q0, q_inf });
        let ch = challenges[mu_s + v];
        l_cur = fold_table(&l_cur, ch, p);
        r_cur = fold_table(&r_cur, ch, p);
    }

    GruenEinSumcheckProof {
        claim,
        mu_s,
        kappa,
        z_s: z_s.to_vec(),
        rounds,
        challenges: challenges.to_vec(),
        s_phase_entry_claim,
        terminal_openings: (l_cur[0] % p, r_cur[0] % p),
    }
}

/// BabyBear-specialized fast `O(2^m)` Mode-2 Gruen `EinSumcheck` prover (zero prover inversions).
pub fn prove_gruen_einsum_mode2_bb(
    left_tab: &[u64],
    right_tab: &[u64],
    mu_s: usize,
    kappa: usize,
    z_s: &[u64],
    challenges: &[u64],
) -> GruenEinSumcheckProof {
    let m = mu_s + kappa;
    assert_eq!(left_tab.len(), 1usize << m);
    assert_eq!(right_tab.len(), 1usize << m);
    assert_eq!(z_s.len(), mu_s);
    assert_eq!(challenges.len(), m);

    let ns = 1usize << mu_s;
    let nk = 1usize << kappa;
    let eq_h = build_eq_table_lsb_bb(z_s);
    let mut claim = 0u64;
    for q in 0..nk {
        let base = q << mu_s;
        let mut acc = 0u128;
        for h in 0..ns {
            let prod = bmul(left_tab[base + h], right_tab[base + h]);
            acc += (eq_h[h] as u128) * (prod as u128);
            if (h & 15) == 15 {
                acc %= P as u128;
            }
        }
        claim = badd(claim, (acc % P as u128) as u64);
    }

    let suf_tables = build_eq_suffix_tables_bb(z_s);
    let mut l_cur = left_tab.to_vec();
    let mut r_cur = right_tab.to_vec();
    let mut rounds = Vec::with_capacity(m);

    for u in 0..mu_s {
        let suf = &suf_tables[mu_s - 1 - u];
        let [q0, q_inf] = gruen_f2_round_evals_bb(&l_cur, &r_cur, suf, kappa);
        if z_s[u] == 0 {
            let q1 = gruen_f2_direct_q1_p(&l_cur, &r_cur, suf, kappa, P);
            rounds.push(GruenRoundMsg::ZeroEqFallback { q0, q_inf, q1 });
        } else {
            rounds.push(GruenRoundMsg::TwoPoint { q0, q_inf });
        }
        l_cur = fold_table_bb(&l_cur, challenges[u]);
        r_cur = fold_table_bb(&r_cur, challenges[u]);
    }

    let mut s_acc = 0u128;
    for (idx, (&a, &b)) in l_cur.iter().zip(r_cur.iter()).enumerate() {
        s_acc += (a as u128) * (b as u128);
        if (idx & 15) == 15 {
            s_acc %= P as u128;
        }
    }
    let s_phase_entry_claim = (s_acc % P as u128) as u64;

    for v in 0..kappa {
        let half = l_cur.len() / 2;
        let mut acc0 = 0u128;
        let mut acc_inf = 0u128;
        for idx in 0..half {
            let a0 = l_cur[2 * idx];
            let a1 = l_cur[2 * idx + 1];
            let b0 = r_cur[2 * idx];
            let b1 = r_cur[2 * idx + 1];
            let da = bsub(a1, a0);
            let db = bsub(b1, b0);
            acc0 += (a0 as u128) * (b0 as u128);
            acc_inf += (da as u128) * (db as u128);
            if (idx & 15) == 15 {
                acc0 %= P as u128;
                acc_inf %= P as u128;
            }
        }
        rounds.push(GruenRoundMsg::TwoPoint {
            q0: (acc0 % P as u128) as u64,
            q_inf: (acc_inf % P as u128) as u64,
        });
        let ch = challenges[mu_s + v];
        l_cur = fold_table_bb(&l_cur, ch);
        r_cur = fold_table_bb(&r_cur, ch);
    }

    GruenEinSumcheckProof {
        claim,
        mu_s,
        kappa,
        z_s: z_s.to_vec(),
        rounds,
        challenges: challenges.to_vec(),
        s_phase_entry_claim,
        terminal_openings: (l_cur[0], r_cur[0]),
    }
}

/// Fail-closed Mode-2 Gruen `EinSumcheck` verifier (`ePrint 2024/108` §3.3 & App. A.3), mirroring
/// `Assurance/ZkmlGruenSumcheck.lean`:
/// * In `F_{>=2}` rounds (`u < mu_s`):
///   - If `z_s[u] != 0`, requires `TwoPoint { q0, q_inf }`, recovers unique
///     `q1 = z_s[u]^{-1} · (σ - (1 - z_s[u])·q0)` (`gruen_q1_unique_of_r_ne_zero`), and updates
///     stripped claim `σ <- q_u(c_u)` (`gruen_direct_claim_roots_le` `2/|F|` soundness).
///   - If `z_s[u] == 0`, requires `ZeroEqFallback { q0, q_inf, q1 }`, checks `q0 == σ`
///     (`ℓ_0(0)·q0 + 0·q1 == σ`), and updates `σ <- q_u(c_u)`.
/// * At `u = mu_s` (`F_{>=2} -> S` splice): `σ` ALREADY has `eqMle(z_s, c_s)` stripped, so it
///   chains directly into Phase 2 with NO second division (`gruen_phase_splice_double_strip_tooth`).
/// * In `S` rounds (`i >= mu_s`): requires `TwoPoint { q0, q_inf }`, recovers `q1 = σ - q0`,
///   and updates `σ <- q_i(c_i)`.
/// * Terminal check: `σ == Â(xL, c_S, c_κ) · B̂(xR, c_S, c_κ)` from `open_ab`.
pub fn verify_gruen_einsum_mode2(
    expected_claim: Fp,
    proof: &GruenEinSumcheckProof,
    open_ab: impl Fn(&[Fp]) -> (Fp, Fp),
    p: u64,
) -> bool {
    let m = proof.mu_s + proof.kappa;
    if proof.claim != expected_claim || proof.claim >= p {
        return false;
    }
    if proof.z_s.len() != proof.mu_s
        || proof.rounds.len() != m
        || proof.challenges.len() != m
        || proof.z_s.iter().any(|&z| z >= p)
        || proof.challenges.iter().any(|&c| c >= p)
    {
        return false;
    }

    let one = 1 % p;
    let mut sigma = proof.claim;

    for i in 0..m {
        let ch = proof.challenges[i];
        if i < proof.mu_s {
            let r = proof.z_s[i];
            if r == 0 {
                match proof.rounds[i] {
                    GruenRoundMsg::ZeroEqFallback { q0, q_inf, q1 } => {
                        if q0 >= p || q_inf >= p || q1 >= p {
                            return false;
                        }
                        if q0 != sigma {
                            return false;
                        }
                        sigma = eval_quad_zero_one_inf(q0, q1, q_inf, ch, p);
                    }
                    GruenRoundMsg::TwoPoint { .. } => return false,
                }
            } else {
                match proof.rounds[i] {
                    GruenRoundMsg::TwoPoint { q0, q_inf } => {
                        if q0 >= p || q_inf >= p {
                            return false;
                        }
                        let r_inv = match inv_mod(r, p) {
                            Some(v) => v,
                            None => return false,
                        };
                        let l0_q0 = mul_mod(sub_mod(one, r, p), q0, p);
                        let q1 = mul_mod(r_inv, sub_mod(sigma, l0_q0, p), p);
                        sigma = eval_quad_zero_one_inf(q0, q1, q_inf, ch, p);
                    }
                    GruenRoundMsg::ZeroEqFallback { .. } => return false,
                }
            }
        } else {
            match proof.rounds[i] {
                GruenRoundMsg::TwoPoint { q0, q_inf } => {
                    if q0 >= p || q_inf >= p {
                        return false;
                    }
                    let q1 = sub_mod(sigma, q0, p);
                    sigma = eval_quad_zero_one_inf(q0, q1, q_inf, ch, p);
                }
                GruenRoundMsg::ZeroEqFallback { .. } => return false,
            }
        }
    }

    let (open_a, open_b) = open_ab(&proof.challenges);
    if open_a >= p || open_b >= p {
        return false;
    }
    sigma == mul_mod(open_a, open_b, p)
}

// ===========================================================================
// §3. Delayed Block-Bind (`b -> j -> k`) + 7-Bucket 0-Mul E2M1 MXFP4 Horner
// ===========================================================================

/// Doubled E2M1 magnitude lookup table indexed by `nibble & 7`:
/// `{0, 0.5, 1.0, 1.5, 2.0, 3.0, 4.0, 6.0} * 2 = {0, 1, 2, 3, 4, 6, 8, 12}`.
pub const E2M1_X2_MAGS: [u64; 8] = [0, 1, 2, 3, 4, 6, 8, 12];

/// Decode a 4-bit OCP E2M1 nibble (`0..16`, bit 3 = sign, bits 0..2 = magnitude index)
/// to its canonical BabyBear element (`±{0, 1, 2, 3, 4, 6, 8, 12} mod P`, with `-0 == 0`).
#[inline]
pub fn decode_e2m1_x2_bb(nibble: u8) -> u64 {
    let mag = E2M1_X2_MAGS[(nibble & 7) as usize];
    if mag == 0 || (nibble & 8) == 0 {
        mag
    } else {
        P - mag
    }
}

/// Encode a signed doubled E2M1 integer `∈ {-12,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,12}` to a 4-bit nibble.
pub fn encode_e2m1_x2(val: i8) -> u8 {
    let sign = if val < 0 { 8u8 } else { 0u8 };
    let mag_idx = match val.unsigned_abs() {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 3,
        4 => 4,
        6 => 5,
        8 => 6,
        12 => 7,
        other => panic!("invalid doubled E2M1 value {other}"),
    };
    sign | mag_idx
}

/// Return `(buckets_1_to_7, planes_c8_c4_c2_c1, dot_product)` for a slice of 4-bit E2M1 nibbles
/// against a BabyBear slice using **7 signed buckets + 4 bit-planes + 3 Horner doublings** and
/// **ZERO field multiplications**.
pub fn e2m1_horner_buckets_bb(q_nibbles: &[u8], vec: &[u64]) -> ([u64; 7], [u64; 4], u64) {
    assert_eq!(q_nibbles.len(), vec.len());
    let mut b = [0u64; 8];
    for (&nib, &v) in q_nibbles.iter().zip(vec.iter()) {
        let mag = (nib & 7) as usize;
        if mag != 0 {
            if (nib & 8) == 0 {
                b[mag] = badd(b[mag], v);
            } else {
                b[mag] = bsub(b[mag], v);
            }
        }
    }
    // b[1]=B_1, b[2]=B_2, b[3]=B_3, b[4]=B_4, b[5]=B_6, b[6]=B_8, b[7]=B_12
    let c8 = badd(b[6], b[7]);
    let c4 = badd(badd(b[4], b[5]), b[7]);
    let c2 = badd(badd(b[2], b[3]), b[5]);
    let c1 = badd(b[1], b[3]);

    // (((2 * c8 + c4) * 2 + c2) * 2 + c1) via pure additions
    let d8 = badd(badd(c8, c8), c4);
    let d4 = badd(badd(d8, d8), c2);
    let dot = badd(badd(d4, d4), c1);

    ([b[1], b[2], b[3], b[4], b[5], b[6], b[7]], [c8, c4, c2, c1], dot)
}

/// Fast zero-multiplication E2M1 inner product `Σ_b decode_e2m1(q[b]) · vec[b] mod P`.
#[inline]
pub fn e2m1_horner_dot_bb(q_nibbles: &[u8], vec: &[u64]) -> u64 {
    e2m1_horner_buckets_bb(q_nibbles, vec).2
}

/// Degree-3 `{p(0), p(2), p(∞)}` wire message used on the 7 `k`-rounds of MXFP4 `b -> j -> k`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CubicZeroTwoInfMsg {
    pub p0: u64,
    pub p2: u64,
    pub p_inf: u64,
}

/// Transcript for native MXFP4 contraction `Y[i, j] = Σ_{k, b} X[i, k, b] · Q_e2m1[j, k, b] · S[j, k]`
/// (`ikb,jkb,jk -> ij`) under elimination order `b -> j -> k` (`l_0 = 5` on `B = 32`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Mxfp4BjkProof {
    pub claim: u64,
    pub log_j: usize,
    pub log_k: usize,
    pub r_j: Vec<u64>,
    /// 5 quadratic `{q(0), q(∞)}` messages for `b ∈ {0..31}` (`S`).
    pub b_rounds: Vec<[u64; 2]>,
    /// `log_j` Gruen Mode-2 quadratic messages for `j ∈ F_{>=2}` (including `r_j[u] == 0` fallback).
    pub j_rounds: Vec<GruenRoundMsg>,
    /// `log_k` cubic `{p(0), p(2), p(∞)}` messages for `k ∈ S`.
    pub k_rounds: Vec<CubicZeroTwoInfMsg>,
    pub chals_b: [u64; 5],
    pub chals_j: Vec<u64>,
    pub chals_k: Vec<u64>,
    /// Terminal evaluations `(X̂(r_i, c_k, c_b), Q̂(c_j, c_k, c_b), Ŝ(c_j, c_k))`.
    pub finals: (u64, u64, u64),
}

/// Delayed block-bind (`l_0 = 5`) + 7-bucket 0-mul E2M1 Horner MXFP4 prover (`b -> j -> k`):
/// * Never materializes a `(J, K, 32)` field buffer (`16×` smaller peak `Q` buffer!),
/// * Executes **zero multiplications** on `Q_nibbles` across both the `M[k, b]` projection and
///   the `Q^{(5)}[j, k]` block bind,
/// * Emits bit-identical sumcheck round messages to naive full-table `b -> j -> k`.
///
/// Tensor flat layouts (row-major over LSB-indexed axes):
/// * `x_ri`: `[K * 32]` (`k * 32 + b`, already bound at `F_1` challenge `r_i`),
/// * `q_nibbles`: `[J * K * 32]` (`(j * K + k) * 32 + b`, 4-bit E2M1 nibbles `0..16`),
/// * `s_scale`: `[J * K]` (`j * K + k`, BabyBear block scales).
pub fn prove_mxfp4_delayed_bjk_horner(
    x_ri: &[u64],
    q_nibbles: &[u8],
    s_scale: &[u64],
    log_j: usize,
    log_k: usize,
    r_j: &[u64],
    chals_b: &[u64; 5],
    chals_j: &[u64],
    chals_k: &[u64],
) -> Mxfp4BjkProof {
    let j_len = 1usize << log_j;
    let k_len = 1usize << log_k;
    assert_eq!(x_ri.len(), k_len * 32);
    assert_eq!(q_nibbles.len(), j_len * k_len * 32);
    assert_eq!(s_scale.len(), j_len * k_len);
    assert_eq!(r_j.len(), log_j);
    assert_eq!(chals_j.len(), log_j);
    assert_eq!(chals_k.len(), log_k);

    // Step 1: E_jk[j, k] = eq(r_j, j) · S[j, k] (`J * K` muls, 32x smaller than Q!)
    let eq_j = build_eq_table_lsb_bb(r_j);
    let mut e_jk = vec![0u64; j_len * k_len];
    for j in 0..j_len {
        let ej = eq_j[j];
        let row = j * k_len;
        for k in 0..k_len {
            e_jk[row + k] = bmul(ej, s_scale[row + k]);
        }
    }

    // Step 2: Collapse M[b, k] = Σ_j E_jk[j, k] · Q[j, k, b] via 7-bucket 0-mul E2M1 Horner!
    // Layout `[k * 32 + b]` so `b` is LSB stride 1 for `fold_table_bb`.
    let mut m_kb = vec![0u64; k_len * 32];
    for k in 0..k_len {
        let mut buckets = [[0u64; 8]; 32];
        for j in 0..j_len {
            let ejk = e_jk[j * k_len + k];
            let q_blk = &q_nibbles[(j * k_len + k) * 32..(j * k_len + k + 1) * 32];
            for b in 0..32 {
                let nib = q_blk[b];
                let mag = (nib & 7) as usize;
                if mag != 0 {
                    if (nib & 8) == 0 {
                        buckets[b][mag] = badd(buckets[b][mag], ejk);
                    } else {
                        buckets[b][mag] = bsub(buckets[b][mag], ejk);
                    }
                }
            }
        }
        for b in 0..32 {
            let bk = &buckets[b];
            let c8 = badd(bk[6], bk[7]);
            let c4 = badd(badd(bk[4], bk[5]), bk[7]);
            let c2 = badd(badd(bk[2], bk[3]), bk[5]);
            let c1 = badd(bk[1], bk[3]);
            let d8 = badd(badd(c8, c8), c4);
            let d4 = badd(badd(d8, d8), c2);
            m_kb[k * 32 + b] = badd(badd(d4, d4), c1);
        }
    }
    drop(e_jk);

    // Initial claim = Σ_{k, b} X_ri[k, b] · M[k, b]
    let mut claim_acc = 0u128;
    for idx in 0..(k_len * 32) {
        claim_acc += (x_ri[idx] as u128) * (m_kb[idx] as u128);
        if (idx & 15) == 15 {
            claim_acc %= P as u128;
        }
    }
    let claim = (claim_acc % P as u128) as u64;

    // Step 3: Run all 5 quadratic `b`-rounds on tiny `(K * 32)` buffers (`b` is LSB stride 1!)
    let mut x_cur = x_ri.to_vec();
    let mut m_cur = m_kb;
    let mut b_rounds = Vec::with_capacity(5);
    for r in 0..5 {
        let half = x_cur.len() / 2;
        let mut acc0 = 0u128;
        let mut acc_inf = 0u128;
        for idx in 0..half {
            let x0 = x_cur[2 * idx];
            let x1 = x_cur[2 * idx + 1];
            let m0 = m_cur[2 * idx];
            let m1 = m_cur[2 * idx + 1];
            let dx = bsub(x1, x0);
            let dm = bsub(m1, m0);
            acc0 += (x0 as u128) * (m0 as u128);
            acc_inf += (dx as u128) * (dm as u128);
            if (idx & 15) == 15 {
                acc0 %= P as u128;
                acc_inf %= P as u128;
            }
        }
        b_rounds.push([(acc0 % P as u128) as u64, (acc_inf % P as u128) as u64]);
        x_cur = fold_table_bb(&x_cur, chals_b[r]);
        m_cur = fold_table_bb(&m_cur, chals_b[r]);
    }
    let x5 = x_cur; // length `k_len`

    // Step 4: Bind Q^{(5)}[k, j] (`j` at LSB stride 1, `k` at high bits) via 0-mul E2M1 Horner!
    let eq_b = build_eq_table_lsb_bb(chals_b);
    let mut q_kj = vec![0u64; k_len * j_len];
    let mut s_kj = vec![0u64; k_len * j_len];
    for j in 0..j_len {
        for k in 0..k_len {
            let q_blk = &q_nibbles[(j * k_len + k) * 32..(j * k_len + k + 1) * 32];
            q_kj[k * j_len + j] = e2m1_horner_dot_bb(q_blk, &eq_b);
            s_kj[k * j_len + j] = s_scale[j * k_len + k];
        }
    }

    // Step 5: Gruen Mode-2 `j`-rounds on `q_kj` and `s_kj` weighted by `x5[k]`!
    // Pre-multiply `x5[k]` into `q_kj[k, j]`? Wait: `q_kj[k, j] * x5[k]` is linear in `q_kj`!
    // Check: `(X5[k] · Q_j(t)) · S_j(t)` has the EXACT same value for all `t` if we scale `Q5[k, j]`
    // once by `X5[k]` (`J * K` muls total instead of `2 * J * K` across rounds), while keeping `q_kj`
    // separately or folding `q_kj` for the terminal `Q̂` opening! Let's fold `q_kj` cleanly and weight
    // the `k`-accumulations by `x5[k]` so `q_kj` folds directly to `Q̂(c_j, k, c_b)`!
    let suf_j = build_eq_suffix_tables_bb(r_j);
    let mut j_rounds = Vec::with_capacity(log_j);
    for u in 0..log_j {
        let suf = &suf_j[log_j - 1 - u];
        let rem_j = suf.len();
        let stride_k = rem_j * 2;
        let mut c0_by_j = vec![0u64; rem_j];
        let mut cinf_by_j = vec![0u64; rem_j];
        for k in 0..k_len {
            let xk = x5[k];
            let base = k * stride_k;
            for jr in 0..rem_j {
                let idx0 = base + 2 * jr;
                let q0 = q_kj[idx0];
                let q1 = q_kj[idx0 + 1];
                let s0 = s_kj[idx0];
                let s1 = s_kj[idx0 + 1];
                let dq = bsub(q1, q0);
                let ds = bsub(s1, s0);
                c0_by_j[jr] = badd(c0_by_j[jr], bmul(xk, bmul(q0, s0)));
                cinf_by_j[jr] = badd(cinf_by_j[jr], bmul(xk, bmul(dq, ds)));
            }
        }
        let mut qu0 = 0u64;
        let mut qu_inf = 0u64;
        for jr in 0..rem_j {
            qu0 = badd(qu0, bmul(suf[jr], c0_by_j[jr]));
            qu_inf = badd(qu_inf, bmul(suf[jr], cinf_by_j[jr]));
        }
        if r_j[u] == 0 {
            let mut qu1 = 0u64;
            for k in 0..k_len {
                let xk = x5[k];
                let base = k * stride_k;
                for jr in 0..rem_j {
                    let idx1 = base + 2 * jr + 1;
                    let term = bmul(xk, bmul(q_kj[idx1], s_kj[idx1]));
                    qu1 = badd(qu1, bmul(suf[jr], term));
                }
            }
            j_rounds.push(GruenRoundMsg::ZeroEqFallback {
                q0: qu0,
                q_inf: qu_inf,
                q1: qu1,
            });
        } else {
            j_rounds.push(GruenRoundMsg::TwoPoint {
                q0: qu0,
                q_inf: qu_inf,
            });
        }
        q_kj = fold_table_bb(&q_kj, chals_j[u]);
        s_kj = fold_table_bb(&s_kj, chals_j[u]);
    }

    // Step 6: `log_k` cubic `{0, 2, ∞}` rounds on length-`K` vectors `(x5, q_kj, s_kj)`!
    let mut xk = x5;
    let mut qk = q_kj;
    let mut sk = s_kj;
    let mut k_rounds = Vec::with_capacity(log_k);
    for r in 0..log_k {
        let half = xk.len() / 2;
        let mut p0 = 0u64;
        let mut p2 = 0u64;
        let mut p_inf = 0u64;
        for idx in 0..half {
            let x0 = xk[2 * idx];
            let x1 = xk[2 * idx + 1];
            let q0 = qk[2 * idx];
            let q1 = qk[2 * idx + 1];
            let s0 = sk[2 * idx];
            let s1 = sk[2 * idx + 1];
            let dx = bsub(x1, x0);
            let dq = bsub(q1, q0);
            let ds = bsub(s1, s0);
            let x2 = badd(x1, dx);
            let q2 = badd(q1, dq);
            let s2 = badd(s1, ds);
            p0 = badd(p0, bmul(x0, bmul(q0, s0)));
            p2 = badd(p2, bmul(x2, bmul(q2, s2)));
            p_inf = badd(p_inf, bmul(dx, bmul(dq, ds)));
        }
        k_rounds.push(CubicZeroTwoInfMsg { p0, p2, p_inf });
        let ch = chals_k[r];
        xk = fold_table_bb(&xk, ch);
        qk = fold_table_bb(&qk, ch);
        sk = fold_table_bb(&sk, ch);
    }

    Mxfp4BjkProof {
        claim,
        log_j,
        log_k,
        r_j: r_j.to_vec(),
        b_rounds,
        j_rounds,
        k_rounds,
        chals_b: *chals_b,
        chals_j: chals_j.to_vec(),
        chals_k: chals_k.to_vec(),
        finals: (xk[0], qk[0], sk[0]),
    }
}

/// Reference naive `b -> j -> k` MXFP4 prover that materializes the full `(J * K * 32)` BabyBear
/// `Q` table and multiplies via `bmul` (used to cross-check bit-for-bit agreement and measure the
/// delayed block-bind + 7-bucket Horner speedup).
pub fn prove_mxfp4_naive_bjk(
    x_ri: &[u64],
    q_nibbles: &[u8],
    s_scale: &[u64],
    log_j: usize,
    log_k: usize,
    r_j: &[u64],
    chals_b: &[u64; 5],
    chals_j: &[u64],
    chals_k: &[u64],
) -> Mxfp4BjkProof {
    let j_len = 1usize << log_j;
    let k_len = 1usize << log_k;
    let eq_j = build_eq_table_lsb_bb(r_j);

    // Materialize full `(J * K * 32)` BabyBear buffer (`j * K * 32 + k * 32 + b`):
    let mut q_full = Vec::with_capacity(j_len * k_len * 32);
    for &nib in q_nibbles {
        q_full.push(decode_e2m1_x2_bb(nib));
    }

    // Claim:
    let mut claim = 0u64;
    for j in 0..j_len {
        for k in 0..k_len {
            let w_jk = bmul(eq_j[j], s_scale[j * k_len + k]);
            let mut inner = 0u64;
            for b in 0..32 {
                inner = badd(
                    inner,
                    bmul(x_ri[k * 32 + b], q_full[(j * k_len + k) * 32 + b]),
                );
            }
            claim = badd(claim, bmul(w_jk, inner));
        }
    }

    // 5 `b`-rounds scanning and folding the ENTIRE `(J * K * b_rem)` `q_full` buffer:
    let mut x_cur = x_ri.to_vec();
    let mut q_cur = q_full;
    let mut b_rounds = Vec::with_capacity(5);
    for r in 0..5 {
        let b_pairs = x_cur.len() / (2 * k_len);
        let mut r0 = 0u64;
        let mut r_inf = 0u64;
        for j in 0..j_len {
            let w_j = eq_j[j];
            let mut j0 = 0u64;
            let mut j_inf = 0u64;
            for k in 0..k_len {
                let s_jk = s_scale[j * k_len + k];
                let mut k0 = 0u64;
                let mut k_inf = 0u64;
                let x_base = k * 2 * b_pairs;
                let q_base = (j * k_len + k) * 2 * b_pairs;
                for bp in 0..b_pairs {
                    let x0 = x_cur[x_base + 2 * bp];
                    let x1 = x_cur[x_base + 2 * bp + 1];
                    let q0 = q_cur[q_base + 2 * bp];
                    let q1 = q_cur[q_base + 2 * bp + 1];
                    k0 = badd(k0, bmul(x0, q0));
                    k_inf = badd(k_inf, bmul(bsub(x1, x0), bsub(q1, q0)));
                }
                j0 = badd(j0, bmul(s_jk, k0));
                j_inf = badd(j_inf, bmul(s_jk, k_inf));
            }
            r0 = badd(r0, bmul(w_j, j0));
            r_inf = badd(r_inf, bmul(w_j, j_inf));
        }
        b_rounds.push([r0, r_inf]);
        x_cur = fold_table_bb(&x_cur, chals_b[r]);
        q_cur = fold_table_bb(&q_cur, chals_b[r]);
    }

    // Transpose `q_cur` `[J * K]` -> `[K * J]` for `j`-rounds:
    let mut q_kj = vec![0u64; k_len * j_len];
    let mut s_kj = vec![0u64; k_len * j_len];
    for j in 0..j_len {
        for k in 0..k_len {
            q_kj[k * j_len + j] = q_cur[j * k_len + k];
            s_kj[k * j_len + j] = s_scale[j * k_len + k];
        }
    }

    let suf_j = build_eq_suffix_tables_bb(r_j);
    let mut j_rounds = Vec::with_capacity(log_j);
    for u in 0..log_j {
        let suf = &suf_j[log_j - 1 - u];
        let rem_j = suf.len();
        let stride_k = rem_j * 2;
        let mut qu0 = 0u64;
        let mut qu_inf = 0u64;
        for jr in 0..rem_j {
            let mut acc0 = 0u64;
            let mut acc_inf = 0u64;
            for k in 0..k_len {
                let idx0 = k * stride_k + 2 * jr;
                let dq = bsub(q_kj[idx0 + 1], q_kj[idx0]);
                let ds = bsub(s_kj[idx0 + 1], s_kj[idx0]);
                acc0 = badd(acc0, bmul(x_cur[k], bmul(q_kj[idx0], s_kj[idx0])));
                acc_inf = badd(acc_inf, bmul(x_cur[k], bmul(dq, ds)));
            }
            qu0 = badd(qu0, bmul(suf[jr], acc0));
            qu_inf = badd(qu_inf, bmul(suf[jr], acc_inf));
        }
        if r_j[u] == 0 {
            let mut qu1 = 0u64;
            for jr in 0..rem_j {
                let mut acc1 = 0u64;
                for k in 0..k_len {
                    let idx1 = k * stride_k + 2 * jr + 1;
                    acc1 = badd(acc1, bmul(x_cur[k], bmul(q_kj[idx1], s_kj[idx1])));
                }
                qu1 = badd(qu1, bmul(suf[jr], acc1));
            }
            j_rounds.push(GruenRoundMsg::ZeroEqFallback {
                q0: qu0,
                q_inf: qu_inf,
                q1: qu1,
            });
        } else {
            j_rounds.push(GruenRoundMsg::TwoPoint {
                q0: qu0,
                q_inf: qu_inf,
            });
        }
        q_kj = fold_table_bb(&q_kj, chals_j[u]);
        s_kj = fold_table_bb(&s_kj, chals_j[u]);
    }

    let mut xk = x_cur;
    let mut qk = q_kj;
    let mut sk = s_kj;
    let mut k_rounds = Vec::with_capacity(log_k);
    for r in 0..log_k {
        let half = xk.len() / 2;
        let mut p0 = 0u64;
        let mut p2 = 0u64;
        let mut p_inf = 0u64;
        for idx in 0..half {
            let dx = bsub(xk[2 * idx + 1], xk[2 * idx]);
            let dq = bsub(qk[2 * idx + 1], qk[2 * idx]);
            let ds = bsub(sk[2 * idx + 1], sk[2 * idx]);
            let x2 = badd(xk[2 * idx + 1], dx);
            let q2 = badd(qk[2 * idx + 1], dq);
            let s2 = badd(sk[2 * idx + 1], ds);
            p0 = badd(p0, bmul(xk[2 * idx], bmul(qk[2 * idx], sk[2 * idx])));
            p2 = badd(p2, bmul(x2, bmul(q2, s2)));
            p_inf = badd(p_inf, bmul(dx, bmul(dq, ds)));
        }
        k_rounds.push(CubicZeroTwoInfMsg { p0, p2, p_inf });
        let ch = chals_k[r];
        xk = fold_table_bb(&xk, ch);
        qk = fold_table_bb(&qk, ch);
        sk = fold_table_bb(&sk, ch);
    }

    Mxfp4BjkProof {
        claim,
        log_j,
        log_k,
        r_j: r_j.to_vec(),
        b_rounds,
        j_rounds,
        k_rounds,
        chals_b: *chals_b,
        chals_j: chals_j.to_vec(),
        chals_k: chals_k.to_vec(),
        finals: (xk[0], qk[0], sk[0]),
    }
}

/// Fail-closed verifier for MXFP4 `b -> j -> k` Mode-2 sumcheck over BabyBear.
pub fn verify_mxfp4_bjk_mode2(
    expected_claim: u64,
    proof: &Mxfp4BjkProof,
    open_xqs: impl Fn(&[u64; 5], &[u64], &[u64]) -> (u64, u64, u64),
) -> bool {
    if proof.claim != expected_claim || proof.claim >= P {
        return false;
    }
    if proof.b_rounds.len() != 5
        || proof.j_rounds.len() != proof.log_j
        || proof.k_rounds.len() != proof.log_k
        || proof.r_j.len() != proof.log_j
        || proof.chals_j.len() != proof.log_j
        || proof.chals_k.len() != proof.log_k
    {
        return false;
    }
    if proof.chals_b.iter().any(|&c| c >= P)
        || proof.r_j.iter().any(|&r| r >= P)
        || proof.chals_j.iter().any(|&c| c >= P)
        || proof.chals_k.iter().any(|&c| c >= P)
    {
        return false;
    }

    let mut sigma = proof.claim;

    // 1. 5 quadratic `b`-rounds:
    for r in 0..5 {
        let [q0, q_inf] = proof.b_rounds[r];
        if q0 >= P || q_inf >= P {
            return false;
        }
        let q1 = bsub(sigma, q0);
        sigma = eval_quad_zero_one_inf(q0, q1, q_inf, proof.chals_b[r], P);
    }

    // 2. `log_j` Gruen Mode-2 `j`-rounds (`eq(r_j, chals_j)` stripped on exit!):
    for u in 0..proof.log_j {
        let ru = proof.r_j[u];
        let ch = proof.chals_j[u];
        if ru == 0 {
            match proof.j_rounds[u] {
                GruenRoundMsg::ZeroEqFallback { q0, q_inf, q1 } => {
                    if q0 >= P || q_inf >= P || q1 >= P || q0 != sigma {
                        return false;
                    }
                    sigma = eval_quad_zero_one_inf(q0, q1, q_inf, ch, P);
                }
                GruenRoundMsg::TwoPoint { .. } => return false,
            }
        } else {
            match proof.j_rounds[u] {
                GruenRoundMsg::TwoPoint { q0, q_inf } => {
                    if q0 >= P || q_inf >= P {
                        return false;
                    }
                    let l0_q0 = bmul(bsub(1, ru), q0);
                    let q1 = bmul(binv(ru), bsub(sigma, l0_q0));
                    sigma = eval_quad_zero_one_inf(q0, q1, q_inf, ch, P);
                }
                GruenRoundMsg::ZeroEqFallback { .. } => return false,
            }
        }
    }

    // 3. `log_k` cubic `{0, 2, ∞}` `k`-rounds:
    for r in 0..proof.log_k {
        let m = proof.k_rounds[r];
        if m.p0 >= P || m.p2 >= P || m.p_inf >= P {
            return false;
        }
        let p1 = bsub(sigma, m.p0);
        sigma = match eval_cubic_zero_one_two_inf(m.p0, p1, m.p2, m.p_inf, proof.chals_k[r], P) {
            Some(v) => v,
            None => return false,
        };
    }

    let (ox, oq, os) = open_xqs(&proof.chals_b, &proof.chals_j, &proof.chals_k);
    if ox >= P || oq >= P || os >= P {
        return false;
    }
    sigma == bmul(ox, bmul(oq, os))
}
