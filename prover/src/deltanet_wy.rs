//! Division-free `Gated DeltaNet` (`arXiv:2608.30320` Eqs. 1–5) chunkwise WY `(I + L)[U | W] = RHS`
//! solver and flat degree-2 `Gruen` Mode-2 `EinSumcheck` prover/verifier.
//!
//! Substrate, said out loud: UNVERIFIED NATIVE COMPUTE bound to the Lean-authored conformance
//! vector `prover/testdata/deltanet_wy_conformance.json` (`Compiler/DeltaNetWyConformance.lean`
//! instantiating `Theory/ZkmlDeltaNet.lean`). Because `IsStrictLowerTri L` implies `L^C = 0` and
//! `(1 + L) · neumannInv L = 1` division-free over any commutative ring, the prover computes `UW`
//! by forward substitution (`0` inversions, even when `alpha_t == 0`) and proves `L · UW = RHS - UW`
//! (`hij,hjk -> hik`) in one flat quadratic Gruen Mode-2 `EinSumcheck` (`0` sequential GKR layers).

use crate::babybear::{badd, bmul, bsub, P};
use crate::gruen_einsum::{
    build_eq_table_lsb_bb, prove_gruen_einsum_mode2_bb, verify_gruen_einsum_mode2,
    GruenEinSumcheckProof,
};
use crate::sumcheck::mle_eval;

/// Single-head chunkwise WY intermediate artifacts (`C × C` coupling `L`, `C × (d_v + d_k)` `RHS`
/// and `UW = [U | W]`, prefix/suffix/pairwise decays, chunk readouts `Y`, and updated state `S_final`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WyHeadWitness {
    pub gamma: Vec<u64>,
    pub bar_gamma: Vec<u64>,
    pub cap_gamma: Vec<Vec<u64>>,
    pub matrix_l: Vec<Vec<u64>>,
    pub rhs: Vec<Vec<u64>>,
    pub uw: Vec<Vec<u64>>,
    pub y_out: Vec<Vec<u64>>,
    pub s_final: Vec<Vec<u64>>,
}

/// Multi-head flat contiguous chunkwise WY witness (`H_v` value heads, chunk length `C`,
/// `col_dim = d_v + d_k`), optimized for `Qwen3.8-Flash-Next` (`H_v = 48, d_k = d_v = 128, C = 64`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WyLayerChunk {
    pub h_v: usize,
    pub c_len: usize,
    pub d_k: usize,
    pub d_v: usize,
    /// `[h_v * c_len * c_len]` row-major `(h, i, j)`.
    pub l_flat: Vec<u64>,
    /// `[h_v * c_len * (d_v + d_k)]` row-major `(h, i, col)`.
    pub rhs_flat: Vec<u64>,
    /// `[h_v * c_len * (d_v + d_k)]` row-major `(h, i, col)`.
    pub uw_flat: Vec<u64>,
    /// `[h_v * c_len * d_v]` row-major `(h, t, dv)`.
    pub y_flat: Vec<u64>,
    /// `[h_v * d_k * d_v]` row-major `(h, dk, dv)`.
    pub s_final_flat: Vec<u64>,
}

/// Check strict lower triangularity `L[i][j] == 0` for all `i <= j`, mirroring
/// `Theory/ZkmlDeltaNet.IsStrictLowerTri`.
pub fn is_strict_lower_tri_2d(l: &[Vec<u64>]) -> bool {
    let c = l.len();
    for (i, row) in l.iter().enumerate() {
        if row.len() != c {
            return false;
        }
        for j in i..c {
            if row[j] % P != 0 {
                return false;
            }
        }
    }
    true
}

/// Check strict lower triangularity across all `h_v` heads in a flat `[h_v * c * c]` buffer.
pub fn is_strict_lower_tri_flat(l_flat: &[u64], h_v: usize, c: usize) -> bool {
    if l_flat.len() != h_v * c * c {
        return false;
    }
    for h in 0..h_v {
        let h_off = h * c * c;
        for i in 0..c {
            let row_off = h_off + i * c;
            for j in i..c {
                if l_flat[row_off + j] != 0 {
                    return false;
                }
            }
        }
    }
    true
}

/// Mirror of `Theory/ZkmlDeltaNet.neumannInv`: `∑_{m=0}^{C-1} (-L)^m mod P` (division-free).
pub fn neumann_inv_bb(l: &[Vec<u64>]) -> Vec<Vec<u64>> {
    let c = l.len();
    let mut neg_l = vec![vec![0u64; c]; c];
    for i in 0..c {
        assert_eq!(l[i].len(), c);
        for j in 0..c {
            neg_l[i][j] = bsub(0, l[i][j] % P);
        }
    }
    let mut acc = vec![vec![0u64; c]; c];
    let mut cur_pow = vec![vec![0u64; c]; c];
    for i in 0..c {
        cur_pow[i][i] = 1;
    }
    for m in 0..c {
        for i in 0..c {
            for j in 0..c {
                acc[i][j] = badd(acc[i][j], cur_pow[i][j]);
            }
        }
        if m + 1 < c {
            let mut next = vec![vec![0u64; c]; c];
            for i in 0..c {
                for k in 0..c {
                    let cik = cur_pow[i][k];
                    if cik != 0 {
                        for j in 0..c {
                            next[i][j] = badd(next[i][j], bmul(cik, neg_l[k][j]));
                        }
                    }
                }
            }
            cur_pow = next;
        }
    }
    acc
}

/// Sequential Gated DeltaNet (`Theory/ZkmlDeltaNet.gdnStep` + `gdnReadout`) on a single head over
/// `C` steps starting from `s_init` (`d_k × d_v`).
pub fn gdn_sequential_head_bb(
    q: &[Vec<u64>],
    k: &[Vec<u64>],
    v: &[Vec<u64>],
    alpha: &[u64],
    beta: &[u64],
    s_init: &[Vec<u64>],
) -> (Vec<Vec<u64>>, Vec<Vec<u64>>) {
    let c = alpha.len();
    assert_eq!(beta.len(), c);
    assert_eq!(q.len(), c);
    assert_eq!(k.len(), c);
    assert_eq!(v.len(), c);
    let dk = s_init.len();
    let dv = s_init[0].len();

    let mut s = s_init.to_vec();
    let mut y_out = Vec::with_capacity(c);

    for t in 0..c {
        let at = alpha[t] % P;
        let bt = beta[t] % P;
        // s_tilde = alpha_t * S
        let mut s_tilde = vec![vec![0u64; dv]; dk];
        for i in 0..dk {
            for j in 0..dv {
                s_tilde[i][j] = bmul(at, s[i][j] % P);
            }
        }
        // res_j = v_j - (s_tilde^T * k)_j
        let mut res = vec![0u64; dv];
        for j in 0..dv {
            let mut mem = 0u64;
            for i in 0..dk {
                mem = badd(mem, bmul(s_tilde[i][j], k[t][i] % P));
            }
            res[j] = bsub(v[t][j] % P, mem);
        }
        // S' = s_tilde + beta_t * (k ⊗ res)
        for i in 0..dk {
            let b_ki = bmul(bt, k[t][i] % P);
            for j in 0..dv {
                s[i][j] = badd(s_tilde[i][j], bmul(b_ki, res[j]));
            }
        }
        // y_t = S'^T * q_t
        let mut yt = vec![0u64; dv];
        for j in 0..dv {
            let mut sum = 0u64;
            for i in 0..dk {
                sum = badd(sum, bmul(s[i][j], q[t][i] % P));
            }
            yt[j] = sum;
        }
        y_out.push(yt);
    }
    (y_out, s)
}

/// Division-free single-head chunkwise WY solver (`0` inversions; handles `alpha[t] == 0` cleanly).
pub fn gdn_chunkwise_wy_head_bb(
    q: &[Vec<u64>],
    k: &[Vec<u64>],
    v: &[Vec<u64>],
    alpha: &[u64],
    beta: &[u64],
    s_init: &[Vec<u64>],
) -> WyHeadWitness {
    let c = alpha.len();
    let dk = s_init.len();
    let dv = s_init[0].len();
    let cols = dv + dk;

    // 1. Division-free prefix, suffix, and pairwise decays:
    let mut gamma = vec![0u64; c];
    let mut bar_gamma = vec![0u64; c];
    let mut cap_gamma = vec![vec![0u64; c]; c];

    let mut pref = 1u64;
    for i in 0..c {
        pref = bmul(pref, alpha[i] % P);
        gamma[i] = pref;
        cap_gamma[i][i] = 1;
        let mut pij = 1u64;
        for j in (0..i).rev() {
            pij = bmul(pij, alpha[j + 1] % P);
            cap_gamma[i][j] = pij;
        }
    }
    let mut suf = 1u64;
    for j in (0..c).rev() {
        bar_gamma[j] = suf;
        suf = bmul(suf, alpha[j] % P);
    }

    // 2. Strictly lower-triangular coupling matrix L[i][j] = beta_i * cap_gamma[i][j] * <k_i, k_j>
    let mut matrix_l = vec![vec![0u64; c]; c];
    for i in 1..c {
        let bi = beta[i] % P;
        for j in 0..i {
            let mut dot_kk = 0u64;
            for d in 0..dk {
                dot_kk = badd(dot_kk, bmul(k[i][d] % P, k[j][d] % P));
            }
            matrix_l[i][j] = bmul(bi, bmul(cap_gamma[i][j], dot_kk));
        }
    }

    // 3. RHS = [diag(beta) * V | diag(gamma ⊙ beta) * K]
    let mut rhs = vec![vec![0u64; cols]; c];
    for i in 0..c {
        let bi = beta[i] % P;
        let gbi = bmul(gamma[i], bi);
        for j in 0..dv {
            rhs[i][j] = bmul(bi, v[i][j] % P);
        }
        for j in 0..dk {
            rhs[i][dv + j] = bmul(gbi, k[i][j] % P);
        }
    }

    // 4. Unit-lower-triangular forward substitution `(I + L) * UW = RHS` (zero inversions!)
    let mut uw = vec![vec![0u64; cols]; c];
    for i in 0..c {
        for col in 0..cols {
            let mut corr = 0u64;
            for j in 0..i {
                corr = badd(corr, bmul(matrix_l[i][j], uw[j][col]));
            }
            uw[i][col] = bsub(rhs[i][col], corr);
        }
    }

    // 5. U_eff = U - W * S_init (`C × dv`)
    let mut u_eff = vec![vec![0u64; dv]; c];
    for i in 0..c {
        for j in 0..dv {
            let mut ws = 0u64;
            for d in 0..dk {
                ws = badd(ws, bmul(uw[i][dv + d], s_init[d][j] % P));
            }
            u_eff[i][j] = bsub(uw[i][j], ws);
        }
    }

    // 6. Y_out[i] = gamma[i] * (S_init^T * q_i) + ∑_{j <= i} (cap_gamma[i][j] * <q_i, k_j>) * u_eff[j]
    let mut y_out = vec![vec![0u64; dv]; c];
    for i in 0..c {
        let gi = gamma[i];
        let mut m_qk_row = vec![0u64; i + 1];
        for j in 0..=i {
            let mut qk = 0u64;
            for d in 0..dk {
                qk = badd(qk, bmul(q[i][d] % P, k[j][d] % P));
            }
            m_qk_row[j] = bmul(cap_gamma[i][j], qk);
        }
        for col in 0..dv {
            let mut inter = 0u64;
            for d in 0..dk {
                inter = badd(inter, bmul(bmul(gi, q[i][d] % P), s_init[d][col] % P));
            }
            let mut intra = 0u64;
            for j in 0..=i {
                intra = badd(intra, bmul(m_qk_row[j], u_eff[j][col]));
            }
            y_out[i][col] = badd(inter, intra);
        }
    }

    // 7. S_final = gamma[c - 1] * S_init + (diag(bar_gamma) * K)^T * U_eff
    let g_last = gamma[c - 1];
    let mut s_final = vec![vec![0u64; dv]; dk];
    for d in 0..dk {
        for col in 0..dv {
            let mut acc = bmul(g_last, s_init[d][col] % P);
            for j in 0..c {
                let kb = bmul(bar_gamma[j], k[j][d] % P);
                acc = badd(acc, bmul(kb, u_eff[j][col]));
            }
            s_final[d][col] = acc;
        }
    }

    WyHeadWitness {
        gamma,
        bar_gamma,
        cap_gamma,
        matrix_l,
        rhs,
        uw,
        y_out,
        s_final,
    }
}

/// High-throughput flat-buffer multi-head chunkwise WY forward pass (`H_v` value heads, `H_k`
/// key/query heads with GVA broadcast `rep = H_v / H_k`, chunk size `c_len`, `d_k`, `d_v`).
///
/// Flat input layouts:
/// * `q_flat`, `k_flat`: `[h_k * c_len * d_k]`
/// * `v_flat`: `[h_v * c_len * d_v]`
/// * `alpha_flat`, `beta_flat`: `[h_v * c_len]`
/// * `s_init_flat`: `[h_v * d_k * d_v]`
pub fn gdn_chunkwise_wy_layer_bb(
    h_k: usize,
    h_v: usize,
    c_len: usize,
    d_k: usize,
    d_v: usize,
    q_flat: &[u64],
    k_flat: &[u64],
    v_flat: &[u64],
    alpha_flat: &[u64],
    beta_flat: &[u64],
    s_init_flat: &[u64],
) -> WyLayerChunk {
    assert!(h_v % h_k == 0);
    let rep = h_v / h_k;
    let cols = d_v + d_k;
    assert_eq!(q_flat.len(), h_k * c_len * d_k);
    assert_eq!(k_flat.len(), h_k * c_len * d_k);
    assert_eq!(v_flat.len(), h_v * c_len * d_v);
    assert_eq!(alpha_flat.len(), h_v * c_len);
    assert_eq!(beta_flat.len(), h_v * c_len);
    assert_eq!(s_init_flat.len(), h_v * d_k * d_v);

    let mut l_flat = vec![0u64; h_v * c_len * c_len];
    let mut rhs_flat = vec![0u64; h_v * c_len * cols];
    let mut uw_flat = vec![0u64; h_v * c_len * cols];
    let mut y_flat = vec![0u64; h_v * c_len * d_v];
    let mut s_final_flat = vec![0u64; h_v * d_k * d_v];

    // Precompute `k_i · k_j` and `q_i · k_j` per key-head `hk` (`3×` GVA reuse across `rep = 3`!):
    let mut kk_by_hk = vec![0u64; h_k * c_len * c_len];
    let mut qk_by_hk = vec![0u64; h_k * c_len * c_len];
    for hk in 0..h_k {
        let k_head = &k_flat[hk * c_len * d_k..(hk + 1) * c_len * d_k];
        let q_head = &q_flat[hk * c_len * d_k..(hk + 1) * c_len * d_k];
        let out_off = hk * c_len * c_len;
        for i in 0..c_len {
            let ki = &k_head[i * d_k..(i + 1) * d_k];
            let qi = &q_head[i * d_k..(i + 1) * d_k];
            for j in 0..=i {
                let kj = &k_head[j * d_k..(j + 1) * d_k];
                let mut d_kk = 0u128;
                let mut d_qk = 0u128;
                for d in 0..d_k {
                    let kj_d = kj[d] as u128;
                    d_kk += (ki[d] as u128) * kj_d;
                    d_qk += (qi[d] as u128) * kj_d;
                    if (d & 15) == 15 {
                        d_kk %= P as u128;
                        d_qk %= P as u128;
                    }
                }
                kk_by_hk[out_off + i * c_len + j] = (d_kk % P as u128) as u64;
                qk_by_hk[out_off + i * c_len + j] = (d_qk % P as u128) as u64;
            }
        }
    }

    let mut gamma = vec![0u64; c_len];
    let mut bar_gamma = vec![0u64; c_len];
    let mut cap_gamma = vec![0u64; c_len * c_len];
    let mut u_eff = vec![0u64; c_len * d_v];

    for hv in 0..h_v {
        let hk = hv / rep;
        let q_head = &q_flat[hk * c_len * d_k..(hk + 1) * c_len * d_k];
        let k_head = &k_flat[hk * c_len * d_k..(hk + 1) * c_len * d_k];
        let v_head = &v_flat[hv * c_len * d_v..(hv + 1) * c_len * d_v];
        let ac = &alpha_flat[hv * c_len..(hv + 1) * c_len];
        let bc = &beta_flat[hv * c_len..(hv + 1) * c_len];
        let s_prev = &s_init_flat[hv * d_k * d_v..(hv + 1) * d_k * d_v];
        let kk_mat = &kk_by_hk[hk * c_len * c_len..(hk + 1) * c_len * c_len];
        let qk_mat = &qk_by_hk[hk * c_len * c_len..(hk + 1) * c_len * c_len];

        cap_gamma.fill(0);
        let mut pref = 1u64;
        for i in 0..c_len {
            pref = bmul(pref, ac[i]);
            gamma[i] = pref;
            cap_gamma[i * c_len + i] = 1;
            let mut pij = 1u64;
            for j in (0..i).rev() {
                pij = bmul(pij, ac[j + 1]);
                cap_gamma[i * c_len + j] = pij;
            }
        }
        let mut suf = 1u64;
        for j in (0..c_len).rev() {
            bar_gamma[j] = suf;
            suf = bmul(suf, ac[j]);
        }

        let l_head = &mut l_flat[hv * c_len * c_len..(hv + 1) * c_len * c_len];
        for i in 1..c_len {
            let bi = bc[i];
            let row = i * c_len;
            for j in 0..i {
                l_head[row + j] = bmul(bi, bmul(cap_gamma[row + j], kk_mat[row + j]));
            }
        }

        let rhs_head = &mut rhs_flat[hv * c_len * cols..(hv + 1) * c_len * cols];
        let uw_head = &mut uw_flat[hv * c_len * cols..(hv + 1) * c_len * cols];
        for i in 0..c_len {
            let bi = bc[i];
            let gbi = bmul(gamma[i], bi);
            let r_off = i * cols;
            let v_off = i * d_v;
            let k_off = i * d_k;
            for col in 0..d_v {
                rhs_head[r_off + col] = bmul(bi, v_head[v_off + col]);
            }
            for col in 0..d_k {
                rhs_head[r_off + d_v + col] = bmul(gbi, k_head[k_off + col]);
            }

            // Forward substitution row `i`: `UW[i, col] = RHS[i, col] - ∑_{j < i} L[i, j] * UW[j, col]`
            // Accumulate `∑_{j < i} L[i, j] * UW[j, col]` in `u128` (`c_len * P^2 < 2^70 << 2^128`
            // for all practical `c_len <= 2^64`, reducing mod `P` once per output cell!).
            let mut corr_acc = vec![0u128; cols];
            for j in 0..i {
                let lij = l_head[i * c_len + j] as u128;
                if lij != 0 {
                    let uw_j = &uw_head[j * cols..(j + 1) * cols];
                    for col in 0..cols {
                        corr_acc[col] += lij * (uw_j[col] as u128);
                    }
                }
            }
            for col in 0..cols {
                let corr = (corr_acc[col] % (P as u128)) as u64;
                uw_head[r_off + col] = bsub(rhs_head[r_off + col], corr);
            }
        }

        // U_eff[i, dv] = U[i, dv] - ∑_d W[i, d] * S_prev[d, dv] (`d_k * P^2 << 2^128`)
        let mut ws_acc = vec![0u128; d_v];
        for i in 0..c_len {
            let u_row = &mut u_eff[i * d_v..(i + 1) * d_v];
            let uw_row = &uw_head[i * cols..(i + 1) * cols];
            ws_acc.fill(0);
            for d in 0..d_k {
                let wid = uw_row[d_v + d] as u128;
                if wid != 0 {
                    let s_row = &s_prev[d * d_v..(d + 1) * d_v];
                    for col in 0..d_v {
                        ws_acc[col] += wid * (s_row[col] as u128);
                    }
                }
            }
            for col in 0..d_v {
                u_row[col] = bsub(uw_row[col], (ws_acc[col] % (P as u128)) as u64);
            }
        }

        // Y_out[i, col] = (gamma[i] * q_i)^T S_prev[:, col] + ∑_{j <= i} (cap_gamma[i,j]*qk[i,j]) * U_eff[j, col]
        let y_head = &mut y_flat[hv * c_len * d_v..(hv + 1) * c_len * d_v];
        let mut y_acc = vec![0u128; d_v];
        for i in 0..c_len {
            let gi = gamma[i];
            let y_row = &mut y_head[i * d_v..(i + 1) * d_v];
            let qi = &q_head[i * d_k..(i + 1) * d_k];
            y_acc.fill(0);
            if gi != 0 {
                for d in 0..d_k {
                    let qg = bmul(gi, qi[d]) as u128;
                    if qg != 0 {
                        let s_row = &s_prev[d * d_v..(d + 1) * d_v];
                        for col in 0..d_v {
                            y_acc[col] += qg * (s_row[col] as u128);
                        }
                    }
                }
            }
            for j in 0..=i {
                let m_ij = bmul(cap_gamma[i * c_len + j], qk_mat[i * c_len + j]) as u128;
                if m_ij != 0 {
                    let ue_row = &u_eff[j * d_v..(j + 1) * d_v];
                    for col in 0..d_v {
                        y_acc[col] += m_ij * (ue_row[col] as u128);
                    }
                }
            }
            for col in 0..d_v {
                y_row[col] = (y_acc[col] % (P as u128)) as u64;
            }
        }

        // S_final[d, col] = gamma[c_len - 1] * S_prev[d, col] + ∑_j (bar_gamma[j] * k[j, d]) * U_eff[j, col]
        let g_last = gamma[c_len - 1] as u128;
        let sf_head = &mut s_final_flat[hv * d_k * d_v..(hv + 1) * d_k * d_v];
        let mut sf_acc = vec![0u128; d_k * d_v];
        if g_last != 0 {
            for idx in 0..(d_k * d_v) {
                sf_acc[idx] = g_last * (s_prev[idx] as u128);
            }
        }
        for j in 0..c_len {
            let bg_j = bar_gamma[j];
            if bg_j != 0 {
                let kj = &k_head[j * d_k..(j + 1) * d_k];
                let ue_row = &u_eff[j * d_v..(j + 1) * d_v];
                for d in 0..d_k {
                    let kb = bmul(bg_j, kj[d]) as u128;
                    if kb != 0 {
                        let sf_row = &mut sf_acc[d * d_v..(d + 1) * d_v];
                        for col in 0..d_v {
                            sf_row[col] += kb * (ue_row[col] as u128);
                        }
                    }
                }
            }
        }
        for idx in 0..(d_k * d_v) {
            sf_head[idx] = (sf_acc[idx] % (P as u128)) as u64;
        }
    }

    WyLayerChunk {
        h_v,
        c_len,
        d_k,
        d_v,
        l_flat,
        rhs_flat,
        uw_flat,
        y_flat,
        s_final_flat,
    }
}

// ===========================================================================
// §2. Flat Degree-2 `Gruen` Mode-2 `EinSumcheck` for `L · UW = RHS - UW`
// ===========================================================================

/// Proof bundle for batched chunkwise WY `(I + L) · UW = RHS` (`L · UW = RHS - UW`, contraction
/// `hij,hjk -> hik` with `i ∈ F_1(L)`, `k ∈ F_1(UW)`, `h ∈ F_{>=2}`, `j ∈ S`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WyGruenProof {
    pub h_v: usize,
    pub h_pad: usize,
    pub c_pad: usize,
    pub col_pad: usize,
    pub r_h: Vec<u64>,
    pub r_i: Vec<u64>,
    pub r_k: Vec<u64>,
    pub sumcheck: GruenEinSumcheckProof,
}

fn next_pow2_at_least_1(n: usize) -> (usize, usize) {
    let p2 = n.max(1).next_power_of_two();
    (p2, p2.trailing_zeros() as usize)
}

/// Build the `(mu_s + kappa)`-flattened partial tables `(A_flat, B_flat)` and output MLE evaluation
/// `D̂(r_h, r_i, r_k)` where `D = RHS - UW` (`bits 0..b_h-1` = `h`, `bits b_h..b_h+b_j-1` = `j`),
/// skipping zero-padded dummy heads `h >= h_v` with zero overhead!
pub fn build_wy_bilinear_tables_bb(
    h_v: usize,
    c_len: usize,
    cols: usize,
    l_flat: &[u64],
    uw_flat: &[u64],
    rhs_flat: &[u64],
    r_h: &[u64],
    r_i: &[u64],
    r_k: &[u64],
) -> (Vec<u64>, Vec<u64>, u64) {
    let (h_pad, b_h) = next_pow2_at_least_1(h_v);
    let (c_pad, b_c) = next_pow2_at_least_1(c_len);
    let (_col_pad, b_col) = next_pow2_at_least_1(cols);
    assert_eq!(r_h.len(), b_h);
    assert_eq!(r_i.len(), b_c);
    assert_eq!(r_k.len(), b_col);
    assert_eq!(l_flat.len(), h_v * c_len * c_len);
    assert_eq!(uw_flat.len(), h_v * c_len * cols);
    assert_eq!(rhs_flat.len(), h_v * c_len * cols);

    let eq_h = build_eq_table_lsb_bb(r_h);
    let eq_i = build_eq_table_lsb_bb(r_i);
    let eq_k = build_eq_table_lsb_bb(r_k);

    let mut a_tab = vec![0u64; h_pad * c_pad];
    let mut b_tab = vec![0u64; h_pad * c_pad];
    let mut claim_d = 0u64;

    for h in 0..h_v {
        let l_head = &l_flat[h * c_len * c_len..(h + 1) * c_len * c_len];
        let uw_head = &uw_flat[h * c_len * cols..(h + 1) * c_len * cols];
        let rhs_head = &rhs_flat[h * c_len * cols..(h + 1) * c_len * cols];

        // A[h, j] = ∑_{i=0}^{c_len-1} eq_i[i] * L[h, i, j] (note L[h, i, j] == 0 for j >= i if strict lower,
        // but we sum all i in 0..c_len so even non-strict-lower falsifiers are faithfully evaluated!)
        for i in 0..c_len {
            let ei = eq_i[i];
            let l_row = &l_head[i * c_len..(i + 1) * c_len];
            for j in 0..c_len {
                let lij = l_row[j];
                if lij != 0 {
                    let idx = (j << b_h) + h;
                    a_tab[idx] = badd(a_tab[idx], bmul(ei, lij));
                }
            }
        }

        // B[h, j] = ∑_{k=0}^{cols-1} eq_k[k] * UW[h, j, k], and D_h = ∑_{i,k} eq_i[i]*eq_k[k]*(RHS - UW)
        let mut d_head = 0u64;
        for j in 0..c_len {
            let uw_row = &uw_head[j * cols..(j + 1) * cols];
            let rhs_row = &rhs_head[j * cols..(j + 1) * cols];
            let mut acc_b = 0u128;
            let mut acc_d = 0u128;
            for col in 0..cols {
                let ek = eq_k[col] as u128;
                let uw_v = uw_row[col];
                let d_v = bsub(rhs_row[col], uw_v);
                acc_b += ek * (uw_v as u128);
                acc_d += ek * (d_v as u128);
                if (col & 15) == 15 {
                    acc_b %= P as u128;
                    acc_d %= P as u128;
                }
            }
            b_tab[(j << b_h) + h] = (acc_b % P as u128) as u64;
            let d_row = (acc_d % P as u128) as u64;
            d_head = badd(d_head, bmul(eq_i[j], d_row));
        }
        claim_d = badd(claim_d, bmul(eq_h[h], d_head));
    }

    (a_tab, b_tab, claim_d)
}

/// Prove `(I + L) · UW = RHS` (`L · UW = RHS - UW`) across all `h_v` heads in **one flat degree-2
/// Gruen Mode-2 `EinSumcheck`** (`b_h + b_c` quadratic rounds, `0` GKR layers, `0` inversions).
pub fn prove_wy_chunk_gruen(
    h_v: usize,
    c_len: usize,
    cols: usize,
    l_flat: &[u64],
    uw_flat: &[u64],
    rhs_flat: &[u64],
    r_h: &[u64],
    r_i: &[u64],
    r_k: &[u64],
    challenges: &[u64],
) -> WyGruenProof {
    let (h_pad, _) = next_pow2_at_least_1(h_v);
    let (c_pad, _) = next_pow2_at_least_1(c_len);
    let (col_pad, _) = next_pow2_at_least_1(cols);
    let (a_tab, b_tab, _claim_d) = build_wy_bilinear_tables_bb(
        h_v, c_len, cols, l_flat, uw_flat, rhs_flat, r_h, r_i, r_k,
    );
    let sumcheck =
        prove_gruen_einsum_mode2_bb(&a_tab, &b_tab, r_h.len(), r_i.len(), r_h, challenges);
    WyGruenProof {
        h_v,
        h_pad,
        c_pad,
        col_pad,
        r_h: r_h.to_vec(),
        r_i: r_i.to_vec(),
        r_k: r_k.to_vec(),
        sumcheck,
    }
}

/// Unchecked-`L` bilinear sumcheck verifier (`L · UW == RHS - UW` WITHOUT `is_strict_lower_tri`):
/// exposed explicitly to demonstrate Falsifier A1b (`Theory/ZkmlDeltaNet.wyChunk_nonStrictLower_falsifier`),
/// where dropping `IsStrictLowerTri L` (`L_{0,0} = -1`) allows distinct `UW_1 != UW_2` to both pass!
pub fn verify_wy_bilinear_unchecked_l(
    h_v: usize,
    c_len: usize,
    cols: usize,
    l_flat: &[u64],
    uw_flat: &[u64],
    rhs_flat: &[u64],
    proof: &WyGruenProof,
) -> bool {
    let (a_tab, b_tab, expected_d) = build_wy_bilinear_tables_bb(
        h_v,
        c_len,
        cols,
        l_flat,
        uw_flat,
        rhs_flat,
        &proof.r_h,
        &proof.r_i,
        &proof.r_k,
    );
    verify_gruen_einsum_mode2(
        expected_d,
        &proof.sumcheck,
        |chals| (mle_eval(&a_tab, chals, P), mle_eval(&b_tab, chals, P)),
        P,
    )
}

/// Deployed fail-closed WY chunk verifier: enforces `is_strict_lower_tri_flat` (`IsStrictLowerTri L`,
/// guaranteeing `det(I + L) = 1` and unique `UW`) AND verifies the flat degree-2 Gruen Mode-2
/// `EinSumcheck` proof of `L · UW = RHS - UW`.
pub fn verify_wy_chunk_gruen(
    h_v: usize,
    c_len: usize,
    cols: usize,
    l_flat: &[u64],
    uw_flat: &[u64],
    rhs_flat: &[u64],
    proof: &WyGruenProof,
) -> bool {
    if !is_strict_lower_tri_flat(l_flat, h_v, c_len) {
        return false;
    }
    verify_wy_bilinear_unchecked_l(h_v, c_len, cols, l_flat, uw_flat, rhs_flat, proof)
}
