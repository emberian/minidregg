//! `[PROVER-fri]` — the FRI low-degree-test PROTOCOL around the landed fold:
//! commit → fold rounds → query spot-checks → final constant check.
//!
//! Substrate, said out loud: UNVERIFIED COMPUTE following the verified emit
//! seam. Conformance vectors and running tests, NOT refinement — there is no
//! formal semantics of Rust. What this file matches, piece by piece, in
//! `Loom/Proximity.lean` (the verified LDT skeleton):
//!
//! * the prover's descent IS `FoldingTower.word`: round `k` folds the level-`k`
//!   word 2-to-1 at challenge `betas[k]` (`word_succ`: `word (n+1) = fold
//!   (data n) (word n) (αs n)`), computed by the LANDED fold — `fri::fold` /
//!   the GPU kernel, whose per-pair algebra is vector-conformant to Loom's
//!   `fold D f α` (`Compiler/FriConformance`);
//! * the final check IS the `deg m = 1` base check: the level-`m` word must be
//!   CONSTANT (`mem_reedSolomonCode_one_iff` — "membership in `RS[dom, 1]` is
//!   exactly the word is constant"), so an honest input must be a degree-<`2^m`
//!   codeword (`proximity_complete` is the completeness this realizes);
//! * the per-query round-consistency check IS the fold formula the AIR gadget
//!   arithmetizes (`Compiler/FriQueryVerifierAir` check (2), `friFoldVal`):
//!   `next = (lo + hi)·half + β·(lo − hi)·tw` with `tw = 1/(2x)` — identical
//!   to `fri::fold_once`'s per-pair algebra (`fold_pair_matches_fold_once`
//!   pins it), i.e. Loom's `fold_sq` at `f(x) = lo`, `f(−x) = hi`.
//!
//! Honest scope, matching Loom's own limits: `Proximity.lean`'s verifier reads
//! WHOLE level words (claim resolution) and its module doc names the
//! oracle/Merkle query phase as NOT modeled (`[DEC-open]`-adjacent). This file
//! supplies exactly that deployed layer — Merkle-bound spot checks instead of
//! whole words — so the spot-check soundness (the `t = λ/−log(1−δ)` repetition
//! pricing, Merkle binding under `[COMMIT-CR]`) is INHERITED RESIDUAL here, not
//! covered by `proximity_sound`. The tests show a far word is rejected and that
//! the fold-consistency + Merkle checks catch a cheating final word; they do
//! not price the error.
//!
//! Commitment layout: the Merkle layer (`commit.rs`) commits base-`Fp` leaves,
//! so each `Ext4` element is first squeezed to one digest by chaining its four
//! lanes through the `poseidon` permutation (same no-domain-tag caveat as
//! `commit.rs` — the discipline travels with `[PROVER-poseidon-params]` /
//! `[COMMIT-CR]`). One commitment per fold level `0..m`; the level-`m` word
//! travels IN THE CLEAR (it must be constant — sending it is the standard FRI
//! final-polynomial move), bound to the chain by the last consistency check.
//!
//! Challenges (`betas`) and query positions are CALLER-SUPPLIED: drawing them
//! from the Poseidon2 transcript, in the schedule `lightClientGrinding_sound`
//! prices, is `[PROVER-fs]`, not this rung.

use crate::commit::{commit_trace, open, verify_open, MerkleTree};
use crate::descriptor::Fp;
use crate::field4::{binv, bmul, bpow, two_adic_generator, Ext4, HALF, P, TWO_ADIC_BITS};
use crate::fri;
use crate::gpu::GpuFold;
use crate::poseidon::{perm, PermSpec};

/// One query's opened pair at one fold level: `lo = f_k(x)`, `hi = f_k(−x)`
/// (natural-order positions `q_k` and `q_k + n_k/2`), each with its Merkle
/// authentication path against that level's commitment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoundOpening {
    pub lo: Ext4,
    pub hi: Ext4,
    pub lo_path: Vec<Fp>,
    pub hi_path: Vec<Fp>,
}

/// One query's openings across all `m` fold levels.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QueryOpening {
    pub rounds: Vec<RoundOpening>,
}

/// The FRI proof: one Merkle root per fold level `0..m`, the final (claimed
/// constant) level-`m` word in the clear, and the per-query openings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FriProof {
    pub round_commitments: Vec<Fp>,
    pub final_codeword: Vec<Ext4>,
    pub query_openings: Vec<QueryOpening>,
}

/// 2-to-1 sponge step `perm([a, b, 0, …])[0]` (same shape as `commit.rs`).
fn compress2(spec: &PermSpec, a: Fp, b: Fp, p: u64) -> Fp {
    assert!(spec.width >= 2, "ext digest needs width >= 2");
    let mut st = vec![0u64; spec.width];
    st[0] = a;
    st[1] = b;
    perm(spec, &st, p)[0]
}

/// Squeeze an `Ext4` element to one base-field digest by chaining its lanes:
/// the Merkle leaf the commitment binds.
pub fn ext_digest(spec: &PermSpec, v: &Ext4, p: u64) -> Fp {
    let d = compress2(spec, v.c[0], v.c[1], p);
    let d = compress2(spec, d, v.c[2], p);
    compress2(spec, d, v.c[3], p)
}

/// Commit one fold level: per-element digests, then the `commit.rs` Merkle
/// tree over them (level lengths are powers of two — no padding in play).
fn commit_word(spec: &PermSpec, word: &[Ext4], p: u64) -> (Fp, MerkleTree) {
    let digests: Vec<Fp> = word.iter().map(|v| ext_digest(spec, v, p)).collect();
    commit_trace(spec, &digests, p)
}

/// The per-pair fold — EXACTLY `fri::fold_once`'s algebra at one position
/// (pinned by `fold_pair_matches_fold_once`), which is the formula
/// `Compiler/FriQueryVerifierAir`'s `friFoldVal` arithmetizes and Loom's
/// `fold_sq` proves well-defined: `(lo + hi)/2 + β·(lo − hi)·(1/(2x))`.
pub fn fold_pair(lo: Ext4, hi: Ext4, beta: Ext4, twiddle: u64) -> Ext4 {
    lo.add(hi).halve().add(lo.sub(hi).mul(beta).base_mul(twiddle))
}

/// The level twiddle at one position, computed directly:
/// `1/2 · g^{−j}` for `g` the order-`2^log_n` generator — pointwise equal to
/// `fri::halve_inv_powers(log_n)[j]` (pinned by `level_twiddle_matches_table`).
pub fn level_twiddle(log_n: u32, j: usize) -> u64 {
    bmul(HALF, bpow(binv(two_adic_generator(log_n)), j as u64))
}

fn canonical(v: &Ext4) -> bool {
    v.c.iter().all(|&c| c < P)
}

/// **The FRI prover.** Commit the codeword, fold round-by-round at the
/// caller-supplied challenges (one β per 2-to-1 round — Loom's tower schedule),
/// committing each level; collect the final word in the clear and, per query
/// `q < n/2`, the opened `(lo, hi)` pairs with Merkle paths at every level
/// (query positions telescope: `q_k = q mod n_k/2`).
///
/// The fold runs on the GPU when an adapter exists (one reused [`GpuFold`]
/// context — `fold_auto`'s exact semantics without rebuilding the pipeline per
/// round), CPU `fri::fold` otherwise. Panics on contract violations (length not
/// a power of two, too many rounds, query out of range) — prover-side inputs.
pub fn fri_prove(
    codeword: &[Ext4],
    betas: &[Ext4],
    queries: &[usize],
    spec: &PermSpec,
    p: u64,
) -> FriProof {
    assert_eq!(p, P, "the fold layer is BabyBear-hardwired (field4)");
    let n = codeword.len();
    let m = betas.len();
    assert!(m >= 1, "fri_prove: at least one fold round");
    assert!(n.is_power_of_two() && n >= 2, "fri_prove: codeword length must be a power of two >= 2");
    let log_n = n.trailing_zeros();
    assert!(log_n <= TWO_ADIC_BITS, "fri_prove: domain exceeds BabyBear 2-adicity");
    assert!((m as u32) <= log_n, "fri_prove: more rounds than the word can halve");
    for &q in queries {
        assert!(q < n / 2, "fri_prove: query {q} out of range (< {})", n / 2);
    }

    // The descent: words[k] is FoldingTower.word at level k.
    let gpu = GpuFold::new().ok();
    let mut words: Vec<Vec<Ext4>> = vec![codeword.to_vec()];
    for &beta in betas {
        let prev = words.last().unwrap();
        let next = match &gpu {
            Some(g) => g.fold(prev, beta, 1).unwrap_or_else(|_| fri::fold(prev, beta, 1)),
            None => fri::fold(prev, beta, 1),
        };
        words.push(next);
    }

    let committed: Vec<(Fp, MerkleTree)> =
        words[..m].iter().map(|w| commit_word(spec, w, p)).collect();
    let query_openings = queries
        .iter()
        .map(|&q| QueryOpening {
            rounds: (0..m)
                .map(|k| {
                    let word = &words[k];
                    let half = word.len() / 2;
                    let q_k = q % half;
                    let tree = &committed[k].1;
                    RoundOpening {
                        lo: word[q_k],
                        hi: word[q_k + half],
                        lo_path: open(tree, q_k),
                        hi_path: open(tree, q_k + half),
                    }
                })
                .collect(),
        })
        .collect();

    FriProof {
        round_commitments: committed.iter().map(|(r, _)| *r).collect(),
        final_codeword: words[m].clone(),
        query_openings,
    }
}

/// **The FRI verifier.** For each query: verify both opened values' Merkle
/// paths against that level's commitment (`verify_open`), then the FOLD
/// CONSISTENCY `folded = fold_pair(lo, hi, β_k, tw)` against the next level's
/// opened value (lo or hi side, by position) and, at the last round, against
/// the clear final word; finally the base low-degree check — the final word is
/// CONSTANT (`mem_reedSolomonCode_one_iff`, the `deg m = 1` base of Loom's
/// `proximityTest`). Conservative reject on any shape, range, or canonicity
/// violation. Runs; does not verify in the formal sense — no Rust semantics,
/// and the spot-check error is unpriced here (see the module doc).
pub fn fri_verify(
    proof: &FriProof,
    betas: &[Ext4],
    queries: &[usize],
    spec: &PermSpec,
    p: u64,
) -> bool {
    if p != P {
        return false;
    }
    let m = betas.len();
    let final_len = proof.final_codeword.len();
    if m == 0
        || (m as u32) > TWO_ADIC_BITS
        || proof.round_commitments.len() != m
        || proof.query_openings.len() != queries.len()
        || final_len == 0
        || !final_len.is_power_of_two()
    {
        return false;
    }
    let n = match final_len.checked_shl(m as u32) {
        Some(v) if v.trailing_zeros() <= TWO_ADIC_BITS => v,
        _ => return false,
    };
    if !betas.iter().all(canonical) || !proof.final_codeword.iter().all(canonical) {
        return false;
    }

    // The base check: RS[dom, 1] membership is literally "the word is constant".
    let c0 = proof.final_codeword[0];
    if !proof.final_codeword.iter().all(|&v| v == c0) {
        return false;
    }

    for (&q, opening) in queries.iter().zip(proof.query_openings.iter()) {
        if q >= n / 2 || opening.rounds.len() != m {
            return false;
        }
        for k in 0..m {
            let n_k = final_len << (m - k);
            let half_k = n_k / 2;
            let q_k = q % half_k;
            let ro = &opening.rounds[k];
            if !(canonical(&ro.lo) && canonical(&ro.hi)) {
                return false;
            }
            // Merkle binding of the opened pair to level k's commitment.
            let root = proof.round_commitments[k];
            if !verify_open(root, q_k, ext_digest(spec, &ro.lo, p), &ro.lo_path, spec, p)
                || !verify_open(root, q_k + half_k, ext_digest(spec, &ro.hi, p), &ro.hi_path, spec, p)
            {
                return false;
            }
            // Fold consistency: the folded value must be what level k+1 holds
            // at position q_k — the next opened pair's lo/hi side, or the clear
            // final word at the last round.
            let folded = fold_pair(ro.lo, ro.hi, betas[k], level_twiddle(n_k.trailing_zeros(), q_k));
            let expected = if k + 1 < m {
                let next = &opening.rounds[k + 1];
                if q_k < half_k / 2 { next.lo } else { next.hi }
            } else {
                proof.final_codeword[q_k]
            };
            if folded != expected {
                return false;
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fri::{fold_once, halve_inv_powers};
    use crate::poseidon::demo_spec;

    fn prng(seed: &mut u64) -> u64 {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (*seed >> 16) % P
    }

    fn prng_ext(seed: &mut u64) -> Ext4 {
        Ext4 { c: [prng(seed), prng(seed), prng(seed), prng(seed)] }
    }

    fn prng_word(seed: &mut u64, n: usize) -> Vec<Ext4> {
        (0..n).map(|_| prng_ext(seed)).collect()
    }

    /// An HONEST Reed–Solomon codeword: evaluate a polynomial (Ext4
    /// coefficients, degree < coeffs.len()) on the order-`2^log_n` two-adic
    /// domain, natural order — `codeword[j] = p(g^j)`.
    fn rs_codeword(coeffs: &[Ext4], log_n: u32) -> Vec<Ext4> {
        let n = 1usize << log_n;
        let g = two_adic_generator(log_n);
        let mut out = Vec::with_capacity(n);
        let mut x = 1u64;
        for _ in 0..n {
            let mut acc = Ext4::ZERO;
            for &c in coeffs.iter().rev() {
                acc = acc.base_mul(x).add(c);
            }
            out.push(acc);
            x = bmul(x, g);
        }
        out
    }

    const LOG_N: u32 = 8; // n = 256
    const M: usize = 4; // degree < 16, blowup 16

    fn setup(seed: &mut u64) -> (Vec<Ext4>, Vec<usize>) {
        let betas: Vec<Ext4> = (0..M).map(|_| prng_ext(seed)).collect();
        // 32 spread query positions in [0, n/2).
        let queries: Vec<usize> = (0..32).map(|_| (prng(seed) as usize) % 128).collect();
        (betas, queries)
    }

    /// The verifier's per-pair formula IS the landed fold: `fold_pair` at the
    /// level twiddles reproduces `fri::fold_once` position by position, and
    /// `level_twiddle` reproduces the twiddle table.
    #[test]
    fn fold_pair_matches_fold_once() {
        let mut seed = 21u64;
        let cw = prng_word(&mut seed, 16);
        let beta = prng_ext(&mut seed);
        let folded = fold_once(&cw, beta);
        let tw = halve_inv_powers(4);
        for j in 0..8 {
            assert_eq!(fold_pair(cw[j], cw[j + 8], beta, tw[j]), folded[j], "position {j}");
        }
    }

    #[test]
    fn level_twiddle_matches_table() {
        for log_n in [1u32, 3, 4, 8] {
            let table = halve_inv_powers(log_n);
            for (j, &t) in table.iter().enumerate() {
                assert_eq!(level_twiddle(log_n, j), t, "log_n {log_n} position {j}");
            }
        }
    }

    /// Completeness on an honest low-degree word — `proximity_complete`'s
    /// shape, exercised: a real RS codeword proves and verifies.
    #[test]
    fn honest_low_degree_word_accepts() {
        let mut seed = 101u64;
        let coeffs = prng_word(&mut seed, 1 << M); // degree < 16
        let cw = rs_codeword(&coeffs, LOG_N);
        let (betas, queries) = setup(&mut seed);
        let spec = demo_spec();
        let proof = fri_prove(&cw, &betas, &queries, &spec, P);
        // The descent really lands on a constant (fold_preserves_code, iterated).
        assert_eq!(proof.final_codeword.len(), 1 << (LOG_N as usize - M));
        assert!(proof.final_codeword.iter().all(|&v| v == proof.final_codeword[0]));
        assert!(fri_verify(&proof, &betas, &queries, &spec, P));
    }

    /// A NON-low-degree word is rejected: the honest descent of a random word
    /// does not land on a constant, so the final check fires.
    #[test]
    fn random_word_rejected_at_final_check() {
        let mut seed = 202u64;
        let cw = prng_word(&mut seed, 1 << LOG_N);
        let (betas, queries) = setup(&mut seed);
        let spec = demo_spec();
        let proof = fri_prove(&cw, &betas, &queries, &spec, P);
        assert!(!proof.final_codeword.iter().all(|&v| v == proof.final_codeword[0]));
        assert!(!fri_verify(&proof, &betas, &queries, &spec, P));
    }

    /// A CHEATING prover that swaps in a constant final word (the only way past
    /// the final check) is caught by fold consistency at the queried positions:
    /// the committed descent does not fold to that constant. This is the
    /// query layer's load-bearing check — Merkle-bound openings + the fold
    /// formula — with 32 queries; the miss probability is high per query here
    /// and unpriced (see module doc), the test exercises the mechanism.
    #[test]
    fn cheating_constant_final_word_rejected_by_queries() {
        let mut seed = 303u64;
        let cw = prng_word(&mut seed, 1 << LOG_N);
        let (betas, queries) = setup(&mut seed);
        let spec = demo_spec();
        let mut proof = fri_prove(&cw, &betas, &queries, &spec, P);
        proof.final_codeword = vec![Ext4::from_base(7); 1 << (LOG_N as usize - M)];
        assert!(!fri_verify(&proof, &betas, &queries, &spec, P));
    }

    #[test]
    fn tampered_opened_value_rejected() {
        let mut seed = 404u64;
        let coeffs = prng_word(&mut seed, 1 << M);
        let cw = rs_codeword(&coeffs, LOG_N);
        let (betas, queries) = setup(&mut seed);
        let spec = demo_spec();
        let good = fri_prove(&cw, &betas, &queries, &spec, P);
        assert!(fri_verify(&good, &betas, &queries, &spec, P));
        for (round, lo_side) in [(0, true), (2, false), (M - 1, true)] {
            let mut proof = good.clone();
            let ro = &mut proof.query_openings[5].rounds[round];
            let v = if lo_side { &mut ro.lo } else { &mut ro.hi };
            v.c[0] = (v.c[0] + 1) % P;
            assert!(
                !fri_verify(&proof, &betas, &queries, &spec, P),
                "tampered {} at round {round} must fail",
                if lo_side { "lo" } else { "hi" }
            );
        }
    }

    #[test]
    fn tampered_merkle_path_and_commitment_rejected() {
        let mut seed = 505u64;
        let coeffs = prng_word(&mut seed, 1 << M);
        let cw = rs_codeword(&coeffs, LOG_N);
        let (betas, queries) = setup(&mut seed);
        let spec = demo_spec();
        let good = fri_prove(&cw, &betas, &queries, &spec, P);

        let mut proof = good.clone();
        proof.query_openings[3].rounds[1].lo_path[0] =
            (proof.query_openings[3].rounds[1].lo_path[0] + 1) % P;
        assert!(!fri_verify(&proof, &betas, &queries, &spec, P), "tampered path");

        let mut proof = good.clone();
        proof.round_commitments[2] = (proof.round_commitments[2] + 1) % P;
        assert!(!fri_verify(&proof, &betas, &queries, &spec, P), "tampered commitment");

        let mut proof = good;
        proof.final_codeword[3].c[1] = (proof.final_codeword[3].c[1] + 1) % P;
        assert!(!fri_verify(&proof, &betas, &queries, &spec, P), "tampered final word");
    }

    /// Wrong challenges reject: the fold consistency is β-sensitive.
    #[test]
    fn wrong_beta_rejected() {
        let mut seed = 606u64;
        let coeffs = prng_word(&mut seed, 1 << M);
        let cw = rs_codeword(&coeffs, LOG_N);
        let (betas, queries) = setup(&mut seed);
        let spec = demo_spec();
        let proof = fri_prove(&cw, &betas, &queries, &spec, P);
        let mut bad = betas.clone();
        bad[1].c[0] = (bad[1].c[0] + 1) % P;
        assert!(!fri_verify(&proof, &bad, &queries, &spec, P));
    }

    /// Openings are position-bound: verifying against shifted query positions
    /// fails (the Merkle index enters the path fold — `commit.rs`'s
    /// wrong-index behavior, inherited).
    #[test]
    fn mismatched_query_positions_rejected() {
        let mut seed = 707u64;
        let coeffs = prng_word(&mut seed, 1 << M);
        let cw = rs_codeword(&coeffs, LOG_N);
        let (betas, queries) = setup(&mut seed);
        let spec = demo_spec();
        let proof = fri_prove(&cw, &betas, &queries, &spec, P);
        let shifted: Vec<usize> = queries.iter().map(|&q| (q + 1) % 128).collect();
        assert!(!fri_verify(&proof, &betas, &shifted, &spec, P));
    }

    #[test]
    fn malformed_shapes_rejected() {
        let mut seed = 808u64;
        let coeffs = prng_word(&mut seed, 1 << M);
        let cw = rs_codeword(&coeffs, LOG_N);
        let (betas, queries) = setup(&mut seed);
        let spec = demo_spec();
        let good = fri_prove(&cw, &betas, &queries, &spec, P);

        // Query out of the level-0 half range.
        let mut q2 = queries.clone();
        q2[0] = 128;
        assert!(!fri_verify(&good, &betas, &q2, &spec, P));

        // Openings/queries count mismatch.
        let mut proof = good.clone();
        proof.query_openings.pop();
        assert!(!fri_verify(&proof, &betas, &queries, &spec, P));

        // A dropped round inside one opening.
        let mut proof = good.clone();
        proof.query_openings[0].rounds.pop();
        assert!(!fri_verify(&proof, &betas, &queries, &spec, P));

        // Commitment count / round count mismatch.
        let mut proof = good.clone();
        proof.round_commitments.pop();
        assert!(!fri_verify(&proof, &betas, &queries, &spec, P));

        // Non-canonical opened lane.
        let mut proof = good;
        proof.query_openings[0].rounds[0].lo.c[0] += P;
        assert!(!fri_verify(&proof, &betas, &queries, &spec, P));

        // Zero rounds is not a protocol.
        assert!(!fri_verify(
            &fri_prove(&cw, &betas, &queries, &spec, P),
            &[],
            &queries,
            &spec,
            P
        ));
    }
}
