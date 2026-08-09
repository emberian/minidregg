//! `[PROVER-sumcheck]` — the sumcheck ENGINE over a multilinear hypercube table,
//! mirroring `Loom/MultilinearExtension.lean`'s `mle`/`roundSum` machinery.
//!
//! Substrate, said out loud: UNVERIFIED COMPUTE following the verified emit seam.
//! The Lean side proved the sumcheck sound (`mle_sumcheck_soundness`, the round
//! chain `roundSum_zero`/`roundSum_succ`/`roundSum_last`, degree via
//! `roundSum_affine`) about ITS objects; this file re-computes the same shapes in
//! Rust so the prover produces the claim the Lean proved sound. There is no formal
//! semantics of Rust, so the agreement is established by CONFORMANCE VECTORS
//! (`prover/testdata/sumcheck_conformance.json`, written by the Lean `#eval` in
//! `Compiler/SumcheckConformance.lean` from the REAL `mle`/`roundSum`) — never
//! called refinement or verification. Agreement on vectors is the whole claim.
//!
//! The mirrored semantics (Loom, `Cube` section):
//! * `chi_eval` = `chiEval b x = ∏ᵢ (if bᵢ then xᵢ else 1 − xᵢ)`;
//! * `mle_eval` = `mle f x = Σ_b f(b)·χ_b(x)` (WHIR Def 4.5's `f̂`);
//! * `round_sum` = `roundSum g r i t = Σ_{b ∈ {0,1}^{m−i−1}} g(r₀,…,r_{i−1}, t, b)`
//!   at `g = mle f` — challenges strictly below `i`, the running variable at `i`,
//!   boolean corners above (entries of `r` at ≥ `i` are never read, the mirror of
//!   `roundSum_congr_prefix`);
//! * `round_poly` = round `i`'s message as its evals `[gᵢ(0), gᵢ(1)]` — degree ≤ 1
//!   for a multilinear `g` (`roundSum_affine`), so two points determine it; the
//!   Lean `roundPoly` carries the same data as coefficients
//!   `C(gᵢ(1)−gᵢ(0))·X + C(gᵢ(0))`.
//!
//! **Index convention** (pinned by the conformance vector): the table `f` has
//! length `2^m` and index bit `i` (LSB-first) is cube coordinate `i` — Lean's
//! `bitsToIdx b = Σᵢ (if bᵢ then 2^i else 0)`. Round `i` binds coordinate `i`.
//!
//! Challenges are CALLER-SUPPLIED (fixed, for the conformance vector); drawing
//! them from a Fiat-Shamir transcript is `[PROVER-fs]`, not this rung. The
//! gate-constraint → hypercube-table encoding (the descriptor's gates as the
//! R1CS-style `Â·B̂−Ĉ` claim of `Assurance/AirSumcheckQuadratic`, degree-2 round
//! polynomials) is the NEXT rung, `[PROVER-sumcheck-gates]` — this file is the
//! degree-≤1 engine it will drive. Perf note: `round_sum` is the LITERAL mirror
//! (O(2^m) MLE evals per point); the standard table-folding optimization arrives
//! only when a rung needs it, and will be conformance-checked against this mirror.

use crate::descriptor::Fp;

pub(crate) fn add_mod(a: Fp, b: Fp, p: u64) -> Fp {
    ((a as u128 + b as u128) % p as u128) as u64
}

pub(crate) fn sub_mod(a: Fp, b: Fp, p: u64) -> Fp {
    ((a as u128 + p as u128 - b as u128 % p as u128) % p as u128) as u64
}

pub(crate) fn mul_mod(a: Fp, b: Fp, p: u64) -> Fp {
    ((a as u128 * b as u128) % p as u128) as u64
}

/// `m` from a table of length `2^m`. Panics on a non-power-of-two length —
/// there is no hypercube it could be a table of.
fn cube_dim(f: &[Fp]) -> usize {
    assert!(
        !f.is_empty() && f.len().is_power_of_two(),
        "table length {} is not a power of two",
        f.len()
    );
    f.len().trailing_zeros() as usize
}

/// Mirror of `chiEval`: `χ_b(x) = ∏ᵢ (if bᵢ then xᵢ else 1 − xᵢ)`, with corner
/// `b` given as an index (bit `i` = coordinate `i`).
pub fn chi_eval(b: usize, point: &[Fp], p: u64) -> Fp {
    point.iter().enumerate().fold(1 % p, |acc, (i, &x)| {
        let factor = if (b >> i) & 1 == 1 {
            x % p
        } else {
            sub_mod(1 % p, x, p)
        };
        mul_mod(acc, factor, p)
    })
}

/// Mirror of `mle`: the multilinear extension `f̂(x) = Σ_b f(b)·χ_b(x)` of a
/// hypercube table `f` (length `2^m`) at a point (length `m`) — the literal
/// chi-basis sum, matching the Lean definition shape for shape.
pub fn mle_eval(f: &[Fp], point: &[Fp], p: u64) -> Fp {
    let m = cube_dim(f);
    assert_eq!(
        point.len(),
        m,
        "point dimension {} != table dimension {m}",
        point.len()
    );
    f.iter().enumerate().fold(0, |acc, (b, &v)| {
        add_mod(acc, mul_mod(v % p, chi_eval(b, point, p), p), p)
    })
}

/// Mirror of `roundSum` at `g = mle f`: round `i`'s partial sum
/// `gᵢ(t) = Σ_{b ∈ {0,1}^{m−i−1}} f̂(r₀,…,r_{i−1}, t, b)`. `r` must have length
/// `m`; entries at positions ≥ `i` are never read (`roundSum_congr_prefix`).
pub fn round_sum(f: &[Fp], r: &[Fp], i: usize, t: Fp, p: u64) -> Fp {
    let m = cube_dim(f);
    assert_eq!(
        r.len(),
        m,
        "challenge vector length {} != dimension {m}",
        r.len()
    );
    assert!(i < m, "round index {i} out of range (m = {m})");
    let suffix = m - i - 1;
    let mut point: Vec<Fp> = Vec::with_capacity(m);
    let mut acc = 0;
    for b in 0..1usize << suffix {
        point.clear();
        point.extend_from_slice(&r[..i]);
        point.push(t % p);
        for j in 0..suffix {
            point.push(((b >> j) & 1) as u64);
        }
        acc = add_mod(acc, mle_eval(f, &point, p), p);
    }
    acc
}

/// Round `i`'s polynomial `gᵢ` as its evaluations `[gᵢ(0), gᵢ(1)]` — degree ≤ 1
/// for a multilinear table (`roundSum_affine`), so two points interpolate it.
/// The same data as the Lean `roundPoly`'s coefficients.
pub fn round_poly(f: &[Fp], r: &[Fp], i: usize, p: u64) -> Vec<Fp> {
    vec![round_sum(f, r, i, 0, p), round_sum(f, r, i, 1, p)]
}

/// Evaluate a degree-≤1 round polynomial given as `[g(0), g(1)]` at `t`:
/// the two-point interpolation `(1 − t)·g(0) + t·g(1)` (`roundSum_affine`'s
/// right-hand side).
pub fn eval_affine(evals: &[Fp], t: Fp, p: u64) -> Fp {
    assert_eq!(
        evals.len(),
        2,
        "degree-<=1 round polynomial has exactly 2 evals"
    );
    add_mod(
        mul_mod(sub_mod(1 % p, t, p), evals[0], p),
        mul_mod(t % p, evals[1], p),
        p,
    )
}

/// The full sumcheck transcript for the claim `Σ_b f(b)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumcheckProof {
    /// The claimed total `H = Σ_b f(b)` (honest prover: the true sum).
    pub claim: Fp,
    /// Per round `i`, the message `gᵢ` as `[gᵢ(0), gᵢ(1)]`.
    pub rounds: Vec<Vec<Fp>>,
    /// The challenges `rᵢ` folded in after each round — caller-supplied here
    /// (fixed for conformance); Fiat-Shamir drawing is `[PROVER-fs]`.
    pub challenges: Vec<Fp>,
}

/// The honest sumcheck prover: claim `Σ_b f(b)`, then per round the message
/// `gᵢ = [gᵢ(0), gᵢ(1)]` with challenge `rᵢ` folded in. By construction the
/// transcript satisfies the Lean-proved chain: `g₀(0)+g₀(1) = claim`
/// (`roundSum_zero` + `mle_hypercube_sum`), `g_{k+1}(0)+g_{k+1}(1) = g_k(r_k)`
/// (`roundSum_succ`), and `g_{m−1}(r_{m−1}) = f̂(r)` (`roundSum_last`) — the
/// tests EXERCISE these identities, they do not prove them.
pub fn prove_sumcheck(f: &[Fp], challenges: &[Fp], p: u64) -> SumcheckProof {
    let m = cube_dim(f);
    assert_eq!(
        challenges.len(),
        m,
        "need one challenge per round (m = {m})"
    );
    assert!(
        challenges.iter().all(|&r| r < p),
        "challenges must be canonical mod p"
    );
    let claim = f.iter().fold(0, |acc, &v| add_mod(acc, v % p, p));
    let rounds = (0..m).map(|i| round_poly(f, challenges, i, p)).collect();
    SumcheckProof {
        claim,
        rounds,
        challenges: challenges.to_vec(),
    }
}

/// The sumcheck verifier, mirroring `SumcheckAccepts`: every round's boolean
/// check `gᵢ(0)+gᵢ(1) = running` against the folded chain (`scChain`), then the
/// terminal oracle check `running = f̂(r)` with `f̂` supplied as an oracle (in the
/// deployed protocol, an opening of the committed table; here, typically
/// `|pt| mle_eval(f, pt, p)`). Conservative reject on any shape or canonicity
/// violation. Runs; does not verify in the formal sense — no Rust semantics.
pub fn verify_sumcheck(proof: &SumcheckProof, f_oracle: impl Fn(&[Fp]) -> Fp, p: u64) -> bool {
    if proof.rounds.len() != proof.challenges.len() {
        return false;
    }
    if proof.claim >= p || proof.challenges.iter().any(|&r| r >= p) {
        return false;
    }
    let mut running = proof.claim;
    for (g, &r) in proof.rounds.iter().zip(proof.challenges.iter()) {
        if g.len() != 2 || g.iter().any(|&v| v >= p) {
            return false;
        }
        // The boolean check: gᵢ(0) + gᵢ(1) = scChain value (claim, then folds).
        if add_mod(g[0], g[1], p) != running {
            return false;
        }
        // The fold: next chain value is gᵢ(rᵢ).
        running = eval_affine(g, r, p);
    }
    // The terminal oracle check: the folded claim equals f̂ at the challenge
    // point (`scChain_mleHonest_final`'s target).
    running == f_oracle(&proof.challenges)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `Loom/MultilinearExtension.lean`'s `MLEExample` over F₅: the AND table
    /// `[0,0,0,1]` (bit i = coordinate i; AND is 1 only at index 3 = corner
    /// (1,1)). The asserted values are KERNEL-DECIDED in the Lean file
    /// (`mle_and_agrees`, `mle_and_offcube`, `roundSum_and_chain0/1/final`);
    /// reproducing them here is a cross-check on vectors, not a proof.
    const F_AND: [Fp; 4] = [0, 0, 0, 1];
    const P5: u64 = 5;

    #[test]
    fn mle_agrees_on_corners_and_gate() {
        // mle_and_agrees: f̂ interpolates the table at all four corners.
        for b in 0..4usize {
            let corner = vec![(b & 1) as u64, ((b >> 1) & 1) as u64];
            assert_eq!(mle_eval(&F_AND, &corner, P5), F_AND[b], "corner {b}");
        }
    }

    #[test]
    fn mle_and_offcube_matches_lean_decided_value() {
        // mle_and_offcube: f̂_AND(2,3) = 2·3 = 1 in F₅ — a genuine extension.
        assert_eq!(mle_eval(&F_AND, &[2, 3], P5), 1);
    }

    #[test]
    fn round_chain_matches_lean_decided_examples() {
        // roundSum_and_chain0: g₀(0) + g₀(1) = Σ_b fAnd(b) = 1 (r = [2,0]).
        let r = [2, 0];
        let g0 = round_poly(&F_AND, &r, 0, P5);
        assert_eq!(add_mod(g0[0], g0[1], P5), 1);
        // roundSum_and_chain1: g₁(0) + g₁(1) = g₀(2).
        let g1 = round_poly(&F_AND, &r, 1, P5);
        assert_eq!(add_mod(g1[0], g1[1], P5), round_sum(&F_AND, &r, 0, 2, P5));
        // roundSum_and_final: g₁(3) = f̂_AND(2,3) at r = [2,3].
        let r = [2, 3];
        assert_eq!(round_sum(&F_AND, &r, 1, 3, P5), mle_eval(&F_AND, &r, P5));
    }

    /// An asymmetric m = 3 table over F₉₇ — bit-order-sensitive, unlike AND.
    const F97: [Fp; 8] = [3, 1, 4, 1, 5, 9, 2, 6];
    const P97: u64 = 97;

    #[test]
    fn mle_agrees_on_corners_m3() {
        for b in 0..8usize {
            let corner: Vec<Fp> = (0..3).map(|i| ((b >> i) & 1) as u64).collect();
            assert_eq!(mle_eval(&F97, &corner, P97), F97[b], "corner {b}");
        }
    }

    #[test]
    fn round_sum_is_affine_in_t() {
        // roundSum_affine, exercised: gᵢ(t) = (1−t)·gᵢ(0) + t·gᵢ(1) off {0,1}.
        let r = [17, 42, 63];
        for i in 0..3 {
            let g = round_poly(&F97, &r, i, P97);
            for t in [2, 5, 96] {
                assert_eq!(
                    round_sum(&F97, &r, i, t, P97),
                    eval_affine(&g, t, P97),
                    "round {i} t {t}"
                );
            }
        }
    }

    #[test]
    fn round_sum_ignores_challenges_at_and_above_i() {
        // roundSum_congr_prefix, exercised: round i reads r only below i.
        let r1 = [17, 42, 63];
        let r2 = [17, 42, 11];
        assert_eq!(
            round_sum(&F97, &r1, 2, 7, P97),
            round_sum(&F97, &r2, 2, 7, P97)
        );
        let r3 = [17, 5, 90];
        assert_eq!(
            round_sum(&F97, &r1, 1, 7, P97),
            round_sum(&F97, &r3, 1, 7, P97)
        );
    }

    #[test]
    fn prove_verify_round_trip() {
        let chal = [17, 42, 63];
        let proof = prove_sumcheck(&F97, &chal, P97);
        assert_eq!(proof.claim, F97.iter().sum::<u64>() % P97);
        assert!(verify_sumcheck(&proof, |pt| mle_eval(&F97, pt, P97), P97));
    }

    #[test]
    fn chain_identities_hold_on_honest_transcript() {
        // The Lean-proved chain, exercised on the honest transcript:
        // roundSum_zero, roundSum_succ, roundSum_last.
        let chal = [17, 42, 63];
        let proof = prove_sumcheck(&F97, &chal, P97);
        assert_eq!(
            add_mod(proof.rounds[0][0], proof.rounds[0][1], P97),
            proof.claim
        );
        for k in 0..2 {
            assert_eq!(
                add_mod(proof.rounds[k + 1][0], proof.rounds[k + 1][1], P97),
                eval_affine(&proof.rounds[k], chal[k], P97),
                "g_{}(0)+g_{}(1) = g_{}(r_{})",
                k + 1,
                k + 1,
                k,
                k
            );
        }
        assert_eq!(
            eval_affine(&proof.rounds[2], chal[2], P97),
            mle_eval(&F97, &chal, P97)
        );
    }

    #[test]
    fn zero_rounds_table() {
        // m = 0: the table is one value, the claim is that value, no rounds.
        let proof = prove_sumcheck(&[42], &[], P97);
        assert_eq!(proof.claim, 42);
        assert!(proof.rounds.is_empty());
        assert!(verify_sumcheck(&proof, |pt| mle_eval(&[42], pt, P97), P97));
    }

    #[test]
    fn tampered_round_poly_fails() {
        let chal = [17, 42, 63];
        for i in 0..3 {
            for j in 0..2 {
                let mut proof = prove_sumcheck(&F97, &chal, P97);
                proof.rounds[i][j] = (proof.rounds[i][j] + 1) % P97;
                assert!(
                    !verify_sumcheck(&proof, |pt| mle_eval(&F97, pt, P97), P97),
                    "tampered g_{i}({j}) must fail"
                );
            }
        }
    }

    #[test]
    fn false_claim_fails() {
        let chal = [17, 42, 63];
        let mut proof = prove_sumcheck(&F97, &chal, P97);
        proof.claim = (proof.claim + 1) % P97;
        assert!(!verify_sumcheck(&proof, |pt| mle_eval(&F97, pt, P97), P97));
    }

    #[test]
    fn wrong_oracle_fails() {
        // The transcript is internally consistent but the final oracle check
        // targets a DIFFERENT table's MLE — the terminal comparison has teeth.
        let chal = [17, 42, 63];
        let proof = prove_sumcheck(&F97, &chal, P97);
        let other: [Fp; 8] = [3, 1, 4, 1, 5, 9, 2, 7];
        assert!(!verify_sumcheck(
            &proof,
            |pt| mle_eval(&other, pt, P97),
            P97
        ));
    }

    #[test]
    fn malformed_proof_shapes_rejected() {
        let chal = [17, 42, 63];
        let good = prove_sumcheck(&F97, &chal, P97);
        // Round/challenge count mismatch.
        let mut proof = good.clone();
        proof.rounds.pop();
        assert!(!verify_sumcheck(&proof, |pt| mle_eval(&F97, pt, P97), P97));
        // A round message that is not 2 evals.
        let mut proof = good.clone();
        proof.rounds[1] = vec![1, 2, 3];
        assert!(!verify_sumcheck(&proof, |pt| mle_eval(&F97, pt, P97), P97));
        // Non-canonical value.
        let mut proof = good;
        proof.rounds[0][0] += P97;
        assert!(!verify_sumcheck(&proof, |pt| mle_eval(&F97, pt, P97), P97));
    }
}
