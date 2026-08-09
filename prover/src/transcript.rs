//! `[PROVER-fs]` — the Poseidon2 Fiat-Shamir transcript: absorb the proof
//! stream, squeeze the challenges. The prover made NON-INTERACTIVE — sumcheck
//! round challenges, FRI betas, and query positions are all DRAWN from the
//! transcript, and the verifier RE-DERIVES them from the proof's own commitment
//! stream, taking no challenges from any caller.
//!
//! Substrate, said out loud: UNVERIFIED COMPUTE following the verified emit
//! seam — conformance vectors, not refinement (no formal semantics of Rust).
//! What this file matches in the Lean formalization:
//!
//! * the SPONGE is the duplex chain `Compiler/FsConformance.lean` pins:
//!   absorb = add into wire 0 then permute (so every absorbed element passes
//!   through the perm and the state is a function of the whole absorbed
//!   prefix); squeeze = permute then read wire 0; an `Ext4` challenge = 4
//!   consecutive squeezes; a query = one squeeze reduced mod the domain size.
//!   The permutation is `poseidon::perm` — the `AirHash.permExec` mirror,
//!   itself conformance-pinned. The Rust chain must equal the Lean chain on
//!   the vector `testdata/fs_conformance.json` (tests/fs_conformance.rs);
//! * the SHAPE is `Loom/FiatShamir.lean`'s `fiatShamir`: challenge `i` is the
//!   oracle read at the transcript PREFIX through round `i` — absorb the
//!   prefix, squeeze the challenge. "The sponge realizes the oracle" is that
//!   file's named idealization [FS-ROM], a deployment-priced modeling step;
//! * the SOUNDNESS is Loom's, not ours: FS-of-RBR knowledge soundness at the
//!   `(t + k)`-query grinding factor is `fsKeystone_proved`
//!   (Loom/FiatShamir.lean), priced deployably by `lightClientGrinding_sound`
//!   (Loom/LightClientGrinding.lean). This file makes the prover RUN
//!   non-interactively in that schedule shape; it proves nothing about it.
//!
//! What the tests establish (and no more): the round trip re-derives the same
//! challenges from the proof alone; TAMPERING any absorbed value (a round
//! commitment, the final word, a sumcheck message) changes the re-derived
//! challenges and the proof rejects — the FS binding, exercised, not proved.
//! Query positions use rejection sampling, so `p mod size != 0` introduces no
//! modulo bias in the ideal-uniform coordinate.  The demo `PermSpec` is still a
//! conformance instantiation — the deployed constant set with its
//! rate/capacity/domain-separation discipline is `[PROVER-poseidon-params]`.
//! Sumcheck challenges
//! are base BabyBear while FRI challenges are `Ext4`; a security budget that
//! treats every challenge as the extension field needs the separate
//! `[PROVER-challenge-field-unification]` bridge.

use crate::descriptor::Fp;
use crate::field4::{Ext4, P, TWO_ADIC_BITS};
use crate::fri_protocol::{fri_verify, FriDescent, FriProof};
use crate::poseidon::{perm, PermSpec};
use crate::sumcheck::{add_mod, prove_sumcheck, round_poly, verify_sumcheck, SumcheckProof};
use crate::wide::Digest;

const FRI_ROOT_DIGEST_TAG: Fp = 0x4652_5254; // "FRRT"

/// The Fiat-Shamir transcript: a Poseidon2 duplex sponge. State starts
/// all-zero; `absorb` mixes each element through the permutation; `squeeze_*`
/// permutes and reads wire 0. The exact chain is pinned by the Lean-authored
/// vector `testdata/fs_conformance.json` (`Compiler/FsConformance.lean`).
#[derive(Debug, Clone)]
pub struct Transcript {
    state: Vec<Fp>,
    spec: PermSpec,
    p: u64,
}

impl Transcript {
    /// A fresh transcript: all-zero state.
    pub fn new(spec: PermSpec, p: u64) -> Transcript {
        assert!(spec.width >= 1, "transcript needs a wire 0");
        Transcript {
            state: vec![0; spec.width],
            spec,
            p,
        }
    }

    /// Absorb: each element is added into wire 0 and mixed by ONE permutation,
    /// so every squeezed challenge depends on the whole absorbed prefix (the
    /// `fiatShamir` prefix-derivation shape).
    pub fn absorb(&mut self, xs: &[Fp]) {
        for &x in xs {
            assert!(x < self.p, "absorb: non-canonical element {x}");
            self.state[0] = add_mod(self.state[0], x, self.p);
            self.state = perm(&self.spec, &self.state, self.p);
        }
    }

    /// Absorb `WDG1 || domain || nine canonical limbs`.
    ///
    /// Callers use distinct domains for distinct protocol objects.  Prover-side
    /// malformed data is a contract violation; verifier paths validate the
    /// digest before calling this method.
    pub fn absorb_digest(&mut self, domain: Fp, digest: &Digest) {
        let encoded = digest
            .encode_with_domain(domain)
            .expect("transcript digest and domain must be canonical");
        self.absorb(&encoded);
    }

    /// Squeeze one base-field challenge: permute, read wire 0. The permuted
    /// state carries over — consecutive squeezes chain.
    pub fn squeeze_challenge(&mut self) -> Fp {
        self.state = perm(&self.spec, &self.state, self.p);
        self.state[0]
    }

    /// Squeeze one BabyBear⁴ challenge: 4 consecutive squeezes, lanes in order.
    pub fn squeeze_ext4(&mut self) -> Ext4 {
        assert_eq!(self.p, P, "Ext4 challenges are BabyBear-hardwired (field4)");
        let c0 = self.squeeze_challenge();
        let c1 = self.squeeze_challenge();
        let c2 = self.squeeze_challenge();
        let c3 = self.squeeze_challenge();
        Ext4 {
            c: [c0, c1, c2, c3],
        }
    }

    /// Squeeze an unbiased ideal-coordinate query in `[0, domain_size)`.
    /// Candidates at or above the largest multiple of `domain_size` below `p`
    /// are rejected and the sponge is squeezed again.  Thus a uniform field
    /// challenge maps exactly uniformly; the concrete sponge assumption remains
    /// `[PROVER-poseidon-params]` / `[FS-ROM]`.
    pub fn squeeze_query(&mut self, domain_size: usize) -> usize {
        assert!(domain_size >= 1, "squeeze_query: empty domain");
        assert!(
            (domain_size as u128) <= self.p as u128,
            "squeeze_query: domain exceeds field cardinality"
        );
        loop {
            let candidate = self.squeeze_challenge();
            if let Some(query) = reduce_query_candidate(candidate, self.p, domain_size) {
                return query;
            }
        }
    }
}

/// One rejection-sampling step, factored so the exact bias boundary has teeth.
fn reduce_query_candidate(candidate: Fp, p: u64, domain_size: usize) -> Option<usize> {
    let size = domain_size as u64;
    debug_assert!(size >= 1 && size <= p && candidate < p);
    let limit = p - p % size;
    (candidate < limit).then_some((candidate % size) as usize)
}

/// The FRI Fiat-Shamir schedule, replayed from PUBLIC data (the commitment
/// stream a proof carries): absorb the instance shape `(n, m, num_queries)`,
/// then per round absorb the level commitment and squeeze its beta — so each
/// beta depends on the commitment chain so far — then absorb the clear final
/// word, then squeeze the query positions. `None` on non-canonical or
/// unusable shape (conservative reject in the verify path).
fn fri_schedule(
    round_commitments: &[Digest],
    final_codeword: &[Ext4],
    num_queries: usize,
    spec: &PermSpec,
    p: u64,
) -> Option<(Vec<Ext4>, Vec<usize>)> {
    let m = round_commitments.len();
    let final_len = final_codeword.len();
    if p != P
        || spec.width < 2
        || spec.validate(p).is_err()
        || m == 0
        || num_queries == 0
        || final_len == 0
        || !final_len.is_power_of_two()
    {
        return None;
    }
    let n = match final_len.checked_shl(m as u32) {
        Some(v) if v.trailing_zeros() <= TWO_ADIC_BITS => v,
        _ => return None,
    };
    if round_commitments.iter().any(|root| !root.is_canonical())
        || final_codeword.iter().any(|v| v.c.iter().any(|&c| c >= p))
        || (num_queries as u64) >= p
    {
        return None;
    }
    let mut tr = Transcript::new(spec.clone(), p);
    tr.absorb(&[n as Fp, m as Fp, num_queries as Fp]);
    let mut betas = Vec::with_capacity(m);
    for root in round_commitments {
        tr.absorb_digest(FRI_ROOT_DIGEST_TAG, root);
        betas.push(tr.squeeze_ext4());
    }
    for v in final_codeword {
        tr.absorb(&v.c);
    }
    let queries = (0..num_queries).map(|_| tr.squeeze_query(n / 2)).collect();
    Some((betas, queries))
}

/// **The non-interactive FRI prover.** Draws the betas and query positions
/// from the transcript — the interleaved schedule is the real FS: level `k`'s
/// commitment is absorbed BEFORE `beta_k` is squeezed, so the prover cannot
/// pick a word after seeing its challenge. The one retained `FriDescent`
/// stores each word and Merkle tree until the query positions are drawn; the
/// proof and openings are assembled from that state without recomputing any
/// fold or commitment. Returns the drawn `(betas, queries)` alongside the
/// proof for callers that want the schedule (the verifier does NOT — it
/// re-derives its own).
pub fn fri_prove_fs(
    codeword: &[Ext4],
    num_rounds: usize,
    num_queries: usize,
    spec: &PermSpec,
    p: u64,
) -> (FriProof, Vec<Ext4>, Vec<usize>) {
    assert_eq!(p, P, "the fold layer is BabyBear-hardwired (field4)");
    let n = codeword.len();
    assert!(num_rounds >= 1, "fri_prove_fs: at least one fold round");
    assert!(num_queries >= 1, "fri_prove_fs: at least one query");
    assert!(
        n.is_power_of_two() && n >= 2,
        "fri_prove_fs: codeword length must be a power of two >= 2"
    );
    assert!(
        n.trailing_zeros() <= TWO_ADIC_BITS,
        "fri_prove_fs: domain exceeds BabyBear 2-adicity"
    );
    assert!(
        (num_rounds as u32) <= n.trailing_zeros(),
        "fri_prove_fs: more rounds than the word can halve"
    );

    let mut tr = Transcript::new(spec.clone(), p);
    tr.absorb(&[n as Fp, num_rounds as Fp, num_queries as Fp]);
    let mut descent = FriDescent::new(codeword);
    let mut betas = Vec::with_capacity(num_rounds);
    for _ in 0..num_rounds {
        let root = descent.commit_current(spec, p);
        tr.absorb_digest(FRI_ROOT_DIGEST_TAG, &root);
        let beta = tr.squeeze_ext4();
        descent.fold_committed(beta);
        betas.push(beta);
    }
    for v in descent.current_word() {
        tr.absorb(&v.c);
    }
    let queries: Vec<usize> = (0..num_queries).map(|_| tr.squeeze_query(n / 2)).collect();

    let proof = descent.finish(&queries);
    // The FS absorb stream IS the proof's public stream. Replay pins that the
    // retained single-pass builder and verifier schedule cannot drift apart.
    debug_assert_eq!(
        fri_schedule(
            &proof.round_commitments,
            &proof.final_codeword,
            num_queries,
            spec,
            p
        ),
        Some((betas.clone(), queries.clone())),
        "the replayed schedule must equal the interleaved draw"
    );
    (proof, betas, queries)
}

/// **The non-interactive FRI verifier.** RE-DERIVES the betas and query
/// positions from the proof's own commitment stream via a fresh transcript —
/// no challenges enter from any caller (the FS check) — then runs the landed
/// `fri_verify` at the re-derived schedule. Tampering any commitment, the
/// final word, or the claimed shape changes the re-derived challenges, so a
/// forged proof must survive queries it did not choose. Conservative reject
/// on shape or canonicity violations. Runs; not verification in the formal
/// sense — the soundness pricing is Loom's (module doc).
pub fn fri_verify_fs(
    proof: &FriProof,
    num_rounds: usize,
    num_queries: usize,
    spec: &PermSpec,
    p: u64,
) -> bool {
    if p != P
        || spec.width < 2
        || spec.validate(p).is_err()
        || num_queries == 0
        || proof.round_commitments.len() != num_rounds
        || proof.query_openings.len() != num_queries
    {
        return false;
    }
    match fri_schedule(
        &proof.round_commitments,
        &proof.final_codeword,
        num_queries,
        spec,
        p,
    ) {
        Some((betas, queries)) => fri_verify(proof, &betas, &queries, spec, p),
        None => false,
    }
}

/// **Demo-only context-free sumcheck FS prover.** Absorbs the shape and claim,
/// then per round absorbs the message `g_i = [g_i(0), g_i(1)]` and squeezes
/// challenge `r_i` — each challenge depends on the transcript prefix through
/// its round, the `fiatShamir` shape. Builds the proof with the ONE builder,
/// `prove_sumcheck`, at the drawn challenges (round messages only read the
/// challenge prefix below their index — `roundSum_congr_prefix`'s mirror — so
/// the interleaved draw and the batch build agree; pinned by the assert).
/// It does not bind a statement or oracle identity; protocol code must seed a
/// surrounding transcript as `protocol.rs` does instead of treating this
/// standalone helper as a complete Fiat--Shamir transform.
pub fn prove_sumcheck_fs(f: &[Fp], spec: &PermSpec, p: u64) -> SumcheckProof {
    assert!(
        !f.is_empty() && f.len().is_power_of_two(),
        "table length {} is not a power of two",
        f.len()
    );
    let m = f.len().trailing_zeros() as usize;
    let claim = f.iter().fold(0, |acc, &v| add_mod(acc, v % p, p));
    let mut tr = Transcript::new(spec.clone(), p);
    tr.absorb(&[m as Fp, claim]);
    let mut challenges = vec![0u64; m];
    let mut rounds = Vec::with_capacity(m);
    for i in 0..m {
        let g = round_poly(f, &challenges, i, p);
        tr.absorb(&g);
        challenges[i] = tr.squeeze_challenge();
        rounds.push(g);
    }
    let proof = prove_sumcheck(f, &challenges, p);
    assert_eq!(proof.claim, claim, "FS absorbed claim must be the proof's");
    assert_eq!(
        proof.rounds, rounds,
        "FS absorbed messages must be the proof's"
    );
    proof
}

/// **Demo-only context-free sumcheck FS verifier.** RE-DERIVES challenges
/// from the proof's claim + round messages via a fresh transcript and runs the
/// landed `verify_sumcheck` at them.  The carried vector is checked for exact
/// canonical equality with that derivation, but never drives verification.
/// Like the standalone prover above this helper does not bind statement/oracle
/// identity and is not a complete protocol transform.
pub fn verify_sumcheck_fs(
    proof: &SumcheckProof,
    f_oracle: impl Fn(&[Fp]) -> Fp,
    spec: &PermSpec,
    p: u64,
) -> bool {
    let m = proof.rounds.len();
    if spec.width == 0
        || spec.validate(p).is_err()
        || proof.claim >= p
        || (m as u64) >= p
        || proof.challenges.len() != m
    {
        return false;
    }
    let mut tr = Transcript::new(spec.clone(), p);
    tr.absorb(&[m as Fp, proof.claim]);
    let mut derived = Vec::with_capacity(m);
    for g in &proof.rounds {
        if g.len() != 2 || g.iter().any(|&v| v >= p) {
            return false;
        }
        tr.absorb(g);
        derived.push(tr.squeeze_challenge());
    }
    if proof.challenges != derived {
        return false;
    }
    let fs_proof = SumcheckProof {
        claim: proof.claim,
        rounds: proof.rounds.clone(),
        challenges: derived,
    };
    verify_sumcheck(&fs_proof, f_oracle, p)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field4::{bmul, two_adic_generator};
    use crate::poseidon::demo_spec;
    use crate::sumcheck::mle_eval;

    fn prng(seed: &mut u64) -> u64 {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (*seed >> 16) % P
    }

    fn prng_ext(seed: &mut u64) -> Ext4 {
        Ext4 {
            c: [prng(seed), prng(seed), prng(seed), prng(seed)],
        }
    }

    /// An honest RS codeword: `codeword[j] = poly(g^j)` on the order-`2^log_n`
    /// two-adic domain (same helper shape as fri_protocol's tests).
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
    const M: usize = 4; // degree < 16
    const Q: usize = 32;

    /// Determinism + sensitivity of the sponge itself: same absorbs, same
    /// squeezes; ONE changed absorbed element moves the challenge.
    #[test]
    fn transcript_deterministic_and_absorb_sensitive() {
        let spec = demo_spec();
        let mut t1 = Transcript::new(spec.clone(), P);
        let mut t2 = Transcript::new(spec.clone(), P);
        t1.absorb(&[3, 1, 4, 1, 5]);
        t2.absorb(&[3, 1, 4, 1, 5]);
        let c1 = t1.squeeze_challenge();
        assert_eq!(c1, t2.squeeze_challenge(), "same absorbs, same challenge");
        assert_ne!(
            c1,
            t1.squeeze_challenge(),
            "consecutive squeezes chain (state moved)"
        );
        let mut t3 = Transcript::new(spec, P);
        t3.absorb(&[3, 1, 4, 2, 5]);
        assert_ne!(
            c1,
            t3.squeeze_challenge(),
            "one changed element, different challenge"
        );
    }

    #[test]
    fn query_rejection_sampling_boundary_is_exact() {
        // For p=13 and n=5, [0,10) contains exactly two representatives of
        // each query.  The tail {10,11,12} must be resqueezed, not reduced.
        assert_eq!(reduce_query_candidate(0, 13, 5), Some(0));
        assert_eq!(reduce_query_candidate(4, 13, 5), Some(4));
        assert_eq!(reduce_query_candidate(5, 13, 5), Some(0));
        assert_eq!(reduce_query_candidate(9, 13, 5), Some(4));
        assert_eq!(reduce_query_candidate(10, 13, 5), None);
        assert_eq!(reduce_query_candidate(12, 13, 5), None);
    }

    /// prove_fs → verify_fs round-trips on an honest low-degree word: the
    /// verifier re-derives the schedule from the proof alone (no challenges
    /// cross the call), and it equals the prover's draw.
    #[test]
    fn fri_fs_round_trip() {
        use crate::fri_protocol::fri_prove;

        let mut seed = 11u64;
        let coeffs: Vec<Ext4> = (0..1 << M).map(|_| prng_ext(&mut seed)).collect();
        let cw = rs_codeword(&coeffs, LOG_N);
        let spec = demo_spec();
        let (proof, betas, queries) = fri_prove_fs(&cw, M, Q, &spec, P);
        assert!(fri_verify_fs(&proof, M, Q, &spec, P));
        // The re-derived schedule IS the drawn schedule.
        let (b2, q2) =
            fri_schedule(&proof.round_commitments, &proof.final_codeword, Q, &spec, P).unwrap();
        assert_eq!(betas, b2);
        assert_eq!(queries, q2);
        // And the drawn schedule verifies through the interactive verifier too.
        assert!(fri_verify(&proof, &betas, &queries, &spec, P));
        // Single-pass FS assembly is structurally identical to the public
        // caller-supplied-schedule builder at that derived schedule.
        assert_eq!(proof, fri_prove(&cw, &betas, &queries, &spec, P));
    }

    /// The FS binding, non-vacuously: tampering a round commitment changes the
    /// RE-DERIVED challenges (checked directly, not just "it rejects"), and the
    /// tampered proof rejects. You cannot move the transcript without moving
    /// every challenge drawn after the move.
    #[test]
    fn fri_fs_tampered_commitment_rederives_different_challenges_and_rejects() {
        let mut seed = 22u64;
        let coeffs: Vec<Ext4> = (0..1 << M).map(|_| prng_ext(&mut seed)).collect();
        let cw = rs_codeword(&coeffs, LOG_N);
        let spec = demo_spec();
        let (good, betas, queries) = fri_prove_fs(&cw, M, Q, &spec, P);

        let mut bad = good.clone();
        bad.round_commitments[1].limbs[0] = (bad.round_commitments[1].limbs[0] + 1) % P;
        let (bad_betas, bad_queries) =
            fri_schedule(&bad.round_commitments, &bad.final_codeword, Q, &spec, P).unwrap();
        assert_eq!(
            bad_betas[0], betas[0],
            "beta_0 precedes the tampered absorb"
        );
        assert_ne!(
            bad_betas[1..],
            betas[1..],
            "betas after the tampered commitment move"
        );
        assert_ne!(bad_queries, queries, "query positions move too");
        assert!(
            !fri_verify_fs(&bad, M, Q, &spec, P),
            "tampered commitment rejects"
        );
    }

    /// Tampering the CLEAR final word also moves the transcript: the queries
    /// are drawn after it is absorbed, so even a still-constant forged final
    /// word faces re-derived (different) query positions — and rejects.
    #[test]
    fn fri_fs_tampered_final_word_rederives_different_queries_and_rejects() {
        let mut seed = 33u64;
        let coeffs: Vec<Ext4> = (0..1 << M).map(|_| prng_ext(&mut seed)).collect();
        let cw = rs_codeword(&coeffs, LOG_N);
        let spec = demo_spec();
        let (good, _betas, queries) = fri_prove_fs(&cw, M, Q, &spec, P);

        let mut bad = good.clone();
        let forged = Ext4::from_base(7);
        bad.final_codeword = vec![forged; bad.final_codeword.len()]; // still constant
        let (_, bad_queries) =
            fri_schedule(&bad.round_commitments, &bad.final_codeword, Q, &spec, P).unwrap();
        assert_ne!(bad_queries, queries, "queries re-derive differently");
        assert!(
            !fri_verify_fs(&bad, M, Q, &spec, P),
            "forged final word rejects"
        );
    }

    /// Shape gates: wrong round/query counts against the verifier's protocol
    /// parameters reject before any transcript work.
    #[test]
    fn fri_fs_shape_mismatches_rejected() {
        let mut seed = 44u64;
        let coeffs: Vec<Ext4> = (0..1 << M).map(|_| prng_ext(&mut seed)).collect();
        let cw = rs_codeword(&coeffs, LOG_N);
        let spec = demo_spec();
        let (good, _, _) = fri_prove_fs(&cw, M, Q, &spec, P);
        assert!(
            !fri_verify_fs(&good, M - 1, Q, &spec, P),
            "wrong round count"
        );
        assert!(
            !fri_verify_fs(&good, M, Q - 1, &spec, P),
            "wrong query count"
        );
        let mut bad = good.clone();
        bad.query_openings.pop();
        assert!(!fri_verify_fs(&bad, M, Q, &spec, P), "dropped opening");
        let mut empty = good.clone();
        empty.query_openings.clear();
        assert!(!fri_verify_fs(&empty, M, 0, &spec, P), "zero queries");
        assert!(
            fri_schedule(&empty.round_commitments, &empty.final_codeword, 0, &spec, P).is_none()
        );
        let mut malformed_spec = spec.clone();
        malformed_spec.width = 0;
        assert!(!fri_verify_fs(&good, M, Q, &malformed_spec, P));
        let mut bad = good;
        bad.round_commitments[0].limbs[0] = P; // non-canonical
        assert!(
            !fri_verify_fs(&bad, M, Q, &spec, P),
            "non-canonical commitment"
        );
    }

    const FTAB: [Fp; 8] = [3, 1, 4, 1, 5, 9, 2, 6];

    /// Sumcheck FS round trip over the m = 3 table: challenges drawn from the
    /// transcript, re-derived by the verifier, no caller input.
    #[test]
    fn sumcheck_fs_round_trip() {
        let spec = demo_spec();
        let proof = prove_sumcheck_fs(&FTAB, &spec, P);
        assert_eq!(proof.rounds.len(), 3);
        assert!(verify_sumcheck_fs(
            &proof,
            |pt| mle_eval(&FTAB, pt, P),
            &spec,
            P
        ));
        // Determinism: proving again draws the same challenges.
        assert_eq!(proof, prove_sumcheck_fs(&FTAB, &spec, P));
    }

    /// The FS binding on the sumcheck side: tampering a round message changes
    /// every challenge derived at and after it, and the proof rejects.
    #[test]
    fn sumcheck_fs_tampered_message_rejects() {
        let spec = demo_spec();
        let good = prove_sumcheck_fs(&FTAB, &spec, P);
        for i in 0..3 {
            for j in 0..2 {
                let mut bad = good.clone();
                bad.rounds[i][j] = (bad.rounds[i][j] + 1) % P;
                assert!(
                    !verify_sumcheck_fs(&bad, |pt| mle_eval(&FTAB, pt, P), &spec, P),
                    "tampered g_{i}({j}) must reject"
                );
            }
        }
        let mut bad = good;
        bad.claim = (bad.claim + 1) % P;
        assert!(!verify_sumcheck_fs(
            &bad,
            |pt| mle_eval(&FTAB, pt, P),
            &spec,
            P
        ));
    }

    /// The FS verifier draws its OWN challenges and requires the carried
    /// encoding to equal them.  A second challenge vector cannot be a malleable
    /// alternate serialization of the same proof.
    #[test]
    fn sumcheck_fs_rejects_mismatched_carried_challenges() {
        let spec = demo_spec();
        let mut proof = prove_sumcheck_fs(&FTAB, &spec, P);
        proof.challenges[1] = (proof.challenges[1] + 1) % P;
        assert!(!verify_sumcheck_fs(
            &proof,
            |pt| mle_eval(&FTAB, pt, P),
            &spec,
            P
        ));
        assert!(!verify_sumcheck(&proof, |pt| mle_eval(&FTAB, pt, P), P));
    }

    /// Wrong-oracle teeth survive the FS wrapping: an internally consistent
    /// transcript against a different table's MLE still rejects.
    #[test]
    fn sumcheck_fs_wrong_oracle_rejects() {
        let spec = demo_spec();
        let proof = prove_sumcheck_fs(&FTAB, &spec, P);
        let other: [Fp; 8] = [3, 1, 4, 1, 5, 9, 2, 7];
        assert!(!verify_sumcheck_fs(
            &proof,
            |pt| mle_eval(&other, pt, P),
            &spec,
            P
        ));
    }
}
