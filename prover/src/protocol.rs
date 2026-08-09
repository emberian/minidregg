//! `[PROVER-e2e-reference]` — one honest composition of the prover rungs.
//!
//! This module is deliberately called **reference**, not deployed.  It is the
//! first single `prove`/`verify` path through the objects that previously only
//! existed as separate demonstrations:
//!
//! ```text
//! Lean-emitted descriptor -> generated trace -> trace Merkle root
//!   -> Fiat-Shamir gate batching + sumcheck
//!   -> Reed--Solomon encoding of that trace -> Fiat-Shamir FRI
//! ```
//!
//! There is one transcript.  It binds the complete descriptor, public inputs,
//! protocol shape, trace root, sumcheck messages, FRI level commitments, and
//! final FRI word before deriving the challenges that follow each object.  The
//! verifier takes no challenges from the caller and does not trust the
//! convenience challenge vector carried by [`SumcheckProof`].
//!
//! The honest floor is equally important: [`ReferenceProof`] carries the whole
//! trace, and verification recomputes its commitment, gate-defect oracle, and
//! trace-derived Reed--Solomon word.  It is therefore neither succinct nor zero
//! knowledge.  The full recomputation closes today's missing selector/opening
//! plumbing without pretending that plumbing exists.  Replacing the clear trace
//! with committed wire openings and a factored quadratic terminal oracle is the
//! named residual `[PROVER-e2e-succinct-openings]`.  Hash binding and Fiat--Shamir
//! security still rest on `[COMMIT-CR]`, `[FS-ROM]`, and the not-yet-deployed
//! `[PROVER-poseidon-params]`.  Runtime roots now use nine canonical BabyBear
//! limbs (`[PROVER-digest-width]`), but width alone is not a collision-resistance
//! result.  The current Lean `AirMembership` / `AirHash` recursive gadgets still
//! expose scalar roots; making them consume this format is the explicit
//! `[AIR-wide-digest]` residual.  Because this reference proof carries the full
//! trace, verification also evaluates `descriptor_holds` exactly; its base-field
//! gate sumcheck is a transcript/conformance exercise, not the only soundness
//! tooth.  A future succinct path must instead deploy extension-field batching
//! or price the mixed fields (`[PROVER-challenge-field-unification]`).  This Rust
//! remains unverified compute.

use crate::commit::commit_trace;
use crate::descriptor::{Descriptor, Fp, GateOp, Wire};
use crate::field4::{bmul, two_adic_generator, Ext4, P, TWO_ADIC_BITS};
use crate::fri;
use crate::fri_protocol::{commit_word, fri_prove, fri_verify, FriProof};
use crate::gate_claim::{
    batch_defect_table, gate_cube_dim, gate_defect_table, prove_gates, verify_gates,
};
use crate::poseidon::PermSpec;
use crate::sumcheck::{add_mod, mle_eval, round_poly, SumcheckProof};
use crate::trace::{descriptor_holds, generate_trace};
use crate::transcript::Transcript;
use crate::wide::Digest;

/// Protocol parameters that are not derived from the descriptor.
///
/// The number of FRI rounds is derived from the trace length: enough rounds to
/// reduce a polynomial with the trace as its coefficient vector to a constant.
/// `fri_log_blowup` controls the evaluation-domain blowup and `fri_queries` the
/// number of transcript-derived spot checks.  This structure does not attach a
/// security label to either value; parameter pricing lives in `Assurance/`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReferenceConfig {
    pub fri_log_blowup: u32,
    pub fri_queries: usize,
}

impl Default for ReferenceConfig {
    fn default() -> Self {
        ReferenceConfig {
            fri_log_blowup: 2,
            fri_queries: 32,
        }
    }
}

/// A self-contained reference proof.
///
/// `trace` is intentionally explicit.  It is the honest temporary bridge from
/// the descriptor gate claim to the low-degree claim, not a witness-hiding
/// encoding.  `trace_root` is absorbed before any gate challenge.  The first FRI
/// commitment is additionally checked against the deterministic RS encoding of
/// this trace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReferenceProof {
    pub trace: Vec<Fp>,
    pub trace_root: Digest,
    pub gate_sumcheck: SumcheckProof,
    pub fri: FriProof,
}

// Three canonical field elements spelling "MINI", "DREG", "E2E2".
const DOMAIN_TAG: [Fp; 3] = [0x4d49_4e49, 0x4452_4547, 0x4532_4532];
const FIELD_BABYBEAR_TAG: Fp = 1;
const TRACE_TAG: Fp = 2;
const GATE_TAG: Fp = 3;
const FRI_TAG: Fp = 4;
const FINAL_TAG: Fp = 5;

fn wire_defined(w: &Wire, defined: &[bool]) -> bool {
    match *w {
        Wire::Const(_) => true,
        Wire::Wire(i) => defined.get(i as usize).copied().unwrap_or(false),
    }
}

/// `Descriptor::validate` checks bounds but not the emission-order invariant
/// that `generate_trace` requires.  Check that invariant here so the public API
/// returns an error rather than reaching a trace-generation assertion.
fn validate_reference_instance(
    d: &Descriptor,
    public_inputs: &[Fp],
    config: ReferenceConfig,
    spec: &PermSpec,
) -> Result<(u32, u32, usize), String> {
    d.validate()?;
    spec.validate(P)?;
    if spec.width < 2 {
        return Err(
            "reference protocol needs permutation width >= 2 for Merkle compression".into(),
        );
    }
    if d.p != P {
        return Err(format!(
            "reference FRI is BabyBear-hardwired: descriptor modulus {} != {P}",
            d.p
        ));
    }
    if d.n_wires == 0 {
        return Err("reference protocol cannot commit an empty trace".into());
    }
    if public_inputs.len() != d.n_public as usize {
        return Err(format!(
            "public input length {} != nPublic {}",
            public_inputs.len(),
            d.n_public
        ));
    }
    if public_inputs.iter().any(|&x| x >= P) {
        return Err("public inputs must be canonical BabyBear elements".into());
    }
    if d.n_wires as u64 >= P
        || d.gates.len() as u64 >= P
        || d.zeros.len() as u64 >= P
        || config.fri_queries as u64 >= P
    {
        return Err("instance counts must fit in one canonical transcript element".into());
    }
    if config.fri_queries == 0 {
        return Err("reference protocol requires at least one FRI query".into());
    }

    let mut defined = vec![false; d.n_wires as usize];
    defined[..d.n_vars as usize].fill(true);
    for (i, gate) in d.gates.iter().enumerate() {
        if !wire_defined(&gate.a, &defined) || !wire_defined(&gate.b, &defined) {
            return Err(format!("gate {i} reads a wire before it is defined"));
        }
        let out = gate.out as usize;
        if defined[out] {
            return Err(format!("gate {i} redefines wire {out}"));
        }
        defined[out] = true;
    }
    if defined.iter().any(|&is_defined| !is_defined) {
        return Err("descriptor leaves at least one trace wire undefined".into());
    }

    let trace_len = d.n_wires as usize;
    let coeff_bits = (usize::BITS - (trace_len - 1).leading_zeros()).max(1);
    let log_n = coeff_bits
        .checked_add(config.fri_log_blowup)
        .ok_or_else(|| "FRI domain exponent overflow".to_string())?;
    if log_n > TWO_ADIC_BITS {
        return Err(format!(
            "FRI domain 2^{log_n} exceeds BabyBear 2-adicity 2^{TWO_ADIC_BITS}"
        ));
    }
    let n = 1usize << log_n;
    Ok((coeff_bits, log_n, n))
}

fn absorb_wire(tr: &mut Transcript, w: &Wire) {
    match *w {
        Wire::Const(c) => tr.absorb(&[0, c]),
        Wire::Wire(i) => tr.absorb(&[1, i as Fp]),
    }
}

/// Bind the entire statement and protocol shape before any witness-dependent
/// challenge.  BabyBear is represented by a protocol tag because the modulus
/// itself is `0` as a BabyBear field element and cannot be absorbed canonically.
fn absorb_instance(
    tr: &mut Transcript,
    d: &Descriptor,
    public_inputs: &[Fp],
    config: ReferenceConfig,
    fri_rounds: u32,
    log_n: u32,
    n: usize,
) {
    tr.absorb(&DOMAIN_TAG);
    tr.absorb(&[
        FIELD_BABYBEAR_TAG,
        d.n_public as Fp,
        d.n_vars as Fp,
        d.n_wires as Fp,
        d.gates.len() as Fp,
        d.zeros.len() as Fp,
    ]);
    for gate in &d.gates {
        tr.absorb(&[match gate.op {
            GateOp::Add => 0,
            GateOp::Mul => 1,
        }]);
        absorb_wire(tr, &gate.a);
        absorb_wire(tr, &gate.b);
        tr.absorb(&[gate.out as Fp]);
    }
    for zero in &d.zeros {
        absorb_wire(tr, zero);
    }
    tr.absorb(public_inputs);
    tr.absorb(&[
        d.n_wires as Fp,
        fri_rounds as Fp,
        config.fri_log_blowup as Fp,
        config.fri_queries as Fp,
        log_n as Fp,
        n as Fp,
    ]);
}

fn trace_rs_codeword(trace: &[Fp], log_n: u32) -> Vec<Ext4> {
    let n = 1usize << log_n;
    let g = two_adic_generator(log_n);
    let coeffs: Vec<Ext4> = trace.iter().copied().map(Ext4::from_base).collect();
    let mut out = Vec::with_capacity(n);
    let mut x = 1;
    for _ in 0..n {
        let mut acc = Ext4::ZERO;
        for &coefficient in coeffs.iter().rev() {
            acc = acc.base_mul(x).add(coefficient);
        }
        out.push(acc);
        x = bmul(x, g);
    }
    out
}

fn prove_gate_phase(d: &Descriptor, trace: &[Fp], tr: &mut Transcript) -> SumcheckProof {
    let m = gate_cube_dim(d);
    tr.absorb(&[GATE_TAG, m as Fp]);
    let gamma = tr.squeeze_challenge();
    let table = batch_defect_table(&gate_defect_table(d, trace), gamma, P);
    let claim = table.iter().fold(0, |acc, &v| add_mod(acc, v, P));
    tr.absorb(&[claim]);

    let mut challenges = vec![0; m];
    let mut rounds = Vec::with_capacity(m);
    for i in 0..m {
        let round = round_poly(&table, &challenges, i, P);
        tr.absorb(&round);
        challenges[i] = tr.squeeze_challenge();
        rounds.push(round);
    }
    let proof = prove_gates(d, trace, gamma, &challenges);
    assert_eq!(
        proof.claim, claim,
        "gate claim absorbed into the transcript must match"
    );
    assert_eq!(
        proof.rounds, rounds,
        "interleaved gate messages must match prove_gates"
    );
    proof
}

fn verify_gate_phase(
    d: &Descriptor,
    trace: &[Fp],
    proof: &SumcheckProof,
    tr: &mut Transcript,
) -> bool {
    let m = gate_cube_dim(d);
    if proof.rounds.len() != m || proof.claim >= P {
        return false;
    }
    tr.absorb(&[GATE_TAG, m as Fp]);
    let gamma = tr.squeeze_challenge();
    let table = batch_defect_table(&gate_defect_table(d, trace), gamma, P);
    tr.absorb(&[proof.claim]);

    let mut challenges = Vec::with_capacity(m);
    for round in &proof.rounds {
        if round.len() != 2 || round.iter().any(|&v| v >= P) {
            return false;
        }
        tr.absorb(round);
        challenges.push(tr.squeeze_challenge());
    }
    if proof.challenges != challenges {
        return false;
    }
    let replay = SumcheckProof {
        claim: proof.claim,
        rounds: proof.rounds.clone(),
        challenges,
    };
    verify_gates(&replay, |point| mle_eval(&table, point, P), P)
}

fn prove_fri_phase(
    codeword: &[Ext4],
    rounds: usize,
    queries: usize,
    tr: &mut Transcript,
    spec: &PermSpec,
) -> FriProof {
    tr.absorb(&[FRI_TAG, codeword.len() as Fp, rounds as Fp, queries as Fp]);
    let mut word = codeword.to_vec();
    let mut roots = Vec::with_capacity(rounds);
    let mut betas = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let (root, _) = commit_word(spec, &word, P);
        tr.absorb_digest(FRI_TAG, &root);
        let beta = tr.squeeze_ext4();
        roots.push(root);
        betas.push(beta);
        word = fri::fold(&word, beta, 1);
    }
    tr.absorb(&[FINAL_TAG, word.len() as Fp]);
    for value in &word {
        tr.absorb(&value.c);
    }
    let positions: Vec<usize> = (0..queries)
        .map(|_| tr.squeeze_query(codeword.len() / 2))
        .collect();
    let proof = fri_prove(codeword, &betas, &positions, spec, P);
    assert_eq!(
        proof.round_commitments, roots,
        "absorbed FRI roots must match the proof"
    );
    assert_eq!(
        proof.final_codeword, word,
        "absorbed FRI final word must match the proof"
    );
    proof
}

fn verify_fri_phase(
    codeword: &[Ext4],
    rounds: usize,
    queries: usize,
    proof: &FriProof,
    tr: &mut Transcript,
    spec: &PermSpec,
) -> bool {
    let expected_final_len = codeword.len() >> rounds;
    if proof.round_commitments.len() != rounds
        || proof.query_openings.len() != queries
        || proof.final_codeword.len() != expected_final_len
        || proof
            .round_commitments
            .iter()
            .any(|root| !root.is_canonical())
        || proof
            .final_codeword
            .iter()
            .any(|v| v.c.iter().any(|&c| c >= P))
    {
        return false;
    }
    // This is the explicit, O(n) bridge from the clear trace to the FRI claim.
    // Succinct replacement: [PROVER-e2e-succinct-openings].
    let (expected_root, _) = commit_word(spec, codeword, P);
    if proof.round_commitments.first().copied() != Some(expected_root) {
        return false;
    }

    tr.absorb(&[FRI_TAG, codeword.len() as Fp, rounds as Fp, queries as Fp]);
    let mut betas = Vec::with_capacity(rounds);
    for root in &proof.round_commitments {
        tr.absorb_digest(FRI_TAG, root);
        betas.push(tr.squeeze_ext4());
    }
    tr.absorb(&[FINAL_TAG, proof.final_codeword.len() as Fp]);
    for value in &proof.final_codeword {
        tr.absorb(&value.c);
    }
    let positions: Vec<usize> = (0..queries)
        .map(|_| tr.squeeze_query(codeword.len() / 2))
        .collect();
    fri_verify(proof, &betas, &positions, spec, P)
}

/// Build the single reference proof for a satisfying assignment.
///
/// `vars` contains the public prefix followed by the private witness, exactly as
/// in [`generate_trace`].  An unsatisfied assignment is refused instead of
/// producing a transcript whose gate claim is nonzero.
pub fn reference_prove(
    d: &Descriptor,
    vars: &[Fp],
    config: ReferenceConfig,
    spec: &PermSpec,
) -> Result<ReferenceProof, String> {
    // Validate the nested public/variable split before slicing `vars`; the
    // reference API rejects malformed descriptors instead of panicking on them.
    d.validate()?;
    if vars.len() != d.n_vars as usize {
        return Err(format!(
            "variable length {} != nVars {}",
            vars.len(),
            d.n_vars
        ));
    }
    if vars.iter().any(|&x| x >= P) {
        return Err("variables must be canonical BabyBear elements".into());
    }
    let public_inputs = &vars[..d.n_public as usize];
    let (fri_rounds, log_n, n) = validate_reference_instance(d, public_inputs, config, spec)?;
    let trace = generate_trace(d, vars);
    if !descriptor_holds(d, &trace) {
        return Err("assignment does not satisfy the emitted descriptor".into());
    }
    let (trace_root, _) = commit_trace(spec, &trace, P);
    let mut transcript = Transcript::new(spec.clone(), P);
    absorb_instance(
        &mut transcript,
        d,
        public_inputs,
        config,
        fri_rounds,
        log_n,
        n,
    );
    transcript.absorb_digest(TRACE_TAG, &trace_root);

    let gate_sumcheck = prove_gate_phase(d, &trace, &mut transcript);
    let codeword = trace_rs_codeword(&trace, log_n);
    let fri = prove_fri_phase(
        &codeword,
        fri_rounds as usize,
        config.fri_queries,
        &mut transcript,
        spec,
    );
    Ok(ReferenceProof {
        trace,
        trace_root,
        gate_sumcheck,
        fri,
    })
}

/// Verify the single reference proof against a descriptor and its public input.
///
/// Challenges are replayed from one fresh transcript.  Malformed inputs reject;
/// no proof-carried challenge is trusted.  This verifier is intentionally O(the
/// whole trace + whole RS word), as documented at the module boundary.
pub fn reference_verify(
    d: &Descriptor,
    public_inputs: &[Fp],
    proof: &ReferenceProof,
    config: ReferenceConfig,
    spec: &PermSpec,
) -> bool {
    let (fri_rounds, log_n, n) = match validate_reference_instance(d, public_inputs, config, spec) {
        Ok(shape) => shape,
        Err(_) => return false,
    };
    if proof.trace.len() != d.n_wires as usize
        || proof.trace.iter().any(|&x| x >= P)
        || proof.trace[..d.n_public as usize] != *public_inputs
        || !proof.trace_root.is_canonical()
        || !descriptor_holds(d, &proof.trace)
    {
        return false;
    }
    let (expected_trace_root, _) = commit_trace(spec, &proof.trace, P);
    if expected_trace_root != proof.trace_root {
        return false;
    }

    let mut transcript = Transcript::new(spec.clone(), P);
    absorb_instance(
        &mut transcript,
        d,
        public_inputs,
        config,
        fri_rounds,
        log_n,
        n,
    );
    transcript.absorb_digest(TRACE_TAG, &proof.trace_root);
    if !verify_gate_phase(d, &proof.trace, &proof.gate_sumcheck, &mut transcript) {
        return false;
    }

    let codeword = trace_rs_codeword(&proof.trace, log_n);
    verify_fri_phase(
        &codeword,
        fri_rounds as usize,
        config.fri_queries,
        &proof.fri,
        &mut transcript,
        spec,
    )
}
