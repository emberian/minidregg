//! Arbitrary linear-functional retirement for a private GF(2^64) table.
//!
//! For a private LSB Boolean table `a`, public weights `w`, and public `y`, a
//! degree-two inner-product sumcheck reduces
//!
//! ```text
//! y = sum_x MLE(a, x) * MLE(w, x)
//! ```
//!
//! to one product at the transcript point.  The private MLE is committed by
//! [`AdditiveMleTerminalProverState`] in the exact Mobius/reversed-LCH order:
//! each sumcheck challenge binds the next LSB variable and is immediately
//! followed by the next additive root.  Sampled paths are derived only after
//! all round messages, challenges, roots, and the terminal claim are fixed.
//! Proofs contain no private table or full evaluation word.
//! `log_blowup = b` is verifier-visible: the `N` Mobius coefficients are
//! encoded on `M = N * 2^b` points, yielding distance `1 - N/M`.
//!
//! Characteristic two needs a genuine third interpolation point for quadratic
//! messages: integer `2` is not the scalar two, but the canonical non-Boolean
//! tower element with bits `0b10`.  Messages are `(g(0), g(1), g(theta))`.
//!
//! Honest residuals remain explicit:
//! * `[TRACE-LINEAR-GF2-PROXIMITY]`: compose the landed additive coherent
//!   sampled-FRI theorem with reversed-LCH provenance at explicit rate
//!   `N/M = 2^-log_blowup`.
//! * `[TRACE-LINEAR-GF2-CR]`: instantiate collision resistance for BinaryShake
//!   Merkle commitments.
//! * `[TRACE-LINEAR-GF2-ROM]`: analyze the cSHAKE Fiat--Shamir transcript and
//!   with-replacement query schedule in the ROM/XOF game.
//! * `[TRACE-LINEAR-GF2-RUST-UNVERIFIED]`: the Rust Mobius transform is
//!   unverified compute; Lean owns the emitted control and verifier
//!   characteristic-two sumcheck, additive folds, and transcript to Lean.

use core::fmt;

use crate::{
    additive_fri_sampled::tower_leaf_payload,
    additive_mle_terminal::{
        verify_additive_mle_terminal, AdditiveMleTerminalError, AdditiveMleTerminalProof,
        AdditiveMleTerminalProverState, AdditiveMleTerminalStatement,
        AdditiveMleTerminalTranscript,
    },
    binary_hash::{BinaryRoot, BinaryShake256V1, HashSuite},
    binary_tower::{TowerElem, TowerError, MAX_LEVEL},
    binary_transcript::{BinaryShake256Transcript, TranscriptSuite},
};

pub const TRACE_LINEAR_GF2_PROTOCOL_LABEL: &[u8] = b"minidregg/trace-linear-gf2/v2";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceLinearGf2Statement {
    pub table_root: BinaryRoot,
    pub log_blowup: u32,
    pub basis: Vec<TowerElem>,
    pub offset: TowerElem,
    pub claimed_value: TowerElem,
    pub num_queries: usize,
}

/// `(g_i(0), g_i(1), g_i(theta))`, where `theta.bits() == 2`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuadraticSumcheckGf2Proof {
    pub rounds: Vec<[TowerElem; 3]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceLinearGf2Proof {
    pub sumcheck: QuadraticSumcheckGf2Proof,
    pub table_mle_statement: AdditiveMleTerminalStatement,
    pub table_mle_proof: AdditiveMleTerminalProof,
}

/// Metadata obtained from the same successful transcript replay as proof
/// verification. Consumers can authenticate related initial words without
/// duplicating or approximating the trace-linear query schedule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceLinearGf2Verification {
    pub initial_pair_indices: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TraceLinearGf2Error {
    InvalidShape,
    InvalidDomain,
    FieldLevelMismatch,
    ClaimedValueMismatch,
    InvalidProofShape,
    Mle(AdditiveMleTerminalError),
    Tower(TowerError),
}

impl From<AdditiveMleTerminalError> for TraceLinearGf2Error {
    fn from(value: AdditiveMleTerminalError) -> Self {
        Self::Mle(value)
    }
}

impl From<TowerError> for TraceLinearGf2Error {
    fn from(value: TowerError) -> Self {
        Self::Tower(value)
    }
}

impl fmt::Display for TraceLinearGf2Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidShape => write!(
                f,
                "binary linear tables must have equal power-of-two length at least two"
            ),
            Self::InvalidDomain => write!(f, "invalid binary linear additive domain"),
            Self::FieldLevelMismatch => {
                write!(
                    f,
                    "binary linear values must be canonical GF(2^64) elements"
                )
            }
            Self::ClaimedValueMismatch => {
                write!(
                    f,
                    "claimed value is not the private/public GF(2^64) dot product"
                )
            }
            Self::InvalidProofShape => write!(f, "invalid binary linear proof shape"),
            Self::Mle(error) => error.fmt(f),
            Self::Tower(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for TraceLinearGf2Error {}

/// Clear claim constructor. Addition is XOR in the binary tower.
pub fn linear_functional_value_gf2(
    table: &[TowerElem],
    weights: &[TowerElem],
) -> Result<TowerElem, TraceLinearGf2Error> {
    validate_tables(table, weights)?;
    let mut value = TowerElem::zero(MAX_LEVEL)?;
    for (&table_value, &weight) in table.iter().zip(weights) {
        value = value.add(table_value.mul(weight)?)?;
    }
    Ok(value)
}

/// Commit the private table before a containing receipt draws outer challenges.
/// The returned state must remain paired with this exact transcript.
pub fn commit_trace_linear_gf2_table(
    table: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
    transcript: &mut BinaryShake256Transcript,
) -> Result<AdditiveMleTerminalProverState<BinaryShake256V1>, TraceLinearGf2Error> {
    commit_trace_linear_gf2_table_with_blowup(table, basis, offset, 0, transcript)
}

pub fn commit_trace_linear_gf2_table_with_blowup(
    table: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
    log_blowup: u32,
    transcript: &mut BinaryShake256Transcript,
) -> Result<AdditiveMleTerminalProverState<BinaryShake256V1>, TraceLinearGf2Error> {
    validate_single_table(table)?;
    validate_domain_shape(
        table.len(),
        basis,
        offset,
        TowerElem::zero(MAX_LEVEL)?,
        1,
        log_blowup,
    )?;
    Ok(AdditiveMleTerminalProverState::commit_initial_with_blowup(
        table,
        basis,
        offset,
        log_blowup,
        BinaryShake256V1,
        transcript,
    )?)
}

/// Standalone proof in a fresh binary cSHAKE transcript.
pub fn prove_trace_linear_gf2(
    table: &[TowerElem],
    weights: &[TowerElem],
    claimed_value: TowerElem,
    basis: &[TowerElem],
    offset: TowerElem,
    num_queries: usize,
) -> Result<(TraceLinearGf2Statement, TraceLinearGf2Proof), TraceLinearGf2Error> {
    prove_trace_linear_gf2_with_blowup(table, weights, claimed_value, basis, offset, 0, num_queries)
}

pub fn prove_trace_linear_gf2_with_blowup(
    table: &[TowerElem],
    weights: &[TowerElem],
    claimed_value: TowerElem,
    basis: &[TowerElem],
    offset: TowerElem,
    log_blowup: u32,
    num_queries: usize,
) -> Result<(TraceLinearGf2Statement, TraceLinearGf2Proof), TraceLinearGf2Error> {
    let mut transcript = BinaryShake256Transcript::new(TRACE_LINEAR_GF2_PROTOCOL_LABEL);
    prove_trace_linear_gf2_with_transcript_and_blowup(
        table,
        weights,
        claimed_value,
        basis,
        offset,
        log_blowup,
        num_queries,
        &mut transcript,
    )
}

/// Commit and prove inside a caller-owned binary transcript.
pub fn prove_trace_linear_gf2_with_transcript(
    table: &[TowerElem],
    weights: &[TowerElem],
    claimed_value: TowerElem,
    basis: &[TowerElem],
    offset: TowerElem,
    num_queries: usize,
    transcript: &mut BinaryShake256Transcript,
) -> Result<(TraceLinearGf2Statement, TraceLinearGf2Proof), TraceLinearGf2Error> {
    prove_trace_linear_gf2_with_transcript_and_blowup(
        table,
        weights,
        claimed_value,
        basis,
        offset,
        0,
        num_queries,
        transcript,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn prove_trace_linear_gf2_with_transcript_and_blowup(
    table: &[TowerElem],
    weights: &[TowerElem],
    claimed_value: TowerElem,
    basis: &[TowerElem],
    offset: TowerElem,
    log_blowup: u32,
    num_queries: usize,
    transcript: &mut BinaryShake256Transcript,
) -> Result<(TraceLinearGf2Statement, TraceLinearGf2Proof), TraceLinearGf2Error> {
    validate_private_shape(
        table,
        weights,
        basis,
        offset,
        claimed_value,
        num_queries,
        log_blowup,
    )?;
    if linear_functional_value_gf2(table, weights)? != claimed_value {
        return Err(TraceLinearGf2Error::ClaimedValueMismatch);
    }
    let state = AdditiveMleTerminalProverState::commit_initial_with_blowup(
        table,
        basis,
        offset,
        log_blowup,
        BinaryShake256V1,
        &mut *transcript,
    )?;
    prove_trace_linear_gf2_from_state_with_blowup(
        table,
        weights,
        claimed_value,
        basis,
        offset,
        log_blowup,
        num_queries,
        state,
        transcript,
    )
}

/// Continue from an initial table root already observed in `transcript`.
///
/// This is the receipt-composition seam: a caller may commit once, absorb or
/// sample outer protocol data, and only then retire a derived linear functional.
#[allow(clippy::too_many_arguments)]
pub fn prove_trace_linear_gf2_from_state(
    table: &[TowerElem],
    weights: &[TowerElem],
    claimed_value: TowerElem,
    basis: &[TowerElem],
    offset: TowerElem,
    num_queries: usize,
    table_mle: AdditiveMleTerminalProverState<BinaryShake256V1>,
    transcript: &mut BinaryShake256Transcript,
) -> Result<(TraceLinearGf2Statement, TraceLinearGf2Proof), TraceLinearGf2Error> {
    prove_trace_linear_gf2_from_state_with_blowup(
        table,
        weights,
        claimed_value,
        basis,
        offset,
        0,
        num_queries,
        table_mle,
        transcript,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn prove_trace_linear_gf2_from_state_with_blowup(
    table: &[TowerElem],
    weights: &[TowerElem],
    claimed_value: TowerElem,
    basis: &[TowerElem],
    offset: TowerElem,
    log_blowup: u32,
    num_queries: usize,
    mut table_mle: AdditiveMleTerminalProverState<BinaryShake256V1>,
    transcript: &mut BinaryShake256Transcript,
) -> Result<(TraceLinearGf2Statement, TraceLinearGf2Proof), TraceLinearGf2Error> {
    let rounds = validate_private_shape(
        table,
        weights,
        basis,
        offset,
        claimed_value,
        num_queries,
        log_blowup,
    )?;
    if linear_functional_value_gf2(table, weights)? != claimed_value {
        return Err(TraceLinearGf2Error::ClaimedValueMismatch);
    }
    let table_root = table_mle.input_root();
    absorb_linear_statement(transcript, weights, claimed_value, num_queries, log_blowup);

    let mut sumcheck = QuadraticInnerProductGf2Prover::new(table, weights)?;
    let mut messages = Vec::with_capacity(rounds);
    for round in 0..rounds {
        let message = sumcheck.message()?;
        absorb_round(transcript, round, &message);
        let challenge = sample_challenge(transcript);
        sumcheck.bind(challenge)?;
        table_mle.bind(challenge, &mut *transcript)?;
        messages.push(message);
    }
    let challenges = sumcheck.challenges.clone();
    let (table_terminal, weights_terminal) = sumcheck.finish()?;
    let running_terminal = verify_quadratic_chain(claimed_value, &messages, &challenges)?;
    if running_terminal != table_terminal.mul(weights_terminal)? {
        return Err(TraceLinearGf2Error::InvalidProofShape);
    }
    let (table_mle_statement, table_mle_proof) =
        table_mle.finish(table_terminal, num_queries, &mut *transcript)?;
    if table_mle_statement.input_root != table_root
        || table_mle_statement.basis != basis
        || table_mle_statement.offset != offset
        || table_mle_statement.log_blowup != log_blowup
    {
        return Err(TraceLinearGf2Error::InvalidProofShape);
    }
    Ok((
        TraceLinearGf2Statement {
            table_root,
            log_blowup,
            basis: basis.to_vec(),
            offset,
            claimed_value,
            num_queries,
        },
        TraceLinearGf2Proof {
            sumcheck: QuadraticSumcheckGf2Proof { rounds: messages },
            table_mle_statement,
            table_mle_proof,
        },
    ))
}

/// Standalone verification with public weights and no private table.
pub fn verify_trace_linear_gf2(
    statement: &TraceLinearGf2Statement,
    weights: &[TowerElem],
    proof: &TraceLinearGf2Proof,
) -> Result<bool, TraceLinearGf2Error> {
    let mut transcript = BinaryShake256Transcript::new(TRACE_LINEAR_GF2_PROTOCOL_LABEL);
    observe_trace_linear_gf2_initial(statement, &mut transcript)?;
    verify_trace_linear_gf2_after_initial(statement, weights, proof, &mut transcript)
}

/// Observe exactly the initial additive root for caller-owned verification.
pub fn observe_trace_linear_gf2_initial(
    statement: &TraceLinearGf2Statement,
    transcript: &mut BinaryShake256Transcript,
) -> Result<(), TraceLinearGf2Error> {
    validate_statement_shape(statement)?;
    <BinaryShake256Transcript as AdditiveMleTerminalTranscript>::observe_initial(
        transcript,
        <BinaryShake256V1 as HashSuite>::SUITE_ID,
        &statement.basis,
        statement.offset,
        statement.log_blowup,
        &statement.table_root,
    )
    .expect("BinaryShake transcript observation is infallible");
    Ok(())
}

/// Verify after a containing protocol already observed the exact initial root.
pub fn verify_trace_linear_gf2_after_initial(
    statement: &TraceLinearGf2Statement,
    weights: &[TowerElem],
    proof: &TraceLinearGf2Proof,
    transcript: &mut BinaryShake256Transcript,
) -> Result<bool, TraceLinearGf2Error> {
    Ok(
        verify_trace_linear_gf2_after_initial_with_queries(statement, weights, proof, transcript)?
            .is_some(),
    )
}

/// Verify and return the transcript-derived round-zero pair indices.
pub fn verify_trace_linear_gf2_after_initial_with_queries(
    statement: &TraceLinearGf2Statement,
    weights: &[TowerElem],
    proof: &TraceLinearGf2Proof,
    transcript: &mut BinaryShake256Transcript,
) -> Result<Option<TraceLinearGf2Verification>, TraceLinearGf2Error> {
    let table_len = validate_public_shape(statement, weights)?;
    let rounds = table_len.trailing_zeros() as usize;
    let domain_len = checked_domain_len(statement.basis.len())?;
    if proof.sumcheck.rounds.len() != rounds
        || proof.table_mle_statement.input_root != statement.table_root
        || proof.table_mle_statement.basis != statement.basis
        || proof.table_mle_statement.offset != statement.offset
        || proof.table_mle_statement.log_blowup != statement.log_blowup
        || proof.table_mle_statement.num_queries != statement.num_queries
        || proof.table_mle_proof.roots.len() != rounds + 1
        || proof.table_mle_proof.roots.first().copied() != Some(statement.table_root)
    {
        return Ok(None);
    }

    absorb_linear_statement(
        transcript,
        weights,
        statement.claimed_value,
        statement.num_queries,
        statement.log_blowup,
    );
    let mut challenges = Vec::with_capacity(rounds);
    let mut next_word_len = domain_len / 2;
    for (round, message) in proof.sumcheck.rounds.iter().enumerate() {
        absorb_round(transcript, round, message);
        let challenge = sample_challenge(transcript);
        challenges.push(challenge);
        <BinaryShake256Transcript as AdditiveMleTerminalTranscript>::observe_binding(
            transcript,
            round,
            challenge,
            next_word_len,
            &proof.table_mle_proof.roots[round + 1],
        )
        .expect("BinaryShake transcript observation is infallible");
        next_word_len /= 2;
    }
    let running = match verify_quadratic_chain(
        statement.claimed_value,
        &proof.sumcheck.rounds,
        &challenges,
    ) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let weights_terminal = evaluate_public_mle(weights, &challenges)?;
    if running
        != proof
            .table_mle_statement
            .claimed_terminal
            .mul(weights_terminal)?
    {
        return Ok(None);
    }

    <BinaryShake256Transcript as AdditiveMleTerminalTranscript>::observe_final(
        transcript,
        proof.table_mle_statement.claimed_terminal,
        statement.num_queries,
    )
    .expect("BinaryShake transcript observation is infallible");
    let pair_count = domain_len / 2;
    let mut query_indices = Vec::with_capacity(statement.num_queries);
    for query in 0..statement.num_queries {
        query_indices.push(
            <BinaryShake256Transcript as AdditiveMleTerminalTranscript>::draw_query_index(
                transcript, query, pair_count,
            )
            .expect("BinaryShake query draw is infallible"),
        );
    }
    let mut fixed = FixedQueryTranscript::new(query_indices.clone(), pair_count);
    if !verify_additive_mle_terminal(
        &proof.table_mle_statement,
        &challenges,
        &proof.table_mle_proof,
        &BinaryShake256V1,
        &mut fixed,
    ) {
        return Ok(None);
    }
    Ok(Some(TraceLinearGf2Verification {
        initial_pair_indices: query_indices,
    }))
}

fn absorb_linear_statement(
    transcript: &mut BinaryShake256Transcript,
    weights: &[TowerElem],
    claimed_value: TowerElem,
    num_queries: usize,
    log_blowup: u32,
) {
    transcript.observe_bytes(
        b"trace-linear-gf2/protocol",
        TRACE_LINEAR_GF2_PROTOCOL_LABEL,
    );
    transcript.observe_u64(b"trace-linear-gf2/weight-count", weights.len() as u64);
    transcript.observe_u64(b"trace-linear-gf2/num-queries", num_queries as u64);
    transcript.observe_u64(b"trace-linear-gf2/log-blowup", log_blowup as u64);
    for (index, &weight) in weights.iter().enumerate() {
        transcript.observe_u64(b"trace-linear-gf2/weight-index", index as u64);
        transcript.observe_bytes(b"trace-linear-gf2/weight", &tower_leaf_payload(weight));
    }
    transcript.observe_bytes(
        b"trace-linear-gf2/claimed-value",
        &tower_leaf_payload(claimed_value),
    );
}

fn absorb_round(transcript: &mut BinaryShake256Transcript, round: usize, message: &[TowerElem; 3]) {
    transcript.observe_u64(b"trace-linear-gf2/round", round as u64);
    transcript.observe_u64(b"trace-linear-gf2/round-degree", 2);
    for &value in message {
        transcript.observe_bytes(b"trace-linear-gf2/round-value", &tower_leaf_payload(value));
    }
}

fn sample_challenge(transcript: &mut BinaryShake256Transcript) -> TowerElem {
    TowerElem::new(
        MAX_LEVEL,
        transcript.sample_gf2_64(b"trace-linear-gf2/round-challenge"),
    )
    .expect("every u64 is canonical in GF(2^64)")
}

struct QuadraticInnerProductGf2Prover {
    table_layer: Vec<TowerElem>,
    weights_layer: Vec<TowerElem>,
    challenges: Vec<TowerElem>,
}

impl QuadraticInnerProductGf2Prover {
    fn new(table: &[TowerElem], weights: &[TowerElem]) -> Result<Self, TraceLinearGf2Error> {
        validate_tables(table, weights)?;
        Ok(Self {
            table_layer: table.to_vec(),
            weights_layer: weights.to_vec(),
            challenges: Vec::with_capacity(table.len().trailing_zeros() as usize),
        })
    }

    fn message(&self) -> Result<[TowerElem; 3], TraceLinearGf2Error> {
        if self.table_layer.len() <= 1 || self.table_layer.len() != self.weights_layer.len() {
            return Err(TraceLinearGf2Error::InvalidShape);
        }
        let zero = TowerElem::zero(MAX_LEVEL)?;
        let one = TowerElem::one(MAX_LEVEL)?;
        let theta = quadratic_probe()?;
        let mut message = [zero; 3];
        for (table_pair, weights_pair) in self
            .table_layer
            .chunks_exact(2)
            .zip(self.weights_layer.chunks_exact(2))
        {
            let table_delta = table_pair[0].add(table_pair[1])?;
            let weights_delta = weights_pair[0].add(weights_pair[1])?;
            for (slot, point) in message.iter_mut().zip([zero, one, theta]) {
                let table_value = table_pair[0].add(table_delta.mul(point)?)?;
                let weights_value = weights_pair[0].add(weights_delta.mul(point)?)?;
                *slot = slot.add(table_value.mul(weights_value)?)?;
            }
        }
        Ok(message)
    }

    fn bind(&mut self, challenge: TowerElem) -> Result<(), TraceLinearGf2Error> {
        if self.table_layer.len() <= 1 || self.table_layer.len() != self.weights_layer.len() {
            return Err(TraceLinearGf2Error::InvalidShape);
        }
        self.table_layer = bind_affine_layer(&self.table_layer, challenge)?;
        self.weights_layer = bind_affine_layer(&self.weights_layer, challenge)?;
        self.challenges.push(challenge);
        Ok(())
    }

    fn finish(self) -> Result<(TowerElem, TowerElem), TraceLinearGf2Error> {
        if self.table_layer.len() != 1 || self.weights_layer.len() != 1 {
            return Err(TraceLinearGf2Error::InvalidShape);
        }
        Ok((self.table_layer[0], self.weights_layer[0]))
    }
}

fn bind_affine_layer(
    layer: &[TowerElem],
    challenge: TowerElem,
) -> Result<Vec<TowerElem>, TraceLinearGf2Error> {
    layer
        .chunks_exact(2)
        .map(|pair| Ok(pair[0].add(pair[0].add(pair[1])?.mul(challenge)?)?))
        .collect()
}

fn evaluate_public_mle(
    values: &[TowerElem],
    point: &[TowerElem],
) -> Result<TowerElem, TraceLinearGf2Error> {
    if point.len() != values.len().trailing_zeros() as usize {
        return Err(TraceLinearGf2Error::InvalidShape);
    }
    let mut layer = values.to_vec();
    for &challenge in point {
        layer = bind_affine_layer(&layer, challenge)?;
    }
    layer
        .first()
        .copied()
        .ok_or(TraceLinearGf2Error::InvalidShape)
}

fn evaluate_quadratic(
    message: &[TowerElem; 3],
    point: TowerElem,
) -> Result<TowerElem, TraceLinearGf2Error> {
    let theta = quadratic_probe()?;
    let d_one = message[0].add(message[1])?;
    let d_theta = message[0].add(message[2])?;
    let denominator = theta.square().add(theta)?;
    let quadratic = d_theta.add(theta.mul(d_one)?)?.div(denominator)?;
    let point_quadratic = point.square().add(point)?;
    Ok(message[0]
        .add(d_one.mul(point)?)?
        .add(quadratic.mul(point_quadratic)?)?)
}

fn verify_quadratic_chain(
    claimed_value: TowerElem,
    rounds: &[[TowerElem; 3]],
    challenges: &[TowerElem],
) -> Result<TowerElem, TraceLinearGf2Error> {
    if rounds.len() != challenges.len() {
        return Err(TraceLinearGf2Error::InvalidProofShape);
    }
    let mut running = claimed_value;
    for (message, &challenge) in rounds.iter().zip(challenges) {
        if message.iter().any(|value| value.level() != MAX_LEVEL)
            || message[0].add(message[1])? != running
        {
            return Err(TraceLinearGf2Error::InvalidProofShape);
        }
        running = evaluate_quadratic(message, challenge)?;
    }
    Ok(running)
}

fn quadratic_probe() -> Result<TowerElem, TraceLinearGf2Error> {
    Ok(TowerElem::new(MAX_LEVEL, 2)?)
}

fn validate_tables(table: &[TowerElem], weights: &[TowerElem]) -> Result<(), TraceLinearGf2Error> {
    validate_single_table(table)?;
    validate_single_table(weights)?;
    if table.len() != weights.len() {
        return Err(TraceLinearGf2Error::InvalidShape);
    }
    Ok(())
}

fn validate_single_table(values: &[TowerElem]) -> Result<(), TraceLinearGf2Error> {
    if values.len() < 2 || !values.len().is_power_of_two() {
        return Err(TraceLinearGf2Error::InvalidShape);
    }
    if values.iter().any(|value| value.level() != MAX_LEVEL) {
        return Err(TraceLinearGf2Error::FieldLevelMismatch);
    }
    Ok(())
}

fn validate_private_shape(
    table: &[TowerElem],
    weights: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
    claimed_value: TowerElem,
    num_queries: usize,
    log_blowup: u32,
) -> Result<usize, TraceLinearGf2Error> {
    validate_tables(table, weights)?;
    validate_domain_shape(
        table.len(),
        basis,
        offset,
        claimed_value,
        num_queries,
        log_blowup,
    )
}

fn validate_public_shape(
    statement: &TraceLinearGf2Statement,
    weights: &[TowerElem],
) -> Result<usize, TraceLinearGf2Error> {
    let table_len = validate_statement_shape(statement)?;
    if weights.len() != table_len || weights.iter().any(|value| value.level() != MAX_LEVEL) {
        return Err(TraceLinearGf2Error::InvalidShape);
    }
    Ok(table_len)
}

fn validate_statement_shape(
    statement: &TraceLinearGf2Statement,
) -> Result<usize, TraceLinearGf2Error> {
    let log_variables = statement
        .basis
        .len()
        .checked_sub(statement.log_blowup as usize)
        .ok_or(TraceLinearGf2Error::InvalidShape)?;
    let table_len = checked_table_len(log_variables)?;
    validate_domain_shape(
        table_len,
        &statement.basis,
        statement.offset,
        statement.claimed_value,
        statement.num_queries,
        statement.log_blowup,
    )?;
    Ok(table_len)
}

fn validate_domain_shape(
    table_len: usize,
    basis: &[TowerElem],
    offset: TowerElem,
    claimed_value: TowerElem,
    num_queries: usize,
    log_blowup: u32,
) -> Result<usize, TraceLinearGf2Error> {
    let expected_log_domain = (table_len.trailing_zeros() as usize)
        .checked_add(log_blowup as usize)
        .ok_or(TraceLinearGf2Error::InvalidShape)?;
    if table_len < 2 || !table_len.is_power_of_two() || basis.len() != expected_log_domain {
        return Err(TraceLinearGf2Error::InvalidShape);
    }
    if offset.level() != MAX_LEVEL
        || claimed_value.level() != MAX_LEVEL
        || basis.iter().any(|value| value.level() != MAX_LEVEL)
    {
        return Err(TraceLinearGf2Error::FieldLevelMismatch);
    }
    if num_queries == 0 || !basis_is_independent(basis) {
        return Err(TraceLinearGf2Error::InvalidDomain);
    }
    Ok(table_len.trailing_zeros() as usize)
}

fn checked_table_len(log_variables: usize) -> Result<usize, TraceLinearGf2Error> {
    if log_variables == 0 {
        return Err(TraceLinearGf2Error::InvalidShape);
    }
    1usize
        .checked_shl(log_variables as u32)
        .ok_or(TraceLinearGf2Error::InvalidShape)
}

fn checked_domain_len(log_domain: usize) -> Result<usize, TraceLinearGf2Error> {
    1usize
        .checked_shl(log_domain as u32)
        .ok_or(TraceLinearGf2Error::InvalidShape)
}

fn basis_is_independent(basis: &[TowerElem]) -> bool {
    let mut pivots = [0u64; 64];
    for beta in basis {
        let mut value = beta.bits();
        while value != 0 {
            let pivot = 63 - value.leading_zeros() as usize;
            if pivots[pivot] == 0 {
                pivots[pivot] = value;
                break;
            }
            value ^= pivots[pivot];
        }
        if value == 0 {
            return false;
        }
    }
    true
}

#[derive(Debug)]
struct FixedQueryError;

impl fmt::Display for FixedQueryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("fixed binary trace-linear query schedule mismatch")
    }
}

struct FixedQueryTranscript {
    queries: Vec<usize>,
    pair_count: usize,
    cursor: usize,
}

impl FixedQueryTranscript {
    fn new(queries: Vec<usize>, pair_count: usize) -> Self {
        Self {
            queries,
            pair_count,
            cursor: 0,
        }
    }
}

impl AdditiveMleTerminalTranscript for FixedQueryTranscript {
    type Error = FixedQueryError;

    fn observe_initial(
        &mut self,
        _hash_suite_id: &[u8],
        _basis: &[TowerElem],
        _offset: TowerElem,
        _log_blowup: u32,
        _root: &BinaryRoot,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn observe_binding(
        &mut self,
        _round: usize,
        _challenge: TowerElem,
        _next_word_len: usize,
        _next_root: &BinaryRoot,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn observe_final(
        &mut self,
        _claimed_terminal: TowerElem,
        _num_queries: usize,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn draw_query_index(
        &mut self,
        query_number: usize,
        pair_count: usize,
    ) -> Result<usize, Self::Error> {
        if query_number != self.cursor || pair_count != self.pair_count {
            return Err(FixedQueryError);
        }
        let query = self
            .queries
            .get(self.cursor)
            .copied()
            .ok_or(FixedQueryError)?;
        self.cursor += 1;
        Ok(query)
    }
}
