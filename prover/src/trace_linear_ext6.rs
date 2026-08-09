//! Succinct sampled opening of a committed table linear functional.
//!
//! For a private LSB-indexed table `a` and public weights `w`, this protocol
//! proves `y = dot(a,w)` without carrying `a`.  The table is committed through
//! [`MleTerminalProverState`]'s Boolean-Mobius multiplicative-RS root.  A
//! degree-two sumcheck reduces
//!
//! ```text
//! sum_{x in {0,1}^v} MLE(a,x) * MLE(w,x)
//! ```
//!
//! to `MLE(a,r) * MLE(w,r)`.  Every quadratic message is absorbed before its
//! `r_i`; that same `r_i` immediately binds the table PCS and its next root.
//! The final table MLE is discharged by the sampled multiplicative terminal
//! proof.  Public selector vectors can therefore reuse this API directly.
//!
//! Honest assumptions remain explicit: BinaryShake Merkle collision resistance
//! `[TRACE-LINEAR-CR]`, cSHAKE/Fiat--Shamir random-oracle analysis
//! `[TRACE-LINEAR-ROM]`, sampled fold/proximity soundness at the landed coherent
//! multiplicative bound `m*b/|F| + (1-tau)^q` `[TRACE-LINEAR-PROXIMITY]`, and
//! executable-to-formal refinement of the Mobius/RS, sumcheck, transcript, and
//! query code is unverified Rust compute under `[TRACE-LINEAR-RUST-UNVERIFIED]`.

use core::fmt;

use crate::{
    binary_hash::{BinaryRoot, BinaryShake256V1, HashSuite},
    field4::{HALF, P, TWO_ADIC_BITS},
    field6::Ext6,
    multiplicative_mle_terminal::{
        verify_mle_terminal, MleTerminalError, MleTerminalProof, MleTerminalProverState,
        MleTerminalStatement, MleTerminalTranscript,
    },
    sumcheck_generic::evaluate_mle,
    transcript_ext6::{BinaryShakeExt6Backend, Ext6Transcript, Ext6TranscriptError},
};

const BACKEND_LABEL: &[u8] = b"minidregg/trace-linear-ext6/v1";

const STATEMENT_DOMAIN: u64 = 0x544c_5354; // "TLST"
const WEIGHTS_DOMAIN: u64 = 0x544c_5745; // "TLWE"
const CLAIM_DOMAIN: u64 = 0x544c_434c; // "TLCL"
const ROUND_META_DOMAIN: u64 = 0x544c_524d; // "TLRM"
const ROUND_MESSAGE_DOMAIN: u64 = 0x544c_5251; // "TLRQ"
const ROUND_CHALLENGE_DOMAIN: u64 = 0x544c_5243; // "TLRC"

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceLinearStatement {
    pub table_root: BinaryRoot,
    pub log_variables: u32,
    pub log_blowup: u32,
    pub claimed_value: Ext6,
    pub num_queries: usize,
}

/// Three evaluations `(g_i(0), g_i(1), g_i(2))` of a degree-two round.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuadraticSumcheckProof {
    pub rounds: Vec<[Ext6; 3]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceLinearProof {
    pub sumcheck: QuadraticSumcheckProof,
    pub table_mle_statement: MleTerminalStatement,
    pub table_mle_proof: MleTerminalProof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TraceLinearError {
    InvalidShape,
    InvalidDomain,
    ClaimedValueMismatch,
    InvalidProofShape,
    Transcript(Ext6TranscriptError),
    Mle(MleTerminalError),
}

impl From<Ext6TranscriptError> for TraceLinearError {
    fn from(value: Ext6TranscriptError) -> Self {
        Self::Transcript(value)
    }
}

impl From<MleTerminalError> for TraceLinearError {
    fn from(value: MleTerminalError) -> Self {
        Self::Mle(value)
    }
}

impl fmt::Display for TraceLinearError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidShape => write!(
                f,
                "trace linear tables must have equal power-of-two length at least two"
            ),
            Self::InvalidDomain => write!(f, "invalid trace linear encoded domain or query count"),
            Self::ClaimedValueMismatch => write!(
                f,
                "claimed trace linear value is not the private/public dot product"
            ),
            Self::InvalidProofShape => write!(f, "invalid trace linear proof shape"),
            Self::Transcript(error) => error.fmt(f),
            Self::Mle(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for TraceLinearError {}

/// Clear helper for constructing a public claim or selector conformance test.
pub fn linear_functional_value(table: &[Ext6], weights: &[Ext6]) -> Result<Ext6, TraceLinearError> {
    validate_tables(table, weights)?;
    Ok(table
        .iter()
        .copied()
        .zip(weights.iter().copied())
        .fold(Ext6::ZERO, |sum, (value, weight)| {
            sum.add(value.mul(weight))
        }))
}

/// Prove one public linear-functional claim with no table in the proof.
pub fn prove_trace_linear(
    table: &[Ext6],
    weights: &[Ext6],
    claimed_value: Ext6,
    log_blowup: u32,
    num_queries: usize,
) -> Result<(TraceLinearStatement, TraceLinearProof), TraceLinearError> {
    let mut transcript = Ext6Transcript::new(BinaryShakeExt6Backend::new(BACKEND_LABEL))?;
    prove_trace_linear_with_transcript(
        table,
        weights,
        claimed_value,
        log_blowup,
        num_queries,
        &mut transcript,
    )
}

/// Prove inside a caller-owned cSHAKE/Ext6 transcript.
///
/// This is the composition seam for protocols that already bound a statement
/// and drew earlier challenges.  It observes the table's MLE root, the public
/// weights and claim, then interleaves every inner-product sumcheck challenge
/// with the corresponding MLE-PCS root.  The standalone wrapper above uses
/// exactly this schedule in a fresh protocol transcript.
pub fn prove_trace_linear_with_transcript(
    table: &[Ext6],
    weights: &[Ext6],
    claimed_value: Ext6,
    log_blowup: u32,
    num_queries: usize,
    transcript: &mut Ext6Transcript<BinaryShakeExt6Backend>,
) -> Result<(TraceLinearStatement, TraceLinearProof), TraceLinearError> {
    validate_public_shape(table.len(), weights, log_blowup, num_queries)?;
    if linear_functional_value(table, weights)? != claimed_value {
        return Err(TraceLinearError::ClaimedValueMismatch);
    }
    let table_mle = MleTerminalProverState::commit_initial(
        table,
        log_blowup,
        BinaryShake256V1,
        &mut *transcript,
    )?;
    prove_trace_linear_from_state(
        table,
        weights,
        claimed_value,
        log_blowup,
        num_queries,
        table_mle,
        transcript,
    )
}

/// Continue from a trace MLE commitment already observed in `transcript`.
///
/// A containing protocol can commit once before its outer challenges, retain
/// the returned state, and call this after deriving its combined linear claim.
/// The initial root must already have been observed in this exact transcript;
/// this function absorbs only the weights/claim and subsequent fold roots.
#[allow(clippy::too_many_arguments)]
pub fn prove_trace_linear_from_state(
    table: &[Ext6],
    weights: &[Ext6],
    claimed_value: Ext6,
    log_blowup: u32,
    num_queries: usize,
    mut table_mle: MleTerminalProverState<BinaryShake256V1>,
    transcript: &mut Ext6Transcript<BinaryShakeExt6Backend>,
) -> Result<(TraceLinearStatement, TraceLinearProof), TraceLinearError> {
    let log_variables = validate_public_shape(table.len(), weights, log_blowup, num_queries)?;
    if linear_functional_value(table, weights)? != claimed_value {
        return Err(TraceLinearError::ClaimedValueMismatch);
    }
    let table_root = table_mle.input_root();
    absorb_linear_statement(
        transcript,
        log_variables,
        log_blowup,
        num_queries,
        weights,
        claimed_value,
    )?;

    let mut sumcheck = QuadraticInnerProductProver::new(table, weights)?;
    let mut messages = Vec::with_capacity(log_variables as usize);
    for round in 0..log_variables as usize {
        let message = sumcheck.message()?;
        absorb_round(transcript, round, &message)?;
        let challenge = transcript.squeeze_ext6(ROUND_CHALLENGE_DOMAIN)?;
        sumcheck.bind(challenge)?;
        table_mle.bind(challenge, &mut *transcript)?;
        messages.push(message);
    }
    let challenges = sumcheck.challenges.clone();
    let (table_terminal, weights_terminal) = sumcheck.finish()?;
    let running_terminal = verify_quadratic_chain(claimed_value, &messages, &challenges)?;
    if running_terminal != table_terminal.mul(weights_terminal) {
        return Err(TraceLinearError::InvalidProofShape);
    }
    let (table_mle_statement, table_mle_proof) =
        table_mle.finish(table_terminal, num_queries, &mut *transcript)?;
    Ok((
        TraceLinearStatement {
            table_root,
            log_variables,
            log_blowup,
            claimed_value,
            num_queries,
        },
        TraceLinearProof {
            sumcheck: QuadraticSumcheckProof { rounds: messages },
            table_mle_statement,
            table_mle_proof,
        },
    ))
}

/// Verify with public/recomputed weights and no private table.
pub fn verify_trace_linear(
    statement: &TraceLinearStatement,
    weights: &[Ext6],
    proof: &TraceLinearProof,
) -> Result<bool, TraceLinearError> {
    let mut transcript = Ext6Transcript::new(BinaryShakeExt6Backend::new(BACKEND_LABEL))?;
    verify_trace_linear_with_transcript(statement, weights, proof, &mut transcript)
}

/// Verify inside the same caller-owned cSHAKE/Ext6 transcript used by a
/// containing protocol.  No transcript is forked or restarted here.
pub fn verify_trace_linear_with_transcript(
    statement: &TraceLinearStatement,
    weights: &[Ext6],
    proof: &TraceLinearProof,
    transcript: &mut Ext6Transcript<BinaryShakeExt6Backend>,
) -> Result<bool, TraceLinearError> {
    let table_len = checked_table_len(statement.log_variables)?;
    validate_public_shape(
        table_len,
        weights,
        statement.log_blowup,
        statement.num_queries,
    )?;
    let domain_size = table_len << statement.log_blowup;
    <Ext6Transcript<BinaryShakeExt6Backend> as MleTerminalTranscript>::observe_initial(
        &mut *transcript,
        <BinaryShake256V1 as HashSuite>::SUITE_ID,
        statement.log_variables,
        statement.log_blowup,
        domain_size,
        &statement.table_root,
    )?;
    verify_trace_linear_after_initial(statement, weights, proof, transcript)
}

/// Verify after a containing protocol has already observed this exact initial
/// MLE root in the caller-owned transcript.
pub fn verify_trace_linear_after_initial(
    statement: &TraceLinearStatement,
    weights: &[Ext6],
    proof: &TraceLinearProof,
    transcript: &mut Ext6Transcript<BinaryShakeExt6Backend>,
) -> Result<bool, TraceLinearError> {
    let table_len = checked_table_len(statement.log_variables)?;
    validate_public_shape(
        table_len,
        weights,
        statement.log_blowup,
        statement.num_queries,
    )?;
    let rounds = statement.log_variables as usize;
    if proof.sumcheck.rounds.len() != rounds
        || proof.table_mle_statement.input_root != statement.table_root
        || proof.table_mle_statement.log_variables != statement.log_variables
        || proof.table_mle_statement.log_blowup != statement.log_blowup
        || proof.table_mle_statement.num_queries != statement.num_queries
        || proof.table_mle_proof.roots.len() != rounds + 1
        || proof.table_mle_proof.roots.first().copied() != Some(statement.table_root)
    {
        return Ok(false);
    }

    let domain_size = table_len << statement.log_blowup;
    absorb_linear_statement(
        transcript,
        statement.log_variables,
        statement.log_blowup,
        statement.num_queries,
        weights,
        statement.claimed_value,
    )?;

    let mut challenges = Vec::with_capacity(rounds);
    let mut next_word_len = domain_size / 2;
    for (round, message) in proof.sumcheck.rounds.iter().enumerate() {
        absorb_round(transcript, round, message)?;
        let challenge = transcript.squeeze_ext6(ROUND_CHALLENGE_DOMAIN)?;
        challenges.push(challenge);
        <Ext6Transcript<BinaryShakeExt6Backend> as MleTerminalTranscript>::observe_binding(
            &mut *transcript,
            round,
            challenge,
            next_word_len,
            &proof.table_mle_proof.roots[round + 1],
        )?;
        next_word_len /= 2;
    }
    let running = match verify_quadratic_chain(
        statement.claimed_value,
        &proof.sumcheck.rounds,
        &challenges,
    ) {
        Ok(running) => running,
        Err(_) => return Ok(false),
    };
    let weights_terminal =
        evaluate_mle(weights, &challenges).map_err(|_| TraceLinearError::InvalidShape)?;
    if running
        != proof
            .table_mle_statement
            .claimed_terminal
            .mul(weights_terminal)
    {
        return Ok(false);
    }

    let blowup = 1usize << statement.log_blowup;
    <Ext6Transcript<BinaryShakeExt6Backend> as MleTerminalTranscript>::observe_final(
        &mut *transcript,
        blowup,
        proof.table_mle_statement.claimed_terminal,
        statement.num_queries,
    )?;
    let pair_count = domain_size / 2;
    let mut query_indices = Vec::with_capacity(statement.num_queries);
    for query in 0..statement.num_queries {
        query_indices.push(
            <Ext6Transcript<BinaryShakeExt6Backend> as MleTerminalTranscript>::draw_query_index(
                &mut *transcript,
                query,
                pair_count,
            )?,
        );
    }
    let mut fixed = FixedQueryTranscript::new(query_indices, pair_count);
    Ok(verify_mle_terminal(
        &proof.table_mle_statement,
        &challenges,
        &proof.table_mle_proof,
        &BinaryShake256V1,
        &mut fixed,
    ))
}

fn absorb_linear_statement(
    transcript: &mut Ext6Transcript<BinaryShakeExt6Backend>,
    log_variables: u32,
    log_blowup: u32,
    num_queries: usize,
    weights: &[Ext6],
    claimed_value: Ext6,
) -> Result<(), TraceLinearError> {
    transcript.absorb_record(
        STATEMENT_DOMAIN,
        &[
            1,
            log_variables as u64,
            weights.len() as u64,
            log_blowup as u64,
            num_queries as u64,
        ],
    )?;
    transcript.absorb_ext6_record(WEIGHTS_DOMAIN, weights)?;
    transcript.absorb_ext6_record(CLAIM_DOMAIN, &[claimed_value])?;
    Ok(())
}

fn absorb_round(
    transcript: &mut Ext6Transcript<BinaryShakeExt6Backend>,
    round: usize,
    message: &[Ext6; 3],
) -> Result<(), TraceLinearError> {
    transcript.absorb_record(ROUND_META_DOMAIN, &[round as u64, 2])?;
    transcript.absorb_ext6_record(ROUND_MESSAGE_DOMAIN, message)?;
    Ok(())
}

struct QuadraticInnerProductProver {
    table_layer: Vec<Ext6>,
    weights_layer: Vec<Ext6>,
    challenges: Vec<Ext6>,
}

impl QuadraticInnerProductProver {
    fn new(table: &[Ext6], weights: &[Ext6]) -> Result<Self, TraceLinearError> {
        validate_tables(table, weights)?;
        Ok(Self {
            table_layer: table.to_vec(),
            weights_layer: weights.to_vec(),
            challenges: Vec::with_capacity(table.len().trailing_zeros() as usize),
        })
    }

    fn message(&self) -> Result<[Ext6; 3], TraceLinearError> {
        if self.table_layer.len() <= 1 || self.table_layer.len() != self.weights_layer.len() {
            return Err(TraceLinearError::InvalidShape);
        }
        let two = Ext6::try_from_base(2).expect("2 is canonical in BabyBear");
        let mut message = [Ext6::ZERO; 3];
        for (table_pair, weights_pair) in self
            .table_layer
            .chunks_exact(2)
            .zip(self.weights_layer.chunks_exact(2))
        {
            let table_delta = table_pair[1].sub(table_pair[0]);
            let weights_delta = weights_pair[1].sub(weights_pair[0]);
            for (slot, point) in message.iter_mut().zip([Ext6::ZERO, Ext6::ONE, two]) {
                let table_value = table_pair[0].add(table_delta.mul(point));
                let weights_value = weights_pair[0].add(weights_delta.mul(point));
                *slot = slot.add(table_value.mul(weights_value));
            }
        }
        Ok(message)
    }

    fn bind(&mut self, challenge: Ext6) -> Result<(), TraceLinearError> {
        if self.table_layer.len() <= 1 || self.table_layer.len() != self.weights_layer.len() {
            return Err(TraceLinearError::InvalidShape);
        }
        self.table_layer = bind_affine_layer(&self.table_layer, challenge);
        self.weights_layer = bind_affine_layer(&self.weights_layer, challenge);
        self.challenges.push(challenge);
        Ok(())
    }

    fn finish(self) -> Result<(Ext6, Ext6), TraceLinearError> {
        if self.table_layer.len() != 1 || self.weights_layer.len() != 1 {
            return Err(TraceLinearError::InvalidShape);
        }
        Ok((self.table_layer[0], self.weights_layer[0]))
    }
}

fn bind_affine_layer(layer: &[Ext6], challenge: Ext6) -> Vec<Ext6> {
    layer
        .chunks_exact(2)
        .map(|pair| pair[0].add(pair[1].sub(pair[0]).mul(challenge)))
        .collect()
}

fn evaluate_quadratic(message: &[Ext6; 3], point: Ext6) -> Ext6 {
    let first_difference = message[1].sub(message[0]);
    let second_difference = message[2].sub(message[1].base_mul(2)).add(message[0]);
    message[0].add(first_difference.mul(point)).add(
        second_difference
            .base_mul(HALF)
            .mul(point.mul(point.sub(Ext6::ONE))),
    )
}

fn verify_quadratic_chain(
    claimed_value: Ext6,
    rounds: &[[Ext6; 3]],
    challenges: &[Ext6],
) -> Result<Ext6, TraceLinearError> {
    if rounds.len() != challenges.len() {
        return Err(TraceLinearError::InvalidProofShape);
    }
    let mut running = claimed_value;
    for (message, &challenge) in rounds.iter().zip(challenges) {
        if message[0].add(message[1]) != running {
            return Err(TraceLinearError::InvalidProofShape);
        }
        running = evaluate_quadratic(message, challenge);
    }
    Ok(running)
}

fn validate_tables(table: &[Ext6], weights: &[Ext6]) -> Result<(), TraceLinearError> {
    if table.len() < 2 || !table.len().is_power_of_two() || table.len() != weights.len() {
        Err(TraceLinearError::InvalidShape)
    } else {
        Ok(())
    }
}

fn validate_public_shape(
    table_len: usize,
    weights: &[Ext6],
    log_blowup: u32,
    num_queries: usize,
) -> Result<u32, TraceLinearError> {
    if table_len < 2 || !table_len.is_power_of_two() || weights.len() != table_len {
        return Err(TraceLinearError::InvalidShape);
    }
    let log_variables = table_len.trailing_zeros();
    if log_variables
        .checked_add(log_blowup)
        .is_none_or(|log_domain| log_domain > TWO_ADIC_BITS)
        || num_queries == 0
        || num_queries as u128 >= P as u128
    {
        return Err(TraceLinearError::InvalidDomain);
    }
    Ok(log_variables)
}

fn checked_table_len(log_variables: u32) -> Result<usize, TraceLinearError> {
    if log_variables == 0 || log_variables > TWO_ADIC_BITS {
        return Err(TraceLinearError::InvalidShape);
    }
    1usize
        .checked_shl(log_variables)
        .ok_or(TraceLinearError::InvalidShape)
}

#[derive(Debug)]
struct FixedQueryError;

impl fmt::Display for FixedQueryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("fixed trace-linear query schedule mismatch")
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

impl MleTerminalTranscript for FixedQueryTranscript {
    type Error = FixedQueryError;

    fn observe_initial(
        &mut self,
        _hash_suite_id: &[u8],
        _log_variables: u32,
        _log_blowup: u32,
        _domain_size: usize,
        _root: &BinaryRoot,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn observe_binding(
        &mut self,
        _round: usize,
        _challenge: Ext6,
        _next_word_len: usize,
        _next_root: &BinaryRoot,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn observe_final(
        &mut self,
        _blowup: usize,
        _claimed_terminal: Ext6,
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
