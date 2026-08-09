//! Clear gate sumcheck joined to the sampled multiplicative MLE terminal PCS.
//!
//! One [`Ext6Transcript`] owns the whole order:
//!
//! ```text
//! descriptor + public inputs + BinaryShake trace root
//!   -> gamma
//!   -> Mobius/RS root of the gamma-batched defect table
//!   -> (sumcheck message -> r_i -> next PCS root)^v
//!   -> shared terminal -> sampled PCS queries.
//! ```
//!
//! Verification receives the clear trace, recomputes the exact gate-defect
//! table and its initial Mobius/RS root, and therefore rejects a valid PCS for
//! an unrelated oracle.  This closes the clear-reference join.  Deployment's
//! remaining `[GATE-MLE-factored-selector]` seam is replacing that clear-table
//! provenance recomputation with a succinct proof tying the initial root to the
//! emitted trace and factored gate selectors.

use core::{convert::Infallible, fmt};

use crate::{
    binary_hash::{BinaryHashDomain, BinaryRoot, BinaryShake256V1, HashSuite},
    binary_merkle::{BinaryMerkleError, BinaryMerkleTree},
    descriptor::{Descriptor, Fp, GateOp, Wire},
    field4::{P, TWO_ADIC_BITS},
    field6::Ext6,
    gate_claim::gate_defect_table,
    multiplicative_mle_terminal::{
        verify_mle_terminal, MleTerminalError, MleTerminalProof, MleTerminalProverState,
        MleTerminalStatement, MleTerminalTranscript,
    },
    sumcheck_generic::{
        batch_lifted_residuals, claimed_sum, evaluate_mle, verify, SumcheckError, SumcheckProof,
    },
    sumcheck_streaming::{StreamingSumcheckError, StreamingSumcheckProver},
    transcript_ext6::{BinaryShakeExt6Backend, Ext6Transcript, Ext6TranscriptError},
};

const BACKEND_LABEL: &[u8] = b"minidregg/gate-mle-ext6/v1";

const STATEMENT_HEADER_DOMAIN: Fp = 0x474d_4844; // "GMHD"
const STATEMENT_GATE_DOMAIN: Fp = 0x474d_4754; // "GMGT"
const STATEMENT_ZERO_DOMAIN: Fp = 0x474d_5a52; // "GMZR"
const STATEMENT_PUBLIC_DOMAIN: Fp = 0x474d_5055; // "GMPU"
const TRACE_META_DOMAIN: Fp = 0x474d_544d; // "GMTM"
const TRACE_SUITE_DOMAIN: Fp = 0x474d_5453; // "GMTS"
const TRACE_ROOT_DOMAIN: Fp = 0x474d_5452; // "GMTR"
const GATE_PHASE_DOMAIN: Fp = 0x474d_5048; // "GMPH"
const GATE_GAMMA_DOMAIN: Fp = 0x474d_4741; // "GMGA"
const ROUND_INDEX_DOMAIN: Fp = 0x474d_5249; // "GMRI"
const ROUND_MESSAGE_DOMAIN: Fp = 0x474d_524d; // "GMRM"
const ROUND_CHALLENGE_DOMAIN: Fp = 0x474d_5243; // "GMRC"

const TRACE_LEAF_TAG: &[u8; 4] = b"BTR1";
const TRACE_LEAF_BYTES: usize = 9;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GateMleExt6Proof {
    pub trace_root: BinaryRoot,
    pub sumcheck: SumcheckProof<Ext6>,
    pub mle_statement: MleTerminalStatement,
    pub mle_proof: MleTerminalProof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GateMleExt6Error {
    Instance(String),
    UnsatisfiedBatchedClaim,
    Merkle(BinaryMerkleError),
    Transcript(Ext6TranscriptError),
    Streaming(StreamingSumcheckError),
    Sumcheck(SumcheckError),
    Mle(MleTerminalError),
}

impl From<BinaryMerkleError> for GateMleExt6Error {
    fn from(value: BinaryMerkleError) -> Self {
        Self::Merkle(value)
    }
}

impl From<Ext6TranscriptError> for GateMleExt6Error {
    fn from(value: Ext6TranscriptError) -> Self {
        Self::Transcript(value)
    }
}

impl From<StreamingSumcheckError> for GateMleExt6Error {
    fn from(value: StreamingSumcheckError) -> Self {
        Self::Streaming(value)
    }
}

impl From<SumcheckError> for GateMleExt6Error {
    fn from(value: SumcheckError) -> Self {
        Self::Sumcheck(value)
    }
}

impl From<MleTerminalError> for GateMleExt6Error {
    fn from(value: MleTerminalError) -> Self {
        Self::Mle(value)
    }
}

impl fmt::Display for GateMleExt6Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Instance(message) => write!(f, "gate MLE Ext6 instance: {message}"),
            Self::UnsatisfiedBatchedClaim => {
                write!(f, "gamma-batched gate table does not have zero sum")
            }
            Self::Merkle(error) => error.fmt(f),
            Self::Transcript(error) => error.fmt(f),
            Self::Streaming(error) => error.fmt(f),
            Self::Sumcheck(error) => error.fmt(f),
            Self::Mle(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for GateMleExt6Error {}

/// Prove the exact clear-table join under the byte-native Ext6 backend.
pub fn prove_gate_mle_ext6(
    descriptor: &Descriptor,
    public_inputs: &[Fp],
    trace: &[Fp],
    log_blowup: u32,
    num_queries: usize,
) -> Result<GateMleExt6Proof, GateMleExt6Error> {
    let table_len = validate_instance(descriptor, public_inputs, trace, log_blowup, num_queries)?;
    let trace_root = commit_binary_trace(trace)?;
    let mut transcript = start_transcript(
        descriptor,
        public_inputs,
        trace.len(),
        table_len,
        log_blowup,
        num_queries,
        &trace_root,
    )?;
    let gamma = transcript.squeeze_ext6(GATE_GAMMA_DOMAIN)?;
    let table = gate_table_ext6(descriptor, trace, gamma, table_len)?;
    if claimed_sum(&table)? != Ext6::ZERO {
        return Err(GateMleExt6Error::UnsatisfiedBatchedClaim);
    }

    let mut mle = MleTerminalProverState::commit_initial(
        &table,
        log_blowup,
        BinaryShake256V1,
        &mut transcript,
    )?;
    let mut sumcheck = StreamingSumcheckProver::new(&table)?;
    let rounds = table_len.trailing_zeros() as usize;
    let mut messages = Vec::with_capacity(rounds);
    for round in 0..rounds {
        let message = sumcheck.message()?;
        absorb_round(&mut transcript, round, &message)?;
        let challenge = transcript.squeeze_ext6(ROUND_CHALLENGE_DOMAIN)?;
        sumcheck.bind(challenge)?;
        mle.bind(challenge, &mut transcript)?;
        messages.push(message);
    }
    let terminal = sumcheck.finish()?;
    let (mle_statement, mle_proof) = mle.finish(terminal, num_queries, &mut transcript)?;
    Ok(GateMleExt6Proof {
        trace_root,
        sumcheck: SumcheckProof { rounds: messages },
        mle_statement,
        mle_proof,
    })
}

/// Verify the clear trace, exact residual-table provenance, sumcheck chain,
/// and sampled MLE terminal under one replayed Ext6 transcript schedule.
pub fn verify_gate_mle_ext6(
    descriptor: &Descriptor,
    public_inputs: &[Fp],
    trace: &[Fp],
    log_blowup: u32,
    num_queries: usize,
    proof: &GateMleExt6Proof,
) -> Result<bool, GateMleExt6Error> {
    let table_len = validate_instance(descriptor, public_inputs, trace, log_blowup, num_queries)?;
    let rounds = table_len.trailing_zeros() as usize;
    if proof.sumcheck.rounds.len() != rounds
        || proof.mle_statement.log_variables as usize != rounds
        || proof.mle_statement.log_blowup != log_blowup
        || proof.mle_statement.num_queries != num_queries
        || proof.mle_proof.roots.len() != rounds + 1
    {
        return Ok(false);
    }
    let expected_trace_root = commit_binary_trace(trace)?;
    if proof.trace_root != expected_trace_root {
        return Ok(false);
    }

    let mut transcript = start_transcript(
        descriptor,
        public_inputs,
        trace.len(),
        table_len,
        log_blowup,
        num_queries,
        &proof.trace_root,
    )?;
    let gamma = transcript.squeeze_ext6(GATE_GAMMA_DOMAIN)?;
    let table = gate_table_ext6(descriptor, trace, gamma, table_len)?;

    // Clear provenance check: independently recompute the exact Mobius/RS root
    // without perturbing the one real Fiat--Shamir transcript.
    let recomputed = MleTerminalProverState::commit_initial(
        &table,
        log_blowup,
        BinaryShake256V1,
        &mut NoopMleTranscript,
    )?;
    if recomputed.input_root() != proof.mle_statement.input_root
        || proof.mle_proof.roots.first().copied() != Some(recomputed.input_root())
    {
        return Ok(false);
    }

    <Ext6Transcript<BinaryShakeExt6Backend> as MleTerminalTranscript>::observe_initial(
        &mut transcript,
        <BinaryShake256V1 as HashSuite>::SUITE_ID,
        proof.mle_statement.log_variables,
        log_blowup,
        table_len << log_blowup,
        &proof.mle_statement.input_root,
    )?;

    let mut challenges = Vec::with_capacity(rounds);
    let mut next_word_len = (table_len << log_blowup) / 2;
    for (round, message) in proof.sumcheck.rounds.iter().enumerate() {
        absorb_round(&mut transcript, round, message)?;
        let challenge = transcript.squeeze_ext6(ROUND_CHALLENGE_DOMAIN)?;
        challenges.push(challenge);
        <Ext6Transcript<BinaryShakeExt6Backend> as MleTerminalTranscript>::observe_binding(
            &mut transcript,
            round,
            challenge,
            next_word_len,
            &proof.mle_proof.roots[round + 1],
        )?;
        next_word_len /= 2;
    }
    if evaluate_mle(&table, &challenges)? != proof.mle_statement.claimed_terminal {
        return Ok(false);
    }
    if !verify(
        Ext6::ZERO,
        &proof.sumcheck,
        &challenges,
        proof.mle_statement.claimed_terminal,
    )? {
        return Ok(false);
    }

    let blowup = 1usize << log_blowup;
    <Ext6Transcript<BinaryShakeExt6Backend> as MleTerminalTranscript>::observe_final(
        &mut transcript,
        blowup,
        proof.mle_statement.claimed_terminal,
        num_queries,
    )?;
    let pair_count = (table_len << log_blowup) / 2;
    let mut query_indices = Vec::with_capacity(num_queries);
    for query in 0..num_queries {
        query_indices.push(
            <Ext6Transcript<BinaryShakeExt6Backend> as MleTerminalTranscript>::draw_query_index(
                &mut transcript,
                query,
                pair_count,
            )?,
        );
    }

    // The cryptographic transcript above is the sole schedule.  This adapter
    // feeds its already-derived positions into the path/fold verifier without
    // replaying or forking the XOF.
    let mut fixed_queries = FixedQueryTranscript::new(query_indices, pair_count);
    Ok(verify_mle_terminal(
        &proof.mle_statement,
        &challenges,
        &proof.mle_proof,
        &BinaryShake256V1,
        &mut fixed_queries,
    ))
}

fn validate_instance(
    descriptor: &Descriptor,
    public_inputs: &[Fp],
    trace: &[Fp],
    log_blowup: u32,
    num_queries: usize,
) -> Result<usize, GateMleExt6Error> {
    descriptor.validate().map_err(GateMleExt6Error::Instance)?;
    if descriptor.p != P {
        return Err(GateMleExt6Error::Instance(format!(
            "descriptor modulus {} is not BabyBear {P}",
            descriptor.p
        )));
    }
    if descriptor.n_wires == 0 || trace.len() != descriptor.n_wires as usize {
        return Err(GateMleExt6Error::Instance(format!(
            "trace length {}, expected nonzero {}",
            trace.len(),
            descriptor.n_wires
        )));
    }
    if public_inputs.len() != descriptor.n_public as usize
        || trace.get(..public_inputs.len()) != Some(public_inputs)
    {
        return Err(GateMleExt6Error::Instance(
            "trace public prefix does not match the public statement".into(),
        ));
    }
    if public_inputs.iter().chain(trace).any(|&value| value >= P) {
        return Err(GateMleExt6Error::Instance(
            "public input or trace element is non-canonical".into(),
        ));
    }
    if num_queries == 0 || num_queries as u128 >= P as u128 {
        return Err(GateMleExt6Error::Instance(
            "query count must be nonzero and fit BabyBear".into(),
        ));
    }
    for (value, name) in [
        (descriptor.n_public as usize, "n_public"),
        (descriptor.n_vars as usize, "n_vars"),
        (descriptor.n_wires as usize, "n_wires"),
        (descriptor.gates.len(), "gate count"),
        (descriptor.zeros.len(), "zero count"),
        (trace.len(), "trace length"),
    ] {
        checked_fp(value, name)?;
    }
    checked_fp(trace.len().next_power_of_two(), "padded trace length")?;
    let entries = descriptor
        .gates
        .len()
        .checked_add(descriptor.zeros.len())
        .ok_or_else(|| GateMleExt6Error::Instance("gate table length overflow".into()))?;
    let table_len = entries
        .max(2)
        .checked_next_power_of_two()
        .ok_or_else(|| GateMleExt6Error::Instance("gate table domain overflow".into()))?;
    checked_fp(table_len, "gate table length")?;
    let log_variables = table_len.trailing_zeros();
    if log_variables
        .checked_add(log_blowup)
        .is_none_or(|log_domain| log_domain > TWO_ADIC_BITS)
    {
        return Err(GateMleExt6Error::Instance(
            "gate MLE encoded domain exceeds BabyBear two-adicity".into(),
        ));
    }
    Ok(table_len)
}

#[allow(clippy::too_many_arguments)]
fn start_transcript(
    descriptor: &Descriptor,
    public_inputs: &[Fp],
    trace_len: usize,
    table_len: usize,
    log_blowup: u32,
    num_queries: usize,
    trace_root: &BinaryRoot,
) -> Result<Ext6Transcript<BinaryShakeExt6Backend>, GateMleExt6Error> {
    let backend = BinaryShakeExt6Backend::new(BACKEND_LABEL);
    let mut transcript = Ext6Transcript::new(backend)?;
    absorb_statement(&mut transcript, descriptor, public_inputs)?;
    transcript.absorb_record(
        TRACE_META_DOMAIN,
        &[trace_len as Fp, trace_len.next_power_of_two() as Fp],
    )?;
    transcript.absorb_record(
        TRACE_SUITE_DOMAIN,
        &bytes_as_u16_fields(<BinaryShake256V1 as HashSuite>::SUITE_ID),
    )?;
    transcript.absorb_record(TRACE_ROOT_DOMAIN, &root_as_u16_fields(trace_root))?;
    transcript.absorb_record(
        GATE_PHASE_DOMAIN,
        &[
            1,
            table_len as Fp,
            table_len.trailing_zeros() as Fp,
            log_blowup as Fp,
            num_queries as Fp,
            0,
        ],
    )?;
    Ok(transcript)
}

fn absorb_statement(
    transcript: &mut Ext6Transcript<BinaryShakeExt6Backend>,
    descriptor: &Descriptor,
    public_inputs: &[Fp],
) -> Result<(), GateMleExt6Error> {
    transcript.absorb_record(
        STATEMENT_HEADER_DOMAIN,
        &[
            1,
            descriptor.p & 0xffff,
            descriptor.p >> 16,
            descriptor.n_public as Fp,
            descriptor.n_vars as Fp,
            descriptor.n_wires as Fp,
            descriptor.gates.len() as Fp,
            descriptor.zeros.len() as Fp,
        ],
    )?;
    for (index, gate) in descriptor.gates.iter().enumerate() {
        let a = wire_fields(gate.a);
        let b = wire_fields(gate.b);
        transcript.absorb_record(
            STATEMENT_GATE_DOMAIN,
            &[
                index as Fp,
                match gate.op {
                    GateOp::Add => 0,
                    GateOp::Mul => 1,
                },
                a[0],
                a[1],
                b[0],
                b[1],
                gate.out as Fp,
            ],
        )?;
    }
    for (index, &wire) in descriptor.zeros.iter().enumerate() {
        let encoded = wire_fields(wire);
        transcript.absorb_record(
            STATEMENT_ZERO_DOMAIN,
            &[index as Fp, encoded[0], encoded[1]],
        )?;
    }
    transcript.absorb_record(STATEMENT_PUBLIC_DOMAIN, public_inputs)?;
    Ok(())
}

fn absorb_round(
    transcript: &mut Ext6Transcript<BinaryShakeExt6Backend>,
    round: usize,
    message: &[Ext6; 2],
) -> Result<(), GateMleExt6Error> {
    transcript.absorb_record(ROUND_INDEX_DOMAIN, &[round as Fp])?;
    transcript.absorb_ext6_record(ROUND_MESSAGE_DOMAIN, message)?;
    Ok(())
}

fn gate_table_ext6(
    descriptor: &Descriptor,
    trace: &[Fp],
    gamma: Ext6,
    table_len: usize,
) -> Result<Vec<Ext6>, GateMleExt6Error> {
    let defects = gate_defect_table(descriptor, trace);
    let mut table = batch_lifted_residuals::<Ext6>(&defects, gamma)?;
    table.resize(table_len, Ext6::ZERO);
    Ok(table)
}

fn wire_fields(wire: Wire) -> [Fp; 2] {
    match wire {
        Wire::Const(value) => [0, value],
        Wire::Wire(index) => [1, index as Fp],
    }
}

fn checked_fp(value: usize, name: &str) -> Result<Fp, GateMleExt6Error> {
    if value as u128 >= P as u128 {
        Err(GateMleExt6Error::Instance(format!(
            "{name}={value} does not fit BabyBear"
        )))
    } else {
        Ok(value as Fp)
    }
}

fn trace_leaf_payload(value: Fp, padding: bool) -> [u8; TRACE_LEAF_BYTES] {
    let mut payload = [0u8; TRACE_LEAF_BYTES];
    payload[..4].copy_from_slice(TRACE_LEAF_TAG);
    payload[4] = u8::from(padding);
    payload[5..].copy_from_slice(&(value as u32).to_le_bytes());
    payload
}

fn commit_binary_trace(trace: &[Fp]) -> Result<BinaryRoot, GateMleExt6Error> {
    let padded_len = trace.len().next_power_of_two();
    let mut payloads = trace
        .iter()
        .copied()
        .map(|value| trace_leaf_payload(value, false))
        .collect::<Vec<_>>();
    payloads.extend((trace.len()..padded_len).map(|_| trace_leaf_payload(0, true)));
    Ok(BinaryMerkleTree::build(&BinaryShake256V1, BinaryHashDomain::Trace, &payloads)?.root())
}

fn bytes_as_u16_fields(bytes: &[u8]) -> Vec<Fp> {
    bytes
        .chunks(2)
        .map(|chunk| {
            let high = chunk.get(1).copied().unwrap_or(0);
            u16::from_le_bytes([chunk[0], high]) as Fp
        })
        .collect()
}

fn root_as_u16_fields(root: &BinaryRoot) -> Vec<Fp> {
    root.as_bytes()
        .chunks_exact(2)
        .map(|chunk| u16::from_le_bytes([chunk[0], chunk[1]]) as Fp)
        .collect()
}

struct NoopMleTranscript;

impl MleTerminalTranscript for NoopMleTranscript {
    type Error = Infallible;

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
        _query_number: usize,
        _pair_count: usize,
    ) -> Result<usize, Self::Error> {
        Ok(0)
    }
}

#[derive(Debug)]
struct FixedQueryError;

impl fmt::Display for FixedQueryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("fixed MLE query schedule mismatch")
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
