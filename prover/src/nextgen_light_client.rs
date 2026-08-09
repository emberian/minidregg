//! One binary evaluation-history append conjoined with one succinct gate proof.
//!
//! This object is a conjunction, not recursive compression: it carries the
//! landed binary append/output-OOD proof and the landed succinct factored-gate
//! proof.  The join is an injective BabyBear public-input encoding of both full
//! binary input evaluation statements plus the append-derived output claim.
//! The gate trace remains private; only its commitment/opening proof is carried.
//!
//! At the component boundary there are two domain-separated Fiat--Shamir
//! transcript families: the binary evaluation-history component and the Ext6
//! factored-gate component.  The binary family itself retains the landed,
//! separately scheduled append and OOD transcripts.  No recursive transcript
//! merger is claimed.  Their conjunction under a shared cSHAKE random-oracle
//! model remains `[NEXTGEN-LC-shared-ROM]`; each component also retains its own
//! collision-resistance, proximity, and unverified-Rust/generated-control assumptions.
//!
//! For a fixed descriptor and query profile, proof shape is independent of
//! accumulated history depth.

use core::fmt;

use crate::{
    binary_evaluation_history_append::{
        prove_binary_evaluation_history_append, verify_binary_evaluation_history_append,
        BinaryEvaluationHistoryAppendError, BinaryEvaluationHistoryAppendProof,
        BinaryEvaluationHistoryAppendStatement,
    },
    binary_hash::{BinaryRoot, BinaryShake256V1, HashSuite},
    binary_history_append::{BinaryAdditiveRsClaim, BinaryChannelId},
    binary_tower::TowerElem,
    descriptor::{Descriptor, Fp},
    field4::P,
    succinct_factored_gate::{
        prove_succinct_factored_gate, verify_succinct_factored_gate, SuccinctFactoredGateError,
        SuccinctFactoredGateProof,
    },
};

pub const NEXTGEN_PUBLIC_INPUT_ENCODING_VERSION: u64 = 1;

const ENCODING_TAG: &[u8] = b"minidregg/nextgen-light-client/public-inputs/v1";
const BINARY_PROTOCOL_TAG: &[u8] = b"minidregg/binary-evaluation-history-append/v1";
const TOWER_SUITE_TAG: &[u8] = b"FanPaarBinaryTower/GF2^64/level6/v1";

const HEADER_SECTION: Fp = 1;
const LEFT_STATEMENT_SECTION: Fp = 2;
const RIGHT_STATEMENT_SECTION: Fp = 3;
const OUTPUT_CLAIM_SECTION: Fp = 4;
const CLAIM_SECTION: Fp = 5;
const BASIS_SECTION: Fp = 6;
const OFFSET_SECTION: Fp = 7;
const EVALUATION_POINT_SECTION: Fp = 8;
const QUERY_SECTION: Fp = 9;

/// A single light-client conjunction proof.  Neither private word nor gate
/// trace is present.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NextgenLightClientProof {
    pub binary: BinaryEvaluationHistoryAppendProof,
    pub gate: SuccinctFactoredGateProof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NextgenLightClientError {
    EncodingOverflow(&'static str),
    PublicInputLength { descriptor: usize, encoded: usize },
    TracePublicPrefixMismatch,
    Binary(BinaryEvaluationHistoryAppendError),
    Gate(SuccinctFactoredGateError),
}

impl From<BinaryEvaluationHistoryAppendError> for NextgenLightClientError {
    fn from(value: BinaryEvaluationHistoryAppendError) -> Self {
        Self::Binary(value)
    }
}

impl From<SuccinctFactoredGateError> for NextgenLightClientError {
    fn from(value: SuccinctFactoredGateError) -> Self {
        Self::Gate(value)
    }
}

impl fmt::Display for NextgenLightClientError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EncodingOverflow(name) => {
                write!(f, "nextgen public-input {name} does not fit u64")
            }
            Self::PublicInputLength {
                descriptor,
                encoded,
            } => write!(
                f,
                "gate descriptor has {descriptor} public inputs, binary encoding has {encoded}"
            ),
            Self::TracePublicPrefixMismatch => {
                write!(
                    f,
                    "private gate trace does not start with the binary public encoding"
                )
            }
            Self::Binary(error) => error.fmt(f),
            Self::Gate(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for NextgenLightClientError {}

/// Canonically and injectively encode the complete binary public statement and
/// one derived output claim as BabyBear cells.
///
/// Every byte string uses little-endian u16 chunks preceded by its byte length;
/// every integer uses four fixed little-endian u16 chunks.  The body has an
/// explicit field-cell length, both basis vectors have explicit element counts,
/// and section/version/suite tags pin the schema.
pub fn encode_nextgen_public_inputs(
    statement: &BinaryEvaluationHistoryAppendStatement,
    output_claim: &BinaryAdditiveRsClaim,
) -> Result<Vec<Fp>, NextgenLightClientError> {
    let mut body = Vec::new();
    body.push(HEADER_SECTION);
    push_bytes(&mut body, ENCODING_TAG)?;
    push_bytes(&mut body, <BinaryShake256V1 as HashSuite>::SUITE_ID)?;
    push_bytes(&mut body, BINARY_PROTOCOL_TAG)?;
    push_bytes(&mut body, TOWER_SUITE_TAG)?;
    encode_evaluation_statement(&mut body, LEFT_STATEMENT_SECTION, &statement.left)?;
    encode_evaluation_statement(&mut body, RIGHT_STATEMENT_SECTION, &statement.right)?;
    body.push(OUTPUT_CLAIM_SECTION);
    encode_claim(&mut body, output_claim)?;

    let body_len = u64::try_from(body.len())
        .map_err(|_| NextgenLightClientError::EncodingOverflow("body length"))?;
    let mut encoded = Vec::with_capacity(body.len() + 5);
    encoded.push(NEXTGEN_PUBLIC_INPUT_ENCODING_VERSION);
    push_u64(&mut encoded, body_len);
    encoded.extend(body);
    debug_assert!(encoded.iter().all(|&cell| cell < P));
    Ok(encoded)
}

/// First prove and re-authenticate the binary append output, then bind its exact
/// public encoding as the prefix of the private gate trace and prove the gate.
#[allow(clippy::too_many_arguments)]
pub fn prove_nextgen_light_client(
    binary_statement: &BinaryEvaluationHistoryAppendStatement,
    descriptor: &Descriptor,
    gate_trace: &[Fp],
    gate_log_blowup: u32,
    gate_num_queries: usize,
    left_word: &[TowerElem],
    left_coefficients: &[TowerElem],
    right_word: &[TowerElem],
    right_coefficients: &[TowerElem],
) -> Result<NextgenLightClientProof, NextgenLightClientError> {
    let binary = prove_binary_evaluation_history_append(
        binary_statement,
        left_word,
        left_coefficients,
        right_word,
        right_coefficients,
    )?;
    let public_inputs = encode_nextgen_public_inputs(binary_statement, binary.output_claim())?;
    require_public_prefix(descriptor, gate_trace, &public_inputs)?;
    let gate = prove_succinct_factored_gate(
        descriptor,
        &public_inputs,
        gate_trace,
        gate_log_blowup,
        gate_num_queries,
    )?;
    Ok(NextgenLightClientProof { binary, gate })
}

/// Reconstruct the exact gate public inputs from only the external binary
/// statement and the proof's derived output claim, verify the binary append,
/// then verify the private-trace gate proof against those cells.
pub fn verify_nextgen_light_client(
    binary_statement: &BinaryEvaluationHistoryAppendStatement,
    descriptor: &Descriptor,
    gate_log_blowup: u32,
    gate_num_queries: usize,
    proof: &NextgenLightClientProof,
) -> Result<bool, NextgenLightClientError> {
    let public_inputs =
        encode_nextgen_public_inputs(binary_statement, proof.binary.output_claim())?;
    require_public_length(descriptor, &public_inputs)?;
    if !verify_binary_evaluation_history_append(binary_statement, &proof.binary) {
        return Ok(false);
    }
    verify_succinct_factored_gate(
        descriptor,
        &public_inputs,
        gate_log_blowup,
        gate_num_queries,
        &proof.gate,
    )
    .map_err(Into::into)
}

fn encode_evaluation_statement(
    out: &mut Vec<Fp>,
    section: Fp,
    statement: &crate::binary_evaluation_claim::BinaryEvaluationClaimStatement,
) -> Result<(), NextgenLightClientError> {
    out.push(section);
    encode_claim(out, &statement.claim)?;
    out.push(BASIS_SECTION);
    push_len(out, statement.basis.len(), "basis length")?;
    for element in &statement.basis {
        encode_tower(out, *element);
    }
    out.push(OFFSET_SECTION);
    encode_tower(out, statement.offset);
    out.push(EVALUATION_POINT_SECTION);
    encode_tower(out, statement.evaluation_point);
    out.push(QUERY_SECTION);
    push_len(out, statement.num_queries, "binary query count")?;
    Ok(())
}

fn encode_claim(
    out: &mut Vec<Fp>,
    claim: &BinaryAdditiveRsClaim,
) -> Result<(), NextgenLightClientError> {
    out.push(CLAIM_SECTION);
    encode_root(out, &claim.root)?;
    push_u64(out, claim.coefficient_bound);
    encode_channel(out, &claim.channel_id)?;
    encode_tower(out, claim.target);
    Ok(())
}

fn encode_root(out: &mut Vec<Fp>, root: &BinaryRoot) -> Result<(), NextgenLightClientError> {
    push_bytes(out, root.as_bytes())
}

fn encode_channel(
    out: &mut Vec<Fp>,
    channel: &BinaryChannelId,
) -> Result<(), NextgenLightClientError> {
    push_bytes(out, channel.as_bytes())
}

fn encode_tower(out: &mut Vec<Fp>, value: TowerElem) {
    out.push(value.level() as Fp);
    push_u64(out, value.bits());
}

fn push_bytes(out: &mut Vec<Fp>, bytes: &[u8]) -> Result<(), NextgenLightClientError> {
    push_len(out, bytes.len(), "byte-string length")?;
    out.extend(bytes.chunks(2).map(|chunk| {
        let high = chunk.get(1).copied().unwrap_or(0);
        u16::from_le_bytes([chunk[0], high]) as Fp
    }));
    Ok(())
}

fn push_len(
    out: &mut Vec<Fp>,
    length: usize,
    name: &'static str,
) -> Result<(), NextgenLightClientError> {
    let length =
        u64::try_from(length).map_err(|_| NextgenLightClientError::EncodingOverflow(name))?;
    push_u64(out, length);
    Ok(())
}

fn push_u64(out: &mut Vec<Fp>, value: u64) {
    out.extend((0..4).map(|chunk| (value >> (16 * chunk) & 0xffff) as Fp));
}

fn require_public_length(
    descriptor: &Descriptor,
    public_inputs: &[Fp],
) -> Result<(), NextgenLightClientError> {
    let descriptor_len = descriptor.n_public as usize;
    if descriptor_len != public_inputs.len() {
        return Err(NextgenLightClientError::PublicInputLength {
            descriptor: descriptor_len,
            encoded: public_inputs.len(),
        });
    }
    Ok(())
}

fn require_public_prefix(
    descriptor: &Descriptor,
    trace: &[Fp],
    public_inputs: &[Fp],
) -> Result<(), NextgenLightClientError> {
    require_public_length(descriptor, public_inputs)?;
    if trace.get(..public_inputs.len()) != Some(public_inputs) {
        return Err(NextgenLightClientError::TracePublicPrefixMismatch);
    }
    Ok(())
}
