//! Conjunction of one rate-bearing arbitrary-functional binary append and one
//! succinct factored-gate proof.
//!
//! This is a conjunction, not recursive compression: both component proofs
//! are carried. The join is a canonical BabyBear public-prefix encoding of the
//! two complete input functional claims, the append-derived output claim, the
//! fixed channel identity, explicit rate/basis/offset/query profile, and a
//! verifier-recomputed identity of the public weights. The weights themselves
//! remain public verifier inputs; the channel identity cryptographically binds
//! their exact ordered vector.
//!
//! Proving is deliberately ordered append -> append re-verification -> public
//! encoding -> gate. Verification reconstructs the output claim from the proof,
//! checks the functional append first, and only then accepts the gate proof.
//! Component collision-resistance, proximity, ROM/XOF, input-authentication,
//! and unverified-Rust/generated-control assumptions remain; their conjunction under shared
//! cryptographic assumptions is `[FUNCTIONAL-NEXTGEN-CONJUNCTION]`.

use core::fmt;

use crate::{
    binary_functional_append::{
        binary_functional_channel_id, prove_binary_functional_append,
        verify_binary_functional_append, BinaryFunctionalAppendError, BinaryFunctionalAppendProof,
        BinaryFunctionalAppendStatement, BinaryFunctionalChannelId, BinaryFunctionalClaim,
        BINARY_FUNCTIONAL_APPEND_PROTOCOL_LABEL,
    },
    binary_hash::{BinaryRoot, BinaryShake256V1, HashSuite},
    binary_tower::{TowerElem, MAX_LEVEL},
    descriptor::{Descriptor, Fp},
    field4::P,
    succinct_factored_gate::{
        prove_succinct_factored_gate, verify_succinct_factored_gate, SuccinctFactoredGateError,
        SuccinctFactoredGateProof,
    },
};

pub const FUNCTIONAL_NEXTGEN_PUBLIC_INPUT_ENCODING_VERSION: u64 = 1;

const ENCODING_TAG: &[u8] = b"minidregg/functional-nextgen-receipt/public-inputs/v1";
const TOWER_SUITE_TAG: &[u8] = b"FanPaarBinaryTower/GF2^64/level6/v1";

const HEADER_SECTION: Fp = 1;
const WEIGHTS_IDENTITY_SECTION: Fp = 2;
const QUERY_PROFILE_SECTION: Fp = 3;
const LEFT_CLAIM_SECTION: Fp = 4;
const RIGHT_CLAIM_SECTION: Fp = 5;
const OUTPUT_CLAIM_SECTION: Fp = 6;
const CHANNEL_SECTION: Fp = 7;
const LINEAR_STATEMENT_SECTION: Fp = 8;
const BASIS_SECTION: Fp = 9;
const OFFSET_SECTION: Fp = 10;
const TARGET_SECTION: Fp = 11;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionalNextgenReceiptProof {
    pub functional: BinaryFunctionalAppendProof,
    pub gate: SuccinctFactoredGateProof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FunctionalNextgenReceiptError {
    EncodingOverflow(&'static str),
    PublicInputLength { descriptor: usize, encoded: usize },
    TracePublicPrefixMismatch,
    FunctionalReverificationFailed,
    Functional(BinaryFunctionalAppendError),
    Gate(SuccinctFactoredGateError),
}

impl From<BinaryFunctionalAppendError> for FunctionalNextgenReceiptError {
    fn from(value: BinaryFunctionalAppendError) -> Self {
        Self::Functional(value)
    }
}

impl From<SuccinctFactoredGateError> for FunctionalNextgenReceiptError {
    fn from(value: SuccinctFactoredGateError) -> Self {
        Self::Gate(value)
    }
}

impl fmt::Display for FunctionalNextgenReceiptError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EncodingOverflow(name) => {
                write!(f, "functional nextgen encoding {name} does not fit u64")
            }
            Self::PublicInputLength {
                descriptor,
                encoded,
            } => write!(
                f,
                "gate descriptor has {descriptor} public inputs, functional encoding has {encoded}"
            ),
            Self::TracePublicPrefixMismatch => write!(
                f,
                "private gate trace does not start with the functional public encoding"
            ),
            Self::FunctionalReverificationFailed => {
                write!(f, "newly produced functional append failed re-verification")
            }
            Self::Functional(error) => error.fmt(f),
            Self::Gate(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for FunctionalNextgenReceiptError {}

/// Canonical BabyBear encoding of the entire public conjunction boundary.
#[allow(clippy::too_many_arguments)]
pub fn encode_functional_nextgen_public_inputs(
    statement: &BinaryFunctionalAppendStatement,
    output: &BinaryFunctionalClaim,
    weights: &[TowerElem],
    channel_label: &[u8],
    gate_log_blowup: u32,
    gate_num_queries: usize,
) -> Result<Vec<Fp>, FunctionalNextgenReceiptError> {
    let weights_identity = binary_functional_channel_id(
        channel_label,
        weights,
        &statement.left.linear.basis,
        statement.left.linear.offset,
    )?;
    let mut body = Vec::new();
    body.push(HEADER_SECTION);
    push_bytes(&mut body, ENCODING_TAG)?;
    push_bytes(&mut body, <BinaryShake256V1 as HashSuite>::SUITE_ID)?;
    push_bytes(&mut body, BINARY_FUNCTIONAL_APPEND_PROTOCOL_LABEL)?;
    push_bytes(&mut body, TOWER_SUITE_TAG)?;

    body.push(WEIGHTS_IDENTITY_SECTION);
    push_len(&mut body, weights.len(), "weights length")?;
    push_bytes(&mut body, channel_label)?;
    encode_channel(&mut body, &weights_identity)?;

    body.push(QUERY_PROFILE_SECTION);
    push_u64(&mut body, statement.left.linear.num_queries as u64);
    push_u64(&mut body, statement.left.linear.log_blowup as u64);
    push_u64(&mut body, gate_num_queries as u64);
    push_u64(&mut body, gate_log_blowup as u64);

    encode_functional_claim(&mut body, LEFT_CLAIM_SECTION, &statement.left)?;
    encode_functional_claim(&mut body, RIGHT_CLAIM_SECTION, &statement.right)?;
    encode_functional_claim(&mut body, OUTPUT_CLAIM_SECTION, output)?;

    let body_len = u64::try_from(body.len())
        .map_err(|_| FunctionalNextgenReceiptError::EncodingOverflow("body length"))?;
    let mut encoded = Vec::with_capacity(body.len() + 5);
    encoded.push(FUNCTIONAL_NEXTGEN_PUBLIC_INPUT_ENCODING_VERSION);
    push_u64(&mut encoded, body_len);
    encoded.extend(body);
    debug_assert!(encoded.iter().all(|&cell| cell < P));
    Ok(encoded)
}

/// Produce and reverify the functional append before committing it into the
/// gate trace's exact public prefix.
#[allow(clippy::too_many_arguments)]
pub fn prove_functional_nextgen_receipt(
    functional_statement: &BinaryFunctionalAppendStatement,
    weights: &[TowerElem],
    channel_label: &[u8],
    left_table: &[TowerElem],
    right_table: &[TowerElem],
    descriptor: &Descriptor,
    gate_trace: &[Fp],
    gate_log_blowup: u32,
    gate_num_queries: usize,
) -> Result<FunctionalNextgenReceiptProof, FunctionalNextgenReceiptError> {
    let functional = prove_binary_functional_append(
        functional_statement,
        left_table,
        right_table,
        weights,
        channel_label,
    )?;
    if !verify_binary_functional_append(functional_statement, weights, channel_label, &functional)?
    {
        return Err(FunctionalNextgenReceiptError::FunctionalReverificationFailed);
    }
    let public_inputs = encode_functional_nextgen_public_inputs(
        functional_statement,
        &functional.output,
        weights,
        channel_label,
        gate_log_blowup,
        gate_num_queries,
    )?;
    require_public_prefix(descriptor, gate_trace, &public_inputs)?;
    let gate = prove_succinct_factored_gate(
        descriptor,
        &public_inputs,
        gate_trace,
        gate_log_blowup,
        gate_num_queries,
    )?;
    Ok(FunctionalNextgenReceiptProof { functional, gate })
}

/// Reconstruct the proof-carried output claim, verify the arbitrary functional
/// transition, then verify the gate against the exact same canonical cells.
pub fn verify_functional_nextgen_receipt(
    functional_statement: &BinaryFunctionalAppendStatement,
    weights: &[TowerElem],
    channel_label: &[u8],
    descriptor: &Descriptor,
    gate_log_blowup: u32,
    gate_num_queries: usize,
    proof: &FunctionalNextgenReceiptProof,
) -> Result<bool, FunctionalNextgenReceiptError> {
    let public_inputs = encode_functional_nextgen_public_inputs(
        functional_statement,
        &proof.functional.output,
        weights,
        channel_label,
        gate_log_blowup,
        gate_num_queries,
    )?;
    require_public_length(descriptor, &public_inputs)?;
    if !verify_binary_functional_append(
        functional_statement,
        weights,
        channel_label,
        &proof.functional,
    )? {
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

fn encode_functional_claim(
    out: &mut Vec<Fp>,
    section: Fp,
    claim: &BinaryFunctionalClaim,
) -> Result<(), FunctionalNextgenReceiptError> {
    out.push(section);
    out.push(CHANNEL_SECTION);
    encode_channel(out, &claim.channel_id)?;
    out.push(LINEAR_STATEMENT_SECTION);
    encode_root(out, &claim.linear.table_root)?;
    push_u64(out, claim.linear.log_blowup as u64);
    out.push(BASIS_SECTION);
    push_len(out, claim.linear.basis.len(), "basis length")?;
    for &beta in &claim.linear.basis {
        encode_tower(out, beta);
    }
    out.push(OFFSET_SECTION);
    encode_tower(out, claim.linear.offset);
    out.push(TARGET_SECTION);
    encode_tower(out, claim.linear.claimed_value);
    push_len(out, claim.linear.num_queries, "functional query count")?;
    Ok(())
}

fn encode_root(out: &mut Vec<Fp>, root: &BinaryRoot) -> Result<(), FunctionalNextgenReceiptError> {
    push_bytes(out, root.as_bytes())
}

fn encode_channel(
    out: &mut Vec<Fp>,
    channel: &BinaryFunctionalChannelId,
) -> Result<(), FunctionalNextgenReceiptError> {
    encode_root(out, channel.as_root())
}

fn encode_tower(out: &mut Vec<Fp>, value: TowerElem) {
    debug_assert_eq!(value.level(), MAX_LEVEL);
    out.push(value.level() as Fp);
    push_u64(out, value.bits());
}

fn push_bytes(out: &mut Vec<Fp>, bytes: &[u8]) -> Result<(), FunctionalNextgenReceiptError> {
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
) -> Result<(), FunctionalNextgenReceiptError> {
    let length =
        u64::try_from(length).map_err(|_| FunctionalNextgenReceiptError::EncodingOverflow(name))?;
    push_u64(out, length);
    Ok(())
}

fn push_u64(out: &mut Vec<Fp>, value: u64) {
    out.extend((0..4).map(|chunk| (value >> (16 * chunk) & 0xffff) as Fp));
}

fn require_public_length(
    descriptor: &Descriptor,
    public_inputs: &[Fp],
) -> Result<(), FunctionalNextgenReceiptError> {
    let descriptor_len = descriptor.n_public as usize;
    if descriptor_len != public_inputs.len() {
        return Err(FunctionalNextgenReceiptError::PublicInputLength {
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
) -> Result<(), FunctionalNextgenReceiptError> {
    require_public_length(descriptor, public_inputs)?;
    if trace.get(..public_inputs.len()) != Some(public_inputs) {
        return Err(FunctionalNextgenReceiptError::TracePublicPrefixMismatch);
    }
    Ok(())
}
