//! Proof-verified nodes for the semantic history ABI.
//!
//! [`HistoryEnvelope`] deliberately validates only the shape of a heterogeneous
//! receipt.  This module closes the first concrete native-proof seam: one node
//! carries an actual [`FunctionalNextgenReceiptProof`], and its envelope is
//! deterministically reconstructed from the exact public statement accepted by
//! that proof.  A verifier accepts only after checking both the binary
//! functional append and the Ext6 factored-gate proof, then comparing the whole
//! canonical envelope and its previous-node seam.
//!
//! This is an authenticated, uncompressed history node.  It is not WARP/FACS,
//! recursive compression, or heterogeneous accumulator extraction.  The GF(2)
//! functional root is the one real append accumulator in this node; Ext6 is the
//! proof backend for the attached gate relation, not a fictitious second fold
//! lane.  `[PCH-OUTER-ACCUMULATOR]` is the remaining replacement of a chain of
//! these verified nodes by an unbounded hiding/knowledge-sound accumulator.

use core::fmt;

use sha3::{Digest as _, Sha3_256};

use crate::{
    binary_functional_append::{
        BinaryFunctionalAppendStatement, BinaryFunctionalClaim,
        BINARY_FUNCTIONAL_APPEND_PROTOCOL_LABEL,
    },
    binary_hash::BinaryRoot,
    binary_tower::{TowerElem, MAX_LEVEL},
    descriptor::{Descriptor, GateOp, Wire},
    functional_nextgen_receipt::{
        encode_functional_nextgen_public_inputs, prove_functional_nextgen_receipt,
        verify_functional_nextgen_receipt, FunctionalNextgenReceiptError,
        FunctionalNextgenReceiptProof,
    },
    semantic_receipt::{
        semantic_id, validate_history_append, AlgebraId, CommitmentRef, FoldCompatibility,
        HistoryEnvelope, LaneAccumulatorKey, LaneEnvelope, NativeStatement, SemanticId,
        SemanticReceiptError, ValueRef, SEMANTIC_RECEIPT_VERSION,
    },
};

const TOWER_ID_LABEL: &[u8] = b"tower/fan-paar/gf2-64/v1";
const LANE_LABEL: &[u8] = b"lane/proof-carrying-functional-history/v1";
const RELATION_LABEL: &[u8] = b"relation/functional-nextgen-transition/v1";
const ACCUMULATOR_LABEL: &[u8] = b"accumulator/binary-functional-root/v1";
const CODE_LABEL: &[u8] = b"code/additive-lch-rate-bearing/v1";
const TRANSCRIPT_LABEL: &[u8] = b"transcript/binary-shake256/v1";

/// One proof-bearing node.  The proof is intentionally not serialized through
/// the semantic ABI; the envelope is the canonical public statement, while a
/// proof codec/version belongs to the selected native proof suite.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofCarryingHistoryNode {
    pub envelope: HistoryEnvelope,
    pub proof: FunctionalNextgenReceiptProof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofCarryingHistoryError {
    Descriptor(String),
    InvalidTowerValue,
    DomainOverflow,
    Semantic(SemanticReceiptError),
    Native(FunctionalNextgenReceiptError),
}

impl From<SemanticReceiptError> for ProofCarryingHistoryError {
    fn from(value: SemanticReceiptError) -> Self {
        Self::Semantic(value)
    }
}

impl From<FunctionalNextgenReceiptError> for ProofCarryingHistoryError {
    fn from(value: FunctionalNextgenReceiptError) -> Self {
        Self::Native(value)
    }
}

impl fmt::Display for ProofCarryingHistoryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Descriptor(message) => write!(f, "proof-carrying history descriptor: {message}"),
            Self::InvalidTowerValue => write!(f, "proof-carrying history requires GF(2^64) values"),
            Self::DomainOverflow => write!(f, "proof-carrying history domain does not fit u64"),
            Self::Semantic(error) => error.fmt(f),
            Self::Native(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for ProofCarryingHistoryError {}

/// Produce a real native proof and bind it into the next canonical history
/// node.  `previous` is the already-verified predecessor envelope, if any.
#[allow(clippy::too_many_arguments)]
pub fn prove_functional_history_node(
    previous: Option<&HistoryEnvelope>,
    history_domain: SemanticId,
    turn_id: SemanticId,
    statement: &BinaryFunctionalAppendStatement,
    weights: &[TowerElem],
    channel_label: &[u8],
    left_table: &[TowerElem],
    right_table: &[TowerElem],
    descriptor: &Descriptor,
    gate_trace: &[u64],
    gate_log_blowup: u32,
    gate_num_queries: usize,
) -> Result<ProofCarryingHistoryNode, ProofCarryingHistoryError> {
    let proof = prove_functional_nextgen_receipt(
        statement,
        weights,
        channel_label,
        left_table,
        right_table,
        descriptor,
        gate_trace,
        gate_log_blowup,
        gate_num_queries,
    )?;
    let envelope = functional_history_envelope(
        previous,
        history_domain,
        turn_id,
        statement,
        weights,
        channel_label,
        descriptor,
        gate_log_blowup,
        gate_num_queries,
        &proof,
    )?;
    Ok(ProofCarryingHistoryNode { envelope, proof })
}

/// Verify the native conjunction first, then reconstruct the complete public
/// envelope and check the predecessor seam.  Returning `Ok(false)` means a
/// well-formed verification attempt did not authenticate this node.
#[allow(clippy::too_many_arguments)]
pub fn verify_functional_history_node(
    previous: Option<&HistoryEnvelope>,
    history_domain: SemanticId,
    turn_id: SemanticId,
    statement: &BinaryFunctionalAppendStatement,
    weights: &[TowerElem],
    channel_label: &[u8],
    descriptor: &Descriptor,
    gate_log_blowup: u32,
    gate_num_queries: usize,
    node: &ProofCarryingHistoryNode,
) -> Result<bool, ProofCarryingHistoryError> {
    if !verify_functional_nextgen_receipt(
        statement,
        weights,
        channel_label,
        descriptor,
        gate_log_blowup,
        gate_num_queries,
        &node.proof,
    )? {
        return Ok(false);
    }
    let expected = functional_history_envelope(
        previous,
        history_domain,
        turn_id,
        statement,
        weights,
        channel_label,
        descriptor,
        gate_log_blowup,
        gate_num_queries,
        &node.proof,
    )?;
    Ok(node.envelope == expected)
}

#[allow(clippy::too_many_arguments)]
fn functional_history_envelope(
    previous: Option<&HistoryEnvelope>,
    history_domain: SemanticId,
    turn_id: SemanticId,
    statement: &BinaryFunctionalAppendStatement,
    weights: &[TowerElem],
    channel_label: &[u8],
    descriptor: &Descriptor,
    gate_log_blowup: u32,
    gate_num_queries: usize,
    proof: &FunctionalNextgenReceiptProof,
) -> Result<HistoryEnvelope, ProofCarryingHistoryError> {
    descriptor
        .validate()
        .map_err(ProofCarryingHistoryError::Descriptor)?;
    let output = &proof.functional.output;
    validate_tower_boundary(statement, output, weights)?;
    let algebra = AlgebraId::gf2_tower(64, semantic_id(TOWER_ID_LABEL));
    let scheme_id = semantic_id(ACCUMULATOR_LABEL);
    let pre = root_commitment(&algebra, scheme_id, &statement.left.linear.table_root);
    let post = root_commitment(&algebra, scheme_id, &output.linear.table_root);
    let right_root = ValueRef::public(
        semantic_id(b"value/functional-history/right-root/v1"),
        algebra.clone(),
        semantic_id(b"representation/binary-root-48/v1"),
        statement.right.linear.table_root.as_bytes().to_vec(),
    );
    let public_inputs = encode_functional_nextgen_public_inputs(
        statement,
        output,
        weights,
        channel_label,
        gate_log_blowup,
        gate_num_queries,
    )?;
    let public_boundary = ValueRef::public(
        semantic_id(b"value/functional-history/public-boundary/v1"),
        algebra.clone(),
        semantic_id(b"representation/babybear-u64-le-vector/v1"),
        encode_u64_slice(&public_inputs),
    );
    let descriptor_value = ValueRef::public(
        semantic_id(b"value/functional-history/descriptor/v1"),
        algebra.clone(),
        semantic_id(b"representation/descriptor-canonical-v1"),
        encode_descriptor(descriptor),
    );
    let trace_root = ValueRef::public(
        semantic_id(b"value/functional-history/gate-trace-root/v1"),
        algebra.clone(),
        semantic_id(b"representation/binary-root-48/v1"),
        proof.gate.trace_root.as_bytes().to_vec(),
    );
    let weights_value = ValueRef::public(
        semantic_id(b"value/functional-history/weights/v1"),
        algebra.clone(),
        semantic_id(b"representation/gf2-64-vector-v1"),
        encode_tower_slice(weights),
    );
    let channel_value = ValueRef::public(
        semantic_id(b"value/functional-history/channel-label/v1"),
        algebra.clone(),
        semantic_id(b"representation/raw-bytes/v1"),
        channel_label.to_vec(),
    );
    let domain_size = 1u64
        .checked_shl(statement.left.linear.basis.len() as u32)
        .ok_or(ProofCarryingHistoryError::DomainOverflow)?;
    let rate_denominator = 1u64
        .checked_shl(statement.left.linear.log_blowup)
        .ok_or(ProofCarryingHistoryError::DomainOverflow)?;
    let channel_shape = digest(
        b"minidregg/proof-carrying-history/shape/v1",
        statement.left.channel_id.as_root().as_bytes(),
    );
    let relation_id = semantic_id(RELATION_LABEL);
    let lane = LaneEnvelope {
        key: LaneAccumulatorKey {
            lane_id: semantic_id(LANE_LABEL),
            algebra: algebra.clone(),
            native_relation_id: relation_id,
            accumulator_scheme_id: scheme_id,
            fold: FoldCompatibility {
                protocol_id: semantic_id(BINARY_FUNCTIONAL_APPEND_PROTOCOL_LABEL),
                code_id: semantic_id(CODE_LABEL),
                transcript_id: semantic_id(TRANSCRIPT_LABEL),
                constraint_shape_id: channel_shape,
                domain_size,
                rate_numerator: 1,
                rate_denominator,
            },
        },
        statement: NativeStatement {
            algebra,
            relation_id,
            pre_state: pre.clone(),
            post_state: post.clone(),
            values: vec![
                right_root,
                public_boundary,
                descriptor_value,
                trace_root,
                weights_value,
                channel_value,
            ],
        },
        input_accumulator: pre,
        output_accumulator: post,
    };
    let (sequence, previous_envelope) = match previous {
        None => (0, None),
        Some(previous) => (
            previous
                .sequence
                .checked_add(1)
                .ok_or(ProofCarryingHistoryError::DomainOverflow)?,
            Some(previous.envelope_id()?),
        ),
    };
    let envelope = HistoryEnvelope {
        version: SEMANTIC_RECEIPT_VERSION,
        history_domain,
        sequence,
        previous_envelope,
        turn_id,
        lanes: vec![lane],
        repr_equalities: vec![],
    }
    .canonicalize()?;
    if let Some(previous) = previous {
        validate_history_append(previous, &envelope)?;
    }
    Ok(envelope)
}

fn validate_tower_boundary(
    statement: &BinaryFunctionalAppendStatement,
    output: &BinaryFunctionalClaim,
    weights: &[TowerElem],
) -> Result<(), ProofCarryingHistoryError> {
    let values = weights
        .iter()
        .chain(&statement.left.linear.basis)
        .chain(&statement.right.linear.basis)
        .chain(&output.linear.basis)
        .chain([
            &statement.left.linear.offset,
            &statement.right.linear.offset,
            &output.linear.offset,
            &statement.left.linear.claimed_value,
            &statement.right.linear.claimed_value,
            &output.linear.claimed_value,
        ]);
    if values.into_iter().any(|value| value.level() != MAX_LEVEL) {
        return Err(ProofCarryingHistoryError::InvalidTowerValue);
    }
    Ok(())
}

fn root_commitment(algebra: &AlgebraId, scheme_id: SemanticId, root: &BinaryRoot) -> CommitmentRef {
    CommitmentRef {
        algebra: algebra.clone(),
        scheme_id,
        bytes: root.as_bytes().to_vec(),
    }
}

fn encode_tower_slice(values: &[TowerElem]) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + 8 * values.len());
    out.extend_from_slice(&(values.len() as u64).to_le_bytes());
    for value in values {
        out.extend_from_slice(&value.bits().to_le_bytes());
    }
    out
}

fn encode_u64_slice(values: &[u64]) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + 8 * values.len());
    out.extend_from_slice(&(values.len() as u64).to_le_bytes());
    for value in values {
        out.extend_from_slice(&value.to_le_bytes());
    }
    out
}

fn encode_descriptor(descriptor: &Descriptor) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(b"MDRG-DESCRIPTOR-V1");
    out.extend_from_slice(&descriptor.p.to_le_bytes());
    out.extend_from_slice(&descriptor.n_public.to_le_bytes());
    out.extend_from_slice(&descriptor.n_vars.to_le_bytes());
    out.extend_from_slice(&descriptor.n_wires.to_le_bytes());
    out.extend_from_slice(&(descriptor.gates.len() as u64).to_le_bytes());
    for gate in &descriptor.gates {
        out.push(match gate.op {
            GateOp::Add => 0,
            GateOp::Mul => 1,
        });
        encode_wire(&mut out, gate.a);
        encode_wire(&mut out, gate.b);
        out.extend_from_slice(&gate.out.to_le_bytes());
    }
    out.extend_from_slice(&(descriptor.zeros.len() as u64).to_le_bytes());
    for &wire in &descriptor.zeros {
        encode_wire(&mut out, wire);
    }
    out
}

fn encode_wire(out: &mut Vec<u8>, wire: Wire) {
    match wire {
        Wire::Const(value) => {
            out.push(0);
            out.extend_from_slice(&value.to_le_bytes());
        }
        Wire::Wire(index) => {
            out.push(1);
            out.extend_from_slice(&index.to_le_bytes());
        }
    }
}

fn digest(domain: &[u8], payload: &[u8]) -> SemanticId {
    let mut hash = Sha3_256::new();
    hash.update((domain.len() as u64).to_le_bytes());
    hash.update(domain);
    hash.update((payload.len() as u64).to_le_bytes());
    hash.update(payload);
    hash.finalize().into()
}
