//! History-depth-independent append for arbitrary public GF(2^64) functionals.
//!
//! A functional claim fixes a public channel identity (label, weights, basis,
//! and offset), one additive-MLE root, and `dot(table, weights)`.  Given two
//! previously authenticated claims, this protocol derives `gamma` only after
//! both complete claims and roots are observed, commits
//! `table_out = table_left + gamma * table_right`, and proves
//! `target_out = target_left + gamma * target_right` with one
//! [`TraceLinearGf2Proof`].
//!
//! The output trace proof's successfully replayed round-zero query indices are
//! reused to open both input roots.  At each sampled pair, both low and high
//! coordinates satisfy the same affine relation.  Proofs contain no tables or
//! full evaluation words, and their size is independent of append history.
//!
//! Honest residuals:
//! * `[BINARY-FUNCTIONAL-APPEND-PROXIMITY]`: compose the landed additive-FRI
//!   theorem at explicit distance `1 - N/M` with sampled three-word affine
//!   relation testing.
//! * `[BINARY-FUNCTIONAL-APPEND-CR]`: instantiate BinaryShake Merkle collision
//!   resistance and channel-identity binding.
//! * `[BINARY-FUNCTIONAL-APPEND-ROM]`: analyze `gamma`, sumcheck challenges,
//!   and coherent queries in the cSHAKE ROM/XOF game.
//! * `[BINARY-FUNCTIONAL-APPEND-RUST-UNVERIFIED]`: the Rust affine table is
//!   unverified compute behind a generated Lean interface
//!   relation, commitment openings, and composed transcript to Lean.
//! * `[BINARY-FUNCTIONAL-APPEND-INPUT-AUTH]`: the two input root/target claims
//!   must have been authenticated by an earlier receipt or trace-linear proof.

use core::fmt;

use crate::{
    additive_fri_sampled::tower_leaf_payload,
    additive_mle_terminal::{
        additive_mle_initial_word_with_blowup, commit_additive_mle_word,
        verify_additive_mle_word_opening, AdditiveMleTerminalError,
    },
    binary_hash::{BinaryHashDomain, BinaryRoot, BinaryShake256V1, HashSuite},
    binary_merkle::{BinaryMerkleError, BinaryMerklePath, BinaryMerkleTree},
    binary_tower::{TowerElem, TowerError, MAX_LEVEL},
    binary_transcript::{BinaryShake256Transcript, TranscriptSuite},
    trace_linear_gf2::{
        commit_trace_linear_gf2_table_with_blowup, linear_functional_value_gf2,
        observe_trace_linear_gf2_initial, prove_trace_linear_gf2_from_state_with_blowup,
        verify_trace_linear_gf2_after_initial_with_queries, TraceLinearGf2Error,
        TraceLinearGf2Proof, TraceLinearGf2Statement,
    },
};

pub const BINARY_FUNCTIONAL_APPEND_PROTOCOL_LABEL: &[u8] = b"minidregg/binary-functional-append/v2";

const CHANNEL_TAG: &[u8] = b"MDRG-BINARY-FUNCTIONAL-CHANNEL-V2";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BinaryFunctionalChannelId(BinaryRoot);

impl BinaryFunctionalChannelId {
    pub const fn from_root(root: BinaryRoot) -> Self {
        Self(root)
    }

    pub const fn as_root(&self) -> &BinaryRoot {
        &self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryFunctionalClaim {
    pub channel_id: BinaryFunctionalChannelId,
    pub linear: TraceLinearGf2Statement,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryFunctionalAppendStatement {
    pub left: BinaryFunctionalClaim,
    pub right: BinaryFunctionalClaim,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryFunctionalInputPairOpening {
    pub low: TowerElem,
    pub high: TowerElem,
    pub low_path: BinaryMerklePath<BinaryRoot>,
    pub high_path: BinaryMerklePath<BinaryRoot>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryFunctionalAppendQueryOpening {
    pub left: BinaryFunctionalInputPairOpening,
    pub right: BinaryFunctionalInputPairOpening,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryFunctionalAppendProof {
    pub output: BinaryFunctionalClaim,
    pub output_trace_proof: TraceLinearGf2Proof,
    /// Same order as the output trace proof's transcript-derived queries.
    pub input_queries: Vec<BinaryFunctionalAppendQueryOpening>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinaryFunctionalAppendError {
    InvalidShape,
    IncompatibleClaims,
    ChannelMismatch,
    InputRootMismatch,
    InputTargetMismatch,
    InvalidProof,
    Mle(AdditiveMleTerminalError),
    Merkle(BinaryMerkleError),
    Trace(TraceLinearGf2Error),
    Tower(TowerError),
}

impl From<AdditiveMleTerminalError> for BinaryFunctionalAppendError {
    fn from(value: AdditiveMleTerminalError) -> Self {
        Self::Mle(value)
    }
}

impl From<BinaryMerkleError> for BinaryFunctionalAppendError {
    fn from(value: BinaryMerkleError) -> Self {
        Self::Merkle(value)
    }
}

impl From<TraceLinearGf2Error> for BinaryFunctionalAppendError {
    fn from(value: TraceLinearGf2Error) -> Self {
        Self::Trace(value)
    }
}

impl From<TowerError> for BinaryFunctionalAppendError {
    fn from(value: TowerError) -> Self {
        Self::Tower(value)
    }
}

impl fmt::Display for BinaryFunctionalAppendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidShape => write!(f, "invalid binary functional append shape"),
            Self::IncompatibleClaims => write!(f, "binary functional claims are incompatible"),
            Self::ChannelMismatch => write!(f, "binary functional channel identity mismatch"),
            Self::InputRootMismatch => write!(f, "private table does not match an input root"),
            Self::InputTargetMismatch => write!(f, "private table does not match an input target"),
            Self::InvalidProof => write!(f, "invalid binary functional append proof"),
            Self::Mle(error) => error.fmt(f),
            Self::Merkle(error) => error.fmt(f),
            Self::Trace(error) => error.fmt(f),
            Self::Tower(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for BinaryFunctionalAppendError {}

/// Canonical identity of a semantic channel and its fixed public functional.
pub fn binary_functional_channel_id(
    channel_label: &[u8],
    weights: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
) -> Result<BinaryFunctionalChannelId, BinaryFunctionalAppendError> {
    validate_public_components(weights, basis, offset)?;
    let mut payload = CHANNEL_TAG.to_vec();
    append_bytes(&mut payload, channel_label);
    append_u64(&mut payload, basis.len() as u64);
    append_u64(
        &mut payload,
        (basis.len() - weights.len().trailing_zeros() as usize) as u64,
    );
    append_bytes(&mut payload, &tower_leaf_payload(offset));
    for &beta in basis {
        append_bytes(&mut payload, &tower_leaf_payload(beta));
    }
    append_u64(&mut payload, weights.len() as u64);
    for &weight in weights {
        append_bytes(&mut payload, &tower_leaf_payload(weight));
    }
    Ok(BinaryFunctionalChannelId(BinaryShake256V1.hash_leaf(
        BinaryHashDomain::Trace,
        0,
        &payload,
    )))
}

/// Construct a claim after its table has been authenticated elsewhere.
pub fn binary_functional_claim(
    channel_label: &[u8],
    weights: &[TowerElem],
    linear: TraceLinearGf2Statement,
) -> Result<BinaryFunctionalClaim, BinaryFunctionalAppendError> {
    let channel_id =
        binary_functional_channel_id(channel_label, weights, &linear.basis, linear.offset)?;
    Ok(BinaryFunctionalClaim { channel_id, linear })
}

/// Replay the append transcript and return the challenge that combines the
/// two authenticated tables.  History composition uses this exact helper so
/// it never copies the Fiat--Shamir schedule in a second module.
pub fn derive_binary_functional_append_challenge(
    statement: &BinaryFunctionalAppendStatement,
    weights: &[TowerElem],
    channel_label: &[u8],
) -> Result<TowerElem, BinaryFunctionalAppendError> {
    validate_claims(statement, weights, channel_label)?;
    let mut transcript = BinaryShake256Transcript::new(BINARY_FUNCTIONAL_APPEND_PROTOCOL_LABEL);
    absorb_append_claims(&mut transcript, statement);
    Ok(sample_gamma(&mut transcript))
}

/// Materialize the private table represented by an honest append.  This is a
/// prover-side state transition helper, not verifier input: verification still
/// authenticates only sampled openings against the three committed roots.
pub fn fold_binary_functional_tables(
    statement: &BinaryFunctionalAppendStatement,
    left: &[TowerElem],
    right: &[TowerElem],
    weights: &[TowerElem],
    channel_label: &[u8],
) -> Result<Vec<TowerElem>, BinaryFunctionalAppendError> {
    let shape = validate_claims(statement, weights, channel_label)?;
    if left.len() != shape.table_len || right.len() != shape.table_len {
        return Err(BinaryFunctionalAppendError::InvalidShape);
    }
    affine_table(
        left,
        right,
        derive_binary_functional_append_challenge(statement, weights, channel_label)?,
    )
}

pub fn prove_binary_functional_append(
    statement: &BinaryFunctionalAppendStatement,
    left_table: &[TowerElem],
    right_table: &[TowerElem],
    weights: &[TowerElem],
    channel_label: &[u8],
) -> Result<BinaryFunctionalAppendProof, BinaryFunctionalAppendError> {
    let shape = validate_claims(statement, weights, channel_label)?;
    if left_table.len() != shape.table_len || right_table.len() != shape.table_len {
        return Err(BinaryFunctionalAppendError::InvalidShape);
    }
    let (left_word, left_tree) =
        authenticate_private_input(&statement.left, left_table, weights, &BinaryShake256V1)?;
    let (right_word, right_tree) =
        authenticate_private_input(&statement.right, right_table, weights, &BinaryShake256V1)?;

    let gamma = derive_binary_functional_append_challenge(statement, weights, channel_label)?;
    let output_table = affine_table(left_table, right_table, gamma)?;
    let mut transcript = BinaryShake256Transcript::new(BINARY_FUNCTIONAL_APPEND_PROTOCOL_LABEL);
    absorb_append_claims(&mut transcript, statement);
    let output_target = statement
        .left
        .linear
        .claimed_value
        .add(gamma.mul(statement.right.linear.claimed_value)?)?;
    let output_state = commit_trace_linear_gf2_table_with_blowup(
        &output_table,
        &statement.left.linear.basis,
        statement.left.linear.offset,
        shape.log_blowup,
        &mut transcript,
    )?;
    // This clone is exactly after the output initial root. It replays the
    // trace verifier to recover authenticated query metadata without copying
    // the trace-linear transcript schedule into this module.
    let mut query_replay_transcript = transcript.clone();
    let (output_linear, output_trace_proof) = prove_trace_linear_gf2_from_state_with_blowup(
        &output_table,
        weights,
        output_target,
        &statement.left.linear.basis,
        statement.left.linear.offset,
        shape.log_blowup,
        statement.left.linear.num_queries,
        output_state,
        &mut transcript,
    )?;
    let verification = verify_trace_linear_gf2_after_initial_with_queries(
        &output_linear,
        weights,
        &output_trace_proof,
        &mut query_replay_transcript,
    )?
    .ok_or(BinaryFunctionalAppendError::InvalidProof)?;
    let half = shape.domain_len / 2;
    let mut input_queries = Vec::with_capacity(verification.initial_pair_indices.len());
    for &pair_index in &verification.initial_pair_indices {
        input_queries.push(BinaryFunctionalAppendQueryOpening {
            left: open_input_pair(&left_word, &left_tree, pair_index, half)?,
            right: open_input_pair(&right_word, &right_tree, pair_index, half)?,
        });
    }
    Ok(BinaryFunctionalAppendProof {
        output: BinaryFunctionalClaim {
            channel_id: statement.left.channel_id,
            linear: output_linear,
        },
        output_trace_proof,
        input_queries,
    })
}

pub fn verify_binary_functional_append(
    statement: &BinaryFunctionalAppendStatement,
    weights: &[TowerElem],
    channel_label: &[u8],
    proof: &BinaryFunctionalAppendProof,
) -> Result<bool, BinaryFunctionalAppendError> {
    let shape = validate_claims(statement, weights, channel_label)?;
    let gamma = derive_binary_functional_append_challenge(statement, weights, channel_label)?;
    let mut transcript = BinaryShake256Transcript::new(BINARY_FUNCTIONAL_APPEND_PROTOCOL_LABEL);
    absorb_append_claims(&mut transcript, statement);
    let expected_target = statement
        .left
        .linear
        .claimed_value
        .add(gamma.mul(statement.right.linear.claimed_value)?)?;
    if proof.output.channel_id != statement.left.channel_id
        || proof.output.linear.basis != statement.left.linear.basis
        || proof.output.linear.offset != statement.left.linear.offset
        || proof.output.linear.log_blowup != statement.left.linear.log_blowup
        || proof.output.linear.num_queries != statement.left.linear.num_queries
        || proof.output.linear.claimed_value != expected_target
    {
        return Ok(false);
    }
    observe_trace_linear_gf2_initial(&proof.output.linear, &mut transcript)?;
    let verification = match verify_trace_linear_gf2_after_initial_with_queries(
        &proof.output.linear,
        weights,
        &proof.output_trace_proof,
        &mut transcript,
    )? {
        Some(verification) => verification,
        None => return Ok(false),
    };
    if proof.input_queries.len() != verification.initial_pair_indices.len()
        || proof.input_queries.len() != proof.output.linear.num_queries
    {
        return Ok(false);
    }

    let half = shape.domain_len / 2;
    for (query_number, (&pair_index, input)) in verification
        .initial_pair_indices
        .iter()
        .zip(&proof.input_queries)
        .enumerate()
    {
        let output = &proof.output_trace_proof.table_mle_proof.queries[query_number].rounds[0];
        if !verify_input_pair(
            &statement.left.linear,
            pair_index,
            half,
            &input.left,
            &BinaryShake256V1,
        )? || !verify_input_pair(
            &statement.right.linear,
            pair_index,
            half,
            &input.right,
            &BinaryShake256V1,
        )? {
            return Ok(false);
        }
        let expected_low = input.left.low.add(gamma.mul(input.right.low)?)?;
        let expected_high = input.left.high.add(gamma.mul(input.right.high)?)?;
        if output.low != expected_low || output.high != expected_high {
            return Ok(false);
        }
    }
    Ok(true)
}

struct ValidatedClaims {
    table_len: usize,
    domain_len: usize,
    log_blowup: u32,
}

fn validate_claims(
    statement: &BinaryFunctionalAppendStatement,
    weights: &[TowerElem],
    channel_label: &[u8],
) -> Result<ValidatedClaims, BinaryFunctionalAppendError> {
    let left = &statement.left.linear;
    let right = &statement.right.linear;
    if statement.left.channel_id != statement.right.channel_id
        || left.basis != right.basis
        || left.offset != right.offset
        || left.log_blowup != right.log_blowup
        || left.num_queries != right.num_queries
    {
        return Err(BinaryFunctionalAppendError::IncompatibleClaims);
    }
    let expected_channel =
        binary_functional_channel_id(channel_label, weights, &left.basis, left.offset)?;
    if statement.left.channel_id != expected_channel {
        return Err(BinaryFunctionalAppendError::ChannelMismatch);
    }
    let log_variables = left
        .basis
        .len()
        .checked_sub(left.log_blowup as usize)
        .ok_or(BinaryFunctionalAppendError::InvalidShape)?;
    let table_len = checked_table_len(log_variables)?;
    let domain_len = checked_table_len(left.basis.len())?;
    if weights.len() != table_len
        || left.claimed_value.level() != MAX_LEVEL
        || right.claimed_value.level() != MAX_LEVEL
        || left.num_queries == 0
    {
        return Err(BinaryFunctionalAppendError::InvalidShape);
    }
    Ok(ValidatedClaims {
        table_len,
        domain_len,
        log_blowup: left.log_blowup,
    })
}

fn authenticate_private_input<H: HashSuite<Root = BinaryRoot>>(
    claim: &BinaryFunctionalClaim,
    table: &[TowerElem],
    weights: &[TowerElem],
    hash: &H,
) -> Result<(Vec<TowerElem>, BinaryMerkleTree<BinaryRoot>), BinaryFunctionalAppendError> {
    if linear_functional_value_gf2(table, weights)? != claim.linear.claimed_value {
        return Err(BinaryFunctionalAppendError::InputTargetMismatch);
    }
    let word = additive_mle_initial_word_with_blowup(
        table,
        &claim.linear.basis,
        claim.linear.offset,
        claim.linear.log_blowup,
    )?;
    let tree = commit_additive_mle_word(&word, hash)?;
    if tree.root() != claim.linear.table_root {
        return Err(BinaryFunctionalAppendError::InputRootMismatch);
    }
    Ok((word, tree))
}

fn affine_table(
    left: &[TowerElem],
    right: &[TowerElem],
    gamma: TowerElem,
) -> Result<Vec<TowerElem>, BinaryFunctionalAppendError> {
    if left.len() != right.len() {
        return Err(BinaryFunctionalAppendError::InvalidShape);
    }
    left.iter()
        .copied()
        .zip(right.iter().copied())
        .map(|(left, right)| Ok(left.add(gamma.mul(right)?)?))
        .collect()
}

fn open_input_pair(
    word: &[TowerElem],
    tree: &BinaryMerkleTree<BinaryRoot>,
    pair_index: usize,
    half: usize,
) -> Result<BinaryFunctionalInputPairOpening, BinaryFunctionalAppendError> {
    if pair_index >= half || word.len() != 2 * half {
        return Err(BinaryFunctionalAppendError::InvalidShape);
    }
    Ok(BinaryFunctionalInputPairOpening {
        low: word[pair_index],
        high: word[half + pair_index],
        low_path: tree.open(pair_index)?,
        high_path: tree.open(half + pair_index)?,
    })
}

fn verify_input_pair<H: HashSuite<Root = BinaryRoot>>(
    statement: &TraceLinearGf2Statement,
    pair_index: usize,
    half: usize,
    opening: &BinaryFunctionalInputPairOpening,
    hash: &H,
) -> Result<bool, BinaryFunctionalAppendError> {
    let word_len = 2 * half;
    Ok(verify_additive_mle_word_opening(
        hash,
        word_len,
        pair_index,
        opening.low,
        &opening.low_path,
        &statement.table_root,
    )? && verify_additive_mle_word_opening(
        hash,
        word_len,
        half + pair_index,
        opening.high,
        &opening.high_path,
        &statement.table_root,
    )?)
}

fn absorb_append_claims(
    transcript: &mut BinaryShake256Transcript,
    statement: &BinaryFunctionalAppendStatement,
) {
    transcript.observe_bytes(
        b"binary-functional-append/protocol",
        BINARY_FUNCTIONAL_APPEND_PROTOCOL_LABEL,
    );
    absorb_claim(transcript, b"left", &statement.left);
    absorb_claim(transcript, b"right", &statement.right);
}

fn absorb_claim(
    transcript: &mut BinaryShake256Transcript,
    side: &[u8],
    claim: &BinaryFunctionalClaim,
) {
    transcript.observe_bytes(b"binary-functional-append/side", side);
    transcript.observe_root(
        b"binary-functional-append/channel",
        claim.channel_id.as_root(),
    );
    transcript.observe_root(
        b"binary-functional-append/table-root",
        &claim.linear.table_root,
    );
    transcript.observe_u64(
        b"binary-functional-append/log-variables",
        (claim.linear.basis.len() - claim.linear.log_blowup as usize) as u64,
    );
    transcript.observe_u64(
        b"binary-functional-append/log-blowup",
        claim.linear.log_blowup as u64,
    );
    transcript.observe_bytes(
        b"binary-functional-append/offset",
        &tower_leaf_payload(claim.linear.offset),
    );
    for (index, &beta) in claim.linear.basis.iter().enumerate() {
        transcript.observe_u64(b"binary-functional-append/basis-index", index as u64);
        transcript.observe_bytes(
            b"binary-functional-append/basis-value",
            &tower_leaf_payload(beta),
        );
    }
    transcript.observe_bytes(
        b"binary-functional-append/target",
        &tower_leaf_payload(claim.linear.claimed_value),
    );
    transcript.observe_u64(
        b"binary-functional-append/num-queries",
        claim.linear.num_queries as u64,
    );
}

fn sample_gamma(transcript: &mut BinaryShake256Transcript) -> TowerElem {
    TowerElem::new(
        MAX_LEVEL,
        transcript.sample_gf2_64(b"binary-functional-append/gamma"),
    )
    .expect("every u64 is canonical in GF(2^64)")
}

fn validate_public_components(
    weights: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
) -> Result<(), BinaryFunctionalAppendError> {
    if weights.len() < 2
        || !weights.len().is_power_of_two()
        || basis.len() < weights.len().trailing_zeros() as usize
        || weights
            .iter()
            .chain(basis)
            .any(|value| value.level() != MAX_LEVEL)
        || offset.level() != MAX_LEVEL
    {
        return Err(BinaryFunctionalAppendError::InvalidShape);
    }
    Ok(())
}

fn checked_table_len(log_variables: usize) -> Result<usize, BinaryFunctionalAppendError> {
    if log_variables == 0 {
        return Err(BinaryFunctionalAppendError::InvalidShape);
    }
    1usize
        .checked_shl(log_variables as u32)
        .ok_or(BinaryFunctionalAppendError::InvalidShape)
}

fn append_u64(payload: &mut Vec<u8>, value: u64) {
    payload.extend_from_slice(&value.to_le_bytes());
}

fn append_bytes(payload: &mut Vec<u8>, bytes: &[u8]) {
    append_u64(payload, bytes.len() as u64);
    payload.extend_from_slice(bytes);
}
