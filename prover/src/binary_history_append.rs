//! One sampled binary proof-carrying-history append.
//!
//! Two additive-RS evaluation words are already named by binary Merkle roots.
//! The prover supplies both words and their novel-basis coefficients.  This
//! module checks those witnesses, derives `gamma in GF(2^64)` only after both
//! roots and their claim metadata have entered a byte-native transcript, and
//! commits the coordinatewise fold
//!
//! ```text
//! folded[i] = left[i] + gamma * right[i].
//! ```
//!
//! The same continuing transcript drives [`crate::additive_fri_sampled`].  Its
//! initial pair openings authenticate the folded coordinates; this proof adds
//! the matching left/right paths and checks the two coordinate equations at
//! every sampled pair.  Consequently no complete word is carried in the proof
//! and its size is independent of history depth.
//!
//! Honest residuals:
//! * `[BINARY-APPEND-linear-channel]`: channel identity and the target
//!   recurrence are proved here, but this layer does not yet retire the
//!   `dot(weights, word) = target` opening/link relation.
//! * `[BINARY-APPEND-LDT-rate]`: `output_claim.coefficient_bound` is now also
//!   the starting degree field of `SampledFriStatement` and is transcript
//!   bound immediately before the first FRI root.  The remaining obligation is
//!   the formal additive proximity theorem at that degree schedule, inherited
//!   from the sampled layer's `[ANTT-FRI-PROXIMITY]` residual.
//! * `[BINARY-APPEND-RUST-UNVERIFIED]`, `[BINARY-APPEND-XOF]`, and
//!   `[BINARY-APPEND-COMMIT-CR]`: unverified Rust compute and the cSHAKE/Merkle
//!   assumptions remain outside this executable join.

use core::fmt;

use crate::{
    additive_fri_sampled::{
        prove_sampled, tower_leaf_payload, verify_sampled, ChallengeSource, SampledFriError,
        SampledFriProof, SampledFriStatement,
    },
    additive_ntt::{forward, AdditiveNttError},
    binary_hash::{BinaryHashDomain, BinaryRoot, BinaryShake256V1, HashSuite},
    binary_merkle::{verify_binary_opening, BinaryMerkleError, BinaryMerklePath, BinaryMerkleTree},
    binary_tower::{TowerElem, TowerError, MAX_LEVEL},
    binary_transcript::{BinaryShake256Transcript, TranscriptSuite},
};

const PROTOCOL_LABEL: &[u8] = b"minidregg/binary-history-append/v1";

/// Fixed width keeps channel identity independent of accumulated history depth.
/// Forty-eight bytes match the binary suite's commitment roots, avoiding the
/// 128-bit generic collision ceiling of a 32-byte identifier.
pub const CHANNEL_ID_BYTES: usize = 48;

/// A typed identifier for one linear accumulator channel.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BinaryChannelId([u8; CHANNEL_ID_BYTES]);

impl BinaryChannelId {
    pub const fn from_bytes(bytes: [u8; CHANNEL_ID_BYTES]) -> Self {
        Self(bytes)
    }

    pub const fn as_bytes(&self) -> &[u8; CHANNEL_ID_BYTES] {
        &self.0
    }
}

/// One previously committed additive-RS claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryAdditiveRsClaim {
    pub root: BinaryRoot,
    /// Number of potentially nonzero novel-basis coefficients.
    pub coefficient_bound: u64,
    pub channel_id: BinaryChannelId,
    pub target: TowerElem,
}

/// Public inputs for one append.  Both words use this exact affine domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryHistoryAppendStatement {
    pub left: BinaryAdditiveRsClaim,
    pub right: BinaryAdditiveRsClaim,
    pub basis: Vec<TowerElem>,
    pub offset: TowerElem,
    pub num_queries: usize,
}

/// Left/right openings for the pair already opened by sampled FRI.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryRelationPairOpening {
    pub left_low: TowerElem,
    pub left_high: TowerElem,
    pub right_low: TowerElem,
    pub right_high: TowerElem,
    pub left_low_path: BinaryMerklePath<BinaryRoot>,
    pub left_high_path: BinaryMerklePath<BinaryRoot>,
    pub right_low_path: BinaryMerklePath<BinaryRoot>,
    pub right_high_path: BinaryMerklePath<BinaryRoot>,
}

/// Succinct-in-history append object.  The first FRI root is the new folded
/// word root and can be carried into the next append.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryHistoryAppendProof {
    pub output_claim: BinaryAdditiveRsClaim,
    pub fri_proof: SampledFriProof,
    pub relation_openings: Vec<BinaryRelationPairOpening>,
}

impl BinaryHistoryAppendProof {
    pub const fn output_root(&self) -> BinaryRoot {
        self.output_claim.root
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinaryHistoryAppendError {
    Tower(TowerError),
    Transform(AdditiveNttError),
    Merkle(BinaryMerkleError),
    Fri(SampledFriError),
    InvalidStatement,
    ChannelMismatch,
    OutputClaimMismatch,
    InvalidWitnessShape,
    CoefficientBoundViolation(&'static str),
    WordCoefficientMismatch(&'static str),
    CommitmentMismatch(&'static str),
    FoldedWordMismatch,
    InvalidProofShape,
    MissingQuerySchedule,
    InvalidOpening {
        query: usize,
        side: &'static str,
    },
    RelationMismatch {
        query: usize,
        coordinate: &'static str,
    },
}

impl From<TowerError> for BinaryHistoryAppendError {
    fn from(value: TowerError) -> Self {
        Self::Tower(value)
    }
}

impl From<AdditiveNttError> for BinaryHistoryAppendError {
    fn from(value: AdditiveNttError) -> Self {
        Self::Transform(value)
    }
}

impl From<BinaryMerkleError> for BinaryHistoryAppendError {
    fn from(value: BinaryMerkleError) -> Self {
        Self::Merkle(value)
    }
}

impl From<SampledFriError> for BinaryHistoryAppendError {
    fn from(value: SampledFriError) -> Self {
        Self::Fri(value)
    }
}

impl fmt::Display for BinaryHistoryAppendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Tower(error) => error.fmt(f),
            Self::Transform(error) => error.fmt(f),
            Self::Merkle(error) => error.fmt(f),
            Self::Fri(error) => error.fmt(f),
            Self::InvalidStatement => write!(f, "invalid binary append statement"),
            Self::ChannelMismatch => write!(f, "binary append claims use different channels"),
            Self::OutputClaimMismatch => {
                write!(
                    f,
                    "binary append output claim violates the public recurrence"
                )
            }
            Self::InvalidWitnessShape => write!(f, "invalid binary append witness shape"),
            Self::CoefficientBoundViolation(side) => {
                write!(f, "{side} coefficients exceed the advertised bound")
            }
            Self::WordCoefficientMismatch(side) => {
                write!(f, "{side} word is not the transform of its coefficients")
            }
            Self::CommitmentMismatch(side) => {
                write!(f, "{side} word does not match its commitment")
            }
            Self::FoldedWordMismatch => {
                write!(f, "coordinate and coefficient folds disagree")
            }
            Self::InvalidProofShape => write!(f, "invalid binary append proof shape"),
            Self::MissingQuerySchedule => write!(f, "sampled FRI did not draw append queries"),
            Self::InvalidOpening { query, side } => {
                write!(f, "query {query} has an invalid {side} opening")
            }
            Self::RelationMismatch { query, coordinate } => {
                write!(f, "query {query} violates the {coordinate} fold relation")
            }
        }
    }
}

impl std::error::Error for BinaryHistoryAppendError {}

/// Commit a canonical level-6 additive word in the same domain used by
/// sampled additive-FRI.
pub fn commit_additive_rs_word(word: &[TowerElem]) -> Result<BinaryRoot, BinaryHistoryAppendError> {
    Ok(build_word_tree(word)?.root())
}

/// Derive the append fold challenge and public target recurrence after both
/// input roots and all claim/domain metadata have entered the append transcript.
/// This narrow API keeps higher-level joins from copying the private schedule.
pub fn derive_binary_history_append_challenge(
    statement: &BinaryHistoryAppendStatement,
) -> Result<(TowerElem, TowerElem), BinaryHistoryAppendError> {
    validate_statement(statement)?;
    let (_, gamma, output_target) = AppendChallengeSource::new(statement)?;
    Ok((gamma, output_target))
}

/// Prove one append from two committed words and their novel-basis witnesses.
#[allow(clippy::too_many_arguments)]
pub fn prove_binary_history_append(
    statement: &BinaryHistoryAppendStatement,
    left_word: &[TowerElem],
    left_coefficients: &[TowerElem],
    right_word: &[TowerElem],
    right_coefficients: &[TowerElem],
) -> Result<BinaryHistoryAppendProof, BinaryHistoryAppendError> {
    let (word_len, coefficient_bound) = validate_statement(statement)?;
    let hash = BinaryShake256V1;
    let left_tree = validate_witness(
        "left",
        &statement.left,
        left_word,
        left_coefficients,
        statement,
        word_len,
        coefficient_bound,
    )?;
    let right_tree = validate_witness(
        "right",
        &statement.right,
        right_word,
        right_coefficients,
        statement,
        word_len,
        coefficient_bound,
    )?;

    let (gamma, output_target) = derive_binary_history_append_challenge(statement)?;
    let (mut source, replayed_gamma, replayed_target) = AppendChallengeSource::new(statement)?;
    if replayed_gamma != gamma || replayed_target != output_target {
        return Err(BinaryHistoryAppendError::InvalidStatement);
    }
    let folded_word = left_word
        .iter()
        .copied()
        .zip(right_word.iter().copied())
        .map(|(left, right)| left.add(gamma.mul(right)?).map_err(Into::into))
        .collect::<Result<Vec<_>, BinaryHistoryAppendError>>()?;
    let folded_coefficients = left_coefficients
        .iter()
        .copied()
        .zip(right_coefficients.iter().copied())
        .map(|(left, right)| left.add(gamma.mul(right)?).map_err(Into::into))
        .collect::<Result<Vec<_>, BinaryHistoryAppendError>>()?;

    if forward(&folded_coefficients, &statement.basis, statement.offset)? != folded_word {
        return Err(BinaryHistoryAppendError::FoldedWordMismatch);
    }
    let folded_root = build_word_tree(&folded_word)?.root();
    let (fri_statement, fri_proof) = prove_sampled(
        &folded_coefficients,
        &statement.basis,
        statement.offset,
        coefficient_bound,
        statement.num_queries,
        &hash,
        &mut source,
    )?;
    if fri_statement.input_root != folded_root {
        return Err(BinaryHistoryAppendError::FoldedWordMismatch);
    }
    let query_indices = source
        .query_indices()
        .ok_or(BinaryHistoryAppendError::MissingQuerySchedule)?;
    let half = word_len / 2;
    let relation_openings = query_indices
        .iter()
        .map(
            |&pair_index| -> Result<BinaryRelationPairOpening, BinaryHistoryAppendError> {
                Ok(BinaryRelationPairOpening {
                    left_low: left_word[pair_index],
                    left_high: left_word[half + pair_index],
                    right_low: right_word[pair_index],
                    right_high: right_word[half + pair_index],
                    left_low_path: left_tree.open(pair_index)?,
                    left_high_path: left_tree.open(half + pair_index)?,
                    right_low_path: right_tree.open(pair_index)?,
                    right_high_path: right_tree.open(half + pair_index)?,
                })
            },
        )
        .collect::<Result<Vec<_>, _>>()?;

    Ok(BinaryHistoryAppendProof {
        output_claim: BinaryAdditiveRsClaim {
            root: folded_root,
            coefficient_bound: statement.left.coefficient_bound,
            channel_id: statement.left.channel_id,
            target: output_target,
        },
        fri_proof,
        relation_openings,
    })
}

/// Replay the root-before-gamma transcript, sampled-FRI schedule, exact Merkle
/// paths, and both sampled coordinate equations.
pub fn verify_binary_history_append(
    statement: &BinaryHistoryAppendStatement,
    proof: &BinaryHistoryAppendProof,
) -> bool {
    check_binary_history_append(statement, proof).is_ok()
}

fn check_binary_history_append(
    statement: &BinaryHistoryAppendStatement,
    proof: &BinaryHistoryAppendProof,
) -> Result<(), BinaryHistoryAppendError> {
    let (word_len, coefficient_bound) = validate_statement(statement)?;
    if proof.relation_openings.len() != statement.num_queries {
        return Err(BinaryHistoryAppendError::InvalidProofShape);
    }
    let hash = BinaryShake256V1;
    let (mut source, gamma, output_target) = AppendChallengeSource::new(statement)?;
    if proof.output_claim.coefficient_bound != statement.left.coefficient_bound
        || proof.output_claim.channel_id != statement.left.channel_id
        || proof.output_claim.target != output_target
    {
        return Err(BinaryHistoryAppendError::OutputClaimMismatch);
    }
    let fri_statement = SampledFriStatement {
        input_root: proof.output_claim.root,
        basis: statement.basis.clone(),
        offset: statement.offset,
        coefficient_bound,
        num_queries: statement.num_queries,
    };
    if !verify_sampled(&fri_statement, &proof.fri_proof, &hash, &mut source) {
        return Err(BinaryHistoryAppendError::InvalidProofShape);
    }
    let query_indices = source
        .query_indices()
        .ok_or(BinaryHistoryAppendError::MissingQuerySchedule)?;
    let half = word_len / 2;

    for (query, (&pair_index, relation)) in query_indices
        .iter()
        .zip(&proof.relation_openings)
        .enumerate()
    {
        let folded = &proof.fri_proof.queries[query].rounds[0];
        verify_relation_opening(
            query,
            "left-low",
            statement.left.root,
            word_len,
            pair_index,
            relation.left_low,
            &relation.left_low_path,
        )?;
        verify_relation_opening(
            query,
            "left-high",
            statement.left.root,
            word_len,
            half + pair_index,
            relation.left_high,
            &relation.left_high_path,
        )?;
        verify_relation_opening(
            query,
            "right-low",
            statement.right.root,
            word_len,
            pair_index,
            relation.right_low,
            &relation.right_low_path,
        )?;
        verify_relation_opening(
            query,
            "right-high",
            statement.right.root,
            word_len,
            half + pair_index,
            relation.right_high,
            &relation.right_high_path,
        )?;

        if relation.left_low.add(gamma.mul(relation.right_low)?)? != folded.low {
            return Err(BinaryHistoryAppendError::RelationMismatch {
                query,
                coordinate: "low",
            });
        }
        if relation.left_high.add(gamma.mul(relation.right_high)?)? != folded.high {
            return Err(BinaryHistoryAppendError::RelationMismatch {
                query,
                coordinate: "high",
            });
        }
    }
    Ok(())
}

fn validate_statement(
    statement: &BinaryHistoryAppendStatement,
) -> Result<(usize, usize), BinaryHistoryAppendError> {
    if statement.offset.level() != MAX_LEVEL
        || statement.basis.is_empty()
        || statement.num_queries == 0
        || statement
            .basis
            .iter()
            .any(|element| element.level() != MAX_LEVEL)
        || statement.left.coefficient_bound == 0
        || statement.left.coefficient_bound != statement.right.coefficient_bound
        || statement.left.target.level() != MAX_LEVEL
        || statement.right.target.level() != MAX_LEVEL
    {
        return Err(BinaryHistoryAppendError::InvalidStatement);
    }
    if statement.left.channel_id != statement.right.channel_id {
        return Err(BinaryHistoryAppendError::ChannelMismatch);
    }
    let word_len = 1usize
        .checked_shl(statement.basis.len() as u32)
        .ok_or(BinaryHistoryAppendError::InvalidStatement)?;
    let coefficient_bound = usize::try_from(statement.left.coefficient_bound)
        .map_err(|_| BinaryHistoryAppendError::InvalidStatement)?;
    if coefficient_bound > word_len {
        return Err(BinaryHistoryAppendError::InvalidStatement);
    }
    Ok((word_len, coefficient_bound))
}

fn validate_witness(
    side: &'static str,
    claim: &BinaryAdditiveRsClaim,
    word: &[TowerElem],
    coefficients: &[TowerElem],
    statement: &BinaryHistoryAppendStatement,
    expected_len: usize,
    coefficient_bound: usize,
) -> Result<BinaryMerkleTree<BinaryRoot>, BinaryHistoryAppendError> {
    if word.len() != expected_len || coefficients.len() != expected_len {
        return Err(BinaryHistoryAppendError::InvalidWitnessShape);
    }
    debug_assert_eq!(claim.coefficient_bound, coefficient_bound as u64);
    if coefficients[coefficient_bound..]
        .iter()
        .any(|coefficient| !coefficient.is_zero())
    {
        return Err(BinaryHistoryAppendError::CoefficientBoundViolation(side));
    }
    if forward(coefficients, &statement.basis, statement.offset)? != word {
        return Err(BinaryHistoryAppendError::WordCoefficientMismatch(side));
    }
    let tree = build_word_tree(word)?;
    if tree.root() != claim.root {
        return Err(BinaryHistoryAppendError::CommitmentMismatch(side));
    }
    Ok(tree)
}

fn build_word_tree(
    word: &[TowerElem],
) -> Result<BinaryMerkleTree<BinaryRoot>, BinaryHistoryAppendError> {
    if word.iter().any(|element| element.level() != MAX_LEVEL) {
        return Err(BinaryHistoryAppendError::InvalidWitnessShape);
    }
    let payloads = word
        .iter()
        .copied()
        .map(tower_leaf_payload)
        .collect::<Vec<_>>();
    Ok(BinaryMerkleTree::build(
        &BinaryShake256V1,
        BinaryHashDomain::AdditiveFri,
        &payloads,
    )?)
}

#[allow(clippy::too_many_arguments)]
fn verify_relation_opening(
    query: usize,
    side: &'static str,
    root: BinaryRoot,
    word_len: usize,
    index: usize,
    value: TowerElem,
    path: &BinaryMerklePath<BinaryRoot>,
) -> Result<(), BinaryHistoryAppendError> {
    if value.level() != MAX_LEVEL
        || !verify_binary_opening(
            &BinaryShake256V1,
            BinaryHashDomain::AdditiveFri,
            word_len,
            index,
            &tower_leaf_payload(value),
            path,
            &root,
        )?
    {
        return Err(BinaryHistoryAppendError::InvalidOpening { query, side });
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AppendSourceError {
    WrongTowerLevel(u8),
    InvalidQueryDomain,
}

impl fmt::Display for AppendSourceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongTowerLevel(level) => {
                write!(
                    f,
                    "append FRI requested tower level {level}, expected {MAX_LEVEL}"
                )
            }
            Self::InvalidQueryDomain => write!(f, "append FRI requested an empty query domain"),
        }
    }
}

struct AppendChallengeSource {
    transcript: BinaryShake256Transcript,
    query_indices: Option<Vec<usize>>,
    output_coefficient_bound: u64,
    output_channel_id: BinaryChannelId,
    output_target: TowerElem,
    output_metadata_observed: bool,
}

impl AppendChallengeSource {
    fn new(
        statement: &BinaryHistoryAppendStatement,
    ) -> Result<(Self, TowerElem, TowerElem), BinaryHistoryAppendError> {
        let mut transcript = BinaryShake256Transcript::new(PROTOCOL_LABEL);
        transcript.observe_bytes(b"hash-suite", <BinaryShake256V1 as HashSuite>::SUITE_ID);
        transcript.observe_u64(b"tower-level", MAX_LEVEL as u64);
        transcript.observe_u64(b"log-domain", statement.basis.len() as u64);
        transcript.observe_u64(b"num-queries", statement.num_queries as u64);
        transcript.observe_bytes(b"offset", &tower_leaf_payload(statement.offset));
        for (index, basis_element) in statement.basis.iter().copied().enumerate() {
            transcript.observe_u64(b"basis-index", index as u64);
            transcript.observe_bytes(b"basis-element", &tower_leaf_payload(basis_element));
        }
        observe_claim(&mut transcript, b"left", &statement.left);
        observe_claim(&mut transcript, b"right", &statement.right);

        // Both roots and all claim/domain metadata are in the prefix here.
        let gamma = TowerElem::new(MAX_LEVEL, transcript.sample_gf2_64(b"append-gamma"))?;
        let output_target = statement
            .left
            .target
            .add(gamma.mul(statement.right.target)?)?;
        Ok((
            Self {
                transcript,
                query_indices: None,
                output_coefficient_bound: statement.left.coefficient_bound,
                output_channel_id: statement.left.channel_id,
                output_target,
                output_metadata_observed: false,
            },
            gamma,
            output_target,
        ))
    }

    fn query_indices(&self) -> Option<&[usize]> {
        self.query_indices.as_deref()
    }
}

impl ChallengeSource for AppendChallengeSource {
    type Error = AppendSourceError;

    fn observe_commitment(
        &mut self,
        round: usize,
        word_len: usize,
        root: &BinaryRoot,
    ) -> Result<(), Self::Error> {
        if round == 0 && !self.output_metadata_observed {
            self.transcript
                .observe_u64(b"output-coefficient-bound", self.output_coefficient_bound);
            self.transcript
                .observe_bytes(b"output-channel-id", self.output_channel_id.as_bytes());
            self.transcript
                .observe_bytes(b"output-target", &tower_leaf_payload(self.output_target));
            self.output_metadata_observed = true;
        }
        self.transcript.observe_u64(b"fri-round", round as u64);
        self.transcript
            .observe_u64(b"fri-round-word-length", word_len as u64);
        self.transcript.observe_root(b"fri-round-root", root);
        Ok(())
    }

    fn draw_fold_challenge(
        &mut self,
        _round: usize,
        tower_level: u8,
    ) -> Result<TowerElem, Self::Error> {
        if tower_level != MAX_LEVEL {
            return Err(AppendSourceError::WrongTowerLevel(tower_level));
        }
        Ok(TowerElem::new(
            MAX_LEVEL,
            self.transcript.sample_gf2_64(b"fri-fold-challenge"),
        )
        .expect("every u64 is canonical in GF(2^64)"))
    }

    fn draw_query_indices(
        &mut self,
        initial_pair_count: usize,
        count: usize,
    ) -> Result<Vec<usize>, Self::Error> {
        if initial_pair_count == 0 || !initial_pair_count.is_power_of_two() {
            return Err(AppendSourceError::InvalidQueryDomain);
        }
        let indices = (0..count)
            .map(|_| {
                (self.transcript.sample_gf2_64(b"append-query-index") as usize)
                    & (initial_pair_count - 1)
            })
            .collect::<Vec<_>>();
        self.query_indices = Some(indices.clone());
        Ok(indices)
    }
}

fn observe_claim(
    transcript: &mut BinaryShake256Transcript,
    side: &[u8],
    claim: &BinaryAdditiveRsClaim,
) {
    transcript.observe_bytes(b"claim-side", side);
    transcript.observe_root(b"claim-word-root", &claim.root);
    transcript.observe_u64(b"claim-coefficient-bound", claim.coefficient_bound);
    transcript.observe_bytes(b"claim-channel-id", claim.channel_id.as_bytes());
    transcript.observe_bytes(b"claim-target", &tower_leaf_payload(claim.target));
}
