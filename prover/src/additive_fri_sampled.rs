//! Sampled multi-round additive-FRI fold-consistency over the binary suite.
//!
//! Roots and Merkle paths are typed [`BinaryRoot`] values produced through
//! [`HashSuite`].  [`ChallengeSource`] enforces commit-before-challenge and
//! final-commit-before-query call order; [`BinaryShakeFriSource`] is the
//! cSHAKE256 implementation. Low-degree/proximity soundness, Lean-emitted
//! refinement, and the cryptographic XOF/Merkle assumptions remain explicit as
//! `[ANTT-FRI-PROXIMITY]`, `[ANTT-FRI-RUST-UNVERIFIED]`,
//! `[ANTT-FRI-XOF-analysis]`, and `[COMMIT-CR]`.

use core::fmt;

use crate::additive_ntt::{forward, AdditiveNttError};
use crate::binary_hash::{BinaryHashDomain, BinaryRoot, HashSuite};
use crate::binary_merkle::{
    verify_binary_opening, BinaryMerkleError, BinaryMerklePath, BinaryMerkleTree,
};
use crate::binary_tower::{additive_fold_map, additive_fold_pair, TowerElem, TowerError};
use crate::binary_transcript::{BinaryShake256Transcript, TranscriptSuite};

const PROTOCOL_LABEL: &[u8] = b"minidregg/additive-fri-sampled/v1";
const TOWER_LEAF_TAG: &[u8; 4] = b"BTL1";
const TOWER_LEAF_BYTES: usize = 13;

/// An injected transcript contract. Implementations must bind every observed
/// root and sample uniformly; the verifier replays the identical schedule.
pub trait ChallengeSource {
    type Error: fmt::Display;

    fn observe_commitment(
        &mut self,
        round: usize,
        word_len: usize,
        root: &BinaryRoot,
    ) -> Result<(), Self::Error>;

    fn draw_fold_challenge(
        &mut self,
        round: usize,
        tower_level: u8,
    ) -> Result<TowerElem, Self::Error>;

    fn draw_query_indices(
        &mut self,
        initial_pair_count: usize,
        count: usize,
    ) -> Result<Vec<usize>, Self::Error>;
}

/// cSHAKE256 challenge source for the binary additive suite.
pub struct BinaryShakeFriSource {
    transcript: BinaryShake256Transcript,
}

impl BinaryShakeFriSource {
    pub fn new(
        hash_suite_id: &[u8],
        basis: &[TowerElem],
        offset: TowerElem,
        coefficient_bound: usize,
        num_queries: usize,
    ) -> Self {
        let mut transcript = BinaryShake256Transcript::new(PROTOCOL_LABEL);
        transcript.observe_bytes(b"hash-suite", hash_suite_id);
        transcript.observe_u64(b"tower-level", offset.level() as u64);
        transcript.observe_u64(b"log-domain", basis.len() as u64);
        transcript.observe_u64(b"coefficient-bound", coefficient_bound as u64);
        transcript.observe_u64(b"num-queries", num_queries as u64);
        transcript.observe_bytes(b"offset", &tower_leaf_payload(offset));
        for (index, beta) in basis.iter().copied().enumerate() {
            transcript.observe_u64(b"basis-index", index as u64);
            transcript.observe_bytes(b"basis-element", &tower_leaf_payload(beta));
        }
        Self { transcript }
    }
}

impl ChallengeSource for BinaryShakeFriSource {
    type Error = core::convert::Infallible;

    fn observe_commitment(
        &mut self,
        round: usize,
        word_len: usize,
        root: &BinaryRoot,
    ) -> Result<(), Self::Error> {
        self.transcript.observe_u64(b"round", round as u64);
        self.transcript
            .observe_u64(b"round-word-length", word_len as u64);
        self.transcript.observe_root(b"round-root", root);
        Ok(())
    }

    fn draw_fold_challenge(
        &mut self,
        _round: usize,
        tower_level: u8,
    ) -> Result<TowerElem, Self::Error> {
        let sample = self.transcript.sample_gf2_64(b"fold-challenge");
        let width = 1usize << tower_level;
        let mask = if width == 64 {
            u64::MAX
        } else {
            (1u64 << width) - 1
        };
        Ok(TowerElem::new(tower_level, sample & mask).expect("masked GF(2) sample is canonical"))
    }

    fn draw_query_indices(
        &mut self,
        initial_pair_count: usize,
        count: usize,
    ) -> Result<Vec<usize>, Self::Error> {
        // Independent sampling with replacement is the exact experiment used
        // by the `(1-tau)^q` proximity term.  The pair domain is a power of two,
        // so masking each fresh XOF word is uniform with no rejection bias.
        Ok((0..count)
            .map(|_| {
                (self.transcript.sample_gf2_64(b"query-index") as usize) & (initial_pair_count - 1)
            })
            .collect())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SampledFriStatement {
    pub input_root: BinaryRoot,
    pub basis: Vec<TowerElem>,
    pub offset: TowerElem,
    /// Starting novel-basis degree bound: coefficients at this index and above
    /// are zero in the claimed additive Reed--Solomon word.
    pub coefficient_bound: usize,
    pub num_queries: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairOpening {
    pub low: TowerElem,
    pub high: TowerElem,
    pub low_path: BinaryMerklePath<BinaryRoot>,
    pub high_path: BinaryMerklePath<BinaryRoot>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QueryOpening {
    pub rounds: Vec<PairOpening>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SampledFriProof {
    /// Roots for lengths `n, n/2, ..., 1`.
    pub roots: Vec<BinaryRoot>,
    pub final_value: TowerElem,
    pub queries: Vec<QueryOpening>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SampledFriError {
    Tower(TowerError),
    Transform(AdditiveNttError),
    Merkle(BinaryMerkleError),
    ChallengeSource(String),
    InvalidStatement,
    InvalidProofShape,
    InputRootMismatch,
    QueryOutOfRange(usize),
    InvalidOpening { query: usize, round: usize },
    FoldMismatch { query: usize, round: usize },
}

impl From<TowerError> for SampledFriError {
    fn from(value: TowerError) -> Self {
        Self::Tower(value)
    }
}

impl From<AdditiveNttError> for SampledFriError {
    fn from(value: AdditiveNttError) -> Self {
        Self::Transform(value)
    }
}

impl From<BinaryMerkleError> for SampledFriError {
    fn from(value: BinaryMerkleError) -> Self {
        Self::Merkle(value)
    }
}

impl fmt::Display for SampledFriError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Tower(error) => error.fmt(f),
            Self::Transform(error) => error.fmt(f),
            Self::Merkle(error) => error.fmt(f),
            Self::ChallengeSource(error) => write!(f, "challenge source: {error}"),
            Self::InvalidStatement => write!(f, "invalid sampled additive-FRI statement"),
            Self::InvalidProofShape => write!(f, "invalid sampled additive-FRI proof shape"),
            Self::InputRootMismatch => write!(f, "first proof root is not the statement root"),
            Self::QueryOutOfRange(index) => write!(f, "query index {index} is out of range"),
            Self::InvalidOpening { query, round } => {
                write!(
                    f,
                    "query {query}, round {round} has an invalid Merkle opening"
                )
            }
            Self::FoldMismatch { query, round } => {
                write!(f, "query {query}, round {round} violates fold consistency")
            }
        }
    }
}

impl std::error::Error for SampledFriError {}

pub fn prove_sampled<H: HashSuite<Root = BinaryRoot>, S: ChallengeSource>(
    coefficients: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
    coefficient_bound: usize,
    num_queries: usize,
    hash: &H,
    source: &mut S,
) -> Result<(SampledFriStatement, SampledFriProof), SampledFriError> {
    validate_statement_domain(basis, offset, coefficient_bound, num_queries)?;
    if coefficients.len() != checked_domain_size(basis.len())?
        || coefficients[coefficient_bound..]
            .iter()
            .any(|coefficient| !coefficient.is_zero())
    {
        return Err(SampledFriError::InvalidStatement);
    }
    let initial_word = forward(coefficients, basis, offset)?;
    let mut words = vec![initial_word];
    let mut roots = Vec::with_capacity(basis.len() + 1);
    let mut trees = Vec::with_capacity(basis.len());
    let mut round_basis = basis.to_vec();
    let mut round_offset = offset;

    for round in 0..basis.len() {
        let current = words.last().ok_or(SampledFriError::InvalidProofShape)?;
        let tree = commit_word(current, hash)?;
        let root = tree.root();
        source
            .observe_commitment(round, current.len(), &root)
            .map_err(source_error)?;
        let challenge = source
            .draw_fold_challenge(round, offset.level())
            .map_err(source_error)?;
        if challenge.level() != offset.level() {
            return Err(SampledFriError::InvalidStatement);
        }
        roots.push(root);
        trees.push(tree);
        let folded = fold_word(current, &round_basis, round_offset, challenge)?;
        (round_basis, round_offset) = fold_domain(&round_basis, round_offset)?;
        words.push(folded);
    }

    let final_word = words.last().ok_or(SampledFriError::InvalidProofShape)?;
    if final_word.len() != 1 {
        return Err(SampledFriError::InvalidProofShape);
    }
    let final_root = commit_word(final_word, hash)?.root();
    source
        .observe_commitment(basis.len(), 1, &final_root)
        .map_err(source_error)?;
    roots.push(final_root);

    let query_indices = source
        .draw_query_indices(coefficients.len() / 2, num_queries)
        .map_err(source_error)?;
    validate_queries(&query_indices, coefficients.len() / 2, num_queries)?;
    let queries = query_indices
        .iter()
        .map(|&initial_index| -> Result<QueryOpening, SampledFriError> {
            let rounds = (0..basis.len())
                .map(|round| -> Result<PairOpening, SampledFriError> {
                    let word = &words[round];
                    let half = word.len() / 2;
                    let pair_index = initial_index % half;
                    Ok(PairOpening {
                        low: word[pair_index],
                        high: word[half + pair_index],
                        low_path: trees[round].open(pair_index)?,
                        high_path: trees[round].open(half + pair_index)?,
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(QueryOpening { rounds })
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok((
        SampledFriStatement {
            input_root: roots[0],
            basis: basis.to_vec(),
            offset,
            coefficient_bound,
            num_queries,
        },
        SampledFriProof {
            roots,
            final_value: final_word[0],
            queries,
        },
    ))
}

pub fn verify_sampled<H: HashSuite<Root = BinaryRoot>, S: ChallengeSource>(
    statement: &SampledFriStatement,
    proof: &SampledFriProof,
    hash: &H,
    source: &mut S,
) -> bool {
    check_sampled(statement, proof, hash, source).is_ok()
}

fn check_sampled<H: HashSuite<Root = BinaryRoot>, S: ChallengeSource>(
    statement: &SampledFriStatement,
    proof: &SampledFriProof,
    hash: &H,
    source: &mut S,
) -> Result<(), SampledFriError> {
    validate_statement_domain(
        &statement.basis,
        statement.offset,
        statement.coefficient_bound,
        statement.num_queries,
    )?;
    let rounds = statement.basis.len();
    if proof.roots.len() != rounds + 1
        || proof.queries.len() != statement.num_queries
        || proof
            .queries
            .iter()
            .any(|query| query.rounds.len() != rounds)
        || proof.final_value.level() != statement.offset.level()
    {
        return Err(SampledFriError::InvalidProofShape);
    }
    if proof.roots.first().copied() != Some(statement.input_root) {
        return Err(SampledFriError::InputRootMismatch);
    }

    let domain_size = checked_domain_size(rounds)?;
    let mut challenges = Vec::with_capacity(rounds);
    let mut word_len = domain_size;
    for round in 0..rounds {
        source
            .observe_commitment(round, word_len, &proof.roots[round])
            .map_err(source_error)?;
        let challenge = source
            .draw_fold_challenge(round, statement.offset.level())
            .map_err(source_error)?;
        if challenge.level() != statement.offset.level() {
            return Err(SampledFriError::InvalidStatement);
        }
        challenges.push(challenge);
        word_len /= 2;
    }
    source
        .observe_commitment(rounds, 1, &proof.roots[rounds])
        .map_err(source_error)?;
    let query_indices = source
        .draw_query_indices(domain_size / 2, statement.num_queries)
        .map_err(source_error)?;
    validate_queries(&query_indices, domain_size / 2, statement.num_queries)?;

    if commit_word(&[proof.final_value], hash)?.root() != proof.roots[rounds] {
        return Err(SampledFriError::InvalidOpening {
            query: 0,
            round: rounds,
        });
    }

    let mut bases = Vec::with_capacity(rounds);
    let mut offsets = Vec::with_capacity(rounds);
    let mut round_basis = statement.basis.clone();
    let mut round_offset = statement.offset;
    for _ in 0..rounds {
        bases.push(round_basis.clone());
        offsets.push(round_offset);
        (round_basis, round_offset) = fold_domain(&round_basis, round_offset)?;
    }

    for (query_number, (&initial_index, query)) in
        query_indices.iter().zip(&proof.queries).enumerate()
    {
        let mut level_len = domain_size;
        for round in 0..rounds {
            let half = level_len / 2;
            let pair_index = initial_index % half;
            let opening = &query.rounds[round];
            if opening.low.level() != statement.offset.level()
                || opening.high.level() != statement.offset.level()
                || !verify_binary_opening(
                    hash,
                    BinaryHashDomain::AdditiveFri,
                    level_len,
                    pair_index,
                    &tower_leaf_payload(opening.low),
                    &opening.low_path,
                    &proof.roots[round],
                )?
                || !verify_binary_opening(
                    hash,
                    BinaryHashDomain::AdditiveFri,
                    level_len,
                    half + pair_index,
                    &tower_leaf_payload(opening.high),
                    &opening.high_path,
                    &proof.roots[round],
                )?
            {
                return Err(SampledFriError::InvalidOpening {
                    query: query_number,
                    round,
                });
            }

            let x = domain_point(
                &bases[round][..bases[round].len() - 1],
                offsets[round],
                pair_index,
            )?;
            let expected = additive_fold_pair(
                *bases[round]
                    .last()
                    .ok_or(SampledFriError::InvalidStatement)?,
                challenges[round],
                x,
                opening.low,
                opening.high,
            )?;
            let actual = if round + 1 == rounds {
                proof.final_value
            } else {
                let next_half = half / 2;
                let next = &query.rounds[round + 1];
                if pair_index < next_half {
                    next.low
                } else {
                    next.high
                }
            };
            if expected != actual {
                return Err(SampledFriError::FoldMismatch {
                    query: query_number,
                    round,
                });
            }
            level_len = half;
        }
    }
    Ok(())
}

fn commit_word<H: HashSuite<Root = BinaryRoot>>(
    word: &[TowerElem],
    hash: &H,
) -> Result<BinaryMerkleTree<BinaryRoot>, SampledFriError> {
    let payloads = word
        .iter()
        .copied()
        .map(tower_leaf_payload)
        .collect::<Vec<_>>();
    Ok(BinaryMerkleTree::build(
        hash,
        BinaryHashDomain::AdditiveFri,
        &payloads,
    )?)
}

pub const fn tower_leaf_payload(value: TowerElem) -> [u8; TOWER_LEAF_BYTES] {
    let mut payload = [0u8; TOWER_LEAF_BYTES];
    payload[0] = TOWER_LEAF_TAG[0];
    payload[1] = TOWER_LEAF_TAG[1];
    payload[2] = TOWER_LEAF_TAG[2];
    payload[3] = TOWER_LEAF_TAG[3];
    payload[4] = value.level();
    let bits = value.bits().to_le_bytes();
    let mut i = 0;
    while i < 8 {
        payload[5 + i] = bits[i];
        i += 1;
    }
    payload
}

fn fold_word(
    word: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
    challenge: TowerElem,
) -> Result<Vec<TowerElem>, SampledFriError> {
    let half = word.len() / 2;
    let beta = *basis.last().ok_or(SampledFriError::InvalidStatement)?;
    let beta_inverse = beta.inverse()?;
    let points = domain_points(&basis[..basis.len() - 1], offset)?;
    let mut output = Vec::with_capacity(half);
    for i in 0..half {
        let odd = word[i].add(word[half + i])?.mul(beta_inverse)?;
        output.push(word[i].add(points[i].add(challenge)?.mul(odd)?)?);
    }
    Ok(output)
}

fn fold_domain(
    basis: &[TowerElem],
    offset: TowerElem,
) -> Result<(Vec<TowerElem>, TowerElem), SampledFriError> {
    let beta = *basis.last().ok_or(SampledFriError::InvalidStatement)?;
    let next_basis = basis[..basis.len() - 1]
        .iter()
        .copied()
        .map(|value| additive_fold_map(beta, value).map_err(SampledFriError::from))
        .collect::<Result<Vec<_>, _>>()?;
    Ok((next_basis, additive_fold_map(beta, offset)?))
}

fn domain_points(
    basis: &[TowerElem],
    offset: TowerElem,
) -> Result<Vec<TowerElem>, SampledFriError> {
    let mut points = vec![offset];
    for beta in basis.iter().copied() {
        let old_len = points.len();
        for i in 0..old_len {
            points.push(points[i].add(beta)?);
        }
    }
    Ok(points)
}

fn domain_point(
    basis: &[TowerElem],
    offset: TowerElem,
    index: usize,
) -> Result<TowerElem, SampledFriError> {
    let mut point = offset;
    for (i, beta) in basis.iter().copied().enumerate() {
        if index & (1usize << i) != 0 {
            point = point.add(beta)?;
        }
    }
    Ok(point)
}

fn validate_statement_domain(
    basis: &[TowerElem],
    offset: TowerElem,
    coefficient_bound: usize,
    num_queries: usize,
) -> Result<(), SampledFriError> {
    if basis.is_empty() {
        return Err(SampledFriError::InvalidStatement);
    }
    checked_domain_size(basis.len())?;
    let domain_size = checked_domain_size(basis.len())?;
    if coefficient_bound == 0 || coefficient_bound > domain_size || num_queries == 0 {
        return Err(SampledFriError::InvalidStatement);
    }
    let dimension = 1usize << offset.level();
    if basis.len() > dimension || basis.iter().any(|value| value.level() != offset.level()) {
        return Err(SampledFriError::InvalidStatement);
    }
    let mut gamma: Vec<TowerElem> = Vec::with_capacity(basis.len());
    for beta in basis.iter().copied() {
        let mut value = beta;
        for coefficient in gamma.iter().copied() {
            value = value.square().add(coefficient.mul(value)?)?;
        }
        if value.is_zero() {
            return Err(SampledFriError::InvalidStatement);
        }
        gamma.push(value);
    }
    Ok(())
}

fn checked_domain_size(log_size: usize) -> Result<usize, SampledFriError> {
    1usize
        .checked_shl(log_size as u32)
        .ok_or(SampledFriError::InvalidStatement)
}

fn validate_queries(
    indices: &[usize],
    pair_count: usize,
    expected_count: usize,
) -> Result<(), SampledFriError> {
    if indices.len() != expected_count {
        return Err(SampledFriError::InvalidProofShape);
    }
    for &index in indices {
        if index >= pair_count {
            return Err(SampledFriError::QueryOutOfRange(index));
        }
    }
    Ok(())
}

fn source_error<E: fmt::Display>(error: E) -> SampledFriError {
    SampledFriError::ChallengeSource(error.to_string())
}
