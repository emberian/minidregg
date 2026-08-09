//! Reusable sampled additive MLE commitment over fixed-width `GF(2^256)`.
//!
//! A Boolean table of length `N = 2^v` is Mobius-transformed, zero-padded to
//! `M = 2^(v + log_blowup)`, encoded in the reversed LCH basis, and committed
//! over the canonical affine domain
//!
//! ```text
//! offset = 0, basis[i] = coordinate bit i, 0 <= i < log2(M).
//! ```
//!
//! Leaves are exactly the canonical 32-byte little-endian [`Tower256`]
//! encodings under [`BinaryShake256V1`].  The initial tree is retained by
//! [`Tower256MleCommitment`], so the same commitment can be opened at multiple
//! externally supplied MLE points.  Each opening uses a caller-owned
//! [`BinaryShake256Transcript`]: it observes the initial root, then each
//! `point coordinate -> folded root` pair, fixes the claimed terminal, and
//! only then draws sampled Merkle queries.
//!
//! Honest residuals:
//!
//! * `[T256-MLE-PROXIMITY]`: compose additive-FRI proximity at explicit rate
//!   `N/M = 2^-log_blowup` with the Mobius/reversed-LCH provenance argument.
//! * `[COMMIT-CR]`: instantiate collision resistance for the cSHAKE256 Merkle
//!   commitment rather than treating paths as ideal position bindings.
//! * `[T256-MLE-ROM]`: analyze the caller context, fold-root schedule, and
//!   sampled indices in the cSHAKE256 ROM/XOF game.
//! * `[T256-MLE-RUST-UNVERIFIED]`: this fixed-width Rust schedule is unverified
//!   `Theory.BinaryTower`'s all-level field algebra, `Theory.AdditiveNTT`, and
//!   the formal Mobius MLE semantics.

use core::fmt;

use crate::{
    binary_hash::{BinaryHashDomain, BinaryRoot, BinaryShake256V1},
    binary_merkle::{verify_binary_opening, BinaryMerkleError, BinaryMerklePath, BinaryMerkleTree},
    binary_tower_256::{Tower256, Tower256Error, TOWER_256_LEVEL},
    binary_transcript::{BinaryShake256Transcript, TranscriptSuite},
};

pub const TOWER256_MLE_PROTOCOL_LABEL: &[u8] = b"minidregg/additive-mle-tower256/v1";
pub const TOWER256_MLE_LEAF_BYTES: usize = 32;
/// Reference-runtime allocation cap; the algebraic field still has dimension
/// 256, but verifier-controlled metadata must not request impractical vectors.
pub const TOWER256_MLE_MAX_LOG_DOMAIN: usize = 24;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tower256MlePairOpening {
    pub low: Tower256,
    pub high: Tower256,
    pub low_path: BinaryMerklePath<BinaryRoot>,
    pub high_path: BinaryMerklePath<BinaryRoot>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tower256MleQueryOpening {
    pub rounds: Vec<Tower256MlePairOpening>,
}

/// An opening at one externally supplied MLE point.
///
/// `fold_roots[r]` commits the word after binding `point[r]`.  The initial
/// root belongs to [`Tower256MleCommitment`] and is deliberately not repeated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tower256MleOpening {
    pub terminal: Tower256,
    pub fold_roots: Vec<BinaryRoot>,
    pub queries: Vec<Tower256MleQueryOpening>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tower256MleError {
    InvalidTableShape,
    DomainTooLarge { log_domain: usize },
    DomainSizeOverflow,
    InvalidPointLength { expected: usize, actual: usize },
    InvalidQueryCount,
    DependentBasis { index: usize },
    InvalidProofShape,
    InconsistentTerminalWord,
    Merkle(BinaryMerkleError),
    Tower(Tower256Error),
}

impl From<BinaryMerkleError> for Tower256MleError {
    fn from(value: BinaryMerkleError) -> Self {
        Self::Merkle(value)
    }
}

impl From<Tower256Error> for Tower256MleError {
    fn from(value: Tower256Error) -> Self {
        Self::Tower(value)
    }
}

impl fmt::Display for Tower256MleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidTableShape => {
                write!(
                    f,
                    "Tower256 MLE table length must be a power of two at least two"
                )
            }
            Self::DomainTooLarge { log_domain } => write!(
                f,
                "Tower256 additive domain has {log_domain} directions, runtime maximum is {TOWER256_MLE_MAX_LOG_DOMAIN}"
            ),
            Self::DomainSizeOverflow => write!(f, "Tower256 MLE domain size overflows usize"),
            Self::InvalidPointLength { expected, actual } => write!(
                f,
                "Tower256 MLE point has {actual} coordinates, expected {expected}"
            ),
            Self::InvalidQueryCount => write!(f, "Tower256 MLE opening needs at least one query"),
            Self::DependentBasis { index } => write!(
                f,
                "Tower256 additive basis becomes dependent at reversed index {index}"
            ),
            Self::InvalidProofShape => write!(f, "invalid Tower256 MLE opening shape"),
            Self::InconsistentTerminalWord => write!(
                f,
                "Tower256 folded word is not the claimed constant terminal codeword"
            ),
            Self::Merkle(error) => error.fmt(f),
            Self::Tower(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for Tower256MleError {}

/// A reusable commitment to one canonical additive encoding of a Boolean MLE.
///
/// [`Self::prove_opening`] takes `&self`; no transcript state or evaluation
/// point is retained, so callers can produce multiple independently framed
/// openings of the same root.
#[derive(Clone, Debug)]
pub struct Tower256MleCommitment {
    table: Vec<Tower256>,
    log_variables: usize,
    log_blowup: u32,
    initial_word: Vec<Tower256>,
    initial_tree: BinaryMerkleTree<BinaryRoot>,
}

impl Tower256MleCommitment {
    pub fn new(table: &[Tower256], log_blowup: u32) -> Result<Self, Tower256MleError> {
        let (log_variables, log_domain, domain_size) =
            validate_parameters(table.len(), log_blowup)?;
        let basis = tower256_standard_basis(log_domain)?;
        let mut coefficients = boolean_mobius_coefficients(table)?;
        coefficients.resize(domain_size, Tower256::ZERO);
        let initial_word = reversed_lch_encode(&coefficients, &basis, Tower256::ZERO)?;
        let initial_tree = commit_tower256_mle_word(&initial_word)?;
        Ok(Self {
            table: table.to_vec(),
            log_variables,
            log_blowup,
            initial_word,
            initial_tree,
        })
    }

    pub fn root(&self) -> BinaryRoot {
        self.initial_tree.root()
    }

    pub fn table_len(&self) -> usize {
        self.table.len()
    }

    pub fn log_blowup(&self) -> u32 {
        self.log_blowup
    }

    /// Prove the committed table's multilinear evaluation at `point`.
    ///
    /// `context` is absorbed as one framed byte string.  It should identify
    /// the surrounding statement/claim when this PCS is embedded in a larger
    /// protocol; the caller also owns the transcript's outer protocol label.
    pub fn prove_opening(
        &self,
        point: &[Tower256],
        num_queries: usize,
        context: &[u8],
        transcript: &mut BinaryShake256Transcript,
    ) -> Result<Tower256MleOpening, Tower256MleError> {
        if point.len() != self.log_variables {
            return Err(Tower256MleError::InvalidPointLength {
                expected: self.log_variables,
                actual: point.len(),
            });
        }
        if num_queries == 0 {
            return Err(Tower256MleError::InvalidQueryCount);
        }

        let log_domain = self
            .log_variables
            .checked_add(self.log_blowup as usize)
            .ok_or(Tower256MleError::DomainSizeOverflow)?;
        let mut basis = tower256_standard_basis(log_domain)?;
        let mut offset = Tower256::ZERO;
        let mut words = vec![self.initial_word.clone()];
        let mut trees = vec![self.initial_tree.clone()];
        let mut fold_roots = Vec::with_capacity(self.log_variables);

        observe_initial(
            transcript,
            self.table.len(),
            self.log_blowup,
            context,
            &self.root(),
        );

        for (round, &challenge) in point.iter().enumerate() {
            let (next_word, next_basis, next_offset) = fold_reversed_lch_round(
                words.last().ok_or(Tower256MleError::InvalidTableShape)?,
                &basis,
                offset,
                challenge,
            )?;
            let tree = commit_tower256_mle_word(&next_word)?;
            let root = tree.root();
            observe_binding(transcript, round, challenge, next_word.len(), &root);
            words.push(next_word);
            trees.push(tree);
            fold_roots.push(root);
            basis = next_basis;
            offset = next_offset;
        }

        let terminal = evaluate_table_mle(&self.table, point)?;
        let final_word = words.last().ok_or(Tower256MleError::InvalidTableShape)?;
        if final_word.iter().any(|&value| value != terminal) {
            return Err(Tower256MleError::InconsistentTerminalWord);
        }

        observe_final(transcript, terminal, num_queries);
        let query_indices = draw_queries(transcript, self.initial_word.len() / 2, num_queries)?;
        let queries = query_indices
            .into_iter()
            .map(|initial_index| {
                let rounds = (0..self.log_variables)
                    .map(|round| {
                        let word = &words[round];
                        let half = word.len() / 2;
                        let pair_index = initial_index % half;
                        Ok(Tower256MlePairOpening {
                            low: word[pair_index],
                            high: word[half + pair_index],
                            low_path: trees[round].open(pair_index)?,
                            high_path: trees[round].open(half + pair_index)?,
                        })
                    })
                    .collect::<Result<Vec<_>, Tower256MleError>>()?;
                Ok(Tower256MleQueryOpening { rounds })
            })
            .collect::<Result<Vec<_>, Tower256MleError>>()?;

        Ok(Tower256MleOpening {
            terminal,
            fold_roots,
            queries,
        })
    }
}

/// Verify one sampled opening against a reusable commitment root.
///
/// Structural/Merkle-shape failures are returned as errors.  Authentication,
/// terminal, and fold-consistency mismatches return `Ok(false)`.
#[allow(clippy::too_many_arguments)]
pub fn verify_tower256_mle_opening(
    root: &BinaryRoot,
    table_len: usize,
    log_blowup: u32,
    point: &[Tower256],
    expected_terminal: Tower256,
    num_queries: usize,
    context: &[u8],
    proof: &Tower256MleOpening,
    transcript: &mut BinaryShake256Transcript,
) -> Result<bool, Tower256MleError> {
    let (log_variables, log_domain, domain_size) = validate_parameters(table_len, log_blowup)?;
    if point.len() != log_variables {
        return Err(Tower256MleError::InvalidPointLength {
            expected: log_variables,
            actual: point.len(),
        });
    }
    if num_queries == 0 {
        return Err(Tower256MleError::InvalidQueryCount);
    }
    if proof.fold_roots.len() != log_variables
        || proof.queries.len() != num_queries
        || proof
            .queries
            .iter()
            .any(|query| query.rounds.len() != log_variables)
    {
        return Err(Tower256MleError::InvalidProofShape);
    }
    if proof.terminal != expected_terminal {
        return Ok(false);
    }

    observe_initial(transcript, table_len, log_blowup, context, root);
    let mut next_word_len = domain_size / 2;
    for (round, (&challenge, next_root)) in point.iter().zip(&proof.fold_roots).enumerate() {
        observe_binding(transcript, round, challenge, next_word_len, next_root);
        next_word_len /= 2;
    }
    observe_final(transcript, expected_terminal, num_queries);
    let query_indices = draw_queries(transcript, domain_size / 2, num_queries)?;

    let final_size = 1usize
        .checked_shl(log_blowup)
        .ok_or(Tower256MleError::DomainSizeOverflow)?;
    let final_word = vec![expected_terminal; final_size];
    let final_root = commit_tower256_mle_word(&final_word)?.root();
    if proof.fold_roots.last().copied() != Some(final_root) {
        return Ok(false);
    }

    let mut round_bases = Vec::with_capacity(log_variables);
    let mut round_offsets = Vec::with_capacity(log_variables);
    let mut round_beta_inverses = Vec::with_capacity(log_variables);
    let mut basis = tower256_standard_basis(log_domain)?;
    let mut offset = Tower256::ZERO;
    for _ in 0..log_variables {
        let beta = *basis.last().ok_or(Tower256MleError::InvalidProofShape)?;
        round_bases.push(basis.clone());
        round_offsets.push(offset);
        round_beta_inverses.push(beta.inverse()?);
        basis = basis[..basis.len() - 1]
            .iter()
            .copied()
            .map(|value| additive_fold_map(beta, value))
            .collect();
        offset = additive_fold_map(beta, offset);
    }

    for (&initial_index, query) in query_indices.iter().zip(&proof.queries) {
        let mut word_len = domain_size;
        for round in 0..log_variables {
            let half = word_len / 2;
            let pair_index = initial_index % half;
            let opening = &query.rounds[round];
            let current_root = if round == 0 {
                root
            } else {
                &proof.fold_roots[round - 1]
            };
            if !verify_tower256_mle_word_opening(
                word_len,
                pair_index,
                opening.low,
                &opening.low_path,
                current_root,
            )? || !verify_tower256_mle_word_opening(
                word_len,
                half + pair_index,
                opening.high,
                &opening.high_path,
                current_root,
            )? {
                return Ok(false);
            }

            let x = domain_point(
                &round_bases[round][..round_bases[round].len() - 1],
                round_offsets[round],
                pair_index,
            );
            let expected = additive_fold_pair_with_inverse(
                point[round],
                x,
                opening.low,
                opening.high,
                round_beta_inverses[round],
            );
            let actual = if round + 1 == log_variables {
                expected_terminal
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
                return Ok(false);
            }
            word_len = half;
        }
    }
    Ok(true)
}

/// Canonical little-endian coordinate-bit basis for the additive domain.
pub fn tower256_standard_basis(log_domain: usize) -> Result<Vec<Tower256>, Tower256MleError> {
    if log_domain > 256 {
        return Err(Tower256MleError::DomainTooLarge { log_domain });
    }
    Ok((0..log_domain)
        .map(|bit| {
            let mut limbs = [0u64; 4];
            limbs[bit / 64] = 1u64 << (bit % 64);
            Tower256::from_limbs(limbs)
        })
        .collect())
}

/// LSB Boolean values to LSB multilinear monomial coefficients.
pub fn boolean_mobius_coefficients(table: &[Tower256]) -> Result<Vec<Tower256>, Tower256MleError> {
    validate_table(table.len())?;
    let mut coefficients = table.to_vec();
    let variables = table.len().trailing_zeros() as usize;
    for bit in 0..variables {
        let flag = 1usize << bit;
        for mask in 0..table.len() {
            if mask & flag != 0 {
                coefficients[mask] = coefficients[mask].add(coefficients[mask ^ flag]);
            }
        }
    }
    Ok(coefficients)
}

/// Literal multilinear evaluation of an LSB-first Boolean table.
pub fn evaluate_table_mle(
    table: &[Tower256],
    point: &[Tower256],
) -> Result<Tower256, Tower256MleError> {
    validate_table(table.len())?;
    let expected = table.len().trailing_zeros() as usize;
    if point.len() != expected {
        return Err(Tower256MleError::InvalidPointLength {
            expected,
            actual: point.len(),
        });
    }
    let mut layer = table.to_vec();
    for &challenge in point {
        layer = layer
            .chunks_exact(2)
            .map(|pair| pair[0].add(challenge.mul(pair[0].add(pair[1]))))
            .collect();
    }
    layer
        .first()
        .copied()
        .ok_or(Tower256MleError::InvalidTableShape)
}

/// Fast reversed-LCH encoding on the ordinary little-endian domain order.
pub fn reversed_lch_encode(
    coefficients: &[Tower256],
    basis: &[Tower256],
    offset: Tower256,
) -> Result<Vec<Tower256>, Tower256MleError> {
    let expected_len = 1usize
        .checked_shl(basis.len() as u32)
        .ok_or(Tower256MleError::DomainSizeOverflow)?;
    if coefficients.len() != expected_len {
        return Err(Tower256MleError::InvalidTableShape);
    }
    let reversed_basis = basis.iter().copied().rev().collect::<Vec<_>>();
    let mut reversed_domain_word = coefficients.to_vec();
    forward_in_place(&mut reversed_domain_word, &reversed_basis, offset)?;
    if basis.is_empty() {
        return Ok(reversed_domain_word);
    }
    Ok((0..reversed_domain_word.len())
        .map(|index| reversed_domain_word[reverse_low_bits(index, basis.len())])
        .collect())
}

/// One reversed-LCH runtime fold and the transported affine domain.
pub fn fold_reversed_lch_round(
    word: &[Tower256],
    basis: &[Tower256],
    offset: Tower256,
    challenge: Tower256,
) -> Result<(Vec<Tower256>, Vec<Tower256>, Tower256), Tower256MleError> {
    let expected_len = 1usize
        .checked_shl(basis.len() as u32)
        .ok_or(Tower256MleError::DomainSizeOverflow)?;
    if word.len() < 2 || word.len() != expected_len {
        return Err(Tower256MleError::InvalidTableShape);
    }
    let beta = *basis.last().ok_or(Tower256MleError::InvalidTableShape)?;
    let beta_inverse = beta.inverse()?;
    let half = word.len() / 2;
    let points = domain_points(&basis[..basis.len() - 1], offset);
    let folded = (0..half)
        .map(|index| {
            additive_fold_pair_with_inverse(
                challenge,
                points[index],
                word[index],
                word[half + index],
                beta_inverse,
            )
        })
        .collect();
    let next_basis = basis[..basis.len() - 1]
        .iter()
        .copied()
        .map(|value| additive_fold_map(beta, value))
        .collect();
    let next_offset = additive_fold_map(beta, offset);
    Ok((folded, next_basis, next_offset))
}

/// Commit exact 32-byte Tower256 leaves using the binary additive domain.
pub fn commit_tower256_mle_word(
    word: &[Tower256],
) -> Result<BinaryMerkleTree<BinaryRoot>, Tower256MleError> {
    let payloads = word
        .iter()
        .copied()
        .map(Tower256::to_le_bytes)
        .collect::<Vec<_>>();
    Ok(BinaryMerkleTree::build(
        &BinaryShake256V1,
        BinaryHashDomain::AdditiveFri,
        &payloads,
    )?)
}

pub fn verify_tower256_mle_word_opening(
    leaf_count: usize,
    index: usize,
    value: Tower256,
    path: &BinaryMerklePath<BinaryRoot>,
    root: &BinaryRoot,
) -> Result<bool, Tower256MleError> {
    Ok(verify_binary_opening(
        &BinaryShake256V1,
        BinaryHashDomain::AdditiveFri,
        leaf_count,
        index,
        &value.to_le_bytes(),
        path,
        root,
    )?)
}

fn validate_parameters(
    table_len: usize,
    log_blowup: u32,
) -> Result<(usize, usize, usize), Tower256MleError> {
    validate_table(table_len)?;
    let log_variables = table_len.trailing_zeros() as usize;
    let log_domain = log_variables
        .checked_add(log_blowup as usize)
        .ok_or(Tower256MleError::DomainSizeOverflow)?;
    if log_domain > TOWER256_MLE_MAX_LOG_DOMAIN {
        return Err(Tower256MleError::DomainTooLarge { log_domain });
    }
    let domain_size = 1usize
        .checked_shl(log_domain as u32)
        .ok_or(Tower256MleError::DomainSizeOverflow)?;
    Ok((log_variables, log_domain, domain_size))
}

fn validate_table(table_len: usize) -> Result<(), Tower256MleError> {
    if table_len < 2 || !table_len.is_power_of_two() {
        Err(Tower256MleError::InvalidTableShape)
    } else {
        Ok(())
    }
}

fn forward_in_place(
    values: &mut [Tower256],
    basis: &[Tower256],
    offset: Tower256,
) -> Result<(), Tower256MleError> {
    let gamma = vanishing_constants(basis)?;
    forward_recursive(values, basis, &gamma, offset)
}

fn vanishing_constants(basis: &[Tower256]) -> Result<Vec<Tower256>, Tower256MleError> {
    let mut gamma = Vec::with_capacity(basis.len());
    for (index, &beta) in basis.iter().enumerate() {
        let value = subspace_vanishing_eval(&gamma, beta);
        if value.is_zero() {
            return Err(Tower256MleError::DependentBasis { index });
        }
        gamma.push(value);
    }
    Ok(gamma)
}

fn subspace_vanishing_eval(gamma: &[Tower256], x: Tower256) -> Tower256 {
    gamma.iter().copied().fold(x, |value, coefficient| {
        value.square().add(coefficient.mul(value))
    })
}

fn forward_recursive(
    data: &mut [Tower256],
    basis: &[Tower256],
    gamma: &[Tower256],
    offset: Tower256,
) -> Result<(), Tower256MleError> {
    let Some(last) = basis.len().checked_sub(1) else {
        return Ok(());
    };
    let half = data.len() / 2;
    let at_offset = subspace_vanishing_eval(&gamma[..last], offset);
    let at_right = at_offset.add(gamma[last]);
    for index in 0..half {
        let low = data[index];
        let high = data[half + index];
        data[index] = low.add(at_offset.mul(high));
        data[half + index] = low.add(at_right.mul(high));
    }
    let right_offset = offset.add(basis[last]);
    let (left, right) = data.split_at_mut(half);
    forward_recursive(left, &basis[..last], &gamma[..last], offset)?;
    forward_recursive(right, &basis[..last], &gamma[..last], right_offset)
}

#[inline]
fn additive_fold_map(beta: Tower256, x: Tower256) -> Tower256 {
    x.square().add(beta.mul(x))
}

#[inline]
fn additive_fold_pair_with_inverse(
    challenge: Tower256,
    x: Tower256,
    low: Tower256,
    high: Tower256,
    beta_inverse: Tower256,
) -> Tower256 {
    let odd = low.add(high).mul(beta_inverse);
    low.add(x.add(challenge).mul(odd))
}

fn domain_points(basis: &[Tower256], offset: Tower256) -> Vec<Tower256> {
    let mut points = vec![offset];
    for &beta in basis {
        let old_len = points.len();
        for index in 0..old_len {
            points.push(points[index].add(beta));
        }
    }
    points
}

fn domain_point(basis: &[Tower256], offset: Tower256, index: usize) -> Tower256 {
    basis
        .iter()
        .copied()
        .enumerate()
        .fold(offset, |point, (bit, beta)| {
            if index & (1usize << bit) != 0 {
                point.add(beta)
            } else {
                point
            }
        })
}

fn observe_initial(
    transcript: &mut BinaryShake256Transcript,
    table_len: usize,
    log_blowup: u32,
    context: &[u8],
    root: &BinaryRoot,
) {
    transcript.observe_bytes(b"tower256-mle/protocol", TOWER256_MLE_PROTOCOL_LABEL);
    transcript.observe_bytes(b"tower256-mle/context", context);
    transcript.observe_bytes(b"tower256-mle/hash-suite", BinaryShake256V1::SUITE_ID);
    transcript.observe_u64(b"tower256-mle/tower-level", TOWER_256_LEVEL as u64);
    transcript.observe_u64(b"tower256-mle/leaf-bytes", TOWER256_MLE_LEAF_BYTES as u64);
    transcript.observe_u64(b"tower256-mle/table-length", table_len as u64);
    transcript.observe_u64(
        b"tower256-mle/log-variables",
        table_len.trailing_zeros() as u64,
    );
    transcript.observe_u64(b"tower256-mle/log-blowup", log_blowup as u64);
    transcript.observe_bytes(b"tower256-mle/basis", b"standard-coordinate-bits-lsb/v1");
    transcript.observe_bytes(b"tower256-mle/offset", &Tower256::ZERO.to_le_bytes());
    transcript.observe_root(b"tower256-mle/input-root", root);
}

fn observe_binding(
    transcript: &mut BinaryShake256Transcript,
    round: usize,
    challenge: Tower256,
    next_word_len: usize,
    next_root: &BinaryRoot,
) {
    transcript.observe_u64(b"tower256-mle/bind-round", round as u64);
    transcript.observe_bytes(
        b"tower256-mle/evaluation-coordinate",
        &challenge.to_le_bytes(),
    );
    transcript.observe_u64(b"tower256-mle/next-word-length", next_word_len as u64);
    transcript.observe_root(b"tower256-mle/next-root", next_root);
}

fn observe_final(
    transcript: &mut BinaryShake256Transcript,
    terminal: Tower256,
    num_queries: usize,
) {
    transcript.observe_bytes(b"tower256-mle/terminal", &terminal.to_le_bytes());
    transcript.observe_u64(b"tower256-mle/num-queries", num_queries as u64);
}

fn draw_queries(
    transcript: &mut BinaryShake256Transcript,
    pair_count: usize,
    num_queries: usize,
) -> Result<Vec<usize>, Tower256MleError> {
    if pair_count == 0 || !pair_count.is_power_of_two() || num_queries == 0 {
        return Err(Tower256MleError::InvalidQueryCount);
    }
    Ok((0..num_queries)
        .map(|query| {
            transcript.observe_u64(b"tower256-mle/query-number", query as u64);
            (transcript.sample_gf2_64(b"tower256-mle/query-index") as usize) & (pair_count - 1)
        })
        .collect())
}

fn reverse_low_bits(value: usize, bits: usize) -> usize {
    debug_assert!(bits > 0 && bits < usize::BITS as usize);
    value.reverse_bits() >> (usize::BITS as usize - bits)
}
