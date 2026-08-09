//! Sampled multiplicative FRI with BabyBear⁶ folds and atomic challenges.
//!
//! An honest input polynomial may have BabyBear coefficients, but it is lifted
//! before commitment and every committed value, fold challenge, folded value,
//! and final coefficient has type [`Ext6`].  There is no `Ext4` path here.
//!
//! Commitments use a typed [`HashSuite`] with [`BinaryRoot`] roots.  The
//! `BinaryShake256V1` instantiation is byte-native and non-demo; collision
//! resistance and shared-RO composition remain assumptions rather than claims
//! of this runtime reference.  Transcript challenges come only from
//! [`WideExt6Backend`] through its atomic six-coordinate method.
//!
//! The verifier binds the exact degree/rate pair `(degree_bound, domain_size)`,
//! every round root, fixed six-limb leaf encodings, and the final low-degree
//! polynomial before drawing sampled query positions.  It reconstructs and
//! commits the complete final word, then checks sampled Merkle openings and the
//! multiplicative FRI fold identity at every preceding level.

use core::fmt;

use crate::binary_hash::{BinaryHashDomain, BinaryRoot, HashSuite};
use crate::binary_merkle::{
    verify_binary_opening, BinaryMerkleError, BinaryMerklePath, BinaryMerkleTree,
};
use crate::field4::{binv, bmul, bpow, two_adic_generator, HALF, P, TWO_ADIC_BITS};
use crate::field6::Ext6;
use crate::transcript_ext6::{Ext6Transcript, Ext6TranscriptError, WideExt6Backend};

const PROTOCOL_LABEL: &[u8] = b"minidregg/multiplicative-fri-ext6/v1";
const LEAF_FRAME_TAG: &[u8] = b"MDRG-MUL-FRI-EXT6-LEAF-V1";
const EXT6_LEAF_TAG: [u8; 4] = *b"E6L1";
pub const EXT6_LEAF_BYTES: usize = 4 + 6 * 4;

const PROTOCOL_DOMAIN: u64 = 0x4d36_5052; // "M6PR"
const HASH_SUITE_DOMAIN: u64 = 0x4d36_4853; // "M6HS"
const STATEMENT_DOMAIN: u64 = 0x4d36_5354; // "M6ST"
const ROUND_META_DOMAIN: u64 = 0x4d36_524d; // "M6RM"
const ROUND_ROOT_DOMAIN: u64 = 0x4d36_5254; // "M6RT"
const ROUND_BETA_DOMAIN: u64 = 0x4d36_4245; // "M6BE"
const FINAL_META_DOMAIN: u64 = 0x4d36_464d; // "M6FM"
const FINAL_COEFF_DOMAIN: u64 = 0x4d36_4643; // "M6FC"
const QUERY_INDEX_DOMAIN: u64 = 0x4d36_5149; // "M6QI"
const QUERY_DRAW_DOMAIN: u64 = 0x4d36_5144; // "M6QD"

/// Exact statement whose rate is `degree_bound / 2^log_domain`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ext6FriStatement {
    pub input_root: BinaryRoot,
    pub log_domain: u32,
    pub degree_bound: usize,
    pub fold_rounds: usize,
    pub num_queries: usize,
}

/// One authenticated `(f(x), f(-x))` pair at a committed FRI level.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ext6FriPairOpening {
    pub low: Ext6,
    pub high: Ext6,
    pub low_path: BinaryMerklePath<BinaryRoot>,
    pub high_path: BinaryMerklePath<BinaryRoot>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ext6FriQueryOpening {
    pub rounds: Vec<Ext6FriPairOpening>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ext6FriProof {
    /// Roots for lengths `n, n/2, ..., n/2^fold_rounds`.
    pub roots: Vec<BinaryRoot>,
    /// Exactly `ceil(degree_bound / 2^fold_rounds)` coefficients.
    pub final_coefficients: Vec<Ext6>,
    /// Query indices are transcript-derived and therefore not proof-carried.
    pub queries: Vec<Ext6FriQueryOpening>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ext6FriError {
    InvalidStatement(String),
    NonCanonicalCoefficient { index: usize, value: u64 },
    InvalidProofShape,
    InputRootMismatch,
    FinalRootMismatch,
    Merkle(BinaryMerkleError),
    Transcript(Ext6TranscriptError),
    InvalidOpening { query: usize, round: usize },
    FoldMismatch { query: usize, round: usize },
}

impl fmt::Display for Ext6FriError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidStatement(message) => write!(f, "invalid Ext6 FRI statement: {message}"),
            Self::NonCanonicalCoefficient { index, value } => {
                write!(f, "base coefficient {index} is non-canonical: {value}")
            }
            Self::InvalidProofShape => write!(f, "invalid Ext6 FRI proof shape"),
            Self::InputRootMismatch => write!(f, "first FRI root differs from the statement root"),
            Self::FinalRootMismatch => {
                write!(
                    f,
                    "final low-degree polynomial does not match the final root"
                )
            }
            Self::Merkle(error) => error.fmt(f),
            Self::Transcript(error) => error.fmt(f),
            Self::InvalidOpening { query, round } => {
                write!(f, "query {query}, round {round} has an invalid opening")
            }
            Self::FoldMismatch { query, round } => {
                write!(f, "query {query}, round {round} violates the Ext6 fold")
            }
        }
    }
}

impl std::error::Error for Ext6FriError {}

impl From<BinaryMerkleError> for Ext6FriError {
    fn from(error: BinaryMerkleError) -> Self {
        Self::Merkle(error)
    }
}

impl From<Ext6TranscriptError> for Ext6FriError {
    fn from(error: Ext6TranscriptError) -> Self {
        Self::Transcript(error)
    }
}

/// Fixed leaf wire representation: `E6L1 || c0_u32_le || ... || c5_u32_le`.
pub fn ext6_leaf_payload(value: Ext6) -> [u8; EXT6_LEAF_BYTES] {
    let mut payload = [0u8; EXT6_LEAF_BYTES];
    payload[..4].copy_from_slice(&EXT6_LEAF_TAG);
    for (lane, &coefficient) in value.limbs().iter().enumerate() {
        payload[4 + 4 * lane..8 + 4 * lane].copy_from_slice(&(coefficient as u32).to_le_bytes());
    }
    payload
}

/// Round-specific wrapper around a typed binary hash suite.
///
/// The FRI round and inner suite ID are injected into every leaf hash. Internal
/// roots inherit that separation from their children.
struct Ext6FriRoundHash<'a, H> {
    inner: &'a H,
    round: u32,
}

impl<H: HashSuite<Root = BinaryRoot>> HashSuite for Ext6FriRoundHash<'_, H> {
    type Root = BinaryRoot;

    const SUITE_ID: &'static [u8] = PROTOCOL_LABEL;

    fn hash_leaf(&self, _domain: BinaryHashDomain, index: u64, payload: &[u8]) -> Self::Root {
        let mut framed =
            Vec::with_capacity(LEAF_FRAME_TAG.len() + 4 + 8 + H::SUITE_ID.len() + payload.len());
        framed.extend_from_slice(LEAF_FRAME_TAG);
        framed.extend_from_slice(&self.round.to_le_bytes());
        framed.extend_from_slice(&(H::SUITE_ID.len() as u64).to_le_bytes());
        framed.extend_from_slice(H::SUITE_ID);
        framed.extend_from_slice(payload);
        self.inner
            .hash_leaf(BinaryHashDomain::AdditiveFri, index, &framed)
    }

    fn hash_node(
        &self,
        _domain: BinaryHashDomain,
        level: u32,
        left: &Self::Root,
        right: &Self::Root,
    ) -> Self::Root {
        self.inner
            .hash_node(BinaryHashDomain::AdditiveFri, level, left, right)
    }
}

fn checked_domain_size(log_domain: u32) -> Result<usize, Ext6FriError> {
    if log_domain > TWO_ADIC_BITS {
        return Err(Ext6FriError::InvalidStatement(format!(
            "log domain {log_domain} exceeds BabyBear two-adicity {TWO_ADIC_BITS}"
        )));
    }
    1usize
        .checked_shl(log_domain)
        .ok_or_else(|| Ext6FriError::InvalidStatement("domain size overflow".into()))
}

fn final_degree_bound(degree_bound: usize, fold_rounds: usize) -> usize {
    ((degree_bound - 1) >> fold_rounds) + 1
}

fn validate_statement_shape(
    log_domain: u32,
    degree_bound: usize,
    fold_rounds: usize,
    num_queries: usize,
) -> Result<(usize, usize, usize), Ext6FriError> {
    let domain_size = checked_domain_size(log_domain)?;
    if degree_bound == 0 || degree_bound > domain_size {
        return Err(Ext6FriError::InvalidStatement(format!(
            "degree bound {degree_bound} is outside 1..={domain_size}"
        )));
    }
    if fold_rounds == 0 || fold_rounds > log_domain as usize {
        return Err(Ext6FriError::InvalidStatement(format!(
            "fold rounds {fold_rounds} are outside 1..={log_domain}"
        )));
    }
    if num_queries == 0 || num_queries as u128 >= P as u128 {
        return Err(Ext6FriError::InvalidStatement(
            "query count must be nonzero and fit one BabyBear element".into(),
        ));
    }
    let final_len = domain_size >> fold_rounds;
    let final_bound = final_degree_bound(degree_bound, fold_rounds);
    Ok((domain_size, final_len, final_bound))
}

fn commit_word<H: HashSuite<Root = BinaryRoot>>(
    word: &[Ext6],
    round: usize,
    hash: &H,
) -> Result<BinaryMerkleTree<BinaryRoot>, Ext6FriError> {
    let round = u32::try_from(round)
        .map_err(|_| Ext6FriError::InvalidStatement("FRI round index overflow".into()))?;
    let round_hash = Ext6FriRoundHash { inner: hash, round };
    let payloads = word
        .iter()
        .copied()
        .map(ext6_leaf_payload)
        .collect::<Vec<_>>();
    Ok(BinaryMerkleTree::build(
        &round_hash,
        BinaryHashDomain::AdditiveFri,
        &payloads,
    )?)
}

fn verify_opening<H: HashSuite<Root = BinaryRoot>>(
    hash: &H,
    round: usize,
    leaf_count: usize,
    index: usize,
    value: Ext6,
    path: &BinaryMerklePath<BinaryRoot>,
    root: &BinaryRoot,
) -> Result<bool, Ext6FriError> {
    let round = u32::try_from(round)
        .map_err(|_| Ext6FriError::InvalidStatement("FRI round index overflow".into()))?;
    let round_hash = Ext6FriRoundHash { inner: hash, round };
    Ok(verify_binary_opening(
        &round_hash,
        BinaryHashDomain::AdditiveFri,
        leaf_count,
        index,
        &ext6_leaf_payload(value),
        path,
        root,
    )?)
}

/// Multiplicative FRI pair fold over Ext6 with a base-field twiddle.
pub fn fold_pair_ext6(lo: Ext6, hi: Ext6, beta: Ext6, twiddle: u64) -> Ext6 {
    lo.add(hi)
        .base_mul(HALF)
        .add(lo.sub(hi).mul(beta).base_mul(twiddle))
}

fn level_twiddle(log_n: u32, index: usize) -> u64 {
    bmul(HALF, bpow(binv(two_adic_generator(log_n)), index as u64))
}

fn fold_word(word: &[Ext6], beta: Ext6) -> Vec<Ext6> {
    let half = word.len() / 2;
    let log_n = word.len().trailing_zeros();
    (0..half)
        .map(|index| {
            fold_pair_ext6(
                word[index],
                word[index + half],
                beta,
                level_twiddle(log_n, index),
            )
        })
        .collect()
}

fn fold_coefficients(coefficients: &[Ext6], beta: Ext6) -> Vec<Ext6> {
    coefficients
        .chunks(2)
        .map(|pair| {
            let odd = pair.get(1).copied().unwrap_or(Ext6::ZERO);
            pair[0].add(odd.mul(beta))
        })
        .collect()
}

fn evaluate_polynomial(coefficients: &[Ext6], log_domain: u32) -> Vec<Ext6> {
    let domain_size = 1usize << log_domain;
    let generator = two_adic_generator(log_domain);
    let mut point = 1;
    let mut word = Vec::with_capacity(domain_size);
    for _ in 0..domain_size {
        let value = coefficients
            .iter()
            .rev()
            .fold(Ext6::ZERO, |acc, &coefficient| {
                acc.base_mul(point).add(coefficient)
            });
        word.push(value);
        point = bmul(point, generator);
    }
    word
}

fn bytes_as_field_record(bytes: &[u8]) -> Result<Vec<u64>, Ext6FriError> {
    if bytes.len() as u128 >= P as u128 {
        return Err(Ext6FriError::InvalidStatement(
            "byte record length does not fit BabyBear".into(),
        ));
    }
    let mut fields = Vec::with_capacity(1 + bytes.len().div_ceil(2));
    fields.push(bytes.len() as u64);
    for chunk in bytes.chunks(2) {
        let high = chunk.get(1).copied().unwrap_or(0) as u64;
        fields.push(chunk[0] as u64 | (high << 8));
    }
    Ok(fields)
}

fn root_as_field_record(root: &BinaryRoot) -> Vec<u64> {
    root.as_bytes()
        .chunks_exact(2)
        .map(|chunk| u16::from_le_bytes([chunk[0], chunk[1]]) as u64)
        .collect()
}

fn start_transcript<'a, H: HashSuite<Root = BinaryRoot>, B: WideExt6Backend>(
    backend: &'a mut B,
    statement: &Ext6FriStatement,
) -> Result<Ext6Transcript<&'a mut B>, Ext6FriError> {
    let (domain_size, final_len, final_bound) = validate_statement_shape(
        statement.log_domain,
        statement.degree_bound,
        statement.fold_rounds,
        statement.num_queries,
    )?;
    let mut transcript = Ext6Transcript::new(backend)?;
    transcript.absorb_record(PROTOCOL_DOMAIN, &bytes_as_field_record(PROTOCOL_LABEL)?)?;
    transcript.absorb_record(HASH_SUITE_DOMAIN, &bytes_as_field_record(H::SUITE_ID)?)?;
    transcript.absorb_record(
        STATEMENT_DOMAIN,
        &[
            1,
            statement.log_domain as u64,
            domain_size as u64,
            statement.degree_bound as u64,
            statement.fold_rounds as u64,
            final_len as u64,
            final_bound as u64,
            statement.num_queries as u64,
        ],
    )?;
    Ok(transcript)
}

fn observe_round_root<B: WideExt6Backend>(
    transcript: &mut Ext6Transcript<B>,
    round: usize,
    word_len: usize,
    root: &BinaryRoot,
) -> Result<(), Ext6FriError> {
    transcript.absorb_record(ROUND_META_DOMAIN, &[round as u64, word_len as u64])?;
    transcript.absorb_record(ROUND_ROOT_DOMAIN, &root_as_field_record(root))?;
    Ok(())
}

fn observe_final_coefficients<B: WideExt6Backend>(
    transcript: &mut Ext6Transcript<B>,
    coefficients: &[Ext6],
) -> Result<(), Ext6FriError> {
    transcript.absorb_record(FINAL_META_DOMAIN, &[coefficients.len() as u64])?;
    transcript.absorb_ext6_record(FINAL_COEFF_DOMAIN, coefficients)?;
    Ok(())
}

fn draw_queries<B: WideExt6Backend>(
    transcript: &mut Ext6Transcript<B>,
    pair_count: usize,
    count: usize,
) -> Result<Vec<usize>, Ext6FriError> {
    let pair_count_u64 = pair_count as u64;
    let limit = P - P % pair_count_u64;
    let mut queries = Vec::with_capacity(count);
    for query_number in 0..count {
        transcript.absorb_record(QUERY_INDEX_DOMAIN, &[query_number as u64])?;
        loop {
            let candidate = transcript.squeeze_ext6(QUERY_DRAW_DOMAIN)?.limbs()[0];
            if candidate < limit {
                queries.push((candidate % pair_count_u64) as usize);
                break;
            }
        }
    }
    Ok(queries)
}

/// Honest prover from canonical BabyBear coefficients.
///
/// `base_coefficients.len() <= degree_bound`; omitted high coefficients are
/// zero. The returned initial root can be attached directly to the surrounding
/// trace/codeword statement.
pub fn prove_base_sampled<H: HashSuite<Root = BinaryRoot>, B: WideExt6Backend>(
    base_coefficients: &[u64],
    log_domain: u32,
    degree_bound: usize,
    fold_rounds: usize,
    num_queries: usize,
    hash: &H,
    backend: &mut B,
) -> Result<(Ext6FriStatement, Ext6FriProof), Ext6FriError> {
    let (domain_size, _final_len, expected_final_bound) =
        validate_statement_shape(log_domain, degree_bound, fold_rounds, num_queries)?;
    if base_coefficients.len() > degree_bound {
        return Err(Ext6FriError::InvalidStatement(format!(
            "{} coefficients exceed degree bound {degree_bound}",
            base_coefficients.len()
        )));
    }
    let mut coefficients = Vec::with_capacity(degree_bound);
    for (index, &value) in base_coefficients.iter().enumerate() {
        let coefficient = Ext6::try_from_base(value)
            .map_err(|_| Ext6FriError::NonCanonicalCoefficient { index, value })?;
        coefficients.push(coefficient);
    }
    coefficients.resize(degree_bound, Ext6::ZERO);

    let initial_word = evaluate_polynomial(&coefficients, log_domain);
    debug_assert_eq!(initial_word.len(), domain_size);
    let initial_tree = commit_word(&initial_word, 0, hash)?;
    let statement = Ext6FriStatement {
        input_root: initial_tree.root(),
        log_domain,
        degree_bound,
        fold_rounds,
        num_queries,
    };
    let mut transcript = start_transcript::<H, B>(backend, &statement)?;

    let mut words = vec![initial_word];
    let mut trees = Vec::with_capacity(fold_rounds + 1);
    let mut roots = Vec::with_capacity(fold_rounds + 1);
    let mut folded_coefficients = coefficients;
    for round in 0..fold_rounds {
        let tree = if round == 0 {
            initial_tree.clone()
        } else {
            commit_word(
                words.last().ok_or(Ext6FriError::InvalidProofShape)?,
                round,
                hash,
            )?
        };
        let root = tree.root();
        let word_len = words.last().ok_or(Ext6FriError::InvalidProofShape)?.len();
        observe_round_root(&mut transcript, round, word_len, &root)?;
        let beta = transcript.squeeze_ext6(ROUND_BETA_DOMAIN)?;
        let next_word = fold_word(words.last().ok_or(Ext6FriError::InvalidProofShape)?, beta);
        folded_coefficients = fold_coefficients(&folded_coefficients, beta);
        roots.push(root);
        trees.push(tree);
        words.push(next_word);
    }

    if folded_coefficients.len() != expected_final_bound {
        return Err(Ext6FriError::InvalidProofShape);
    }
    let final_word = words.last().ok_or(Ext6FriError::InvalidProofShape)?;
    let final_tree = commit_word(final_word, fold_rounds, hash)?;
    let final_root = final_tree.root();
    observe_round_root(&mut transcript, fold_rounds, final_word.len(), &final_root)?;
    observe_final_coefficients(&mut transcript, &folded_coefficients)?;
    roots.push(final_root);
    trees.push(final_tree);

    let query_indices = draw_queries(&mut transcript, domain_size / 2, num_queries)?;
    let queries = query_indices
        .iter()
        .map(
            |&initial_index| -> Result<Ext6FriQueryOpening, Ext6FriError> {
                let rounds = (0..fold_rounds)
                    .map(|round| -> Result<Ext6FriPairOpening, Ext6FriError> {
                        let word = &words[round];
                        let half = word.len() / 2;
                        let pair_index = initial_index % half;
                        Ok(Ext6FriPairOpening {
                            low: word[pair_index],
                            high: word[half + pair_index],
                            low_path: trees[round].open(pair_index)?,
                            high_path: trees[round].open(half + pair_index)?,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Ext6FriQueryOpening { rounds })
            },
        )
        .collect::<Result<Vec<_>, _>>()?;

    Ok((
        statement,
        Ext6FriProof {
            roots,
            final_coefficients: folded_coefficients,
            queries,
        },
    ))
}

pub fn verify_sampled<H: HashSuite<Root = BinaryRoot>, B: WideExt6Backend>(
    statement: &Ext6FriStatement,
    proof: &Ext6FriProof,
    hash: &H,
    backend: &mut B,
) -> bool {
    check_sampled(statement, proof, hash, backend).is_ok()
}

fn check_sampled<H: HashSuite<Root = BinaryRoot>, B: WideExt6Backend>(
    statement: &Ext6FriStatement,
    proof: &Ext6FriProof,
    hash: &H,
    backend: &mut B,
) -> Result<(), Ext6FriError> {
    let (domain_size, final_len, expected_final_bound) = validate_statement_shape(
        statement.log_domain,
        statement.degree_bound,
        statement.fold_rounds,
        statement.num_queries,
    )?;
    if proof.roots.len() != statement.fold_rounds + 1
        || proof.final_coefficients.len() != expected_final_bound
        || proof.queries.len() != statement.num_queries
        || proof
            .queries
            .iter()
            .any(|query| query.rounds.len() != statement.fold_rounds)
    {
        return Err(Ext6FriError::InvalidProofShape);
    }
    if proof.roots.first().copied() != Some(statement.input_root) {
        return Err(Ext6FriError::InputRootMismatch);
    }

    let mut transcript = start_transcript::<H, B>(backend, statement)?;
    let mut challenges = Vec::with_capacity(statement.fold_rounds);
    let mut word_len = domain_size;
    for round in 0..statement.fold_rounds {
        observe_round_root(&mut transcript, round, word_len, &proof.roots[round])?;
        challenges.push(transcript.squeeze_ext6(ROUND_BETA_DOMAIN)?);
        word_len /= 2;
    }
    observe_round_root(
        &mut transcript,
        statement.fold_rounds,
        final_len,
        &proof.roots[statement.fold_rounds],
    )?;
    observe_final_coefficients(&mut transcript, &proof.final_coefficients)?;
    let query_indices = draw_queries(&mut transcript, domain_size / 2, statement.num_queries)?;

    // Final degree check: exactly the advertised low coefficients reconstruct
    // the committed final evaluation word; no high coefficient is proof-carried.
    let final_word = evaluate_polynomial(
        &proof.final_coefficients,
        statement.log_domain - statement.fold_rounds as u32,
    );
    if final_word.len() != final_len
        || commit_word(&final_word, statement.fold_rounds, hash)?.root()
            != proof.roots[statement.fold_rounds]
    {
        return Err(Ext6FriError::FinalRootMismatch);
    }

    for (query_number, (&initial_index, query)) in
        query_indices.iter().zip(&proof.queries).enumerate()
    {
        let mut level_len = domain_size;
        for round in 0..statement.fold_rounds {
            let half = level_len / 2;
            let pair_index = initial_index % half;
            let opening = &query.rounds[round];
            if !verify_opening(
                hash,
                round,
                level_len,
                pair_index,
                opening.low,
                &opening.low_path,
                &proof.roots[round],
            )? || !verify_opening(
                hash,
                round,
                level_len,
                half + pair_index,
                opening.high,
                &opening.high_path,
                &proof.roots[round],
            )? {
                return Err(Ext6FriError::InvalidOpening {
                    query: query_number,
                    round,
                });
            }

            let expected = fold_pair_ext6(
                opening.low,
                opening.high,
                challenges[round],
                level_twiddle(level_len.trailing_zeros(), pair_index),
            );
            let actual = if round + 1 == statement.fold_rounds {
                final_word[pair_index]
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
                return Err(Ext6FriError::FoldMismatch {
                    query: query_number,
                    round,
                });
            }
            level_len = half;
        }
    }
    Ok(())
}
