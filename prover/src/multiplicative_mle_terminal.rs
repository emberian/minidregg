//! A sampled committed MLE terminal over multiplicative RS and BabyBear^6.
//!
//! For an LSB-first multilinear value table `a[0..2^v]`, first compute its
//! Boolean subset-Mobius coefficients `c`: for each bit, subtract the entry
//! without that bit from every entry carrying it.  Then
//!
//! ```text
//! MLE(a, r) = sum_mask c[mask] * product_{i in mask} r_i.
//! ```
//!
//! Regard `c` as the coefficients of `f(X) = sum_i c_i X^i` and evaluate `f`
//! on a BabyBear multiplicative domain of size `M = 2^v * B`.  Binding the next
//! LSB variable to `r` replaces adjacent coefficients by
//! `c[2j] + r*c[2j+1]`.  On the committed evaluation word this is exactly the
//! multiplicative even/odd fold
//!
//! ```text
//! even(x) + r*odd(x)
//!   = (f(x)+f(-x))/2 + r*(f(x)-f(-x))/(2x).
//! ```
//!
//! [`MleTerminalProverState`] exposes `commit_initial`, `bind`, and `finish` so
//! a gate transcript can interleave `sumcheck message -> r_i -> next PCS root`.
//! Roots and challenges are fixed before sampled paths are materialized.  After
//! all `v` binds, the remaining `B` evaluations must all equal the claimed MLE
//! terminal; the verifier recomputes that constant codeword and its root.
//!
//! This is sampled fold consistency, not a full opening.  Its exact remaining
//! composition seam is `[MLE-PCS-factored-selector]`: the initial committed
//! word is not yet proved to encode the Boolean Mobius transform of the emitted
//! trace's factored gate-residual table.  The clear transform helper below is a
//! provenance bridge, not a succinct proof of that fact.  Binary Merkle
//! binding, transcript XOF security, sampled
//! proximity pricing and unverified Rust execution retain their explicit assumptions.

use core::{convert::Infallible, fmt};

use crate::{
    binary_hash::{BinaryHashDomain, BinaryRoot, HashSuite},
    binary_merkle::{verify_binary_opening, BinaryMerkleError, BinaryMerklePath, BinaryMerkleTree},
    binary_transcript::{BinaryShake256Transcript, TranscriptSuite},
    field4::{binv, bmul, bpow, two_adic_generator, HALF, P, TWO_ADIC_BITS},
    field6::Ext6,
    fri_ext6_reference::ext6_leaf_payload,
    transcript_ext6::{Ext6Transcript, Ext6TranscriptError, WideExt6Backend},
};

pub const MLE_TERMINAL_PROTOCOL_LABEL: &[u8] = b"minidregg/multiplicative-mle-terminal/v1";

const LEAF_FRAME_TAG: &[u8] = b"MDRG-MLE-TERMINAL-LEAF-V1";

const EXT6_PROTOCOL_DOMAIN: u64 = 0x4d54_5052; // "MTPR"
const EXT6_INITIAL_META_DOMAIN: u64 = 0x4d54_494d; // "MTIM"
const EXT6_INITIAL_ROOT_DOMAIN: u64 = 0x4d54_4952; // "MTIR"
const EXT6_BIND_META_DOMAIN: u64 = 0x4d54_424d; // "MTBM"
const EXT6_BIND_VALUE_DOMAIN: u64 = 0x4d54_4256; // "MTBV"
const EXT6_BIND_ROOT_DOMAIN: u64 = 0x4d54_4252; // "MTBR"
const EXT6_FINAL_META_DOMAIN: u64 = 0x4d54_464d; // "MTFM"
const EXT6_FINAL_VALUE_DOMAIN: u64 = 0x4d54_4656; // "MTFV"
const EXT6_QUERY_META_DOMAIN: u64 = 0x4d54_514d; // "MTQM"
const EXT6_QUERY_DRAW_DOMAIN: u64 = 0x4d54_5144; // "MTQD"

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MleTerminalStatement {
    pub input_root: BinaryRoot,
    pub log_variables: u32,
    pub log_blowup: u32,
    pub claimed_terminal: Ext6,
    pub num_queries: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MleTerminalPairOpening {
    pub low: Ext6,
    pub high: Ext6,
    pub low_path: BinaryMerklePath<BinaryRoot>,
    pub high_path: BinaryMerklePath<BinaryRoot>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MleTerminalQueryOpening {
    pub rounds: Vec<MleTerminalPairOpening>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MleTerminalProof {
    /// Roots for lengths `M, M/2, ..., B`.
    pub roots: Vec<BinaryRoot>,
    /// Query positions are transcript-derived and not proof-carried.
    pub queries: Vec<MleTerminalQueryOpening>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MleTerminalError {
    InvalidTableShape,
    InvalidDomain,
    TooManyBindings,
    MissingBindings { expected: usize, actual: usize },
    ClaimedTerminalMismatch,
    InvalidProofShape,
    InputRootMismatch,
    FinalRootMismatch,
    Merkle(BinaryMerkleError),
    Transcript(String),
    InvalidOpening { query: usize, round: usize },
    FoldMismatch { query: usize, round: usize },
}

impl From<BinaryMerkleError> for MleTerminalError {
    fn from(value: BinaryMerkleError) -> Self {
        Self::Merkle(value)
    }
}

impl fmt::Display for MleTerminalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidTableShape => write!(
                f,
                "MLE terminal table must have power-of-two length at least two"
            ),
            Self::InvalidDomain => write!(f, "invalid multiplicative MLE terminal domain"),
            Self::TooManyBindings => write!(f, "too many MLE terminal bindings"),
            Self::MissingBindings { expected, actual } => {
                write!(f, "MLE terminal has {actual} bindings, expected {expected}")
            }
            Self::ClaimedTerminalMismatch => {
                write!(f, "final RS word is not the claimed MLE constant")
            }
            Self::InvalidProofShape => write!(f, "invalid MLE terminal proof shape"),
            Self::InputRootMismatch => write!(f, "MLE terminal input root mismatch"),
            Self::FinalRootMismatch => write!(f, "MLE terminal constant-codeword root mismatch"),
            Self::Merkle(error) => error.fmt(f),
            Self::Transcript(error) => write!(f, "MLE terminal transcript: {error}"),
            Self::InvalidOpening { query, round } => {
                write!(
                    f,
                    "MLE terminal query {query}, round {round} has an invalid opening"
                )
            }
            Self::FoldMismatch { query, round } => {
                write!(
                    f,
                    "MLE terminal query {query}, round {round} violates the bind fold"
                )
            }
        }
    }
}

impl std::error::Error for MleTerminalError {}

/// Convert an LSB-indexed Boolean value table to its multilinear monomial
/// coefficients by subset Mobius inversion.
///
/// This clear helper is intentionally exposed for the future emitted-table
/// provenance check.  Calling it in the prover does not make that check
/// succinct or tie an opaque input root to gate selectors.
pub fn boolean_mobius_coefficients(table: &[Ext6]) -> Result<Vec<Ext6>, MleTerminalError> {
    if table.len() < 2 || !table.len().is_power_of_two() {
        return Err(MleTerminalError::InvalidTableShape);
    }
    let mut coefficients = table.to_vec();
    let variables = table.len().trailing_zeros() as usize;
    for bit in 0..variables {
        let flag = 1usize << bit;
        for mask in 0..table.len() {
            if mask & flag != 0 {
                coefficients[mask] = coefficients[mask].sub(coefficients[mask ^ flag]);
            }
        }
    }
    Ok(coefficients)
}

/// Transcript hook for interleaving gate sumcheck and PCS roots.
///
/// A caller may use the blanket byte-native implementation or an
/// [`Ext6Transcript`] already carrying gate messages and challenge draws.
pub trait MleTerminalTranscript {
    type Error: fmt::Display;

    fn observe_initial(
        &mut self,
        hash_suite_id: &[u8],
        log_variables: u32,
        log_blowup: u32,
        domain_size: usize,
        root: &BinaryRoot,
    ) -> Result<(), Self::Error>;

    /// Called after `challenge` has been supplied and after `next_root` was
    /// committed, preserving `r_i -> root_{i+1}` order.
    fn observe_binding(
        &mut self,
        round: usize,
        challenge: Ext6,
        next_word_len: usize,
        next_root: &BinaryRoot,
    ) -> Result<(), Self::Error>;

    fn observe_final(
        &mut self,
        blowup: usize,
        claimed_terminal: Ext6,
        num_queries: usize,
    ) -> Result<(), Self::Error>;

    fn draw_query_index(
        &mut self,
        query_number: usize,
        pair_count: usize,
    ) -> Result<usize, Self::Error>;
}

impl MleTerminalTranscript for BinaryShake256Transcript {
    type Error = Infallible;

    fn observe_initial(
        &mut self,
        hash_suite_id: &[u8],
        log_variables: u32,
        log_blowup: u32,
        domain_size: usize,
        root: &BinaryRoot,
    ) -> Result<(), Self::Error> {
        self.observe_bytes(b"mle-terminal/protocol", MLE_TERMINAL_PROTOCOL_LABEL);
        self.observe_bytes(b"mle-terminal/hash-suite", hash_suite_id);
        self.observe_u64(b"mle-terminal/log-variables", log_variables as u64);
        self.observe_u64(b"mle-terminal/log-blowup", log_blowup as u64);
        self.observe_u64(b"mle-terminal/domain-size", domain_size as u64);
        self.observe_root(b"mle-terminal/input-root", root);
        Ok(())
    }

    fn observe_binding(
        &mut self,
        round: usize,
        challenge: Ext6,
        next_word_len: usize,
        next_root: &BinaryRoot,
    ) -> Result<(), Self::Error> {
        self.observe_u64(b"mle-terminal/bind-round", round as u64);
        self.observe_bytes(b"mle-terminal/bind-value", &ext6_leaf_payload(challenge));
        self.observe_u64(b"mle-terminal/next-word-length", next_word_len as u64);
        self.observe_root(b"mle-terminal/next-root", next_root);
        Ok(())
    }

    fn observe_final(
        &mut self,
        blowup: usize,
        claimed_terminal: Ext6,
        num_queries: usize,
    ) -> Result<(), Self::Error> {
        self.observe_u64(b"mle-terminal/final-word-length", blowup as u64);
        self.observe_bytes(
            b"mle-terminal/claimed-terminal",
            &ext6_leaf_payload(claimed_terminal),
        );
        self.observe_u64(b"mle-terminal/num-queries", num_queries as u64);
        Ok(())
    }

    fn draw_query_index(
        &mut self,
        query_number: usize,
        pair_count: usize,
    ) -> Result<usize, Self::Error> {
        self.observe_u64(b"mle-terminal/query-number", query_number as u64);
        Ok((self.sample_gf2_64(b"mle-terminal/query-index") as usize) & (pair_count - 1))
    }
}

impl<B: WideExt6Backend> MleTerminalTranscript for Ext6Transcript<B> {
    type Error = Ext6TranscriptError;

    fn observe_initial(
        &mut self,
        hash_suite_id: &[u8],
        log_variables: u32,
        log_blowup: u32,
        domain_size: usize,
        root: &BinaryRoot,
    ) -> Result<(), Self::Error> {
        let mut record = vec![log_variables as u64, log_blowup as u64, domain_size as u64];
        record.extend(bytes_as_u16_fields(MLE_TERMINAL_PROTOCOL_LABEL));
        record.extend(bytes_as_u16_fields(hash_suite_id));
        self.absorb_record(EXT6_PROTOCOL_DOMAIN, &record)?;
        self.absorb_record(
            EXT6_INITIAL_META_DOMAIN,
            &[log_variables as u64, log_blowup as u64, domain_size as u64],
        )?;
        self.absorb_record(EXT6_INITIAL_ROOT_DOMAIN, &root_as_u16_fields(root))
    }

    fn observe_binding(
        &mut self,
        round: usize,
        challenge: Ext6,
        next_word_len: usize,
        next_root: &BinaryRoot,
    ) -> Result<(), Self::Error> {
        self.absorb_record(EXT6_BIND_META_DOMAIN, &[round as u64, next_word_len as u64])?;
        self.absorb_ext6_record(EXT6_BIND_VALUE_DOMAIN, &[challenge])?;
        self.absorb_record(EXT6_BIND_ROOT_DOMAIN, &root_as_u16_fields(next_root))
    }

    fn observe_final(
        &mut self,
        blowup: usize,
        claimed_terminal: Ext6,
        num_queries: usize,
    ) -> Result<(), Self::Error> {
        self.absorb_record(EXT6_FINAL_META_DOMAIN, &[blowup as u64, num_queries as u64])?;
        self.absorb_ext6_record(EXT6_FINAL_VALUE_DOMAIN, &[claimed_terminal])
    }

    fn draw_query_index(
        &mut self,
        query_number: usize,
        pair_count: usize,
    ) -> Result<usize, Self::Error> {
        self.absorb_record(EXT6_QUERY_META_DOMAIN, &[query_number as u64])?;
        let modulus = pair_count as u64;
        let limit = P - P % modulus;
        loop {
            let candidate = self.squeeze_ext6(EXT6_QUERY_DRAW_DOMAIN)?.limbs()[0];
            if candidate < limit {
                return Ok((candidate % modulus) as usize);
            }
        }
    }
}

/// Stateful prover half of the interleavable protocol.
pub struct MleTerminalProverState<H: HashSuite<Root = BinaryRoot>> {
    hash: H,
    log_variables: u32,
    log_blowup: u32,
    coefficients: Vec<Ext6>,
    words: Vec<Vec<Ext6>>,
    trees: Vec<BinaryMerkleTree<BinaryRoot>>,
    roots: Vec<BinaryRoot>,
    bindings: Vec<Ext6>,
}

impl<H: HashSuite<Root = BinaryRoot>> MleTerminalProverState<H> {
    /// Mobius-transform the Boolean value table, then RS-encode and commit its
    /// coefficients before any MLE evaluation challenge is known.
    pub fn commit_initial<T: MleTerminalTranscript>(
        table: &[Ext6],
        log_blowup: u32,
        hash: H,
        transcript: &mut T,
    ) -> Result<Self, MleTerminalError> {
        if table.len() < 2 || !table.len().is_power_of_two() {
            return Err(MleTerminalError::InvalidTableShape);
        }
        let log_variables = table.len().trailing_zeros();
        let log_domain = log_variables
            .checked_add(log_blowup)
            .ok_or(MleTerminalError::InvalidDomain)?;
        let domain_size = checked_domain_size(log_domain)?;
        let coefficients = boolean_mobius_coefficients(table)?;
        let word = evaluate_polynomial(&coefficients, log_domain);
        let tree = commit_word(&word, 0, &hash)?;
        let root = tree.root();
        transcript
            .observe_initial(H::SUITE_ID, log_variables, log_blowup, domain_size, &root)
            .map_err(transcript_error)?;
        Ok(Self {
            hash,
            log_variables,
            log_blowup,
            coefficients,
            words: vec![word],
            trees: vec![tree],
            roots: vec![root],
            bindings: Vec::with_capacity(log_variables as usize),
        })
    }

    pub fn input_root(&self) -> BinaryRoot {
        self.roots[0]
    }

    pub fn bindings_complete(&self) -> bool {
        self.bindings.len() == self.log_variables as usize
    }

    /// Bind the next LSB variable, commit the resulting RS word, then expose
    /// that root to the shared transcript.
    pub fn bind<T: MleTerminalTranscript>(
        &mut self,
        challenge: Ext6,
        transcript: &mut T,
    ) -> Result<BinaryRoot, MleTerminalError> {
        if self.bindings_complete() {
            return Err(MleTerminalError::TooManyBindings);
        }
        let round = self.bindings.len();
        let next_word = fold_word(
            self.words
                .last()
                .ok_or(MleTerminalError::InvalidTableShape)?,
            challenge,
        );
        self.coefficients = fold_coefficients(&self.coefficients, challenge);
        let tree = commit_word(&next_word, round + 1, &self.hash)?;
        let root = tree.root();
        transcript
            .observe_binding(round, challenge, next_word.len(), &root)
            .map_err(transcript_error)?;
        self.bindings.push(challenge);
        self.words.push(next_word);
        self.trees.push(tree);
        self.roots.push(root);
        Ok(root)
    }

    /// Fix the terminal claim and only then derive coherent sampled paths.
    pub fn finish<T: MleTerminalTranscript>(
        self,
        claimed_terminal: Ext6,
        num_queries: usize,
        transcript: &mut T,
    ) -> Result<(MleTerminalStatement, MleTerminalProof), MleTerminalError> {
        let expected_bindings = self.log_variables as usize;
        if self.bindings.len() != expected_bindings {
            return Err(MleTerminalError::MissingBindings {
                expected: expected_bindings,
                actual: self.bindings.len(),
            });
        }
        if num_queries == 0 || num_queries as u128 >= P as u128 {
            return Err(MleTerminalError::InvalidDomain);
        }
        let blowup = checked_domain_size(self.log_blowup)?;
        let final_word = self
            .words
            .last()
            .ok_or(MleTerminalError::InvalidTableShape)?;
        if self.coefficients.as_slice() != [claimed_terminal]
            || final_word.len() != blowup
            || final_word.iter().any(|&value| value != claimed_terminal)
        {
            return Err(MleTerminalError::ClaimedTerminalMismatch);
        }
        transcript
            .observe_final(blowup, claimed_terminal, num_queries)
            .map_err(transcript_error)?;
        let pair_count = self.words[0].len() / 2;
        let query_indices = draw_queries(transcript, pair_count, num_queries)?;
        let queries = query_indices
            .iter()
            .map(
                |&initial_index| -> Result<MleTerminalQueryOpening, MleTerminalError> {
                    let rounds = (0..expected_bindings)
                        .map(
                            |round| -> Result<MleTerminalPairOpening, MleTerminalError> {
                                let word = &self.words[round];
                                let half = word.len() / 2;
                                let pair_index = initial_index % half;
                                Ok(MleTerminalPairOpening {
                                    low: word[pair_index],
                                    high: word[half + pair_index],
                                    low_path: self.trees[round].open(pair_index)?,
                                    high_path: self.trees[round].open(half + pair_index)?,
                                })
                            },
                        )
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(MleTerminalQueryOpening { rounds })
                },
            )
            .collect::<Result<Vec<_>, _>>()?;

        Ok((
            MleTerminalStatement {
                input_root: self.roots[0],
                log_variables: self.log_variables,
                log_blowup: self.log_blowup,
                claimed_terminal,
                num_queries,
            },
            MleTerminalProof {
                roots: self.roots,
                queries,
            },
        ))
    }
}

/// Replay the interleaved roots for an LSB-first evaluation point and verify
/// all sampled folds plus the final constant-codeword root.
pub fn verify_mle_terminal<H: HashSuite<Root = BinaryRoot>, T: MleTerminalTranscript>(
    statement: &MleTerminalStatement,
    evaluation_point: &[Ext6],
    proof: &MleTerminalProof,
    hash: &H,
    transcript: &mut T,
) -> bool {
    check_mle_terminal(statement, evaluation_point, proof, hash, transcript).is_ok()
}

fn check_mle_terminal<H: HashSuite<Root = BinaryRoot>, T: MleTerminalTranscript>(
    statement: &MleTerminalStatement,
    evaluation_point: &[Ext6],
    proof: &MleTerminalProof,
    hash: &H,
    transcript: &mut T,
) -> Result<(), MleTerminalError> {
    if statement.log_variables == 0
        || statement.num_queries == 0
        || statement.num_queries as u128 >= P as u128
        || evaluation_point.len() != statement.log_variables as usize
        || proof.roots.len() != statement.log_variables as usize + 1
        || proof.queries.len() != statement.num_queries
        || proof
            .queries
            .iter()
            .any(|query| query.rounds.len() != statement.log_variables as usize)
    {
        return Err(MleTerminalError::InvalidProofShape);
    }
    let log_domain = statement
        .log_variables
        .checked_add(statement.log_blowup)
        .ok_or(MleTerminalError::InvalidDomain)?;
    let domain_size = checked_domain_size(log_domain)?;
    let blowup = checked_domain_size(statement.log_blowup)?;
    if proof.roots[0] != statement.input_root {
        return Err(MleTerminalError::InputRootMismatch);
    }
    transcript
        .observe_initial(
            H::SUITE_ID,
            statement.log_variables,
            statement.log_blowup,
            domain_size,
            &statement.input_root,
        )
        .map_err(transcript_error)?;
    let mut next_len = domain_size / 2;
    for (round, (&challenge, root)) in evaluation_point
        .iter()
        .zip(proof.roots.iter().skip(1))
        .enumerate()
    {
        transcript
            .observe_binding(round, challenge, next_len, root)
            .map_err(transcript_error)?;
        next_len /= 2;
    }
    if next_len.checked_mul(2) != Some(blowup) {
        return Err(MleTerminalError::InvalidProofShape);
    }
    transcript
        .observe_final(blowup, statement.claimed_terminal, statement.num_queries)
        .map_err(transcript_error)?;
    let query_indices = draw_queries(transcript, domain_size / 2, statement.num_queries)?;

    let constant_word = vec![statement.claimed_terminal; blowup];
    if commit_word(&constant_word, statement.log_variables as usize, hash)?.root()
        != *proof
            .roots
            .last()
            .ok_or(MleTerminalError::InvalidProofShape)?
    {
        return Err(MleTerminalError::FinalRootMismatch);
    }

    for (query_number, (&initial_index, query)) in
        query_indices.iter().zip(&proof.queries).enumerate()
    {
        let mut word_len = domain_size;
        for round in 0..statement.log_variables as usize {
            let half = word_len / 2;
            let pair_index = initial_index % half;
            let opening = &query.rounds[round];
            if !verify_round_opening(
                hash,
                round,
                word_len,
                pair_index,
                opening.low,
                &opening.low_path,
                &proof.roots[round],
            )? || !verify_round_opening(
                hash,
                round,
                word_len,
                half + pair_index,
                opening.high,
                &opening.high_path,
                &proof.roots[round],
            )? {
                return Err(MleTerminalError::InvalidOpening {
                    query: query_number,
                    round,
                });
            }
            let expected = fold_pair(
                opening.low,
                opening.high,
                evaluation_point[round],
                level_twiddle(word_len.trailing_zeros(), pair_index),
            );
            let actual = if round + 1 == statement.log_variables as usize {
                statement.claimed_terminal
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
                return Err(MleTerminalError::FoldMismatch {
                    query: query_number,
                    round,
                });
            }
            word_len = half;
        }
    }
    Ok(())
}

struct MleRoundHash<'a, H> {
    inner: &'a H,
    round: u32,
}

impl<H: HashSuite<Root = BinaryRoot>> HashSuite for MleRoundHash<'_, H> {
    type Root = BinaryRoot;

    const SUITE_ID: &'static [u8] = MLE_TERMINAL_PROTOCOL_LABEL;

    fn hash_leaf(&self, _domain: BinaryHashDomain, index: u64, payload: &[u8]) -> BinaryRoot {
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
        left: &BinaryRoot,
        right: &BinaryRoot,
    ) -> BinaryRoot {
        self.inner
            .hash_node(BinaryHashDomain::AdditiveFri, level, left, right)
    }
}

fn commit_word<H: HashSuite<Root = BinaryRoot>>(
    word: &[Ext6],
    round: usize,
    hash: &H,
) -> Result<BinaryMerkleTree<BinaryRoot>, MleTerminalError> {
    let round = u32::try_from(round).map_err(|_| MleTerminalError::InvalidDomain)?;
    let round_hash = MleRoundHash { inner: hash, round };
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

#[allow(clippy::too_many_arguments)]
fn verify_round_opening<H: HashSuite<Root = BinaryRoot>>(
    hash: &H,
    round: usize,
    leaf_count: usize,
    index: usize,
    value: Ext6,
    path: &BinaryMerklePath<BinaryRoot>,
    root: &BinaryRoot,
) -> Result<bool, MleTerminalError> {
    let round = u32::try_from(round).map_err(|_| MleTerminalError::InvalidDomain)?;
    let round_hash = MleRoundHash { inner: hash, round };
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

fn fold_coefficients(coefficients: &[Ext6], challenge: Ext6) -> Vec<Ext6> {
    coefficients
        .chunks_exact(2)
        .map(|pair| pair[0].add(pair[1].mul(challenge)))
        .collect()
}

fn fold_word(word: &[Ext6], challenge: Ext6) -> Vec<Ext6> {
    let half = word.len() / 2;
    let log_n = word.len().trailing_zeros();
    (0..half)
        .map(|index| {
            fold_pair(
                word[index],
                word[half + index],
                challenge,
                level_twiddle(log_n, index),
            )
        })
        .collect()
}

fn fold_pair(low: Ext6, high: Ext6, challenge: Ext6, twiddle: u64) -> Ext6 {
    low.add(high)
        .base_mul(HALF)
        .add(low.sub(high).mul(challenge).base_mul(twiddle))
}

fn level_twiddle(log_n: u32, index: usize) -> u64 {
    bmul(HALF, bpow(binv(two_adic_generator(log_n)), index as u64))
}

fn checked_domain_size(log_domain: u32) -> Result<usize, MleTerminalError> {
    if log_domain > TWO_ADIC_BITS {
        return Err(MleTerminalError::InvalidDomain);
    }
    1usize
        .checked_shl(log_domain)
        .ok_or(MleTerminalError::InvalidDomain)
}

fn draw_queries<T: MleTerminalTranscript>(
    transcript: &mut T,
    pair_count: usize,
    count: usize,
) -> Result<Vec<usize>, MleTerminalError> {
    if pair_count == 0 || !pair_count.is_power_of_two() {
        return Err(MleTerminalError::InvalidDomain);
    }
    (0..count)
        .map(|query| {
            transcript
                .draw_query_index(query, pair_count)
                .map_err(transcript_error)
                .and_then(|index| {
                    if index < pair_count {
                        Ok(index)
                    } else {
                        Err(MleTerminalError::InvalidDomain)
                    }
                })
        })
        .collect()
}

fn bytes_as_u16_fields(bytes: &[u8]) -> Vec<u64> {
    let mut fields = Vec::with_capacity(1 + bytes.len().div_ceil(2));
    fields.push(bytes.len() as u64);
    for chunk in bytes.chunks(2) {
        let high = chunk.get(1).copied().unwrap_or(0);
        fields.push(u16::from_le_bytes([chunk[0], high]) as u64);
    }
    fields
}

fn root_as_u16_fields(root: &BinaryRoot) -> Vec<u64> {
    root.as_bytes()
        .chunks_exact(2)
        .map(|chunk| u16::from_le_bytes([chunk[0], chunk[1]]) as u64)
        .collect()
}

fn transcript_error<E: fmt::Display>(error: E) -> MleTerminalError {
    MleTerminalError::Transcript(error.to_string())
}
