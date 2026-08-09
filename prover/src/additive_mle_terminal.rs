//! Stateful sampled MLE terminal over the reversed-LCH additive tower.
//!
//! Boolean tables and Mobius coefficients are LSB-first.  Coefficient bit `i`
//! is paired with the `i`-th polynomial in the *reversed* LCH chain
//! `beta[last], beta[last-1], ...`.  The evaluation domain retains the ordinary
//! little-endian `beta[0], beta[1], ...` order.  Therefore the runtime fold,
//! which removes `beta.last()`, binds coefficient bit zero; after quotienting,
//! the same invariant recurs.  No coefficient permutation is needed.
//! For `N = 2^v` table entries and `M = 2^(v+b)` domain points, coefficients
//! are zero-padded to `M`, exactly `v` variables are bound, and the retained
//! `2^b` word must be the claimed constant codeword.
//!
//! The prover commits the initial root before any binding value, then exposes
//! `challenge -> next root` round by round.  Coherent sampled paths are derived
//! only after the final constant-codeword claim is fixed. Proofs carry roots and
//! Merkle paths, never the Boolean table or a full word.
//!
//! Honest residuals:
//! * `[ANTT-MLE-PROXIMITY]`: compose the landed additive-FRI proximity theorem
//!   with Mobius/reversed-LCH provenance at explicit rate
//!   `N/M = 2^-log_blowup` and distance `1 - N/M`.
//! * `[COMMIT-CR]`: instantiate collision resistance for the binary Merkle
//!   commitment rather than ideal position binding.
//! * `[ANTT-MLE-ROM]`: analyze transcript challenges/queries in the ROM/XOF
//!   game.
//! * `[ANTT-MLE-RUST-UNVERIFIED]`: this Rust schedule is unverified compute;
//!   Lean reversed additive tower and Mobius MLE semantics.

use core::{convert::Infallible, fmt};

use crate::{
    additive_fri_sampled::tower_leaf_payload,
    additive_ntt::{forward, AdditiveNttError},
    binary_hash::{BinaryHashDomain, BinaryRoot, HashSuite},
    binary_merkle::{verify_binary_opening, BinaryMerkleError, BinaryMerklePath, BinaryMerkleTree},
    binary_tower::{additive_fold_map, additive_fold_pair, TowerElem, TowerError},
    binary_transcript::{BinaryShake256Transcript, TranscriptSuite},
};

pub const ADDITIVE_MLE_TERMINAL_PROTOCOL_LABEL: &[u8] = b"minidregg/additive-mle-terminal/v2";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdditiveMleTerminalStatement {
    pub input_root: BinaryRoot,
    /// `M/N = 2^log_blowup`; the basis has `v + log_blowup` directions.
    pub log_blowup: u32,
    pub basis: Vec<TowerElem>,
    pub offset: TowerElem,
    pub claimed_terminal: TowerElem,
    pub num_queries: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdditiveMlePairOpening {
    pub low: TowerElem,
    pub high: TowerElem,
    pub low_path: BinaryMerklePath<BinaryRoot>,
    pub high_path: BinaryMerklePath<BinaryRoot>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdditiveMleQueryOpening {
    pub rounds: Vec<AdditiveMlePairOpening>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdditiveMleTerminalProof {
    /// Roots for lengths `2^(v+b), ..., 2^b` after exactly `v` binds.
    pub roots: Vec<BinaryRoot>,
    /// Query indices are transcript-derived and are not proof-carried.
    pub queries: Vec<AdditiveMleQueryOpening>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdditiveMleTerminalError {
    InvalidTableShape,
    InvalidDomain,
    DependentBasis(usize),
    FieldLevelMismatch,
    TooManyBindings,
    MissingBindings { expected: usize, actual: usize },
    ClaimedTerminalMismatch,
    InvalidProofShape,
    InputRootMismatch,
    FinalRootMismatch,
    Merkle(BinaryMerkleError),
    Transform(AdditiveNttError),
    Tower(TowerError),
    Transcript(String),
    InvalidOpening { query: usize, round: usize },
    FoldMismatch { query: usize, round: usize },
}

impl From<BinaryMerkleError> for AdditiveMleTerminalError {
    fn from(value: BinaryMerkleError) -> Self {
        Self::Merkle(value)
    }
}

impl From<AdditiveNttError> for AdditiveMleTerminalError {
    fn from(value: AdditiveNttError) -> Self {
        Self::Transform(value)
    }
}

impl From<TowerError> for AdditiveMleTerminalError {
    fn from(value: TowerError) -> Self {
        Self::Tower(value)
    }
}

impl fmt::Display for AdditiveMleTerminalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidTableShape => {
                write!(
                    f,
                    "additive MLE table must have power-of-two length at least two"
                )
            }
            Self::InvalidDomain => write!(f, "invalid additive MLE terminal domain"),
            Self::DependentBasis(index) => {
                write!(
                    f,
                    "reversed additive basis becomes dependent at index {index}"
                )
            }
            Self::FieldLevelMismatch => write!(f, "additive MLE field level mismatch"),
            Self::TooManyBindings => write!(f, "too many additive MLE bindings"),
            Self::MissingBindings { expected, actual } => write!(
                f,
                "additive MLE terminal has {actual} bindings, expected {expected}"
            ),
            Self::ClaimedTerminalMismatch => {
                write!(
                    f,
                    "final additive word is not the claimed MLE constant codeword"
                )
            }
            Self::InvalidProofShape => write!(f, "invalid additive MLE terminal proof shape"),
            Self::InputRootMismatch => write!(f, "additive MLE input root mismatch"),
            Self::FinalRootMismatch => write!(f, "additive MLE final root mismatch"),
            Self::Merkle(error) => error.fmt(f),
            Self::Transform(error) => error.fmt(f),
            Self::Tower(error) => error.fmt(f),
            Self::Transcript(error) => write!(f, "additive MLE transcript: {error}"),
            Self::InvalidOpening { query, round } => {
                write!(
                    f,
                    "additive MLE query {query}, round {round} has an invalid opening"
                )
            }
            Self::FoldMismatch { query, round } => {
                write!(
                    f,
                    "additive MLE query {query}, round {round} violates the fold"
                )
            }
        }
    }
}

impl std::error::Error for AdditiveMleTerminalError {}

/// LSB Boolean value table to LSB multilinear monomial coefficients.
/// Subtraction is addition in characteristic two.
pub fn boolean_mobius_coefficients(
    table: &[TowerElem],
) -> Result<Vec<TowerElem>, AdditiveMleTerminalError> {
    validate_table(table)?;
    let mut coefficients = table.to_vec();
    let variables = table.len().trailing_zeros() as usize;
    for bit in 0..variables {
        let flag = 1usize << bit;
        for mask in 0..table.len() {
            if mask & flag != 0 {
                coefficients[mask] = coefficients[mask].add(coefficients[mask ^ flag])?;
            }
        }
    }
    Ok(coefficients)
}

/// Literal multilinear extension of an LSB Boolean table.
pub fn evaluate_table_mle(
    table: &[TowerElem],
    point: &[TowerElem],
) -> Result<TowerElem, AdditiveMleTerminalError> {
    validate_table(table)?;
    if point.len() != table.len().trailing_zeros() as usize {
        return Err(AdditiveMleTerminalError::InvalidDomain);
    }
    let level = table[0].level();
    if point.iter().any(|value| value.level() != level) {
        return Err(AdditiveMleTerminalError::FieldLevelMismatch);
    }
    let mut layer = table.to_vec();
    for &challenge in point {
        let mut next = Vec::with_capacity(layer.len() / 2);
        for pair in layer.chunks_exact(2) {
            let slope = pair[0].add(pair[1])?;
            next.push(pair[0].add(challenge.mul(slope)?)?);
        }
        layer = next;
    }
    layer
        .first()
        .copied()
        .ok_or(AdditiveMleTerminalError::InvalidTableShape)
}

/// Bind coefficient bit zero, the next LSB MLE variable.
pub fn bind_mle_coefficients(
    coefficients: &[TowerElem],
    challenge: TowerElem,
) -> Result<Vec<TowerElem>, AdditiveMleTerminalError> {
    if coefficients.len() < 2 || !coefficients.len().is_power_of_two() {
        return Err(AdditiveMleTerminalError::InvalidTableShape);
    }
    if coefficients
        .iter()
        .any(|value| value.level() != challenge.level())
    {
        return Err(AdditiveMleTerminalError::FieldLevelMismatch);
    }
    coefficients
        .chunks_exact(2)
        .map(|pair| Ok(pair[0].add(challenge.mul(pair[1])?)?))
        .collect()
}

/// Fast reversed-LCH encoding on the ordinary little-endian affine domain.
///
/// [`forward`] accepts one basis order for both the polynomial chain and its
/// domain indices. Feeding it `basis.rev()` selects the required reversed LCH
/// chain; bit-reversing the resulting indices transports its domain back to
/// the ordinary `basis[0], basis[1], ...` enumeration used by runtime folds.
/// Coefficient indices are deliberately unchanged.
pub fn reversed_lch_encode(
    coefficients: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
) -> Result<Vec<TowerElem>, AdditiveMleTerminalError> {
    let reversed_basis = basis.iter().copied().rev().collect::<Vec<_>>();
    let reversed_domain_word = forward(coefficients, &reversed_basis, offset)?;
    let bits = basis.len();
    if bits == 0 {
        return Ok(reversed_domain_word);
    }
    Ok((0..reversed_domain_word.len())
        .map(|index| reversed_domain_word[reverse_low_bits(index, bits)])
        .collect())
}

/// Canonical initial MLE word shared by the terminal and protocols which must
/// authenticate a linear relation between independently committed tables.
pub fn additive_mle_initial_word(
    table: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
) -> Result<Vec<TowerElem>, AdditiveMleTerminalError> {
    additive_mle_initial_word_with_blowup(table, basis, offset, 0)
}

pub fn additive_mle_initial_word_with_blowup(
    table: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
    log_blowup: u32,
) -> Result<Vec<TowerElem>, AdditiveMleTerminalError> {
    Ok(additive_mle_initial_encoding(table, basis, offset, log_blowup)?.1)
}

fn additive_mle_initial_encoding(
    table: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
    log_blowup: u32,
) -> Result<(Vec<TowerElem>, Vec<TowerElem>), AdditiveMleTerminalError> {
    validate_table(table)?;
    let log_variables = table.len().trailing_zeros() as usize;
    let log_domain = log_variables
        .checked_add(log_blowup as usize)
        .ok_or(AdditiveMleTerminalError::InvalidDomain)?;
    let domain_size = 1usize
        .checked_shl(log_domain as u32)
        .ok_or(AdditiveMleTerminalError::InvalidDomain)?;
    if basis.len() != log_domain {
        return Err(AdditiveMleTerminalError::InvalidDomain);
    }
    let mut coefficients = boolean_mobius_coefficients(table)?;
    coefficients.resize(domain_size, TowerElem::zero(offset.level())?);
    let word = reversed_lch_encode(&coefficients, basis, offset)?;
    Ok((coefficients, word))
}

/// Evaluate coefficients in the reversed LCH chain on the ordinary
/// little-endian affine domain.  This dense routine is the executable ordering
/// oracle used by the focused smoke test.
pub fn reversed_lch_evaluations(
    coefficients: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
) -> Result<Vec<TowerElem>, AdditiveMleTerminalError> {
    validate_domain(coefficients, basis, offset)?;
    let reversed = basis.iter().copied().rev().collect::<Vec<_>>();
    let gamma = reversed_vanishing_constants(&reversed)?;
    let mut output = Vec::with_capacity(coefficients.len());
    for domain_index in 0..coefficients.len() {
        let point = domain_point(basis, offset, domain_index)?;
        let vanishing = vanishing_prefix_values(&gamma, point)?;
        let mut value = TowerElem::zero(offset.level())?;
        for (mask, &coefficient) in coefficients.iter().enumerate() {
            let mut term = coefficient;
            for (bit, &basis_value) in vanishing.iter().enumerate() {
                if mask & (1usize << bit) != 0 {
                    term = term.mul(basis_value)?;
                }
            }
            value = value.add(term)?;
        }
        output.push(value);
    }
    Ok(output)
}

/// One runtime fold plus the transported affine domain.
pub fn fold_reversed_lch_round(
    word: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
    challenge: TowerElem,
) -> Result<(Vec<TowerElem>, Vec<TowerElem>, TowerElem), AdditiveMleTerminalError> {
    if word.len() < 2 || word.len() != 1usize << basis.len() {
        return Err(AdditiveMleTerminalError::InvalidDomain);
    }
    let beta = *basis
        .last()
        .ok_or(AdditiveMleTerminalError::InvalidDomain)?;
    let half = word.len() / 2;
    let points = domain_points(&basis[..basis.len() - 1], offset)?;
    let mut folded = Vec::with_capacity(half);
    for index in 0..half {
        folded.push(additive_fold_pair(
            beta,
            challenge,
            points[index],
            word[index],
            word[half + index],
        )?);
    }
    let next_basis = basis[..basis.len() - 1]
        .iter()
        .copied()
        .map(|value| additive_fold_map(beta, value).map_err(AdditiveMleTerminalError::from))
        .collect::<Result<Vec<_>, AdditiveMleTerminalError>>()?;
    let next_offset = additive_fold_map(beta, offset)?;
    Ok((folded, next_basis, next_offset))
}

pub trait AdditiveMleTerminalTranscript {
    type Error: fmt::Display;

    fn observe_initial(
        &mut self,
        hash_suite_id: &[u8],
        basis: &[TowerElem],
        offset: TowerElem,
        log_blowup: u32,
        root: &BinaryRoot,
    ) -> Result<(), Self::Error>;

    /// Records `challenge` before `next_root` in the transcript framing.
    fn observe_binding(
        &mut self,
        round: usize,
        challenge: TowerElem,
        next_word_len: usize,
        next_root: &BinaryRoot,
    ) -> Result<(), Self::Error>;

    fn observe_final(
        &mut self,
        claimed_terminal: TowerElem,
        num_queries: usize,
    ) -> Result<(), Self::Error>;

    fn draw_query_index(
        &mut self,
        query_number: usize,
        pair_count: usize,
    ) -> Result<usize, Self::Error>;
}

impl AdditiveMleTerminalTranscript for BinaryShake256Transcript {
    type Error = Infallible;

    fn observe_initial(
        &mut self,
        hash_suite_id: &[u8],
        basis: &[TowerElem],
        offset: TowerElem,
        log_blowup: u32,
        root: &BinaryRoot,
    ) -> Result<(), Self::Error> {
        self.observe_bytes(
            b"additive-mle/protocol",
            ADDITIVE_MLE_TERMINAL_PROTOCOL_LABEL,
        );
        self.observe_bytes(b"additive-mle/hash-suite", hash_suite_id);
        self.observe_u64(b"additive-mle/tower-level", offset.level() as u64);
        self.observe_u64(
            b"additive-mle/log-variables",
            basis.len().saturating_sub(log_blowup as usize) as u64,
        );
        self.observe_u64(b"additive-mle/log-blowup", log_blowup as u64);
        self.observe_bytes(b"additive-mle/offset", &tower_leaf_payload(offset));
        for (index, &beta) in basis.iter().enumerate() {
            self.observe_u64(b"additive-mle/basis-index", index as u64);
            self.observe_bytes(b"additive-mle/basis-value", &tower_leaf_payload(beta));
        }
        self.observe_root(b"additive-mle/input-root", root);
        Ok(())
    }

    fn observe_binding(
        &mut self,
        round: usize,
        challenge: TowerElem,
        next_word_len: usize,
        next_root: &BinaryRoot,
    ) -> Result<(), Self::Error> {
        self.observe_u64(b"additive-mle/bind-round", round as u64);
        self.observe_bytes(b"additive-mle/bind-value", &tower_leaf_payload(challenge));
        self.observe_u64(b"additive-mle/next-word-length", next_word_len as u64);
        self.observe_root(b"additive-mle/next-root", next_root);
        Ok(())
    }

    fn observe_final(
        &mut self,
        claimed_terminal: TowerElem,
        num_queries: usize,
    ) -> Result<(), Self::Error> {
        self.observe_bytes(
            b"additive-mle/claimed-terminal",
            &tower_leaf_payload(claimed_terminal),
        );
        self.observe_u64(b"additive-mle/num-queries", num_queries as u64);
        Ok(())
    }

    fn draw_query_index(
        &mut self,
        query_number: usize,
        pair_count: usize,
    ) -> Result<usize, Self::Error> {
        self.observe_u64(b"additive-mle/query-number", query_number as u64);
        Ok((self.sample_gf2_64(b"additive-mle/query-index") as usize) & (pair_count - 1))
    }
}

pub struct AdditiveMleTerminalProverState<H: HashSuite<Root = BinaryRoot>> {
    hash: H,
    basis: Vec<TowerElem>,
    log_variables: usize,
    log_blowup: u32,
    offset: TowerElem,
    coefficients: Vec<TowerElem>,
    words: Vec<Vec<TowerElem>>,
    round_bases: Vec<Vec<TowerElem>>,
    round_offsets: Vec<TowerElem>,
    trees: Vec<BinaryMerkleTree<BinaryRoot>>,
    roots: Vec<BinaryRoot>,
    bindings: Vec<TowerElem>,
}

impl<H: HashSuite<Root = BinaryRoot>> AdditiveMleTerminalProverState<H> {
    pub fn commit_initial<T: AdditiveMleTerminalTranscript>(
        table: &[TowerElem],
        basis: &[TowerElem],
        offset: TowerElem,
        hash: H,
        transcript: &mut T,
    ) -> Result<Self, AdditiveMleTerminalError> {
        Self::commit_initial_with_blowup(table, basis, offset, 0, hash, transcript)
    }

    pub fn commit_initial_with_blowup<T: AdditiveMleTerminalTranscript>(
        table: &[TowerElem],
        basis: &[TowerElem],
        offset: TowerElem,
        log_blowup: u32,
        hash: H,
        transcript: &mut T,
    ) -> Result<Self, AdditiveMleTerminalError> {
        validate_table(table)?;
        let log_variables = table.len().trailing_zeros() as usize;
        if basis.len() != log_variables + log_blowup as usize {
            return Err(AdditiveMleTerminalError::InvalidDomain);
        }
        let (coefficients, word) = additive_mle_initial_encoding(table, basis, offset, log_blowup)?;
        let tree = commit_additive_mle_word(&word, &hash)?;
        let root = tree.root();
        transcript
            .observe_initial(H::SUITE_ID, basis, offset, log_blowup, &root)
            .map_err(transcript_error)?;
        Ok(Self {
            hash,
            basis: basis.to_vec(),
            log_variables,
            log_blowup,
            offset,
            coefficients,
            words: vec![word],
            round_bases: vec![basis.to_vec()],
            round_offsets: vec![offset],
            trees: vec![tree],
            roots: vec![root],
            bindings: Vec::with_capacity(log_variables),
        })
    }

    pub fn input_root(&self) -> BinaryRoot {
        self.roots[0]
    }

    pub fn bindings_complete(&self) -> bool {
        self.bindings.len() == self.log_variables
    }

    pub fn bind<T: AdditiveMleTerminalTranscript>(
        &mut self,
        challenge: TowerElem,
        transcript: &mut T,
    ) -> Result<BinaryRoot, AdditiveMleTerminalError> {
        if self.bindings_complete() {
            return Err(AdditiveMleTerminalError::TooManyBindings);
        }
        if challenge.level() != self.offset.level() {
            return Err(AdditiveMleTerminalError::FieldLevelMismatch);
        }
        let round = self.bindings.len();
        let current_word = self
            .words
            .last()
            .ok_or(AdditiveMleTerminalError::InvalidDomain)?;
        let current_basis = self
            .round_bases
            .last()
            .ok_or(AdditiveMleTerminalError::InvalidDomain)?;
        let current_offset = *self
            .round_offsets
            .last()
            .ok_or(AdditiveMleTerminalError::InvalidDomain)?;
        let (next_word, next_basis, next_offset) =
            fold_reversed_lch_round(current_word, current_basis, current_offset, challenge)?;
        self.coefficients = bind_mle_coefficients(&self.coefficients, challenge)?;
        let tree = commit_additive_mle_word(&next_word, &self.hash)?;
        let root = tree.root();
        transcript
            .observe_binding(round, challenge, next_word.len(), &root)
            .map_err(transcript_error)?;
        self.bindings.push(challenge);
        self.words.push(next_word);
        self.round_bases.push(next_basis);
        self.round_offsets.push(next_offset);
        self.trees.push(tree);
        self.roots.push(root);
        Ok(root)
    }

    pub fn finish<T: AdditiveMleTerminalTranscript>(
        self,
        claimed_terminal: TowerElem,
        num_queries: usize,
        transcript: &mut T,
    ) -> Result<(AdditiveMleTerminalStatement, AdditiveMleTerminalProof), AdditiveMleTerminalError>
    {
        if self.bindings.len() != self.log_variables {
            return Err(AdditiveMleTerminalError::MissingBindings {
                expected: self.log_variables,
                actual: self.bindings.len(),
            });
        }
        if num_queries == 0 || claimed_terminal.level() != self.offset.level() {
            return Err(AdditiveMleTerminalError::InvalidDomain);
        }
        let final_word = self
            .words
            .last()
            .ok_or(AdditiveMleTerminalError::InvalidDomain)?;
        if self.coefficients.first().copied() != Some(claimed_terminal)
            || self
                .coefficients
                .iter()
                .skip(1)
                .any(|value| !value.is_zero())
            || final_word.iter().any(|&value| value != claimed_terminal)
        {
            return Err(AdditiveMleTerminalError::ClaimedTerminalMismatch);
        }
        transcript
            .observe_final(claimed_terminal, num_queries)
            .map_err(transcript_error)?;
        let query_indices = draw_queries(transcript, self.words[0].len() / 2, num_queries)?;
        let queries = query_indices
            .iter()
            .map(|&initial_index| {
                let rounds = (0..self.log_variables)
                    .map(|round| {
                        let word = &self.words[round];
                        let half = word.len() / 2;
                        let pair_index = initial_index % half;
                        Ok(AdditiveMlePairOpening {
                            low: word[pair_index],
                            high: word[half + pair_index],
                            low_path: self.trees[round].open(pair_index)?,
                            high_path: self.trees[round].open(half + pair_index)?,
                        })
                    })
                    .collect::<Result<Vec<_>, AdditiveMleTerminalError>>()?;
                Ok(AdditiveMleQueryOpening { rounds })
            })
            .collect::<Result<Vec<_>, AdditiveMleTerminalError>>()?;
        Ok((
            AdditiveMleTerminalStatement {
                input_root: self.roots[0],
                log_blowup: self.log_blowup,
                basis: self.basis,
                offset: self.offset,
                claimed_terminal,
                num_queries,
            },
            AdditiveMleTerminalProof {
                roots: self.roots,
                queries,
            },
        ))
    }
}

pub fn verify_additive_mle_terminal<
    H: HashSuite<Root = BinaryRoot>,
    T: AdditiveMleTerminalTranscript,
>(
    statement: &AdditiveMleTerminalStatement,
    evaluation_point: &[TowerElem],
    proof: &AdditiveMleTerminalProof,
    hash: &H,
    transcript: &mut T,
) -> bool {
    check_additive_mle_terminal(statement, evaluation_point, proof, hash, transcript).is_ok()
}

fn check_additive_mle_terminal<
    H: HashSuite<Root = BinaryRoot>,
    T: AdditiveMleTerminalTranscript,
>(
    statement: &AdditiveMleTerminalStatement,
    evaluation_point: &[TowerElem],
    proof: &AdditiveMleTerminalProof,
    hash: &H,
    transcript: &mut T,
) -> Result<(), AdditiveMleTerminalError> {
    let log_blowup = statement.log_blowup as usize;
    let rounds = statement
        .basis
        .len()
        .checked_sub(log_blowup)
        .ok_or(AdditiveMleTerminalError::InvalidProofShape)?;
    let domain_size = 1usize
        .checked_shl(statement.basis.len() as u32)
        .ok_or(AdditiveMleTerminalError::InvalidProofShape)?;
    if rounds == 0
        || evaluation_point.len() != rounds
        || statement.num_queries == 0
        || proof.roots.len() != rounds + 1
        || proof.queries.len() != statement.num_queries
        || proof
            .queries
            .iter()
            .any(|query| query.rounds.len() != rounds)
        || evaluation_point
            .iter()
            .any(|value| value.level() != statement.offset.level())
    {
        return Err(AdditiveMleTerminalError::InvalidProofShape);
    }
    validate_basis(&statement.basis, statement.offset)?;
    if proof.roots[0] != statement.input_root {
        return Err(AdditiveMleTerminalError::InputRootMismatch);
    }
    transcript
        .observe_initial(
            H::SUITE_ID,
            &statement.basis,
            statement.offset,
            statement.log_blowup,
            &statement.input_root,
        )
        .map_err(transcript_error)?;
    let initial_pair_count = domain_size / 2;
    let mut next_len = initial_pair_count;
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
    transcript
        .observe_final(statement.claimed_terminal, statement.num_queries)
        .map_err(transcript_error)?;
    let query_indices = draw_queries(transcript, initial_pair_count, statement.num_queries)?;
    let final_size = 1usize
        .checked_shl(statement.log_blowup)
        .ok_or(AdditiveMleTerminalError::InvalidProofShape)?;
    let final_codeword = vec![statement.claimed_terminal; final_size];
    if commit_additive_mle_word(&final_codeword, hash)?.root()
        != *proof
            .roots
            .last()
            .ok_or(AdditiveMleTerminalError::InvalidProofShape)?
    {
        return Err(AdditiveMleTerminalError::FinalRootMismatch);
    }

    let mut round_bases = Vec::with_capacity(rounds);
    let mut round_offsets = Vec::with_capacity(rounds);
    let mut basis = statement.basis.clone();
    let mut offset = statement.offset;
    for _ in 0..rounds {
        round_bases.push(basis.clone());
        round_offsets.push(offset);
        let beta = *basis
            .last()
            .ok_or(AdditiveMleTerminalError::InvalidDomain)?;
        basis = basis[..basis.len() - 1]
            .iter()
            .copied()
            .map(|value| additive_fold_map(beta, value).map_err(Into::into))
            .collect::<Result<Vec<_>, AdditiveMleTerminalError>>()?;
        offset = additive_fold_map(beta, offset)?;
    }

    for (query_number, (&initial_index, query)) in
        query_indices.iter().zip(&proof.queries).enumerate()
    {
        let mut word_len = domain_size;
        for round in 0..rounds {
            let half = word_len / 2;
            let pair_index = initial_index % half;
            let opening = &query.rounds[round];
            if !verify_additive_mle_word_opening(
                hash,
                word_len,
                pair_index,
                opening.low,
                &opening.low_path,
                &proof.roots[round],
            )? || !verify_additive_mle_word_opening(
                hash,
                word_len,
                half + pair_index,
                opening.high,
                &opening.high_path,
                &proof.roots[round],
            )? {
                return Err(AdditiveMleTerminalError::InvalidOpening {
                    query: query_number,
                    round,
                });
            }
            let x = domain_point(
                &round_bases[round][..round_bases[round].len() - 1],
                round_offsets[round],
                pair_index,
            )?;
            let expected = additive_fold_pair(
                *round_bases[round]
                    .last()
                    .ok_or(AdditiveMleTerminalError::InvalidDomain)?,
                evaluation_point[round],
                x,
                opening.low,
                opening.high,
            )?;
            let actual = if round + 1 == rounds {
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
                return Err(AdditiveMleTerminalError::FoldMismatch {
                    query: query_number,
                    round,
                });
            }
            word_len = half;
        }
    }
    Ok(())
}

fn validate_table(table: &[TowerElem]) -> Result<(), AdditiveMleTerminalError> {
    if table.len() < 2 || !table.len().is_power_of_two() {
        return Err(AdditiveMleTerminalError::InvalidTableShape);
    }
    let level = table[0].level();
    if table.iter().any(|value| value.level() != level) {
        return Err(AdditiveMleTerminalError::FieldLevelMismatch);
    }
    Ok(())
}

fn validate_basis(basis: &[TowerElem], offset: TowerElem) -> Result<(), AdditiveMleTerminalError> {
    if basis.len() > (1usize << offset.level())
        || basis.iter().any(|value| value.level() != offset.level())
    {
        return Err(AdditiveMleTerminalError::InvalidDomain);
    }
    let reversed = basis.iter().copied().rev().collect::<Vec<_>>();
    reversed_vanishing_constants(&reversed)?;
    Ok(())
}

fn validate_domain(
    coefficients: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
) -> Result<(), AdditiveMleTerminalError> {
    let expected_len = 1usize
        .checked_shl(basis.len() as u32)
        .ok_or(AdditiveMleTerminalError::InvalidDomain)?;
    if coefficients.len() != expected_len {
        return Err(AdditiveMleTerminalError::InvalidDomain);
    }
    validate_basis(basis, offset)?;
    if coefficients
        .iter()
        .any(|value| value.level() != offset.level())
    {
        return Err(AdditiveMleTerminalError::FieldLevelMismatch);
    }
    Ok(())
}

fn reversed_vanishing_constants(
    reversed_basis: &[TowerElem],
) -> Result<Vec<TowerElem>, AdditiveMleTerminalError> {
    let mut gamma = Vec::with_capacity(reversed_basis.len());
    for (index, &beta) in reversed_basis.iter().enumerate() {
        let value = subspace_vanishing_eval(&gamma, beta)?;
        if value.is_zero() {
            return Err(AdditiveMleTerminalError::DependentBasis(index));
        }
        gamma.push(value);
    }
    Ok(gamma)
}

fn subspace_vanishing_eval(
    gamma: &[TowerElem],
    x: TowerElem,
) -> Result<TowerElem, AdditiveMleTerminalError> {
    let mut value = x;
    for &coefficient in gamma {
        value = value.square().add(coefficient.mul(value)?)?;
    }
    Ok(value)
}

fn vanishing_prefix_values(
    gamma: &[TowerElem],
    x: TowerElem,
) -> Result<Vec<TowerElem>, AdditiveMleTerminalError> {
    let mut values = Vec::with_capacity(gamma.len());
    let mut value = x;
    for &coefficient in gamma {
        values.push(value);
        value = value.square().add(coefficient.mul(value)?)?;
    }
    Ok(values)
}

fn domain_points(
    basis: &[TowerElem],
    offset: TowerElem,
) -> Result<Vec<TowerElem>, AdditiveMleTerminalError> {
    let mut points = vec![offset];
    for &beta in basis {
        let old_len = points.len();
        for index in 0..old_len {
            points.push(points[index].add(beta)?);
        }
    }
    Ok(points)
}

fn domain_point(
    basis: &[TowerElem],
    offset: TowerElem,
    index: usize,
) -> Result<TowerElem, AdditiveMleTerminalError> {
    let mut point = offset;
    for (bit, &beta) in basis.iter().enumerate() {
        if index & (1usize << bit) != 0 {
            point = point.add(beta)?;
        }
    }
    Ok(point)
}

pub fn commit_additive_mle_word<H: HashSuite<Root = BinaryRoot>>(
    word: &[TowerElem],
    hash: &H,
) -> Result<BinaryMerkleTree<BinaryRoot>, AdditiveMleTerminalError> {
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

pub fn verify_additive_mle_word_opening<H: HashSuite<Root = BinaryRoot>>(
    hash: &H,
    leaf_count: usize,
    index: usize,
    value: TowerElem,
    path: &BinaryMerklePath<BinaryRoot>,
    root: &BinaryRoot,
) -> Result<bool, AdditiveMleTerminalError> {
    Ok(verify_binary_opening(
        hash,
        BinaryHashDomain::AdditiveFri,
        leaf_count,
        index,
        &tower_leaf_payload(value),
        path,
        root,
    )?)
}

fn draw_queries<T: AdditiveMleTerminalTranscript>(
    transcript: &mut T,
    pair_count: usize,
    num_queries: usize,
) -> Result<Vec<usize>, AdditiveMleTerminalError> {
    if pair_count == 0 || !pair_count.is_power_of_two() || num_queries == 0 {
        return Err(AdditiveMleTerminalError::InvalidDomain);
    }
    (0..num_queries)
        .map(|query| {
            let index = transcript
                .draw_query_index(query, pair_count)
                .map_err(transcript_error)?;
            if index < pair_count {
                Ok(index)
            } else {
                Err(AdditiveMleTerminalError::InvalidDomain)
            }
        })
        .collect()
}

fn transcript_error<E: fmt::Display>(error: E) -> AdditiveMleTerminalError {
    AdditiveMleTerminalError::Transcript(error.to_string())
}

fn reverse_low_bits(value: usize, bits: usize) -> usize {
    debug_assert!(bits > 0 && bits < usize::BITS as usize);
    value.reverse_bits() >> (usize::BITS as usize - bits)
}
