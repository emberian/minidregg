//! Sampled additive polynomial-commitment opening at one GF(2^64) point.
//!
//! The verifier receives no full evaluation word.  The quotient is currently
//! formed through a dense monomial conversion/division; replacing that path is
//! `[ANTT-PCS-fast-novel-quotient]`.  Low-degree soundness is inherited from
//! `[ANTT-FRI-PROXIMITY]`.  This retires point-evaluation channels only;
//! `[BINARY-PCS-general-linear-retirement]` is the separate arbitrary-weight
//! opening problem.

use core::convert::Infallible;
use core::fmt;

use crate::additive_fri_sampled::{
    prove_sampled, tower_leaf_payload, verify_sampled, ChallengeSource, SampledFriProof,
    SampledFriStatement,
};
use crate::additive_ntt::{forward, inverse, AdditiveNttError};
use crate::binary_hash::{BinaryHashDomain, BinaryRoot, BinaryShake256V1, HashSuite};
use crate::binary_merkle::{
    verify_binary_opening, BinaryMerkleError, BinaryMerklePath, BinaryMerkleTree,
};
use crate::binary_tower::{TowerElem, TowerError};
use crate::binary_transcript::{BinaryShake256Transcript, TranscriptSuite};

const PROTOCOL_LABEL: &[u8] = b"minidregg/additive-pcs-ood/v1";
const TOWER_LEVEL_GF2_64: u8 = 6;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdditivePcsOodStatement {
    pub evaluation_root: BinaryRoot,
    pub basis: Vec<TowerElem>,
    pub offset: TowerElem,
    pub coefficient_bound: usize,
    pub z: TowerElem,
    pub y: TowerElem,
    pub num_queries: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvaluationPairOpening {
    pub low: TowerElem,
    pub high: TowerElem,
    pub low_path: BinaryMerklePath<BinaryRoot>,
    pub high_path: BinaryMerklePath<BinaryRoot>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdditivePcsOodProof {
    pub quotient_fri: SampledFriProof,
    pub evaluation_openings: Vec<EvaluationPairOpening>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdditivePcsOodError {
    Tower(TowerError),
    Transform(AdditiveNttError),
    Merkle(BinaryMerkleError),
    InvalidStatement,
    ClaimedValueMismatch,
    PolynomialDivision,
    QuotientDegree,
    FriProver,
    FriVerifier,
    InvalidProofShape,
    InvalidEvaluationOpening(usize),
    QuotientIdentity(usize),
}

impl From<TowerError> for AdditivePcsOodError {
    fn from(value: TowerError) -> Self {
        Self::Tower(value)
    }
}

impl From<AdditiveNttError> for AdditivePcsOodError {
    fn from(value: AdditiveNttError) -> Self {
        Self::Transform(value)
    }
}

impl From<BinaryMerkleError> for AdditivePcsOodError {
    fn from(value: BinaryMerkleError) -> Self {
        Self::Merkle(value)
    }
}

impl fmt::Display for AdditivePcsOodError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Tower(error) => error.fmt(f),
            Self::Transform(error) => error.fmt(f),
            Self::Merkle(error) => error.fmt(f),
            Self::InvalidStatement => write!(f, "invalid additive PCS OOD statement"),
            Self::ClaimedValueMismatch => write!(f, "claimed OOD value is not f(z)"),
            Self::PolynomialDivision => write!(f, "(f-y) is not divisible by X-z"),
            Self::QuotientDegree => write!(f, "quotient exceeds the derived coefficient bound"),
            Self::FriProver => write!(f, "quotient sampled-FRI prover rejected"),
            Self::FriVerifier => write!(f, "quotient sampled-FRI verifier rejected"),
            Self::InvalidProofShape => write!(f, "invalid additive PCS proof shape"),
            Self::InvalidEvaluationOpening(query) => {
                write!(f, "evaluation opening {query} rejects")
            }
            Self::QuotientIdentity(query) => {
                write!(f, "evaluation/quotient identity fails at query {query}")
            }
        }
    }
}

impl std::error::Error for AdditivePcsOodError {}

pub fn evaluate_novel_polynomial(
    coefficients: &[TowerElem],
    basis: &[TowerElem],
    x: TowerElem,
) -> Result<TowerElem, AdditivePcsOodError> {
    if coefficients.len() != checked_domain_size(basis.len())?
        || coefficients.iter().any(|value| value.level() != x.level())
        || basis.iter().any(|value| value.level() != x.level())
    {
        return Err(AdditivePcsOodError::InvalidStatement);
    }
    let vanishing = vanishing_values(basis, x)?;
    let mut result = TowerElem::zero(x.level())?;
    for (index, coefficient) in coefficients.iter().copied().enumerate() {
        let mut term = coefficient;
        for (i, value) in vanishing.iter().copied().enumerate() {
            if index & (1usize << i) != 0 {
                term = term.mul(value)?;
            }
        }
        result = result.add(term)?;
    }
    Ok(result)
}

pub fn prove_ood(
    coefficients: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
    coefficient_bound: usize,
    z: TowerElem,
    y: TowerElem,
    num_queries: usize,
) -> Result<(AdditivePcsOodStatement, AdditivePcsOodProof), AdditivePcsOodError> {
    validate_public_inputs(basis, offset, coefficient_bound, z, y, num_queries)?;
    let domain_size = checked_domain_size(basis.len())?;
    if coefficients.len() != domain_size
        || coefficients
            .iter()
            .any(|value| value.level() != TOWER_LEVEL_GF2_64)
        || coefficients[coefficient_bound..]
            .iter()
            .any(|coefficient| !coefficient.is_zero())
    {
        return Err(AdditivePcsOodError::InvalidStatement);
    }
    if evaluate_novel_polynomial(coefficients, basis, z)? != y {
        return Err(AdditivePcsOodError::ClaimedValueMismatch);
    }

    let evaluation_word = forward(coefficients, basis, offset)?;
    let hash = BinaryShake256V1;
    let evaluation_tree = commit_word(&evaluation_word, &hash)?;
    let evaluation_root = evaluation_tree.root();
    let statement = AdditivePcsOodStatement {
        evaluation_root,
        basis: basis.to_vec(),
        offset,
        coefficient_bound,
        z,
        y,
        num_queries,
    };

    let dense_f = novel_to_dense(coefficients, basis, coefficient_bound)?;
    let dense_q = divide_by_x_add_z(&dense_f, y, z)?;
    let points = domain_points(basis, offset)?;
    let quotient_word = points
        .iter()
        .copied()
        .map(|point| poly_eval(&dense_q, point))
        .collect::<Result<Vec<_>, _>>()?;
    for ((&f_value, &q_value), &point) in evaluation_word.iter().zip(&quotient_word).zip(&points) {
        let lhs = f_value.add(y)?;
        let rhs = point.add(z)?.mul(q_value)?;
        if lhs != rhs {
            return Err(AdditivePcsOodError::PolynomialDivision);
        }
    }
    let quotient_coefficients = inverse(&quotient_word, basis, offset)?;
    let quotient_bound = quotient_bound(coefficient_bound);
    if quotient_coefficients[quotient_bound..]
        .iter()
        .any(|coefficient| !coefficient.is_zero())
    {
        return Err(AdditivePcsOodError::QuotientDegree);
    }

    let mut source = PcsTranscriptSource::new(&statement, quotient_bound);
    let (quotient_statement, quotient_fri) = prove_sampled(
        &quotient_coefficients,
        basis,
        offset,
        quotient_bound,
        num_queries,
        &hash,
        &mut source,
    )
    .map_err(|_| AdditivePcsOodError::FriProver)?;
    let query_indices = source
        .queries()
        .ok_or(AdditivePcsOodError::InvalidProofShape)?;
    let half = domain_size / 2;
    let evaluation_openings = query_indices
        .iter()
        .copied()
        .map(
            |index| -> Result<EvaluationPairOpening, AdditivePcsOodError> {
                Ok(EvaluationPairOpening {
                    low: evaluation_word[index],
                    high: evaluation_word[half + index],
                    low_path: evaluation_tree.open(index)?,
                    high_path: evaluation_tree.open(half + index)?,
                })
            },
        )
        .collect::<Result<Vec<_>, _>>()?;
    debug_assert_eq!(quotient_statement.input_root, quotient_fri.roots[0]);
    Ok((
        statement,
        AdditivePcsOodProof {
            quotient_fri,
            evaluation_openings,
        },
    ))
}

pub fn verify_ood(statement: &AdditivePcsOodStatement, proof: &AdditivePcsOodProof) -> bool {
    check_ood(statement, proof).is_ok()
}

fn check_ood(
    statement: &AdditivePcsOodStatement,
    proof: &AdditivePcsOodProof,
) -> Result<(), AdditivePcsOodError> {
    validate_public_inputs(
        &statement.basis,
        statement.offset,
        statement.coefficient_bound,
        statement.z,
        statement.y,
        statement.num_queries,
    )?;
    if proof.quotient_fri.roots.is_empty()
        || proof.evaluation_openings.len() != statement.num_queries
    {
        return Err(AdditivePcsOodError::InvalidProofShape);
    }
    let quotient_bound = quotient_bound(statement.coefficient_bound);
    let quotient_statement = SampledFriStatement {
        input_root: proof.quotient_fri.roots[0],
        basis: statement.basis.clone(),
        offset: statement.offset,
        coefficient_bound: quotient_bound,
        num_queries: statement.num_queries,
    };
    let hash = BinaryShake256V1;
    let mut source = PcsTranscriptSource::new(statement, quotient_bound);
    if !verify_sampled(&quotient_statement, &proof.quotient_fri, &hash, &mut source) {
        return Err(AdditivePcsOodError::FriVerifier);
    }
    let query_indices = source
        .queries()
        .ok_or(AdditivePcsOodError::InvalidProofShape)?;
    if query_indices.len() != proof.evaluation_openings.len()
        || proof.quotient_fri.queries.len() != query_indices.len()
    {
        return Err(AdditivePcsOodError::InvalidProofShape);
    }

    let domain_size = checked_domain_size(statement.basis.len())?;
    let half = domain_size / 2;
    let beta = *statement
        .basis
        .last()
        .ok_or(AdditivePcsOodError::InvalidStatement)?;
    for (query_number, (&index, opening)) in query_indices
        .iter()
        .zip(&proof.evaluation_openings)
        .enumerate()
    {
        if opening.low.level() != TOWER_LEVEL_GF2_64
            || opening.high.level() != TOWER_LEVEL_GF2_64
            || !verify_binary_opening(
                &hash,
                BinaryHashDomain::AdditiveFri,
                domain_size,
                index,
                &tower_leaf_payload(opening.low),
                &opening.low_path,
                &statement.evaluation_root,
            )?
            || !verify_binary_opening(
                &hash,
                BinaryHashDomain::AdditiveFri,
                domain_size,
                half + index,
                &tower_leaf_payload(opening.high),
                &opening.high_path,
                &statement.evaluation_root,
            )?
        {
            return Err(AdditivePcsOodError::InvalidEvaluationOpening(query_number));
        }
        let quotient_pair = proof
            .quotient_fri
            .queries
            .get(query_number)
            .and_then(|query| query.rounds.first())
            .ok_or(AdditivePcsOodError::InvalidProofShape)?;
        let x = domain_point(
            &statement.basis[..statement.basis.len() - 1],
            statement.offset,
            index,
        )?;
        if opening.low.add(statement.y)? != x.add(statement.z)?.mul(quotient_pair.low)?
            || opening.high.add(statement.y)?
                != x.add(beta)?.add(statement.z)?.mul(quotient_pair.high)?
        {
            return Err(AdditivePcsOodError::QuotientIdentity(query_number));
        }
    }
    Ok(())
}

struct PcsTranscriptSource {
    transcript: BinaryShake256Transcript,
    queries: Option<Vec<usize>>,
}

impl PcsTranscriptSource {
    fn new(statement: &AdditivePcsOodStatement, quotient_bound: usize) -> Self {
        let mut transcript = BinaryShake256Transcript::new(PROTOCOL_LABEL);
        transcript.observe_bytes(b"hash-suite", <BinaryShake256V1 as HashSuite>::SUITE_ID);
        transcript.observe_u64(b"tower-level", TOWER_LEVEL_GF2_64 as u64);
        transcript.observe_u64(b"log-domain", statement.basis.len() as u64);
        transcript.observe_u64(b"coefficient-bound", statement.coefficient_bound as u64);
        transcript.observe_u64(b"quotient-bound", quotient_bound as u64);
        transcript.observe_u64(b"num-queries", statement.num_queries as u64);
        transcript.observe_bytes(b"offset", &tower_leaf_payload(statement.offset));
        transcript.observe_bytes(b"ood-point", &tower_leaf_payload(statement.z));
        transcript.observe_bytes(b"claimed-value", &tower_leaf_payload(statement.y));
        for (index, beta) in statement.basis.iter().copied().enumerate() {
            transcript.observe_u64(b"basis-index", index as u64);
            transcript.observe_bytes(b"basis-element", &tower_leaf_payload(beta));
        }
        transcript.observe_root(b"evaluation-root", &statement.evaluation_root);
        Self {
            transcript,
            queries: None,
        }
    }

    fn queries(&self) -> Option<&[usize]> {
        self.queries.as_deref()
    }
}

impl ChallengeSource for PcsTranscriptSource {
    type Error = Infallible;

    fn observe_commitment(
        &mut self,
        round: usize,
        word_len: usize,
        root: &BinaryRoot,
    ) -> Result<(), Self::Error> {
        self.transcript.observe_u64(b"quotient-round", round as u64);
        self.transcript
            .observe_u64(b"quotient-word-length", word_len as u64);
        self.transcript.observe_root(b"quotient-root", root);
        Ok(())
    }

    fn draw_fold_challenge(
        &mut self,
        _round: usize,
        tower_level: u8,
    ) -> Result<TowerElem, Self::Error> {
        let sample = self.transcript.sample_gf2_64(b"quotient-fold-challenge");
        let mask = if tower_level == TOWER_LEVEL_GF2_64 {
            u64::MAX
        } else {
            (1u64 << (1usize << tower_level)) - 1
        };
        Ok(TowerElem::new(tower_level, sample & mask).expect("masked GF(2) sample is canonical"))
    }

    fn draw_query_indices(
        &mut self,
        initial_pair_count: usize,
        count: usize,
    ) -> Result<Vec<usize>, Self::Error> {
        let indices = (0..count)
            .map(|_| {
                (self.transcript.sample_gf2_64(b"pcs-query-index") as usize)
                    & (initial_pair_count - 1)
            })
            .collect::<Vec<_>>();
        self.queries = Some(indices.clone());
        Ok(indices)
    }
}

fn validate_public_inputs(
    basis: &[TowerElem],
    offset: TowerElem,
    coefficient_bound: usize,
    z: TowerElem,
    y: TowerElem,
    num_queries: usize,
) -> Result<(), AdditivePcsOodError> {
    if basis.is_empty()
        || offset.level() != TOWER_LEVEL_GF2_64
        || z.level() != TOWER_LEVEL_GF2_64
        || y.level() != TOWER_LEVEL_GF2_64
        || basis
            .iter()
            .any(|value| value.level() != TOWER_LEVEL_GF2_64)
    {
        return Err(AdditivePcsOodError::InvalidStatement);
    }
    let domain_size = checked_domain_size(basis.len())?;
    if coefficient_bound == 0 || coefficient_bound > domain_size || num_queries == 0 {
        return Err(AdditivePcsOodError::InvalidStatement);
    }
    let vectors = basis.iter().map(|value| value.bits()).collect::<Vec<_>>();
    if !gf2_independent(&vectors) || gf2_in_span(z.bits() ^ offset.bits(), &vectors) {
        return Err(AdditivePcsOodError::InvalidStatement);
    }
    Ok(())
}

fn gf2_independent(vectors: &[u64]) -> bool {
    let mut pivots = [0u64; 64];
    for &input in vectors {
        let mut value = input;
        while value != 0 {
            let pivot = 63 - value.leading_zeros() as usize;
            if pivots[pivot] == 0 {
                pivots[pivot] = value;
                break;
            }
            value ^= pivots[pivot];
        }
        if value == 0 {
            return false;
        }
    }
    true
}

fn gf2_in_span(target: u64, vectors: &[u64]) -> bool {
    let mut pivots = [0u64; 64];
    for &input in vectors {
        let mut value = input;
        while value != 0 {
            let pivot = 63 - value.leading_zeros() as usize;
            if pivots[pivot] == 0 {
                pivots[pivot] = value;
                break;
            }
            value ^= pivots[pivot];
        }
    }
    let mut value = target;
    while value != 0 {
        let pivot = 63 - value.leading_zeros() as usize;
        if pivots[pivot] == 0 {
            return false;
        }
        value ^= pivots[pivot];
    }
    true
}

fn quotient_bound(coefficient_bound: usize) -> usize {
    coefficient_bound.saturating_sub(1).max(1)
}

fn commit_word(
    word: &[TowerElem],
    hash: &BinaryShake256V1,
) -> Result<BinaryMerkleTree<BinaryRoot>, AdditivePcsOodError> {
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

fn vanishing_values(
    basis: &[TowerElem],
    x: TowerElem,
) -> Result<Vec<TowerElem>, AdditivePcsOodError> {
    let mut values = Vec::with_capacity(basis.len());
    let mut gamma: Vec<TowerElem> = Vec::with_capacity(basis.len());
    let mut current = x;
    for beta in basis.iter().copied() {
        values.push(current);
        let mut coefficient = beta;
        for prior in gamma.iter().copied() {
            coefficient = coefficient.square().add(prior.mul(coefficient)?)?;
        }
        gamma.push(coefficient);
        current = current.square().add(coefficient.mul(current)?)?;
    }
    Ok(values)
}

fn subspace_polynomials(basis: &[TowerElem]) -> Result<Vec<Vec<TowerElem>>, AdditivePcsOodError> {
    let level = basis[0].level();
    let zero = TowerElem::zero(level)?;
    let one = TowerElem::one(level)?;
    let mut current = vec![zero, one];
    let mut result = Vec::with_capacity(basis.len());
    for beta in basis.iter().copied() {
        result.push(current.clone());
        let gamma = poly_eval(&current, beta)?;
        let squared = poly_mul(&current, &current)?;
        let correction = poly_scale(&current, gamma)?;
        current = poly_add(&squared, &correction)?;
    }
    Ok(result)
}

fn novel_to_dense(
    coefficients: &[TowerElem],
    basis: &[TowerElem],
    bound: usize,
) -> Result<Vec<TowerElem>, AdditivePcsOodError> {
    let level = basis[0].level();
    let zero = TowerElem::zero(level)?;
    let one = TowerElem::one(level)?;
    let vanishing = subspace_polynomials(basis)?;
    let mut dense = vec![zero];
    for (index, coefficient) in coefficients.iter().copied().take(bound).enumerate() {
        if coefficient.is_zero() {
            continue;
        }
        let mut basis_polynomial = vec![one];
        for (i, polynomial) in vanishing.iter().enumerate() {
            if index & (1usize << i) != 0 {
                basis_polynomial = poly_mul(&basis_polynomial, polynomial)?;
            }
        }
        let term = poly_scale(&basis_polynomial, coefficient)?;
        dense = poly_add(&dense, &term)?;
    }
    trim_polynomial(&mut dense);
    Ok(dense)
}

fn divide_by_x_add_z(
    polynomial: &[TowerElem],
    y: TowerElem,
    z: TowerElem,
) -> Result<Vec<TowerElem>, AdditivePcsOodError> {
    let mut numerator = polynomial.to_vec();
    numerator[0] = numerator[0].add(y)?;
    trim_polynomial(&mut numerator);
    if numerator.len() == 1 {
        if !numerator[0].is_zero() {
            return Err(AdditivePcsOodError::PolynomialDivision);
        }
        return Ok(vec![TowerElem::zero(z.level())?]);
    }
    let degree = numerator.len() - 1;
    let mut quotient = vec![TowerElem::zero(z.level())?; degree];
    quotient[degree - 1] = numerator[degree];
    for i in (1..degree).rev() {
        quotient[i - 1] = numerator[i].add(z.mul(quotient[i])?)?;
    }
    let remainder = numerator[0].add(z.mul(quotient[0])?)?;
    if !remainder.is_zero() {
        return Err(AdditivePcsOodError::PolynomialDivision);
    }
    trim_polynomial(&mut quotient);
    Ok(quotient)
}

fn poly_eval(polynomial: &[TowerElem], x: TowerElem) -> Result<TowerElem, AdditivePcsOodError> {
    let mut value = TowerElem::zero(x.level())?;
    for coefficient in polynomial.iter().copied().rev() {
        value = value.mul(x)?.add(coefficient)?;
    }
    Ok(value)
}

fn poly_add(
    left: &[TowerElem],
    right: &[TowerElem],
) -> Result<Vec<TowerElem>, AdditivePcsOodError> {
    let level = left
        .first()
        .or_else(|| right.first())
        .ok_or(AdditivePcsOodError::PolynomialDivision)?
        .level();
    let mut result = vec![TowerElem::zero(level)?; left.len().max(right.len())];
    for (i, value) in left.iter().copied().enumerate() {
        result[i] = result[i].add(value)?;
    }
    for (i, value) in right.iter().copied().enumerate() {
        result[i] = result[i].add(value)?;
    }
    trim_polynomial(&mut result);
    Ok(result)
}

fn poly_scale(
    polynomial: &[TowerElem],
    scalar: TowerElem,
) -> Result<Vec<TowerElem>, AdditivePcsOodError> {
    polynomial
        .iter()
        .copied()
        .map(|coefficient| coefficient.mul(scalar).map_err(AdditivePcsOodError::from))
        .collect()
}

fn poly_mul(
    left: &[TowerElem],
    right: &[TowerElem],
) -> Result<Vec<TowerElem>, AdditivePcsOodError> {
    let level = left[0].level();
    let mut result = vec![TowerElem::zero(level)?; left.len() + right.len() - 1];
    for (i, a) in left.iter().copied().enumerate() {
        for (j, b) in right.iter().copied().enumerate() {
            result[i + j] = result[i + j].add(a.mul(b)?)?;
        }
    }
    trim_polynomial(&mut result);
    Ok(result)
}

fn trim_polynomial(polynomial: &mut Vec<TowerElem>) {
    while polynomial.len() > 1 && polynomial.last().is_some_and(|value| value.is_zero()) {
        polynomial.pop();
    }
}

fn domain_points(
    basis: &[TowerElem],
    offset: TowerElem,
) -> Result<Vec<TowerElem>, AdditivePcsOodError> {
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
) -> Result<TowerElem, AdditivePcsOodError> {
    let mut point = offset;
    for (i, beta) in basis.iter().copied().enumerate() {
        if index & (1usize << i) != 0 {
            point = point.add(beta)?;
        }
    }
    Ok(point)
}

fn checked_domain_size(log_size: usize) -> Result<usize, AdditivePcsOodError> {
    1usize
        .checked_shl(log_size as u32)
        .ok_or(AdditivePcsOodError::InvalidStatement)
}
