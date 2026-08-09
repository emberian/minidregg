//! A field-generic multilinear sumcheck core.
//!
//! The existing `sumcheck.rs` is deliberately frozen as the BabyBear
//! conformance rung.  This isolated implementation makes the scalar generic so
//! gate defects can be lifted from BabyBear and every batching/sumcheck
//! challenge can live in BabyBear⁶.  It uses the repository's LSB-first cube
//! convention: adjacent entries differ in the current coordinate.

use core::fmt;

/// The operations required by multilinear sumcheck; inversion is not needed.
pub trait SumcheckScalar: Copy + Eq + fmt::Debug {
    const ZERO: Self;
    const ONE: Self;

    fn add(self, rhs: Self) -> Self;
    fn sub(self, rhs: Self) -> Self;
    fn mul(self, rhs: Self) -> Self;
}

/// A canonical embedding of one base-field representative.
pub trait BaseEmbedding: SumcheckScalar {
    fn try_from_base(value: u64) -> Option<Self>;
}

impl SumcheckScalar for crate::field6::Ext6 {
    const ZERO: Self = crate::field6::Ext6::ZERO;
    const ONE: Self = crate::field6::Ext6::ONE;

    fn add(self, rhs: Self) -> Self {
        self.add(rhs)
    }

    fn sub(self, rhs: Self) -> Self {
        self.sub(rhs)
    }

    fn mul(self, rhs: Self) -> Self {
        self.mul(rhs)
    }
}

impl BaseEmbedding for crate::field6::Ext6 {
    fn try_from_base(value: u64) -> Option<Self> {
        crate::field6::Ext6::try_from_base(value).ok()
    }
}

/// Shape/canonicality failures are errors, never verifier panics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SumcheckError {
    EmptyTable,
    NonPowerOfTwo { len: usize },
    ChallengeCount { expected: usize, actual: usize },
    RoundCount { expected: usize, actual: usize },
    NonCanonicalBase { value: u64 },
}

impl fmt::Display for SumcheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SumcheckError::EmptyTable => write!(f, "sumcheck table is empty"),
            SumcheckError::NonPowerOfTwo { len } => {
                write!(f, "sumcheck table length {len} is not a power of two")
            }
            SumcheckError::ChallengeCount { expected, actual } => {
                write!(f, "sumcheck has {actual} challenges, expected {expected}")
            }
            SumcheckError::RoundCount { expected, actual } => {
                write!(f, "sumcheck proof has {actual} rounds, expected {expected}")
            }
            SumcheckError::NonCanonicalBase { value } => {
                write!(f, "cannot embed non-canonical base value {value}")
            }
        }
    }
}

impl std::error::Error for SumcheckError {}

/// Fiat--Shamir challenges and the claim are deliberately absent: the protocol
/// derives challenges after each message and supplies the expected claim from
/// the statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumcheckProof<E> {
    pub rounds: Vec<[E; 2]>,
}

fn cube_dim<E>(table: &[E]) -> Result<usize, SumcheckError> {
    if table.is_empty() {
        Err(SumcheckError::EmptyTable)
    } else if !table.len().is_power_of_two() {
        Err(SumcheckError::NonPowerOfTwo { len: table.len() })
    } else {
        Ok(table.len().trailing_zeros() as usize)
    }
}

fn sum<E: SumcheckScalar>(values: impl IntoIterator<Item = E>) -> E {
    values
        .into_iter()
        .fold(E::ZERO, |accumulator, value| accumulator.add(value))
}

/// Sum of the original Boolean-hypercube table.
pub fn claimed_sum<E: SumcheckScalar>(table: &[E]) -> Result<E, SumcheckError> {
    cube_dim(table)?;
    Ok(sum(table.iter().copied()))
}

fn fold_layer<E: SumcheckScalar>(layer: &[E], challenge: E) -> Vec<E> {
    layer
        .chunks_exact(2)
        .map(|pair| pair[0].add(pair[1].sub(pair[0]).mul(challenge)))
        .collect()
}

/// Evaluate the table's multilinear extension at an LSB-first point in `O(N)`
/// field operations.
pub fn evaluate_mle<E: SumcheckScalar>(table: &[E], challenges: &[E]) -> Result<E, SumcheckError> {
    let expected = cube_dim(table)?;
    if challenges.len() != expected {
        return Err(SumcheckError::ChallengeCount {
            expected,
            actual: challenges.len(),
        });
    }
    let mut layer = table.to_vec();
    for &challenge in challenges {
        layer = fold_layer(&layer, challenge);
    }
    Ok(layer[0])
}

/// Honest multilinear sumcheck messages at a caller-supplied challenge schedule.
/// A future transcript wrapper must interleave each returned message with the
/// challenge draw rather than serializing `challenges` into the proof.
pub fn prove<E: SumcheckScalar>(
    table: &[E],
    challenges: &[E],
) -> Result<SumcheckProof<E>, SumcheckError> {
    let expected = cube_dim(table)?;
    if challenges.len() != expected {
        return Err(SumcheckError::ChallengeCount {
            expected,
            actual: challenges.len(),
        });
    }
    let mut layer = table.to_vec();
    let mut rounds = Vec::with_capacity(expected);
    for &challenge in challenges {
        let g0 = sum(layer.iter().step_by(2).copied());
        let g1 = sum(layer.iter().skip(1).step_by(2).copied());
        rounds.push([g0, g1]);
        layer = fold_layer(&layer, challenge);
    }
    Ok(SumcheckProof { rounds })
}

/// Verify the sumcheck chain against a statement-supplied claim and terminal
/// oracle value.  Malformed round counts return an error; algebraic failures
/// return `Ok(false)`.
pub fn verify<E: SumcheckScalar>(
    expected_claim: E,
    proof: &SumcheckProof<E>,
    challenges: &[E],
    terminal_oracle_value: E,
) -> Result<bool, SumcheckError> {
    if proof.rounds.len() != challenges.len() {
        return Err(SumcheckError::RoundCount {
            expected: challenges.len(),
            actual: proof.rounds.len(),
        });
    }
    let mut running = expected_claim;
    for (&[g0, g1], &challenge) in proof.rounds.iter().zip(challenges.iter()) {
        if g0.add(g1) != running {
            return Ok(false);
        }
        running = g0.add(g1.sub(g0).mul(challenge));
    }
    Ok(running == terminal_oracle_value)
}

/// Lift base-field gate residuals and weight entry `k` by `gamma^k`.  This is
/// the executable mirror of applying the existing field-generic batching
/// theorem after `algebraMap` into the challenge field.
pub fn batch_lifted_residuals<E: BaseEmbedding>(
    residuals: &[u64],
    gamma: E,
) -> Result<Vec<E>, SumcheckError> {
    let mut power = E::ONE;
    let mut out = Vec::with_capacity(residuals.len());
    for &residual in residuals {
        let lifted = E::try_from_base(residual)
            .ok_or(SumcheckError::NonCanonicalBase { value: residual })?;
        out.push(power.mul(lifted));
        power = power.mul(gamma);
    }
    Ok(out)
}
