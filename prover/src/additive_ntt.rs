//! Fast evaluation/interpolation in the unnormalised LCH novel basis.
//!
//! This is the executable counterpart of `Theory.AdditiveNTT.novelBasisTransform`.
//! Given an ordered GF(2)-independent basis `beta[0..k]`, coefficients are
//! indexed by a little-endian bit vector and represent
//!
//! ```text
//! P(X) = sum_j a[j] * product_i W_i(X)^bit(j,i),
//! W_0(X) = X,
//! W_{i+1}(X) = W_i(X)^2 + W_i(beta_i) W_i(X).
//! ```
//!
//! On an affine coset `alpha + W_k`, split `P = P0 + W_{k-1} P1`.
//! The last vanishing polynomial is constant on each half of that coset, so
//! one butterfly produces the two smaller transforms:
//!
//! ```text
//! left_i  = a0_i + W_{k-1}(alpha)                 * a1_i
//! right_i = a0_i + (W_{k-1}(alpha)+W_{k-1}(beta)) * a1_i.
//! ```
//!
//! Recursing gives exactly `n log2(n) / 2` butterflies and O(n log n) field
//! operations.  The inverse reverses the same schedule.  A deliberately slow
//! dense evaluator is kept as an executable oracle for conformance tests.
//!
//! This remains isolated arithmetic, not a prover backend.  Honest residuals:
//!
//! * `[ANTT-basis-coherence-runtime]`: formally identify this explicit bit
//!   basis and domain order with Lean's choice-selected `binaryTower` values.
//! * `[ANTT-RUST-UNVERIFIED]`: the Rust schedule is unverified compute; Lean
//!   emits the authoritative interface and verifier rather than "refining" Rust
//!   `novelBasisTransform`/its inverse in a semantics for Rust.
//! * `[ANTT-protocol-runtime]`: commitments, transcript, query scheduling, and
//!   multi-round additive-FRI integration are not supplied by this module.

use core::fmt;

use crate::binary_tower::{TowerElem, TowerError};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdditiveNttError {
    Tower(TowerError),
    EmptyInput,
    LengthNotPowerOfTwo(usize),
    BasisLengthMismatch {
        expected: usize,
        actual: usize,
    },
    DomainTooLarge {
        basis_len: usize,
        dimension: usize,
    },
    FieldLevelMismatch {
        role: &'static str,
        index: usize,
        expected: u8,
        actual: u8,
    },
    DependentBasis {
        index: usize,
    },
}

impl From<TowerError> for AdditiveNttError {
    fn from(value: TowerError) -> Self {
        Self::Tower(value)
    }
}

impl fmt::Display for AdditiveNttError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Tower(error) => error.fmt(f),
            Self::EmptyInput => write!(f, "an additive transform needs at least one value"),
            Self::LengthNotPowerOfTwo(len) => {
                write!(f, "additive transform length {len} is not a power of two")
            }
            Self::BasisLengthMismatch { expected, actual } => write!(
                f,
                "additive transform needs {expected} basis elements, got {actual}"
            ),
            Self::DomainTooLarge {
                basis_len,
                dimension,
            } => write!(
                f,
                "{basis_len} independent directions do not fit field dimension {dimension}"
            ),
            Self::FieldLevelMismatch {
                role,
                index,
                expected,
                actual,
            } => write!(
                f,
                "{role}[{index}] is at tower level {actual}, expected {expected}"
            ),
            Self::DependentBasis { index } => write!(
                f,
                "basis[{index}] lies in the span of the preceding directions"
            ),
        }
    }
}

impl std::error::Error for AdditiveNttError {}

/// Evaluate novel-basis coefficients on `offset + span(basis)` in place.
///
/// Inputs and outputs use the same little-endian bit order: bit `i` selects
/// `W_i` in a coefficient index and `basis[i]` in a domain-point index.
pub fn forward_in_place(
    coefficients: &mut [TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
) -> Result<(), AdditiveNttError> {
    let gamma = validate_and_vanishing_constants(coefficients, basis, offset)?;
    forward_recursive(coefficients, basis, &gamma, offset)
}

/// Allocate the output of [`forward_in_place`] while preserving coefficients.
pub fn forward(
    coefficients: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
) -> Result<Vec<TowerElem>, AdditiveNttError> {
    let mut output = coefficients.to_vec();
    forward_in_place(&mut output, basis, offset)?;
    Ok(output)
}

/// Interpolate evaluations on `offset + span(basis)` back to novel-basis
/// coefficients, reversing [`forward_in_place`] in O(n log n) operations.
pub fn inverse_in_place(
    evaluations: &mut [TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
) -> Result<(), AdditiveNttError> {
    let gamma = validate_and_vanishing_constants(evaluations, basis, offset)?;
    let inverse_gamma = gamma
        .iter()
        .map(|value| value.inverse().map_err(AdditiveNttError::from))
        .collect::<Result<Vec<_>, _>>()?;
    inverse_recursive(evaluations, basis, &gamma, &inverse_gamma, offset)
}

/// Allocate the output of [`inverse_in_place`] while preserving evaluations.
pub fn inverse(
    evaluations: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
) -> Result<Vec<TowerElem>, AdditiveNttError> {
    let mut output = evaluations.to_vec();
    inverse_in_place(&mut output, basis, offset)?;
    Ok(output)
}

/// Directly evaluate the Lean `novelBasisTransform` sum.
///
/// This is O(n^2 log n), intended only as a small-domain specification oracle.
pub fn forward_dense_reference(
    coefficients: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
) -> Result<Vec<TowerElem>, AdditiveNttError> {
    let gamma = validate_and_vanishing_constants(coefficients, basis, offset)?;
    let level = offset.level();
    let mut output = Vec::with_capacity(coefficients.len());

    for domain_index in 0..coefficients.len() {
        let point = domain_point(basis, offset, domain_index)?;
        let vanishing_values = vanishing_prefix_values(point, &gamma)?;
        let mut value = TowerElem::zero(level)?;

        for (coefficient_index, coefficient) in coefficients.iter().copied().enumerate() {
            let mut term = coefficient;
            for (i, vanishing) in vanishing_values.iter().copied().enumerate() {
                if coefficient_index & (1usize << i) != 0 {
                    term = term.mul(vanishing)?;
                }
            }
            value = value.add(term)?;
        }
        output.push(value);
    }
    Ok(output)
}

fn validate_and_vanishing_constants(
    values: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
) -> Result<Vec<TowerElem>, AdditiveNttError> {
    if values.is_empty() {
        return Err(AdditiveNttError::EmptyInput);
    }
    if !values.len().is_power_of_two() {
        return Err(AdditiveNttError::LengthNotPowerOfTwo(values.len()));
    }
    let log_n = values.len().ilog2() as usize;
    if basis.len() != log_n {
        return Err(AdditiveNttError::BasisLengthMismatch {
            expected: log_n,
            actual: basis.len(),
        });
    }

    let level = offset.level();
    let dimension = 1usize << level;
    if basis.len() > dimension {
        return Err(AdditiveNttError::DomainTooLarge {
            basis_len: basis.len(),
            dimension,
        });
    }
    for (index, value) in values.iter().copied().enumerate() {
        check_level("value", index, level, value)?;
    }
    for (index, value) in basis.iter().copied().enumerate() {
        check_level("basis", index, level, value)?;
    }

    let mut gamma = Vec::with_capacity(basis.len());
    for (i, beta) in basis.iter().copied().enumerate() {
        let value = subspace_vanishing_eval(&gamma, beta)?;
        if value.is_zero() {
            return Err(AdditiveNttError::DependentBasis { index: i });
        }
        gamma.push(value);
    }
    Ok(gamma)
}

fn check_level(
    role: &'static str,
    index: usize,
    expected: u8,
    value: TowerElem,
) -> Result<(), AdditiveNttError> {
    if value.level() == expected {
        Ok(())
    } else {
        Err(AdditiveNttError::FieldLevelMismatch {
            role,
            index,
            expected,
            actual: value.level(),
        })
    }
}

/// Evaluate W_i at `x`, where `gamma[j] = W_j(beta_j)` for `j < i`.
fn subspace_vanishing_eval(
    gamma: &[TowerElem],
    x: TowerElem,
) -> Result<TowerElem, AdditiveNttError> {
    let mut value = x;
    for coefficient in gamma.iter().copied() {
        value = value.square().add(coefficient.mul(value)?)?;
    }
    Ok(value)
}

/// Return `[W_0(x), ..., W_{k-1}(x)]`.
fn vanishing_prefix_values(
    x: TowerElem,
    gamma: &[TowerElem],
) -> Result<Vec<TowerElem>, AdditiveNttError> {
    let mut output = Vec::with_capacity(gamma.len());
    let mut value = x;
    for coefficient in gamma.iter().copied() {
        output.push(value);
        value = value.square().add(coefficient.mul(value)?)?;
    }
    Ok(output)
}

fn domain_point(
    basis: &[TowerElem],
    offset: TowerElem,
    index: usize,
) -> Result<TowerElem, AdditiveNttError> {
    let mut point = offset;
    for (i, beta) in basis.iter().copied().enumerate() {
        if index & (1usize << i) != 0 {
            point = point.add(beta)?;
        }
    }
    Ok(point)
}

fn forward_recursive(
    data: &mut [TowerElem],
    basis: &[TowerElem],
    gamma: &[TowerElem],
    offset: TowerElem,
) -> Result<(), AdditiveNttError> {
    let Some(last) = basis.len().checked_sub(1) else {
        return Ok(());
    };
    let half = data.len() / 2;
    let at_offset = subspace_vanishing_eval(&gamma[..last], offset)?;
    let at_right = at_offset.add(gamma[last])?;

    for i in 0..half {
        let low = data[i];
        let high = data[half + i];
        data[i] = low.add(at_offset.mul(high)?)?;
        data[half + i] = low.add(at_right.mul(high)?)?;
    }

    let right_offset = offset.add(basis[last])?;
    let (left, right) = data.split_at_mut(half);
    forward_recursive(left, &basis[..last], &gamma[..last], offset)?;
    forward_recursive(right, &basis[..last], &gamma[..last], right_offset)
}

fn inverse_recursive(
    data: &mut [TowerElem],
    basis: &[TowerElem],
    gamma: &[TowerElem],
    inverse_gamma: &[TowerElem],
    offset: TowerElem,
) -> Result<(), AdditiveNttError> {
    let Some(last) = basis.len().checked_sub(1) else {
        return Ok(());
    };
    let half = data.len() / 2;
    let right_offset = offset.add(basis[last])?;
    let (left, right) = data.split_at_mut(half);
    inverse_recursive(
        left,
        &basis[..last],
        &gamma[..last],
        &inverse_gamma[..last],
        offset,
    )?;
    inverse_recursive(
        right,
        &basis[..last],
        &gamma[..last],
        &inverse_gamma[..last],
        right_offset,
    )?;

    let at_offset = subspace_vanishing_eval(&gamma[..last], offset)?;
    for i in 0..half {
        let left_value = left[i];
        let right_value = right[i];
        let high = left_value.add(right_value)?.mul(inverse_gamma[last])?;
        left[i] = left_value.add(at_offset.mul(high)?)?;
        right[i] = high;
    }
    Ok(())
}
