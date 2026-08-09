//! Native multilinear-extension arithmetic.
//!
//! This module contains no complete statements, transcripts, proof carriers,
//! verifiers, or final acceptance predicates. It nevertheless authors native
//! representation and transform conventions: LSB-first Boolean indexing,
//! adjacent-variable folds, reversed-LCH basis/bit order, and multiplicative
//! domain pairing. Callers supply tables, domains, and challenges directly.
//! These conventions are unverified; no compiled generated adapter currently
//! selects, checks, or invokes them as a Lean-owned profile.

use core::fmt;

use crate::{
    additive_ntt::{forward, AdditiveNttError},
    babybear::{binv, bmul, bpow, two_adic_generator, HALF, TWO_ADIC_BITS},
    binary_tower::{additive_fold_map, additive_fold_pair, TowerElem, TowerError, MAX_LEVEL},
    binary_tower_256::{Tower256, Tower256Error},
    field6::Ext6,
};

/// Arithmetic-shape failures at the native-kernel boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MleKernelError {
    EmptyTable,
    NonPowerOfTwo {
        len: usize,
    },
    CannotFoldSingleton,
    LengthMismatch {
        left: usize,
        right: usize,
    },
    PointLength {
        expected: usize,
        actual: usize,
    },
    DomainLength {
        expected: usize,
        actual: usize,
    },
    DomainSizeOverflow {
        dimensions: usize,
    },
    DependentBasis {
        index: usize,
    },
    FieldLevel {
        role: &'static str,
        index: usize,
        expected: u8,
        actual: u8,
    },
    TwoAdicDomainTooLarge {
        bits: u32,
        maximum: u32,
    },
    AdditiveNtt(AdditiveNttError),
    Tower(TowerError),
    Tower256(Tower256Error),
}

impl fmt::Display for MleKernelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyTable => write!(f, "an MLE table must be nonempty"),
            Self::NonPowerOfTwo { len } => {
                write!(f, "MLE table length {len} is not a power of two")
            }
            Self::CannotFoldSingleton => write!(f, "a singleton table has no variable to fold"),
            Self::LengthMismatch { left, right } => {
                write!(f, "vector lengths differ: {left} and {right}")
            }
            Self::PointLength { expected, actual } => {
                write!(f, "MLE point has length {actual}, expected {expected}")
            }
            Self::DomainLength { expected, actual } => {
                write!(f, "domain word has length {actual}, expected {expected}")
            }
            Self::DomainSizeOverflow { dimensions } => {
                write!(f, "a {dimensions}-dimensional domain does not fit in usize")
            }
            Self::DependentBasis { index } => {
                write!(f, "basis[{index}] depends on the preceding directions")
            }
            Self::FieldLevel {
                role,
                index,
                expected,
                actual,
            } => write!(
                f,
                "{role}[{index}] has tower level {actual}, expected {expected}"
            ),
            Self::TwoAdicDomainTooLarge { bits, maximum } => write!(
                f,
                "2-adic domain has {bits} bits, but the field supports at most {maximum}"
            ),
            Self::AdditiveNtt(error) => error.fmt(f),
            Self::Tower(error) => error.fmt(f),
            Self::Tower256(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for MleKernelError {}

impl From<AdditiveNttError> for MleKernelError {
    fn from(value: AdditiveNttError) -> Self {
        Self::AdditiveNtt(value)
    }
}

impl From<TowerError> for MleKernelError {
    fn from(value: TowerError) -> Self {
        Self::Tower(value)
    }
}

impl From<Tower256Error> for MleKernelError {
    fn from(value: Tower256Error) -> Self {
        Self::Tower256(value)
    }
}

/// Minimal arithmetic used by value-table Mobius transforms and MLE folds.
pub trait NativeMleScalar: Copy {
    fn add_native(self, rhs: Self) -> Result<Self, MleKernelError>;
    fn sub_native(self, rhs: Self) -> Result<Self, MleKernelError>;
    fn mul_native(self, rhs: Self) -> Result<Self, MleKernelError>;
}

impl NativeMleScalar for Ext6 {
    fn add_native(self, rhs: Self) -> Result<Self, MleKernelError> {
        Ok(self.add(rhs))
    }

    fn sub_native(self, rhs: Self) -> Result<Self, MleKernelError> {
        Ok(self.sub(rhs))
    }

    fn mul_native(self, rhs: Self) -> Result<Self, MleKernelError> {
        Ok(self.mul(rhs))
    }
}

impl NativeMleScalar for TowerElem {
    fn add_native(self, rhs: Self) -> Result<Self, MleKernelError> {
        Ok(self.add(rhs)?)
    }

    fn sub_native(self, rhs: Self) -> Result<Self, MleKernelError> {
        // The binary tower has characteristic two.
        Ok(self.add(rhs)?)
    }

    fn mul_native(self, rhs: Self) -> Result<Self, MleKernelError> {
        Ok(self.mul(rhs)?)
    }
}

impl NativeMleScalar for Tower256 {
    fn add_native(self, rhs: Self) -> Result<Self, MleKernelError> {
        Ok(self.add(rhs))
    }

    fn sub_native(self, rhs: Self) -> Result<Self, MleKernelError> {
        // The binary tower has characteristic two.
        Ok(self.add(rhs))
    }

    fn mul_native(self, rhs: Self) -> Result<Self, MleKernelError> {
        Ok(self.mul(rhs))
    }
}

fn table_dimension<T>(table: &[T]) -> Result<usize, MleKernelError> {
    if table.is_empty() {
        Err(MleKernelError::EmptyTable)
    } else if !table.len().is_power_of_two() {
        Err(MleKernelError::NonPowerOfTwo { len: table.len() })
    } else {
        Ok(table.len().trailing_zeros() as usize)
    }
}

/// Convert LSB-indexed Boolean values to multilinear monomial coefficients.
pub fn boolean_mobius_coefficients<S: NativeMleScalar>(
    table: &[S],
) -> Result<Vec<S>, MleKernelError> {
    let variables = table_dimension(table)?;
    let mut coefficients = table.to_vec();
    for bit in 0..variables {
        let flag = 1usize << bit;
        for mask in 0..table.len() {
            if mask & flag != 0 {
                coefficients[mask] = coefficients[mask].sub_native(coefficients[mask ^ flag])?;
            }
        }
    }
    Ok(coefficients)
}

/// Bind the next LSB variable of a multilinear value table.
pub fn fold_mle_table<S: NativeMleScalar>(
    table: &[S],
    challenge: S,
) -> Result<Vec<S>, MleKernelError> {
    table_dimension(table)?;
    if table.len() == 1 {
        return Err(MleKernelError::CannotFoldSingleton);
    }
    table
        .chunks_exact(2)
        .map(|pair| pair[0].add_native(pair[1].sub_native(pair[0])?.mul_native(challenge)?))
        .collect()
}

/// Bind the next LSB variable of multilinear monomial coefficients.
pub fn fold_mle_coefficients<S: NativeMleScalar>(
    coefficients: &[S],
    challenge: S,
) -> Result<Vec<S>, MleKernelError> {
    table_dimension(coefficients)?;
    if coefficients.len() == 1 {
        return Err(MleKernelError::CannotFoldSingleton);
    }
    coefficients
        .chunks_exact(2)
        .map(|pair| pair[0].add_native(pair[1].mul_native(challenge)?))
        .collect()
}

/// Evaluate an LSB-indexed Boolean table's multilinear extension.
pub fn evaluate_mle<S: NativeMleScalar>(table: &[S], point: &[S]) -> Result<S, MleKernelError> {
    let expected = table_dimension(table)?;
    if point.len() != expected {
        return Err(MleKernelError::PointLength {
            expected,
            actual: point.len(),
        });
    }
    let mut layer = table.to_vec();
    for &challenge in point {
        layer = fold_mle_table(&layer, challenge)?;
    }
    Ok(layer[0])
}

/// Compute `sum_i values[i] * weights[i]` from a caller-supplied additive zero.
pub fn linear_functional_dot<S: NativeMleScalar>(
    values: &[S],
    weights: &[S],
    zero: S,
) -> Result<S, MleKernelError> {
    if values.len() != weights.len() {
        return Err(MleKernelError::LengthMismatch {
            left: values.len(),
            right: weights.len(),
        });
    }
    values
        .iter()
        .copied()
        .zip(weights.iter().copied())
        .try_fold(zero, |sum, (value, weight)| {
            sum.add_native(value.mul_native(weight)?)
        })
}

/// Encode GF(2^64) novel-basis coefficients on the ordinary LSB affine order
/// while using the reversed LCH polynomial chain.
pub fn reversed_lch_encode_gf64(
    coefficients: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
) -> Result<Vec<TowerElem>, MleKernelError> {
    check_gf64_levels("coefficient", coefficients)?;
    check_gf64_levels("basis", basis)?;
    check_gf64_levels("offset", core::slice::from_ref(&offset))?;
    let expected = checked_domain_size(basis.len())?;
    if coefficients.len() != expected {
        return Err(MleKernelError::DomainLength {
            expected,
            actual: coefficients.len(),
        });
    }
    let reversed_basis = basis.iter().copied().rev().collect::<Vec<_>>();
    let reversed_domain_word = forward(coefficients, &reversed_basis, offset)?;
    Ok(bit_reverse_domain(&reversed_domain_word, basis.len()))
}

/// Fold one GF(2^64) reversed-LCH word and transport its affine domain.
pub fn fold_reversed_lch_round_gf64(
    word: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
    challenge: TowerElem,
) -> Result<(Vec<TowerElem>, Vec<TowerElem>, TowerElem), MleKernelError> {
    check_gf64_levels("word", word)?;
    check_gf64_levels("basis", basis)?;
    check_gf64_levels("offset", core::slice::from_ref(&offset))?;
    check_gf64_levels("challenge", core::slice::from_ref(&challenge))?;
    let expected = checked_domain_size(basis.len())?;
    if word.len() != expected {
        return Err(MleKernelError::DomainLength {
            expected,
            actual: word.len(),
        });
    }
    if word.len() == 1 {
        return Err(MleKernelError::CannotFoldSingleton);
    }
    let beta = basis[basis.len() - 1];
    let half = word.len() / 2;
    let points = gf64_domain_points(&basis[..basis.len() - 1], offset)?;
    let folded = (0..half)
        .map(|index| {
            additive_fold_pair(
                beta,
                challenge,
                points[index],
                word[index],
                word[half + index],
            )
            .map_err(MleKernelError::from)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let next_basis = basis[..basis.len() - 1]
        .iter()
        .copied()
        .map(|value| additive_fold_map(beta, value).map_err(MleKernelError::from))
        .collect::<Result<Vec<_>, _>>()?;
    let next_offset = additive_fold_map(beta, offset)?;
    Ok((folded, next_basis, next_offset))
}

/// Encode GF(2^256) novel-basis coefficients on the ordinary LSB affine order
/// while using the reversed LCH polynomial chain.
pub fn reversed_lch_encode_tower256(
    coefficients: &[Tower256],
    basis: &[Tower256],
    offset: Tower256,
) -> Result<Vec<Tower256>, MleKernelError> {
    let expected = checked_domain_size(basis.len())?;
    if coefficients.len() != expected {
        return Err(MleKernelError::DomainLength {
            expected,
            actual: coefficients.len(),
        });
    }
    let reversed_basis = basis.iter().copied().rev().collect::<Vec<_>>();
    let mut reversed_domain_word = coefficients.to_vec();
    tower256_forward_in_place(&mut reversed_domain_word, &reversed_basis, offset)?;
    Ok(bit_reverse_domain(&reversed_domain_word, basis.len()))
}

/// Fold one GF(2^256) reversed-LCH word and transport its affine domain.
pub fn fold_reversed_lch_round_tower256(
    word: &[Tower256],
    basis: &[Tower256],
    offset: Tower256,
    challenge: Tower256,
) -> Result<(Vec<Tower256>, Vec<Tower256>, Tower256), MleKernelError> {
    let expected = checked_domain_size(basis.len())?;
    if word.len() != expected {
        return Err(MleKernelError::DomainLength {
            expected,
            actual: word.len(),
        });
    }
    if word.len() == 1 {
        return Err(MleKernelError::CannotFoldSingleton);
    }
    let beta = basis[basis.len() - 1];
    let beta_inverse = beta.inverse()?;
    let half = word.len() / 2;
    let points = tower256_domain_points(&basis[..basis.len() - 1], offset);
    let folded = (0..half)
        .map(|index| {
            tower256_fold_pair_with_inverse(
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
        .map(|value| tower256_fold_map(beta, value))
        .collect();
    let next_offset = tower256_fold_map(beta, offset);
    Ok((folded, next_basis, next_offset))
}

/// Bind adjacent Ext6 monomial coefficients to one challenge.
pub fn fold_ext6_coefficients(
    coefficients: &[Ext6],
    challenge: Ext6,
) -> Result<Vec<Ext6>, MleKernelError> {
    fold_mle_coefficients(coefficients, challenge)
}

/// Fold the even/odd halves of an Ext6 multiplicative-domain evaluation word.
pub fn fold_ext6_multiplicative_word(
    word: &[Ext6],
    challenge: Ext6,
) -> Result<Vec<Ext6>, MleKernelError> {
    let log_n = table_dimension(word)? as u32;
    if word.len() == 1 {
        return Err(MleKernelError::CannotFoldSingleton);
    }
    if log_n > TWO_ADIC_BITS {
        return Err(MleKernelError::TwoAdicDomainTooLarge {
            bits: log_n,
            maximum: TWO_ADIC_BITS,
        });
    }
    let half = word.len() / 2;
    Ok((0..half)
        .map(|index| {
            ext6_multiplicative_fold_pair(
                word[index],
                word[half + index],
                challenge,
                ext6_level_twiddle(log_n, index),
            )
        })
        .collect())
}

fn checked_domain_size(dimensions: usize) -> Result<usize, MleKernelError> {
    let shift =
        u32::try_from(dimensions).map_err(|_| MleKernelError::DomainSizeOverflow { dimensions })?;
    1usize
        .checked_shl(shift)
        .ok_or(MleKernelError::DomainSizeOverflow { dimensions })
}

fn check_gf64_levels(role: &'static str, values: &[TowerElem]) -> Result<(), MleKernelError> {
    for (index, value) in values.iter().copied().enumerate() {
        if value.level() != MAX_LEVEL {
            return Err(MleKernelError::FieldLevel {
                role,
                index,
                expected: MAX_LEVEL,
                actual: value.level(),
            });
        }
    }
    Ok(())
}

fn bit_reverse_domain<T: Copy>(values: &[T], bits: usize) -> Vec<T> {
    if bits == 0 {
        return values.to_vec();
    }
    (0..values.len())
        .map(|index| values[reverse_low_bits(index, bits)])
        .collect()
}

fn reverse_low_bits(mut value: usize, bits: usize) -> usize {
    let mut reversed = 0usize;
    for _ in 0..bits {
        reversed = (reversed << 1) | (value & 1);
        value >>= 1;
    }
    reversed
}

fn gf64_domain_points(
    basis: &[TowerElem],
    offset: TowerElem,
) -> Result<Vec<TowerElem>, MleKernelError> {
    let mut points = vec![offset];
    for &beta in basis {
        let old_len = points.len();
        for index in 0..old_len {
            points.push(points[index].add(beta)?);
        }
    }
    Ok(points)
}

fn tower256_forward_in_place(
    values: &mut [Tower256],
    basis: &[Tower256],
    offset: Tower256,
) -> Result<(), MleKernelError> {
    let gamma = tower256_vanishing_constants(basis)?;
    tower256_forward_recursive(values, basis, &gamma, offset)
}

fn tower256_vanishing_constants(basis: &[Tower256]) -> Result<Vec<Tower256>, MleKernelError> {
    let mut gamma = Vec::with_capacity(basis.len());
    for (index, &beta) in basis.iter().enumerate() {
        let value = tower256_subspace_vanishing_eval(&gamma, beta);
        if value.is_zero() {
            return Err(MleKernelError::DependentBasis { index });
        }
        gamma.push(value);
    }
    Ok(gamma)
}

fn tower256_subspace_vanishing_eval(gamma: &[Tower256], x: Tower256) -> Tower256 {
    gamma.iter().copied().fold(x, |value, coefficient| {
        value.square().add(coefficient.mul(value))
    })
}

fn tower256_forward_recursive(
    data: &mut [Tower256],
    basis: &[Tower256],
    gamma: &[Tower256],
    offset: Tower256,
) -> Result<(), MleKernelError> {
    let Some(last) = basis.len().checked_sub(1) else {
        return Ok(());
    };
    let half = data.len() / 2;
    let at_offset = tower256_subspace_vanishing_eval(&gamma[..last], offset);
    let at_right = at_offset.add(gamma[last]);
    for index in 0..half {
        let low = data[index];
        let high = data[half + index];
        data[index] = low.add(at_offset.mul(high));
        data[half + index] = low.add(at_right.mul(high));
    }
    let right_offset = offset.add(basis[last]);
    let (left, right) = data.split_at_mut(half);
    tower256_forward_recursive(left, &basis[..last], &gamma[..last], offset)?;
    tower256_forward_recursive(right, &basis[..last], &gamma[..last], right_offset)
}

fn tower256_fold_map(beta: Tower256, x: Tower256) -> Tower256 {
    x.square().add(beta.mul(x))
}

fn tower256_fold_pair_with_inverse(
    challenge: Tower256,
    x: Tower256,
    low: Tower256,
    high: Tower256,
    beta_inverse: Tower256,
) -> Tower256 {
    let odd = low.add(high).mul(beta_inverse);
    low.add(x.add(challenge).mul(odd))
}

fn tower256_domain_points(basis: &[Tower256], offset: Tower256) -> Vec<Tower256> {
    let mut points = vec![offset];
    for &beta in basis {
        let old_len = points.len();
        for index in 0..old_len {
            points.push(points[index].add(beta));
        }
    }
    points
}

fn ext6_multiplicative_fold_pair(low: Ext6, high: Ext6, challenge: Ext6, twiddle: u64) -> Ext6 {
    low.add(high)
        .base_mul(HALF)
        .add(low.sub(high).mul(challenge).base_mul(twiddle))
}

fn ext6_level_twiddle(log_n: u32, index: usize) -> u64 {
    bmul(HALF, bpow(binv(two_adic_generator(log_n)), index as u64))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::babybear::bmul;

    fn e(value: u64) -> Ext6 {
        Ext6::try_from_base(value).unwrap()
    }

    fn gf64(value: u64) -> TowerElem {
        TowerElem::new(MAX_LEVEL, value).unwrap()
    }

    #[test]
    fn generic_mobius_mle_and_dot_are_exact() {
        let table = [e(2), e(5), e(11), e(19)];
        let coefficients = boolean_mobius_coefficients(&table).unwrap();
        assert_eq!(coefficients, vec![e(2), e(3), e(9), e(5)]);

        let point = [e(7), e(13)];
        let once = fold_mle_table(&table, point[0]).unwrap();
        assert_eq!(
            evaluate_mle(&table, &point).unwrap(),
            fold_mle_table(&once, point[1]).unwrap()[0]
        );

        let weights = [e(3), e(7), e(13), e(17)];
        let expected = table
            .iter()
            .copied()
            .zip(weights)
            .fold(Ext6::ZERO, |sum, (value, weight)| {
                sum.add(value.mul(weight))
            });
        assert_eq!(
            linear_functional_dot(&table, &weights, Ext6::ZERO).unwrap(),
            expected
        );
    }

    #[test]
    fn gf64_reversed_lch_fold_matches_bound_coefficients() {
        let table = [gf64(3), gf64(5), gf64(11), gf64(29)];
        let coefficients = boolean_mobius_coefficients(&table).unwrap();
        let basis = [gf64(1), gf64(2)];
        let offset = gf64(0);
        let challenge = gf64(17);
        let word = reversed_lch_encode_gf64(&coefficients, &basis, offset).unwrap();
        let (folded, next_basis, next_offset) =
            fold_reversed_lch_round_gf64(&word, &basis, offset, challenge).unwrap();
        let bound = fold_mle_coefficients(&coefficients, challenge).unwrap();
        assert_eq!(
            folded,
            reversed_lch_encode_gf64(&bound, &next_basis, next_offset).unwrap()
        );
    }

    #[test]
    fn tower256_reversed_lch_fold_matches_bound_coefficients() {
        let t = |value| Tower256::from_limbs([value, 0, 0, 0]);
        let table = [t(3), t(5), t(11), t(29)];
        let coefficients = boolean_mobius_coefficients(&table).unwrap();
        let basis = [t(1), t(2)];
        let challenge = t(17);
        let word = reversed_lch_encode_tower256(&coefficients, &basis, Tower256::ZERO).unwrap();
        let (folded, next_basis, next_offset) =
            fold_reversed_lch_round_tower256(&word, &basis, Tower256::ZERO, challenge).unwrap();
        let bound = fold_mle_coefficients(&coefficients, challenge).unwrap();
        assert_eq!(
            folded,
            reversed_lch_encode_tower256(&bound, &next_basis, next_offset).unwrap()
        );
    }

    fn evaluate_ext6_word(coefficients: &[Ext6], log_domain: u32) -> Vec<Ext6> {
        let generator = two_adic_generator(log_domain);
        let mut point = 1;
        let mut word = Vec::with_capacity(1usize << log_domain);
        for _ in 0..1usize << log_domain {
            word.push(
                coefficients
                    .iter()
                    .rev()
                    .fold(Ext6::ZERO, |acc, &coefficient| {
                        acc.base_mul(point).add(coefficient)
                    }),
            );
            point = bmul(point, generator);
        }
        word
    }

    #[test]
    fn ext6_word_fold_matches_coefficient_binding() {
        let coefficients = [e(2), e(3), e(5), e(7)];
        let challenge = e(11);
        let word = evaluate_ext6_word(&coefficients, 2);
        let bound = fold_ext6_coefficients(&coefficients, challenge).unwrap();
        assert_eq!(
            fold_ext6_multiplicative_word(&word, challenge).unwrap(),
            evaluate_ext6_word(&bound, 1)
        );
    }
}
