//! Low-level arithmetic kernels over caller-supplied buffers.
//!
//! This module produces arithmetic messages only.  Every challenge and table is
//! explicit caller data.  Failures are limited to unusable moduli,
//! non-canonical representatives, and arithmetic buffer shape.

use core::fmt;

use crate::field6::Ext6;

/// Seven operand tables for the factored degree-two gate polynomial.
pub const GATE_OPERAND_TABLES: usize = 7;
pub const MUL_LEFT_WEIGHTED: usize = 0;
pub const MUL_RIGHT: usize = 1;
pub const MUL_OUTPUT_WEIGHTED: usize = 2;
pub const ADD_LEFT_WEIGHTED: usize = 3;
pub const ADD_RIGHT_WEIGHTED: usize = 4;
pub const ADD_OUTPUT_WEIGHTED: usize = 5;
pub const ZERO_WEIGHTED: usize = 6;

pub type GateOperandValues<E> = [E; GATE_OPERAND_TABLES];
pub type GateOperandTables<E> = [Vec<E>; GATE_OPERAND_TABLES];

/// The buffer in which a non-canonical base-field representative occurred.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BufferKind {
    Residual,
    Challenge,
    Table,
    Point,
}

/// Arithmetic-kernel input and execution failures.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GateKernelError {
    InvalidModulus {
        modulus: u64,
    },
    EmptyTable,
    NonPowerOfTwo {
        len: usize,
    },
    PointDimension {
        expected: usize,
        actual: usize,
    },
    NonCanonical {
        buffer: BufferKind,
        index: usize,
        value: u64,
        modulus: u64,
    },
    NonCanonicalBase {
        index: usize,
        value: u64,
    },
    OperandTableLength {
        table: usize,
        expected: usize,
        actual: usize,
    },
    NoRoundRemaining,
    NotTerminal {
        remaining: usize,
    },
}

impl fmt::Display for GateKernelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidModulus { modulus } => {
                write!(f, "arithmetic modulus {modulus} must be at least two")
            }
            Self::EmptyTable => write!(f, "multilinear table is empty"),
            Self::NonPowerOfTwo { len } => {
                write!(f, "multilinear table length {len} is not a power of two")
            }
            Self::PointDimension { expected, actual } => {
                write!(f, "point has dimension {actual}, expected {expected}")
            }
            Self::NonCanonical {
                buffer,
                index,
                value,
                modulus,
            } => write!(
                f,
                "non-canonical {buffer:?}[{index}] = {value} for modulus {modulus}"
            ),
            Self::NonCanonicalBase { index, value } => {
                write!(f, "base embedding rejected residual[{index}] = {value}")
            }
            Self::OperandTableLength {
                table,
                expected,
                actual,
            } => write!(
                f,
                "gate operand table {table} has length {actual}, expected {expected}"
            ),
            Self::NoRoundRemaining => write!(f, "sumcheck layer is already terminal"),
            Self::NotTerminal { remaining } => {
                write!(f, "sumcheck layer has {remaining} terminal candidates")
            }
        }
    }
}

impl std::error::Error for GateKernelError {}

fn check_modulus(modulus: u64) -> Result<(), GateKernelError> {
    if modulus < 2 {
        Err(GateKernelError::InvalidModulus { modulus })
    } else {
        Ok(())
    }
}

fn check_canonical(
    values: &[u64],
    modulus: u64,
    buffer: BufferKind,
) -> Result<(), GateKernelError> {
    if let Some((index, &value)) = values
        .iter()
        .enumerate()
        .find(|(_, value)| **value >= modulus)
    {
        Err(GateKernelError::NonCanonical {
            buffer,
            index,
            value,
            modulus,
        })
    } else {
        Ok(())
    }
}

#[inline]
fn add_mod_unchecked(a: u64, b: u64, modulus: u64) -> u64 {
    ((a as u128 + b as u128) % modulus as u128) as u64
}

#[inline]
fn sub_mod_unchecked(a: u64, b: u64, modulus: u64) -> u64 {
    ((a as u128 + modulus as u128 - b as u128) % modulus as u128) as u64
}

#[inline]
fn mul_mod_unchecked(a: u64, b: u64, modulus: u64) -> u64 {
    ((a as u128 * b as u128) % modulus as u128) as u64
}

/// Canonical modular addition.
pub fn add_mod(a: u64, b: u64, modulus: u64) -> Result<u64, GateKernelError> {
    check_modulus(modulus)?;
    check_canonical(&[a, b], modulus, BufferKind::Table)?;
    Ok(add_mod_unchecked(a, b, modulus))
}

/// Canonical modular subtraction.
pub fn sub_mod(a: u64, b: u64, modulus: u64) -> Result<u64, GateKernelError> {
    check_modulus(modulus)?;
    check_canonical(&[a, b], modulus, BufferKind::Table)?;
    Ok(sub_mod_unchecked(a, b, modulus))
}

/// Canonical modular multiplication.
pub fn mul_mod(a: u64, b: u64, modulus: u64) -> Result<u64, GateKernelError> {
    check_modulus(modulus)?;
    check_canonical(&[a, b], modulus, BufferKind::Table)?;
    Ok(mul_mod_unchecked(a, b, modulus))
}

/// Weight canonical base-field residual `k` by `gamma^k`.
pub fn batch_base_residuals(
    residuals: &[u64],
    gamma: u64,
    modulus: u64,
) -> Result<Vec<u64>, GateKernelError> {
    check_modulus(modulus)?;
    check_canonical(residuals, modulus, BufferKind::Residual)?;
    check_canonical(&[gamma], modulus, BufferKind::Challenge)?;
    let mut power = 1 % modulus;
    let mut out = Vec::with_capacity(residuals.len());
    for &residual in residuals {
        out.push(mul_mod_unchecked(power, residual, modulus));
        power = mul_mod_unchecked(power, gamma, modulus);
    }
    Ok(out)
}

// --- Base-field table and MLE kernels --------------------------------------

/// Cube dimension for a nonempty power-of-two table buffer.
pub fn cube_dim(len: usize) -> Result<usize, GateKernelError> {
    if len == 0 {
        Err(GateKernelError::EmptyTable)
    } else if !len.is_power_of_two() {
        Err(GateKernelError::NonPowerOfTwo { len })
    } else {
        Ok(len.trailing_zeros() as usize)
    }
}

/// Sum a canonical base-field table.
pub fn base_table_sum(table: &[u64], modulus: u64) -> Result<u64, GateKernelError> {
    check_modulus(modulus)?;
    cube_dim(table.len())?;
    check_canonical(table, modulus, BufferKind::Table)?;
    Ok(table
        .iter()
        .fold(0, |sum, &value| add_mod_unchecked(sum, value, modulus)))
}

/// `chi_b(point)` with LSB-first coordinate numbering.
pub fn base_chi_eval(corner: usize, point: &[u64], modulus: u64) -> Result<u64, GateKernelError> {
    check_modulus(modulus)?;
    check_canonical(point, modulus, BufferKind::Point)?;
    Ok(point
        .iter()
        .enumerate()
        .fold(1 % modulus, |product, (i, &x)| {
            let factor = if (corner >> i) & 1 == 1 {
                x
            } else {
                sub_mod_unchecked(1 % modulus, x, modulus)
            };
            mul_mod_unchecked(product, factor, modulus)
        }))
}

fn base_fold_layer_unchecked(layer: &[u64], challenge: u64, modulus: u64) -> Vec<u64> {
    layer
        .chunks_exact(2)
        .map(|pair| {
            add_mod_unchecked(
                pair[0],
                mul_mod_unchecked(
                    sub_mod_unchecked(pair[1], pair[0], modulus),
                    challenge,
                    modulus,
                ),
                modulus,
            )
        })
        .collect()
}

/// Fold one LSB-first multilinear layer at a caller-supplied challenge.
pub fn base_fold_layer(
    layer: &[u64],
    challenge: u64,
    modulus: u64,
) -> Result<Vec<u64>, GateKernelError> {
    check_modulus(modulus)?;
    let rounds = cube_dim(layer.len())?;
    if rounds == 0 {
        return Err(GateKernelError::NoRoundRemaining);
    }
    check_canonical(layer, modulus, BufferKind::Table)?;
    check_canonical(&[challenge], modulus, BufferKind::Challenge)?;
    Ok(base_fold_layer_unchecked(layer, challenge, modulus))
}

/// The next affine sumcheck message `[g(0), g(1)]` from a current layer.
pub fn base_affine_round_message(layer: &[u64], modulus: u64) -> Result<[u64; 2], GateKernelError> {
    check_modulus(modulus)?;
    let rounds = cube_dim(layer.len())?;
    if rounds == 0 {
        return Err(GateKernelError::NoRoundRemaining);
    }
    check_canonical(layer, modulus, BufferKind::Table)?;
    let mut message = [0, 0];
    for (index, &value) in layer.iter().enumerate() {
        message[index & 1] = add_mod_unchecked(message[index & 1], value, modulus);
    }
    Ok(message)
}

/// Evaluate `[g(0),g(1)]` at a caller-supplied challenge.
pub fn base_evaluate_affine(
    message: [u64; 2],
    challenge: u64,
    modulus: u64,
) -> Result<u64, GateKernelError> {
    check_modulus(modulus)?;
    check_canonical(&message, modulus, BufferKind::Table)?;
    check_canonical(&[challenge], modulus, BufferKind::Challenge)?;
    Ok(add_mod_unchecked(
        message[0],
        mul_mod_unchecked(
            sub_mod_unchecked(message[1], message[0], modulus),
            challenge,
            modulus,
        ),
        modulus,
    ))
}

/// Return the affine message after folding every supplied prior challenge.
pub fn base_streaming_round_message(
    table: &[u64],
    prior_challenges: &[u64],
    modulus: u64,
) -> Result<[u64; 2], GateKernelError> {
    check_modulus(modulus)?;
    let dimension = cube_dim(table.len())?;
    if prior_challenges.len() >= dimension {
        return Err(GateKernelError::NoRoundRemaining);
    }
    check_canonical(table, modulus, BufferKind::Table)?;
    check_canonical(prior_challenges, modulus, BufferKind::Challenge)?;
    let mut layer = table.to_vec();
    for &challenge in prior_challenges {
        layer = base_fold_layer_unchecked(&layer, challenge, modulus);
    }
    base_affine_round_message(&layer, modulus)
}

/// Evaluate a base-field table's MLE by folding adjacent LSB-first pairs.
pub fn base_evaluate_mle(
    table: &[u64],
    point: &[u64],
    modulus: u64,
) -> Result<u64, GateKernelError> {
    check_modulus(modulus)?;
    let dimension = cube_dim(table.len())?;
    if point.len() != dimension {
        return Err(GateKernelError::PointDimension {
            expected: dimension,
            actual: point.len(),
        });
    }
    check_canonical(table, modulus, BufferKind::Table)?;
    check_canonical(point, modulus, BufferKind::Point)?;
    let mut layer = table.to_vec();
    for &challenge in point {
        layer = base_fold_layer_unchecked(&layer, challenge, modulus);
    }
    Ok(layer[0])
}

// --- Field-generic streaming kernels ---------------------------------------

/// Ring operations needed by multilinear and degree-two sumcheck arithmetic.
/// Inversion is not required; the caller supplies the inverse of two when it
/// requests degree-two interpolation.
pub trait KernelScalar: Copy + Eq + fmt::Debug {
    const ZERO: Self;
    const ONE: Self;

    fn add(self, rhs: Self) -> Self;
    fn sub(self, rhs: Self) -> Self;
    fn mul(self, rhs: Self) -> Self;
}

/// Canonical embedding of a base-field representative into a kernel scalar.
pub trait BaseEmbedding: KernelScalar {
    fn try_from_base(value: u64) -> Option<Self>;
}

impl KernelScalar for Ext6 {
    const ZERO: Self = Ext6::ZERO;
    const ONE: Self = Ext6::ONE;

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

impl BaseEmbedding for Ext6 {
    fn try_from_base(value: u64) -> Option<Self> {
        Ext6::try_from_base(value).ok()
    }
}

fn scalar_sum<E: KernelScalar>(values: impl IntoIterator<Item = E>) -> E {
    values
        .into_iter()
        .fold(E::ZERO, |sum, value| sum.add(value))
}

/// Sum one field-generic Boolean table.
pub fn table_sum<E: KernelScalar>(table: &[E]) -> Result<E, GateKernelError> {
    cube_dim(table.len())?;
    Ok(scalar_sum(table.iter().copied()))
}

fn fold_layer_unchecked<E: KernelScalar>(layer: &[E], challenge: E) -> Vec<E> {
    layer
        .chunks_exact(2)
        .map(|pair| pair[0].add(pair[1].sub(pair[0]).mul(challenge)))
        .collect()
}

/// Fold one generic LSB-first multilinear layer at a caller challenge.
pub fn fold_layer<E: KernelScalar>(layer: &[E], challenge: E) -> Result<Vec<E>, GateKernelError> {
    let rounds = cube_dim(layer.len())?;
    if rounds == 0 {
        return Err(GateKernelError::NoRoundRemaining);
    }
    Ok(fold_layer_unchecked(layer, challenge))
}

/// The next generic affine message `[g(0),g(1)]`.
pub fn affine_round_message<E: KernelScalar>(layer: &[E]) -> Result<[E; 2], GateKernelError> {
    let rounds = cube_dim(layer.len())?;
    if rounds == 0 {
        return Err(GateKernelError::NoRoundRemaining);
    }
    Ok([
        scalar_sum(layer.iter().step_by(2).copied()),
        scalar_sum(layer.iter().skip(1).step_by(2).copied()),
    ])
}

/// Evaluate an affine message at a caller challenge.
pub fn evaluate_affine<E: KernelScalar>(message: [E; 2], challenge: E) -> E {
    message[0].add(message[1].sub(message[0]).mul(challenge))
}

/// Return the affine message after binding each supplied prior challenge.
pub fn streaming_round_message<E: KernelScalar>(
    table: &[E],
    prior_challenges: &[E],
) -> Result<[E; 2], GateKernelError> {
    let dimension = cube_dim(table.len())?;
    if prior_challenges.len() >= dimension {
        return Err(GateKernelError::NoRoundRemaining);
    }
    let mut layer = table.to_vec();
    for &challenge in prior_challenges {
        layer = fold_layer_unchecked(&layer, challenge);
    }
    affine_round_message(&layer)
}

/// Evaluate a field-generic table's MLE by an explicit challenge fold schedule.
pub fn evaluate_mle<E: KernelScalar>(table: &[E], point: &[E]) -> Result<E, GateKernelError> {
    let dimension = cube_dim(table.len())?;
    if point.len() != dimension {
        return Err(GateKernelError::PointDimension {
            expected: dimension,
            actual: point.len(),
        });
    }
    let mut layer = table.to_vec();
    for &challenge in point {
        layer = fold_layer_unchecked(&layer, challenge);
    }
    Ok(layer[0])
}

/// Lift canonical base residuals and weight entry `k` by `gamma^k`.
pub fn batch_lifted_residuals<E: BaseEmbedding>(
    residuals: &[u64],
    gamma: E,
) -> Result<Vec<E>, GateKernelError> {
    let mut power = E::ONE;
    let mut out = Vec::with_capacity(residuals.len());
    for (index, &residual) in residuals.iter().enumerate() {
        let lifted = E::try_from_base(residual).ok_or(GateKernelError::NonCanonicalBase {
            index,
            value: residual,
        })?;
        out.push(power.mul(lifted));
        power = power.mul(gamma);
    }
    Ok(out)
}

// --- Degree-two factored-gate kernels --------------------------------------

fn check_operand_tables<E>(tables: &GateOperandTables<E>) -> Result<usize, GateKernelError> {
    let len = tables[MUL_LEFT_WEIGHTED].len();
    cube_dim(len)?;
    for (table, values) in tables.iter().enumerate().skip(1) {
        if values.len() != len {
            return Err(GateKernelError::OperandTableLength {
                table,
                expected: len,
                actual: values.len(),
            });
        }
    }
    Ok(len)
}

/// `(gamma*A)*B - gamma*C + gamma*(L+R-O) + gamma*Z` at one point.
pub fn gate_polynomial_value<E: KernelScalar>(values: GateOperandValues<E>) -> E {
    values[MUL_LEFT_WEIGHTED]
        .mul(values[MUL_RIGHT])
        .sub(values[MUL_OUTPUT_WEIGHTED])
        .add(values[ADD_LEFT_WEIGHTED])
        .add(values[ADD_RIGHT_WEIGHTED])
        .sub(values[ADD_OUTPUT_WEIGHTED])
        .add(values[ZERO_WEIGHTED])
}

fn interpolate<E: KernelScalar>(low: E, high: E, at: E) -> E {
    low.add(high.sub(low).mul(at))
}

fn gate_round_value<E: KernelScalar>(tables: &GateOperandTables<E>, at: E) -> E {
    let mut sum = E::ZERO;
    for pair in 0..tables[0].len() / 2 {
        let low = 2 * pair;
        let high = low + 1;
        let values =
            core::array::from_fn(|table| interpolate(tables[table][low], tables[table][high], at));
        sum = sum.add(gate_polynomial_value(values));
    }
    sum
}

/// Sum the factored degree-two gate polynomial over the current cube.
pub fn quadratic_gate_cube_sum<E: KernelScalar>(
    tables: &GateOperandTables<E>,
) -> Result<E, GateKernelError> {
    let len = check_operand_tables(tables)?;
    Ok((0..len).fold(E::ZERO, |sum, index| {
        let values = core::array::from_fn(|table| tables[table][index]);
        sum.add(gate_polynomial_value(values))
    }))
}

/// Emit `[g(0),g(1),g(2)]` for the factored gate polynomial.  `two` is caller
/// supplied so the kernel does not select a field or encoding.
pub fn quadratic_gate_round_message<E: KernelScalar>(
    tables: &GateOperandTables<E>,
    two: E,
) -> Result<[E; 3], GateKernelError> {
    let len = check_operand_tables(tables)?;
    if len == 1 {
        return Err(GateKernelError::NoRoundRemaining);
    }
    Ok([
        gate_round_value(tables, E::ZERO),
        gate_round_value(tables, E::ONE),
        gate_round_value(tables, two),
    ])
}

/// Fold all seven gate operand buffers at one caller-supplied challenge.
pub fn fold_gate_operand_tables<E: KernelScalar>(
    tables: &GateOperandTables<E>,
    challenge: E,
) -> Result<GateOperandTables<E>, GateKernelError> {
    let len = check_operand_tables(tables)?;
    if len == 1 {
        return Err(GateKernelError::NoRoundRemaining);
    }
    Ok(core::array::from_fn(|table| {
        fold_layer_unchecked(&tables[table], challenge)
    }))
}

/// Read the seven singleton terminal values after all folds.
pub fn gate_operand_terminal<E: Copy>(
    tables: &GateOperandTables<E>,
) -> Result<GateOperandValues<E>, GateKernelError> {
    let len = check_operand_tables(tables)?;
    if len != 1 {
        return Err(GateKernelError::NotTerminal { remaining: len });
    }
    Ok(core::array::from_fn(|table| tables[table][0]))
}

/// Evaluate `[g(0),g(1),g(2)]` at a caller challenge.  The caller also supplies
/// the field element `1/2` explicitly.
pub fn evaluate_quadratic<E: KernelScalar>(message: [E; 3], challenge: E, two_inverse: E) -> E {
    let [g0, g1, g2] = message;
    let linear = g1.sub(g0).mul(challenge);
    let second_difference = g2.sub(g1.add(g1)).add(g0);
    let choose_two = challenge.mul(challenge.sub(E::ONE)).mul(two_inverse);
    g0.add(linear).add(second_difference.mul(choose_two))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field4::{HALF, P};

    fn ext(value: u64) -> Ext6 {
        Ext6::try_from_base(value).unwrap()
    }

    #[test]
    fn affine_streaming_matches_generic_mle() {
        let table: Vec<Ext6> = [3, 1, 4, 1, 5, 9, 2, 6].into_iter().map(ext).collect();
        let point = [ext(17), ext(42), ext(63)];
        let mut layer = table.clone();
        for &challenge in &point {
            let message = affine_round_message(&layer).unwrap();
            layer = fold_layer(&layer, challenge).unwrap();
            assert_eq!(
                evaluate_affine(message, challenge),
                table_sum(&layer).unwrap()
            );
        }
        assert_eq!(layer[0], evaluate_mle(&table, &point).unwrap());
    }

    #[test]
    fn quadratic_message_and_fold_share_the_caller_challenge() {
        let mut tables: GateOperandTables<Ext6> = core::array::from_fn(|_| vec![Ext6::ZERO; 4]);
        tables[MUL_LEFT_WEIGHTED] = vec![ext(1), ext(2), ext(3), ext(4)];
        tables[MUL_RIGHT] = vec![ext(5), ext(6), ext(7), ext(8)];
        tables[ZERO_WEIGHTED] = vec![ext(9), ext(10), ext(11), ext(12)];

        let message = quadratic_gate_round_message(&tables, ext(2)).unwrap();
        let challenge = ext(13);
        let next = fold_gate_operand_tables(&tables, challenge).unwrap();
        assert_eq!(
            evaluate_quadratic(message, challenge, ext(HALF)),
            quadratic_gate_cube_sum(&next).unwrap()
        );
        assert_eq!(P, 2_013_265_921);
    }
}
