//! Generic native arithmetic over caller-supplied `Tower256` buffers.
//!
//! This module owns no proof-system statement, relation polynomial, transcript,
//! round schedule, proof carrier, verifier, or acceptance predicate. It exposes
//! only fallible scatter, vector, multilinear-evaluation, and rational-pair
//! reduction operations. Lean-owned generated control must choose every buffer,
//! index, coordinate, and operation before treating the returned values as
//! candidates for Lean checking.

use core::fmt;

use crate::binary_tower_256::{Tower256, Tower256Error};

/// Arithmetic-shape failures at the generic `Tower256` buffer boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tower256KernelError {
    InvalidLength {
        role: &'static str,
        len: usize,
    },
    LengthMismatch {
        left: usize,
        right: usize,
    },
    AddressOutOfRange {
        row: usize,
        address: usize,
        table_count: usize,
    },
    BufferIndexOutOfRange {
        item: usize,
        index: usize,
        buffer_len: usize,
    },
    SizeOverflow,
    PointLength {
        expected: usize,
        actual: usize,
    },
    Tower(Tower256Error),
}

impl fmt::Display for Tower256KernelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidLength { role, len } => {
                write!(f, "{role} has unsupported arithmetic length {len}")
            }
            Self::LengthMismatch { left, right } => {
                write!(f, "arithmetic vector lengths differ: {left} and {right}")
            }
            Self::AddressOutOfRange {
                row,
                address,
                table_count,
            } => write!(
                f,
                "row {row} has address {address}, outside table length {table_count}"
            ),
            Self::BufferIndexOutOfRange {
                item,
                index,
                buffer_len,
            } => write!(
                f,
                "item {item} targets buffer index {index}, outside length {buffer_len}"
            ),
            Self::SizeOverflow => write!(f, "arithmetic vector size overflows usize"),
            Self::PointLength { expected, actual } => {
                write!(f, "point has length {actual}, expected {expected}")
            }
            Self::Tower(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for Tower256KernelError {}

impl From<Tower256Error> for Tower256KernelError {
    fn from(value: Tower256Error) -> Self {
        Self::Tower(value)
    }
}

/// Scatter unit values to exact caller-supplied output positions.
pub fn unit_scatter(
    positions: &[usize],
    output_len: usize,
) -> Result<Vec<Tower256>, Tower256KernelError> {
    let mut output = vec![Tower256::ZERO; output_len];
    for (item, &index) in positions.iter().enumerate() {
        let Some(slot) = output.get_mut(index) else {
            return Err(Tower256KernelError::BufferIndexOutOfRange {
                item,
                index,
                buffer_len: output_len,
            });
        };
        *slot = Tower256::ONE;
    }
    Ok(output)
}

/// Scatter one weight per row into address-indexed table slots.
///
/// Repeated addresses are accumulated with characteristic-two addition.
pub fn scatter_weights(
    addresses: &[usize],
    weights: &[Tower256],
    table_count: usize,
) -> Result<Vec<Tower256>, Tower256KernelError> {
    if addresses.len() != weights.len() {
        return Err(Tower256KernelError::LengthMismatch {
            left: addresses.len(),
            right: weights.len(),
        });
    }
    let mut output = vec![Tower256::ZERO; table_count];
    for (row, (&address, &weight)) in addresses.iter().zip(weights).enumerate() {
        let Some(slot) = output.get_mut(address) else {
            return Err(Tower256KernelError::AddressOutOfRange {
                row,
                address,
                table_count,
            });
        };
        *slot = slot.add(weight);
    }
    Ok(output)
}

/// Dot product over `GF(2^256)`.
pub fn dot_product(left: &[Tower256], right: &[Tower256]) -> Result<Tower256, Tower256KernelError> {
    if left.len() != right.len() {
        return Err(Tower256KernelError::LengthMismatch {
            left: left.len(),
            right: right.len(),
        });
    }
    Ok(left
        .iter()
        .zip(right)
        .fold(Tower256::ZERO, |sum, (&a, &b)| sum.add(a.mul(b))))
}

/// All LSB-indexed multilinear equality weights at `point`.
///
/// For Boolean index `i`, the result is
/// `product_bit (i_bit ? point_bit : 1 + point_bit)`.
pub fn equality_weights(point: &[Tower256]) -> Result<Vec<Tower256>, Tower256KernelError> {
    let shift = u32::try_from(point.len()).map_err(|_| Tower256KernelError::SizeOverflow)?;
    let len = 1usize
        .checked_shl(shift)
        .ok_or(Tower256KernelError::SizeOverflow)?;
    let mut weights = Vec::with_capacity(len);
    weights.push(Tower256::ONE);
    for &coordinate in point {
        let complement = Tower256::ONE.add(coordinate);
        let half = weights.len();
        weights.resize(2 * half, Tower256::ZERO);
        for index in (0..half).rev() {
            let prefix = weights[index];
            weights[half + index] = prefix.mul(coordinate);
            weights[index] = prefix.mul(complement);
        }
    }
    Ok(weights)
}

/// `eq(left, right) = product_i (1 + left_i + right_i)`.
pub fn equality_weight(
    left: &[Tower256],
    right: &[Tower256],
) -> Result<Tower256, Tower256KernelError> {
    if left.len() != right.len() {
        return Err(Tower256KernelError::LengthMismatch {
            left: left.len(),
            right: right.len(),
        });
    }
    Ok(left
        .iter()
        .zip(right)
        .fold(Tower256::ONE, |product, (&a, &b)| {
            product.mul(Tower256::ONE.add(a).add(b))
        }))
}

/// Evaluate the affine line through `left` at zero and `right` at one.
#[inline]
pub fn affine(left: Tower256, right: Tower256, point: Tower256) -> Tower256 {
    left.add(left.add(right).mul(point))
}

/// Bind the lowest remaining variable of a power-of-two evaluation layer.
pub fn bind_affine_layer(
    layer: &[Tower256],
    challenge: Tower256,
) -> Result<Vec<Tower256>, Tower256KernelError> {
    if layer.len() < 2 || !layer.len().is_power_of_two() {
        return Err(Tower256KernelError::InvalidLength {
            role: "affine layer",
            len: layer.len(),
        });
    }
    Ok(layer
        .chunks_exact(2)
        .map(|pair| affine(pair[0], pair[1], challenge))
        .collect())
}

/// Evaluate a nonconstant multilinear table at caller-supplied coordinates.
pub fn evaluate_mle(
    table: &[Tower256],
    point: &[Tower256],
) -> Result<Tower256, Tower256KernelError> {
    if table.len() < 2 || !table.len().is_power_of_two() {
        return Err(Tower256KernelError::InvalidLength {
            role: "MLE table",
            len: table.len(),
        });
    }
    let expected = table.len().trailing_zeros() as usize;
    if point.len() != expected {
        return Err(Tower256KernelError::PointLength {
            expected,
            actual: point.len(),
        });
    }
    let mut layer = table.to_vec();
    for &challenge in point {
        layer = bind_affine_layer(&layer, challenge)?;
    }
    Ok(layer[0])
}

/// Add one layer of fractions without inversion.
///
/// The input layer is split in halves.  Output entry `i` combines fractions
/// `i` and `half + i`, preserving the coordinate order used by the caller's
/// multilinear layer reduction.
pub fn fraction_add_layer(
    numerators: &[Tower256],
    denominators: &[Tower256],
) -> Result<(Vec<Tower256>, Vec<Tower256>), Tower256KernelError> {
    if numerators.len() != denominators.len() {
        return Err(Tower256KernelError::LengthMismatch {
            left: numerators.len(),
            right: denominators.len(),
        });
    }
    if numerators.len() < 2 || !numerators.len().is_power_of_two() {
        return Err(Tower256KernelError::InvalidLength {
            role: "fraction layer",
            len: numerators.len(),
        });
    }
    let half = numerators.len() / 2;
    let mut next_numerators = Vec::with_capacity(half);
    let mut next_denominators = Vec::with_capacity(half);
    for index in 0..half {
        next_numerators.push(
            numerators[index]
                .mul(denominators[half + index])
                .add(numerators[half + index].mul(denominators[index])),
        );
        next_denominators.push(denominators[index].mul(denominators[half + index]));
    }
    Ok((next_numerators, next_denominators))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn t(value: u64) -> Tower256 {
        Tower256::from_limbs([value, 0, 0, 0])
    }

    #[test]
    fn unit_scatter_uses_exact_caller_positions() {
        let addresses = [2, 0, 2, 3];
        let positions = [8, 1, 10, 15];
        let scattered = unit_scatter(&positions, 16).unwrap();
        for index in 0..16 {
            let expected = if positions.contains(&index) {
                Tower256::ONE
            } else {
                Tower256::ZERO
            };
            assert_eq!(scattered[index], expected);
        }

        let weights = [t(1), t(2), t(4), t(8)];
        assert_eq!(
            scatter_weights(&addresses, &weights, 4).unwrap(),
            vec![t(2), t(0), t(5), t(8)]
        );
    }

    #[test]
    fn fraction_layer_is_cross_multiplied_without_inversion() {
        let (numerators, denominators) = fraction_add_layer(&[t(3), t(5)], &[t(7), t(11)]).unwrap();
        assert_eq!(
            [numerators[0], denominators[0]],
            [t(3).mul(t(11)).add(t(5).mul(t(7))), t(7).mul(t(11))],
        );
    }

    #[test]
    fn equality_weight_recurrence_preserves_lsb_address_order() {
        let point = [t(3), t(5), t(7), t(11)];
        let weights = equality_weights(&point).unwrap();
        assert_eq!(weights.len(), 16);
        for (address, &weight) in weights.iter().enumerate() {
            let corner = (0..point.len())
                .map(|bit| {
                    if address & (1usize << bit) == 0 {
                        Tower256::ZERO
                    } else {
                        Tower256::ONE
                    }
                })
                .collect::<Vec<_>>();
            assert_eq!(weight, equality_weight(&corner, &point).unwrap());
        }
    }
}
