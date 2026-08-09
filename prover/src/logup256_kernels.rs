//! Native `Tower256` arithmetic kernels for a LogUp-style experiment.
//!
//! This module has no complete statement, transcript, proof carrier, verifier,
//! or final acceptance predicate. It does, however, author an unverified native
//! relation/profile: incidence-table order, fraction-tree layout, and the
//! quadratic/cubic round probes and message arities below. Addresses, values,
//! batching scalars, and fold challenges are caller supplied. No compiled
//! generated adapter currently pins these conventions or invokes them as a
//! Lean-owned LogUp suite.

use core::fmt;

use crate::binary_tower_256::{Tower256, Tower256Error};

/// Arithmetic-shape failures at the LogUp kernel boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Logup256KernelError {
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
    SizeOverflow,
    PointLength {
        expected: usize,
        actual: usize,
    },
    InterpolationArity {
        actual: usize,
    },
    Tower(Tower256Error),
}

impl fmt::Display for Logup256KernelError {
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
            Self::SizeOverflow => write!(f, "arithmetic vector size overflows usize"),
            Self::PointLength { expected, actual } => {
                write!(f, "point has length {actual}, expected {expected}")
            }
            Self::InterpolationArity { actual } => {
                write!(f, "round interpolation has unsupported arity {actual}")
            }
            Self::Tower(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for Logup256KernelError {}

impl From<Tower256Error> for Logup256KernelError {
    fn from(value: Tower256Error) -> Self {
        Self::Tower(value)
    }
}

/// Flatten `Y(row, address) = [addresses[row] = address]` with the row
/// coordinate varying fastest.
///
/// Entry `(row, address)` is stored at `address * addresses.len() + row`.
pub fn incidence_table(
    addresses: &[usize],
    table_count: usize,
) -> Result<Vec<Tower256>, Logup256KernelError> {
    let len = addresses
        .len()
        .checked_mul(table_count)
        .ok_or(Logup256KernelError::SizeOverflow)?;
    let mut incidence = vec![Tower256::ZERO; len];
    for (row, &address) in addresses.iter().enumerate() {
        if address >= table_count {
            return Err(Logup256KernelError::AddressOutOfRange {
                row,
                address,
                table_count,
            });
        }
        incidence[address * addresses.len() + row] = Tower256::ONE;
    }
    Ok(incidence)
}

/// Scatter one weight per row into address-indexed table slots.
///
/// Repeated addresses are accumulated with characteristic-two addition.
pub fn scatter_weights(
    addresses: &[usize],
    weights: &[Tower256],
    table_count: usize,
) -> Result<Vec<Tower256>, Logup256KernelError> {
    if addresses.len() != weights.len() {
        return Err(Logup256KernelError::LengthMismatch {
            left: addresses.len(),
            right: weights.len(),
        });
    }
    let mut output = vec![Tower256::ZERO; table_count];
    for (row, (&address, &weight)) in addresses.iter().zip(weights).enumerate() {
        let Some(slot) = output.get_mut(address) else {
            return Err(Logup256KernelError::AddressOutOfRange {
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
pub fn dot_product(left: &[Tower256], right: &[Tower256]) -> Result<Tower256, Logup256KernelError> {
    if left.len() != right.len() {
        return Err(Logup256KernelError::LengthMismatch {
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
pub fn equality_weights(point: &[Tower256]) -> Result<Vec<Tower256>, Logup256KernelError> {
    let shift = u32::try_from(point.len()).map_err(|_| Logup256KernelError::SizeOverflow)?;
    let len = 1usize
        .checked_shl(shift)
        .ok_or(Logup256KernelError::SizeOverflow)?;
    let mut weights = Vec::with_capacity(len);
    for index in 0..len {
        let mut value = Tower256::ONE;
        for (bit, &coordinate) in point.iter().enumerate() {
            let factor = if index & (1usize << bit) == 0 {
                Tower256::ONE.add(coordinate)
            } else {
                coordinate
            };
            value = value.mul(factor);
        }
        weights.push(value);
    }
    Ok(weights)
}

/// `eq(left, right) = product_i (1 + left_i + right_i)`.
pub fn equality_weight(
    left: &[Tower256],
    right: &[Tower256],
) -> Result<Tower256, Logup256KernelError> {
    if left.len() != right.len() {
        return Err(Logup256KernelError::LengthMismatch {
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
) -> Result<Vec<Tower256>, Logup256KernelError> {
    if layer.len() < 2 || !layer.len().is_power_of_two() {
        return Err(Logup256KernelError::InvalidLength {
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
) -> Result<Tower256, Logup256KernelError> {
    if table.len() < 2 || !table.len().is_power_of_two() {
        return Err(Logup256KernelError::InvalidLength {
            role: "MLE table",
            len: table.len(),
        });
    }
    let expected = table.len().trailing_zeros() as usize;
    if point.len() != expected {
        return Err(Logup256KernelError::PointLength {
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
) -> Result<(Vec<Tower256>, Vec<Tower256>), Logup256KernelError> {
    if numerators.len() != denominators.len() {
        return Err(Logup256KernelError::LengthMismatch {
            left: numerators.len(),
            right: denominators.len(),
        });
    }
    if numerators.len() < 2 || !numerators.len().is_power_of_two() {
        return Err(Logup256KernelError::InvalidLength {
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

/// Leaf-to-root fraction-addition arithmetic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FractionAddTree256 {
    numerator_layers: Vec<Vec<Tower256>>,
    denominator_layers: Vec<Vec<Tower256>>,
}

impl FractionAddTree256 {
    pub fn new(
        numerators: &[Tower256],
        denominators: &[Tower256],
    ) -> Result<Self, Logup256KernelError> {
        if numerators.len() != denominators.len() {
            return Err(Logup256KernelError::LengthMismatch {
                left: numerators.len(),
                right: denominators.len(),
            });
        }
        if numerators.len() < 2 || !numerators.len().is_power_of_two() {
            return Err(Logup256KernelError::InvalidLength {
                role: "fraction leaves",
                len: numerators.len(),
            });
        }
        let mut numerator_layers = vec![numerators.to_vec()];
        let mut denominator_layers = vec![denominators.to_vec()];
        while numerator_layers.last().expect("leaf layer exists").len() > 1 {
            let (next_numerators, next_denominators) = fraction_add_layer(
                numerator_layers.last().expect("numerator layer exists"),
                denominator_layers.last().expect("denominator layer exists"),
            )?;
            numerator_layers.push(next_numerators);
            denominator_layers.push(next_denominators);
        }
        Ok(Self {
            numerator_layers,
            denominator_layers,
        })
    }

    /// Root numerator and denominator.
    pub fn root(&self) -> [Tower256; 2] {
        [
            self.numerator_layers.last().expect("root layer exists")[0],
            self.denominator_layers.last().expect("root layer exists")[0],
        ]
    }

    /// Number of fraction-addition steps from leaves to root.
    pub fn depth(&self) -> usize {
        self.numerator_layers.len() - 1
    }

    /// Numerator layers ordered leaves first and root last.
    pub fn numerator_layers(&self) -> &[Vec<Tower256>] {
        &self.numerator_layers
    }

    /// Denominator layers ordered leaves first and root last.
    pub fn denominator_layers(&self) -> &[Vec<Tower256>] {
        &self.denominator_layers
    }
}

/// Arithmetic state for one fraction-addition layer's cubic reductions.
///
/// `batching_scalar` in [`Self::round_message`] and every challenge passed to
/// [`Self::bind`] are supplied by the caller.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FractionRoundState256 {
    equality: Vec<Tower256>,
    p0: Vec<Tower256>,
    p1: Vec<Tower256>,
    q0: Vec<Tower256>,
    q1: Vec<Tower256>,
    challenges: Vec<Tower256>,
}

impl FractionRoundState256 {
    pub fn new(
        parent_point: &[Tower256],
        p0: &[Tower256],
        p1: &[Tower256],
        q0: &[Tower256],
        q1: &[Tower256],
    ) -> Result<Self, Logup256KernelError> {
        let len = p0.len();
        for other in [p1.len(), q0.len(), q1.len()] {
            if other != len {
                return Err(Logup256KernelError::LengthMismatch {
                    left: len,
                    right: other,
                });
            }
        }
        if len == 0 || !len.is_power_of_two() {
            return Err(Logup256KernelError::InvalidLength {
                role: "fraction round",
                len,
            });
        }
        let expected = len.trailing_zeros() as usize;
        if parent_point.len() != expected {
            return Err(Logup256KernelError::PointLength {
                expected,
                actual: parent_point.len(),
            });
        }
        Ok(Self {
            equality: equality_weights(parent_point)?,
            p0: p0.to_vec(),
            p1: p1.to_vec(),
            q0: q0.to_vec(),
            q1: q1.to_vec(),
            challenges: Vec::with_capacity(parent_point.len()),
        })
    }

    /// Four evaluations of the current cubic round at [`cubic_probes`].
    pub fn round_message(
        &self,
        batching_scalar: Tower256,
    ) -> Result<[Tower256; 4], Logup256KernelError> {
        if self.equality.len() < 2 {
            return Err(Logup256KernelError::InvalidLength {
                role: "fraction round",
                len: self.equality.len(),
            });
        }
        let probes = cubic_probes();
        let mut message = [Tower256::ZERO; 4];
        for index in 0..(self.equality.len() / 2) {
            for (slot, &probe) in message.iter_mut().zip(&probes) {
                let equality = affine(
                    self.equality[2 * index],
                    self.equality[2 * index + 1],
                    probe,
                );
                let p0 = affine(self.p0[2 * index], self.p0[2 * index + 1], probe);
                let p1 = affine(self.p1[2 * index], self.p1[2 * index + 1], probe);
                let q0 = affine(self.q0[2 * index], self.q0[2 * index + 1], probe);
                let q1 = affine(self.q1[2 * index], self.q1[2 * index + 1], probe);
                let numerator = p0.mul(q1).add(p1.mul(q0));
                let denominator = q0.mul(q1);
                *slot = slot.add(equality.mul(numerator.add(batching_scalar.mul(denominator))));
            }
        }
        Ok(message)
    }

    /// Bind one caller-supplied challenge in every current arithmetic layer.
    pub fn bind(&mut self, challenge: Tower256) -> Result<(), Logup256KernelError> {
        self.equality = bind_affine_layer(&self.equality, challenge)?;
        self.p0 = bind_affine_layer(&self.p0, challenge)?;
        self.p1 = bind_affine_layer(&self.p1, challenge)?;
        self.q0 = bind_affine_layer(&self.q0, challenge)?;
        self.q1 = bind_affine_layer(&self.q1, challenge)?;
        self.challenges.push(challenge);
        Ok(())
    }

    /// Caller-supplied challenges bound so far, in binding order.
    pub fn challenges(&self) -> &[Tower256] {
        &self.challenges
    }

    /// `[p0, p1, q0, q1]` after all variables have been bound.
    pub fn terminal(&self) -> Result<[Tower256; 4], Logup256KernelError> {
        for len in [
            self.equality.len(),
            self.p0.len(),
            self.p1.len(),
            self.q0.len(),
            self.q1.len(),
        ] {
            if len != 1 {
                return Err(Logup256KernelError::InvalidLength {
                    role: "fraction terminal",
                    len,
                });
            }
        }
        Ok([self.p0[0], self.p1[0], self.q0[0], self.q1[0]])
    }
}

/// Four evaluations of `sum eq * value * (value + 1)` at
/// [`cubic_probes`].
pub fn index_booleanity_round_message(
    equality: &[Tower256],
    values: &[Tower256],
) -> Result<[Tower256; 4], Logup256KernelError> {
    if equality.len() != values.len() {
        return Err(Logup256KernelError::LengthMismatch {
            left: equality.len(),
            right: values.len(),
        });
    }
    if equality.len() < 2 || !equality.len().is_power_of_two() {
        return Err(Logup256KernelError::InvalidLength {
            role: "Booleanity round",
            len: equality.len(),
        });
    }
    let probes = cubic_probes();
    let mut message = [Tower256::ZERO; 4];
    for index in 0..(equality.len() / 2) {
        for (slot, &probe) in message.iter_mut().zip(&probes) {
            let eq_value = affine(equality[2 * index], equality[2 * index + 1], probe);
            let value = affine(values[2 * index], values[2 * index + 1], probe);
            *slot = slot.add(eq_value.mul(value).mul(value.add(Tower256::ONE)));
        }
    }
    Ok(message)
}

/// Three evaluations of `sum left * right` at [`quadratic_probes`].
pub fn quadratic_product_round_message(
    left: &[Tower256],
    right: &[Tower256],
) -> Result<[Tower256; 3], Logup256KernelError> {
    if left.len() != right.len() {
        return Err(Logup256KernelError::LengthMismatch {
            left: left.len(),
            right: right.len(),
        });
    }
    if left.len() < 2 || !left.len().is_power_of_two() {
        return Err(Logup256KernelError::InvalidLength {
            role: "quadratic round",
            len: left.len(),
        });
    }
    let probes = quadratic_probes();
    let mut message = [Tower256::ZERO; 3];
    for index in 0..(left.len() / 2) {
        for (slot, &probe) in message.iter_mut().zip(&probes) {
            let left_value = affine(left[2 * index], left[2 * index + 1], probe);
            let right_value = affine(right[2 * index], right[2 * index + 1], probe);
            *slot = slot.add(left_value.mul(right_value));
        }
    }
    Ok(message)
}

/// Distinct quadratic-round probes `0, 1, theta`.
pub const fn quadratic_probes() -> [Tower256; 3] {
    [
        Tower256::ZERO,
        Tower256::ONE,
        Tower256::from_limbs([2, 0, 0, 0]),
    ]
}

/// Distinct cubic-round probes `0, 1, theta, 1 + theta`.
pub const fn cubic_probes() -> [Tower256; 4] {
    [
        Tower256::ZERO,
        Tower256::ONE,
        Tower256::from_limbs([2, 0, 0, 0]),
        Tower256::from_limbs([3, 0, 0, 0]),
    ]
}

/// Evaluate a quadratic or cubic round interpolant at a caller-supplied point.
pub fn interpolate_round(
    samples: &[Tower256],
    point: Tower256,
) -> Result<Tower256, Logup256KernelError> {
    let probes: &[Tower256] = match samples.len() {
        3 => &quadratic_probes(),
        4 => &cubic_probes(),
        actual => return Err(Logup256KernelError::InterpolationArity { actual }),
    };
    let mut value = Tower256::ZERO;
    for i in 0..samples.len() {
        let mut numerator = Tower256::ONE;
        let mut denominator = Tower256::ONE;
        for j in 0..samples.len() {
            if i != j {
                // Addition is subtraction in characteristic two.
                numerator = numerator.mul(point.add(probes[j]));
                denominator = denominator.mul(probes[i].add(probes[j]));
            }
        }
        value = value.add(samples[i].mul(numerator.div(denominator)?));
    }
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn t(value: u64) -> Tower256 {
        Tower256::from_limbs([value, 0, 0, 0])
    }

    #[test]
    fn incidence_and_weight_scatter_share_the_address_axis() {
        let addresses = [2, 0, 2, 3];
        let incidence = incidence_table(&addresses, 4).unwrap();
        for address in 0..4 {
            for row in 0..4 {
                let expected = if addresses[row] == address {
                    Tower256::ONE
                } else {
                    Tower256::ZERO
                };
                assert_eq!(incidence[address * 4 + row], expected);
            }
        }

        let weights = [t(1), t(2), t(4), t(8)];
        assert_eq!(
            scatter_weights(&addresses, &weights, 4).unwrap(),
            vec![t(2), t(0), t(5), t(8)]
        );
    }

    #[test]
    fn fraction_tree_root_is_cross_multiplied_without_inversion() {
        let tree = FractionAddTree256::new(&[t(3), t(5)], &[t(7), t(11)]).unwrap();
        assert_eq!(
            tree.root(),
            [t(3).mul(t(11)).add(t(5).mul(t(7))), t(7).mul(t(11))]
        );
        assert_eq!(tree.depth(), 1);
    }

    #[test]
    fn quadratic_message_interpolates_to_the_bound_dot_product() {
        let left = [t(1), t(2), t(4), t(8)];
        let right = [t(3), t(5), t(7), t(11)];
        let message = quadratic_product_round_message(&left, &right).unwrap();
        assert_eq!(
            message[0].add(message[1]),
            dot_product(&left, &right).unwrap()
        );

        let challenge = t(13);
        let folded_left = bind_affine_layer(&left, challenge).unwrap();
        let folded_right = bind_affine_layer(&right, challenge).unwrap();
        assert_eq!(
            interpolate_round(&message, challenge).unwrap(),
            dot_product(&folded_left, &folded_right).unwrap()
        );
    }

    #[test]
    fn fraction_round_endpoints_sum_to_the_unbound_layer() {
        let parent_point = [t(9), t(12)];
        let equality = equality_weights(&parent_point).unwrap();
        let p0 = [t(1), t(2), t(3), t(4)];
        let p1 = [t(5), t(6), t(7), t(8)];
        let q0 = [t(9), t(10), t(11), t(12)];
        let q1 = [t(13), t(14), t(15), t(16)];
        let batching_scalar = t(17);
        let state = FractionRoundState256::new(&parent_point, &p0, &p1, &q0, &q1).unwrap();
        let message = state.round_message(batching_scalar).unwrap();

        let expected = (0..4).fold(Tower256::ZERO, |sum, index| {
            let numerator = p0[index].mul(q1[index]).add(p1[index].mul(q0[index]));
            let denominator = q0[index].mul(q1[index]);
            sum.add(equality[index].mul(numerator.add(batching_scalar.mul(denominator))))
        });
        assert_eq!(message[0].add(message[1]), expected);
    }
}
