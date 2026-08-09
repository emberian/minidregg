//! Field-generic executable mirror of Loom's linear `AccClaim` algebra.
//!
//! Unlike the historical base-field-only `accumulator` module, this carrier is
//! suitable for security-sized extension challenges.  It deliberately owns
//! only the algebra proved in `Loom/Accumulator.lean`: shared linear channels,
//! same-word batching, cross-word folding, and witness-word folding.  Root
//! binding, code membership, proximity, transcript order, and extraction stay
//! with the composing protocol.

use core::fmt;

use crate::sumcheck_generic::SumcheckScalar;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldLinearConstraint<E> {
    pub weights: Vec<E>,
    pub target: E,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldAccClaim<Root, E> {
    pub root: Root,
    pub word_len: usize,
    pub channel: Vec<FieldLinearConstraint<E>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FieldAccError {
    ConstraintWidth {
        row: usize,
        expected: usize,
        actual: usize,
    },
    WordWidth {
        expected: usize,
        actual: usize,
    },
    ChannelLength {
        left: usize,
        right: usize,
    },
    UnsharedWeights {
        row: usize,
    },
}

impl fmt::Display for FieldAccError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ConstraintWidth {
                row,
                expected,
                actual,
            } => write!(
                f,
                "constraint row {row} has width {actual}, expected {expected}"
            ),
            Self::WordWidth { expected, actual } => {
                write!(f, "word has width {actual}, expected {expected}")
            }
            Self::ChannelLength { left, right } => {
                write!(f, "claim channels have lengths {left} and {right}")
            }
            Self::UnsharedWeights { row } => {
                write!(f, "claim channels do not share weights at row {row}")
            }
        }
    }
}

impl std::error::Error for FieldAccError {}

impl<Root, E: SumcheckScalar> FieldAccClaim<Root, E> {
    pub fn validate(&self) -> Result<(), FieldAccError> {
        for (row, constraint) in self.channel.iter().enumerate() {
            if constraint.weights.len() != self.word_len {
                return Err(FieldAccError::ConstraintWidth {
                    row,
                    expected: self.word_len,
                    actual: constraint.weights.len(),
                });
            }
        }
        Ok(())
    }

    pub fn channel_satisfied_by(&self, word: &[E]) -> Result<bool, FieldAccError> {
        self.validate()?;
        if word.len() != self.word_len {
            return Err(FieldAccError::WordWidth {
                expected: self.word_len,
                actual: word.len(),
            });
        }
        Ok(self
            .channel
            .iter()
            .all(|constraint| dot(&constraint.weights, word) == constraint.target))
    }
}

fn dot<E: SumcheckScalar>(weights: &[E], word: &[E]) -> E {
    weights
        .iter()
        .copied()
        .zip(word.iter().copied())
        .fold(E::ZERO, |sum, (weight, value)| sum.add(weight.mul(value)))
}

pub fn batch_claim<Root: Clone, E: SumcheckScalar>(
    claim: &FieldAccClaim<Root, E>,
    gamma: E,
) -> Result<FieldAccClaim<Root, E>, FieldAccError> {
    claim.validate()?;
    let mut weights = vec![E::ZERO; claim.word_len];
    let mut target = E::ZERO;
    let mut power = E::ONE;
    for constraint in &claim.channel {
        for (out, weight) in weights.iter_mut().zip(&constraint.weights) {
            *out = out.add(power.mul(*weight));
        }
        target = target.add(power.mul(constraint.target));
        power = power.mul(gamma);
    }
    Ok(FieldAccClaim {
        root: claim.root.clone(),
        word_len: claim.word_len,
        channel: vec![FieldLinearConstraint { weights, target }],
    })
}

pub fn fold_claims<Root, LeftRoot, RightRoot, E: SumcheckScalar>(
    folded_root: Root,
    left: &FieldAccClaim<LeftRoot, E>,
    right: &FieldAccClaim<RightRoot, E>,
    gamma: E,
) -> Result<FieldAccClaim<Root, E>, FieldAccError> {
    left.validate()?;
    right.validate()?;
    if left.word_len != right.word_len {
        return Err(FieldAccError::WordWidth {
            expected: left.word_len,
            actual: right.word_len,
        });
    }
    if left.channel.len() != right.channel.len() {
        return Err(FieldAccError::ChannelLength {
            left: left.channel.len(),
            right: right.channel.len(),
        });
    }
    let mut channel = Vec::with_capacity(left.channel.len());
    for (row, (left_row, right_row)) in left.channel.iter().zip(&right.channel).enumerate() {
        if left_row.weights != right_row.weights {
            return Err(FieldAccError::UnsharedWeights { row });
        }
        channel.push(FieldLinearConstraint {
            weights: left_row.weights.clone(),
            target: left_row.target.add(gamma.mul(right_row.target)),
        });
    }
    Ok(FieldAccClaim {
        root: folded_root,
        word_len: left.word_len,
        channel,
    })
}

pub fn fold_words<E: SumcheckScalar>(
    left: &[E],
    right: &[E],
    gamma: E,
) -> Result<Vec<E>, FieldAccError> {
    if left.len() != right.len() {
        return Err(FieldAccError::WordWidth {
            expected: left.len(),
            actual: right.len(),
        });
    }
    Ok(left
        .iter()
        .copied()
        .zip(right.iter().copied())
        .map(|(left, right)| left.add(gamma.mul(right)))
        .collect())
}
