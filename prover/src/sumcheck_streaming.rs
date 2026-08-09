//! Streaming prover state for the generic multilinear sumcheck core.
//!
//! A Fiat--Shamir prover cannot receive all challenges up front: it must emit
//! `g_i(0), g_i(1)`, absorb that message, and only then bind `r_i`.  This state
//! machine makes that order structural while reusing [`SumcheckScalar`].

use core::fmt;

use crate::sumcheck_generic::SumcheckScalar;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StreamingSumcheckError {
    EmptyTable,
    NonPowerOfTwo { len: usize },
    AlreadyComplete,
    Incomplete { remaining: usize },
}

impl fmt::Display for StreamingSumcheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyTable => write!(f, "sumcheck table is empty"),
            Self::NonPowerOfTwo { len } => {
                write!(f, "sumcheck table length {len} is not a power of two")
            }
            Self::AlreadyComplete => write!(f, "sumcheck prover is already complete"),
            Self::Incomplete { remaining } => {
                write!(f, "sumcheck prover still has {remaining} values")
            }
        }
    }
}

impl std::error::Error for StreamingSumcheckError {}

fn sum<E: SumcheckScalar>(values: impl IntoIterator<Item = E>) -> E {
    values
        .into_iter()
        .fold(E::ZERO, |accumulator, value| accumulator.add(value))
}

/// One honest multilinear-sumcheck prover, reduced after every challenge.
pub struct StreamingSumcheckProver<E> {
    layer: Vec<E>,
}

impl<E: SumcheckScalar> StreamingSumcheckProver<E> {
    pub fn new(table: &[E]) -> Result<Self, StreamingSumcheckError> {
        if table.is_empty() {
            return Err(StreamingSumcheckError::EmptyTable);
        }
        if !table.len().is_power_of_two() {
            return Err(StreamingSumcheckError::NonPowerOfTwo { len: table.len() });
        }
        Ok(Self {
            layer: table.to_vec(),
        })
    }

    /// The next affine round message, before its challenge is known.
    pub fn message(&self) -> Result<[E; 2], StreamingSumcheckError> {
        if self.layer.len() == 1 {
            return Err(StreamingSumcheckError::AlreadyComplete);
        }
        Ok([
            sum(self.layer.iter().step_by(2).copied()),
            sum(self.layer.iter().skip(1).step_by(2).copied()),
        ])
    }

    /// Bind the just-emitted message at `challenge` and advance one round.
    pub fn bind(&mut self, challenge: E) -> Result<(), StreamingSumcheckError> {
        if self.layer.len() == 1 {
            return Err(StreamingSumcheckError::AlreadyComplete);
        }
        self.layer = self
            .layer
            .chunks_exact(2)
            .map(|pair| pair[0].add(pair[1].sub(pair[0]).mul(challenge)))
            .collect();
        Ok(())
    }

    /// Consume a fully reduced state and return the terminal oracle value.
    pub fn finish(self) -> Result<E, StreamingSumcheckError> {
        if self.layer.len() != 1 {
            return Err(StreamingSumcheckError::Incomplete {
                remaining: self.layer.len(),
            });
        }
        Ok(self.layer[0])
    }
}
