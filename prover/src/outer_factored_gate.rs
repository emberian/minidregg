//! Ext6 factored-gate algebra for a future outer quadratic sumcheck.
//!
//! This module is intentionally not exported yet.  It turns an emitted gate
//! descriptor into seven multilinear operand tables.  Only the left and output
//! multiplicative tables carry the gamma weight, so their product has exactly
//! one gamma factor at Boolean corners.  The resulting polynomial has
//! individual degree at most two and the same cube sum as the existing batched
//! gate residual.

use core::fmt;

use crate::{
    descriptor::{Descriptor, GateOp, Wire},
    field4::{HALF, P},
    field6::Ext6,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FactoredGateError {
    Descriptor(String),
    WrongModulus { actual: u64 },
    TraceLength { expected: usize, actual: usize },
    NonCanonicalTrace { index: usize, value: u64 },
    TableShape,
    PointDimension { expected: usize, actual: usize },
    NoRoundRemaining,
    NotTerminal { remaining: usize },
}

impl fmt::Display for FactoredGateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Descriptor(error) => write!(f, "invalid descriptor: {error}"),
            Self::WrongModulus { actual } => {
                write!(
                    f,
                    "factored gates require BabyBear modulus {P}, got {actual}"
                )
            }
            Self::TraceLength { expected, actual } => {
                write!(f, "trace has {actual} wires, expected {expected}")
            }
            Self::NonCanonicalTrace { index, value } => {
                write!(f, "trace wire {index} is non-canonical: {value}")
            }
            Self::TableShape => write!(f, "operand tables must have one common power-of-two size"),
            Self::PointDimension { expected, actual } => {
                write!(
                    f,
                    "terminal point has dimension {actual}, expected {expected}"
                )
            }
            Self::NoRoundRemaining => write!(f, "quadratic sumcheck is already terminal"),
            Self::NotTerminal { remaining } => {
                write!(f, "quadratic sumcheck still has {remaining} table entries")
            }
        }
    }
}

impl std::error::Error for FactoredGateError {}

/// The fixed seven operand evaluations in the factored gate polynomial.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OperandEvaluations {
    pub mul_left_weighted: Ext6,
    pub mul_right: Ext6,
    pub mul_output_weighted: Ext6,
    pub add_left_weighted: Ext6,
    pub add_right_weighted: Ext6,
    pub add_output_weighted: Ext6,
    pub zero_weighted: Ext6,
}

impl OperandEvaluations {
    /// `(gamma*A) * B - gamma*C + gamma*(L+R-O) + gamma*Z`.
    pub fn polynomial_value(self) -> Ext6 {
        self.mul_left_weighted
            .mul(self.mul_right)
            .sub(self.mul_output_weighted)
            .add(self.add_left_weighted)
            .add(self.add_right_weighted)
            .sub(self.add_output_weighted)
            .add(self.zero_weighted)
    }
}

/// Padded operand tables in LSB-first Boolean-cube order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FactoredGateTables {
    pub mul_left_weighted: Vec<Ext6>,
    pub mul_right: Vec<Ext6>,
    pub mul_output_weighted: Vec<Ext6>,
    pub add_left_weighted: Vec<Ext6>,
    pub add_right_weighted: Vec<Ext6>,
    pub add_output_weighted: Vec<Ext6>,
    pub zero_weighted: Vec<Ext6>,
}

impl FactoredGateTables {
    pub fn len(&self) -> usize {
        self.mul_left_weighted.len()
    }

    pub fn cube_dim(&self) -> Result<usize, FactoredGateError> {
        self.validate_shape()?;
        Ok(self.len().trailing_zeros() as usize)
    }

    /// Sum of the degree-two factored polynomial on the remaining cube.
    pub fn cube_sum(&self) -> Result<Ext6, FactoredGateError> {
        self.validate_shape()?;
        Ok((0..self.len()).fold(Ext6::ZERO, |sum, index| {
            sum.add(self.at(index).polynomial_value())
        }))
    }

    fn at(&self, index: usize) -> OperandEvaluations {
        OperandEvaluations {
            mul_left_weighted: self.mul_left_weighted[index],
            mul_right: self.mul_right[index],
            mul_output_weighted: self.mul_output_weighted[index],
            add_left_weighted: self.add_left_weighted[index],
            add_right_weighted: self.add_right_weighted[index],
            add_output_weighted: self.add_output_weighted[index],
            zero_weighted: self.zero_weighted[index],
        }
    }

    fn validate_shape(&self) -> Result<(), FactoredGateError> {
        let len = self.len();
        if len == 0
            || !len.is_power_of_two()
            || self.mul_right.len() != len
            || self.mul_output_weighted.len() != len
            || self.add_left_weighted.len() != len
            || self.add_right_weighted.len() != len
            || self.add_output_weighted.len() != len
            || self.zero_weighted.len() != len
        {
            Err(FactoredGateError::TableShape)
        } else {
            Ok(())
        }
    }
}

fn base(value: u64) -> Ext6 {
    Ext6::try_from_base(value).expect("validated BabyBear value embeds in Ext6")
}

fn read_operand(trace: &[u64], operand: &Wire) -> Ext6 {
    match *operand {
        Wire::Const(value) => base(value),
        Wire::Wire(index) => base(trace[index as usize]),
    }
}

/// Build the factored operand tables from one validated emitted descriptor and
/// one canonical trace.  Constraint index `k` carries `gamma^k`; padding is zero.
pub fn build_factored_gate_tables(
    descriptor: &Descriptor,
    trace: &[u64],
    gamma: Ext6,
) -> Result<FactoredGateTables, FactoredGateError> {
    descriptor
        .validate()
        .map_err(FactoredGateError::Descriptor)?;
    if descriptor.p != P {
        return Err(FactoredGateError::WrongModulus {
            actual: descriptor.p,
        });
    }
    if trace.len() != descriptor.n_wires as usize {
        return Err(FactoredGateError::TraceLength {
            expected: descriptor.n_wires as usize,
            actual: trace.len(),
        });
    }
    if let Some((index, &value)) = trace.iter().enumerate().find(|(_, value)| **value >= P) {
        return Err(FactoredGateError::NonCanonicalTrace { index, value });
    }

    let constraints = descriptor.gates.len() + descriptor.zeros.len();
    let len = constraints.next_power_of_two();
    let zeros = || vec![Ext6::ZERO; len];
    let mut tables = FactoredGateTables {
        mul_left_weighted: zeros(),
        mul_right: zeros(),
        mul_output_weighted: zeros(),
        add_left_weighted: zeros(),
        add_right_weighted: zeros(),
        add_output_weighted: zeros(),
        zero_weighted: zeros(),
    };

    let mut gamma_power = Ext6::ONE;
    for (index, gate) in descriptor.gates.iter().enumerate() {
        let left = read_operand(trace, &gate.a);
        let right = read_operand(trace, &gate.b);
        let output = base(trace[gate.out as usize]);
        match gate.op {
            GateOp::Mul => {
                tables.mul_left_weighted[index] = gamma_power.mul(left);
                tables.mul_right[index] = right;
                tables.mul_output_weighted[index] = gamma_power.mul(output);
            }
            GateOp::Add => {
                tables.add_left_weighted[index] = gamma_power.mul(left);
                tables.add_right_weighted[index] = gamma_power.mul(right);
                tables.add_output_weighted[index] = gamma_power.mul(output);
            }
        }
        gamma_power = gamma_power.mul(gamma);
    }
    for (zero_index, operand) in descriptor.zeros.iter().enumerate() {
        let index = descriptor.gates.len() + zero_index;
        tables.zero_weighted[index] = gamma_power.mul(read_operand(trace, operand));
        gamma_power = gamma_power.mul(gamma);
    }
    Ok(tables)
}

fn interpolate(pair: &[Ext6], challenge: Ext6) -> Ext6 {
    pair[0].add(pair[1].sub(pair[0]).mul(challenge))
}

fn fold_table(table: &[Ext6], challenge: Ext6) -> Vec<Ext6> {
    table
        .chunks_exact(2)
        .map(|pair| interpolate(pair, challenge))
        .collect()
}

fn fold_all(tables: &mut FactoredGateTables, challenge: Ext6) {
    tables.mul_left_weighted = fold_table(&tables.mul_left_weighted, challenge);
    tables.mul_right = fold_table(&tables.mul_right, challenge);
    tables.mul_output_weighted = fold_table(&tables.mul_output_weighted, challenge);
    tables.add_left_weighted = fold_table(&tables.add_left_weighted, challenge);
    tables.add_right_weighted = fold_table(&tables.add_right_weighted, challenge);
    tables.add_output_weighted = fold_table(&tables.add_output_weighted, challenge);
    tables.zero_weighted = fold_table(&tables.zero_weighted, challenge);
}

fn round_value(tables: &FactoredGateTables, at: Ext6) -> Ext6 {
    let mut sum = Ext6::ZERO;
    for pair in 0..tables.len() / 2 {
        let lo = 2 * pair;
        let hi = lo + 2;
        let values = OperandEvaluations {
            mul_left_weighted: interpolate(&tables.mul_left_weighted[lo..hi], at),
            mul_right: interpolate(&tables.mul_right[lo..hi], at),
            mul_output_weighted: interpolate(&tables.mul_output_weighted[lo..hi], at),
            add_left_weighted: interpolate(&tables.add_left_weighted[lo..hi], at),
            add_right_weighted: interpolate(&tables.add_right_weighted[lo..hi], at),
            add_output_weighted: interpolate(&tables.add_output_weighted[lo..hi], at),
            zero_weighted: interpolate(&tables.zero_weighted[lo..hi], at),
        };
        sum = sum.add(values.polynomial_value());
    }
    sum
}

/// Evaluate a degree-at-most-two round polynomial from `[g(0),g(1),g(2)]`.
pub fn evaluate_quadratic(message: [Ext6; 3], at: Ext6) -> Ext6 {
    let [g0, g1, g2] = message;
    let linear = g1.sub(g0).mul(at);
    let second_difference = g2.sub(g1.add(g1)).add(g0);
    let choose_two = at.mul(at.sub(Ext6::ONE)).mul(base(HALF));
    g0.add(linear).add(second_difference.mul(choose_two))
}

/// Streaming prover state: emit one quadratic message, bind one LSB-first
/// challenge, and discard the bound coordinate from all seven tables.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuadraticGateSumcheckState {
    tables: FactoredGateTables,
}

impl QuadraticGateSumcheckState {
    pub fn new(tables: FactoredGateTables) -> Result<Self, FactoredGateError> {
        tables.validate_shape()?;
        Ok(Self { tables })
    }

    pub fn rounds_remaining(&self) -> usize {
        self.tables.len().trailing_zeros() as usize
    }

    pub fn claim(&self) -> Result<Ext6, FactoredGateError> {
        self.tables.cube_sum()
    }

    pub fn round_message(&self) -> Result<[Ext6; 3], FactoredGateError> {
        if self.tables.len() == 1 {
            return Err(FactoredGateError::NoRoundRemaining);
        }
        Ok([
            round_value(&self.tables, Ext6::ZERO),
            round_value(&self.tables, Ext6::ONE),
            round_value(&self.tables, base(2)),
        ])
    }

    pub fn bind(&mut self, challenge: Ext6) -> Result<(), FactoredGateError> {
        if self.tables.len() == 1 {
            return Err(FactoredGateError::NoRoundRemaining);
        }
        fold_all(&mut self.tables, challenge);
        Ok(())
    }

    pub fn terminal(&self) -> Result<OperandEvaluations, FactoredGateError> {
        if self.tables.len() != 1 {
            return Err(FactoredGateError::NotTerminal {
                remaining: self.tables.len(),
            });
        }
        Ok(self.tables.at(0))
    }
}

/// A public affine selector: `constant + dot(trace, weights)` over Ext6.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraceAffineForm {
    pub constant: Ext6,
    pub weights: Vec<Ext6>,
}

impl TraceAffineForm {
    fn zero(n_wires: usize) -> Self {
        Self {
            constant: Ext6::ZERO,
            weights: vec![Ext6::ZERO; n_wires],
        }
    }

    fn add_operand(&mut self, operand: &Wire, coefficient: Ext6) {
        match *operand {
            Wire::Const(value) => {
                self.constant = self.constant.add(coefficient.mul(base(value)));
            }
            Wire::Wire(index) => {
                let weight = &mut self.weights[index as usize];
                *weight = weight.add(coefficient);
            }
        }
    }

    pub fn evaluate(&self, trace: &[u64]) -> Result<Ext6, FactoredGateError> {
        if trace.len() != self.weights.len() {
            return Err(FactoredGateError::TraceLength {
                expected: self.weights.len(),
                actual: trace.len(),
            });
        }
        let mut value = self.constant;
        for (index, (&wire, &weight)) in trace.iter().zip(&self.weights).enumerate() {
            if wire >= P {
                return Err(FactoredGateError::NonCanonicalTrace { index, value: wire });
            }
            value = value.add(weight.mul(base(wire)));
        }
        Ok(value)
    }
}

/// Public terminal selector weights for all seven fixed operand MLEs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TerminalOperandSelectors {
    pub mul_left_weighted: TraceAffineForm,
    pub mul_right: TraceAffineForm,
    pub mul_output_weighted: TraceAffineForm,
    pub add_left_weighted: TraceAffineForm,
    pub add_right_weighted: TraceAffineForm,
    pub add_output_weighted: TraceAffineForm,
    pub zero_weighted: TraceAffineForm,
}

impl TerminalOperandSelectors {
    fn zero(n_wires: usize) -> Self {
        Self {
            mul_left_weighted: TraceAffineForm::zero(n_wires),
            mul_right: TraceAffineForm::zero(n_wires),
            mul_output_weighted: TraceAffineForm::zero(n_wires),
            add_left_weighted: TraceAffineForm::zero(n_wires),
            add_right_weighted: TraceAffineForm::zero(n_wires),
            add_output_weighted: TraceAffineForm::zero(n_wires),
            zero_weighted: TraceAffineForm::zero(n_wires),
        }
    }

    pub fn evaluate(&self, trace: &[u64]) -> Result<OperandEvaluations, FactoredGateError> {
        Ok(OperandEvaluations {
            mul_left_weighted: self.mul_left_weighted.evaluate(trace)?,
            mul_right: self.mul_right.evaluate(trace)?,
            mul_output_weighted: self.mul_output_weighted.evaluate(trace)?,
            add_left_weighted: self.add_left_weighted.evaluate(trace)?,
            add_right_weighted: self.add_right_weighted.evaluate(trace)?,
            add_output_weighted: self.add_output_weighted.evaluate(trace)?,
            zero_weighted: self.zero_weighted.evaluate(trace)?,
        })
    }
}

fn cube_basis_weights(point: &[Ext6]) -> Vec<Ext6> {
    let mut weights = vec![Ext6::ONE];
    for &coordinate in point {
        let low_factor = Ext6::ONE.sub(coordinate);
        let old = weights;
        let mut next = Vec::with_capacity(2 * old.len());
        next.extend(old.iter().map(|&weight| weight.mul(low_factor)));
        next.extend(old.iter().map(|&weight| weight.mul(coordinate)));
        weights = next;
    }
    weights
}

/// Derive public affine trace selectors for the terminal point.  Their direct
/// evaluation must equal the seven singleton values left by the streaming state.
pub fn terminal_operand_selectors(
    descriptor: &Descriptor,
    gamma: Ext6,
    point: &[Ext6],
) -> Result<TerminalOperandSelectors, FactoredGateError> {
    descriptor
        .validate()
        .map_err(FactoredGateError::Descriptor)?;
    if descriptor.p != P {
        return Err(FactoredGateError::WrongModulus {
            actual: descriptor.p,
        });
    }
    let constraints = descriptor.gates.len() + descriptor.zeros.len();
    let len = constraints.next_power_of_two();
    let dimension = len.trailing_zeros() as usize;
    if point.len() != dimension {
        return Err(FactoredGateError::PointDimension {
            expected: dimension,
            actual: point.len(),
        });
    }

    let basis = cube_basis_weights(point);
    let mut selectors = TerminalOperandSelectors::zero(descriptor.n_wires as usize);
    let mut gamma_power = Ext6::ONE;
    for (index, gate) in descriptor.gates.iter().enumerate() {
        let weighted_basis = basis[index].mul(gamma_power);
        let output = Wire::Wire(gate.out);
        match gate.op {
            GateOp::Mul => {
                selectors
                    .mul_left_weighted
                    .add_operand(&gate.a, weighted_basis);
                selectors.mul_right.add_operand(&gate.b, basis[index]);
                selectors
                    .mul_output_weighted
                    .add_operand(&output, weighted_basis);
            }
            GateOp::Add => {
                selectors
                    .add_left_weighted
                    .add_operand(&gate.a, weighted_basis);
                selectors
                    .add_right_weighted
                    .add_operand(&gate.b, weighted_basis);
                selectors
                    .add_output_weighted
                    .add_operand(&output, weighted_basis);
            }
        }
        gamma_power = gamma_power.mul(gamma);
    }
    for (zero_index, operand) in descriptor.zeros.iter().enumerate() {
        let index = descriptor.gates.len() + zero_index;
        let weighted_basis = basis[index].mul(gamma_power);
        selectors.zero_weighted.add_operand(operand, weighted_basis);
        gamma_power = gamma_power.mul(gamma);
    }
    Ok(selectors)
}
