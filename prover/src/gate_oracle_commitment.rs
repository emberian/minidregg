//! `[PROVER-gate-oracle-join]` — bind the materialized gate-defect oracle to
//! the sumcheck terminal claim.
//!
//! The existing gate prover constructs a gamma-batched hypercube table and the
//! sumcheck verifier receives its multilinear extension as an unbound closure.
//! This reference join commits that exact table, carries every leaf opening,
//! reconstructs it at verification time, checks it equals the descriptor's
//! materialized residual table, and only then evaluates its MLE at the terminal
//! sumcheck point.  A wrong oracle, root, opening, or terminal message therefore
//! rejects fail-closed.
//!
//! This is intentionally the full-opening resolution: `2^m` values and every
//! Merkle path travel with the proof, and the verifier still receives the full
//! trace from which it recomputes the residual table.  The exact remaining join
//! is `[PROVER-gate-oracle-succinct-PCS]`: a root-before-challenge transcript,
//! queried openings plus the selector/factored quadratic terminal identity, and
//! an LDT proving the committed oracle has the required degree, without revealing
//! or recomputing the whole trace/table.  Hash binding remains `[COMMIT-CR]`.
//! Nothing in this module claims either residual.

use core::fmt;

use crate::commit::{commit_trace, open, verify_open};
use crate::descriptor::{Descriptor, Fp};
use crate::field4::P;
use crate::gate_claim::{
    batch_defect_table, gate_cube_dim, gate_defect_table, prove_gates, verify_gates,
};
use crate::poseidon::PermSpec;
use crate::sumcheck::{mle_eval, SumcheckProof};
use crate::trace::descriptor_holds;
use crate::wide::Digest;

/// One fully disclosed oracle leaf and its Merkle authentication path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GateOracleOpening {
    pub index: usize,
    pub value: Fp,
    pub path: Vec<Digest>,
}

/// The gate sumcheck plus the commitment/openings that realize its terminal
/// MLE oracle at reference resolution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CommittedGateOracleProof {
    pub oracle_root: Digest,
    pub oracle_openings: Vec<GateOracleOpening>,
    pub gate_sumcheck: SumcheckProof,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GateOracleError {
    UnsupportedModulus(u64),
    InvalidDescriptor(String),
    InvalidPermutation(String),
    WrongTraceLength { expected: usize, actual: usize },
    NonCanonicalTrace,
    NonCanonicalChallenge,
    WrongChallengeCount { expected: usize, actual: usize },
    UnsatisfiedDescriptor,
}

impl fmt::Display for GateOracleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedModulus(p) => {
                write!(f, "gate oracle commitment requires BabyBear, got {p}")
            }
            Self::InvalidDescriptor(error) => write!(f, "invalid descriptor: {error}"),
            Self::InvalidPermutation(error) => write!(f, "invalid permutation: {error}"),
            Self::WrongTraceLength { expected, actual } => {
                write!(f, "trace length {actual}, expected {expected}")
            }
            Self::NonCanonicalTrace => write!(f, "trace contains a non-canonical field element"),
            Self::NonCanonicalChallenge => write!(f, "gate challenge is non-canonical"),
            Self::WrongChallengeCount { expected, actual } => {
                write!(f, "sumcheck challenge count {actual}, expected {expected}")
            }
            Self::UnsatisfiedDescriptor => write!(f, "trace does not satisfy the descriptor"),
        }
    }
}

impl std::error::Error for GateOracleError {}

fn validate_inputs(
    descriptor: &Descriptor,
    trace: &[Fp],
    gamma: Fp,
    challenges: &[Fp],
    spec: &PermSpec,
    p: u64,
) -> Result<(), GateOracleError> {
    if p != P {
        return Err(GateOracleError::UnsupportedModulus(p));
    }
    if descriptor.p != P {
        return Err(GateOracleError::UnsupportedModulus(descriptor.p));
    }
    descriptor
        .validate()
        .map_err(GateOracleError::InvalidDescriptor)?;
    spec.validate(p)
        .map_err(GateOracleError::InvalidPermutation)?;
    if spec.width < 2 {
        return Err(GateOracleError::InvalidPermutation(
            "Merkle compression needs width >= 2".into(),
        ));
    }
    if trace.len() != descriptor.n_wires as usize {
        return Err(GateOracleError::WrongTraceLength {
            expected: descriptor.n_wires as usize,
            actual: trace.len(),
        });
    }
    if trace.iter().any(|&value| value >= p) {
        return Err(GateOracleError::NonCanonicalTrace);
    }
    if gamma >= p || challenges.iter().any(|&challenge| challenge >= p) {
        return Err(GateOracleError::NonCanonicalChallenge);
    }
    let expected = gate_cube_dim(descriptor);
    if challenges.len() != expected {
        return Err(GateOracleError::WrongChallengeCount {
            expected,
            actual: challenges.len(),
        });
    }
    Ok(())
}

/// Honest reference prover for the committed gate oracle.  An invalid trace is
/// refused instead of emitting a proof whose zero gate claim cannot verify.
pub fn prove_committed_gate_oracle(
    descriptor: &Descriptor,
    trace: &[Fp],
    gamma: Fp,
    challenges: &[Fp],
    spec: &PermSpec,
    p: u64,
) -> Result<CommittedGateOracleProof, GateOracleError> {
    validate_inputs(descriptor, trace, gamma, challenges, spec, p)?;
    if !descriptor_holds(descriptor, trace) {
        return Err(GateOracleError::UnsatisfiedDescriptor);
    }
    let oracle = batch_defect_table(&gate_defect_table(descriptor, trace), gamma, p);
    let (oracle_root, tree) = commit_trace(spec, &oracle, p);
    let oracle_openings = oracle
        .iter()
        .enumerate()
        .map(|(index, &value)| GateOracleOpening {
            index,
            value,
            path: open(&tree, index),
        })
        .collect();
    Ok(CommittedGateOracleProof {
        oracle_root,
        oracle_openings,
        gate_sumcheck: prove_gates(descriptor, trace, gamma, challenges),
    })
}

/// Verify the committed residual table, then use its MLE for the gate
/// sumcheck's terminal oracle check.  Every malformed shape rejects before any
/// assertion-bearing arithmetic helper is reached.
pub fn verify_committed_gate_oracle(
    descriptor: &Descriptor,
    trace: &[Fp],
    gamma: Fp,
    proof: &CommittedGateOracleProof,
    spec: &PermSpec,
    p: u64,
) -> bool {
    let challenges = &proof.gate_sumcheck.challenges;
    if validate_inputs(descriptor, trace, gamma, challenges, spec, p).is_err()
        || proof.oracle_root.validate().is_err()
    {
        return false;
    }
    let expected = batch_defect_table(&gate_defect_table(descriptor, trace), gamma, p);
    let height = expected.len().trailing_zeros() as usize;
    if proof.oracle_openings.len() != expected.len() {
        return false;
    }

    let mut oracle = Vec::with_capacity(expected.len());
    for (index, (opening, &expected_value)) in
        proof.oracle_openings.iter().zip(&expected).enumerate()
    {
        if opening.index != index
            || opening.value != expected_value
            || opening.value >= p
            || opening.path.len() != height
            || !verify_open(
                proof.oracle_root,
                index,
                opening.value,
                &opening.path,
                spec,
                p,
            )
        {
            return false;
        }
        oracle.push(opening.value);
    }
    if commit_trace(spec, &oracle, p).0 != proof.oracle_root {
        return false;
    }
    verify_gates(&proof.gate_sumcheck, |point| mle_eval(&oracle, point, p), p)
}
