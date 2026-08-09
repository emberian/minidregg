//! Isolated Ext6 Fiat--Shamir gate-sumcheck reference phase.
//!
//! Base-field descriptor defects are embedded into BabyBear⁶, weighted by an
//! extension-field `gamma`, and retired by a streaming multilinear sumcheck.
//! Every message is absorbed before the next atomic Ext6 challenge.  The proof
//! carries only a wide trace root and round messages: the gate claim is the
//! statement-fixed zero, and no proof-carried challenge is trusted.
//!
//! This is intentionally a clear-trace reference join.  Verification recomputes
//! the whole gate table and terminal MLE from `trace`; succinct deployment still
//! needs the factored quadratic selector/opening terminal oracle.

use core::fmt;

use crate::commit::commit_trace;
use crate::descriptor::{Descriptor, Fp, GateOp, Wire};
use crate::field4::P;
use crate::field6::Ext6;
use crate::gate_claim::gate_defect_table;
use crate::poseidon::PermSpec;
use crate::sumcheck_generic::{
    batch_lifted_residuals, evaluate_mle, verify, SumcheckError, SumcheckProof,
};
use crate::sumcheck_streaming::{StreamingSumcheckError, StreamingSumcheckProver};
use crate::transcript_ext6::{Ext6Transcript, Ext6TranscriptError, WideExt6Backend};
use crate::wide::Digest;

const STATEMENT_HEADER_DOMAIN: Fp = 0x5847_4844; // "XGHD"
const STATEMENT_GATE_DOMAIN: Fp = 0x5847_4154; // "XGAT"
const STATEMENT_ZERO_DOMAIN: Fp = 0x585a_4552; // "XZER"
const STATEMENT_PUBLIC_DOMAIN: Fp = 0x5850_5542; // "XPUB"
const TRACE_ROOT_DOMAIN: Fp = 0x5854_5254; // "XTRT"
const GATE_PHASE_DOMAIN: Fp = 0x5847_5048; // "XGPH"
const GATE_GAMMA_DOMAIN: Fp = 0x5847_414d; // "XGAM"
const ROUND_INDEX_DOMAIN: Fp = 0x5852_4944; // "XRID"
const ROUND_MESSAGE_DOMAIN: Fp = 0x5852_4d53; // "XRMS"
const ROUND_CHALLENGE_DOMAIN: Fp = 0x5852_4348; // "XRCH"

/// Proof-controlled data for the isolated gate phase.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ext6GateProof {
    pub trace_root: Digest,
    pub sumcheck: SumcheckProof<Ext6>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ext6GateError {
    Instance(String),
    Transcript(Ext6TranscriptError),
    Streaming(StreamingSumcheckError),
    Sumcheck(SumcheckError),
}

impl fmt::Display for Ext6GateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Instance(message) => write!(f, "Ext6 gate instance: {message}"),
            Self::Transcript(error) => write!(f, "{error}"),
            Self::Streaming(error) => write!(f, "{error}"),
            Self::Sumcheck(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for Ext6GateError {}

impl From<Ext6TranscriptError> for Ext6GateError {
    fn from(error: Ext6TranscriptError) -> Self {
        Self::Transcript(error)
    }
}

impl From<StreamingSumcheckError> for Ext6GateError {
    fn from(error: StreamingSumcheckError) -> Self {
        Self::Streaming(error)
    }
}

impl From<SumcheckError> for Ext6GateError {
    fn from(error: SumcheckError) -> Self {
        Self::Sumcheck(error)
    }
}

fn wire_fields(wire: &Wire) -> [Fp; 2] {
    match *wire {
        Wire::Const(value) => [0, value],
        Wire::Wire(index) => [1, index as Fp],
    }
}

fn checked_fp(value: usize, what: &str) -> Result<Fp, Ext6GateError> {
    if value as u128 >= P as u128 {
        Err(Ext6GateError::Instance(format!(
            "{what}={value} does not fit one canonical BabyBear element"
        )))
    } else {
        Ok(value as Fp)
    }
}

fn gate_shape(descriptor: &Descriptor) -> Result<(usize, usize), Ext6GateError> {
    let entries = descriptor
        .gates
        .len()
        .checked_add(descriptor.zeros.len())
        .ok_or_else(|| Ext6GateError::Instance("gate-table length overflow".into()))?;
    let table_len = if entries == 0 {
        1
    } else {
        entries.checked_next_power_of_two().ok_or_else(|| {
            Ext6GateError::Instance("gate-table power-of-two padding overflow".into())
        })?
    };
    checked_fp(table_len, "gate table length")?;
    Ok((table_len, table_len.trailing_zeros() as usize))
}

fn validate_instance(
    descriptor: &Descriptor,
    public_inputs: &[Fp],
    trace: &[Fp],
    spec: &PermSpec,
) -> Result<(), Ext6GateError> {
    descriptor.validate().map_err(Ext6GateError::Instance)?;
    spec.validate(P).map_err(Ext6GateError::Instance)?;
    if descriptor.p != P {
        return Err(Ext6GateError::Instance(format!(
            "descriptor modulus {} is not BabyBear {P}",
            descriptor.p
        )));
    }
    if spec.width < 2 {
        return Err(Ext6GateError::Instance(
            "trace commitment needs permutation width at least two".into(),
        ));
    }
    if descriptor.n_wires == 0 {
        return Err(Ext6GateError::Instance(
            "clear gate reference cannot commit an empty trace".into(),
        ));
    }
    if public_inputs.len() != descriptor.n_public as usize {
        return Err(Ext6GateError::Instance(format!(
            "public input length {}, expected {}",
            public_inputs.len(),
            descriptor.n_public
        )));
    }
    if trace.len() != descriptor.n_wires as usize {
        return Err(Ext6GateError::Instance(format!(
            "trace length {}, expected {}",
            trace.len(),
            descriptor.n_wires
        )));
    }
    if let Some((index, &value)) = public_inputs
        .iter()
        .chain(trace.iter())
        .enumerate()
        .find(|(_, value)| **value >= P)
    {
        return Err(Ext6GateError::Instance(format!(
            "public/trace element {index} is non-canonical: {value}"
        )));
    }
    if trace[..public_inputs.len()] != *public_inputs {
        return Err(Ext6GateError::Instance(
            "trace public prefix does not equal the public statement".into(),
        ));
    }

    checked_fp(descriptor.n_public as usize, "n_public")?;
    checked_fp(descriptor.n_vars as usize, "n_vars")?;
    checked_fp(descriptor.n_wires as usize, "n_wires")?;
    checked_fp(descriptor.gates.len(), "gate count")?;
    checked_fp(descriptor.zeros.len(), "zero-check count")?;
    gate_shape(descriptor)?;
    Ok(())
}

fn absorb_statement<B: WideExt6Backend>(
    transcript: &mut Ext6Transcript<B>,
    descriptor: &Descriptor,
    public_inputs: &[Fp],
) -> Result<(), Ext6GateError> {
    transcript.absorb_record(
        STATEMENT_HEADER_DOMAIN,
        &[
            1, // gate protocol version
            descriptor.n_public as Fp,
            descriptor.n_vars as Fp,
            descriptor.n_wires as Fp,
            descriptor.gates.len() as Fp,
            descriptor.zeros.len() as Fp,
        ],
    )?;
    for (index, gate) in descriptor.gates.iter().enumerate() {
        let a = wire_fields(&gate.a);
        let b = wire_fields(&gate.b);
        transcript.absorb_record(
            STATEMENT_GATE_DOMAIN,
            &[
                index as Fp,
                match gate.op {
                    GateOp::Add => 0,
                    GateOp::Mul => 1,
                },
                a[0],
                a[1],
                b[0],
                b[1],
                gate.out as Fp,
            ],
        )?;
    }
    for (index, wire) in descriptor.zeros.iter().enumerate() {
        let encoded = wire_fields(wire);
        transcript.absorb_record(
            STATEMENT_ZERO_DOMAIN,
            &[index as Fp, encoded[0], encoded[1]],
        )?;
    }
    transcript.absorb_record(STATEMENT_PUBLIC_DOMAIN, public_inputs)?;
    Ok(())
}

fn absorb_round<B: WideExt6Backend>(
    transcript: &mut Ext6Transcript<B>,
    round_index: usize,
    message: &[Ext6; 2],
) -> Result<(), Ext6GateError> {
    transcript.absorb_record(ROUND_INDEX_DOMAIN, &[round_index as Fp])?;
    transcript.absorb_ext6_record(ROUND_MESSAGE_DOMAIN, message)?;
    Ok(())
}

fn start_transcript<'a, B: WideExt6Backend>(
    backend: &'a mut B,
    descriptor: &Descriptor,
    public_inputs: &[Fp],
    trace_root: &Digest,
) -> Result<Ext6Transcript<&'a mut B>, Ext6GateError> {
    let (table_len, rounds) = gate_shape(descriptor)?;
    let mut transcript = Ext6Transcript::new(backend)?;
    absorb_statement(&mut transcript, descriptor, public_inputs)?;
    transcript.absorb_digest(TRACE_ROOT_DOMAIN, trace_root)?;
    transcript.absorb_record(
        GATE_PHASE_DOMAIN,
        &[
            rounds as Fp,
            table_len as Fp,
            0, // statement-fixed sumcheck claim
        ],
    )?;
    Ok(transcript)
}

/// Prove the clear-reference gate phase with atomic Ext6 challenges.
pub fn prove_clear_gate_ext6<B: WideExt6Backend>(
    descriptor: &Descriptor,
    public_inputs: &[Fp],
    trace: &[Fp],
    spec: &PermSpec,
    backend: &mut B,
) -> Result<Ext6GateProof, Ext6GateError> {
    validate_instance(descriptor, public_inputs, trace, spec)?;
    let (trace_root, _) = commit_trace(spec, trace, P);
    let mut transcript = start_transcript(backend, descriptor, public_inputs, &trace_root)?;
    let gamma = transcript.squeeze_ext6(GATE_GAMMA_DOMAIN)?;
    let table = batch_lifted_residuals::<Ext6>(&gate_defect_table(descriptor, trace), gamma)?;

    let mut prover = StreamingSumcheckProver::new(&table)?;
    let (_, num_rounds) = gate_shape(descriptor)?;
    let mut rounds = Vec::with_capacity(num_rounds);
    for round_index in 0..num_rounds {
        let message = prover.message()?;
        absorb_round(&mut transcript, round_index, &message)?;
        let challenge = transcript.squeeze_ext6(ROUND_CHALLENGE_DOMAIN)?;
        prover.bind(challenge)?;
        rounds.push(message);
    }
    let _terminal_oracle_value = prover.finish()?;
    Ok(Ext6GateProof {
        trace_root,
        sumcheck: SumcheckProof { rounds },
    })
}

/// Verify the clear-reference gate phase, replaying every Ext6 challenge.
///
/// Proof shape/root/message failures return `Ok(false)`; invalid public
/// instances or a failing transcript backend return an explicit error.
pub fn verify_clear_gate_ext6<B: WideExt6Backend>(
    descriptor: &Descriptor,
    public_inputs: &[Fp],
    trace: &[Fp],
    proof: &Ext6GateProof,
    spec: &PermSpec,
    backend: &mut B,
) -> Result<bool, Ext6GateError> {
    validate_instance(descriptor, public_inputs, trace, spec)?;
    let (_, num_rounds) = gate_shape(descriptor)?;
    if !proof.trace_root.is_canonical() || proof.sumcheck.rounds.len() != num_rounds {
        return Ok(false);
    }
    let (expected_root, _) = commit_trace(spec, trace, P);
    if proof.trace_root != expected_root {
        return Ok(false);
    }

    let mut transcript = start_transcript(backend, descriptor, public_inputs, &proof.trace_root)?;
    let gamma = transcript.squeeze_ext6(GATE_GAMMA_DOMAIN)?;
    let table = batch_lifted_residuals::<Ext6>(&gate_defect_table(descriptor, trace), gamma)?;
    let mut challenges = Vec::with_capacity(proof.sumcheck.rounds.len());
    for (round_index, message) in proof.sumcheck.rounds.iter().enumerate() {
        absorb_round(&mut transcript, round_index, message)?;
        challenges.push(transcript.squeeze_ext6(ROUND_CHALLENGE_DOMAIN)?);
    }
    let terminal = evaluate_mle(&table, &challenges)?;
    verify(Ext6::ZERO, &proof.sumcheck, &challenges, terminal).map_err(Ext6GateError::from)
}
