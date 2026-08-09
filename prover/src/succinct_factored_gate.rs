//! Succinct factored-gate proof against one committed trace table.
//!
//! The prover commits the zero-padded, BabyBear-to-Ext6 lifted trace before
//! drawing `gamma`.  A degree-two outer sumcheck reduces the factored gate
//! claim to seven affine trace values.  After all seven values are bound, a
//! fresh `eta` combines their public affine selectors into one linear claim,
//! which [`crate::trace_linear_ext6`] opens against that same trace root.  One
//! cSHAKE/Ext6 transcript owns the entire schedule; the inner opening uses its
//! caller-owned transcript seam and cannot restart Fiat--Shamir.
//!
//! After the seven selector equations, the same `eta` aggregation appends one
//! equation for every public-prefix cell and every required zero-padding cell.
//! Thus the committed table is tied to the entire public statement, including
//! public wires unused by any gate, and to its advertised zero padding.  A false
//! aggregate is a nonzero polynomial in `eta` of degree at most
//! `6 + n_public + padding`, which is part of `[SUCCINCT-GATE-ROM]`'s soundness
//! accounting.
//!
//! This closes the factored-selector/table-provenance seam at the current
//! sampled PCS resolution.  Remaining assumptions are BinaryShake Merkle
//! collision resistance `[SUCCINCT-GATE-CR]`, cSHAKE/Fiat--Shamir random-oracle
//! analysis (including outer sumcheck and `eta` aggregation soundness)
//! `[SUCCINCT-GATE-ROM]`, sampled fold/proximity soundness at the landed coherent
//! multiplicative bound `m*b/|F| + (1-tau)^q` `[SUCCINCT-GATE-PROXIMITY]`, and
//! executable-to-formal refinement of the descriptor, selector, sumcheck,
//! Mobius/RS, and query code are unverified Rust compute under
//! `[SUCCINCT-GATE-RUST-UNVERIFIED]`.
//!
//! The verifier additionally requires both round-zero values in every sampled
//! MLE pair to be base-field lifts.  Conditioned on the initial word being
//! `delta`-close to an Ext6 RS codeword of degree `< N` over its `M`-point base
//! domain, a genuinely non-base component polynomial has both values base on at
//! most `floor((N-1)/2)` of the `M/2` antipodal pairs.  A `delta*M` corruption
//! set can contaminate that many further pairs, so the safe query miss term is
//! `(min(1, 2*delta + (N-1)/M))^q` `[SUCCINCT-GATE-SUBFIELD]`.  Composing this
//! executable check with the coherent proximity theorem remains part of runtime
//! refinement.

use core::fmt;

use crate::{
    binary_hash::{BinaryRoot, BinaryShake256V1, HashSuite},
    descriptor::{Descriptor, Fp, GateOp, Wire},
    field4::{P, TWO_ADIC_BITS},
    field6::Ext6,
    multiplicative_mle_terminal::{
        MleTerminalError, MleTerminalProverState, MleTerminalTranscript,
    },
    outer_factored_gate::{
        build_factored_gate_tables, evaluate_quadratic, terminal_operand_selectors,
        FactoredGateError, OperandEvaluations, QuadraticGateSumcheckState,
    },
    trace_linear_ext6::{
        prove_trace_linear_from_state, verify_trace_linear_after_initial, TraceLinearError,
        TraceLinearProof, TraceLinearStatement,
    },
    transcript_ext6::{BinaryShakeExt6Backend, Ext6Transcript, Ext6TranscriptError},
};

const BACKEND_LABEL: &[u8] = b"minidregg/succinct-factored-gate/v1";

const STATEMENT_HEADER_DOMAIN: Fp = 0x5347_4844; // "SGHD"
const STATEMENT_GATE_DOMAIN: Fp = 0x5347_4754; // "SGGT"
const STATEMENT_ZERO_DOMAIN: Fp = 0x5347_5a52; // "SGZR"
const STATEMENT_PUBLIC_DOMAIN: Fp = 0x5347_5055; // "SGPU"
const GAMMA_DOMAIN: Fp = 0x5347_4741; // "SGGA"
const OUTER_ROUND_META_DOMAIN: Fp = 0x5347_5249; // "SGRI"
const OUTER_ROUND_MESSAGE_DOMAIN: Fp = 0x5347_524d; // "SGRM"
const OUTER_ROUND_CHALLENGE_DOMAIN: Fp = 0x5347_5243; // "SGRC"
const TERMINAL_VALUES_DOMAIN: Fp = 0x5347_544d; // "SGTM"
const ETA_DOMAIN: Fp = 0x5347_4554; // "SGET"

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SuccinctFactoredGateProof {
    /// The Boolean-Mobius multiplicative-RS root of the padded lifted trace.
    pub trace_root: BinaryRoot,
    pub outer_rounds: Vec<[Ext6; 3]>,
    pub terminal_operands: OperandEvaluations,
    pub trace_linear_statement: TraceLinearStatement,
    pub trace_linear_proof: TraceLinearProof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SuccinctFactoredGateError {
    Instance(String),
    UnsatisfiedGateClaim,
    TerminalSelectorMismatch,
    Factored(FactoredGateError),
    Transcript(Ext6TranscriptError),
    Mle(MleTerminalError),
    TraceLinear(TraceLinearError),
}

impl From<FactoredGateError> for SuccinctFactoredGateError {
    fn from(value: FactoredGateError) -> Self {
        Self::Factored(value)
    }
}

impl From<Ext6TranscriptError> for SuccinctFactoredGateError {
    fn from(value: Ext6TranscriptError) -> Self {
        Self::Transcript(value)
    }
}

impl From<MleTerminalError> for SuccinctFactoredGateError {
    fn from(value: MleTerminalError) -> Self {
        Self::Mle(value)
    }
}

impl From<TraceLinearError> for SuccinctFactoredGateError {
    fn from(value: TraceLinearError) -> Self {
        Self::TraceLinear(value)
    }
}

impl fmt::Display for SuccinctFactoredGateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Instance(message) => write!(f, "succinct factored-gate instance: {message}"),
            Self::UnsatisfiedGateClaim => {
                write!(f, "factored gate polynomial does not have zero cube sum")
            }
            Self::TerminalSelectorMismatch => {
                write!(
                    f,
                    "terminal operand values do not match public trace selectors"
                )
            }
            Self::Factored(error) => error.fmt(f),
            Self::Transcript(error) => error.fmt(f),
            Self::Mle(error) => error.fmt(f),
            Self::TraceLinear(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for SuccinctFactoredGateError {}

/// Prove gate satisfaction without putting the trace table in the proof.
pub fn prove_succinct_factored_gate(
    descriptor: &Descriptor,
    public_inputs: &[Fp],
    trace: &[Fp],
    log_blowup: u32,
    num_queries: usize,
) -> Result<SuccinctFactoredGateProof, SuccinctFactoredGateError> {
    let shape =
        validate_prover_instance(descriptor, public_inputs, trace, log_blowup, num_queries)?;
    let trace_table = lifted_trace_table(trace, shape.trace_table_len);
    prove_with_trace_table(
        descriptor,
        public_inputs,
        trace,
        trace_table,
        shape,
        log_blowup,
        num_queries,
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_with_trace_table(
    descriptor: &Descriptor,
    public_inputs: &[Fp],
    trace: &[Fp],
    trace_table: Vec<Ext6>,
    shape: InstanceShape,
    log_blowup: u32,
    num_queries: usize,
) -> Result<SuccinctFactoredGateProof, SuccinctFactoredGateError> {
    if trace_table.len() != shape.trace_table_len {
        return Err(SuccinctFactoredGateError::Instance(
            "committed trace table has the wrong padded length".into(),
        ));
    }

    let mut transcript =
        start_transcript(descriptor, public_inputs, shape, log_blowup, num_queries)?;
    // Commit once, before gamma, under the standard MLE terminal record.  The
    // retained state is consumed by the trace-linear phase after eta.
    let trace_mle = MleTerminalProverState::commit_initial(
        &trace_table,
        log_blowup,
        BinaryShake256V1,
        &mut transcript,
    )?;
    let trace_root = trace_mle.input_root();
    let gamma = transcript.squeeze_ext6(GAMMA_DOMAIN)?;
    let tables = build_factored_gate_tables(descriptor, trace, gamma)?;
    let mut outer = QuadraticGateSumcheckState::new(tables)?;
    if outer.claim()? != Ext6::ZERO {
        return Err(SuccinctFactoredGateError::UnsatisfiedGateClaim);
    }

    let mut outer_rounds = Vec::with_capacity(shape.outer_rounds);
    let mut outer_challenges = Vec::with_capacity(shape.outer_rounds);
    for round in 0..shape.outer_rounds {
        let message = outer.round_message()?;
        absorb_outer_round(&mut transcript, round, &message)?;
        let challenge = transcript.squeeze_ext6(OUTER_ROUND_CHALLENGE_DOMAIN)?;
        outer.bind(challenge)?;
        outer_rounds.push(message);
        outer_challenges.push(challenge);
    }
    let terminal_operands = outer.terminal()?;
    absorb_terminal_operands(&mut transcript, terminal_operands)?;
    let eta = transcript.squeeze_ext6(ETA_DOMAIN)?;

    let selectors = terminal_operand_selectors(descriptor, gamma, &outer_challenges)?;
    if selectors.evaluate(trace)? != terminal_operands {
        return Err(SuccinctFactoredGateError::TerminalSelectorMismatch);
    }
    let (combined_claim, combined_weights) = aggregate_selectors(
        public_inputs,
        shape.trace_len,
        shape.trace_table_len,
        terminal_operands,
        selectors,
        eta,
    );
    let (trace_linear_statement, trace_linear_proof) = prove_trace_linear_from_state(
        &trace_table,
        &combined_weights,
        combined_claim,
        log_blowup,
        num_queries,
        trace_mle,
        &mut transcript,
    )?;
    if trace_linear_statement.table_root != trace_root {
        return Err(SuccinctFactoredGateError::TerminalSelectorMismatch);
    }

    Ok(SuccinctFactoredGateProof {
        trace_root,
        outer_rounds,
        terminal_operands,
        trace_linear_statement,
        trace_linear_proof,
    })
}

/// Verify using only the descriptor, public inputs, and the succinct proof.
pub fn verify_succinct_factored_gate(
    descriptor: &Descriptor,
    public_inputs: &[Fp],
    log_blowup: u32,
    num_queries: usize,
    proof: &SuccinctFactoredGateProof,
) -> Result<bool, SuccinctFactoredGateError> {
    let shape = validate_verifier_instance(descriptor, public_inputs, log_blowup, num_queries)?;
    if proof.outer_rounds.len() != shape.outer_rounds
        || proof.trace_linear_statement.table_root != proof.trace_root
        || proof.trace_linear_statement.log_variables as usize
            != shape.trace_table_len.trailing_zeros() as usize
        || proof.trace_linear_statement.log_blowup != log_blowup
        || proof.trace_linear_statement.num_queries != num_queries
        || !sampled_initial_values_are_base(&proof.trace_linear_proof, num_queries)
    {
        return Ok(false);
    }

    let mut transcript =
        start_transcript(descriptor, public_inputs, shape, log_blowup, num_queries)?;
    <Ext6Transcript<BinaryShakeExt6Backend> as MleTerminalTranscript>::observe_initial(
        &mut transcript,
        <BinaryShake256V1 as HashSuite>::SUITE_ID,
        shape.trace_table_len.trailing_zeros(),
        log_blowup,
        shape.trace_table_len << log_blowup,
        &proof.trace_root,
    )?;
    let gamma = transcript.squeeze_ext6(GAMMA_DOMAIN)?;

    let mut running = Ext6::ZERO;
    let mut outer_challenges = Vec::with_capacity(shape.outer_rounds);
    for (round, message) in proof.outer_rounds.iter().enumerate() {
        if message[0].add(message[1]) != running {
            return Ok(false);
        }
        absorb_outer_round(&mut transcript, round, message)?;
        let challenge = transcript.squeeze_ext6(OUTER_ROUND_CHALLENGE_DOMAIN)?;
        running = evaluate_quadratic(*message, challenge);
        outer_challenges.push(challenge);
    }
    if running != proof.terminal_operands.polynomial_value() {
        return Ok(false);
    }

    absorb_terminal_operands(&mut transcript, proof.terminal_operands)?;
    let eta = transcript.squeeze_ext6(ETA_DOMAIN)?;
    let selectors = terminal_operand_selectors(descriptor, gamma, &outer_challenges)?;
    let (combined_claim, combined_weights) = aggregate_selectors(
        public_inputs,
        shape.trace_len,
        shape.trace_table_len,
        proof.terminal_operands,
        selectors,
        eta,
    );
    if proof.trace_linear_statement.claimed_value != combined_claim {
        return Ok(false);
    }
    verify_trace_linear_after_initial(
        &proof.trace_linear_statement,
        &combined_weights,
        &proof.trace_linear_proof,
        &mut transcript,
    )
    .map_err(Into::into)
}

fn sampled_initial_values_are_base(proof: &TraceLinearProof, num_queries: usize) -> bool {
    proof.table_mle_proof.queries.len() == num_queries
        && proof.table_mle_proof.queries.iter().all(|query| {
            query
                .rounds
                .first()
                .is_some_and(|opening| is_base_lift(opening.low) && is_base_lift(opening.high))
        })
}

fn is_base_lift(value: Ext6) -> bool {
    value.limbs()[1..].iter().all(|&limb| limb == 0)
}

/// Test-only adversarial constructor: it leaves the base-field gate trace
/// unchanged but commits one caller-selected Ext6 table cell.  This builds a
/// self-consistent proof used to exercise the sampled subfield check.
#[cfg(test)]
#[doc(hidden)]
#[allow(clippy::too_many_arguments)]
pub fn prove_with_extension_cell_for_test(
    descriptor: &Descriptor,
    public_inputs: &[Fp],
    trace: &[Fp],
    cell: usize,
    value: Ext6,
    log_blowup: u32,
    num_queries: usize,
) -> Result<SuccinctFactoredGateProof, SuccinctFactoredGateError> {
    let shape =
        validate_prover_instance(descriptor, public_inputs, trace, log_blowup, num_queries)?;
    if cell >= shape.trace_len || is_base_lift(value) {
        return Err(SuccinctFactoredGateError::Instance(
            "test extension override must target a trace cell with a non-base value".into(),
        ));
    }
    let mut trace_table = lifted_trace_table(trace, shape.trace_table_len);
    trace_table[cell] = value;
    prove_with_trace_table(
        descriptor,
        public_inputs,
        trace,
        trace_table,
        shape,
        log_blowup,
        num_queries,
    )
}

#[derive(Clone, Copy)]
struct InstanceShape {
    trace_len: usize,
    trace_table_len: usize,
    outer_table_len: usize,
    outer_rounds: usize,
}

fn validate_prover_instance(
    descriptor: &Descriptor,
    public_inputs: &[Fp],
    trace: &[Fp],
    log_blowup: u32,
    num_queries: usize,
) -> Result<InstanceShape, SuccinctFactoredGateError> {
    let shape = validate_verifier_instance(descriptor, public_inputs, log_blowup, num_queries)?;
    if trace.len() != shape.trace_len {
        return Err(SuccinctFactoredGateError::Instance(format!(
            "trace length {}, expected {}",
            trace.len(),
            shape.trace_len
        )));
    }
    if trace.get(..public_inputs.len()) != Some(public_inputs) {
        return Err(SuccinctFactoredGateError::Instance(
            "trace public prefix does not match the public statement".into(),
        ));
    }
    if trace.iter().any(|&value| value >= P) {
        return Err(SuccinctFactoredGateError::Instance(
            "trace contains a non-canonical BabyBear value".into(),
        ));
    }
    Ok(shape)
}

fn validate_verifier_instance(
    descriptor: &Descriptor,
    public_inputs: &[Fp],
    log_blowup: u32,
    num_queries: usize,
) -> Result<InstanceShape, SuccinctFactoredGateError> {
    descriptor
        .validate()
        .map_err(SuccinctFactoredGateError::Instance)?;
    if descriptor.p != P {
        return Err(SuccinctFactoredGateError::Instance(format!(
            "descriptor modulus {} is not BabyBear {P}",
            descriptor.p
        )));
    }
    if descriptor.n_wires == 0 || public_inputs.len() != descriptor.n_public as usize {
        return Err(SuccinctFactoredGateError::Instance(
            "public-input length or nonzero trace shape is invalid".into(),
        ));
    }
    if public_inputs.iter().any(|&value| value >= P) {
        return Err(SuccinctFactoredGateError::Instance(
            "public input is non-canonical".into(),
        ));
    }
    if num_queries == 0 || num_queries as u128 >= P as u128 {
        return Err(SuccinctFactoredGateError::Instance(
            "query count must be nonzero and fit BabyBear".into(),
        ));
    }
    let trace_len = descriptor.n_wires as usize;
    let trace_table_len = trace_len
        .max(2)
        .checked_next_power_of_two()
        .ok_or_else(|| SuccinctFactoredGateError::Instance("trace table overflow".into()))?;
    let outer_entries = descriptor
        .gates
        .len()
        .checked_add(descriptor.zeros.len())
        .ok_or_else(|| SuccinctFactoredGateError::Instance("gate table overflow".into()))?;
    let outer_table_len = outer_entries
        .checked_next_power_of_two()
        .ok_or_else(|| SuccinctFactoredGateError::Instance("gate table overflow".into()))?;
    for (value, name) in [
        (trace_len, "trace length"),
        (trace_table_len, "padded trace length"),
        (outer_entries, "constraint count"),
        (outer_table_len, "gate table length"),
    ] {
        if value as u128 >= P as u128 {
            return Err(SuccinctFactoredGateError::Instance(format!(
                "{name}={value} does not fit BabyBear"
            )));
        }
    }
    let log_variables = trace_table_len.trailing_zeros();
    if log_variables
        .checked_add(log_blowup)
        .is_none_or(|log_domain| log_domain > TWO_ADIC_BITS)
    {
        return Err(SuccinctFactoredGateError::Instance(
            "trace opening domain exceeds BabyBear two-adicity".into(),
        ));
    }
    Ok(InstanceShape {
        trace_len,
        trace_table_len,
        outer_table_len,
        outer_rounds: outer_table_len.trailing_zeros() as usize,
    })
}

fn lifted_trace_table(trace: &[Fp], table_len: usize) -> Vec<Ext6> {
    let mut table = trace
        .iter()
        .copied()
        .map(|value| Ext6::try_from_base(value).expect("validated BabyBear trace value"))
        .collect::<Vec<_>>();
    table.resize(table_len, Ext6::ZERO);
    table
}

fn aggregate_selectors(
    public_inputs: &[Fp],
    trace_len: usize,
    table_len: usize,
    operands: OperandEvaluations,
    selectors: crate::outer_factored_gate::TerminalOperandSelectors,
    eta: Ext6,
) -> (Ext6, Vec<Ext6>) {
    let operand_values = operand_array(operands);
    let forms = [
        selectors.mul_left_weighted,
        selectors.mul_right,
        selectors.mul_output_weighted,
        selectors.add_left_weighted,
        selectors.add_right_weighted,
        selectors.add_output_weighted,
        selectors.zero_weighted,
    ];
    let mut combined_claim = Ext6::ZERO;
    let mut combined_weights = vec![Ext6::ZERO; table_len];
    let mut eta_power = Ext6::ONE;
    for (value, form) in operand_values.into_iter().zip(forms) {
        combined_claim = combined_claim.add(eta_power.mul(value.sub(form.constant)));
        for (combined, weight) in combined_weights.iter_mut().zip(form.weights) {
            *combined = combined.add(eta_power.mul(weight));
        }
        eta_power = eta_power.mul(eta);
    }
    for (index, &public) in public_inputs.iter().enumerate() {
        let public = Ext6::try_from_base(public).expect("validated public BabyBear value");
        combined_claim = combined_claim.add(eta_power.mul(public));
        combined_weights[index] = combined_weights[index].add(eta_power);
        eta_power = eta_power.mul(eta);
    }
    for weight in &mut combined_weights[trace_len..] {
        *weight = weight.add(eta_power);
        eta_power = eta_power.mul(eta);
    }
    (combined_claim, combined_weights)
}

fn operand_array(values: OperandEvaluations) -> [Ext6; 7] {
    [
        values.mul_left_weighted,
        values.mul_right,
        values.mul_output_weighted,
        values.add_left_weighted,
        values.add_right_weighted,
        values.add_output_weighted,
        values.zero_weighted,
    ]
}

fn start_transcript(
    descriptor: &Descriptor,
    public_inputs: &[Fp],
    shape: InstanceShape,
    log_blowup: u32,
    num_queries: usize,
) -> Result<Ext6Transcript<BinaryShakeExt6Backend>, SuccinctFactoredGateError> {
    let mut transcript = Ext6Transcript::new(BinaryShakeExt6Backend::new(BACKEND_LABEL))?;
    transcript.absorb_record(
        STATEMENT_HEADER_DOMAIN,
        &[
            1,
            descriptor.p & 0xffff,
            descriptor.p >> 16,
            descriptor.n_public as Fp,
            descriptor.n_vars as Fp,
            descriptor.n_wires as Fp,
            descriptor.gates.len() as Fp,
            descriptor.zeros.len() as Fp,
            shape.trace_len as Fp,
            shape.trace_table_len as Fp,
            shape.outer_table_len as Fp,
            log_blowup as Fp,
            num_queries as Fp,
        ],
    )?;
    for (index, gate) in descriptor.gates.iter().enumerate() {
        let a = wire_fields(gate.a);
        let b = wire_fields(gate.b);
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
    for (index, &wire) in descriptor.zeros.iter().enumerate() {
        let encoded = wire_fields(wire);
        transcript.absorb_record(
            STATEMENT_ZERO_DOMAIN,
            &[index as Fp, encoded[0], encoded[1]],
        )?;
    }
    transcript.absorb_record(STATEMENT_PUBLIC_DOMAIN, public_inputs)?;
    Ok(transcript)
}

fn absorb_outer_round(
    transcript: &mut Ext6Transcript<BinaryShakeExt6Backend>,
    round: usize,
    message: &[Ext6; 3],
) -> Result<(), SuccinctFactoredGateError> {
    transcript.absorb_record(OUTER_ROUND_META_DOMAIN, &[round as Fp, 2])?;
    transcript.absorb_ext6_record(OUTER_ROUND_MESSAGE_DOMAIN, message)?;
    Ok(())
}

fn absorb_terminal_operands(
    transcript: &mut Ext6Transcript<BinaryShakeExt6Backend>,
    operands: OperandEvaluations,
) -> Result<(), SuccinctFactoredGateError> {
    transcript.absorb_ext6_record(TERMINAL_VALUES_DOMAIN, &operand_array(operands))?;
    Ok(())
}

fn wire_fields(wire: Wire) -> [Fp; 2] {
    match wire {
        Wire::Const(value) => [0, value],
        Wire::Wire(index) => [1, index as Fp],
    }
}
