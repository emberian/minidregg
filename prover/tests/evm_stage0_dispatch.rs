//! Stage 0 (EVM u256 add) through the generated native seam: the Rust reply for work
//! `9103` is byte-identical to the Lean-written witness vectors
//! (`prover/testdata/evm_stage0_add_witness_v{1..5}.json`, authored by the `#eval` in
//! `Compiler/DescriptorEval.lean`; each vector is accepted there by the compiled
//! `descriptorHoldsCheck`, and `evmAddCandidate_holds` is the theorem behind it).
//!
//! Vector agreement, NOT verification.  There is no semantics of Rust here: the generated
//! `WORK_2_ROWS` table is the Lean descriptor's gate list rendered as data, and these
//! tests say the opaque evaluator reproduces Lean's `fillAux` on these five vectors and
//! turns the local error shapes into errors rather than replies.  Nothing here decides
//! descriptor satisfaction — `descriptorHoldsCheck` does, on the Lean side of the plan.

use std::path::Path;

use serde::Deserialize;

use minidregg_prover::babybear::P;
use minidregg_prover::evm_stage0_add_aux::{
    dispatch_native, NativeErrorKind, NativeWorkRequestDto, WORK_2_CARRIER_PROFILE_ID_DECIMAL,
    WORK_2_DESCRIPTOR_N_PUBLIC, WORK_2_DESCRIPTOR_N_VARS, WORK_2_DESCRIPTOR_N_WIRES,
    WORK_2_FIELD_MODULUS, WORK_2_ID_DECIMAL, WORK_2_REQUEST_CODEC_ID_DECIMAL,
    WORK_2_REQUEST_WIRE_COUNT, WORK_2_REQUEST_WIRE_WIDTH, WORK_2_RESPONSE_CODEC_ID_DECIMAL,
    WORK_2_RESPONSE_WIDTH, WORK_2_ROWS, WORK_2_ZEROS,
};
use minidregg_prover::native_dispatch::{evaluate_descriptor_rows, NativeDispatchError};

/// Mirror of the witness file Lane A's `#eval` writes — exactly these eleven keys
/// (`deny_unknown_fields`).  `x`/`y`/`z` are hex strings (256-bit values do not fit a JSON
/// integer) and label the vector; `wires` are the 4,131 canonical words, of which the first
/// `nVars` = 833 are the request and all 4,131 are the expected reply.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct WitnessFile {
    p: u64,
    descriptor: String,
    vector: String,
    x: String,
    y: String,
    z: String,
    n_public: usize,
    n_vars: usize,
    n_wires: usize,
    accepted: bool,
    wires: Vec<u64>,
}

const VECTORS: [&str; 5] = ["v1", "v2", "v3", "v4", "v5"];

fn witness(name: &str) -> WitnessFile {
    let path = format!(
        "{}/testdata/evm_stage0_add_witness_{name}.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let text = std::fs::read_to_string(Path::new(&path))
        .expect("read the Lean-written Stage-0 witness file");
    let file: WitnessFile =
        serde_json::from_str(&text).expect("parse the Lean-written Stage-0 witness file");
    assert_eq!(file.p, P, "the vector is over the prover's field");
    assert_eq!(file.descriptor, "evm_stage0_add_descriptor.json");
    assert_eq!(file.vector, name);
    for label in [&file.x, &file.y, &file.z] {
        assert!(label.starts_with("0x"), "operands are hex strings");
    }
    assert_eq!(file.n_public, WORK_2_DESCRIPTOR_N_PUBLIC);
    assert_eq!(file.n_vars, WORK_2_DESCRIPTOR_N_VARS);
    assert_eq!(file.n_wires, WORK_2_DESCRIPTOR_N_WIRES);
    assert_eq!(file.wires.len(), file.n_wires);
    assert!(file.accepted, "Lean's compiled checker accepted this vector");
    assert!(file.wires.iter().all(|&w| w < P), "every word is canonical");
    file
}

fn words_le(words: &[u64]) -> Vec<u8> {
    words
        .iter()
        .flat_map(|&w| (w as u32).to_le_bytes())
        .collect()
}

fn request_for(file: &WitnessFile) -> NativeWorkRequestDto {
    NativeWorkRequestDto::from_ids(
        WORK_2_ID_DECIMAL,
        WORK_2_CARRIER_PROFILE_ID_DECIMAL,
        WORK_2_REQUEST_CODEC_ID_DECIMAL,
        WORK_2_RESPONSE_CODEC_ID_DECIMAL,
        words_le(&file.wires[..file.n_vars]).into_boxed_slice(),
    )
    .expect("the authenticated pins of work 9103 construct a request")
}

/// **Control — counts unchanged.**  The generated table is the Stage-0 descriptor's shape:
/// 3,298 rows (1,665 add + 1,633 mul), 850 zero-checks, 833 variables (48 public), 4,131
/// wires, outputs strictly increasing from 833 (the emitted SSA order), every operand kind
/// and op inside the encoding, and the transport pins of work 9103.
#[test]
fn generated_constants_pin_the_stage0_shape() {
    assert_eq!(WORK_2_ID_DECIMAL, "9103");
    assert_eq!(WORK_2_CARRIER_PROFILE_ID_DECIMAL, "206");
    assert_eq!(WORK_2_REQUEST_CODEC_ID_DECIMAL, "9007");
    assert_eq!(WORK_2_RESPONSE_CODEC_ID_DECIMAL, "9009");
    assert_eq!(WORK_2_FIELD_MODULUS, P);
    assert_eq!(WORK_2_DESCRIPTOR_N_PUBLIC, 48);
    assert_eq!(WORK_2_DESCRIPTOR_N_VARS, 833);
    assert_eq!(WORK_2_DESCRIPTOR_N_WIRES, 4131);
    assert_eq!(WORK_2_REQUEST_WIRE_WIDTH, 4);
    assert_eq!(WORK_2_REQUEST_WIRE_COUNT, WORK_2_DESCRIPTOR_N_VARS);
    assert_eq!(WORK_2_RESPONSE_WIDTH, 4 * WORK_2_DESCRIPTOR_N_WIRES);

    assert_eq!(WORK_2_ROWS.len(), 3298, "3,298 row evaluations per fill");
    let adds = WORK_2_ROWS.iter().filter(|row| row.0 == 0).count();
    let muls = WORK_2_ROWS.iter().filter(|row| row.0 == 1).count();
    assert_eq!((adds, muls), (1665, 1633));
    assert_eq!(WORK_2_ZEROS.len(), 850, "850 boundary pins, for Lean's checker");

    let mut previous_out = WORK_2_DESCRIPTOR_N_VARS as u32 - 1;
    for (row, &(op, a_kind, a, b_kind, b, out)) in WORK_2_ROWS.iter().enumerate() {
        assert!(op <= 1, "row {row}: op inside the encoding");
        assert!(a_kind <= 1 && b_kind <= 1, "row {row}: operand kinds inside the encoding");
        for (kind, operand) in [(a_kind, a), (b_kind, b)] {
            if kind == 0 {
                assert!(u64::from(operand) < P, "row {row}: canonical constant");
            } else {
                assert!(operand < out, "row {row}: reads only earlier wires (SSA)");
            }
        }
        assert!(out > previous_out, "row {row}: outputs strictly increase");
        assert!((out as usize) < WORK_2_DESCRIPTOR_N_WIRES);
        previous_out = out;
    }
    assert_eq!(previous_out as usize, WORK_2_DESCRIPTOR_N_WIRES - 1);
    for &(kind, operand) in WORK_2_ZEROS {
        assert!(kind <= 1);
        if kind == 1 {
            assert!((operand as usize) < WORK_2_DESCRIPTOR_N_WIRES);
        }
    }
}

/// **The vector agreement**: on all five Lean-authored vectors, the generated dispatch of
/// work 9103 returns bytes identical to the Lean-written 4,131 words.
#[test]
fn dispatch_reproduces_the_lean_written_wires_on_all_five_vectors() {
    for name in VECTORS {
        let file = witness(name);
        let reply = dispatch_native(request_for(&file))
            .unwrap_or_else(|error| panic!("{name}: dispatch failed: {}", error.detail));
        let expected = words_le(&file.wires);
        assert_eq!(reply.response_bytes().len(), WORK_2_RESPONSE_WIDTH, "{name}");
        assert!(
            reply.response_bytes() == &expected[..],
            "{name}: reply differs from the Lean-written wires"
        );
        // The request is echoed unchanged in the reply's variable prefix (Lean's
        // `fillAux_getD_of_lt`: variables are never overwritten).
        assert_eq!(
            &reply.response_bytes()[..4 * file.n_vars],
            &words_le(&file.wires[..file.n_vars])[..],
            "{name}: variable prefix"
        );
    }
}

/// The generated constructor refuses an unregistered work id and any drift in the pins.
#[test]
fn unregistered_work_id_and_wrong_pins_are_refused_by_the_generated_constructor() {
    let bytes = words_le(&witness("v1").wires[..WORK_2_DESCRIPTOR_N_VARS]);
    let unregistered = NativeWorkRequestDto::from_ids(
        "9104",
        WORK_2_CARRIER_PROFILE_ID_DECIMAL,
        WORK_2_REQUEST_CODEC_ID_DECIMAL,
        WORK_2_RESPONSE_CODEC_ID_DECIMAL,
        bytes.clone().into_boxed_slice(),
    )
    .unwrap_err();
    assert_eq!(unregistered.kind, NativeErrorKind::UnsupportedWork);

    let wrong_carrier = NativeWorkRequestDto::from_ids(
        WORK_2_ID_DECIMAL,
        "205",
        WORK_2_REQUEST_CODEC_ID_DECIMAL,
        WORK_2_RESPONSE_CODEC_ID_DECIMAL,
        bytes.into_boxed_slice(),
    )
    .unwrap_err();
    assert_eq!(wrong_carrier.kind, NativeErrorKind::MalformedRequest);
}

/// Local error shapes are errors, never replies: a short request, a non-canonical word,
/// and — at the generic evaluator with tiny hand tables — a read before write, a rewrite,
/// an unwritten wire, and a foreign modulus.
#[test]
fn local_error_shapes_are_errors_not_verdicts() {
    let file = witness("v1");
    let mut words = file.wires[..file.n_vars].to_vec();

    let short = NativeWorkRequestDto::evm_stage0_add_aux(
        words_le(&words[..words.len() - 1]).into_boxed_slice(),
    );
    assert_eq!(dispatch_native(short).unwrap_err().kind, NativeErrorKind::ExecutionFailure);

    words[0] = P;
    let above = NativeWorkRequestDto::evm_stage0_add_aux(words_le(&words).into_boxed_slice());
    let failure = dispatch_native(above).unwrap_err();
    assert_eq!(failure.kind, NativeErrorKind::ExecutionFailure);
    assert!(failure.detail.contains("not a canonical residue"), "{}", failure.detail);

    let one_var = words_le(&[7]);
    // wire 1 <- wire 0 + wire 2, but wire 2 is never written.
    let read_before_write: [(u8, u8, u32, u8, u32, u32); 1] = [(0, 1, 0, 1, 2, 1)];
    assert_eq!(
        evaluate_descriptor_rows(&read_before_write, 1, 3, P, &one_var).unwrap_err(),
        NativeDispatchError::ReadBeforeWrite { row: 0, wire: 2 }
    );
    // wire 1 <- 0 * 3 twice.
    let rewrite: [(u8, u8, u32, u8, u32, u32); 2] = [(1, 1, 0, 0, 3, 1), (1, 1, 0, 0, 3, 1)];
    assert_eq!(
        evaluate_descriptor_rows(&rewrite, 1, 2, P, &one_var).unwrap_err(),
        NativeDispatchError::Rewrite { row: 1, wire: 1 }
    );
    // Two aux wires declared, one written.
    let unwritten: [(u8, u8, u32, u8, u32, u32); 1] = [(0, 1, 0, 0, 1, 1)];
    assert_eq!(
        evaluate_descriptor_rows(&unwritten, 1, 3, P, &one_var).unwrap_err(),
        NativeDispatchError::UnwrittenWire { wire: 2 }
    );
    assert_eq!(
        evaluate_descriptor_rows(&unwritten, 1, 2, P + 2, &one_var).unwrap_err(),
        NativeDispatchError::FieldModulus { table: P + 2, kernel: P }
    );
    // The honest tiny table: 7 + 1 = 8.
    assert_eq!(
        evaluate_descriptor_rows(&unwritten, 1, 2, P, &one_var).unwrap(),
        words_le(&[7, 8])
    );
}
