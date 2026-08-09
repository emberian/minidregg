//! One focused two-node chain/splice smoke for proof-carrying semantic history.

use minidregg_prover::{
    additive_mle_terminal::{additive_mle_initial_word_with_blowup, commit_additive_mle_word},
    binary_functional_append::{
        binary_functional_channel_id, fold_binary_functional_tables,
        prove_binary_functional_append, BinaryFunctionalAppendStatement, BinaryFunctionalClaim,
    },
    binary_hash::BinaryShake256V1,
    binary_tower::TowerElem,
    descriptor::{Descriptor, Gate, GateOp, Wire},
    field4::P,
    functional_nextgen_receipt::encode_functional_nextgen_public_inputs,
    proof_carrying_history::{prove_functional_history_node, verify_functional_history_node},
    semantic_receipt::semantic_id,
    trace_linear_gf2::{linear_functional_value_gf2, TraceLinearGf2Statement},
};

const CHANNEL_LABEL: &[u8] = b"semantic-computer/state-functional/v1";
const FUNCTIONAL_LOG_BLOWUP: u32 = 2;
const FUNCTIONAL_QUERIES: usize = 3;
const GATE_LOG_BLOWUP: u32 = 1;
const GATE_QUERIES: usize = 2;

fn e(bits: u64) -> TowerElem {
    TowerElem::new(6, bits).unwrap()
}

fn claim(
    table: &[TowerElem],
    weights: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
) -> BinaryFunctionalClaim {
    let word =
        additive_mle_initial_word_with_blowup(table, basis, offset, FUNCTIONAL_LOG_BLOWUP).unwrap();
    BinaryFunctionalClaim {
        channel_id: binary_functional_channel_id(CHANNEL_LABEL, weights, basis, offset).unwrap(),
        linear: TraceLinearGf2Statement {
            table_root: commit_additive_mle_word(&word, &BinaryShake256V1)
                .unwrap()
                .root(),
            log_blowup: FUNCTIONAL_LOG_BLOWUP,
            basis: basis.to_vec(),
            offset,
            claimed_value: linear_functional_value_gf2(table, weights).unwrap(),
            num_queries: FUNCTIONAL_QUERIES,
        },
    }
}

fn gate_instance(public_inputs: &[u64]) -> (Descriptor, Vec<u64>) {
    let n_public = u32::try_from(public_inputs.len()).unwrap();
    let private = if public_inputs[0] == 0 {
        0
    } else {
        P - public_inputs[0]
    };
    let output = n_public + 1;
    let descriptor = Descriptor {
        p: P,
        n_public,
        n_vars: n_public + 1,
        n_wires: n_public + 2,
        gates: vec![Gate {
            op: GateOp::Add,
            a: Wire::Wire(0),
            b: Wire::Wire(n_public),
            out: output,
        }],
        zeros: vec![Wire::Wire(output)],
    };
    let mut trace = public_inputs.to_vec();
    trace.extend([private, 0]);
    (descriptor, trace)
}

fn gate_for(
    statement: &BinaryFunctionalAppendStatement,
    left: &[TowerElem],
    right: &[TowerElem],
    weights: &[TowerElem],
) -> (Descriptor, Vec<u64>) {
    let preview =
        prove_binary_functional_append(statement, left, right, weights, CHANNEL_LABEL).unwrap();
    let public = encode_functional_nextgen_public_inputs(
        statement,
        &preview.output,
        weights,
        CHANNEL_LABEL,
        GATE_LOG_BLOWUP,
        GATE_QUERIES,
    )
    .unwrap();
    gate_instance(&public)
}

#[test]
fn verified_native_proofs_form_one_canonical_two_node_history() {
    let history_domain = semantic_id(b"history/semantic-computer/smoke/v1");
    let basis = [e(1), e(2), e(4), e(8), e(16)];
    let offset = e(0x6a09_e667_f3bc_c908);
    let weights = (0..8)
        .map(|i| e((i as u64 + 7).wrapping_mul(0x94d0_49bb_1331_11eb)))
        .collect::<Vec<_>>();
    let left = (0..8)
        .map(|i| e((i as u64 + 3).wrapping_mul(0x9e37_79b9_7f4a_7c15)))
        .collect::<Vec<_>>();
    let right0 = (0..8)
        .map(|i| e((i as u64 + 19).wrapping_mul(0xbf58_476d_1ce4_e5b9)))
        .collect::<Vec<_>>();
    let statement0 = BinaryFunctionalAppendStatement {
        left: claim(&left, &weights, &basis, offset),
        right: claim(&right0, &weights, &basis, offset),
    };
    let (descriptor0, trace0) = gate_for(&statement0, &left, &right0, &weights);
    let node0 = prove_functional_history_node(
        None,
        history_domain,
        semantic_id(b"turn/0"),
        &statement0,
        &weights,
        CHANNEL_LABEL,
        &left,
        &right0,
        &descriptor0,
        &trace0,
        GATE_LOG_BLOWUP,
        GATE_QUERIES,
    )
    .unwrap();
    assert!(verify_functional_history_node(
        None,
        history_domain,
        semantic_id(b"turn/0"),
        &statement0,
        &weights,
        CHANNEL_LABEL,
        &descriptor0,
        GATE_LOG_BLOWUP,
        GATE_QUERIES,
        &node0,
    )
    .unwrap());

    let accumulated0 =
        fold_binary_functional_tables(&statement0, &left, &right0, &weights, CHANNEL_LABEL)
            .unwrap();
    let right1 = (0..8)
        .map(|i| e((i as u64 + 41).wrapping_mul(0xd6e8_feb8_6659_fd93)))
        .collect::<Vec<_>>();
    let statement1 = BinaryFunctionalAppendStatement {
        left: node0.proof.functional.output.clone(),
        right: claim(&right1, &weights, &basis, offset),
    };
    let (descriptor1, trace1) = gate_for(&statement1, &accumulated0, &right1, &weights);
    let node1 = prove_functional_history_node(
        Some(&node0.envelope),
        history_domain,
        semantic_id(b"turn/1"),
        &statement1,
        &weights,
        CHANNEL_LABEL,
        &accumulated0,
        &right1,
        &descriptor1,
        &trace1,
        GATE_LOG_BLOWUP,
        GATE_QUERIES,
    )
    .unwrap();
    assert!(verify_functional_history_node(
        Some(&node0.envelope),
        history_domain,
        semantic_id(b"turn/1"),
        &statement1,
        &weights,
        CHANNEL_LABEL,
        &descriptor1,
        GATE_LOG_BLOWUP,
        GATE_QUERIES,
        &node1,
    )
    .unwrap());
    assert_eq!(node1.envelope.sequence, 1);
    assert_eq!(
        node1.envelope.previous_envelope,
        Some(node0.envelope.envelope_id().unwrap())
    );

    // A proof valid for the predecessor cannot be spliced under this node's
    // statement or canonical envelope.
    let mut proof_splice = node1.clone();
    proof_splice.proof = node0.proof.clone();
    assert!(!verify_functional_history_node(
        Some(&node0.envelope),
        history_domain,
        semantic_id(b"turn/1"),
        &statement1,
        &weights,
        CHANNEL_LABEL,
        &descriptor1,
        GATE_LOG_BLOWUP,
        GATE_QUERIES,
        &proof_splice,
    )
    .unwrap());

    // Canonical metadata and exact lane parameters are part of the accepted
    // statement, not advisory receipt decoration.
    let mut metadata_splice = node1.clone();
    metadata_splice.envelope.turn_id = semantic_id(b"turn/unrelated");
    assert!(!verify_functional_history_node(
        Some(&node0.envelope),
        history_domain,
        semantic_id(b"turn/1"),
        &statement1,
        &weights,
        CHANNEL_LABEL,
        &descriptor1,
        GATE_LOG_BLOWUP,
        GATE_QUERIES,
        &metadata_splice,
    )
    .unwrap());
    let mut dialect_splice = node1;
    dialect_splice.envelope.lanes[0].key.fold.transcript_id = semantic_id(b"transcript/other");
    assert!(!verify_functional_history_node(
        Some(&node0.envelope),
        history_domain,
        semantic_id(b"turn/1"),
        &statement1,
        &weights,
        CHANNEL_LABEL,
        &descriptor1,
        GATE_LOG_BLOWUP,
        GATE_QUERIES,
        &dialect_splice,
    )
    .unwrap());
}
