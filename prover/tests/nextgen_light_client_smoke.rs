use minidregg_prover::{
    additive_ntt::forward,
    binary_evaluation_claim::prove_evaluation_claim,
    binary_evaluation_history_append::{
        prove_binary_evaluation_history_append, BinaryEvaluationHistoryAppendStatement,
    },
    binary_tower::TowerElem,
    descriptor::{Descriptor, Gate, GateOp, Wire},
    field4::P,
};

// Path-load the new module until its one-line lib integration lands.
mod binary_evaluation_claim {
    pub use minidregg_prover::binary_evaluation_claim::*;
}
mod binary_evaluation_history_append {
    pub use minidregg_prover::binary_evaluation_history_append::*;
}
mod binary_hash {
    pub use minidregg_prover::binary_hash::*;
}
mod binary_history_append {
    pub use minidregg_prover::binary_history_append::*;
}
mod binary_tower {
    pub use minidregg_prover::binary_tower::*;
}
mod descriptor {
    pub use minidregg_prover::descriptor::*;
}
mod field4 {
    pub use minidregg_prover::field4::*;
}
mod succinct_factored_gate {
    pub use minidregg_prover::succinct_factored_gate::*;
}
#[path = "../src/nextgen_light_client.rs"]
mod nextgen_light_client;

use nextgen_light_client::{
    encode_nextgen_public_inputs, prove_nextgen_light_client, verify_nextgen_light_client,
};

fn e(bits: u64) -> TowerElem {
    TowerElem::new(6, bits).unwrap()
}

struct BinaryFixture {
    statement: BinaryEvaluationHistoryAppendStatement,
    left_word: Vec<TowerElem>,
    left_coefficients: Vec<TowerElem>,
    right_word: Vec<TowerElem>,
    right_coefficients: Vec<TowerElem>,
}

fn binary_fixture(seed: u64) -> BinaryFixture {
    let log_domain = 3;
    let word_len = 1usize << log_domain;
    let bound = 4;
    let queries = 2;
    let basis = (0..log_domain)
        .map(|index| e(1u64 << index))
        .collect::<Vec<_>>();
    let offset = e(0xd6e8_feb8_6659_fd93);
    let point = e(1 << 12);
    let mut left_coefficients = vec![e(0); word_len];
    let mut right_coefficients = vec![e(0); word_len];
    for index in 0..bound {
        left_coefficients[index] = e((index as u64 + seed).wrapping_mul(0x9e37_79b9_7f4a_7c15));
        right_coefficients[index] =
            e((index as u64 + seed + 17).wrapping_mul(0xbf58_476d_1ce4_e5b9));
    }
    let left_word = forward(&left_coefficients, &basis, offset).unwrap();
    let right_word = forward(&right_coefficients, &basis, offset).unwrap();
    let (left, _) =
        prove_evaluation_claim(&left_coefficients, &basis, offset, bound, point, queries).unwrap();
    let (right, _) =
        prove_evaluation_claim(&right_coefficients, &basis, offset, bound, point, queries).unwrap();
    BinaryFixture {
        statement: BinaryEvaluationHistoryAppendStatement { left, right },
        left_word,
        left_coefficients,
        right_word,
        right_coefficients,
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

#[test]
fn nextgen_light_client_conjoins_binary_and_gate_and_rejects_both_splice_directions() {
    let a = binary_fixture(3);
    let b = binary_fixture(29);
    let preview_a = prove_binary_evaluation_history_append(
        &a.statement,
        &a.left_word,
        &a.left_coefficients,
        &a.right_word,
        &a.right_coefficients,
    )
    .unwrap();
    let preview_b = prove_binary_evaluation_history_append(
        &b.statement,
        &b.left_word,
        &b.left_coefficients,
        &b.right_word,
        &b.right_coefficients,
    )
    .unwrap();
    let public_a = encode_nextgen_public_inputs(&a.statement, preview_a.output_claim()).unwrap();
    let public_b = encode_nextgen_public_inputs(&b.statement, preview_b.output_claim()).unwrap();
    assert_eq!(public_a.len(), public_b.len());
    assert_ne!(public_a, public_b);

    let (descriptor, trace_a) = gate_instance(&public_a);
    let (_, trace_b) = gate_instance(&public_b);
    let proof_a = prove_nextgen_light_client(
        &a.statement,
        &descriptor,
        &trace_a,
        1,
        2,
        &a.left_word,
        &a.left_coefficients,
        &a.right_word,
        &a.right_coefficients,
    )
    .unwrap();
    let proof_b = prove_nextgen_light_client(
        &b.statement,
        &descriptor,
        &trace_b,
        1,
        2,
        &b.left_word,
        &b.left_coefficients,
        &b.right_word,
        &b.right_coefficients,
    )
    .unwrap();
    assert!(verify_nextgen_light_client(&a.statement, &descriptor, 1, 2, &proof_a).unwrap());
    assert!(verify_nextgen_light_client(&b.statement, &descriptor, 1, 2, &proof_b).unwrap());

    let mut gate_from_different_binary_metadata = proof_a.clone();
    gate_from_different_binary_metadata.gate = proof_b.gate.clone();
    assert!(!verify_nextgen_light_client(
        &a.statement,
        &descriptor,
        1,
        2,
        &gate_from_different_binary_metadata,
    )
    .unwrap());

    let mut binary_under_another_gate_root = proof_a;
    binary_under_another_gate_root.binary = proof_b.binary;
    assert!(!verify_nextgen_light_client(
        &b.statement,
        &descriptor,
        1,
        2,
        &binary_under_another_gate_root,
    )
    .unwrap());
}
