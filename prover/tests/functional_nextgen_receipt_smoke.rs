//! One focused conjunction/splice smoke for the functional nextgen receipt.

use minidregg_prover::{
    additive_mle_terminal::{additive_mle_initial_word_with_blowup, commit_additive_mle_word},
    binary_functional_append::{
        binary_functional_channel_id, prove_binary_functional_append,
        BinaryFunctionalAppendStatement, BinaryFunctionalClaim,
    },
    binary_hash::BinaryShake256V1,
    binary_tower::TowerElem,
    descriptor::{Descriptor, Gate, GateOp, Wire},
    field4::P,
    trace_linear_gf2::{linear_functional_value_gf2, TraceLinearGf2Statement},
};

mod binary_functional_append {
    pub use minidregg_prover::binary_functional_append::*;
}
mod binary_hash {
    pub use minidregg_prover::binary_hash::*;
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
#[path = "../src/functional_nextgen_receipt.rs"]
mod functional_nextgen_receipt;

use functional_nextgen_receipt::{
    encode_functional_nextgen_public_inputs, prove_functional_nextgen_receipt,
    verify_functional_nextgen_receipt,
};

const CHANNEL_LABEL: &[u8] = b"receipt/arbitrary-functional-nextgen/v1";
const FUNCTIONAL_LOG_BLOWUP: u32 = 2;
const FUNCTIONAL_QUERIES: usize = 3;
const GATE_LOG_BLOWUP: u32 = 1;
const GATE_QUERIES: usize = 2;

fn e(bits: u64) -> TowerElem {
    TowerElem::new(6, bits).unwrap()
}

struct FunctionalFixture {
    statement: BinaryFunctionalAppendStatement,
    left_table: Vec<TowerElem>,
    right_table: Vec<TowerElem>,
    weights: Vec<TowerElem>,
}

fn functional_fixture(seed: u64) -> FunctionalFixture {
    let basis = [e(1), e(2), e(4), e(8), e(16)];
    let offset = e(0x6a09_e667_f3bc_c908);
    let left_table = (0..8)
        .map(|index| e((index as u64 + seed + 3).wrapping_mul(0x9e37_79b9_7f4a_7c15)))
        .collect::<Vec<_>>();
    let right_table = (0..8)
        .map(|index| e((index as u64 + seed + 19).wrapping_mul(0xbf58_476d_1ce4_e5b9)))
        .collect::<Vec<_>>();
    let weights = (0..8)
        .map(|index| e((index as u64 + 11).wrapping_mul(0x94d0_49bb_1331_11eb)))
        .collect::<Vec<_>>();
    let claim = |table: &[TowerElem]| {
        let word =
            additive_mle_initial_word_with_blowup(table, &basis, offset, FUNCTIONAL_LOG_BLOWUP)
                .unwrap();
        BinaryFunctionalClaim {
            channel_id: binary_functional_channel_id(CHANNEL_LABEL, &weights, &basis, offset)
                .unwrap(),
            linear: TraceLinearGf2Statement {
                table_root: commit_additive_mle_word(&word, &BinaryShake256V1)
                    .unwrap()
                    .root(),
                log_blowup: FUNCTIONAL_LOG_BLOWUP,
                basis: basis.to_vec(),
                offset,
                claimed_value: linear_functional_value_gf2(table, &weights).unwrap(),
                num_queries: FUNCTIONAL_QUERIES,
            },
        }
    };
    FunctionalFixture {
        statement: BinaryFunctionalAppendStatement {
            left: claim(&left_table),
            right: claim(&right_table),
        },
        left_table,
        right_table,
        weights,
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
fn functional_nextgen_conjoins_rate_bearing_append_and_gate_without_splicing() {
    let a = functional_fixture(3);
    let b = functional_fixture(37);
    assert_eq!(a.statement.left.linear.log_blowup, FUNCTIONAL_LOG_BLOWUP);
    let preview_a = prove_binary_functional_append(
        &a.statement,
        &a.left_table,
        &a.right_table,
        &a.weights,
        CHANNEL_LABEL,
    )
    .unwrap();
    let preview_b = prove_binary_functional_append(
        &b.statement,
        &b.left_table,
        &b.right_table,
        &b.weights,
        CHANNEL_LABEL,
    )
    .unwrap();
    let public_a = encode_functional_nextgen_public_inputs(
        &a.statement,
        &preview_a.output,
        &a.weights,
        CHANNEL_LABEL,
        GATE_LOG_BLOWUP,
        GATE_QUERIES,
    )
    .unwrap();
    let public_b = encode_functional_nextgen_public_inputs(
        &b.statement,
        &preview_b.output,
        &b.weights,
        CHANNEL_LABEL,
        GATE_LOG_BLOWUP,
        GATE_QUERIES,
    )
    .unwrap();
    assert_eq!(public_a.len(), public_b.len());
    assert_ne!(public_a, public_b);

    let (descriptor, trace_a) = gate_instance(&public_a);
    let (_, trace_b) = gate_instance(&public_b);
    let proof_a = prove_functional_nextgen_receipt(
        &a.statement,
        &a.weights,
        CHANNEL_LABEL,
        &a.left_table,
        &a.right_table,
        &descriptor,
        &trace_a,
        GATE_LOG_BLOWUP,
        GATE_QUERIES,
    )
    .unwrap();
    let proof_b = prove_functional_nextgen_receipt(
        &b.statement,
        &b.weights,
        CHANNEL_LABEL,
        &b.left_table,
        &b.right_table,
        &descriptor,
        &trace_b,
        GATE_LOG_BLOWUP,
        GATE_QUERIES,
    )
    .unwrap();
    assert!(verify_functional_nextgen_receipt(
        &a.statement,
        &a.weights,
        CHANNEL_LABEL,
        &descriptor,
        GATE_LOG_BLOWUP,
        GATE_QUERIES,
        &proof_a,
    )
    .unwrap());

    let mut unrelated_weights = a.weights.clone();
    unrelated_weights[0] = unrelated_weights[0].add(e(1)).unwrap();
    assert!(verify_functional_nextgen_receipt(
        &a.statement,
        &unrelated_weights,
        CHANNEL_LABEL,
        &descriptor,
        GATE_LOG_BLOWUP,
        GATE_QUERIES,
        &proof_a,
    )
    .is_err());

    let mut unrelated_gate = proof_a.clone();
    unrelated_gate.gate = proof_b.gate.clone();
    assert!(!verify_functional_nextgen_receipt(
        &a.statement,
        &a.weights,
        CHANNEL_LABEL,
        &descriptor,
        GATE_LOG_BLOWUP,
        GATE_QUERIES,
        &unrelated_gate,
    )
    .unwrap());

    let mut unrelated_functional = proof_a;
    unrelated_functional.functional = proof_b.functional;
    assert!(!verify_functional_nextgen_receipt(
        &a.statement,
        &a.weights,
        CHANNEL_LABEL,
        &descriptor,
        GATE_LOG_BLOWUP,
        GATE_QUERIES,
        &unrelated_functional,
    )
    .unwrap());
}
