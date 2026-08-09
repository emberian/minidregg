use minidregg_prover::{
    binary_hash::BinaryShake256V1,
    descriptor::{Descriptor, Gate, GateOp, Wire},
    field4::{badd, P},
    field6::Ext6,
    gate_mle_ext6::{prove_gate_mle_ext6, verify_gate_mle_ext6},
    multiplicative_mle_terminal::MleTerminalProverState,
    sumcheck_generic::evaluate_mle,
    transcript_ext6::{BinaryShakeExt6Backend, Ext6Transcript},
};

fn descriptor() -> Descriptor {
    let descriptor = Descriptor {
        p: P,
        n_public: 1,
        n_vars: 1,
        n_wires: 3,
        gates: vec![
            Gate {
                op: GateOp::Add,
                a: Wire::Wire(0),
                b: Wire::Const(0),
                out: 1,
            },
            Gate {
                op: GateOp::Mul,
                a: Wire::Wire(1),
                b: Wire::Wire(0),
                out: 2,
            },
        ],
        zeros: vec![Wire::Wire(2)],
    };
    descriptor.validate().unwrap();
    descriptor
}

fn bump(value: Ext6) -> Ext6 {
    let mut limbs = *value.limbs();
    limbs[0] = badd(limbs[0], 1);
    Ext6::try_from_limbs(limbs).unwrap()
}

#[test]
fn clear_gate_mle_join_roundtrip_tampers_and_unrelated_oracle_reject() {
    let descriptor = descriptor();
    let public = [0];
    let trace = [0, 0, 0];
    let proof = prove_gate_mle_ext6(&descriptor, &public, &trace, 2, 4).unwrap();
    assert_eq!(proof.sumcheck.rounds.len(), 2);
    assert_eq!(proof.mle_proof.roots.len(), 3);
    assert!(verify_gate_mle_ext6(&descriptor, &public, &trace, 2, 4, &proof).unwrap());

    let mut bad = proof.clone();
    bad.sumcheck.rounds[0][0] = bump(bad.sumcheck.rounds[0][0]);
    assert!(!verify_gate_mle_ext6(&descriptor, &public, &trace, 2, 4, &bad).unwrap());
    let mut bad = proof.clone();
    bad.mle_proof.queries[0].rounds[0].low = bump(bad.mle_proof.queries[0].rounds[0].low);
    assert!(!verify_gate_mle_ext6(&descriptor, &public, &trace, 2, 4, &bad).unwrap());

    // Build a valid, self-consistent PCS for an unrelated nonzero oracle, then
    // splice it into the gate proof. Exact clear provenance must reject before
    // that unrelated root can substitute for the recomputed defect table.
    let unrelated = vec![
        Ext6::ONE,
        Ext6::ZERO,
        Ext6::try_from_base(7).unwrap(),
        Ext6::try_from_base(11).unwrap(),
    ];
    let point = vec![
        Ext6::try_from_base(13).unwrap(),
        Ext6::try_from_base(17).unwrap(),
    ];
    let terminal = evaluate_mle(&unrelated, &point).unwrap();
    let mut transcript = Ext6Transcript::new(BinaryShakeExt6Backend::new(
        b"gate-mle-unrelated-oracle-smoke",
    ))
    .unwrap();
    let mut state =
        MleTerminalProverState::commit_initial(&unrelated, 2, BinaryShake256V1, &mut transcript)
            .unwrap();
    for &challenge in &point {
        state.bind(challenge, &mut transcript).unwrap();
    }
    let (unrelated_statement, unrelated_proof) =
        state.finish(terminal, 4, &mut transcript).unwrap();
    let mut unrelated_gate = proof.clone();
    unrelated_gate.mle_statement = unrelated_statement;
    unrelated_gate.mle_proof = unrelated_proof;
    assert!(!verify_gate_mle_ext6(&descriptor, &public, &trace, 2, 4, &unrelated_gate,).unwrap());
}
