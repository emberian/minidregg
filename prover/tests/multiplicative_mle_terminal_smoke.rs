use minidregg_prover::{
    binary_hash::{BinaryRoot, BinaryShake256V1},
    field4::badd,
    field6::Ext6,
    multiplicative_mle_terminal::{verify_mle_terminal, MleTerminalProverState},
    sumcheck_generic::evaluate_mle,
    transcript_ext6::{BinaryShakeExt6Backend, Ext6Transcript},
};

const BACKEND_LABEL: &[u8] = b"multiplicative-mle-terminal-smoke";

fn e(limbs: [u64; 6]) -> Ext6 {
    Ext6::try_from_limbs(limbs).unwrap()
}

fn bump(value: Ext6) -> Ext6 {
    let mut limbs = *value.limbs();
    limbs[0] = badd(limbs[0], 1);
    e(limbs)
}

fn bump_root(root: BinaryRoot) -> BinaryRoot {
    let mut bytes = root.into_bytes();
    bytes[0] ^= 1;
    BinaryRoot::from_bytes(bytes)
}

#[test]
fn committed_mle_terminal_interleaves_binds_and_rejects_tampers() {
    let table = (0..8)
        .map(|i| {
            e([
                (17 * i + 3) as u64,
                (5 * i * i + 1) as u64,
                (11 * i + 7) as u64,
                0,
                0,
                0,
            ])
        })
        .collect::<Vec<_>>();
    let point = vec![
        e([19, 2, 0, 0, 0, 0]),
        e([23, 0, 3, 0, 0, 0]),
        e([29, 0, 0, 5, 0, 0]),
    ];
    let terminal = evaluate_mle(&table, &point).unwrap();
    let mut prover_transcript =
        Ext6Transcript::new(BinaryShakeExt6Backend::new(BACKEND_LABEL)).unwrap();
    let mut state =
        MleTerminalProverState::commit_initial(&table, 2, BinaryShake256V1, &mut prover_transcript)
            .unwrap();
    let input_root = state.input_root();
    for &challenge in &point {
        state.bind(challenge, &mut prover_transcript).unwrap();
    }
    let (statement, proof) = state.finish(terminal, 4, &mut prover_transcript).unwrap();
    assert_eq!(statement.input_root, input_root);
    assert_eq!(proof.roots.len(), point.len() + 1);
    assert_eq!(proof.queries.len(), statement.num_queries);
    assert!(proof
        .queries
        .iter()
        .all(|query| query.rounds.len() == point.len()));

    let verify = |statement, point: &[Ext6], proof| {
        let mut transcript =
            Ext6Transcript::new(BinaryShakeExt6Backend::new(BACKEND_LABEL)).unwrap();
        verify_mle_terminal(statement, point, proof, &BinaryShake256V1, &mut transcript)
    };
    assert!(verify(&statement, &point, &proof));

    let mut bad = proof.clone();
    bad.queries[0].rounds[0].low = bump(bad.queries[0].rounds[0].low);
    assert!(!verify(&statement, &point, &bad));
    let mut bad = proof.clone();
    bad.roots[1] = bump_root(bad.roots[1]);
    assert!(!verify(&statement, &point, &bad));
    let mut bad_statement = statement.clone();
    bad_statement.claimed_terminal = bump(bad_statement.claimed_terminal);
    assert!(!verify(&bad_statement, &point, &proof));
    let mut bad_point = point.clone();
    bad_point[1] = bump(bad_point[1]);
    assert!(!verify(&statement, &bad_point, &proof));
}
