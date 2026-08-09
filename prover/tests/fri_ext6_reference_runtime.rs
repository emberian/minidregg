//! Focused smoke tests for sampled multiplicative FRI over BabyBear⁶.

use minidregg_prover::{
    binary_hash::{BinaryRoot, BinaryShake256V1},
    field4::{badd, P},
    field6::Ext6,
    fri_ext6_reference::{
        ext6_leaf_payload, prove_base_sampled, verify_sampled, Ext6FriProof, Ext6FriStatement,
        EXT6_LEAF_BYTES,
    },
    transcript_ext6::BinaryShakeExt6Backend,
};

const BACKEND_LABEL: &[u8] = b"fri-ext6-reference-smoke";

fn fixture() -> (Ext6FriStatement, Ext6FriProof) {
    let coefficients = (0..16)
        .map(|index| (index * index + 3 * index + 11) as u64)
        .collect::<Vec<_>>();
    let mut backend = BinaryShakeExt6Backend::new(BACKEND_LABEL);
    prove_base_sampled(
        &coefficients,
        6,  // domain size 64
        16, // exact rate 1/4
        3,  // final length 8, final degree bound 2
        6,
        &BinaryShake256V1,
        &mut backend,
    )
    .unwrap()
}

fn verify(statement: &Ext6FriStatement, proof: &Ext6FriProof) -> bool {
    let mut backend = BinaryShakeExt6Backend::new(BACKEND_LABEL);
    verify_sampled(statement, proof, &BinaryShake256V1, &mut backend)
}

fn bump(value: Ext6, lane: usize) -> Ext6 {
    let mut limbs = *value.limbs();
    limbs[lane] = badd(limbs[lane], 1);
    Ext6::try_from_limbs(limbs).unwrap()
}

fn bump_root(root: BinaryRoot) -> BinaryRoot {
    let mut bytes = root.into_bytes();
    bytes[7] ^= 1;
    BinaryRoot::from_bytes(bytes)
}

#[test]
fn sampled_ext6_fri_round_trip_and_leaf_format() {
    let (statement, proof) = fixture();
    assert!(verify(&statement, &proof));
    assert_eq!(statement.degree_bound, 16);
    assert_eq!(1usize << statement.log_domain, 64);
    assert_eq!(proof.roots.len(), 4);
    assert_eq!(proof.final_coefficients.len(), 2);
    assert_eq!(proof.queries.len(), 6);

    let opening = &proof.queries[0].rounds[0];
    let payload = ext6_leaf_payload(opening.low);
    assert_eq!(payload.len(), EXT6_LEAF_BYTES);
    assert_eq!(&payload[..4], b"E6L1");
    for (lane, &coefficient) in opening.low.limbs().iter().enumerate() {
        assert_eq!(
            &payload[4 + 4 * lane..8 + 4 * lane],
            &(coefficient as u32).to_le_bytes()
        );
    }

    // Level zero is a lifted BabyBear word; after one non-base beta, the
    // committed fold genuinely occupies extension lanes.
    assert!(proof.queries.iter().any(|query| {
        let round = &query.rounds[1];
        round.low.limbs()[1..].iter().any(|&lane| lane != 0)
            || round.high.limbs()[1..].iter().any(|&lane| lane != 0)
    }));
}

#[test]
fn degree_rate_final_polynomial_and_roots_are_bound() {
    let (statement, proof) = fixture();

    let mut changed_rate = statement.clone();
    changed_rate.degree_bound = 15; // same final coefficient count, different bound/transcript
    assert!(!verify(&changed_rate, &proof));

    let mut changed_input = statement.clone();
    changed_input.input_root = bump_root(changed_input.input_root);
    assert!(!verify(&changed_input, &proof));

    let mut changed_round_root = proof.clone();
    changed_round_root.roots[1] = bump_root(changed_round_root.roots[1]);
    assert!(!verify(&statement, &changed_round_root));

    for coefficient in 0..proof.final_coefficients.len() {
        for lane in 0..6 {
            let mut changed_final = proof.clone();
            changed_final.final_coefficients[coefficient] =
                bump(changed_final.final_coefficients[coefficient], lane);
            assert!(!verify(&statement, &changed_final));
        }
    }
}

#[test]
fn sampled_values_paths_and_shapes_reject_tampering() {
    let (statement, proof) = fixture();

    for round in 0..statement.fold_rounds {
        for lane in 0..6 {
            let mut changed_value = proof.clone();
            let opening = &mut changed_value.queries[0].rounds[round];
            opening.low = bump(opening.low, lane);
            assert!(!verify(&statement, &changed_value));
        }
    }

    let mut changed_path = proof.clone();
    changed_path.queries[0].rounds[0].high_path.siblings[0] =
        bump_root(changed_path.queries[0].rounds[0].high_path.siblings[0]);
    assert!(!verify(&statement, &changed_path));

    let mut short_path = proof.clone();
    short_path.queries[0].rounds[0].low_path.siblings.pop();
    assert!(!verify(&statement, &short_path));

    let mut short_roots = proof.clone();
    short_roots.roots.pop();
    assert!(!verify(&statement, &short_roots));

    let mut noncanonical_base = BinaryShakeExt6Backend::new(BACKEND_LABEL);
    assert!(prove_base_sampled(
        &[1, P],
        3,
        2,
        1,
        1,
        &BinaryShake256V1,
        &mut noncanonical_base,
    )
    .is_err());
}
