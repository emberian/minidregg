//! Integration tests for the committed-accumulator reference layer.

use minidregg_prover::accumulator::{AccClaim, LinearConstraint};
use minidregg_prover::commit::{commit_trace, open};
use minidregg_prover::committed_accumulator::{
    commit_claim, commit_fold, commit_fold_fs, derive_fold_challenge, reference_rs_contains,
    verify_committed_claim, CommittedAccError, CommittedAccProof, CommittedAccRef, ReferenceRsCode,
    WordOpening,
};
use minidregg_prover::field4::{badd, bmul, two_adic_generator, P};
use minidregg_prover::poseidon::demo_spec;
use minidregg_prover::wide::Digest;

const CODE: ReferenceRsCode = ReferenceRsCode {
    log_domain: 3,
    degree_bound: 2,
};

fn rs_word(constant: u64, linear: u64) -> Vec<u64> {
    let g = two_adic_generator(CODE.log_domain);
    let mut x = 1;
    let mut word = Vec::with_capacity(1 << CODE.log_domain);
    for _ in 0..1 << CODE.log_domain {
        word.push(badd(constant, bmul(linear, x)));
        x = bmul(x, g);
    }
    word
}

fn eval_claim(word: &[u64], index: usize) -> AccClaim<()> {
    let mut weights = vec![0; word.len()];
    weights[index] = 1;
    AccClaim {
        root: (),
        word_len: word.len(),
        channel: vec![LinearConstraint {
            weights,
            target: word[index],
        }],
    }
}

fn committed(
    constant: u64,
    linear: u64,
    index: usize,
) -> (AccClaim<Digest>, CommittedAccProof, Vec<u64>) {
    let word = rs_word(constant, linear);
    let (claim, proof) = commit_claim(&eval_claim(&word, index), &word, CODE, &demo_spec(), P)
        .expect("honest committed claim");
    (claim, proof, word)
}

#[test]
fn committed_claim_round_trip_checks_every_opening_and_code_membership() {
    let (claim, proof, word) = committed(3, 5, 2);
    assert_eq!(proof.openings.len(), word.len());
    assert!(verify_committed_claim(
        &claim,
        &proof,
        CODE,
        &demo_spec(),
        P
    ));
    assert!(reference_rs_contains(&word, CODE, P).unwrap());
}

#[test]
fn value_path_root_index_and_target_tampers_reject() {
    let (claim, good, _) = committed(3, 5, 2);
    let spec = demo_spec();

    let mut proof = good.clone();
    proof.openings[2].value = (proof.openings[2].value + 1) % P;
    assert!(!verify_committed_claim(&claim, &proof, CODE, &spec, P));

    let mut proof = good.clone();
    proof.openings[4].path[1].limbs[0] = (proof.openings[4].path[1].limbs[0] + 1) % P;
    assert!(!verify_committed_claim(&claim, &proof, CODE, &spec, P));

    let mut bad_claim = claim.clone();
    bad_claim.root.limbs[3] = (bad_claim.root.limbs[3] + 1) % P;
    assert!(!verify_committed_claim(&bad_claim, &good, CODE, &spec, P));

    let mut proof = good.clone();
    proof.openings.swap(1, 2);
    assert!(!verify_committed_claim(&claim, &proof, CODE, &spec, P));

    let mut bad_claim = claim;
    bad_claim.channel[0].target = (bad_claim.channel[0].target + 1) % P;
    assert!(!verify_committed_claim(&bad_claim, &good, CODE, &spec, P));
}

#[test]
fn malformed_and_noncanonical_proof_data_reject_without_panicking() {
    let (claim, good, _) = committed(3, 5, 2);
    let spec = demo_spec();

    let mut proof = good.clone();
    proof.openings.pop();
    assert!(!verify_committed_claim(&claim, &proof, CODE, &spec, P));

    let mut proof = good.clone();
    proof.openings[0].value = P;
    assert!(!verify_committed_claim(&claim, &proof, CODE, &spec, P));

    let mut proof = good;
    proof.openings[0].path[0].limbs[8] = P;
    assert!(!verify_committed_claim(&claim, &proof, CODE, &spec, P));
}

#[test]
fn low_degree_check_rejects_a_committed_full_rate_word() {
    let word = vec![3, 1, 4, 1, 5, 9, 2, 6];
    let full_rate = ReferenceRsCode {
        log_domain: 3,
        degree_bound: 8,
    };
    let broad = AccClaim {
        root: (),
        word_len: word.len(),
        channel: vec![],
    };
    let (claim, proof) = commit_claim(&broad, &word, full_rate, &demo_spec(), P).unwrap();
    assert!(verify_committed_claim(
        &claim,
        &proof,
        full_rate,
        &demo_spec(),
        P
    ));
    assert!(!verify_committed_claim(
        &claim,
        &proof,
        CODE,
        &demo_spec(),
        P
    ));
    assert_eq!(
        commit_claim(&broad, &word, CODE, &demo_spec(), P),
        Err(CommittedAccError::NotCodeword)
    );
}

#[test]
fn committed_fold_round_trip_binds_the_folded_word() {
    let index = 2;
    let (left, left_proof, left_word) = committed(3, 5, index);
    let (right, right_proof, right_word) = committed(7, 1, index);
    let gamma = 11;
    let (folded, proof) = commit_fold(
        CommittedAccRef {
            claim: &left,
            proof: &left_proof,
        },
        CommittedAccRef {
            claim: &right,
            proof: &right_proof,
        },
        gamma,
        CODE,
        &demo_spec(),
        P,
    )
    .unwrap();
    assert!(verify_committed_claim(
        &folded,
        &proof,
        CODE,
        &demo_spec(),
        P
    ));
    for (opening, (&a, &b)) in proof.openings.iter().zip(left_word.iter().zip(&right_word)) {
        assert_eq!(opening.value, badd(a, bmul(gamma, b)));
    }
    assert_eq!(
        folded.channel[0].target,
        badd(left.channel[0].target, bmul(gamma, right.channel[0].target))
    );
}

#[test]
fn fs_fold_binds_both_complete_claims_before_deriving_gamma() {
    let index = 2;
    let (left, left_proof, left_word) = committed(3, 5, index);
    let (right, right_proof, right_word) = committed(7, 1, index);
    let spec = demo_spec();
    let replayed = derive_fold_challenge(&left, &right, &spec, P).unwrap();
    let (gamma, folded, proof) = commit_fold_fs(
        CommittedAccRef {
            claim: &left,
            proof: &left_proof,
        },
        CommittedAccRef {
            claim: &right,
            proof: &right_proof,
        },
        CODE,
        &spec,
        P,
    )
    .unwrap();
    assert_eq!(gamma, replayed);
    assert!(verify_committed_claim(&folded, &proof, CODE, &spec, P));
    for (opening, (&a, &b)) in proof.openings.iter().zip(left_word.iter().zip(&right_word)) {
        assert_eq!(opening.value, badd(a, bmul(gamma, b)));
    }

    let mut changed_target = right.clone();
    changed_target.channel[0].target = badd(changed_target.channel[0].target, 1);
    assert_ne!(
        gamma,
        derive_fold_challenge(&left, &changed_target, &spec, P).unwrap()
    );
    assert_ne!(
        gamma,
        derive_fold_challenge(&right, &left, &spec, P).unwrap()
    );
}

#[test]
fn committed_fold_refuses_a_tampered_input_and_output_tamper_rejects() {
    let (left, mut left_proof, _) = committed(3, 5, 2);
    let (right, right_proof, _) = committed(7, 1, 2);
    left_proof.openings[0].path[0].limbs[0] = (left_proof.openings[0].path[0].limbs[0] + 1) % P;
    assert_eq!(
        commit_fold(
            CommittedAccRef {
                claim: &left,
                proof: &left_proof,
            },
            CommittedAccRef {
                claim: &right,
                proof: &right_proof,
            },
            11,
            CODE,
            &demo_spec(),
            P,
        ),
        Err(CommittedAccError::InvalidInputProof("left"))
    );

    let (left, left_proof, _) = committed(3, 5, 2);
    let (mut folded, proof) = commit_fold(
        CommittedAccRef {
            claim: &left,
            proof: &left_proof,
        },
        CommittedAccRef {
            claim: &right,
            proof: &right_proof,
        },
        11,
        CODE,
        &demo_spec(),
        P,
    )
    .unwrap();
    folded.root.limbs[0] = (folded.root.limbs[0] + 1) % P;
    assert!(!verify_committed_claim(
        &folded,
        &proof,
        CODE,
        &demo_spec(),
        P
    ));
}

#[test]
fn forged_opening_shape_does_not_substitute_for_full_reference_resolution() {
    let (claim, proof, _) = committed(3, 5, 2);
    let one = proof.openings[0].clone();
    let forged = CommittedAccProof {
        openings: vec![WordOpening {
            index: 0,
            value: one.value,
            path: one.path,
        }],
    };
    assert!(!verify_committed_claim(
        &claim,
        &forged,
        CODE,
        &demo_spec(),
        P
    ));
}

#[test]
fn direct_merkle_fixture_agrees_with_protocol_root() {
    let (_, _, word) = committed(3, 5, 2);
    let (root, tree) = commit_trace(&demo_spec(), &word, P);
    let proof = CommittedAccProof {
        openings: word
            .iter()
            .enumerate()
            .map(|(index, &value)| WordOpening {
                index,
                value,
                path: open(&tree, index),
            })
            .collect(),
    };
    let mut weights = vec![0; word.len()];
    weights[2] = 1;
    let claim = AccClaim {
        root,
        word_len: word.len(),
        channel: vec![LinearConstraint {
            weights,
            target: word[2],
        }],
    };
    assert!(verify_committed_claim(
        &claim,
        &proof,
        CODE,
        &demo_spec(),
        P
    ));
}
