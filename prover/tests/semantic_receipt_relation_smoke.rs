//! One focused exhaustive join for ReceiptDelta quadratics and AccClaim fold.

use minidregg_prover::semantic_receipt::semantic_id;
use minidregg_prover::semantic_receipt_relation::{
    commit_semantic_receipt, fold_semantic_receipts, verify_committed_semantic_receipt,
    verify_folded_semantic_accumulator, SemanticReceiptRelationError, SemanticReceiptWord,
};

#[test]
fn semantic_receipt_word_is_frame_checked_committed_and_really_folded() {
    let left = commit_semantic_receipt(SemanticReceiptWord {
        binding: semantic_id(b"typed-receipt/left"),
        pre: vec![1, 2, 3, 4],
        post: vec![9, 2, 8, 4],
        touched: vec![1, 0, 1, 0],
    })
    .unwrap();
    let right = commit_semantic_receipt(SemanticReceiptWord {
        binding: semantic_id(b"typed-receipt/right"),
        pre: vec![9, 2, 8, 4],
        post: vec![9, 7, 8, 6],
        touched: vec![0, 1, 0, 1],
    })
    .unwrap();
    let encoded_left = left.word.encode_word().unwrap();
    assert_eq!(encoded_left.len(), 16 + 12);
    assert_eq!(&encoded_left[16..], &[1, 9, 1, 2, 2, 0, 3, 8, 1, 4, 4, 0]);
    assert!(left
        .word
        .quadratic_residuals()
        .unwrap()
        .iter()
        .all(|residual| *residual == [0, 0]));
    assert!(verify_committed_semantic_receipt(&left).unwrap());
    assert!(verify_committed_semantic_receipt(&right).unwrap());

    let folded = fold_semantic_receipts(&left, &right).unwrap();
    assert!(verify_folded_semantic_accumulator(&left, &right, &folded).unwrap());
    assert_eq!(folded.word.len(), left.word.encode_word().unwrap().len());

    let ghost = SemanticReceiptWord {
        binding: semantic_id(b"typed-receipt/ghost"),
        pre: vec![1, 2],
        post: vec![1, 3],
        touched: vec![0, 0],
    };
    assert_eq!(
        ghost.validate(),
        Err(SemanticReceiptRelationError::FrameViolation { index: 1 })
    );
    let nonboolean = SemanticReceiptWord {
        binding: semantic_id(b"typed-receipt/nonboolean"),
        pre: vec![1],
        post: vec![1],
        touched: vec![2],
    };
    assert_eq!(
        nonboolean.validate(),
        Err(SemanticReceiptRelationError::NonBooleanTouched { index: 0, value: 2 })
    );

    let mut root_tamper = left.clone();
    let mut bytes = root_tamper.root.into_bytes();
    bytes[0] ^= 1;
    root_tamper.root = minidregg_prover::binary_hash::BinaryRoot::from_bytes(bytes);
    assert!(!verify_committed_semantic_receipt(&root_tamper).unwrap());

    let mut claim_tamper = right.clone();
    claim_tamper.claim.channel[0].target = claim_tamper.claim.channel[0]
        .target
        .add(minidregg_prover::field6::Ext6::ONE);
    assert!(!verify_committed_semantic_receipt(&claim_tamper).unwrap());

    let mut binding_tamper = left.clone();
    binding_tamper.word.binding[0] ^= 1;
    assert!(!verify_committed_semantic_receipt(&binding_tamper).unwrap());

    let mut gamma_tamper = folded;
    gamma_tamper.gamma = gamma_tamper.gamma.add(minidregg_prover::field6::Ext6::ONE);
    assert!(!verify_folded_semantic_accumulator(&left, &right, &gamma_tamper).unwrap());
}
