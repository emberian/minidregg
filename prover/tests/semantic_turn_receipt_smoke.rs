use minidregg_prover::{
    binary_hash::BinaryRoot,
    semantic_receipt::{semantic_id, SEMANTIC_RECEIPT_VERSION},
    semantic_receipt_relation::verify_committed_semantic_receipt,
    semantic_turn_receipt::{
        semantic_state_id, verify_semantic_turn, AuthorizationBinding, AuthorizationKind,
        CommitOutcome, NativeClauseBinding, RejectOutcome, ResourceKind, SemanticTurnReceipt,
        SemanticTurnVerifier, TurnOutcome, TypedRequest, Verb,
    },
};

#[derive(Clone)]
struct ExactVerifier {
    request: TypedRequest,
    authorization: AuthorizationBinding,
    effects_relation: [u8; 32],
    disclosure_relation: [u8; 32],
    clause: NativeClauseBinding,
    denial: [u8; 32],
}

impl SemanticTurnVerifier for ExactVerifier {
    fn verify_authorization(
        &self,
        request: &TypedRequest,
        authorization: &AuthorizationBinding,
    ) -> bool {
        request == &self.request && authorization == &self.authorization
    }

    fn verify_effects(
        &self,
        request: &TypedRequest,
        pre: &[u64],
        post: &[u64],
        touched: &[u64],
        effects_relation_id: &[u8; 32],
    ) -> bool {
        request == &self.request
            && effects_relation_id == &self.effects_relation
            && pre == [1, 2, 3, 4]
            && post == [9, 2, 8, 4]
            && touched == [1, 0, 1, 0]
    }

    fn verify_disclosures(
        &self,
        request: &TypedRequest,
        disclosure_relation_id: &[u8; 32],
    ) -> bool {
        request == &self.request && disclosure_relation_id == &self.disclosure_relation
    }

    fn verify_native_clause(&self, request: &TypedRequest, clause: &NativeClauseBinding) -> bool {
        request == &self.request && clause == &self.clause
    }

    fn verify_rejection(
        &self,
        request: &TypedRequest,
        pre: &[u64],
        rejection: &RejectOutcome,
    ) -> bool {
        request == &self.request
            && pre == [1, 2, 3, 4]
            && rejection.error_code == 7
            && rejection.denial_statement_id == self.denial
    }
}

fn request(pre_state_root: [u8; 32]) -> TypedRequest {
    TypedRequest {
        domain: semantic_id(b"turn/domain"),
        semantics: semantic_id(b"turn/semantics"),
        federation: semantic_id(b"turn/federation"),
        subject: semantic_id(b"turn/subject"),
        subject_key_epoch: 3,
        resource_kind: ResourceKind::Object,
        target: semantic_id(b"turn/target"),
        verb: Verb::MutateObject,
        args_digest: semantic_id(b"turn/args"),
        effects_digest: semantic_id(b"turn/effects"),
        nonce: 11,
        height: 12,
        pre_state_root,
        policy_id: semantic_id(b"turn/policy"),
        policy_epoch: 4,
        cost: 50,
    }
}

#[test]
fn typed_turn_header_binds_exact_request_clauses_and_atomic_outcome() {
    let pre = vec![1, 2, 3, 4];
    let post = vec![9, 2, 8, 4];
    let typed_request = request(semantic_state_id(&pre).unwrap());
    let authorization = AuthorizationBinding {
        kind: AuthorizationKind::Capability,
        evidence_id: semantic_id(b"turn/auth/evidence"),
        auth_state_id: semantic_id(b"turn/auth/state"),
        policy_decision_id: semantic_id(b"turn/auth/policy-decision"),
    };
    let clause = NativeClauseBinding {
        relation_id: semantic_id(b"relation/tower256/logup-indexed/v2"),
        statement_id: semantic_id(b"statement/tower256/logup/example"),
        commitment_root: BinaryRoot::from_bytes([0x42; 48]),
    };
    let effects_relation = semantic_id(b"relation/effects/exact-delta/v1");
    let disclosure_relation = semantic_id(b"relation/disclosure/none/v1");
    let denial = semantic_id(b"relation/denial/v1");
    let verifier = ExactVerifier {
        request: typed_request.clone(),
        authorization: authorization.clone(),
        effects_relation,
        disclosure_relation,
        clause: clause.clone(),
        denial,
    };
    let receipt = SemanticTurnReceipt {
        version: SEMANTIC_RECEIPT_VERSION,
        history_domain: semantic_id(b"history/typed-turns"),
        sequence: 0,
        previous_receipt: None,
        turn_id: semantic_id(b"turn/0"),
        request: typed_request.clone(),
        pre: pre.clone(),
        outcome: TurnOutcome::Commit(CommitOutcome {
            authorization,
            post: post.clone(),
            touched: vec![1, 0, 1, 0],
            post_state_root: semantic_state_id(&post).unwrap(),
            effects_relation_id: effects_relation,
            disclosure_relation_id: disclosure_relation,
            native_clauses: vec![clause],
        }),
    };

    let verified = verify_semantic_turn(&receipt, &verifier).unwrap().unwrap();
    assert!(verified.is_committed());
    assert_eq!(verified.post(), post);
    let core = verified.committed_core().unwrap();
    assert_eq!(&core.word.binding, verified.binding());
    assert!(verify_committed_semantic_receipt(core).unwrap());

    // Exact-request indexing: a target substitution changes the header but is
    // rejected by every portal method receiving the substituted request.
    let mut target_splice = receipt.clone();
    target_splice.request.target = semantic_id(b"turn/other-target");
    assert!(verify_semantic_turn(&target_splice, &verifier)
        .unwrap()
        .is_none());

    let mut clause_splice = receipt.clone();
    if let TurnOutcome::Commit(commit) = &mut clause_splice.outcome {
        commit.native_clauses[0].commitment_root = BinaryRoot::from_bytes([0x99; 48]);
    }
    assert!(verify_semantic_turn(&clause_splice, &verifier)
        .unwrap()
        .is_none());

    let mut ghost = receipt.clone();
    if let TurnOutcome::Commit(commit) = &mut ghost.outcome {
        commit.touched[0] = 0;
    }
    assert!(verify_semantic_turn(&ghost, &verifier).is_err());

    // Rejection has no post payload; the verified observation is exactly pre.
    let rejected = SemanticTurnReceipt {
        outcome: TurnOutcome::Reject(RejectOutcome {
            error_code: 7,
            denial_statement_id: denial,
        }),
        ..receipt
    };
    let denied = verify_semantic_turn(&rejected, &verifier).unwrap().unwrap();
    assert!(!denied.is_committed());
    assert_eq!(denied.post(), pre);
}
