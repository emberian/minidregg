//! One focused smoke for the heterogeneous semantic-receipt ABI.

#[path = "../src/semantic_receipt.rs"]
mod semantic_receipt;

use semantic_receipt::{
    semantic_id, validate_history_append, AlgebraId, Characteristic, CommitmentRef, Endian,
    FoldCompatibility, HistoryEnvelope, LaneAccumulatorKey, LaneEnvelope, NativeStatement,
    ReprEqMode, ReprEqStatement, SemanticReceiptError, ValueRef, BABY_BEAR_CHARACTERISTIC,
    SEMANTIC_RECEIPT_VERSION,
};

fn commitment(algebra: &AlgebraId, scheme: [u8; 32], byte: u8) -> CommitmentRef {
    CommitmentRef {
        algebra: algebra.clone(),
        scheme_id: scheme,
        bytes: vec![byte; 32],
    }
}

fn fold(label: &[u8]) -> FoldCompatibility {
    FoldCompatibility {
        protocol_id: semantic_id(b"fold/warp-shape/v1"),
        code_id: semantic_id(label),
        transcript_id: semantic_id(b"transcript/shake256/v1"),
        constraint_shape_id: semantic_id(b"constraint/native-receipt/v1"),
        domain_size: 1 << 12,
        rate_numerator: 1,
        rate_denominator: 2,
    }
}

#[allow(clippy::too_many_arguments)]
fn lane(
    lane_label: &[u8],
    algebra: AlgebraId,
    value: ValueRef,
    pre: CommitmentRef,
    post: CommitmentRef,
    input_accumulator: CommitmentRef,
    output_accumulator: CommitmentRef,
    code_label: &[u8],
) -> LaneEnvelope {
    let relation = semantic_id(b"relation/native-transition/v1");
    LaneEnvelope {
        key: LaneAccumulatorKey {
            lane_id: semantic_id(lane_label),
            algebra: algebra.clone(),
            native_relation_id: relation,
            accumulator_scheme_id: input_accumulator.scheme_id,
            fold: fold(code_label),
        },
        statement: NativeStatement {
            algebra,
            relation_id: relation,
            pre_state: pre,
            post_state: post,
            values: vec![value],
        },
        input_accumulator,
        output_accumulator,
    }
}

#[test]
fn heterogeneous_receipt_is_a_sorted_product_not_a_universal_or_casting_accumulator() {
    let babybear_ext6 = AlgebraId::baby_bear_ext6();
    let gf2 = AlgebraId::gf2_tower(64, semantic_id(b"tower/fan-paar/level6/v1"));

    // Extension fields report their base characteristic, never the integer
    // cardinality p^6.  Reusing the known suite id with p^6 is rejected.
    assert_eq!(
        babybear_ext6.characteristic(),
        Characteristic::from_u64(BABY_BEAR_CHARACTERISTIC)
    );
    assert_eq!(babybear_ext6.extension_degree(), 6);
    let mut cardinality_confusion = babybear_ext6.clone();
    let AlgebraId::ExtensionField {
        base_characteristic,
        ..
    } = &mut cardinality_confusion
    else {
        unreachable!()
    };
    *base_characteristic = Characteristic::from_power_u64(BABY_BEAR_CHARACTERISTIC, 6);
    assert_eq!(
        cardinality_confusion.validate(),
        Err(SemanticReceiptError::KnownAlgebraParameterMismatch)
    );

    let state_scheme = semantic_id(b"commit/state/v1");
    let acc_scheme = semantic_id(b"commit/accumulator/v1");
    let repr_ext6 = semantic_id(b"repr/ext6-six-u32-le/v1");
    let repr_gf2 = semantic_id(b"repr/gf2-raw-24/v1");
    let shared_public_bytes = (0u8..24).collect::<Vec<_>>();
    let ext_value = ValueRef::public(
        semantic_id(b"value/ext6/public"),
        babybear_ext6.clone(),
        repr_ext6,
        shared_public_bytes.clone(),
    );
    let gf2_value = ValueRef::public(
        semantic_id(b"value/gf2/public"),
        gf2.clone(),
        repr_gf2,
        shared_public_bytes,
    );

    let ext_lane = lane(
        b"lane/ext6",
        babybear_ext6.clone(),
        ext_value.clone(),
        commitment(&babybear_ext6, state_scheme, 1),
        commitment(&babybear_ext6, state_scheme, 2),
        commitment(&babybear_ext6, acc_scheme, 11),
        commitment(&babybear_ext6, acc_scheme, 12),
        b"code/rs-babybear-ext6/v1",
    );
    let gf2_lane = lane(
        b"lane/gf2",
        gf2.clone(),
        gf2_value.clone(),
        commitment(&gf2, state_scheme, 3),
        commitment(&gf2, state_scheme, 4),
        commitment(&gf2, acc_scheme, 13),
        commitment(&gf2, acc_scheme, 14),
        b"code/additive-gf2/v1",
    );
    let bridge = ReprEqStatement {
        bridge_id: semantic_id(b"bridge/public-byte-identity"),
        left: ext_value.clone(),
        right: gf2_value.clone(),
        mode: ReprEqMode::PublicByteIdentity,
    };

    let genesis = HistoryEnvelope {
        version: SEMANTIC_RECEIPT_VERSION,
        history_domain: semantic_id(b"history/smoke"),
        sequence: 0,
        previous_envelope: None,
        turn_id: semantic_id(b"turn/0"),
        // Deliberately reverse caller order: `canonicalize` owns product order.
        lanes: vec![gf2_lane.clone(), ext_lane.clone()],
        repr_equalities: vec![bridge.clone()],
    }
    .canonicalize()
    .unwrap();
    genesis.validate().unwrap();
    let canonical = genesis.canonical_bytes().unwrap();
    assert_eq!(&canonical[..4], b"HSR1");
    assert_eq!(
        canonical,
        genesis
            .clone()
            .canonicalize()
            .unwrap()
            .canonical_bytes()
            .unwrap()
    );

    // Public-byte identity is explicitly byte-only.  The other two bridge
    // modes are also explicit and structurally validate; none is a proof.
    let exact = ReprEqStatement {
        bridge_id: semantic_id(b"bridge/exact-limb"),
        left: ext_value.clone(),
        right: gf2_value.clone(),
        mode: ReprEqMode::ExactLimb {
            limb_bits: 32,
            limb_count: 6,
            endian: Endian::Little,
        },
    };
    exact.validate().unwrap();
    let joint_left = ValueRef::committed(
        semantic_id(b"value/ext6/committed"),
        babybear_ext6.clone(),
        repr_ext6,
        commitment(&babybear_ext6, state_scheme, 31),
    );
    let joint_right = ValueRef::committed(
        semantic_id(b"value/gf2/committed"),
        gf2.clone(),
        repr_gf2,
        commitment(&gf2, state_scheme, 32),
    );
    let joint = ReprEqStatement {
        bridge_id: semantic_id(b"bridge/joint-protocol"),
        left: joint_left,
        right: joint_right,
        mode: ReprEqMode::JointProtocol {
            protocol_id: semantic_id(b"protocol/cross-field-joint/v1"),
            statement_digest: semantic_id(b"statement/cross-field-joint/smoke"),
        },
    };
    joint.validate().unwrap();

    // A GF(2) value inserted into a BabyBear^6 native statement is an implicit
    // semantic cast and refuses.  The explicit bridges above are the only seam.
    let mut implicit_cast = ext_lane.clone();
    implicit_cast.statement.values = vec![gf2_value.clone()];
    assert!(matches!(
        implicit_cast.validate(),
        Err(SemanticReceiptError::ImplicitSemanticCast { .. })
    ));

    let mut next_ext = ext_lane;
    next_ext.input_accumulator = next_ext.output_accumulator.clone();
    next_ext.output_accumulator = commitment(&babybear_ext6, acc_scheme, 22);
    next_ext.statement.pre_state = next_ext.statement.post_state.clone();
    next_ext.statement.post_state = commitment(&babybear_ext6, state_scheme, 23);
    let mut next_gf2 = gf2_lane;
    next_gf2.input_accumulator = next_gf2.output_accumulator.clone();
    next_gf2.output_accumulator = commitment(&gf2, acc_scheme, 24);
    next_gf2.statement.pre_state = next_gf2.statement.post_state.clone();
    next_gf2.statement.post_state = commitment(&gf2, state_scheme, 25);
    let next = HistoryEnvelope {
        version: SEMANTIC_RECEIPT_VERSION,
        history_domain: genesis.history_domain,
        sequence: 1,
        previous_envelope: Some(genesis.envelope_id().unwrap()),
        turn_id: semantic_id(b"turn/1"),
        lanes: vec![next_gf2, next_ext],
        repr_equalities: vec![bridge],
    }
    .canonicalize()
    .unwrap();
    validate_history_append(&genesis, &next).unwrap();

    // Exact fold compatibility has teeth: changing one domain parameter is
    // not a compatible lane merely because its lane id and algebra still match.
    let mut bad_fold = next.clone();
    bad_fold.lanes[0].key.fold.domain_size *= 2;
    assert!(matches!(
        validate_history_append(&genesis, &bad_fold),
        Err(SemanticReceiptError::FoldIncompatible { .. })
    ));

    // Canonical map validation rejects both order malleability and replaying a
    // lane under the same key in one receipt.
    let mut unsorted = genesis.clone();
    unsorted.lanes.swap(0, 1);
    assert!(matches!(
        unsorted.validate(),
        Err(SemanticReceiptError::UnsortedLane(_))
    ));
    let mut duplicate = genesis;
    duplicate.lanes.insert(1, duplicate.lanes[0].clone());
    assert!(matches!(
        duplicate.validate(),
        Err(SemanticReceiptError::DuplicateLane(_))
    ));
}
