//! Canonical logical envelope for a heterogeneous receipt history.
//!
//! This module is deliberately only an ABI and a structural validator.  A
//! [`HistoryEnvelope`] is not a proof, [`validate_history_append`] does not fold
//! an accumulator, and a [`ReprEqStatement`] does not establish its relation.
//! Proof systems may carry these statements, but must verify them elsewhere.
//!
//! Heterogeneity is represented as a product map of homogeneous lanes.  Every
//! object inside one [`LaneEnvelope`] has exactly the lane's [`AlgebraId`].
//! Cross-algebra relations are inexpressible in [`NativeStatement`] and may be
//! named only by one of the three explicit [`ReprEqMode`] bridge forms.

use core::fmt;

use serde::{Deserialize, Serialize};
use sha3::{Digest as _, Sha3_256};

/// Current canonical wire version.
pub const SEMANTIC_RECEIPT_VERSION: u16 = 1;

/// BabyBear's prime characteristic, `2^31 - 2^27 + 1`.
pub const BABY_BEAR_CHARACTERISTIC: u64 = 2_013_265_921;

const MAX_OPAQUE_BYTES: usize = 1 << 20;
const CANONICAL_TAG: &[u8; 4] = b"HSR1";

/// A fixed-width semantic identifier.  Identifiers name suites and relations;
/// they do not stand in for proofs of those relations.
pub type SemanticId = [u8; 32];

/// Deterministically derive a semantic identifier from a domain-separated
/// public label.
pub fn semantic_id(label: &[u8]) -> SemanticId {
    let mut hash = Sha3_256::new();
    hash.update(b"minidregg/semantic-id/v1");
    hash.update((label.len() as u64).to_le_bytes());
    hash.update(label);
    hash.finalize().into()
}

/// Canonical positive characteristic as an unsigned big-endian integer.
///
/// This is intentionally not called a modulus or a field size.  In particular,
/// `BabyBear[u]/(u^6-31)` reports characteristic `p`, not cardinality `p^6`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Characteristic(Vec<u8>);

impl Characteristic {
    /// Construct the canonical big-endian representation of a `u64`.
    pub fn from_u64(value: u64) -> Self {
        let bytes = value.to_be_bytes();
        let first = bytes.iter().position(|&byte| byte != 0).unwrap_or(7);
        Self(bytes[first..].to_vec())
    }

    /// Construct `base^exponent` without truncating to a machine integer.
    /// Useful for detecting the extension-cardinality/characteristic mix-up.
    pub fn from_power_u64(base: u64, exponent: u16) -> Self {
        let mut little_endian = vec![1u8];
        for _ in 0..exponent {
            let mut carry = 0u128;
            for byte in &mut little_endian {
                let product = u128::from(*byte) * u128::from(base) + carry;
                *byte = product as u8;
                carry = product >> 8;
            }
            while carry != 0 {
                little_endian.push(carry as u8);
                carry >>= 8;
            }
        }
        little_endian.reverse();
        Self(little_endian)
    }

    /// Canonical unsigned big-endian bytes.
    pub fn as_be_bytes(&self) -> &[u8] {
        &self.0
    }

    fn validate(&self) -> Result<(), SemanticReceiptError> {
        if self.0.is_empty() || self.0[0] == 0 || self.0 == [1] {
            return Err(SemanticReceiptError::InvalidCharacteristic);
        }
        if self.0.len() > MAX_OPAQUE_BYTES {
            return Err(SemanticReceiptError::OpaqueValueTooLong {
                what: "characteristic",
                length: self.0.len(),
            });
        }
        Ok(())
    }
}

/// Exact algebra identity used by a native statement and accumulator lane.
///
/// Extension fields carry their *base characteristic* and extension degree as
/// separate fields.  No cardinality-to-characteristic coercion exists.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum AlgebraId {
    PrimeField {
        suite_id: SemanticId,
        characteristic: Characteristic,
    },
    ExtensionField {
        suite_id: SemanticId,
        base_characteristic: Characteristic,
        degree: u16,
        defining_polynomial_id: SemanticId,
    },
    BinaryTower {
        suite_id: SemanticId,
        degree: u16,
        tower_id: SemanticId,
    },
}

impl AlgebraId {
    /// The canonical BabyBear base field suite.
    pub fn baby_bear() -> Self {
        Self::PrimeField {
            suite_id: semantic_id(b"algebra/babybear/base/v1"),
            characteristic: Characteristic::from_u64(BABY_BEAR_CHARACTERISTIC),
        }
    }

    /// The canonical `BabyBear[u]/(u^6-31)` suite.
    pub fn baby_bear_ext6() -> Self {
        Self::ExtensionField {
            suite_id: semantic_id(b"algebra/babybear/ext6/v1"),
            base_characteristic: Characteristic::from_u64(BABY_BEAR_CHARACTERISTIC),
            degree: 6,
            defining_polynomial_id: semantic_id(b"polynomial/u^6-31/babybear/v1"),
        }
    }

    /// The explicit Fan--Paar-style `GF(2)^degree` tower suite.
    pub fn gf2_tower(degree: u16, tower_id: SemanticId) -> Self {
        Self::BinaryTower {
            suite_id: semantic_id(b"algebra/gf2/tower/v1"),
            degree,
            tower_id,
        }
    }

    /// The base characteristic.  Extension degree never changes this value.
    pub fn characteristic(&self) -> Characteristic {
        match self {
            Self::PrimeField { characteristic, .. } => characteristic.clone(),
            Self::ExtensionField {
                base_characteristic,
                ..
            } => base_characteristic.clone(),
            Self::BinaryTower { .. } => Characteristic::from_u64(2),
        }
    }

    /// Degree over the base field (`1` for a prime field).
    pub fn extension_degree(&self) -> u16 {
        match self {
            Self::PrimeField { .. } => 1,
            Self::ExtensionField { degree, .. } | Self::BinaryTower { degree, .. } => *degree,
        }
    }

    pub fn validate(&self) -> Result<(), SemanticReceiptError> {
        match self {
            Self::PrimeField {
                suite_id,
                characteristic,
            } => {
                require_id("algebra suite", suite_id)?;
                characteristic.validate()?;
            }
            Self::ExtensionField {
                suite_id,
                base_characteristic,
                degree,
                defining_polynomial_id,
            } => {
                require_id("algebra suite", suite_id)?;
                base_characteristic.validate()?;
                if *degree < 2 {
                    return Err(SemanticReceiptError::InvalidExtensionDegree(*degree));
                }
                require_id("defining polynomial", defining_polynomial_id)?;
            }
            Self::BinaryTower {
                suite_id,
                degree,
                tower_id,
            } => {
                require_id("algebra suite", suite_id)?;
                if *degree == 0 {
                    return Err(SemanticReceiptError::InvalidExtensionDegree(*degree));
                }
                require_id("binary tower", tower_id)?;
            }
        }

        // Known suite ids are parameter pins, not caller-selected labels.  This
        // gives the extension-cardinality confusion a structural rejection.
        let known = match self {
            Self::PrimeField { suite_id, .. }
                if *suite_id == semantic_id(b"algebra/babybear/base/v1") =>
            {
                Some(Self::baby_bear())
            }
            Self::ExtensionField { suite_id, .. }
                if *suite_id == semantic_id(b"algebra/babybear/ext6/v1") =>
            {
                Some(Self::baby_bear_ext6())
            }
            _ => None,
        };
        if known.as_ref().is_some_and(|expected| expected != self) {
            return Err(SemanticReceiptError::KnownAlgebraParameterMismatch);
        }
        Ok(())
    }
}

/// A commitment, typed by the algebra of the committed native object.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CommitmentRef {
    pub algebra: AlgebraId,
    pub scheme_id: SemanticId,
    pub bytes: Vec<u8>,
}

impl CommitmentRef {
    pub fn validate(&self) -> Result<(), SemanticReceiptError> {
        self.algebra.validate()?;
        require_id("commitment scheme", &self.scheme_id)?;
        require_opaque("commitment", &self.bytes)
    }
}

/// Disclosure carried by a typed value reference.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ValueDisclosure {
    PublicBytes { bytes: Vec<u8> },
    Committed { commitment: CommitmentRef },
}

/// A named value used by a native statement or explicit representation bridge.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValueRef {
    pub value_id: SemanticId,
    pub algebra: AlgebraId,
    pub representation_id: SemanticId,
    pub disclosure: ValueDisclosure,
}

impl ValueRef {
    pub fn public(
        value_id: SemanticId,
        algebra: AlgebraId,
        representation_id: SemanticId,
        bytes: Vec<u8>,
    ) -> Self {
        Self {
            value_id,
            algebra,
            representation_id,
            disclosure: ValueDisclosure::PublicBytes { bytes },
        }
    }

    pub fn committed(
        value_id: SemanticId,
        algebra: AlgebraId,
        representation_id: SemanticId,
        commitment: CommitmentRef,
    ) -> Self {
        Self {
            value_id,
            algebra,
            representation_id,
            disclosure: ValueDisclosure::Committed { commitment },
        }
    }

    pub fn public_bytes(&self) -> Option<&[u8]> {
        match &self.disclosure {
            ValueDisclosure::PublicBytes { bytes } => Some(bytes),
            ValueDisclosure::Committed { .. } => None,
        }
    }

    pub fn validate(&self) -> Result<(), SemanticReceiptError> {
        require_id("value", &self.value_id)?;
        self.algebra.validate()?;
        require_id("value representation", &self.representation_id)?;
        match &self.disclosure {
            ValueDisclosure::PublicBytes { bytes } => require_opaque("public value", bytes),
            ValueDisclosure::Committed { commitment } => {
                commitment.validate()?;
                require_same_algebra("committed value", &self.algebra, &commitment.algebra)
            }
        }
    }
}

/// A relation native to exactly one algebra.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeStatement {
    pub algebra: AlgebraId,
    pub relation_id: SemanticId,
    pub pre_state: CommitmentRef,
    pub post_state: CommitmentRef,
    /// Strictly sorted by `value_id`; duplicates are not aliases.
    pub values: Vec<ValueRef>,
}

impl NativeStatement {
    pub fn canonicalize_values(&mut self) {
        self.values.sort_by_key(|value| value.value_id);
    }

    pub fn validate(&self) -> Result<(), SemanticReceiptError> {
        self.algebra.validate()?;
        require_id("native relation", &self.relation_id)?;
        self.pre_state.validate()?;
        self.post_state.validate()?;
        require_same_algebra("native pre-state", &self.algebra, &self.pre_state.algebra)?;
        require_same_algebra("native post-state", &self.algebra, &self.post_state.algebra)?;
        if self.pre_state.scheme_id != self.post_state.scheme_id {
            return Err(SemanticReceiptError::NativeCommitmentSchemeChanged);
        }
        validate_sorted_values(&self.values)?;
        for value in &self.values {
            value.validate()?;
            require_same_algebra("native value", &self.algebra, &value.algebra)?;
        }
        Ok(())
    }
}

/// Byte order for an explicit exact-limb representation bridge.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Endian {
    Little,
    Big,
}

/// The only three cross-algebra representation relations admitted by the ABI.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ReprEqMode {
    /// Both values are public, and their byte strings are literally identical.
    /// This says nothing about equality of their field denotations.
    PublicByteIdentity,
    /// Equality of an explicitly sized, ordered limb vector.  Public limbs are
    /// checked here; committed limbs remain a statement for an external proof.
    ExactLimb {
        limb_bits: u16,
        limb_count: u32,
        endian: Endian,
    },
    /// A named joint protocol owns the relation.  The digest binds its public
    /// statement, not a proof or an accept bit.
    JointProtocol {
        protocol_id: SemanticId,
        statement_digest: SemanticId,
    },
}

/// Explicit representation relation between two declared [`ValueRef`]s.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReprEqStatement {
    pub bridge_id: SemanticId,
    pub left: ValueRef,
    pub right: ValueRef,
    pub mode: ReprEqMode,
}

impl ReprEqStatement {
    pub fn validate(&self) -> Result<(), SemanticReceiptError> {
        require_id("representation bridge", &self.bridge_id)?;
        self.left.validate()?;
        self.right.validate()?;
        match &self.mode {
            ReprEqMode::PublicByteIdentity => {
                let left = self
                    .left
                    .public_bytes()
                    .ok_or(SemanticReceiptError::PublicByteIdentityIsNotPublic)?;
                let right = self
                    .right
                    .public_bytes()
                    .ok_or(SemanticReceiptError::PublicByteIdentityIsNotPublic)?;
                if left != right {
                    return Err(SemanticReceiptError::PublicByteIdentityMismatch);
                }
            }
            ReprEqMode::ExactLimb {
                limb_bits,
                limb_count,
                ..
            } => {
                if *limb_bits == 0 || *limb_bits > 64 || *limb_bits % 8 != 0 || *limb_count == 0 {
                    return Err(SemanticReceiptError::InvalidExactLimbShape {
                        limb_bits: *limb_bits,
                        limb_count: *limb_count,
                    });
                }
                let expected = usize::from(*limb_bits / 8)
                    .checked_mul(*limb_count as usize)
                    .ok_or(SemanticReceiptError::EncodingLengthOverflow)?;
                match (self.left.public_bytes(), self.right.public_bytes()) {
                    (Some(left), Some(right)) => {
                        if left.len() != expected || right.len() != expected {
                            return Err(SemanticReceiptError::ExactLimbLength {
                                expected,
                                left: left.len(),
                                right: right.len(),
                            });
                        }
                        if left != right {
                            return Err(SemanticReceiptError::ExactLimbMismatch);
                        }
                    }
                    (None, None) => {
                        // Structural only: an external proof must establish this claim.
                    }
                    _ => return Err(SemanticReceiptError::ExactLimbMixedDisclosure),
                }
            }
            ReprEqMode::JointProtocol {
                protocol_id,
                statement_digest,
            } => {
                require_id("joint bridge protocol", protocol_id)?;
                require_id("joint bridge statement", statement_digest)?;
            }
        }
        Ok(())
    }
}

/// Every field that can affect folding.  Compatibility is exact structural
/// equality; there is no rate, domain, transcript, or code-family coercion.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FoldCompatibility {
    pub protocol_id: SemanticId,
    pub code_id: SemanticId,
    pub transcript_id: SemanticId,
    pub constraint_shape_id: SemanticId,
    pub domain_size: u64,
    pub rate_numerator: u64,
    pub rate_denominator: u64,
}

impl FoldCompatibility {
    pub fn validate(&self) -> Result<(), SemanticReceiptError> {
        require_id("fold protocol", &self.protocol_id)?;
        require_id("fold code", &self.code_id)?;
        require_id("fold transcript", &self.transcript_id)?;
        require_id("fold constraint shape", &self.constraint_shape_id)?;
        if self.domain_size == 0
            || self.rate_numerator == 0
            || self.rate_denominator == 0
            || self.rate_numerator > self.rate_denominator
        {
            return Err(SemanticReceiptError::InvalidFoldParameters);
        }
        Ok(())
    }
}

/// Stable key for one homogeneous accumulator lane in the product map.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LaneAccumulatorKey {
    pub lane_id: SemanticId,
    pub algebra: AlgebraId,
    pub native_relation_id: SemanticId,
    pub accumulator_scheme_id: SemanticId,
    pub fold: FoldCompatibility,
}

impl LaneAccumulatorKey {
    pub fn validate(&self) -> Result<(), SemanticReceiptError> {
        require_id("lane", &self.lane_id)?;
        self.algebra.validate()?;
        require_id("lane native relation", &self.native_relation_id)?;
        require_id("lane accumulator scheme", &self.accumulator_scheme_id)?;
        self.fold.validate()
    }

    /// Exact fold compatibility.  No field is projected away.
    pub fn exact_fold_compatible(&self, other: &Self) -> bool {
        self == other
    }
}

/// One homogeneous factor of the heterogeneous history product.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LaneEnvelope {
    pub key: LaneAccumulatorKey,
    pub statement: NativeStatement,
    pub input_accumulator: CommitmentRef,
    pub output_accumulator: CommitmentRef,
}

impl LaneEnvelope {
    pub fn validate(&self) -> Result<(), SemanticReceiptError> {
        self.key.validate()?;
        self.statement.validate()?;
        self.input_accumulator.validate()?;
        self.output_accumulator.validate()?;
        require_same_algebra("lane statement", &self.key.algebra, &self.statement.algebra)?;
        require_same_algebra(
            "lane input accumulator",
            &self.key.algebra,
            &self.input_accumulator.algebra,
        )?;
        require_same_algebra(
            "lane output accumulator",
            &self.key.algebra,
            &self.output_accumulator.algebra,
        )?;
        if self.statement.relation_id != self.key.native_relation_id {
            return Err(SemanticReceiptError::LaneRelationMismatch);
        }
        if self.input_accumulator.scheme_id != self.key.accumulator_scheme_id
            || self.output_accumulator.scheme_id != self.key.accumulator_scheme_id
        {
            return Err(SemanticReceiptError::LaneAccumulatorSchemeMismatch);
        }
        Ok(())
    }
}

/// Canonical product of heterogeneous, individually homogeneous lanes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HistoryEnvelope {
    pub version: u16,
    pub history_domain: SemanticId,
    pub sequence: u64,
    pub previous_envelope: Option<SemanticId>,
    pub turn_id: SemanticId,
    /// Strictly sorted by `key.lane_id`; a lane appears exactly once.
    pub lanes: Vec<LaneEnvelope>,
    /// Strictly sorted by `bridge_id`.
    pub repr_equalities: Vec<ReprEqStatement>,
}

impl HistoryEnvelope {
    /// Sort every canonical product index, then validate the resulting envelope.
    pub fn canonicalize(mut self) -> Result<Self, SemanticReceiptError> {
        for lane in &mut self.lanes {
            lane.statement.canonicalize_values();
        }
        self.lanes.sort_by_key(|lane| lane.key.lane_id);
        self.repr_equalities
            .sort_by_key(|statement| statement.bridge_id);
        self.validate()?;
        Ok(self)
    }

    pub fn validate(&self) -> Result<(), SemanticReceiptError> {
        if self.version != SEMANTIC_RECEIPT_VERSION {
            return Err(SemanticReceiptError::UnsupportedVersion(self.version));
        }
        require_id("history domain", &self.history_domain)?;
        require_id("turn", &self.turn_id)?;
        match (self.sequence, self.previous_envelope) {
            (0, None) | (1.., Some(_)) => {}
            (0, Some(_)) => return Err(SemanticReceiptError::GenesisHasPrevious),
            (_, None) => return Err(SemanticReceiptError::NonGenesisMissingPrevious),
        }
        if let Some(previous) = &self.previous_envelope {
            require_id("previous envelope", previous)?;
        }
        if self.lanes.is_empty() {
            return Err(SemanticReceiptError::EmptyLaneProduct);
        }
        validate_sorted_lanes(&self.lanes)?;
        validate_sorted_bridges(&self.repr_equalities)?;

        let mut declared_values: Vec<&ValueRef> = Vec::new();
        for lane in &self.lanes {
            lane.validate()?;
            for value in &lane.statement.values {
                if declared_values
                    .iter()
                    .any(|declared| declared.value_id == value.value_id)
                {
                    return Err(SemanticReceiptError::DuplicateGlobalValue(value.value_id));
                }
                declared_values.push(value);
            }
        }
        for bridge in &self.repr_equalities {
            bridge.validate()?;
            require_declared_value(&declared_values, &bridge.left)?;
            require_declared_value(&declared_values, &bridge.right)?;
        }
        Ok(())
    }

    /// The sole canonical byte encoding.  Serde encodings are transport
    /// conveniences and are not consensus encodings.
    pub fn canonical_bytes(&self) -> Result<Vec<u8>, SemanticReceiptError> {
        self.validate()?;
        let mut out = Vec::new();
        out.extend_from_slice(CANONICAL_TAG);
        put_u16(&mut out, self.version);
        put_id(&mut out, &self.history_domain);
        put_u64(&mut out, self.sequence);
        match self.previous_envelope {
            None => out.push(0),
            Some(previous) => {
                out.push(1);
                put_id(&mut out, &previous);
            }
        }
        put_id(&mut out, &self.turn_id);
        put_len(&mut out, self.lanes.len())?;
        for lane in &self.lanes {
            encode_lane(&mut out, lane)?;
        }
        put_len(&mut out, self.repr_equalities.len())?;
        for bridge in &self.repr_equalities {
            encode_bridge(&mut out, bridge)?;
        }
        Ok(out)
    }

    /// Digest of the canonical envelope bytes, for the next history link.
    pub fn envelope_id(&self) -> Result<SemanticId, SemanticReceiptError> {
        let bytes = self.canonical_bytes()?;
        let mut hash = Sha3_256::new();
        hash.update(b"minidregg/history-envelope/v1");
        hash.update((bytes.len() as u64).to_le_bytes());
        hash.update(bytes);
        Ok(hash.finalize().into())
    }
}

/// Validate one history append without constructing or verifying any proof.
///
/// The lane product must stay identical, each fold key must match in full, and
/// both the native state and accumulator seams must be exact byte-for-byte
/// typed references.
pub fn validate_history_append(
    previous: &HistoryEnvelope,
    next: &HistoryEnvelope,
) -> Result<(), SemanticReceiptError> {
    previous.validate()?;
    next.validate()?;
    if previous.history_domain != next.history_domain {
        return Err(SemanticReceiptError::HistoryDomainMismatch);
    }
    if previous.sequence.checked_add(1) != Some(next.sequence) {
        return Err(SemanticReceiptError::HistorySequenceMismatch);
    }
    if next.previous_envelope != Some(previous.envelope_id()?) {
        return Err(SemanticReceiptError::PreviousEnvelopeMismatch);
    }
    if previous.lanes.len() != next.lanes.len() {
        return Err(SemanticReceiptError::LaneProductChanged);
    }
    for (left, right) in previous.lanes.iter().zip(&next.lanes) {
        if left.key.lane_id != right.key.lane_id {
            return Err(SemanticReceiptError::LaneProductChanged);
        }
        if !left.key.exact_fold_compatible(&right.key) {
            return Err(SemanticReceiptError::FoldIncompatible {
                lane_id: left.key.lane_id,
            });
        }
        if left.output_accumulator != right.input_accumulator {
            return Err(SemanticReceiptError::AccumulatorSeamMismatch {
                lane_id: left.key.lane_id,
            });
        }
        if left.statement.post_state != right.statement.pre_state {
            return Err(SemanticReceiptError::NativeStateSeamMismatch {
                lane_id: left.key.lane_id,
            });
        }
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticReceiptError {
    EmptyId(&'static str),
    InvalidCharacteristic,
    InvalidExtensionDegree(u16),
    KnownAlgebraParameterMismatch,
    OpaqueValueTooLong {
        what: &'static str,
        length: usize,
    },
    EmptyOpaqueValue(&'static str),
    ImplicitSemanticCast {
        context: &'static str,
        expected: AlgebraId,
        found: AlgebraId,
    },
    NativeCommitmentSchemeChanged,
    DuplicateValue(SemanticId),
    UnsortedValue(SemanticId),
    PublicByteIdentityIsNotPublic,
    PublicByteIdentityMismatch,
    InvalidExactLimbShape {
        limb_bits: u16,
        limb_count: u32,
    },
    ExactLimbLength {
        expected: usize,
        left: usize,
        right: usize,
    },
    ExactLimbMismatch,
    ExactLimbMixedDisclosure,
    InvalidFoldParameters,
    LaneRelationMismatch,
    LaneAccumulatorSchemeMismatch,
    UnsupportedVersion(u16),
    GenesisHasPrevious,
    NonGenesisMissingPrevious,
    EmptyLaneProduct,
    DuplicateLane(SemanticId),
    UnsortedLane(SemanticId),
    DuplicateBridge(SemanticId),
    UnsortedBridge(SemanticId),
    DuplicateGlobalValue(SemanticId),
    BridgeValueNotDeclared(SemanticId),
    BridgeValueDeclarationMismatch(SemanticId),
    EncodingLengthOverflow,
    HistoryDomainMismatch,
    HistorySequenceMismatch,
    PreviousEnvelopeMismatch,
    LaneProductChanged,
    FoldIncompatible {
        lane_id: SemanticId,
    },
    AccumulatorSeamMismatch {
        lane_id: SemanticId,
    },
    NativeStateSeamMismatch {
        lane_id: SemanticId,
    },
}

impl fmt::Display for SemanticReceiptError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyId(what) => write!(f, "{what} id is all zero"),
            Self::InvalidCharacteristic => {
                write!(f, "characteristic is not a canonical integer > 1")
            }
            Self::InvalidExtensionDegree(degree) => write!(f, "invalid extension degree {degree}"),
            Self::KnownAlgebraParameterMismatch => {
                write!(f, "known algebra suite carries noncanonical parameters")
            }
            Self::OpaqueValueTooLong { what, length } => {
                write!(f, "{what} length {length} exceeds the ABI limit")
            }
            Self::EmptyOpaqueValue(what) => write!(f, "{what} is empty"),
            Self::ImplicitSemanticCast { context, .. } => {
                write!(
                    f,
                    "{context} attempts an implicit cross-algebra semantic cast"
                )
            }
            Self::NativeCommitmentSchemeChanged => {
                write!(f, "native statement changes commitment scheme")
            }
            Self::DuplicateValue(id) => write!(f, "duplicate native value {id:?}"),
            Self::UnsortedValue(id) => write!(f, "native value {id:?} is not canonically sorted"),
            Self::PublicByteIdentityIsNotPublic => {
                write!(f, "public-byte identity requires two public values")
            }
            Self::PublicByteIdentityMismatch => write!(f, "public byte strings are not identical"),
            Self::InvalidExactLimbShape {
                limb_bits,
                limb_count,
            } => {
                write!(f, "invalid exact-limb shape {limb_count}x{limb_bits}")
            }
            Self::ExactLimbLength {
                expected,
                left,
                right,
            } => write!(
                f,
                "exact-limb bridge expects {expected} bytes, got {left} and {right}"
            ),
            Self::ExactLimbMismatch => write!(f, "exact public limbs differ"),
            Self::ExactLimbMixedDisclosure => {
                write!(
                    f,
                    "exact-limb bridge cannot mix public and committed operands"
                )
            }
            Self::InvalidFoldParameters => write!(f, "invalid fold parameters"),
            Self::LaneRelationMismatch => write!(f, "lane and native relation differ"),
            Self::LaneAccumulatorSchemeMismatch => {
                write!(f, "lane accumulator commitment scheme differs from its key")
            }
            Self::UnsupportedVersion(version) => write!(f, "unsupported receipt version {version}"),
            Self::GenesisHasPrevious => write!(f, "genesis receipt has a previous envelope"),
            Self::NonGenesisMissingPrevious => {
                write!(f, "non-genesis receipt lacks a previous envelope")
            }
            Self::EmptyLaneProduct => write!(f, "heterogeneous lane product is empty"),
            Self::DuplicateLane(id) => write!(f, "duplicate/replayed lane {id:?}"),
            Self::UnsortedLane(id) => write!(f, "lane {id:?} is not canonically sorted"),
            Self::DuplicateBridge(id) => write!(f, "duplicate representation bridge {id:?}"),
            Self::UnsortedBridge(id) => {
                write!(f, "representation bridge {id:?} is not canonically sorted")
            }
            Self::DuplicateGlobalValue(id) => write!(f, "value id {id:?} is declared twice"),
            Self::BridgeValueNotDeclared(id) => write!(f, "bridge value {id:?} is not declared"),
            Self::BridgeValueDeclarationMismatch(id) => {
                write!(f, "bridge value {id:?} differs from its declaration")
            }
            Self::EncodingLengthOverflow => write!(f, "canonical encoding length exceeds u32"),
            Self::HistoryDomainMismatch => write!(f, "history domains differ"),
            Self::HistorySequenceMismatch => write!(f, "history sequence is not consecutive"),
            Self::PreviousEnvelopeMismatch => write!(f, "previous-envelope digest mismatch"),
            Self::LaneProductChanged => write!(f, "history append changes the lane product"),
            Self::FoldIncompatible { lane_id } => {
                write!(f, "lane {lane_id:?} has a non-identical fold key")
            }
            Self::AccumulatorSeamMismatch { lane_id } => {
                write!(f, "lane {lane_id:?} accumulator seam does not match")
            }
            Self::NativeStateSeamMismatch { lane_id } => {
                write!(f, "lane {lane_id:?} native state seam does not match")
            }
        }
    }
}

impl std::error::Error for SemanticReceiptError {}

fn require_id(what: &'static str, id: &SemanticId) -> Result<(), SemanticReceiptError> {
    if *id == [0; 32] {
        Err(SemanticReceiptError::EmptyId(what))
    } else {
        Ok(())
    }
}

fn require_opaque(what: &'static str, bytes: &[u8]) -> Result<(), SemanticReceiptError> {
    if bytes.is_empty() {
        Err(SemanticReceiptError::EmptyOpaqueValue(what))
    } else if bytes.len() > MAX_OPAQUE_BYTES {
        Err(SemanticReceiptError::OpaqueValueTooLong {
            what,
            length: bytes.len(),
        })
    } else {
        Ok(())
    }
}

fn require_same_algebra(
    context: &'static str,
    expected: &AlgebraId,
    found: &AlgebraId,
) -> Result<(), SemanticReceiptError> {
    if expected == found {
        Ok(())
    } else {
        Err(SemanticReceiptError::ImplicitSemanticCast {
            context,
            expected: expected.clone(),
            found: found.clone(),
        })
    }
}

fn validate_sorted_values(values: &[ValueRef]) -> Result<(), SemanticReceiptError> {
    for pair in values.windows(2) {
        if pair[0].value_id == pair[1].value_id {
            return Err(SemanticReceiptError::DuplicateValue(pair[0].value_id));
        }
        if pair[0].value_id > pair[1].value_id {
            return Err(SemanticReceiptError::UnsortedValue(pair[1].value_id));
        }
    }
    Ok(())
}

fn validate_sorted_lanes(lanes: &[LaneEnvelope]) -> Result<(), SemanticReceiptError> {
    for pair in lanes.windows(2) {
        if pair[0].key.lane_id == pair[1].key.lane_id {
            return Err(SemanticReceiptError::DuplicateLane(pair[0].key.lane_id));
        }
        if pair[0].key.lane_id > pair[1].key.lane_id {
            return Err(SemanticReceiptError::UnsortedLane(pair[1].key.lane_id));
        }
    }
    Ok(())
}

fn validate_sorted_bridges(bridges: &[ReprEqStatement]) -> Result<(), SemanticReceiptError> {
    for pair in bridges.windows(2) {
        if pair[0].bridge_id == pair[1].bridge_id {
            return Err(SemanticReceiptError::DuplicateBridge(pair[0].bridge_id));
        }
        if pair[0].bridge_id > pair[1].bridge_id {
            return Err(SemanticReceiptError::UnsortedBridge(pair[1].bridge_id));
        }
    }
    Ok(())
}

fn require_declared_value(
    declared: &[&ValueRef],
    bridge_value: &ValueRef,
) -> Result<(), SemanticReceiptError> {
    let Some(value) = declared
        .iter()
        .find(|value| value.value_id == bridge_value.value_id)
    else {
        return Err(SemanticReceiptError::BridgeValueNotDeclared(
            bridge_value.value_id,
        ));
    };
    if **value != *bridge_value {
        return Err(SemanticReceiptError::BridgeValueDeclarationMismatch(
            bridge_value.value_id,
        ));
    }
    Ok(())
}

fn put_u16(out: &mut Vec<u8>, value: u16) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_id(out: &mut Vec<u8>, id: &SemanticId) {
    out.extend_from_slice(id);
}

fn put_len(out: &mut Vec<u8>, length: usize) -> Result<(), SemanticReceiptError> {
    let length = u32::try_from(length).map_err(|_| SemanticReceiptError::EncodingLengthOverflow)?;
    put_u32(out, length);
    Ok(())
}

fn put_bytes(out: &mut Vec<u8>, bytes: &[u8]) -> Result<(), SemanticReceiptError> {
    put_len(out, bytes.len())?;
    out.extend_from_slice(bytes);
    Ok(())
}

fn encode_characteristic(
    out: &mut Vec<u8>,
    characteristic: &Characteristic,
) -> Result<(), SemanticReceiptError> {
    put_bytes(out, characteristic.as_be_bytes())
}

fn encode_algebra(out: &mut Vec<u8>, algebra: &AlgebraId) -> Result<(), SemanticReceiptError> {
    match algebra {
        AlgebraId::PrimeField {
            suite_id,
            characteristic,
        } => {
            out.push(0);
            put_id(out, suite_id);
            encode_characteristic(out, characteristic)?;
        }
        AlgebraId::ExtensionField {
            suite_id,
            base_characteristic,
            degree,
            defining_polynomial_id,
        } => {
            out.push(1);
            put_id(out, suite_id);
            encode_characteristic(out, base_characteristic)?;
            put_u16(out, *degree);
            put_id(out, defining_polynomial_id);
        }
        AlgebraId::BinaryTower {
            suite_id,
            degree,
            tower_id,
        } => {
            out.push(2);
            put_id(out, suite_id);
            put_u16(out, *degree);
            put_id(out, tower_id);
        }
    }
    Ok(())
}

fn encode_commitment(
    out: &mut Vec<u8>,
    commitment: &CommitmentRef,
) -> Result<(), SemanticReceiptError> {
    encode_algebra(out, &commitment.algebra)?;
    put_id(out, &commitment.scheme_id);
    put_bytes(out, &commitment.bytes)
}

fn encode_value(out: &mut Vec<u8>, value: &ValueRef) -> Result<(), SemanticReceiptError> {
    put_id(out, &value.value_id);
    encode_algebra(out, &value.algebra)?;
    put_id(out, &value.representation_id);
    match &value.disclosure {
        ValueDisclosure::PublicBytes { bytes } => {
            out.push(0);
            put_bytes(out, bytes)?;
        }
        ValueDisclosure::Committed { commitment } => {
            out.push(1);
            encode_commitment(out, commitment)?;
        }
    }
    Ok(())
}

fn encode_native(
    out: &mut Vec<u8>,
    statement: &NativeStatement,
) -> Result<(), SemanticReceiptError> {
    encode_algebra(out, &statement.algebra)?;
    put_id(out, &statement.relation_id);
    encode_commitment(out, &statement.pre_state)?;
    encode_commitment(out, &statement.post_state)?;
    put_len(out, statement.values.len())?;
    for value in &statement.values {
        encode_value(out, value)?;
    }
    Ok(())
}

fn encode_fold(out: &mut Vec<u8>, fold: &FoldCompatibility) {
    put_id(out, &fold.protocol_id);
    put_id(out, &fold.code_id);
    put_id(out, &fold.transcript_id);
    put_id(out, &fold.constraint_shape_id);
    put_u64(out, fold.domain_size);
    put_u64(out, fold.rate_numerator);
    put_u64(out, fold.rate_denominator);
}

fn encode_lane(out: &mut Vec<u8>, lane: &LaneEnvelope) -> Result<(), SemanticReceiptError> {
    put_id(out, &lane.key.lane_id);
    encode_algebra(out, &lane.key.algebra)?;
    put_id(out, &lane.key.native_relation_id);
    put_id(out, &lane.key.accumulator_scheme_id);
    encode_fold(out, &lane.key.fold);
    encode_native(out, &lane.statement)?;
    encode_commitment(out, &lane.input_accumulator)?;
    encode_commitment(out, &lane.output_accumulator)
}

fn encode_bridge(out: &mut Vec<u8>, bridge: &ReprEqStatement) -> Result<(), SemanticReceiptError> {
    put_id(out, &bridge.bridge_id);
    encode_value(out, &bridge.left)?;
    encode_value(out, &bridge.right)?;
    match &bridge.mode {
        ReprEqMode::PublicByteIdentity => out.push(0),
        ReprEqMode::ExactLimb {
            limb_bits,
            limb_count,
            endian,
        } => {
            out.push(1);
            put_u16(out, *limb_bits);
            put_u32(out, *limb_count);
            out.push(match endian {
                Endian::Little => 0,
                Endian::Big => 1,
            });
        }
        ReprEqMode::JointProtocol {
            protocol_id,
            statement_digest,
        } => {
            out.push(2);
            put_id(out, protocol_id);
            put_id(out, statement_digest);
        }
    }
    Ok(())
}
