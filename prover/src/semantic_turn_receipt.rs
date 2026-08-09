//! Canonical executable header for the typed semantic turn receipt.
//!
//! This is the runtime counterpart of `Assurance.SemanticTurnReceipt`.  It
//! binds one complete request, history position, authorization/effect/
//! disclosure statements, pre/post state roots, and native dialect clauses.
//! Its canonical digest becomes the 32-byte public prefix of the accumulated
//! semantic receipt word.
//!
//! A structural codec is not authorization.  Admission therefore requires a
//! caller-supplied [`SemanticTurnVerifier`] that receives the exact request for
//! every check.  Only [`verify_semantic_turn`] can construct
//! [`VerifiedSemanticTurn`]; committed outcomes are then converted to the
//! root-linked Ext6 receipt relation.  Rejection has no post-state payload and
//! is definitionally observed as the pre-state.
//!
//! This handwritten module is an executable prototype, not a refinement of
//! Lean: the project has no Rust operational semantics. It must be replaced by
//! a Lean-emitted codec/verifier surface under `[SEMANTIC-TURN-generated]`.
//! `[PCH-OUTER-ACCUMULATOR]` remains the succinct,
//! hiding, knowledge-sound history accumulator.

use core::fmt;

use sha3::{Digest as _, Sha3_256};

use crate::{
    binary_hash::BinaryRoot,
    field4::P,
    semantic_receipt::{SemanticId, SEMANTIC_RECEIPT_VERSION},
    semantic_receipt_relation::{
        commit_semantic_receipt, CommittedSemanticReceipt, SemanticReceiptRelationError,
        SemanticReceiptWord,
    },
};

const HEADER_TAG: &[u8] = b"MDRG-SEMANTIC-TURN-HEADER-V1";
const STATE_TAG: &[u8] = b"MDRG-SEMANTIC-STATE-V1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum ResourceKind {
    Object = 1,
    Account = 2,
    Program = 3,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Verb {
    ObserveObject = 1,
    MutateObject = 2,
    DelegateObject = 3,
    ObserveAccount = 4,
    Transfer = 5,
    DelegateAccount = 6,
    ObserveProgram = 7,
    InstallProgram = 8,
    DelegateProgram = 9,
}

impl Verb {
    fn accepts(self, kind: ResourceKind) -> bool {
        matches!(
            (kind, self),
            (
                ResourceKind::Object,
                Self::ObserveObject | Self::MutateObject | Self::DelegateObject
            ) | (
                ResourceKind::Account,
                Self::ObserveAccount | Self::Transfer | Self::DelegateAccount
            ) | (
                ResourceKind::Program,
                Self::ObserveProgram | Self::InstallProgram | Self::DelegateProgram
            )
        )
    }
}

/// Complete runtime request index.  Every digest/id is fixed-width and every
/// scalar has one little-endian encoding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedRequest {
    pub domain: SemanticId,
    pub semantics: SemanticId,
    pub federation: SemanticId,
    pub subject: SemanticId,
    pub subject_key_epoch: u64,
    pub resource_kind: ResourceKind,
    pub target: SemanticId,
    pub verb: Verb,
    pub args_digest: SemanticId,
    pub effects_digest: SemanticId,
    pub nonce: u64,
    pub height: u64,
    pub pre_state_root: SemanticId,
    pub policy_id: SemanticId,
    pub policy_epoch: u64,
    pub cost: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum AuthorizationKind {
    Signature = 1,
    Proof = 2,
    Capability = 3,
    Threshold = 4,
}

/// Public commitment to the evidence checked for the exact request.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuthorizationBinding {
    pub kind: AuthorizationKind,
    pub evidence_id: SemanticId,
    pub auth_state_id: SemanticId,
    pub policy_decision_id: SemanticId,
}

/// One native proof adapter referenced by the typed receipt header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeClauseBinding {
    pub relation_id: SemanticId,
    pub statement_id: SemanticId,
    pub commitment_root: BinaryRoot,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommitOutcome {
    pub authorization: AuthorizationBinding,
    pub post: Vec<u64>,
    pub touched: Vec<u64>,
    pub post_state_root: SemanticId,
    pub effects_relation_id: SemanticId,
    pub disclosure_relation_id: SemanticId,
    /// Strictly sorted by relation id and unique.
    pub native_clauses: Vec<NativeClauseBinding>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RejectOutcome {
    pub error_code: u32,
    pub denial_statement_id: SemanticId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TurnOutcome {
    Reject(RejectOutcome),
    Commit(CommitOutcome),
}

/// The canonical semantic receipt prior to proof verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticTurnReceipt {
    pub version: u16,
    pub history_domain: SemanticId,
    pub sequence: u64,
    pub previous_receipt: Option<SemanticId>,
    pub turn_id: SemanticId,
    pub request: TypedRequest,
    pub pre: Vec<u64>,
    pub outcome: TurnOutcome,
}

/// Concrete verifier portal.  Every method receives the exact complete
/// request; there are no mode-specific early-return APIs.
pub trait SemanticTurnVerifier {
    fn verify_authorization(
        &self,
        request: &TypedRequest,
        authorization: &AuthorizationBinding,
    ) -> bool;

    fn verify_effects(
        &self,
        request: &TypedRequest,
        pre: &[u64],
        post: &[u64],
        touched: &[u64],
        effects_relation_id: &SemanticId,
    ) -> bool;

    fn verify_disclosures(
        &self,
        request: &TypedRequest,
        disclosure_relation_id: &SemanticId,
    ) -> bool;

    fn verify_native_clause(&self, request: &TypedRequest, clause: &NativeClauseBinding) -> bool;

    fn verify_rejection(
        &self,
        request: &TypedRequest,
        pre: &[u64],
        rejection: &RejectOutcome,
    ) -> bool;
}

/// Opaque successful verification result.  Construction is private.
#[derive(Clone, Debug)]
pub struct VerifiedSemanticTurn {
    binding: SemanticId,
    committed_core: Option<CommittedSemanticReceipt>,
    post: Vec<u64>,
}

impl VerifiedSemanticTurn {
    pub const fn binding(&self) -> &SemanticId {
        &self.binding
    }

    pub const fn committed_core(&self) -> Option<&CommittedSemanticReceipt> {
        self.committed_core.as_ref()
    }

    pub fn post(&self) -> &[u64] {
        &self.post
    }

    pub const fn is_committed(&self) -> bool {
        self.committed_core.is_some()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticTurnError {
    UnsupportedVersion(u16),
    EmptyId(&'static str),
    InvalidHistoryLink,
    VerbKindMismatch,
    EmptyState,
    NonCanonicalState {
        section: &'static str,
        index: usize,
        value: u64,
    },
    PreStateRootMismatch,
    PostStateRootMismatch,
    InvalidClauseOrder,
    VerificationFailed(&'static str),
    LengthOverflow,
    Core(SemanticReceiptRelationError),
}

impl From<SemanticReceiptRelationError> for SemanticTurnError {
    fn from(value: SemanticReceiptRelationError) -> Self {
        Self::Core(value)
    }
}

impl fmt::Display for SemanticTurnError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedVersion(version) => write!(f, "unsupported typed receipt v{version}"),
            Self::EmptyId(name) => write!(f, "typed receipt {name} is all zero"),
            Self::InvalidHistoryLink => write!(f, "typed receipt history link is malformed"),
            Self::VerbKindMismatch => write!(f, "typed verb does not apply to resource kind"),
            Self::EmptyState => write!(f, "typed receipt state is empty"),
            Self::NonCanonicalState {
                section,
                index,
                value,
            } => {
                write!(f, "{section}[{index}]={value} is not canonical BabyBear")
            }
            Self::PreStateRootMismatch => write!(f, "typed request pre-state root mismatch"),
            Self::PostStateRootMismatch => write!(f, "typed commit post-state root mismatch"),
            Self::InvalidClauseOrder => write!(f, "native clauses are not strictly sorted"),
            Self::VerificationFailed(clause) => {
                write!(f, "typed receipt {clause} verification failed")
            }
            Self::LengthOverflow => write!(f, "typed receipt encoding length overflow"),
            Self::Core(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for SemanticTurnError {}

/// Verify the complete semantic receipt and, for commit, bind its canonical
/// header digest into the accumulated relation word.
pub fn verify_semantic_turn<V: SemanticTurnVerifier>(
    receipt: &SemanticTurnReceipt,
    verifier: &V,
) -> Result<Option<VerifiedSemanticTurn>, SemanticTurnError> {
    receipt.validate_structure()?;
    let binding = receipt.binding_id()?;
    match &receipt.outcome {
        TurnOutcome::Reject(rejection) => {
            if !verifier.verify_rejection(&receipt.request, &receipt.pre, rejection) {
                return Ok(None);
            }
            Ok(Some(VerifiedSemanticTurn {
                binding,
                committed_core: None,
                post: receipt.pre.clone(),
            }))
        }
        TurnOutcome::Commit(commit) => {
            if !verifier.verify_authorization(&receipt.request, &commit.authorization) {
                return Ok(None);
            }
            if !verifier.verify_effects(
                &receipt.request,
                &receipt.pre,
                &commit.post,
                &commit.touched,
                &commit.effects_relation_id,
            ) {
                return Ok(None);
            }
            if !verifier.verify_disclosures(&receipt.request, &commit.disclosure_relation_id) {
                return Ok(None);
            }
            for clause in &commit.native_clauses {
                if !verifier.verify_native_clause(&receipt.request, clause) {
                    return Ok(None);
                }
            }
            let core = commit_semantic_receipt(SemanticReceiptWord {
                binding,
                pre: receipt.pre.clone(),
                post: commit.post.clone(),
                touched: commit.touched.clone(),
            })?;
            Ok(Some(VerifiedSemanticTurn {
                binding,
                committed_core: Some(core),
                post: commit.post.clone(),
            }))
        }
    }
}

impl SemanticTurnReceipt {
    pub fn validate_structure(&self) -> Result<(), SemanticTurnError> {
        if self.version != SEMANTIC_RECEIPT_VERSION {
            return Err(SemanticTurnError::UnsupportedVersion(self.version));
        }
        require_id("history domain", &self.history_domain)?;
        require_id("turn", &self.turn_id)?;
        match (self.sequence, self.previous_receipt) {
            (0, None) | (1.., Some(_)) => {}
            _ => return Err(SemanticTurnError::InvalidHistoryLink),
        }
        if let Some(previous) = &self.previous_receipt {
            require_id("previous receipt", previous)?;
        }
        self.request.validate()?;
        validate_state("pre", &self.pre)?;
        if semantic_state_id(&self.pre)? != self.request.pre_state_root {
            return Err(SemanticTurnError::PreStateRootMismatch);
        }
        match &self.outcome {
            TurnOutcome::Reject(rejection) => {
                require_id("denial statement", &rejection.denial_statement_id)?;
            }
            TurnOutcome::Commit(commit) => {
                validate_state("post", &commit.post)?;
                if commit.post.len() != self.pre.len() || commit.touched.len() != self.pre.len() {
                    return Err(SemanticTurnError::Core(
                        SemanticReceiptRelationError::Shape {
                            pre: self.pre.len(),
                            post: commit.post.len(),
                            touched: commit.touched.len(),
                        },
                    ));
                }
                if semantic_state_id(&commit.post)? != commit.post_state_root {
                    return Err(SemanticTurnError::PostStateRootMismatch);
                }
                require_id("authorization evidence", &commit.authorization.evidence_id)?;
                require_id("authorization state", &commit.authorization.auth_state_id)?;
                require_id("policy decision", &commit.authorization.policy_decision_id)?;
                require_id("effects relation", &commit.effects_relation_id)?;
                require_id("disclosure relation", &commit.disclosure_relation_id)?;
                validate_clauses(&commit.native_clauses)?;
                // Reuse the exact core relation for Booleanity and frame.
                SemanticReceiptWord {
                    binding: [1; 32],
                    pre: self.pre.clone(),
                    post: commit.post.clone(),
                    touched: commit.touched.clone(),
                }
                .validate()?;
            }
        }
        Ok(())
    }

    /// Canonical header bytes.  Raw state cells are bound by pre/post roots and
    /// by the accumulated core word, so they are not duplicated here.
    pub fn canonical_header_bytes(&self) -> Result<Vec<u8>, SemanticTurnError> {
        self.validate_structure()?;
        let mut out = HEADER_TAG.to_vec();
        out.extend_from_slice(&self.version.to_le_bytes());
        out.extend_from_slice(&self.history_domain);
        out.extend_from_slice(&self.sequence.to_le_bytes());
        match self.previous_receipt {
            None => out.push(0),
            Some(previous) => {
                out.push(1);
                out.extend_from_slice(&previous);
            }
        }
        out.extend_from_slice(&self.turn_id);
        encode_request(&mut out, &self.request);
        match &self.outcome {
            TurnOutcome::Reject(rejection) => {
                out.push(0);
                out.extend_from_slice(&rejection.error_code.to_le_bytes());
                out.extend_from_slice(&rejection.denial_statement_id);
            }
            TurnOutcome::Commit(commit) => {
                out.push(1);
                out.push(commit.authorization.kind as u8);
                out.extend_from_slice(&commit.authorization.evidence_id);
                out.extend_from_slice(&commit.authorization.auth_state_id);
                out.extend_from_slice(&commit.authorization.policy_decision_id);
                out.extend_from_slice(&commit.post_state_root);
                out.extend_from_slice(&commit.effects_relation_id);
                out.extend_from_slice(&commit.disclosure_relation_id);
                let count = u32::try_from(commit.native_clauses.len())
                    .map_err(|_| SemanticTurnError::LengthOverflow)?;
                out.extend_from_slice(&count.to_le_bytes());
                for clause in &commit.native_clauses {
                    out.extend_from_slice(&clause.relation_id);
                    out.extend_from_slice(&clause.statement_id);
                    out.extend_from_slice(clause.commitment_root.as_bytes());
                }
            }
        }
        Ok(out)
    }

    pub fn binding_id(&self) -> Result<SemanticId, SemanticTurnError> {
        let bytes = self.canonical_header_bytes()?;
        let mut hash = Sha3_256::new();
        hash.update(b"minidregg/semantic-turn-binding/v1");
        hash.update((bytes.len() as u64).to_le_bytes());
        hash.update(bytes);
        Ok(hash.finalize().into())
    }
}

impl TypedRequest {
    fn validate(&self) -> Result<(), SemanticTurnError> {
        for (name, id) in [
            ("request domain", &self.domain),
            ("semantics", &self.semantics),
            ("federation", &self.federation),
            ("subject", &self.subject),
            ("target", &self.target),
            ("args digest", &self.args_digest),
            ("effects digest", &self.effects_digest),
            ("pre-state root", &self.pre_state_root),
            ("policy", &self.policy_id),
        ] {
            require_id(name, id)?;
        }
        if !self.verb.accepts(self.resource_kind) {
            return Err(SemanticTurnError::VerbKindMismatch);
        }
        Ok(())
    }
}

pub fn semantic_state_id(values: &[u64]) -> Result<SemanticId, SemanticTurnError> {
    validate_state("state", values)?;
    let len = u64::try_from(values.len()).map_err(|_| SemanticTurnError::LengthOverflow)?;
    let mut hash = Sha3_256::new();
    hash.update(STATE_TAG);
    hash.update(len.to_le_bytes());
    for value in values {
        hash.update(value.to_le_bytes());
    }
    Ok(hash.finalize().into())
}

fn encode_request(out: &mut Vec<u8>, request: &TypedRequest) {
    out.extend_from_slice(&request.domain);
    out.extend_from_slice(&request.semantics);
    out.extend_from_slice(&request.federation);
    out.extend_from_slice(&request.subject);
    out.extend_from_slice(&request.subject_key_epoch.to_le_bytes());
    out.push(request.resource_kind as u8);
    out.extend_from_slice(&request.target);
    out.push(request.verb as u8);
    out.extend_from_slice(&request.args_digest);
    out.extend_from_slice(&request.effects_digest);
    out.extend_from_slice(&request.nonce.to_le_bytes());
    out.extend_from_slice(&request.height.to_le_bytes());
    out.extend_from_slice(&request.pre_state_root);
    out.extend_from_slice(&request.policy_id);
    out.extend_from_slice(&request.policy_epoch.to_le_bytes());
    out.extend_from_slice(&request.cost.to_le_bytes());
}

fn validate_clauses(clauses: &[NativeClauseBinding]) -> Result<(), SemanticTurnError> {
    let mut previous = None;
    for clause in clauses {
        require_id("native relation", &clause.relation_id)?;
        require_id("native statement", &clause.statement_id)?;
        if previous.is_some_and(|prior| prior >= clause.relation_id) {
            return Err(SemanticTurnError::InvalidClauseOrder);
        }
        previous = Some(clause.relation_id);
    }
    Ok(())
}

fn validate_state(section: &'static str, values: &[u64]) -> Result<(), SemanticTurnError> {
    if values.is_empty() {
        return Err(SemanticTurnError::EmptyState);
    }
    for (index, &value) in values.iter().enumerate() {
        if value >= P {
            return Err(SemanticTurnError::NonCanonicalState {
                section,
                index,
                value,
            });
        }
    }
    Ok(())
}

fn require_id(name: &'static str, id: &SemanticId) -> Result<(), SemanticTurnError> {
    if id.iter().all(|byte| *byte == 0) {
        Err(SemanticTurnError::EmptyId(name))
    } else {
        Ok(())
    }
}
