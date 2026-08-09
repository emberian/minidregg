/-
# Assurance.PrivateComputationReceiptClause — private completion as a receipt event

This file joins `PrivateComputationDeclaration.Completion` to the common
`SemanticTurnReceipt` disclosure seam.  The join is proof-relevant and positive:
only a completed private request produces an event, and only a committed turn can
record one.  Rejected turns and committed turns with an empty disclosure list do
not denote a release.

The manifest binding below names a dialect clause and both representation
bridges.  It assigns no cryptographic meaning to a proof suite and invokes no
native verifier.  Mode-specific evidence remains ordinary Lean data accepted by
the abstract portal declared in `Theory.PrivateComputationDeclaration`.
-/
import Assurance.SemanticTurnReceipt
import Compiler.SemanticManifest
import Theory.PrivateComputationDeclaration

namespace Minidregg.Assurance.PrivateComputationReceiptClause

open Minidregg.Assurance.SemanticReceiptRelation
open Minidregg.Assurance.SemanticTurnReceipt
open Minidregg.Compiler.SemanticManifest
open Minidregg.Theory
open Minidregg.Theory.AuthorizationDeclaration
open Minidregg.Theory.ReactiveReceipt
open Minidregg.Theory.TypedAuthorization

/-! ## Manifest-bound dialect and bridge names -/

/-- The manifest vocabulary associated with one typed private-computation
declaration.  The private input bridge name is specialized to `Digest`, so its
semantic name can be bound exactly to a registered manifest bridge.  The output
bridge is likewise registered and required by the same dialect clause.

These fields are registry facts only.  In particular, `proofSuiteId` is not
interpreted here and registration is not evidence of cryptographic soundness. -/
structure ClauseBinding
    {language : PrivateComputationLanguage} {mode : PrivateComputationKind}
    {Observer Policy Recipient Purpose AuthorizationContext CanonicalInput SemanticInput
      InputSourceWitness InputTargetWitness AuthorizationWitness OutputCommitment
      PrivateOutput OutputSourceWitness OutputTargetWitness ReleaseAuthorizationWitness
      DeclassificationAuthority Release : Type*}
    (manifest : Manifest)
    (declaration : PrivateComputationDeclaration language mode Observer Policy Recipient
      Purpose Digest AuthorizationContext CanonicalInput SemanticInput InputSourceWitness
      InputTargetWitness AuthorizationWitness OutputCommitment PrivateOutput
      OutputSourceWitness OutputTargetWitness ReleaseAuthorizationWitness
      DeclassificationAuthority Release) where
  manifestWellFormed : manifest.WellFormed
  clause : DialectClauseDecl
  clauseRegistered : manifest.lookupClause clause.clauseId = some clause
  controllerBound : clause.verifierControllerDigest = manifest.transcriptControllerDigest
  inputBridge : NamedBridgeRequirement
  inputBridgeRegistered : manifest.lookupBridge inputBridge.bridgeId = some inputBridge
  inputBridgeNameExact : declaration.inputBridge.name = inputBridge.bridgeId
  inputBridgeRequired : inputBridge.bridgeId ∈ clause.requiredBridgeIds
  outputBridge : NamedBridgeRequirement
  outputBridgeRegistered : manifest.lookupBridge outputBridge.bridgeId = some outputBridge
  outputBridgeRequired : outputBridge.bridgeId ∈ clause.requiredBridgeIds

/-! ## Exact private-computation disclosure event -/

/-- A manifest and mode pin for the exact evidence accepted by the declaration.
The witness type is `language.Evidence mode`; evidence from another private
computation family therefore cannot inhabit this pin. -/
structure ModeEvidencePin
    {language : PrivateComputationLanguage} {mode : PrivateComputationKind}
    {Observer Policy Recipient Purpose AuthorizationContext CanonicalInput SemanticInput
      InputSourceWitness InputTargetWitness AuthorizationWitness OutputCommitment
      PrivateOutput OutputSourceWitness OutputTargetWitness ReleaseAuthorizationWitness
      DeclassificationAuthority Release : Type*}
    {manifest : Manifest}
    {declaration : PrivateComputationDeclaration language mode Observer Policy Recipient
      Purpose Digest AuthorizationContext CanonicalInput SemanticInput InputSourceWitness
      InputTargetWitness AuthorizationWitness OutputCommitment PrivateOutput
      OutputSourceWitness OutputTargetWitness ReleaseAuthorizationWitness
      DeclassificationAuthority Release}
    (binding : ClauseBinding manifest declaration)
    (request : declaration.Request) (outcome : declaration.Outcome) where
  modeTag : PrivateComputationKind
  modeExact : modeTag = mode
  clauseId : Digest
  clauseIdExact : clauseId = binding.clause.clauseId
  relationId : Digest
  relationIdExact : relationId = binding.clause.relationId
  checked : CheckedPrivateEvidence declaration.computationPortal
    (declaration.statementOf request outcome)

/-- The disclosure payload recorded by the common semantic turn receipt.  Its
first field binds it to an exact typed authorization request.  The remaining
fields are precisely the four proof legs of private completion, plus the
manifest/mode evidence pin. -/
structure ReceiptEvent
    {language : PrivateComputationLanguage} {mode : PrivateComputationKind}
    {Observer Policy Recipient Purpose AuthorizationContext CanonicalInput SemanticInput
      InputSourceWitness InputTargetWitness AuthorizationWitness OutputCommitment
      PrivateOutput OutputSourceWitness OutputTargetWitness ReleaseAuthorizationWitness
      DeclassificationAuthority Release : Type*}
    {manifest : Manifest}
    {declaration : PrivateComputationDeclaration language mode Observer Policy Recipient
      Purpose Digest AuthorizationContext CanonicalInput SemanticInput InputSourceWitness
      InputTargetWitness AuthorizationWitness OutputCommitment PrivateOutput
      OutputSourceWitness OutputTargetWitness ReleaseAuthorizationWitness
      DeclassificationAuthority Release}
    (binding : ClauseBinding manifest declaration) [DecidableEq Release] where
  turnRequest : SomeRequest
  privateRequest : declaration.Request
  outcome : declaration.Outcome
  authorization : CheckedPrivateEvidence declaration.authorizationPortal privateRequest
  inputIdentity : declaration.inputBridge.CheckedIdentity privateRequest.inputBridgeName
    privateRequest.canonicalInput privateRequest.computationInput privateRequest.inputValue
  evidence : ModeEvidencePin binding privateRequest outcome
  outputDisclosure : declaration.disclosureDeclaration.VerifiedRelease
    privateRequest.disclosureRequest outcome.output outcome.release
  disclosureDeclared :
    outcome.disclosureEffect =
      privateRequest.disclosureIntent.materialize outcome.release

namespace ReceiptEvent

variable
    {language : PrivateComputationLanguage} {mode : PrivateComputationKind}
    {Observer Policy Recipient Purpose AuthorizationContext CanonicalInput SemanticInput
      InputSourceWitness InputTargetWitness AuthorizationWitness OutputCommitment
      PrivateOutput OutputSourceWitness OutputTargetWitness ReleaseAuthorizationWitness
      DeclassificationAuthority Release : Type*}
    {manifest : Manifest}
    {declaration : PrivateComputationDeclaration language mode Observer Policy Recipient
      Purpose Digest AuthorizationContext CanonicalInput SemanticInput InputSourceWitness
      InputTargetWitness AuthorizationWitness OutputCommitment PrivateOutput
      OutputSourceWitness OutputTargetWitness ReleaseAuthorizationWitness
      DeclassificationAuthority Release}
    {binding : ClauseBinding manifest declaration}

/-- The unique positive constructor used by this join: materialize a receipt
event from an existing completion token and an exact common turn request. -/
def ofCompletion [DecidableEq Release]
    {kind : ResourceKind} (turnRequest : Request kind)
    {request : declaration.Request} {outcome : declaration.Outcome}
    (completion : declaration.Completion request outcome) : ReceiptEvent binding where
  turnRequest := ⟨kind, turnRequest⟩
  privateRequest := request
  outcome := outcome
  authorization := completion.authorization
  inputIdentity := completion.inputIdentity
  evidence := {
    modeTag := mode
    modeExact := rfl
    clauseId := binding.clause.clauseId
    clauseIdExact := rfl
    relationId := binding.clause.relationId
    relationIdExact := rfl
    checked := completion.computation
  }
  outputDisclosure := completion.outputDisclosure
  disclosureDeclared := completion.disclosureDeclared

/-- Forgetting the receipt/manifest wrapper reconstructs the exact original
semantic completion shape; none of its authority legs is weakened. -/
def toCompletion [DecidableEq Release] (event : ReceiptEvent binding) :
    declaration.Completion event.privateRequest event.outcome where
  authorization := event.authorization
  inputIdentity := event.inputIdentity
  computation := event.evidence.checked
  outputDisclosure := event.outputDisclosure
  disclosureDeclared := event.disclosureDeclared

/-- The event exposes the existing semantic relations rather than defining a
second privacy or release judgment. -/
theorem implies_declared_semantics [DecidableEq Release]
    (event : ReceiptEvent binding) :
    declaration.authorizationPortal.Accepts event.privateRequest
        event.authorization.witness ∧
      SameOpening declaration.inputBridge.sourceSemantics
        declaration.inputBridge.targetSemantics
        event.privateRequest.canonicalInput event.inputIdentity.sourceWitness
        event.privateRequest.computationInput event.inputIdentity.targetWitness ∧
      declaration.computationPortal.Accepts
        (declaration.statementOf event.privateRequest event.outcome)
        event.evidence.checked.witness ∧
      event.outcome.disclosureEffect =
        event.privateRequest.disclosureIntent.materialize event.outcome.release ∧
      (SameOpening
          declaration.disclosureDeclaration.sourceOpeningSemantics
          declaration.disclosureDeclaration.targetOpeningSemantics
          event.outcome.output.commitment
          event.outputDisclosure.sameOpening.witness.source
          event.outcome.output.representation
          event.outputDisclosure.sameOpening.witness.target ∧
        AuthorizedRelease declaration.disclosureDeclaration.releaseSemantics
          event.privateRequest.disclosureRequest
          event.privateRequest.disclosureRequest.recipient
          event.privateRequest.disclosureRequest.purpose
          event.outcome.output.privateOutput event.outcome.release) :=
  event.toCompletion.implies_declared_semantics

/-- The input bridge recorded by an event is both its checked semantic name and
the exact manifest-required bridge identifier. -/
theorem input_bridge_name_bound [DecidableEq Release]
    (event : ReceiptEvent binding) :
    event.privateRequest.inputBridgeName = binding.inputBridge.bridgeId := by
  exact event.inputIdentity.nameBound.trans binding.inputBridgeNameExact

/-- Both representation identities are paired with their registered manifest
names.  The names themselves add no hiding claim; the semantic content is still
exactly the two existing `SameOpening` relations. -/
theorem named_representation_identities [DecidableEq Release]
    (event : ReceiptEvent binding) :
    event.privateRequest.inputBridgeName = binding.inputBridge.bridgeId ∧
      manifest.lookupBridge binding.inputBridge.bridgeId = some binding.inputBridge ∧
      SameOpening declaration.inputBridge.sourceSemantics
        declaration.inputBridge.targetSemantics
        event.privateRequest.canonicalInput event.inputIdentity.sourceWitness
        event.privateRequest.computationInput event.inputIdentity.targetWitness ∧
      manifest.lookupBridge binding.outputBridge.bridgeId = some binding.outputBridge ∧
      SameOpening
        declaration.disclosureDeclaration.sourceOpeningSemantics
        declaration.disclosureDeclaration.targetOpeningSemantics
        event.outcome.output.commitment
        event.outputDisclosure.sameOpening.witness.source
        event.outcome.output.representation
        event.outputDisclosure.sameOpening.witness.target := by
  have semantics := event.implies_declared_semantics
  exact ⟨event.input_bridge_name_bound, binding.inputBridgeRegistered,
    semantics.2.1, binding.outputBridgeRegistered, semantics.2.2.2.2.1⟩

end ReceiptEvent

/-! ## Common `SemanticTurnReceipt` disclosure clause -/

variable
    {language : PrivateComputationLanguage} {mode : PrivateComputationKind}
    {Observer Policy Recipient Purpose AuthorizationContext CanonicalInput SemanticInput
      InputSourceWitness InputTargetWitness AuthorizationWitness OutputCommitment
      PrivateOutput OutputSourceWitness OutputTargetWitness ReleaseAuthorizationWitness
      DeclassificationAuthority Release : Type*}
    {manifest : Manifest}
    {declaration : PrivateComputationDeclaration language mode Observer Policy Recipient
      Purpose Digest AuthorizationContext CanonicalInput SemanticInput InputSourceWitness
      InputTargetWitness AuthorizationWitness OutputCommitment PrivateOutput
      OutputSourceWitness OutputTargetWitness ReleaseAuthorizationWitness
      DeclassificationAuthority Release}
    (binding : ClauseBinding manifest declaration)

/-- The common receipt policy does one additional job: it binds an already
proof-relevant private event to the exact dependent authorization request of the
surrounding turn.  All release authority remains inside `ReceiptEvent`. -/
def disclosurePolicy [DecidableEq Release] :
    DisclosurePolicy (ReceiptEvent binding) where
  Permitted := fun {kind} request event => event.turnRequest = ⟨kind, request⟩

theorem ofCompletion_permitted [DecidableEq Release]
    {kind : ResourceKind} (turnRequest : Request kind)
    {request : declaration.Request} {outcome : declaration.Outcome}
    (completion : declaration.Completion request outcome) :
    (disclosurePolicy binding).Permitted turnRequest
      (ReceiptEvent.ofCompletion (binding := binding) turnRequest completion) :=
  rfl

/-- Add one completed private event to an already valid common committed turn.
Typed turn authorization, state transition, effects, and earlier disclosures
are preserved verbatim. -/
def recordCompletion [DecidableEq Release]
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {Key Value Effect : Type*} [DecidableEq Key]
    {stateCommitment : StateCommitment Key Value}
    {effectSemantics : EffectSemantics Key Value Effect}
    {turnRequest : Request kind} {pre : Store Key Value}
    (commit : CommittedTurn portal authState turnRequest stateCommitment effectSemantics
      (disclosurePolicy binding) pre)
    {request : declaration.Request} {outcome : declaration.Outcome}
    (completion : declaration.Completion request outcome) :
    CommittedTurn portal authState turnRequest stateCommitment effectSemantics
      (disclosurePolicy binding) pre where
  authorization := commit.authorization
  post := commit.post
  delta := commit.delta
  postStateRoot := commit.postStateRoot
  postRootBound := commit.postRootBound
  effects := commit.effects
  effectsDigestBound := commit.effectsDigestBound
  effectsRealize := commit.effectsRealize
  disclosures := ReceiptEvent.ofCompletion (binding := binding) turnRequest completion ::
    commit.disclosures
  disclosuresPermitted := by
    intro event member
    rcases List.mem_cons.mp member with rfl | old
    · exact ofCompletion_permitted binding turnRequest completion
    · exact commit.disclosuresPermitted event old

@[simp] theorem recordCompletion_disclosures [DecidableEq Release]
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {Key Value Effect : Type*} [DecidableEq Key]
    {stateCommitment : StateCommitment Key Value}
    {effectSemantics : EffectSemantics Key Value Effect}
    {turnRequest : Request kind} {pre : Store Key Value}
    (commit : CommittedTurn portal authState turnRequest stateCommitment effectSemantics
      (disclosurePolicy binding) pre)
    {request : declaration.Request} {outcome : declaration.Outcome}
    (completion : declaration.Completion request outcome) :
    (recordCompletion binding commit completion).disclosures =
      ReceiptEvent.ofCompletion (binding := binding) turnRequest completion ::
        commit.disclosures :=
  rfl

/-- The augmented committed turn reaches the same common algebraic receipt
relation.  Private-computation evidence is a disclosure clause; it does not
replace the state-transition relation or claim a native cryptographic theorem. -/
theorem recordCompletion_coreRelation [DecidableEq Release]
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {Key F Effect : Type*} [Fintype Key] [DecidableEq Key]
    [Field F] [DecidableEq F]
    {stateCommitment : StateCommitment Key F}
    {effectSemantics : EffectSemantics Key F Effect}
    {turnRequest : Request kind} {pre : Store Key F}
    (commit : CommittedTurn portal authState turnRequest stateCommitment effectSemantics
      (disclosurePolicy binding) pre)
    {request : declaration.Request} {outcome : declaration.Outcome}
    (completion : declaration.Completion request outcome) :
    SemanticReceiptRelation
      (recordCompletion binding commit completion).coreClaim.witness.encode :=
  (recordCompletion binding commit completion).coreRelation

/-! ## Fail-closed release observation -/

/-- A private release is recorded only by a committed branch containing at
least one `ReceiptEvent`.  This proposition deliberately has no fallback from
an error, an absent completion, or an empty disclosure list. -/
def RecordsPrivateRelease [DecidableEq Release]
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {Key Value Effect Error : Type*} [DecidableEq Key]
    {stateCommitment : StateCommitment Key Value}
    {effectSemantics : EffectSemantics Key Value Effect}
    (receipt : TurnReceipt portal authState kind Error stateCommitment effectSemantics
      (disclosurePolicy binding)) : Prop :=
  match receipt.outcome with
  | .inl _ => False
  | .inr commit => ∃ event, event ∈ commit.disclosures

theorem rejected_not_released [DecidableEq Release]
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {Key Value Effect Error : Type*} [DecidableEq Key]
    {stateCommitment : StateCommitment Key Value}
    {effectSemantics : EffectSemantics Key Value Effect}
    (turnRequest : Request kind) (pre : Store Key Value)
    (preRootBound : turnRequest.preStateRoot = stateCommitment.root pre)
    (error : Error) :
    ¬ RecordsPrivateRelease binding
      (TurnReceipt.rejected (portal := portal) (authState := authState)
        (effectSemantics := effectSemantics)
        (disclosurePolicy := disclosurePolicy binding)
        turnRequest pre preRootBound error) := by
  simp [RecordsPrivateRelease, TurnReceipt.rejected]

theorem empty_disclosures_not_released [DecidableEq Release]
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {Key Value Effect Error : Type*} [DecidableEq Key]
    {stateCommitment : StateCommitment Key Value}
    {effectSemantics : EffectSemantics Key Value Effect}
    {turnRequest : Request kind} {pre : Store Key Value}
    (preRootBound : turnRequest.preStateRoot = stateCommitment.root pre)
    (commit : CommittedTurn portal authState turnRequest stateCommitment effectSemantics
      (disclosurePolicy binding) pre)
    (empty : commit.disclosures = []) :
    ¬ RecordsPrivateRelease binding
      (TurnReceipt.committed (Error := Error) turnRequest pre preRootBound commit) := by
  simp [RecordsPrivateRelease, TurnReceipt.committed, empty]

theorem recorded_after_completion [DecidableEq Release]
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {Key Value Effect Error : Type*} [DecidableEq Key]
    {stateCommitment : StateCommitment Key Value}
    {effectSemantics : EffectSemantics Key Value Effect}
    {turnRequest : Request kind} {pre : Store Key Value}
    (preRootBound : turnRequest.preStateRoot = stateCommitment.root pre)
    (commit : CommittedTurn portal authState turnRequest stateCommitment effectSemantics
      (disclosurePolicy binding) pre)
    {request : declaration.Request} {outcome : declaration.Outcome}
    (completion : declaration.Completion request outcome) :
    RecordsPrivateRelease binding
      (TurnReceipt.committed (Error := Error) turnRequest pre preRootBound
        (recordCompletion binding commit completion)) := by
  simp [RecordsPrivateRelease, TurnReceipt.committed]

end Minidregg.Assurance.PrivateComputationReceiptClause
