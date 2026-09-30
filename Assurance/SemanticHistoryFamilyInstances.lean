/-
# Assurance.SemanticHistoryFamilyInstances -- turn and hyperedge admission

These are the first two exact `EntrySemanticsFamily` instances:

* a singular `SemanticTurnReceipt`, including receipts derived by
  `DeclaredTurnReceipt`;
* a flat `TypedCellHyperedge`, retaining its proof-relevant
  `SemanticOutcome`: on commit the full `Commit`, on rejection the proof that
  no commit exists.

The hyperedge header projections consume the complete declaration.  No
incidence is selected or encoded as a primary request.  Their deployed
canonical encodings/digests are the named `[HISTORY-HEADER-HASH]` seam, just as
for the singular header codec; supplying these Lean functions proves no
cryptographic collision-resistance claim.
-/

import Assurance.SemanticHistoryFamily
import Assurance.DeclaredTurnReceipt
import Assurance.TypedCellHyperedgeReceipt

namespace Minidregg.Assurance.SemanticHistoryFamilyInstances

open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Assurance.SemanticReceiptRelation
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.SemanticTurnReceipt
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ReactiveReceipt

set_option autoImplicit false

universe uF uEffect uDisclosure uError uSemantics
  uClauseInput uClauseQuery uClauseReply uClauseOutcome uClauseEvidence

noncomputable section

/-! ## Singular turn family -/

section Singular

variable
    {n : Nat} {F : Type uF} [Field F] [DecidableEq F]
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {Effect : Type uEffect} {Disclosure : Type uDisclosure}
    {Error : Type uError}
    {stateCommitment : StateCommitment (Fin n) F}
    {effectSemantics : EffectSemantics (Fin n) F Effect}
    {disclosurePolicy : DisclosurePolicy Disclosure}

local notation "Turn" => SemanticTurn n F portal authState kind Effect
  Disclosure Error stateCommitment effectSemantics disclosurePolicy

/-- Lean-owned projections of the complete singular semantic object into the
public header.  In particular `semanticObjectRoot` consumes the whole receipt,
not merely a resource identifier. -/
structure TurnHeaderProjection where
  semanticObjectRoot : Turn → Digest
  effectRoot : Turn → Digest
  authorizationRoot : Turn → Digest
  disclosureRoot : Turn → Digest
  errorId : Error → Digest

def turnHistoryWitness
    (headerCells : HistoryAdmissionContext → BindingIx → F)
    (context : HistoryAdmissionContext) (receipt : Turn) :
    BoundReceiptWitness n F where
  binding := headerCells context
  core := historyCore receipt

def turnHistoryClaim
    (headerCells : HistoryAdmissionContext → BindingIx → F)
    (context : HistoryAdmissionContext) (receipt : Turn) :
    BoundSemanticReceiptClaim n F where
  witness := turnHistoryWitness headerCells context receipt
  valid := historyCore_valid receipt

/-- Complete evidence that the generic public context and exact accumulated
claim are the singular receipt's own projections. -/
structure TurnEvidence
    (projection : TurnHeaderProjection (n := n) (F := F)
      (portal := portal) (authState := authState) (kind := kind)
      (Effect := Effect) (Disclosure := Disclosure) (Error := Error)
      (stateCommitment := stateCommitment)
      (effectSemantics := effectSemantics)
      (disclosurePolicy := disclosurePolicy))
    (headerCells : HistoryAdmissionContext → BindingIx → F)
    (context : HistoryAdmissionContext)
    (claim : BoundSemanticReceiptClaim n F) : Type _ where
  receipt : Turn
  claimExact : claim = turnHistoryClaim headerCells context receipt
  semanticObjectRootExact :
    context.semanticObjectRoot = projection.semanticObjectRoot receipt
  semanticRelationExact :
    context.semanticRelationId = receipt.request.semantics
  outcomeExact :
    context.outcome = receiptAdmissionOutcome projection.errorId receipt
  preStateExact :
    context.preStateRoot = stateCommitment.root receipt.pre
  postStateExact :
    context.postStateRoot = stateCommitment.root receipt.post
  effectRootExact : context.effectRoot = projection.effectRoot receipt
  authorizationRootExact :
    context.authorizationRoot = projection.authorizationRoot receipt
  disclosureRootExact :
    context.disclosureRoot = projection.disclosureRoot receipt

/-- Singular turns instantiate the generic entry semantics without changing
their existing semantic core. -/
def turnFamily
    (projection : TurnHeaderProjection (n := n) (F := F)
      (portal := portal) (authState := authState) (kind := kind)
      (Effect := Effect) (Disclosure := Disclosure) (Error := Error)
      (stateCommitment := stateCommitment)
      (effectSemantics := effectSemantics)
      (disclosurePolicy := disclosurePolicy))
    (headerCells : HistoryAdmissionContext → BindingIx → F) :
    EntrySemanticsFamily.{max uF uEffect uDisclosure uError} n F where
  Evidence := TurnEvidence projection headerCells
  rejectedCoreAtomic := by
    intro context claim evidence denial rejected
    rw [evidence.claimExact]
    cases receiptOutcome : evidence.receipt.outcome with
    | inl error =>
        exact historyCore_reject_atomic evidence.receipt receiptOutcome
    | inr commit =>
        have outcomeExact := evidence.outcomeExact
        rw [rejected] at outcomeExact
        simp [receiptAdmissionOutcome, receiptOutcome] at outcomeExact

namespace TurnEvidence

variable
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {projection : TurnHeaderProjection (n := n) (F := F)
      (portal := portal) (authState := authState) (kind := kind)
      (Effect := Effect) (Disclosure := Disclosure) (Error := Error)
      (stateCommitment := stateCommitment)
      (effectSemantics := effectSemantics)
      (disclosurePolicy := disclosurePolicy)}
    {headerCells : HistoryAdmissionContext → BindingIx → F}
    {context : HistoryAdmissionContext}
    {claim : BoundSemanticReceiptClaim n F}
    {C : Submodule F (BoundReceiptIx n → F)}

/-- Package exact singular evidence into an entry accepted by the generic
history.  `DeclaredTurnReceipt.canonicalReceipt` supplies `receipt` for the
executable declared-turn path. -/
def toVerifiedEntry
    (evidence : TurnEvidence projection headerCells context claim)
    (contextWellFormed : context.WellFormed manifest)
    (dialectEvidence :
      ClauseEvidenceCoverage clauseEvidence context.dialectClauseRoots)
    (bindingExact : claim.witness.binding = headerCells context)
    (codeword : claim.witness.encode ∈ C) :
    Minidregg.Assurance.SemanticHistoryFamily.VerifiedEntry
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence)
      (family := turnFamily projection headerCells)
      (headerCells := headerCells) (C := C) where
  context := context
  claim := claim
  semantics := evidence
  contextWellFormed := contextWellFormed
  dialectEvidence := dialectEvidence
  bindingExact := bindingExact
  codeword := codeword

end TurnEvidence

end Singular

/-! ## Flat typed-hyperedge family -/

section Hyperedge

open Minidregg.Kernel.TypedCellHyperedge
open Minidregg.Assurance.TypedCellHyperedgeReceipt

universe uL vL wL

variable {L : Minidregg.Theory.Store.Layout.{uL, vL, wL}}
variable {M : Minidregg.Theory.CellState.Materializer L Digest}
variable {portal : Portal} {projection : AuthorizationProjection L}
variable {Incidence : Type} [Fintype Incidence]
variable {Coordinate : Type} {Balance : Type} [AddCommMonoid Balance]

/-- Exact whole-hyperedge projections used by the public header.  Every
function consumes the full declaration, so authorization/effect/presentation
roots may commit ordered data for every incidence without inventing a primary
request. -/
structure HyperedgeHeaderProjection where
  semanticObjectRoot :
    Declaration.{uL, vL, wL, 0, 0} L M portal projection Incidence → Digest
  effectRoot : Declaration.{uL, vL, wL, 0, 0} L M portal projection Incidence → Digest
  authorizationRoot :
    Declaration.{uL, vL, wL, 0, 0} L M portal projection Incidence → Digest
  disclosureRoot : Declaration.{uL, vL, wL, 0, 0} L M portal projection Incidence → Digest
  rejectReasonId : TypedCellHyperedgeReceipt.RejectReason → Digest

variable {law : ResourceLaw.{uL, vL, wL, 0, 0} L M portal Coordinate Balance}

def HyperedgeOutcome.admissionOutcome
    {declaration : Declaration.{uL, vL, wL, 0, 0} L M portal projection Incidence}
    (reasonId : TypedCellHyperedgeReceipt.RejectReason → Digest) :
    SemanticOutcome law declaration → AdmissionOutcome
  | .rejected reason _ => .rejected (reasonId reason)
  | .committed _ => .committed

def HyperedgeOutcome.postRoot
    {declaration : Declaration.{uL, vL, wL, 0, 0} L M portal projection Incidence}
    {n : Nat} {F : Type*}
    (model : BoundedModel declaration n F) :
    SemanticOutcome law declaration → Digest
  | .rejected _ _ =>
      model.stateCommitment.root (model.project declaration.pre.logical)
  | .committed _ =>
      model.stateCommitment.root (model.project model.postStore)

def hyperedgeHistoryWitness
    {declaration : Declaration.{uL, vL, wL, 0, 0} L M portal projection Incidence}
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F)
    (outcome : SemanticOutcome law declaration)
    (headerCells : HistoryAdmissionContext → BindingIx → F)
    (context : HistoryAdmissionContext) : BoundReceiptWitness n F where
  binding := headerCells context
  core := outcome.core model

def hyperedgeHistoryClaim
    {declaration : Declaration.{uL, vL, wL, 0, 0} L M portal projection Incidence}
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F)
    (outcome : SemanticOutcome law declaration)
    (headerCells : HistoryAdmissionContext → BindingIx → F)
    (context : HistoryAdmissionContext) : BoundSemanticReceiptClaim n F where
  witness := hyperedgeHistoryWitness model outcome headerCells context
  valid := outcome.core_valid model

/-- Exact evidence for one joint turn.  The proof-relevant outcome keeps the
`Commit` on success and the refusal proof on rejection. -/
structure HyperedgeEvidence
    (headerProjection : HyperedgeHeaderProjection
      (L := L) (M := M) (portal := portal) (projection := projection)
      (Incidence := Incidence))
    (law : ResourceLaw.{uL, vL, wL, 0, 0} L M portal Coordinate Balance)
    (declaration : Declaration.{uL, vL, wL, 0, 0} L M portal projection Incidence)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F)
    (headerCells : HistoryAdmissionContext → BindingIx → F)
    (context : HistoryAdmissionContext)
    (claim : BoundSemanticReceiptClaim n F) : Type where
  outcome : SemanticOutcome law declaration
  claimExact : claim = hyperedgeHistoryClaim model outcome headerCells context
  semanticObjectRootExact : context.semanticObjectRoot =
    headerProjection.semanticObjectRoot declaration
  semanticRelationExact : ∀ incidence,
    (declaration.legs incidence).request.semantics =
      context.semanticRelationId
  outcomeExact : context.outcome =
    HyperedgeOutcome.admissionOutcome headerProjection.rejectReasonId outcome
  preStateExact : context.preStateRoot =
    model.stateCommitment.root (model.project declaration.pre.logical)
  postStateExact : context.postStateRoot =
    HyperedgeOutcome.postRoot model outcome
  effectRootExact :
    context.effectRoot = headerProjection.effectRoot declaration
  authorizationRootExact : context.authorizationRoot =
    headerProjection.authorizationRoot declaration
  disclosureRootExact :
    context.disclosureRoot = headerProjection.disclosureRoot declaration

/-- Flat hyperedges instantiate the same generic history family.  Rejection
atomicity is the rejected core's, which a refusal proof selects. -/
def hyperedgeFamily
    (headerProjection : HyperedgeHeaderProjection
      (L := L) (M := M) (portal := portal) (projection := projection)
      (Incidence := Incidence))
    (law : ResourceLaw.{uL, vL, wL, 0, 0} L M portal Coordinate Balance)
    (declaration : Declaration.{uL, vL, wL, 0, 0} L M portal projection Incidence)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F)
    (headerCells : HistoryAdmissionContext → BindingIx → F) :
    EntrySemanticsFamily n F where
  Evidence := HyperedgeEvidence headerProjection law declaration model headerCells
  rejectedCoreAtomic := by
    intro context claim evidence denial rejected
    rw [evidence.claimExact]
    have outcomeExact := evidence.outcomeExact
    cases outcomeEq : evidence.outcome with
    | rejected reason refused =>
        exact SemanticOutcome.core_rejected_atomic model reason refused
    | committed commit =>
        rw [rejected, outcomeEq] at outcomeExact
        simp [HyperedgeOutcome.admissionOutcome] at outcomeExact

namespace HyperedgeEvidence

variable
    {headerProjection : HyperedgeHeaderProjection
      (L := L) (M := M) (portal := portal) (projection := projection)
      (Incidence := Incidence)}
    {declaration : Declaration.{uL, vL, wL, 0, 0} L M portal projection Incidence}
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    {model : BoundedModel declaration n F}
    {headerCells : HistoryAdmissionContext → BindingIx → F}
    {context : HistoryAdmissionContext}
    {claim : BoundSemanticReceiptClaim n F}
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {C : Submodule F (BoundReceiptIx n → F)}

/-- Package exact joint semantic evidence into an entry accepted by the same
generic history constructor used for singular turns. -/
def toVerifiedEntry
    (evidence : HyperedgeEvidence headerProjection law declaration
      model headerCells context claim)
    (contextWellFormed : context.WellFormed manifest)
    (dialectEvidence :
      ClauseEvidenceCoverage clauseEvidence context.dialectClauseRoots)
    (bindingExact : claim.witness.binding = headerCells context)
    (codeword : claim.witness.encode ∈ C) :
    Minidregg.Assurance.SemanticHistoryFamily.VerifiedEntry
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence)
      (family := hyperedgeFamily headerProjection law declaration model
        headerCells)
      (headerCells := headerCells) (C := C) where
  context := context
  claim := claim
  semantics := evidence
  contextWellFormed := contextWellFormed
  dialectEvidence := dialectEvidence
  bindingExact := bindingExact
  codeword := codeword

/-- The exact semantic outcome retained by an admitted hyperedge entry. -/
def retainedOutcome
    (evidence : HyperedgeEvidence headerProjection law declaration
      model headerCells context claim) :
    SemanticOutcome law declaration :=
  evidence.outcome

end HyperedgeEvidence

end Hyperedge

/-- info: 'Minidregg.Assurance.SemanticHistoryFamilyInstances.turnFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms turnFamily
/-- info: 'Minidregg.Assurance.SemanticHistoryFamilyInstances.TurnEvidence.toVerifiedEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms TurnEvidence.toVerifiedEntry
/-- info: 'Minidregg.Assurance.SemanticHistoryFamilyInstances.hyperedgeFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hyperedgeFamily
/-- info: 'Minidregg.Assurance.SemanticHistoryFamilyInstances.HyperedgeEvidence.toVerifiedEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HyperedgeEvidence.toVerifiedEntry
/-- info: 'Minidregg.Assurance.SemanticHistoryFamilyInstances.HyperedgeEvidence.retainedOutcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HyperedgeEvidence.retainedOutcome

end


end Minidregg.Assurance.SemanticHistoryFamilyInstances
