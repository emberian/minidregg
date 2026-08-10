/-
# Assurance.SemanticHistoryFamilyInstances -- turn and hyperedge admission

These are the first two exact `EntrySemanticsFamily` instances:

* a singular `SemanticTurnReceipt`, including receipts derived by
  `DeclaredTurnReceipt`;
* a flat `DeclaredHyperedge`, retaining its proof-relevant
  `SemanticOutcome` and, on commit, the full `CommittedHyperedge`.

The hyperedge header projections consume the complete declaration.  No
incidence is selected or encoded as a primary request.  Their deployed
canonical encodings/digests are the named `[HISTORY-HEADER-HASH]` seam, just as
for the singular header codec; supplying these Lean functions proves no
cryptographic collision-resistance claim.
-/

import Assurance.SemanticHistoryFamily
import Assurance.DeclaredTurnReceipt
import Assurance.DeclaredHyperedgeReceipt

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

/-! ## Flat declared-hyperedge family -/

section Hyperedge

open Minidregg.Kernel.DeclaredHyperedge
open Minidregg.Assurance.DeclaredHyperedgeReceipt
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.CellState

variable {portal : Portal}
variable
  {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
variable {Incidence : Type} [Fintype Incidence] [DecidableEq Incidence]

/-- Exact whole-hyperedge projections used by the public header.  Every
function consumes the full declaration, so authorization/effect/presentation
roots may commit ordered data for every incidence without inventing a primary
request. -/
structure HyperedgeHeaderProjection where
  semanticObjectRoot :
    Declaration portal materializer Incidence → Digest
  effectRoot : Declaration portal materializer Incidence → Digest
  authorizationRoot :
    Declaration portal materializer Incidence → Digest
  disclosureRoot : Declaration portal materializer Incidence → Digest
  rejectReasonId : Minidregg.Kernel.DeclaredHyperedge.RejectReason → Digest

def HyperedgeOutcome.admissionOutcome
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    (reasonId : Minidregg.Kernel.DeclaredHyperedge.RejectReason → Digest) :
    SemanticOutcome projection declaration → AdmissionOutcome
  | .rejected reason _ => .rejected (reasonId reason)
  | .committed _ _ _ => .committed

def HyperedgeOutcome.postRoot
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {n : Nat} {F : Type*}
    (model : BoundedModel declaration n F) :
    SemanticOutcome projection declaration → Digest
  | .rejected _ _ =>
      model.stateCommitment.root (model.project declaration.preStore)
  | .committed postStore _ _ =>
      model.stateCommitment.root (model.project postStore)

def hyperedgeHistoryWitness
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F)
    (headerCells : HistoryAdmissionContext → BindingIx → F)
    (context : HistoryAdmissionContext) : BoundReceiptWitness n F where
  binding := headerCells context
  core := executeCore projection declaration model

def hyperedgeHistoryClaim
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F)
    (headerCells : HistoryAdmissionContext → BindingIx → F)
    (context : HistoryAdmissionContext) : BoundSemanticReceiptClaim n F where
  witness := hyperedgeHistoryWitness projection declaration model
    headerCells context
  valid := executeCore_valid projection declaration model

/-- Exact evidence for one joint execution.  The proof-relevant outcome keeps
the literal `execute` equality and its `CommittedHyperedge` on success. -/
structure HyperedgeEvidence
    (headerProjection : HyperedgeHeaderProjection
      (portal := portal) (materializer := materializer)
      (Incidence := Incidence))
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F)
    (headerCells : HistoryAdmissionContext → BindingIx → F)
    (context : HistoryAdmissionContext)
    (claim : BoundSemanticReceiptClaim n F) : Type where
  outcome : SemanticOutcome projection declaration
  claimExact : claim = hyperedgeHistoryClaim projection declaration model
    headerCells context
  semanticObjectRootExact : context.semanticObjectRoot =
    headerProjection.semanticObjectRoot declaration
  semanticRelationExact : ∀ incidence,
    (declaration.legs incidence).request.semantics =
      context.semanticRelationId
  outcomeExact : context.outcome =
    HyperedgeOutcome.admissionOutcome headerProjection.rejectReasonId outcome
  preStateExact : context.preStateRoot =
    model.stateCommitment.root (model.project declaration.preStore)
  postStateExact : context.postStateRoot =
    HyperedgeOutcome.postRoot model outcome
  effectRootExact :
    context.effectRoot = headerProjection.effectRoot declaration
  authorizationRootExact : context.authorizationRoot =
    headerProjection.authorizationRoot declaration
  disclosureRootExact :
    context.disclosureRoot = headerProjection.disclosureRoot declaration

/-- Flat hyperedges instantiate the same generic history family.  Rejection
atomicity is inherited from the exact `DeclaredHyperedge.execute` branch. -/
def hyperedgeFamily
    (headerProjection : HyperedgeHeaderProjection
      (portal := portal) (materializer := materializer)
      (Incidence := Incidence))
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F)
    (headerCells : HistoryAdmissionContext → BindingIx → F) :
    EntrySemanticsFamily n F where
  Evidence := HyperedgeEvidence headerProjection projection declaration model
    headerCells
  rejectedCoreAtomic := by
    intro context claim evidence denial rejected
    rw [evidence.claimExact]
    cases outcomeEq : evidence.outcome with
    | rejected reason executed =>
        exact executeCore_rejected_atomic projection declaration model reason
          executed
    | committed postStore executed semantic =>
        have outcomeExact := evidence.outcomeExact
        rw [rejected, outcomeEq] at outcomeExact
        simp [HyperedgeOutcome.admissionOutcome] at outcomeExact

namespace HyperedgeEvidence

variable
    {headerProjection : HyperedgeHeaderProjection
      (portal := portal) (materializer := materializer)
      (Incidence := Incidence)}
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
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
    (evidence : HyperedgeEvidence headerProjection projection declaration
      model headerCells context claim)
    (contextWellFormed : context.WellFormed manifest)
    (dialectEvidence :
      ClauseEvidenceCoverage clauseEvidence context.dialectClauseRoots)
    (bindingExact : claim.witness.binding = headerCells context)
    (codeword : claim.witness.encode ∈ C) :
    Minidregg.Assurance.SemanticHistoryFamily.VerifiedEntry
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence)
      (family := hyperedgeFamily headerProjection projection declaration model
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
    (evidence : HyperedgeEvidence headerProjection projection declaration
      model headerCells context claim) :
    SemanticOutcome projection declaration :=
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
