/-
# Assurance.AcceptedCellEffectHistory -- canonical cell effects enter history

`Theory.AcceptedCellEffect` is the positive semantic object for ordinary,
private, and reactive effect families.  This module sends that object directly
to the common bounded receipt/history word.  It does not first manufacture a
legacy `SemanticTurnReceipt`, and it does not attach mode evidence to an
unrelated commit.

The only additional datum is one family-wide, Lean-authored projection from
heterogeneous canonical cells to the fixed field word used by the accumulator.
Its root and frame laws are universal over materialized cells and validated
family patches; callers cannot choose a post-state, footprint, or receipt core
for an individual accepted effect.
-/
import Theory.AcceptedCellEffect
import Assurance.SemanticHistoryFamily

namespace Minidregg.Assurance.AcceptedCellEffectHistory

open Minidregg.Assurance.SemanticReceiptRelation
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Assurance.SemanticTurnReceipt
open Minidregg.Compiler.SemanticManifest
open Minidregg.Theory
open Minidregg.Theory.CanonicalTransition
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ReactiveReceipt
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe u v w x y z uClauseInput uClauseQuery uClauseReply uClauseOutcome
  uClauseEvidence

noncomputable section

/-! ## One family-wide projection into the accumulator carrier -/

/--
The bounded history interpretation of one semantic effect family.

`projectFootprint` is a projection of the family's canonical patch, not a
per-execution receipt field.  `frame` must hold for every validated application
of that patch.  `root_exact` states that this fixed-width representation is an
exact representation of the canonical materializer root.  Neither law says
that a native implementation computes either representation.
-/
structure HistoryProjection
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    (family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier)
    (n : Nat) (F : Type*) [Field F] [DecidableEq F] where
  project : CellState.Materialized M -> Store (Fin n) F
  stateCommitment : StateCommitment (Fin n) F
  projectFootprint : CellState.Patch S Digest -> Finset (Fin n)
  root_exact : forall cell,
    stateCommitment.root (project cell) = cell.root
  frame : forall (declaration : family.Declaration)
    (outcome : family.Outcome declaration)
    (pre : CellState.Materialized M)
    (validated : CellState.ValidatedPatch M pre
      (family.patch declaration outcome))
    (index : Fin n),
    index ∉ projectFootprint (family.patch declaration outcome) ->
      project validated.apply index = project pre index

namespace HistoryProjection

variable
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (projection : HistoryProjection family n F)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {request : Request kind} {pre : CellState.Materialized M}
    {declaration : family.Declaration} {outcome : family.Outcome declaration}

/-- The exact accumulator delta induced by the accepted validated patch. -/
def delta
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    ReceiptDelta (projection.project pre)
      (projection.project accepted.prepared.post) where
  touched := projection.projectFootprint (family.patch declaration outcome)
  frame := projection.frame declaration outcome pre accepted.validated

/-- The canonical receipt core.  Its post and touched set are projections of
the same validated patch carried by `accepted`. -/
def core
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    ReceiptWitness (Fin n) F :=
  ReceiptWitness.ofDelta (projection.delta accepted)

theorem core_valid
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    (projection.core accepted).Satisfies :=
  ReceiptWitness.ofDelta_satisfies (projection.delta accepted)

@[simp] theorem core_pre
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    (projection.core accepted).pre = projection.project pre :=
  rfl

@[simp] theorem core_post
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    (projection.core accepted).post =
      projection.project accepted.prepared.post :=
  rfl

@[simp] theorem core_touched
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) (index : Fin n) :
    (projection.core accepted).touched index =
      if index ∈ projection.projectFootprint (family.patch declaration outcome)
      then 1 else 0 :=
  rfl

/-- The common request root is the root of the exact projected pre-word. -/
theorem request_preRoot_projected
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    request.preStateRoot =
      projection.stateCommitment.root (projection.project pre) :=
  accepted.preRootBound.trans (projection.root_exact pre).symm

/-- The projected post-word commits to the canonical prepared post root. -/
theorem prepared_postRoot_projected
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    projection.stateCommitment.root
        (projection.project accepted.prepared.post) =
      accepted.prepared.postRoot :=
  projection.root_exact accepted.prepared.post

/-! ## Direct common-history claim -/

def historyWitness
    (headerCells : HistoryAdmissionContext -> BindingIx -> F)
    (context : HistoryAdmissionContext)
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    BoundReceiptWitness n F where
  binding := headerCells context
  core := projection.core accepted

def historyClaim
    (headerCells : HistoryAdmissionContext -> BindingIx -> F)
    (context : HistoryAdmissionContext)
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    BoundSemanticReceiptClaim n F where
  witness := projection.historyWitness headerCells context accepted
  valid := projection.core_valid accepted

@[simp] theorem historyClaim_core
    (headerCells : HistoryAdmissionContext -> BindingIx -> F)
    (context : HistoryAdmissionContext)
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    (projection.historyClaim headerCells context accepted).witness.core =
      projection.core accepted :=
  rfl

/-! ## Request-shape-neutral semantic history evidence -/

/-- Lean-owned public-header projections for an accepted effect.  Every
projection consumes the exact first-order semantic data.  The effect root is
already canonical (`family.effectDigest declaration`) and therefore needs no
second projection field. -/
structure HeaderProjection where
  semanticObjectRoot : {kind : ResourceKind} ->
    Request kind -> CellState.Materialized M ->
    (declaration : family.Declaration) ->
    family.Outcome declaration -> Digest
  authorizationRoot : {kind : ResourceKind} -> Request kind -> Digest
  disclosureRoot : (declaration : family.Declaration) ->
    (outcome : family.Outcome declaration) ->
    DisclosureDecision (family.Release declaration outcome)
      (family.DeclassificationAuthority declaration outcome)
      (family.ReleaseAuthorization declaration outcome) -> Digest

/-- Exact proof-relevant evidence that one generic history context and claim
are the projections of one accepted cell effect.  `kind`, request,
declaration, outcome, mode evidence, validated patch, and disclosure are all
retained.  There is no privileged legacy turn wrapper. -/
structure Evidence
    (headerProjection : HeaderProjection (family := family))
    (headerCells : HistoryAdmissionContext -> BindingIx -> F)
    (context : HistoryAdmissionContext)
    (claim : BoundSemanticReceiptClaim n F) : Type _ where
  kind : ResourceKind
  request : Request kind
  pre : CellState.Materialized M
  declaration : family.Declaration
  outcome : family.Outcome declaration
  accepted : AcceptedCellEffect (portal := portal) (authState := authState)
    family request pre declaration outcome
  claimExact : claim = projection.historyClaim headerCells context accepted
  semanticObjectRootExact : context.semanticObjectRoot =
    headerProjection.semanticObjectRoot request pre declaration outcome
  semanticRelationExact : context.semanticRelationId = request.semantics
  outcomeExact : context.outcome = .committed
  preStateExact : context.preStateRoot = pre.root
  postStateExact : context.postStateRoot = accepted.prepared.postRoot
  effectRootExact : context.effectRoot = family.effectDigest declaration
  authorizationRootExact : context.authorizationRoot =
    headerProjection.authorizationRoot request
  disclosureRootExact : context.disclosureRoot =
    headerProjection.disclosureRoot declaration outcome accepted.disclosure

/-- Accepted effects form a generic semantic-history family.  Its rejected
case is impossible by construction; rejected executions must use a separate
proof-relevant rejection family rather than forge an accepted effect. -/
def entryFamily
    (headerProjection : HeaderProjection (family := family))
    (headerCells : HistoryAdmissionContext -> BindingIx -> F) :
    EntrySemanticsFamily n F where
  Evidence := Evidence (portal := portal) (authState := authState)
    projection headerProjection headerCells
  rejectedCoreAtomic := by
    intro context claim evidence denial rejected
    have impossible : AdmissionOutcome.committed = .rejected denial :=
      evidence.outcomeExact.symm.trans rejected
    cases impossible

namespace Evidence

variable
    {headerProjection : HeaderProjection (family := family)}
    {headerCells : HistoryAdmissionContext -> BindingIx -> F}
    {context : HistoryAdmissionContext}
    {claim : BoundSemanticReceiptClaim n F}

@[simp] theorem binding_exact
    (evidence : Evidence (portal := portal) (authState := authState)
      projection headerProjection headerCells context claim) :
    claim.witness.binding = headerCells context := by
  rw [evidence.claimExact]
  rfl

theorem preState_projected
    (evidence : Evidence (portal := portal) (authState := authState)
      projection headerProjection headerCells context claim) :
    context.preStateRoot = projection.stateCommitment.root
      (projection.project evidence.pre) :=
  evidence.preStateExact.trans (projection.root_exact evidence.pre).symm

theorem postState_projected
    (evidence : Evidence (portal := portal) (authState := authState)
      projection headerProjection headerCells context claim) :
    context.postStateRoot = projection.stateCommitment.root
      (projection.project evidence.accepted.prepared.post) :=
  evidence.postStateExact.trans
    (projection.prepared_postRoot_projected evidence.accepted).symm

theorem not_rejected
    (evidence : Evidence (portal := portal) (authState := authState)
      projection headerProjection headerCells context claim)
    (denial : Digest) : context.outcome ≠ AdmissionOutcome.rejected denial := by
  rw [evidence.outcomeExact]
  intro impossible
  cases impossible

variable
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {C : Submodule F (BoundReceiptIx n -> F)}

/-- Complete manifest/code admission into the request-shape-neutral semantic
history.  The exact accepted effect remains recoverable as `semantics.accepted`
from the resulting entry. -/
def toVerifiedEntry
    (evidence : Evidence (portal := portal) (authState := authState)
      projection headerProjection headerCells context claim)
    (contextWellFormed : context.WellFormed manifest)
    (dialectEvidence :
      ClauseEvidenceCoverage clauseEvidence context.dialectClauseRoots)
    (codeword : claim.witness.encode ∈ C) :
    Minidregg.Assurance.SemanticHistoryFamily.VerifiedEntry
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence)
      (family := projection.entryFamily (portal := portal)
        (authState := authState) headerProjection headerCells)
      (headerCells := headerCells) (C := C) where
  context := context
  claim := claim
  semantics := evidence
  contextWellFormed := contextWellFormed
  dialectEvidence := dialectEvidence
  bindingExact := evidence.binding_exact
  codeword := codeword

end Evidence

end HistoryProjection

/-- info: 'Minidregg.Assurance.AcceptedCellEffectHistory.HistoryProjection.core_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HistoryProjection.core_valid
/-- info: 'Minidregg.Assurance.AcceptedCellEffectHistory.HistoryProjection.request_preRoot_projected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HistoryProjection.request_preRoot_projected
/-- info: 'Minidregg.Assurance.AcceptedCellEffectHistory.HistoryProjection.entryFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HistoryProjection.entryFamily
/-- info: 'Minidregg.Assurance.AcceptedCellEffectHistory.HistoryProjection.Evidence.toVerifiedEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HistoryProjection.Evidence.toVerifiedEntry

end


end Minidregg.Assurance.AcceptedCellEffectHistory
