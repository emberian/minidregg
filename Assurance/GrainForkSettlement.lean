/-
# Assurance.GrainForkSettlement -- canonical fork/cut/stitch semantics

This module gives grains and forked views one Lean-owned settlement boundary.
It does not describe a network protocol, durable compare-and-swap, Rust codec,
or physical deployment.  A fork is indexed by one exact canonical history head;
every branch is a causally linked extension of that value.  A focus/cut retains
the exact typed field/resource selection, selected sparse-state roots, current
canonical branch, and one proposal branch for every incidence.

Settlement is not a second mutation kernel.  It is an accepted
`TypedCellHyperedge.Commit`: every incidence is an existing request-indexed
`AcceptedCellEffect`, the joint patch is validated once, resource writes are
disjoint, field overlap is either disjoint or resolved by the declared canonical
order, and the typed resource law balances.  The minted receipt retains that
actual hyperedge and derives its quadratic history core from the unique canonical
pre/post cells.  Deployment hashing and header-cell injection remain explicit
parameters over this exact semantic object.
-/
import Assurance.SemanticReceiptRuntimeCodec
import Kernel.SparseAuthenticatedState
import Kernel.TypedCellHyperedge
import Theory.CredentialAuthorityFamily

namespace Minidregg.Assurance.GrainForkSettlement

open Minidregg.Assurance.SemanticReceiptRelation
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Kernel.TypedCellHyperedge
open Minidregg.Theory
open Minidregg.Theory.CredentialAuthorityFamily
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe u v w x y z b p

noncomputable section

/-! ## Exact fork point and causally linked branch histories -/

/-- The complete public head from which a family of grain branches forks. -/
structure CanonicalHead where
  historyDomain : Digest
  sequence : Nat
  receiptRoot : Digest
  stateRoot : Digest
  deriving DecidableEq, Repr

/-- One history transition.  Its domain is inherited from the preceding head;
the remaining predecessor equations are checked by `LinkedFrom`. -/
structure HistoryStep where
  sequence : Nat
  previousReceiptRoot : Digest
  receiptRoot : Digest
  preStateRoot : Digest
  postStateRoot : Digest
  semanticObjectRoot : Digest
  deriving DecidableEq, Repr

def HistoryStep.toHead (domain : Digest) (step : HistoryStep) : CanonicalHead where
  historyDomain := domain
  sequence := step.sequence
  receiptRoot := step.receiptRoot
  stateRoot := step.postStateRoot

/-- Prefix-sensitive causal linkage from one exact head. -/
def LinkedFrom : CanonicalHead -> List HistoryStep -> Prop
  | _, [] => True
  | head, step :: rest =>
      step.sequence = head.sequence + 1 /\
      step.previousReceiptRoot = head.receiptRoot /\
      step.preStateRoot = head.stateRoot /\
      LinkedFrom (step.toHead head.historyDomain) rest

/-- A branch is definitionally indexed by its exact fork point.  Two branches
with merely equal-looking roots but different base values cannot be silently
interchanged without transporting that equality. -/
structure BranchHistory (base : CanonicalHead) where
  branchId : Digest
  steps : List HistoryStep
  linked : LinkedFrom base steps

namespace BranchHistory

def headFrom : CanonicalHead -> List HistoryStep -> CanonicalHead
  | head, [] => head
  | head, step :: rest => headFrom (step.toHead head.historyDomain) rest

def head {base : CanonicalHead} (branch : BranchHistory base) : CanonicalHead :=
  headFrom base branch.steps

def latestSemanticObjectRoot {base : CanonicalHead}
    (branch : BranchHistory base) : Option Digest :=
  branch.steps.getLast?.map HistoryStep.semanticObjectRoot

@[simp] theorem headFrom_nil (base : CanonicalHead) : headFrom base [] = base := rfl

@[simp] theorem head_nil {base : CanonicalHead} (branchId : Digest)
    (linked : LinkedFrom base []) :
    (BranchHistory.mk branchId [] linked).head = base :=
  rfl

theorem headFrom_historyDomain (base : CanonicalHead) (steps : List HistoryStep) :
    (headFrom base steps).historyDomain = base.historyDomain := by
  induction steps generalizing base with
  | nil => rfl
  | cons step rest induction =>
      exact (induction (step.toHead base.historyDomain)).trans rfl

theorem head_historyDomain {base : CanonicalHead} (branch : BranchHistory base) :
    branch.head.historyDomain = base.historyDomain :=
  headFrom_historyDomain base branch.steps

end BranchHistory

/-! ## Focus/cut and selected sparse roots -/

/-- A focus is a typed selection from the canonical cell plus a finite set of
sparse planes.  A selected sparse root is never supplied independently: it is
projected from the exact materialized sparse state for that plane. -/
structure StateFocus
    (S : CellState.Schema.{u, v, w, x})
    (L : Minidregg.Kernel.SparseAuthenticatedState.Layout.{u, v, w})
    (sparseMaterializer :
      Minidregg.Kernel.SparseAuthenticatedState.Materializer L Digest)
    (Plane : Type p) [DecidableEq Plane]
    (sparseState : Plane ->
      Minidregg.Kernel.SparseAuthenticatedState.Materialized sparseMaterializer) where
  fields : Finset S.Field
  resources : Finset S.Resource
  sparsePlanes : Finset Plane

namespace StateFocus

def sparseRootAt
    {S : CellState.Schema.{u, v, w, x}}
    {L : Minidregg.Kernel.SparseAuthenticatedState.Layout.{u, v, w}}
    {sparseMaterializer :
      Minidregg.Kernel.SparseAuthenticatedState.Materializer L Digest}
    {Plane : Type p} [DecidableEq Plane]
    {sparseState : Plane ->
      Minidregg.Kernel.SparseAuthenticatedState.Materialized sparseMaterializer}
    (_focus : StateFocus S L sparseMaterializer Plane sparseState)
    (plane : Plane) : Digest :=
  (sparseState plane).root

@[simp] theorem sparseRootAt_exact
    {S : CellState.Schema.{u, v, w, x}}
    {L : Minidregg.Kernel.SparseAuthenticatedState.Layout.{u, v, w}}
    {sparseMaterializer :
      Minidregg.Kernel.SparseAuthenticatedState.Materializer L Digest}
    {Plane : Type p} [DecidableEq Plane]
    {sparseState : Plane ->
      Minidregg.Kernel.SparseAuthenticatedState.Materialized sparseMaterializer}
    (focus : StateFocus S L sparseMaterializer Plane sparseState)
    (plane : Plane) :
    focus.sparseRootAt plane = (sparseState plane).root :=
  rfl

end StateFocus

/-! ## Current authority paths -/

/-- The authority used by a settlement leg is current for the exact request and,
for capability transport, retains the proof-relevant strict attenuation path.
Signature/proof grants have the unit lineage required by the common authority
family. -/
structure LiveAuthorityPath
    {portal : Portal} {state : AuthState} {kind : ResourceKind}
    {request : Request kind} (authorization : Authorized portal state request) where
  lineage : authorization.evidence.LineageRequirement
  current : authorization.evidence.Current

namespace LiveAuthorityPath

def ofLineage
    {portal : Portal} {state : AuthState} {kind : ResourceKind}
    {request : Request kind} (authorization : Authorized portal state request)
    (lineage : authorization.evidence.LineageRequirement) :
    LiveAuthorityPath authorization where
  lineage := lineage
  current := authorization.evidence.semanticEnvelope.current

end LiveAuthorityPath

/-! ## A cut indexed by one typed hyperedge declaration -/

section Cut

variable
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {portal : Portal} {projection : AuthorizationProjection S}
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence}
    {L : Minidregg.Kernel.SparseAuthenticatedState.Layout.{u, v, w}}
    {sparseMaterializer :
      Minidregg.Kernel.SparseAuthenticatedState.Materializer L Digest}
    {Plane : Type p} [DecidableEq Plane]
    {sparseState : Plane ->
      Minidregg.Kernel.SparseAuthenticatedState.Materialized sparseMaterializer}

/-- The exact focus/cut presented for settlement.

The canonical branch says which public history head is currently being updated.
Every incidence has a branch whose latest semantic-object root is exactly that
leg's effect digest.  The focused cell keys are exactly the joint patch
footprints; sparse roots are retained as additional read context and derived by
`StateFocus.sparseRootAt`. -/
structure FocusCut (base : CanonicalHead)
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence) where
  canonical : BranchHistory base
  branches : Incidence -> BranchHistory base
  focus : StateFocus S L sparseMaterializer Plane sparseState
  canonicalPreStateExact : canonical.head.stateRoot = declaration.pre.root
  branchProposalExact : forall incidence,
    (branches incidence).latestSemanticObjectRoot =
      some (declaration.legs incidence).request.effectsDigest
  fieldsExact : focus.fields = declaration.jointPatch.fieldFootprint
  resourcesExact : focus.resources = declaration.jointPatch.resourceFootprint

namespace FocusCut

theorem exactBaseDomain
    {base : CanonicalHead}
    (cut : FocusCut (L := L) (sparseMaterializer := sparseMaterializer)
      (Plane := Plane) (sparseState := sparseState) base declaration)
    (incidence : Incidence) :
    (cut.branches incidence).head.historyDomain = base.historyDomain :=
  (cut.branches incidence).head_historyDomain

theorem no_stale_canonical_pre
    {base : CanonicalHead}
    (cut : FocusCut (L := L) (sparseMaterializer := sparseMaterializer)
      (Plane := Plane) (sparseState := sparseState) base declaration)
    (stale : cut.canonical.head.stateRoot ≠ declaration.pre.root) : False :=
  stale cut.canonicalPreStateExact

end FocusCut

end Cut

/-! ## Exact merge-conflict semantics -/

section Conflicts

variable
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {portal : Portal} {projection : AuthorizationProjection S}
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : ResourceLaw.{u, v, w, x, y, z, b} S M portal Coordinate Balance}
    {declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence}

/-- An unresolved conflict is exactly a colliding resource replacement, or a
field collision while the plan declares disjoint field composition.  Field
overlap in canonical mode is resolved by the complete declared later-wins order
and is therefore not called an unresolved conflict. -/
inductive MergeConflict
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence)
    (left right : Incidence) : Prop
  | field
      (mode : declaration.composition.fieldMode = .disjoint)
      (key : S.Field)
      (leftWrites : key ∈ (declaration.legPatch left).fieldFootprint)
      (rightWrites : key ∈ (declaration.legPatch right).fieldFootprint)
  | resource
      (key : S.Resource)
      (leftWrites : key ∈ (declaration.legPatch left).resourceFootprint)
      (rightWrites : key ∈ (declaration.legPatch right).resourceFootprint)

/-- A typed commit contains the real conflict-freedom proof. -/
theorem Commit.noMergeConflict
    (commit : Commit law declaration)
    {left right : Incidence} (different : left ≠ right) :
    Not (MergeConflict declaration left right) := by
  intro conflict
  cases conflict with
  | field mode key leftWrites rightWrites =>
      have disjoint : declaration.FieldFootprintsDisjoint := by
        simpa [mode] using commit.shape.fieldsValid
      exact (Finset.disjoint_left.mp
        (disjoint left right different) leftWrites) rightWrites
  | resource key leftWrites rightWrites =>
      exact (Finset.disjoint_left.mp
        (commit.shape.resourcesDisjoint left right different) leftWrites) rightWrites

end Conflicts

/-! ## Atomic settlement and its canonical receipt -/

section Settlement

variable
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {portal : Portal} {projection : AuthorizationProjection S}
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : ResourceLaw.{u, v, w, x, y, z, b} S M portal Coordinate Balance}
    {declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence}
    {L : Minidregg.Kernel.SparseAuthenticatedState.Layout.{u, v, w}}
    {sparseMaterializer :
      Minidregg.Kernel.SparseAuthenticatedState.Materializer L Digest}
    {Plane : Type p} [DecidableEq Plane]
    {sparseState : Plane ->
      Minidregg.Kernel.SparseAuthenticatedState.Materialized sparseMaterializer}
    {base : CanonicalHead}
    {cut : FocusCut (L := L) (sparseMaterializer := sparseMaterializer)
      (Plane := Plane) (sparseState := sparseState) base declaration}

/-- Successful settlement is the existing schema-polymorphic typed hyperedge
commit plus a current proof-relevant authority path for every exact leg. -/
structure AcceptedSettlement
    (cut : FocusCut (L := L) (sparseMaterializer := sparseMaterializer)
      (Plane := Plane) (sparseState := sparseState) base declaration) where
  commit : Commit law declaration
  authorityPath : forall incidence,
    LiveAuthorityPath (declaration.legs incidence).authorization

namespace AcceptedSettlement

def post (settlement : AcceptedSettlement (law := law) cut) :
    CellState.Materialized M :=
  settlement.commit.prepared.post

def hyperedge (settlement : AcceptedSettlement (law := law) cut) :
    Minidregg.Kernel.TypedCellHyperedge.Commit.SemanticHyperedge
      settlement.commit :=
  settlement.commit.toHyperedge

@[simp] theorem postRoot (settlement : AcceptedSettlement (law := law) cut) :
    settlement.post.root = declaration.apex :=
  settlement.commit.prepared_postRoot

theorem noMergeConflict (settlement : AcceptedSettlement (law := law) cut)
    {left right : Incidence} (different : left ≠ right) :
    Not (MergeConflict declaration left right) :=
  GrainForkSettlement.Commit.noMergeConflict settlement.commit different

theorem includes_leg_field
    (settlement : AcceptedSettlement (law := law) cut)
    (incidence : Incidence) :
    (declaration.legPatch incidence).fieldFootprint ⊆ cut.focus.fields := by
  rw [cut.fieldsExact]
  exact settlement.commit.leg_fieldFootprint_subset incidence

theorem includes_leg_resource
    (settlement : AcceptedSettlement (law := law) cut)
    (incidence : Incidence) :
    (declaration.legPatch incidence).resourceFootprint ⊆ cut.focus.resources := by
  rw [cut.resourcesExact]
  exact settlement.commit.leg_resourceFootprint_subset incidence

end AcceptedSettlement

/-! ### Canonical history core from the unique typed post -/

/-- A finite, surjective field enumeration and typed encoding into the history
field.  Resource packages remain bound by the canonical full-cell pre/post roots;
this projection does not pretend heterogeneous resource evidence is a field. -/
structure FieldProjection (n : Nat) (F : Type*) [Field F] where
  keyAt : Fin n -> S.Field
  keyAt_surjective : Function.Surjective keyAt
  encode : (field : S.Field) -> S.FieldType field -> F

def FieldProjection.project
    {n : Nat} {F : Type*} [Field F]
    (fieldProjection : FieldProjection (S := S) n F)
    (cell : CellState.Materialized M) : Fin n -> F :=
  fun index => fieldProjection.encode (fieldProjection.keyAt index)
    (cell.logical.fields (fieldProjection.keyAt index))

def AcceptedSettlement.receiptDelta
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (settlement : AcceptedSettlement (law := law) cut)
    (fieldProjection : FieldProjection (S := S) n F) :
    Minidregg.Theory.ReactiveReceipt.ReceiptDelta
      (fieldProjection.project declaration.pre)
      (fieldProjection.project settlement.post) where
  touched := Finset.univ.filter fun index =>
    fieldProjection.keyAt index ∈ declaration.jointPatch.fieldFootprint
  frame := by
    intro index outside
    have fieldOutside :
        fieldProjection.keyAt index ∉ declaration.jointPatch.fieldFootprint := by
      simpa using outside
    have framed := settlement.commit.field_frame
      (fieldProjection.keyAt index) fieldOutside
    exact congrArg (fieldProjection.encode (fieldProjection.keyAt index)) framed

/-- Public values projected directly from the exact accepted settlement.  A
deployment codec may hash or pack this structure into the sixteen binding cells,
but cannot choose its pre/post roots independently. -/
structure SettlementHeader where
  historyDomain : Digest
  forkSequence : Nat
  forkReceiptRoot : Digest
  forkStateRoot : Digest
  currentSequence : Nat
  currentReceiptRoot : Digest
  preStateRoot : Digest
  postStateRoot : Digest
  branchCount : Nat
  deriving DecidableEq, Repr

def AcceptedSettlement.header
    (settlement : AcceptedSettlement (law := law) cut) : SettlementHeader where
  historyDomain := base.historyDomain
  forkSequence := base.sequence
  forkReceiptRoot := base.receiptRoot
  forkStateRoot := base.stateRoot
  currentSequence := cut.canonical.head.sequence
  currentReceiptRoot := cut.canonical.head.receiptRoot
  preStateRoot := declaration.pre.root
  postStateRoot := settlement.post.root
  branchCount := Fintype.card Incidence

def AcceptedSettlement.receiptClaim
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (settlement : AcceptedSettlement (law := law) cut)
    (fieldProjection : FieldProjection (S := S) n F)
    (headerCells : AcceptedSettlement (law := law) cut -> BindingIx -> F) :
    BoundSemanticReceiptClaim n F where
  witness :=
    { binding := headerCells settlement
      core := ReceiptWitness.ofDelta (settlement.receiptDelta fieldProjection) }
  valid := ReceiptWitness.ofDelta_satisfies (settlement.receiptDelta fieldProjection)

/-- The sole minted receipt retains the actual typed semantic hyperedge and the
exact accumulated claim derived above. -/
structure CanonicalReceipt
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (settlement : AcceptedSettlement (law := law) cut)
    (fieldProjection : FieldProjection (S := S) n F)
    (headerCells : AcceptedSettlement (law := law) cut -> BindingIx -> F) where
  private mk ::
  semanticHyperedge :
    Minidregg.Kernel.TypedCellHyperedge.Commit.SemanticHyperedge
      settlement.commit
  semanticHyperedgeExact : semanticHyperedge = settlement.hyperedge
  claim : BoundSemanticReceiptClaim n F
  claimExact : claim = settlement.receiptClaim fieldProjection headerCells

def AcceptedSettlement.mintReceipt
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (settlement : AcceptedSettlement (law := law) cut)
    (fieldProjection : FieldProjection (S := S) n F)
    (headerCells : AcceptedSettlement (law := law) cut -> BindingIx -> F) :
    CanonicalReceipt settlement fieldProjection headerCells where
  semanticHyperedge := settlement.hyperedge
  semanticHyperedgeExact := rfl
  claim := settlement.receiptClaim fieldProjection headerCells
  claimExact := rfl

@[simp] theorem CanonicalReceipt.claim_core_exact
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    {settlement : AcceptedSettlement (law := law) cut}
    {fieldProjection : FieldProjection (S := S) n F}
    {headerCells : AcceptedSettlement (law := law) cut -> BindingIx -> F}
    (receipt : CanonicalReceipt settlement fieldProjection headerCells) :
    receipt.claim.witness.core =
      ReceiptWitness.ofDelta (settlement.receiptDelta fieldProjection) := by
  rw [receipt.claimExact]
  rfl

theorem CanonicalReceipt.post_root_exact
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    {settlement : AcceptedSettlement (law := law) cut}
    {fieldProjection : FieldProjection (S := S) n F}
    {headerCells : AcceptedSettlement (law := law) cut -> BindingIx -> F}
    (_receipt : CanonicalReceipt settlement fieldProjection headerCells) :
    settlement.header.postStateRoot = declaration.apex := by
  exact settlement.postRoot

end Settlement

#print axioms BranchHistory.head_historyDomain
#print axioms Commit.noMergeConflict
#print axioms AcceptedSettlement.receiptClaim
#print axioms AcceptedSettlement.mintReceipt
#print axioms CanonicalReceipt.post_root_exact

end


end Minidregg.Assurance.GrainForkSettlement
