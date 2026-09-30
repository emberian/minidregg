/-
# Assurance.TypedCellHyperedgeReceipt -- the joint commit owns the history core

This module projects the flat typed hyperedge (`Kernel.TypedCellHyperedge`)
into the one existing semantic receipt relation.  It does not squeeze an
N-incidence turn through `SemanticTurnReceipt`'s single-request wrapper and
does not introduce a second executor or accumulator language.

The typed carrier's joint admission is proof-relevant: a `Commit` retains every
accepted leg, the re-validated joint patch, the apex, preserved outcomes, joint
postconditions and conservation.  An outcome is therefore either `committed`
with that `Commit`, or `rejected` with a proof that no `Commit` exists.  The
two are mutually exclusive, so the receipt core is a function of the
declaration alone (`core_unique`), whichever outcome evidence is supplied.

The pre-state, post-state and touched mask all come from the commit's one
validated joint patch; the frame is `Commit.frame`.  The projected word is the
existing `BoundSemanticReceiptClaim` consumed by Selvage history.

This replaces `Assurance.DeclaredHyperedgeReceipt`, which projected the deleted
legacy carrier's executable `execute`.
-/

import Kernel.TypedCellHyperedge
import Assurance.SemanticHistoryAccumulator

namespace Minidregg.Assurance.TypedCellHyperedgeReceipt

open Minidregg.Kernel.TypedCellHyperedge
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ReactiveReceipt (ReceiptDelta)
open Minidregg.Assurance.SemanticReceiptRelation
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.SemanticHistoryAccumulator

set_option autoImplicit false

universe u v w

variable {L : Store.Layout.{u, v, w}}
variable {M : CellState.Materializer L Digest}
variable {portal : Portal} {projection : AuthorizationProjection L}
variable {Incidence : Type} [Fintype Incidence]
variable {Coordinate : Type} {Balance : Type} [AddCommMonoid Balance]

/-! ## Bounded projection into the common field word -/

/-- A total finite projection of the canonical typed store.  A value is
projected with its presence, so absence and any stored value stay distinct
words.  Root coherence is required for every possible post-store, so the field
word and the cell's canonical materialization cannot be pointed at unrelated
states. -/
structure BoundedModel
    (declaration : Declaration.{u, v, w, 0, 0} L M portal projection Incidence)
    (n : Nat) (F : Type*) where
  keyAt : Fin n -> Store.Address L
  encodeValue : (address : Store.Address L) -> Option (L.Value address.1) -> F
  stateCommitment : Minidregg.Assurance.SemanticTurnReceipt.StateCommitment (Fin n) F
  preRootBound : declaration.pre.root =
    stateCommitment.root (fun index =>
      encodeValue (keyAt index) (declaration.pre.logical (keyAt index)))
  postRootBound : forall store : Store.Store L,
    (CellState.materialize M store).root =
      stateCommitment.root (fun index => encodeValue (keyAt index) (store (keyAt index)))

namespace BoundedModel

variable {declaration : Declaration.{u, v, w, 0, 0} L M portal projection Incidence}
variable {n : Nat} {F : Type*}

def project (model : BoundedModel declaration n F) (store : Store.Store L) :
    Minidregg.Theory.ReactiveReceipt.Store (Fin n) F :=
  fun index => model.encodeValue (model.keyAt index) (store (model.keyAt index))

def footprint (model : BoundedModel declaration n F) : Finset (Fin n) :=
  Finset.univ.filter fun index =>
    model.keyAt index ∈ Store.Patch.writeFootprint declaration.jointPatch

/-- The joint post store is the run of the one joint patch. -/
def postStore (_model : BoundedModel declaration n F) : Store.Store L :=
  Store.Patch.run declaration.pre.logical declaration.jointPatch

/-- The projected joint delta reuses the committed hyperedge's exact frame
law.  No second patch interpretation appears. -/
def commitDelta (model : BoundedModel declaration n F)
    {law : ResourceLaw.{u, v, w, 0, 0} L M portal Coordinate Balance}
    (commit : Commit law declaration) :
    ReceiptDelta (model.project declaration.pre.logical) (model.project model.postStore) where
  touched := model.footprint
  frame := by
    intro index outside
    have outsideTyped :
        model.keyAt index ∉ Store.Patch.writeFootprint declaration.jointPatch := by
      intro inside
      apply outside
      simp [footprint, inside]
    have framed := commit.frame (model.keyAt index) outsideTyped
    simp only [project, postStore]
    rw [show Store.Patch.run declaration.pre.logical declaration.jointPatch (model.keyAt index) =
      declaration.pre.logical (model.keyAt index) from framed]

def committedCore [Field F] (model : BoundedModel declaration n F)
    {law : ResourceLaw.{u, v, w, 0, 0} L M portal Coordinate Balance}
    (commit : Commit law declaration) : ReceiptWitness (Fin n) F :=
  ReceiptWitness.ofDelta (model.commitDelta commit)

def rejectedCore [Field F] (model : BoundedModel declaration n F) :
    ReceiptWitness (Fin n) F :=
  ReceiptWitness.ofDelta (rejectionDelta (model.project declaration.pre.logical))

end BoundedModel

/-! ## The proof-relevant joint semantic outcome -/

/-- Why a joint turn was refused.  The label names the failed commit condition;
the evidence is the `¬ Commit` proof carried beside it. -/
inductive RejectReason where
  | shape
  | jointValidation (reason : CellState.RejectReason)
  | apex
  | lostOutcome
  | postcondition
  | conservation
  deriving DecidableEq, Repr

/-- A commit retains the full semantic hyperedge certificate; a rejection
retains the proof that no certificate exists. -/
inductive SemanticOutcome
    (law : ResourceLaw.{u, v, w, 0, 0} L M portal Coordinate Balance)
    (declaration : Declaration.{u, v, w, 0, 0} L M portal projection Incidence) : Type where
  | rejected (reason : RejectReason) (refused : ¬ Commit law declaration)
  | committed (commit : Commit law declaration)

namespace SemanticOutcome

variable {law : ResourceLaw.{u, v, w, 0, 0} L M portal Coordinate Balance}
variable {declaration : Declaration.{u, v, w, 0, 0} L M portal projection Incidence}
variable {n : Nat} {F : Type*} [Field F]

def core (model : BoundedModel declaration n F) :
    SemanticOutcome law declaration -> ReceiptWitness (Fin n) F
  | .rejected _ _ => model.rejectedCore
  | .committed commit => model.committedCore commit

/-- **The core is a function of the declaration.**  Commit and refusal exclude
each other, and a commit is a proof, so any two outcome evidences give the same
receipt core. -/
theorem core_unique (model : BoundedModel declaration n F)
    (left right : SemanticOutcome law declaration) :
    left.core model = right.core model := by
  cases left with
  | rejected _ refused =>
      cases right with
      | rejected _ _ => rfl
      | committed commit => exact absurd commit refused
  | committed commit =>
      cases right with
      | rejected _ refused => exact absurd commit refused
      | committed _ => rfl

/-- Rejection is atomic: the rejected core's post is its pre. -/
@[simp] theorem core_rejected_atomic (model : BoundedModel declaration n F)
    (reason : RejectReason) (refused : ¬ Commit law declaration) :
    ((SemanticOutcome.rejected reason refused).core model).post =
      ((SemanticOutcome.rejected reason refused).core model).pre := by
  simp [core, BoundedModel.rejectedCore, rejectionDelta, ReceiptWitness.ofDelta]

/-- A commit's core carries exactly the joint post store. -/
@[simp] theorem core_committed_post (model : BoundedModel declaration n F)
    (commit : Commit law declaration) :
    ((SemanticOutcome.committed commit).core model).post =
      model.project (Store.Patch.run declaration.pre.logical declaration.jointPatch) :=
  rfl

/-- Every outcome's core satisfies the existing semantic receipt relation. -/
theorem core_valid [DecidableEq F] (model : BoundedModel declaration n F)
    (outcome : SemanticOutcome law declaration) :
    (outcome.core model).Satisfies := by
  cases outcome with
  | rejected _ _ =>
      exact ReceiptWitness.ofDelta_satisfies
        (rejectionDelta (model.project declaration.pre.logical))
  | committed commit =>
      exact ReceiptWitness.ofDelta_satisfies (model.commitDelta commit)

/-- On a committed outcome, every incidence retains authorization for its exact
request; the history projection has not erased the joint certificate. -/
def every_request_authorized (_commit : Commit law declaration) (incidence : Incidence) :
    Authorized portal (projection.project declaration.pre.logical)
      (declaration.legs incidence).request :=
  Commit.legAuthorization declaration incidence

end SemanticOutcome

/-! ## Exact projection to the existing history word -/

section History

variable {law : ResourceLaw.{u, v, w, 0, 0} L M portal Coordinate Balance}
variable {declaration : Declaration.{u, v, w, 0, 0} L M portal projection Incidence}
variable {n : Nat} {F : Type*} [Field F] [DecidableEq F]

def historyWitness (model : BoundedModel declaration n F)
    (outcome : SemanticOutcome law declaration)
    (headerCells : Minidregg.Compiler.SemanticManifest.AdmissionContext -> BindingIx -> F)
    (context : Minidregg.Compiler.SemanticManifest.AdmissionContext) :
    BoundReceiptWitness n F where
  binding := headerCells context
  core := outcome.core model

def historyClaim (model : BoundedModel declaration n F)
    (outcome : SemanticOutcome law declaration)
    (headerCells : Minidregg.Compiler.SemanticManifest.AdmissionContext -> BindingIx -> F)
    (context : Minidregg.Compiler.SemanticManifest.AdmissionContext) :
    BoundSemanticReceiptClaim n F where
  witness := historyWitness model outcome headerCells context
  valid := outcome.core_valid model

@[simp] theorem historyClaim_core_exact (model : BoundedModel declaration n F)
    (outcome : SemanticOutcome law declaration)
    (headerCells : Minidregg.Compiler.SemanticManifest.AdmissionContext -> BindingIx -> F)
    (context : Minidregg.Compiler.SemanticManifest.AdmissionContext) :
    (historyClaim model outcome headerCells context).witness.core = outcome.core model :=
  rfl

/-- Two outcome evidences for one declaration give the same history claim
core, so the accumulated meaning does not depend on the evidence chosen. -/
theorem historyClaim_core_unique (model : BoundedModel declaration n F)
    (left right : SemanticOutcome law declaration)
    (headerCells : Minidregg.Compiler.SemanticManifest.AdmissionContext -> BindingIx -> F)
    (context : Minidregg.Compiler.SemanticManifest.AdmissionContext) :
    (historyClaim model left headerCells context).witness.core =
      (historyClaim model right headerCells context).witness.core :=
  SemanticOutcome.core_unique model left right

end History

/-- info: 'Minidregg.Assurance.TypedCellHyperedgeReceipt.SemanticOutcome.core_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SemanticOutcome.core_unique
/-- info: 'Minidregg.Assurance.TypedCellHyperedgeReceipt.SemanticOutcome.core_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SemanticOutcome.core_valid
/-- info: 'Minidregg.Assurance.TypedCellHyperedgeReceipt.SemanticOutcome.core_rejected_atomic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SemanticOutcome.core_rejected_atomic
/-- info: 'Minidregg.Assurance.TypedCellHyperedgeReceipt.historyClaim_core_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms historyClaim_core_unique

end Minidregg.Assurance.TypedCellHyperedgeReceipt
