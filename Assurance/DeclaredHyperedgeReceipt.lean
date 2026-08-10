/-
# Assurance.DeclaredHyperedgeReceipt -- joint execution owns the history core

This module projects the executable flat `DeclaredHyperedge` into the one
existing semantic receipt relation.  It does not squeeze an N-incidence turn
through `SemanticTurnReceipt`'s single-request wrapper and does not introduce
a second executor or accumulator language.

The exact pre-state, post-state, touched mask, rejection identity, and
committed semantic certificate all come from `DeclaredHyperedge.execute`.
For a commit, the proof-relevant `CommittedHyperedge` is retained, including
every exact request-indexed authorization, aggregate balance, guards, shared
apex, and canonical patch result.  The projected word is the existing
`BoundSemanticReceiptClaim` consumed by Loom history.

The next history-admission layer must bind the complete incidence/request list
and its presentation/effect roots in a joint header.  This file intentionally
does not choose one leg as a synthetic primary request.
-/

import Kernel.DeclaredHyperedge
import Assurance.SemanticHistoryAccumulator

namespace Minidregg.Assurance.DeclaredHyperedgeReceipt

open Minidregg.Kernel.DeclaredHyperedge
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.CellState
open Minidregg.Theory.ReactiveReceipt
open Minidregg.Assurance.SemanticReceiptRelation
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.SemanticHistoryAccumulator

set_option autoImplicit false

variable {portal : Portal}
variable {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
variable {Incidence : Type} [Fintype Incidence] [DecidableEq Incidence]

/-! ## Bounded projection into the common field word -/

/-- A total finite projection of the canonical typed store.  Root coherence
is required for every possible post-store, so the field word and the cell's
canonical materialization cannot be pointed at unrelated states. -/
structure BoundedModel
    (declaration : Declaration portal materializer Incidence)
    (n : Nat) (F : Type*) where
  keyAt : Fin n -> StateKey
  encodeValue : Int -> F
  stateCommitment : Minidregg.Assurance.SemanticTurnReceipt.StateCommitment (Fin n) F
  preRootBound : declaration.pre.root =
    stateCommitment.root (fun index =>
      encodeValue (declaration.preStore (keyAt index)))
  postRootBound : forall postStore : Store,
    (materialize materializer
      (Minidregg.Theory.DeclaredTurn.logicalOfStore postStore)).root =
        stateCommitment.root (fun index => encodeValue (postStore (keyAt index)))

def BoundedModel.project
    {declaration : Declaration portal materializer Incidence}
    {n : Nat} {F : Type*}
    (model : BoundedModel declaration n F) (store : Store) :
    Minidregg.Theory.ReactiveReceipt.Store (Fin n) F :=
  fun index => model.encodeValue (store (model.keyAt index))

def BoundedModel.footprint
    {declaration : Declaration portal materializer Incidence}
    {n : Nat} {F : Type*}
    (model : BoundedModel declaration n F) : Finset (Fin n) :=
  Finset.univ.filter fun index =>
    model.keyAt index ∈ declaration.footprint

/-! ## Exact commit/reject cores -/

/-- The projected joint delta reuses the committed hyperedge's exact frame
law.  No second patch interpretation appears. -/
def BoundedModel.commitDelta
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {postStore : Store}
    {n : Nat} {F : Type*}
    (model : BoundedModel declaration n F)
    (commit : CommittedHyperedge projection declaration postStore) :
    ReceiptDelta (model.project declaration.preStore)
      (model.project postStore) where
  touched := model.footprint
  frame := by
    intro index outside
    have outsideTyped : model.keyAt index ∉ declaration.footprint := by
      intro inside
      apply outside
      simp [BoundedModel.footprint, inside]
    exact congrArg model.encodeValue
      (commit.receipt.frame (model.keyAt index) (by
        simpa [CommittedHyperedge.receipt] using outsideTyped))

def BoundedModel.committedCore
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {postStore : Store}
    {n : Nat} {F : Type*} [Field F]
    (model : BoundedModel declaration n F)
    (commit : CommittedHyperedge projection declaration postStore) :
    ReceiptWitness (Fin n) F :=
  ReceiptWitness.ofDelta (model.commitDelta commit)

def BoundedModel.rejectedCore
    {declaration : Declaration portal materializer Incidence}
    {n : Nat} {F : Type*} [Field F]
    (model : BoundedModel declaration n F) : ReceiptWitness (Fin n) F :=
  ReceiptWitness.ofDelta (rejectionDelta (model.project declaration.preStore))

/-- The sole executable joint receipt core. -/
def executeCore
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    {n : Nat} {F : Type*} [Field F]
    (model : BoundedModel declaration n F) : ReceiptWitness (Fin n) F :=
  match execute projection declaration with
  | .committed postStore =>
      { pre := model.project declaration.preStore
        post := model.project postStore
        touched := fun index => if index ∈ model.footprint then 1 else 0 }
  | .rejected _ => model.rejectedCore

@[simp] theorem executeCore_rejected_atomic
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    {n : Nat} {F : Type*} [Field F]
    (model : BoundedModel declaration n F)
    (reason : Minidregg.Kernel.DeclaredHyperedge.RejectReason)
    (executed : execute projection declaration = .rejected reason) :
    (executeCore projection declaration model).post =
      (executeCore projection declaration model).pre := by
  simp [executeCore, executed, BoundedModel.rejectedCore, rejectionDelta,
    ReceiptWitness.ofDelta]

@[simp] theorem executeCore_committed_post
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    {n : Nat} {F : Type*} [Field F]
    (model : BoundedModel declaration n F)
    (postStore : Store)
    (executed : execute projection declaration = .committed postStore) :
    (executeCore projection declaration model).post = model.project postStore := by
  simp [executeCore, executed]

/-! ## The proof-relevant joint semantic outcome -/

/-- Every outcome retains its equality to the actual executable decision.  A
commit additionally retains the full semantic hyperedge certificate. -/
inductive SemanticOutcome
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence) : Type where
  | rejected (reason : Minidregg.Kernel.DeclaredHyperedge.RejectReason)
      (executed : execute projection declaration = .rejected reason)
  | committed (postStore : Store)
      (executed : execute projection declaration = .committed postStore)
      (semantic : CommittedHyperedge projection declaration postStore)

def SemanticOutcome.core
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F) :
    SemanticOutcome projection declaration -> ReceiptWitness (Fin n) F
  | .rejected _ _ => model.rejectedCore
  | .committed _ _ semantic => model.committedCore semantic

theorem SemanticOutcome.core_exact
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F)
    (outcome : SemanticOutcome projection declaration) :
    outcome.core model = executeCore projection declaration model := by
  cases outcome with
  | rejected reason executed => simp [SemanticOutcome.core, executeCore, executed]
  | committed postStore executed semantic =>
      apply ReceiptWitness.ext
      · simp [SemanticOutcome.core, BoundedModel.committedCore,
          BoundedModel.commitDelta, executeCore, executed, ReceiptWitness.ofDelta]
      · simp [SemanticOutcome.core, BoundedModel.committedCore,
          BoundedModel.commitDelta, executeCore, executed, ReceiptWitness.ofDelta]
      · funext index
        simp [SemanticOutcome.core, BoundedModel.committedCore,
          BoundedModel.commitDelta, executeCore, executed, ReceiptWitness.ofDelta]

/-- The executable decision always yields its exact semantic outcome. -/
theorem semanticOutcome_nonempty
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence) :
    Nonempty (SemanticOutcome projection declaration) := by
  cases executed : execute projection declaration with
  | rejected reason => exact ⟨.rejected reason executed⟩
  | committed postStore =>
      rcases execute_committed_hyperedge_sound projection declaration postStore
        executed with ⟨semantic⟩
      exact ⟨.committed postStore executed semantic⟩

/-- Proof selection is confined here; `canonicalCore_exact` makes the
accumulated meaning independent of the selected proof inhabitant. -/
noncomputable def canonicalOutcome
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence) :
    SemanticOutcome projection declaration :=
  Classical.choice (semanticOutcome_nonempty projection declaration)

theorem canonicalCore_exact
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F) :
    (canonicalOutcome projection declaration).core model =
      executeCore projection declaration model :=
  (canonicalOutcome projection declaration).core_exact model

/-- The core produced by joint execution always satisfies the existing
semantic receipt relation. -/
theorem executeCore_valid
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F) :
    (executeCore projection declaration model).Satisfies := by
  rw [← canonicalCore_exact projection declaration model]
  cases canonicalOutcome projection declaration with
  | rejected reason executed =>
      exact ReceiptWitness.ofDelta_satisfies
        (rejectionDelta (model.project declaration.preStore))
  | committed postStore executed semantic =>
      exact ReceiptWitness.ofDelta_satisfies (model.commitDelta semantic)

/-! ## Exact projection to the existing history word -/

def historyWitness
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F)
    (headerCells : Minidregg.Compiler.SemanticManifest.AdmissionContext -> BindingIx -> F)
    (context : Minidregg.Compiler.SemanticManifest.AdmissionContext) :
    BoundReceiptWitness n F where
  binding := headerCells context
  core := executeCore projection declaration model

def historyClaim
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F)
    (headerCells : Minidregg.Compiler.SemanticManifest.AdmissionContext -> BindingIx -> F)
    (context : Minidregg.Compiler.SemanticManifest.AdmissionContext) :
    BoundSemanticReceiptClaim n F where
  witness := historyWitness projection declaration model headerCells context
  valid := executeCore_valid projection declaration model

@[simp] theorem historyClaim_core_exact
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F)
    (headerCells : Minidregg.Compiler.SemanticManifest.AdmissionContext -> BindingIx -> F)
    (context : Minidregg.Compiler.SemanticManifest.AdmissionContext) :
    (historyClaim projection declaration model headerCells context).witness.core =
      executeCore projection declaration model :=
  rfl

/-- On a committed semantic outcome, every incidence retains authorization
for its exact request; the history projection has not erased the joint
certificate used to justify the core. -/
theorem SemanticOutcome.every_request_authorized
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {postStore : Store}
    (_executed : execute projection declaration = .committed postStore)
    (semantic : CommittedHyperedge projection declaration postStore)
    (incidence : Incidence) :
    Nonempty (Authorized portal (declaration.authState projection)
      (declaration.legs incidence).request) :=
  semantic.authorizations incidence

/-- info: 'Minidregg.Assurance.DeclaredHyperedgeReceipt.executeCore_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executeCore_valid
/-- info: 'Minidregg.Assurance.DeclaredHyperedgeReceipt.canonicalCore_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonicalCore_exact
/-- info: 'Minidregg.Assurance.DeclaredHyperedgeReceipt.historyClaim_core_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms historyClaim_core_exact
/-- info: 'Minidregg.Assurance.DeclaredHyperedgeReceipt.SemanticOutcome.every_request_authorized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SemanticOutcome.every_request_authorized

end Minidregg.Assurance.DeclaredHyperedgeReceipt
