/-
# Assurance.DeclaredTurnReceipt -- declared execution owns receipt meaning

This is the bounded join from `Theory.DeclaredTurn` into the existing semantic
receipt/history spine.  A bounded model supplies only the projection of typed
state keys and the state-root realization.  The receipt pre-state, post-state,
touched mask, effect list, authorization, and commit/reject branch are all
derived from `Minidregg.Theory.DeclaredTurn.execute`; there is no caller-authored receipt core.

The executable object is `executeCore`.  Semantic authorization remains in
`Prop`: `derivedReceipt_nonempty` uses `execute_committed_sound`, and the
canonical history receipt is selected only after that proof.  Its accumulated
core is proved equal to `executeCore`, independently of proof selection.
-/
import Theory.DeclaredTurn
import Assurance.SemanticHistoryAccumulator

namespace Minidregg.Assurance.DeclaredTurnReceipt

open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ReactiveReceipt
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.CellState
open Minidregg.Theory.DeclaredTurn
open Minidregg.Assurance.SemanticReceiptRelation
open Minidregg.Assurance.SemanticTurnReceipt
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.SemanticHistoryAccumulator

/-! ## A bounded state/root projection -/

/-- The explicit boundary from the declaration's typed integer store to the
fixed field word consumed by semantic history.  Root coherence is stated for
every projected store; it is a codec/commitment obligation, not receipt data. -/
structure BoundedModel
    {portal : Portal}
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind)
    (n : Nat) (F : Type*) where
  keyAt : Fin n → Minidregg.Theory.EffectDeclaration.StateKey
  encodeValue : Int → F
  stateCommitment : StateCommitment (Fin n) F
  preRootBound :
    declaration.request.preStateRoot =
      stateCommitment.root (fun index =>
        encodeValue (declaration.preStore (keyAt index)))
  postRootBound : ∀ postStore : Minidregg.Theory.EffectDeclaration.Store,
    (Minidregg.Theory.CellState.materialize materializer
      (Minidregg.Theory.DeclaredTurn.logicalOfStore declaration.pre.logical
        declaration.effects.footprint postStore)).root =
        stateCommitment.root (fun index => encodeValue (postStore (keyAt index)))

def BoundedModel.project
    {portal : Portal}
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    {declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind}
    {n : Nat} {F : Type*}
    (model : BoundedModel declaration n F)
    (store : Minidregg.Theory.EffectDeclaration.Store) : Store (Fin n) F :=
  fun index => model.encodeValue (store (model.keyAt index))

def BoundedModel.footprint
    {portal : Portal}
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    {declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind}
    {n : Nat} {F : Type*}
    (model : BoundedModel declaration n F) : Finset (Fin n) :=
  Finset.univ.filter fun index =>
    model.keyAt index ∈ declaration.effects.footprint

/-! ## The exact computable core -/

/-- The committed core is data only: exact projected pre/post stores and the
mask induced by the declaration-derived footprint. -/
def BoundedModel.committedCore
    {portal : Portal}
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    {declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind}
    {n : Nat} {F : Type*} [Field F]
    (model : BoundedModel declaration n F)
    (postStore : Minidregg.Theory.EffectDeclaration.Store) : ReceiptWitness (Fin n) F where
  pre := model.project declaration.preStore
  post := model.project postStore
  touched := fun index => if index ∈ model.footprint then 1 else 0

/-- Rejection is the existing identity delta, hence exact pre equals post and
the touched set is empty. -/
def BoundedModel.rejectedCore
    {portal : Portal}
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    {declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind}
    {n : Nat} {F : Type*} [Field F]
    (model : BoundedModel declaration n F) : ReceiptWitness (Fin n) F :=
  ReceiptWitness.ofDelta
    (Minidregg.Assurance.SemanticHistoryAccumulator.rejectionDelta
      (model.project declaration.preStore))

/-- The sole executable receipt core: it is a projection of the actual
declared-turn decision, with no receipt or witness argument. -/
def executeCore
    {portal : Portal} (authState : AuthState)
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind)
    {n : Nat} {F : Type*} [Field F]
    (model : BoundedModel declaration n F) : ReceiptWitness (Fin n) F :=
  match Minidregg.Theory.DeclaredTurn.execute authState declaration with
  | .committed postStore => model.committedCore postStore
  | .rejected _ => model.rejectedCore

@[simp] theorem executeCore_committed_post
    {portal : Portal} (authState : AuthState)
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind)
    {n : Nat} {F : Type*} [Field F]
    (model : BoundedModel declaration n F)
    (postStore : Minidregg.Theory.EffectDeclaration.Store)
    (executed : Minidregg.Theory.DeclaredTurn.execute authState declaration =
      .committed postStore) :
    (executeCore authState declaration model).post = model.project postStore := by
  simp [executeCore, executed, BoundedModel.committedCore]

@[simp] theorem executeCore_rejected_atomic
    {portal : Portal} (authState : AuthState)
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind)
    {n : Nat} {F : Type*} [Field F]
    (model : BoundedModel declaration n F)
    (reason : Minidregg.Theory.DeclaredTurn.RejectReason)
    (executed : Minidregg.Theory.DeclaredTurn.execute authState declaration =
      .rejected reason) :
    (executeCore authState declaration model).post =
      (executeCore authState declaration model).pre := by
  simp [executeCore, executed, BoundedModel.rejectedCore,
    Minidregg.Assurance.SemanticHistoryAccumulator.rejectionDelta,
    ReceiptWitness.ofDelta]

/-- A semantic commit induces the existing frame-preserving receipt delta. -/
def BoundedModel.commitDelta
    {portal : Portal} {authState : AuthState}
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    {declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind}
    {postStore : Minidregg.Theory.EffectDeclaration.Store}
    {n : Nat} {F : Type*}
    (model : BoundedModel declaration n F)
    (commit : Minidregg.Theory.DeclaredTurn.Commit (state := authState)
      declaration postStore) :
    ReceiptDelta (model.project declaration.preStore)
      (model.project postStore) where
  touched := model.footprint
  frame := by
    intro index outside
    have outsideTyped :
        model.keyAt index ∉ declaration.effects.footprint := by
      intro inside
      apply outside
      simp [BoundedModel.footprint, inside]
    exact congrArg model.encodeValue
      (commit.effect.frame (model.keyAt index) outsideTyped)

@[simp] theorem BoundedModel.committedCore_eq_ofDelta
    {portal : Portal} {authState : AuthState}
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    {declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind}
    {postStore : Minidregg.Theory.EffectDeclaration.Store}
    {n : Nat} {F : Type*} [Field F]
    (model : BoundedModel declaration n F)
    (commit : Minidregg.Theory.DeclaredTurn.Commit (state := authState)
      declaration postStore) :
    model.committedCore postStore =
      ReceiptWitness.ofDelta (model.commitDelta commit) :=
  rfl

/-- The executable core always satisfies the EXISTING semantic receipt
relation.  Commit validity comes only from `execute_committed_sound`; rejection
uses the existing identity delta. -/
theorem executeCore_valid
    {portal : Portal} (authState : AuthState)
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F) :
    (executeCore authState declaration model).Satisfies := by
  cases executed : Minidregg.Theory.DeclaredTurn.execute authState declaration with
  | rejected reason =>
      simpa [executeCore, executed, BoundedModel.rejectedCore] using
        ReceiptWitness.ofDelta_satisfies
          (Minidregg.Assurance.SemanticHistoryAccumulator.rejectionDelta
            (model.project declaration.preStore))
  | committed postStore =>
      rcases Minidregg.Theory.DeclaredTurn.execute_committed_sound authState declaration
        postStore executed with ⟨commit⟩
      simp only [executeCore, executed]
      rw [model.committedCore_eq_ofDelta commit]
      exact ReceiptWitness.ofDelta_satisfies (model.commitDelta commit)

def executeClaim
    {portal : Portal} (authState : AuthState)
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F) :
    SemanticReceiptClaim (Fin n) F where
  witness := executeCore authState declaration model
  valid := executeCore_valid authState declaration model

/-! ## Exact projection through SemanticTurnReceipt -/

abbrev DeclaredEffect
    {portal : Portal}
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind) :=
  Minidregg.Theory.EffectDeclaration.Effect declaration.seed.target

/-- The semantic effect relation is not a new interpreter.  It states that the
receipt delta is exactly the delta induced by an existing declared-turn commit
for the exact request, effect list, pre-store, and post-store. -/
def declaredEffectSemantics
    {portal : Portal} {authState : AuthState}
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind)
    {n : Nat} {F : Type*}
    (model : BoundedModel declaration n F) :
    EffectSemantics (Fin n) F (DeclaredEffect declaration) where
  digest := fun effects =>
    (⟨effects⟩ : Minidregg.Theory.EffectDeclaration.Declaration declaration.seed.target).digest
  Realizes := fun {_requestKind} request effects {pre post} delta =>
    ∃ (postStore : Minidregg.Theory.EffectDeclaration.Store)
      (commit : Minidregg.Theory.DeclaredTurn.Commit (state := authState)
        declaration postStore),
      (⟨_, request⟩ : Minidregg.Theory.AuthorizationDeclaration.SomeRequest) =
          ⟨kind, declaration.request⟩ ∧
      effects = declaration.effects.effects ∧
      pre = model.project declaration.preStore ∧
      post = model.project postStore ∧
      HEq delta (model.commitDelta commit)

def noDisclosure : DisclosurePolicy Empty where
  Permitted := fun _ disclosure => nomatch disclosure

abbrev DerivedTurn
    {portal : Portal} (authState : AuthState)
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind)
    {n : Nat} {F : Type*}
    (model : BoundedModel declaration n F) :=
  Minidregg.Assurance.SemanticHistoryAccumulator.SemanticTurn n F portal authState kind
    (DeclaredEffect declaration) Empty Minidregg.Theory.DeclaredTurn.RejectReason
    model.stateCommitment
    (declaredEffectSemantics (authState := authState) declaration model)
    noDisclosure

def BoundedModel.committedTurn
    {portal : Portal} {authState : AuthState}
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    {declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind}
    {postStore : Minidregg.Theory.EffectDeclaration.Store}
    {n : Nat} {F : Type*}
    (model : BoundedModel declaration n F)
    (commit : Minidregg.Theory.DeclaredTurn.Commit (state := authState)
      declaration postStore) :
    CommittedTurn portal authState declaration.request model.stateCommitment
      (declaredEffectSemantics (authState := authState) declaration model)
      noDisclosure (model.project declaration.preStore) where
  authorization := commit.effect.authorization
  post := model.project postStore
  delta := model.commitDelta commit
  postStateRoot := commit.postRoot
  postRootBound := model.postRootBound postStore
  effects := declaration.effects.effects
  effectsDigestBound := rfl
  effectsRealize := ⟨postStore, commit, rfl, rfl, rfl, rfl, HEq.rfl⟩
  disclosures := []
  disclosuresPermitted := by simp

/-- A semantic receipt paired with the theorem fixing its accumulated core to
the executable declared-turn outcome. -/
structure DerivedReceipt
    {portal : Portal} (authState : AuthState)
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F) where
  receipt : DerivedTurn authState declaration model
  coreExact : Minidregg.Assurance.SemanticHistoryAccumulator.historyCore receipt =
    executeCore authState declaration model

/-- The semantic receipt is derived for both branches.  No caller supplies an
authorization, effect witness, delta, post-state, or touched mask. -/
theorem derivedReceipt_nonempty
    {portal : Portal} (authState : AuthState)
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F) :
    Nonempty (DerivedReceipt authState declaration model) := by
  cases executed : Minidregg.Theory.DeclaredTurn.execute authState declaration with
  | rejected reason =>
      let receipt : DerivedTurn authState declaration model :=
        TurnReceipt.rejected declaration.request
          (model.project declaration.preStore) model.preRootBound reason
      refine ⟨⟨receipt, ?_⟩⟩
      simp [receipt, Minidregg.Assurance.SemanticHistoryAccumulator.historyCore, executeCore,
        executed, BoundedModel.rejectedCore, TurnReceipt.rejected]
  | committed postStore =>
      rcases Minidregg.Theory.DeclaredTurn.execute_committed_sound authState declaration
        postStore executed with ⟨commit⟩
      let semanticCommit := model.committedTurn commit
      let receipt : DerivedTurn authState declaration model :=
        TurnReceipt.committed declaration.request
          (model.project declaration.preStore) model.preRootBound semanticCommit
      refine ⟨⟨receipt, ?_⟩⟩
      change ReceiptWitness.ofDelta (model.commitDelta commit) =
        executeCore authState declaration model
      simp only [executeCore, executed]
      exact (model.committedCore_eq_ofDelta commit).symm

/-- Proof selection is confined here.  `canonical_core_exact` below makes the
semantic meaning independent of which proof inhabitant is selected. -/
noncomputable def canonicalReceipt
    {portal : Portal} (authState : AuthState)
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F) :
    DerivedReceipt authState declaration model :=
  Classical.choice (derivedReceipt_nonempty authState declaration model)

theorem canonical_core_exact
    {portal : Portal} (authState : AuthState)
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F) :
    Minidregg.Assurance.SemanticHistoryAccumulator.historyCore
      (canonicalReceipt authState declaration model).receipt =
        executeCore authState declaration model :=
  (canonicalReceipt authState declaration model).coreExact

/-! ## The exact SemanticHistoryAccumulator seam -/

/-- Existing history binding cells are attached only after the semantic core
has been fixed by execution. -/
noncomputable def historyWitness
    {portal : Portal} (authState : AuthState)
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F)
    (headerCells : Minidregg.Compiler.SemanticManifest.AdmissionContext → BindingIx → F)
    (context : Minidregg.Compiler.SemanticManifest.AdmissionContext) :
    BoundReceiptWitness n F :=
  Minidregg.Assurance.SemanticHistoryAccumulator.historyWitness headerCells context
    (canonicalReceipt authState declaration model).receipt

theorem historyWitness_core_exact
    {portal : Portal} (authState : AuthState)
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F)
    (headerCells : Minidregg.Compiler.SemanticManifest.AdmissionContext → BindingIx → F)
    (context : Minidregg.Compiler.SemanticManifest.AdmissionContext) :
    (historyWitness authState declaration model headerCells context).core =
      executeCore authState declaration model :=
  canonical_core_exact authState declaration model

/-- This is already the exact proof-relevant claim type consumed by
`Minidregg.Assurance.SemanticHistoryAccumulator.VerifiedEntry`.  The remaining entry obligations
are manifest well-formedness, exact header projections, and code membership. -/
noncomputable def historyClaim
    {portal : Portal} (authState : AuthState)
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F)
    (headerCells : Minidregg.Compiler.SemanticManifest.AdmissionContext → BindingIx → F)
    (context : Minidregg.Compiler.SemanticManifest.AdmissionContext) :
    BoundSemanticReceiptClaim n F :=
  Minidregg.Assurance.SemanticHistoryAccumulator.historyClaim headerCells context
    (canonicalReceipt authState declaration model).receipt

@[simp] theorem historyClaim_core_exact
    {portal : Portal} (authState : AuthState)
    {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Minidregg.Theory.DeclaredTurn.Declaration portal materializer kind)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F)
    (headerCells : Minidregg.Compiler.SemanticManifest.AdmissionContext → BindingIx → F)
    (context : Minidregg.Compiler.SemanticManifest.AdmissionContext) :
    (historyClaim authState declaration model headerCells context).witness.core =
      executeCore authState declaration model :=
  canonical_core_exact authState declaration model

end Minidregg.Assurance.DeclaredTurnReceipt
