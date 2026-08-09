/-
# Theory.CanonicalTransition -- one canonical logical transition nucleus

This module is the common semantic target for ordinary and resumed turns.  A
`CellDelta` is indexed by the exact canonical pre/post materializations and
carries the two typed footprints with their frame laws.  A `PreparedTurn`
contains only that canonical post, its delta, and an optional eager nullifier;
both roots are derived projections.

`Decision` is total and intent-like: blocked and rejected decisions expose no
post-state, while a prepared decision exposes the logical transition.  Physical
compare-and-swap, nullifier insertion, receipt persistence, and I/O are outside
this module.
-/
import Theory.DeclaredTurn
import Theory.ReactiveCellTransition

namespace Minidregg.Theory.CanonicalTransition

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram

universe u v w x y z

/-- The legacy declared-turn schema is an opaque definition, so expose the
decidable equalities its canonical-transition adapter needs. -/
local instance effectSchemaFieldDecidableEq :
    DecidableEq DeclaredTurn.effectSchema.Field := by
  change DecidableEq EffectDeclaration.StateKey
  infer_instance

local instance effectSchemaResourceDecidableEq :
    DecidableEq DeclaredTurn.effectSchema.Resource := by
  change DecidableEq Empty
  infer_instance

/-! ## Canonical typed deltas -/

/-- A proof-relevant transition between two exact canonical cells.  Field and
resource footprints remain separate so dependent resource packages never pass
through an untyped value carrier. -/
structure CellDelta
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root}
    (pre post : CellState.Materialized M) : Type _ where
  fieldFootprint : Finset S.Field
  resourceFootprint : Finset S.Resource
  fieldFrame : ∀ field, field ∉ fieldFootprint →
    post.logical.fields field = pre.logical.fields field
  resourceFrame : ∀ resource, resource ∉ resourceFootprint →
    post.logical.resources resource = pre.logical.resources resource

/-- No field may change outside the exact delta footprint. -/
theorem CellDelta.field_changed_only_declared
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root}
    {pre post : CellState.Materialized M} (delta : CellDelta pre post)
    (field : S.Field)
    (changed : post.logical.fields field ≠ pre.logical.fields field) :
    field ∈ delta.fieldFootprint := by
  by_contra outside
  exact changed (delta.fieldFrame field outside)

/-- No resource/value/authority/evidence package may change outside the exact
delta footprint. -/
theorem CellDelta.resource_changed_only_declared
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root}
    {pre post : CellState.Materialized M} (delta : CellDelta pre post)
    (resource : S.Resource)
    (changed : post.logical.resources resource ≠ pre.logical.resources resource) :
    resource ∈ delta.resourceFootprint := by
  by_contra outside
  exact changed (delta.resourceFrame resource outside)

/-- Every validated typed patch induces the canonical delta it actually
applies.  There is no separately supplied post-cell or footprint. -/
def CellDelta.ofValidatedPatch
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root} {pre : CellState.Materialized M}
    {patch : CellState.Patch S Root}
    (validated : CellState.ValidatedPatch M pre patch) :
    CellDelta pre validated.apply where
  fieldFootprint := patch.fieldFootprint
  resourceFootprint := patch.resourceFootprint
  fieldFrame := validated.field_frame
  resourceFrame := validated.resource_frame

@[simp] theorem CellDelta.ofValidatedPatch_fieldFootprint
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root} {pre : CellState.Materialized M}
    {patch : CellState.Patch S Root}
    (validated : CellState.ValidatedPatch M pre patch) :
    (CellDelta.ofValidatedPatch validated).fieldFootprint = patch.fieldFootprint :=
  rfl

@[simp] theorem CellDelta.ofValidatedPatch_resourceFootprint
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root} {pre : CellState.Materialized M}
    {patch : CellState.Patch S Root}
    (validated : CellState.ValidatedPatch M pre patch) :
    (CellDelta.ofValidatedPatch validated).resourceFootprint =
      patch.resourceFootprint :=
  rfl

/-! ## Prepared logical turns and total decisions -/

/-- A commit-ready logical transition.  Roots are deliberately absent as
fields: they are projections of `pre` and `post`. -/
structure PreparedTurn
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    (M : CellState.Materializer S Root) (pre : CellState.Materialized M)
    (Nullifier : Type z) : Type _ where
  post : CellState.Materialized M
  delta : CellDelta pre post
  nullifier : Option Nullifier

/-- The canonical pre-root; no caller field can disagree with it. -/
def PreparedTurn.preRoot
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root} {pre : CellState.Materialized M}
    {Nullifier : Type z} (_turn : PreparedTurn M pre Nullifier) : Root :=
  pre.root

/-- The canonical post-root; no caller field can disagree with it. -/
def PreparedTurn.postRoot
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root} {pre : CellState.Materialized M}
    {Nullifier : Type z} (turn : PreparedTurn M pre Nullifier) : Root :=
  turn.post.root

@[simp] theorem PreparedTurn.preRoot_derived
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root} {pre : CellState.Materialized M}
    {Nullifier : Type z} (turn : PreparedTurn M pre Nullifier) :
    turn.preRoot = M.rootBytes (M.codec.encode pre.logical) :=
  rfl

@[simp] theorem PreparedTurn.postRoot_derived
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root} {pre : CellState.Materialized M}
    {Nullifier : Type z} (turn : PreparedTurn M pre Nullifier) :
    turn.postRoot = M.rootBytes (M.codec.encode turn.post.logical) :=
  rfl

/-- Prepare the exact logical effect of one validated patch. -/
def PreparedTurn.ofValidatedPatch
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root} {pre : CellState.Materialized M}
    {patch : CellState.Patch S Root} {Nullifier : Type z}
    (validated : CellState.ValidatedPatch M pre patch)
    (nullifier : Option Nullifier := none) : PreparedTurn M pre Nullifier where
  post := validated.apply
  delta := CellDelta.ofValidatedPatch validated
  nullifier := nullifier

/-- Total semantic decision.  Block/reject constructors have no post-state
field; only `prepared` carries a canonical transition. -/
inductive Decision
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    (M : CellState.Materializer S Root)
    (Blocked Reject Nullifier : Type z) (pre : CellState.Materialized M) : Type _
  | blocked (reason : Blocked)
  | rejected (reason : Reject)
  | prepared (turn : PreparedTurn M pre Nullifier)

/-- Logical state visible after a decision.  This is not a physical durable
commit operation. -/
def Decision.logicalPost
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root}
    {Blocked Reject Nullifier : Type z} {pre : CellState.Materialized M} :
    Decision M Blocked Reject Nullifier pre → CellState.Materialized M
  | .blocked _ => pre
  | .rejected _ => pre
  | .prepared turn => turn.post

@[simp] theorem Decision.blocked_atomic
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root}
    {Blocked Reject Nullifier : Type z} {pre : CellState.Materialized M}
    (reason : Blocked) :
    (Decision.blocked (M := M) (Reject := Reject) (Nullifier := Nullifier)
      (pre := pre) reason).logicalPost = pre :=
  rfl

@[simp] theorem Decision.rejected_atomic
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root}
    {Blocked Reject Nullifier : Type z} {pre : CellState.Materialized M}
    (reason : Reject) :
    (Decision.rejected (M := M) (Blocked := Blocked) (Nullifier := Nullifier)
      (pre := pre) reason).logicalPost = pre :=
  rfl

/-! ## One-way adapters from the current turn models -/

/-- An ordinary declared commit projects into the canonical nucleus.  Its
legacy schema has no resource lane, so the resource footprint is empty. -/
def CellDelta.ofDeclaredCommit
    {portal : TypedAuthorization.Portal} {authState : TypedAuthorization.AuthState}
    {M : CellState.Materializer DeclaredTurn.effectSchema
      TypedAuthorization.Digest}
    {kind : TypedAuthorization.ResourceKind}
    {declaration : DeclaredTurn.Declaration portal M kind}
    {postStore : EffectDeclaration.Store}
    (commit : DeclaredTurn.Commit (state := authState) declaration postStore) :
    CellDelta declaration.pre commit.post where
  fieldFootprint := declaration.effects.footprint.toFinset
  resourceFootprint := ∅
  fieldFrame := by
    intro field outside
    exact commit.frame field (by
      intro present
      exact outside (List.mem_toFinset.mpr present))
  resourceFrame := by
    intro resource
    exact nomatch resource

/-- Ordinary turns have no guarded-resume nullifier in the current model. -/
def PreparedTurn.ofDeclaredCommit
    {portal : TypedAuthorization.Portal} {authState : TypedAuthorization.AuthState}
    {M : CellState.Materializer DeclaredTurn.effectSchema
      TypedAuthorization.Digest}
    {kind : TypedAuthorization.ResourceKind}
    {declaration : DeclaredTurn.Declaration portal M kind}
    {postStore : EffectDeclaration.Store}
    (commit : DeclaredTurn.Commit (state := authState) declaration postStore) :
    PreparedTurn M declaration.pre Empty where
  post := commit.post
  delta := CellDelta.ofDeclaredCommit commit
  nullifier := none

@[simp] theorem PreparedTurn.ofDeclaredCommit_fieldFootprint
    {portal : TypedAuthorization.Portal} {authState : TypedAuthorization.AuthState}
    {M : CellState.Materializer DeclaredTurn.effectSchema
      TypedAuthorization.Digest}
    {kind : TypedAuthorization.ResourceKind}
    {declaration : DeclaredTurn.Declaration portal M kind}
    {postStore : EffectDeclaration.Store}
    (commit : DeclaredTurn.Commit (state := authState) declaration postStore) :
    (PreparedTurn.ofDeclaredCommit commit).delta.fieldFootprint =
      declaration.effects.footprint.toFinset :=
  rfl

@[simp] theorem PreparedTurn.ofDeclaredCommit_nullifier
    {portal : TypedAuthorization.Portal} {authState : TypedAuthorization.AuthState}
    {M : CellState.Materializer DeclaredTurn.effectSchema
      TypedAuthorization.Digest}
    {kind : TypedAuthorization.ResourceKind}
    {declaration : DeclaredTurn.Declaration portal M kind}
    {postStore : EffectDeclaration.Store}
    (commit : DeclaredTurn.Commit (state := authState) declaration postStore) :
    (PreparedTurn.ofDeclaredCommit commit).nullifier = (none : Option Empty) :=
  rfl

/-- The ordinary adapter preserves the request's canonical pre-root. -/
theorem PreparedTurn.ofDeclaredCommit_preRoot
    {portal : TypedAuthorization.Portal} {authState : TypedAuthorization.AuthState}
    {M : CellState.Materializer DeclaredTurn.effectSchema
      TypedAuthorization.Digest}
    {kind : TypedAuthorization.ResourceKind}
    {declaration : DeclaredTurn.Declaration portal M kind}
    {postStore : EffectDeclaration.Store}
    (commit : DeclaredTurn.Commit (state := authState) declaration postStore) :
    (PreparedTurn.ofDeclaredCommit commit).preRoot =
      declaration.request.preStateRoot :=
  rfl

/-- The ordinary adapter's post-root is the commit's canonical post-root. -/
theorem PreparedTurn.ofDeclaredCommit_postRoot
    {portal : TypedAuthorization.Portal} {authState : TypedAuthorization.AuthState}
    {M : CellState.Materializer DeclaredTurn.effectSchema
      TypedAuthorization.Digest}
    {kind : TypedAuthorization.ResourceKind}
    {declaration : DeclaredTurn.Declaration portal M kind}
    {postStore : EffectDeclaration.Store}
    (commit : DeclaredTurn.Commit (state := authState) declaration postStore) :
    (PreparedTurn.ofDeclaredCommit commit).postRoot = commit.postRoot :=
  rfl

/-- Reactive acceptance projects into the same canonical nucleus using only its
validated typed cell patch.  The parallel controller store is not retained. -/
def PreparedTurn.ofReactiveAccepted
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S T.Root}
    {layout : CellState.ControllerLayout S T}
    {declaration : ReactiveController.Declaration U T}
    {observation : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice declaration.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized M} {patch : CellState.Patch S T.Root}
    (accepted : ReactiveCellTransition.Accepted M layout declaration observation
      advice proof controllerPre pre patch) :
    PreparedTurn M pre (GuardedAdvice.NullifierKey T.vocabulary) where
  post := accepted.validated.apply
  delta := CellDelta.ofValidatedPatch accepted.validated
  nullifier := some declaration.hole.nullifierKey

@[simp] theorem PreparedTurn.ofReactiveAccepted_nullifier
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S T.Root}
    {layout : CellState.ControllerLayout S T}
    {declaration : ReactiveController.Declaration U T}
    {observation : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice declaration.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized M} {patch : CellState.Patch S T.Root}
    (accepted : ReactiveCellTransition.Accepted M layout declaration observation
      advice proof controllerPre pre patch) :
    (PreparedTurn.ofReactiveAccepted accepted).nullifier =
      some declaration.hole.nullifierKey :=
  rfl

/-- The reactive adapter's pre-root is exactly the eager request root. -/
theorem PreparedTurn.ofReactiveAccepted_preRoot
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S T.Root}
    {layout : CellState.ControllerLayout S T}
    {declaration : ReactiveController.Declaration U T}
    {observation : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice declaration.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized M} {patch : CellState.Patch S T.Root}
    (accepted : ReactiveCellTransition.Accepted M layout declaration observation
      advice proof controllerPre pre patch) :
    (PreparedTurn.ofReactiveAccepted accepted).preRoot =
      accepted.intent.request.preRoot :=
  accepted.exact_bindings.cellPreRoot.symm

/-- The reactive adapter's post-root is exactly the verified fill root. -/
theorem PreparedTurn.ofReactiveAccepted_postRoot
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S T.Root}
    {layout : CellState.ControllerLayout S T}
    {declaration : ReactiveController.Declaration U T}
    {observation : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice declaration.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized M} {patch : CellState.Patch S T.Root}
    (accepted : ReactiveCellTransition.Accepted M layout declaration observation
      advice proof controllerPre pre patch) :
    (PreparedTurn.ofReactiveAccepted accepted).postRoot =
      accepted.intent.verified.postRoot :=
  accepted.exact_bindings.cellPostRoot.symm

/-- The adapter preserves the eager unified footprint without storing a second
uniform post-state. -/
theorem PreparedTurn.ofReactiveAccepted_footprint
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S T.Root}
    {layout : CellState.ControllerLayout S T}
    {declaration : ReactiveController.Declaration U T}
    {observation : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice declaration.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized M} {patch : CellState.Patch S T.Root}
    (accepted : ReactiveCellTransition.Accepted M layout declaration observation
      advice proof controllerPre pre patch) :
    (PreparedTurn.ofReactiveAccepted accepted).delta.fieldFootprint.image layout.fieldKey ∪
        (PreparedTurn.ofReactiveAccepted accepted).delta.resourceFootprint.image
          layout.resourceKey =
      declaration.hole.footprint := by
  simpa [PreparedTurn.ofReactiveAccepted, CellDelta.ofValidatedPatch,
    CellState.Patch.controllerFootprint] using
      accepted.exact_bindings.patchFootprint

end Minidregg.Theory.CanonicalTransition
