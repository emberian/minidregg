/-
# Theory.TurnTransition -- one typed surface for ordinary and resumed turns

An ordinary declared turn and a resumed reactive cell turn retain different
typed requests, stores, and roots.  This module joins them with an explicit sum
rather than erasing either branch.  `control` delegates to the two existing
Lean controllers, while `TransitionFacts` is their common semantic view:
canonical roots, one exact footprint, a framed receipt delta, and no history or
physical commit machinery.
-/
import Theory.DeclaredTurn
import Theory.ReactiveCellTransition

namespace Minidregg.Theory.TurnTransition

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram

universe u v w x z

/-! ## Typed input and outcome sums -/

/-- The two controller modes. -/
inductive Mode
  | ordinary
  | resumed
deriving DecidableEq, Repr

/-- One typed controller input.  Each constructor retains the exact indices of
the controller it delegates to; there is no untyped request envelope. -/
inductive Input
    (portal : TypedAuthorization.Portal) (authState : TypedAuthorization.AuthState)
    (ordinaryMaterializer :
      CellState.Materializer DeclaredTurn.effectSchema TypedAuthorization.Digest)
    (kind : TypedAuthorization.ResourceKind)
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    (reactiveMaterializer : CellState.Materializer S T.Root)
    (layout : CellState.ControllerLayout S T) where
  | ordinary (declaration :
      DeclaredTurn.Declaration portal ordinaryMaterializer kind)
  | resumed (declaration : ReactiveController.Declaration U T)
      (observation : ReactiveController.HostObservation T)
      (advice : ReactiveController.Advice declaration.hole)
      (proof : ReactiveController.ProofData T)
      (controllerPre : ReactiveReceipt.Store T.Key T.Value)
      (pre : CellState.Materialized reactiveMaterializer)
      (patch : CellState.Patch S T.Root)

/-- The typed result sum mirrors the selected input branch.  Ordinary
commitment carries the exact executable equality needed to recover its semantic
`DeclaredTurn.Commit`; reactive acceptance already carries a private semantic
package. -/
inductive Outcome
    {portal : TypedAuthorization.Portal} (authState : TypedAuthorization.AuthState)
    {ordinaryMaterializer :
      CellState.Materializer DeclaredTurn.effectSchema TypedAuthorization.Digest}
    {kind : TypedAuthorization.ResourceKind}
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {reactiveMaterializer : CellState.Materializer S T.Root}
    {layout : CellState.ControllerLayout S T} :
    Input (U := U) (T := T) (S := S) portal authState ordinaryMaterializer kind
      reactiveMaterializer layout → Type _
  | ordinaryCommitted {declaration}
      (postStore : EffectDeclaration.Store)
      (executed : DeclaredTurn.execute authState declaration = .committed postStore) :
      Outcome authState (.ordinary declaration)
  | ordinaryRejected {declaration} (reason : DeclaredTurn.RejectReason) :
      Outcome authState (.ordinary declaration)
  | resumedBlocked {declaration observation advice proof controllerPre pre patch} :
      Outcome authState
        (.resumed declaration observation advice proof controllerPre pre patch)
  | resumedRejected {declaration observation advice proof controllerPre pre patch}
      (reason : ReactiveCellTransition.RejectReason) :
      Outcome authState
        (.resumed declaration observation advice proof controllerPre pre patch)
  | resumedAccepted {declaration observation advice proof controllerPre pre patch}
      (accepted : ReactiveCellTransition.Accepted reactiveMaterializer layout
        declaration observation advice proof controllerPre pre patch) :
      Outcome authState
        (.resumed declaration observation advice proof controllerPre pre patch)

/-- The one executable controller surface; each case is exactly the existing
Lean controller for that constructor. -/
def control
    {portal : TypedAuthorization.Portal} (authState : TypedAuthorization.AuthState)
    {ordinaryMaterializer :
      CellState.Materializer DeclaredTurn.effectSchema TypedAuthorization.Digest}
    {kind : TypedAuthorization.ResourceKind}
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {reactiveMaterializer : CellState.Materializer S T.Root}
    {layout : CellState.ControllerLayout S T} :
    (input : Input (U := U) (T := T) (S := S) portal authState
      ordinaryMaterializer kind reactiveMaterializer layout) →
      Outcome (U := U) (T := T) (S := S) authState input
  | .ordinary declaration =>
      match executed : DeclaredTurn.execute authState declaration with
      | .committed postStore => .ordinaryCommitted postStore executed
      | .rejected reason => .ordinaryRejected reason
  | .resumed declaration observation advice proof controllerPre pre patch =>
      match ReactiveCellTransition.transition reactiveMaterializer layout
          declaration observation advice proof controllerPre pre patch with
      | .blocked => .resumedBlocked
      | .rejected reason => .resumedRejected reason
      | .accepted accepted => .resumedAccepted accepted

/-! ## Canonical materialization and refusal atomicity -/

/-- A typed sum of the two canonical cell carriers. -/
inductive Cell
    (ordinaryMaterializer :
      CellState.Materializer DeclaredTurn.effectSchema TypedAuthorization.Digest)
    {S : CellState.Schema.{u, v, w, x}} {T : ReactiveController.Types.{z}}
    (reactiveMaterializer : CellState.Materializer S T.Root) where
  | ordinary (cell : CellState.Materialized ordinaryMaterializer)
  | resumed (cell : CellState.Materialized reactiveMaterializer)

/-- Canonical pre-cell selected by the typed input. -/
def Input.preCell
    {portal : TypedAuthorization.Portal} {authState : TypedAuthorization.AuthState}
    {ordinaryMaterializer :
      CellState.Materializer DeclaredTurn.effectSchema TypedAuthorization.Digest}
    {kind : TypedAuthorization.ResourceKind}
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {reactiveMaterializer : CellState.Materializer S T.Root}
    {layout : CellState.ControllerLayout S T} :
    Input (U := U) (T := T) (S := S) portal authState ordinaryMaterializer kind
      reactiveMaterializer layout → Cell ordinaryMaterializer reactiveMaterializer
  | .ordinary declaration => .ordinary declaration.pre
  | .resumed _ _ _ _ _ pre _ => .resumed pre

/-- Pure canonical state after the semantic transition.  Rejection and blocking
are identity; accepted branches expose only their already-derived logical post. -/
def Outcome.materialized
    {portal : TypedAuthorization.Portal} {authState : TypedAuthorization.AuthState}
    {ordinaryMaterializer :
      CellState.Materializer DeclaredTurn.effectSchema TypedAuthorization.Digest}
    {kind : TypedAuthorization.ResourceKind}
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {reactiveMaterializer : CellState.Materializer S T.Root}
    {layout : CellState.ControllerLayout S T}
    {input : Input (U := U) (T := T) (S := S) portal authState
      ordinaryMaterializer kind reactiveMaterializer layout} :
    Outcome (U := U) (T := T) (S := S) authState input →
      Cell ordinaryMaterializer reactiveMaterializer
  | .ordinaryCommitted (declaration := declaration) postStore _ =>
      .ordinary (CellState.materialize ordinaryMaterializer
        (DeclaredTurn.logicalOfStore declaration.pre.logical
          declaration.effects.footprint postStore))
  | .ordinaryRejected _ => input.preCell
  | .resumedBlocked => input.preCell
  | .resumedRejected _ => input.preCell
  | .resumedAccepted accepted => .resumed accepted.validated.apply

@[simp] theorem Outcome.ordinary_rejected_atomic
    {portal : TypedAuthorization.Portal} {authState : TypedAuthorization.AuthState}
    {ordinaryMaterializer :
      CellState.Materializer DeclaredTurn.effectSchema TypedAuthorization.Digest}
    {kind : TypedAuthorization.ResourceKind}
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {reactiveMaterializer : CellState.Materializer S T.Root}
    {layout : CellState.ControllerLayout S T}
    {declaration : DeclaredTurn.Declaration portal ordinaryMaterializer kind}
    (reason : DeclaredTurn.RejectReason) :
    (Outcome.ordinaryRejected (authState := authState) (U := U) (T := T)
      (S := S) (reactiveMaterializer := reactiveMaterializer) (layout := layout)
      (declaration := declaration) reason).materialized =
        (Input.ordinary (authState := authState) (U := U) (T := T) (S := S)
          (reactiveMaterializer := reactiveMaterializer) (layout := layout)
          declaration).preCell :=
  rfl

@[simp] theorem Outcome.resumed_blocked_atomic
    {portal : TypedAuthorization.Portal} {authState : TypedAuthorization.AuthState}
    {ordinaryMaterializer :
      CellState.Materializer DeclaredTurn.effectSchema TypedAuthorization.Digest}
    {kind : TypedAuthorization.ResourceKind}
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {reactiveMaterializer : CellState.Materializer S T.Root}
    {layout : CellState.ControllerLayout S T}
    {declaration : ReactiveController.Declaration U T}
    {observation : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice declaration.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized reactiveMaterializer}
    {patch : CellState.Patch S T.Root} :
    (Outcome.resumedBlocked (portal := portal) (authState := authState)
      (ordinaryMaterializer := ordinaryMaterializer) (kind := kind)
      (layout := layout) (declaration := declaration) (observation := observation)
      (advice := advice) (proof := proof) (controllerPre := controllerPre)
      (pre := pre) (patch := patch)).materialized =
        (Input.resumed (portal := portal) (authState := authState)
          (ordinaryMaterializer := ordinaryMaterializer) (kind := kind)
          (layout := layout) declaration observation advice proof controllerPre pre patch).preCell :=
  rfl

@[simp] theorem Outcome.resumed_rejected_atomic
    {portal : TypedAuthorization.Portal} {authState : TypedAuthorization.AuthState}
    {ordinaryMaterializer :
      CellState.Materializer DeclaredTurn.effectSchema TypedAuthorization.Digest}
    {kind : TypedAuthorization.ResourceKind}
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {reactiveMaterializer : CellState.Materializer S T.Root}
    {layout : CellState.ControllerLayout S T}
    {declaration : ReactiveController.Declaration U T}
    {observation : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice declaration.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized reactiveMaterializer}
    {patch : CellState.Patch S T.Root}
    (reason : ReactiveCellTransition.RejectReason) :
    (Outcome.resumedRejected (portal := portal) (authState := authState)
      (ordinaryMaterializer := ordinaryMaterializer) (kind := kind)
      (layout := layout) (declaration := declaration) (observation := observation)
      (advice := advice) (proof := proof) (controllerPre := controllerPre)
      (pre := pre) (patch := patch) reason).materialized =
        (Input.resumed (portal := portal) (authState := authState)
          (ordinaryMaterializer := ordinaryMaterializer) (kind := kind)
          (layout := layout) declaration observation advice proof controllerPre pre patch).preCell :=
  rfl

/-! ## One common footprint/frame/root/receipt view -/

/-- Branch-independent accepted-transition facts.  `delta` is the existing
receipt-delta type; its frame law and `footprint_exact` make the common semantic
surface precise. -/
structure TransitionFacts (Key Value Root : Type*) [DecidableEq Key] where
  preRoot : Root
  postRoot : Root
  pre : ReactiveReceipt.Store Key Value
  post : ReactiveReceipt.Store Key Value
  footprint : Finset Key
  delta : ReactiveReceipt.ReceiptDelta pre post
  footprint_exact : delta.touched = footprint

/-- Common frame theorem for either accepted branch. -/
theorem TransitionFacts.frame
    {Key Value Root : Type*} [DecidableEq Key]
    (facts : TransitionFacts Key Value Root) (key : Key)
    (outside : key ∉ facts.footprint) : facts.post key = facts.pre key :=
  facts.delta.frame key (by simpa [facts.footprint_exact] using outside)

/-- An ordinary semantic commit yields the common view.  `Nonempty` is exactly
the existing executable-to-semantic bridge and does not select a proof witness
on the controller path. -/
theorem ordinary_facts
    {portal : TypedAuthorization.Portal} (authState : TypedAuthorization.AuthState)
    {ordinaryMaterializer :
      CellState.Materializer DeclaredTurn.effectSchema TypedAuthorization.Digest}
    {kind : TypedAuthorization.ResourceKind}
    (declaration : DeclaredTurn.Declaration portal ordinaryMaterializer kind)
    (postStore : EffectDeclaration.Store)
    (executed : DeclaredTurn.execute authState declaration = .committed postStore) :
    Nonempty (TransitionFacts EffectDeclaration.StateKey Int TypedAuthorization.Digest) := by
  rcases DeclaredTurn.execute_committed_sound authState declaration postStore executed with
    ⟨commit⟩
  let footprint : Finset EffectDeclaration.StateKey :=
    declaration.effects.footprint.toFinset
  let delta : ReactiveReceipt.ReceiptDelta declaration.preStore postStore :=
    { touched := footprint
      frame := by
        intro key outside
        exact commit.effect.frame key (by
          simpa [footprint, DeclaredTurn.Commit.footprint] using outside) }
  exact ⟨
    { preRoot := declaration.pre.root
      postRoot := commit.post.root
      pre := declaration.preStore
      post := postStore
      footprint := footprint
      delta := delta
      footprint_exact := rfl }⟩

/-- A resumed reactive acceptance yields the same view over the controller's
typed store.  Its roots are the canonical cell materializations checked by the
reactive/cell join. -/
def resumedFacts
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {reactiveMaterializer : CellState.Materializer S T.Root}
    {layout : CellState.ControllerLayout S T}
    {declaration : ReactiveController.Declaration U T}
    {observation : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice declaration.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized reactiveMaterializer}
    {patch : CellState.Patch S T.Root}
    (accepted : ReactiveCellTransition.Accepted reactiveMaterializer layout
      declaration observation advice proof controllerPre pre patch) :
    TransitionFacts T.Key T.Value T.Root where
  preRoot := pre.root
  postRoot := accepted.validated.apply.root
  pre := controllerPre
  post := accepted.intent.post
  footprint := declaration.hole.footprint
  delta := accepted.intent.delta
  footprint_exact := by
    change declaration.effect.touched = declaration.hole.footprint
    exact accepted.exact_bindings.effectFootprint

/-- Ordinary accepted roots are projections of the sole canonical pre/post
materializations. -/
theorem ordinary_facts_canonical_roots
    {portal : TypedAuthorization.Portal} {authState : TypedAuthorization.AuthState}
    {ordinaryMaterializer :
      CellState.Materializer DeclaredTurn.effectSchema TypedAuthorization.Digest}
    {kind : TypedAuthorization.ResourceKind}
    {declaration : DeclaredTurn.Declaration portal ordinaryMaterializer kind}
    {postStore : EffectDeclaration.Store}
    (commit : DeclaredTurn.Commit (state := authState) declaration postStore) :
    commit.preRoot = declaration.pre.root ∧ commit.postRoot = commit.post.root :=
  ⟨rfl, rfl⟩

/-- Resumed accepted roots are exactly the canonical cell roots established by
the joined controller. -/
theorem resumed_facts_canonical_roots
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {reactiveMaterializer : CellState.Materializer S T.Root}
    {layout : CellState.ControllerLayout S T}
    {declaration : ReactiveController.Declaration U T}
    {observation : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice declaration.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized reactiveMaterializer}
    {patch : CellState.Patch S T.Root}
    (accepted : ReactiveCellTransition.Accepted reactiveMaterializer layout
      declaration observation advice proof controllerPre pre patch) :
    (resumedFacts accepted).preRoot = pre.root ∧
      (resumedFacts accepted).postRoot = accepted.validated.apply.root :=
  ⟨rfl, rfl⟩

end Minidregg.Theory.TurnTransition
