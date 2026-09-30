/-
# Theory.ReactiveCellTransition -- guarded control over canonical typed cells

This module joins the Lean-derived reactive controller with canonical cell
materialization.  There is no caller-supplied verifier: `transition` first runs
`ReactiveController.control`, then validates the exact typed cell patch against
the pre-root the controller's request quoted, and finally checks the verified
post-root and the footprint before minting an `Accepted` package.  The
`PreparedTurn.ofReactiveAccepted` adapter into the canonical transition nucleus
lives at the end of this module.

The accepted post-cell below remains a logical candidate.  A physical durable
compare-and-swap plus nullifier insertion is represented by one explicit
handler-receipt premise at the final release boundary; no definition in this
module silently mutates a durable store.
-/
import Theory.CanonicalTransition

namespace Minidregg.Theory.ReactiveCellTransition

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.Store

universe u v w z

/-! ## Indexed accepted and total transition outcomes -/

/-- A controller-approved and cell-validated patch.  Its private constructor is
reachable only after both existing verifiers and the exact binding checks run. -/
structure Accepted
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {L : Layout.{u, v, w}}
    (M : CellState.Materializer L T.Root)
    (layout : CellState.ControllerLayout L T)
    (decl : ReactiveController.Declaration U T)
    (obs : ReactiveController.HostObservation T)
    (advice : ReactiveController.Advice decl.hole)
    (proof : ReactiveController.ProofData T)
    (controllerPre : ReactiveReceipt.Store T.Key T.Value)
    (pre : CellState.Materialized M) (patch : Patch L) where
  private mk ::
  intent : ReactiveController.CommitIntent decl obs advice proof controllerPre
  validated : CellState.ValidatedPatch M pre intent.request.preRoot patch
  binding : CellState.IntentBinding M layout intent pre validated

/-- Transition failures preserve their source: controller policy/temporal
failure, cell validation failure (a stale quoted pre-root is
`patch .stalePreRoot`), or a precise cross-layer binding mismatch. -/
inductive RejectReason
  | controller (reason : ReactiveController.RejectReason)
  | patch (reason : CellState.RejectReason)
  | postRootMismatch
  | footprintMismatch
deriving DecidableEq, Repr

/-- The complete first-order transition result. -/
inductive Outcome
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {L : Layout.{u, v, w}}
    (M : CellState.Materializer L T.Root)
    (layout : CellState.ControllerLayout L T)
    (decl : ReactiveController.Declaration U T)
    (obs : ReactiveController.HostObservation T)
    (advice : ReactiveController.Advice decl.hole)
    (proof : ReactiveController.ProofData T)
    (controllerPre : ReactiveReceipt.Store T.Key T.Value)
    (pre : CellState.Materialized M) (patch : Patch L) where
  | blocked
  | rejected (reason : RejectReason)
  | accepted (result :
      Accepted M layout decl obs advice proof controllerPre pre patch)

/-- The total joined controller.  Every decision is the interpretation already
defined in Lean plus decidable equality on first-order data. -/
def transition
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {L : Layout.{u, v, w}}
    (M : CellState.Materializer L T.Root)
    (layout : CellState.ControllerLayout L T)
    (decl : ReactiveController.Declaration U T)
    (obs : ReactiveController.HostObservation T)
    (advice : ReactiveController.Advice decl.hole)
    (proof : ReactiveController.ProofData T)
    (controllerPre : ReactiveReceipt.Store T.Key T.Value)
    (pre : CellState.Materialized M) (patch : Patch L) :
    Outcome M layout decl obs advice proof controllerPre pre patch :=
  match ReactiveController.control decl obs advice proof controllerPre with
  | .pending => .blocked
  | .reject reason => .rejected (.controller reason)
  | .commitIntent intent =>
      match CellState.validate M pre intent.request.preRoot patch with
      | .rejected reason => .rejected (.patch reason)
      | .accepted validated =>
          if hpost : intent.verified.postRoot = validated.apply.root then
            if hfootprint :
                CellState.controllerFootprint layout patch = decl.hole.footprint then
              .accepted ⟨intent, validated, ⟨hpost, hfootprint⟩⟩
            else
              .rejected .footprintMismatch
          else
            .rejected .postRootMismatch

/-! ## Logical post-state and atomic refusal -/

/-- Pure logical reading of an outcome.  Acceptance applies the validated patch;
blocked and rejected results are definitionally the original materialization. -/
def Outcome.logicalPost
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L T.Root}
    {layout : CellState.ControllerLayout L T}
    {decl : ReactiveController.Declaration U T}
    {obs : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice decl.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized M} {patch : Patch L} :
    Outcome M layout decl obs advice proof controllerPre pre patch →
      CellState.Materialized M
  | .blocked => pre
  | .rejected _ => pre
  | .accepted result => result.validated.apply

@[simp] theorem Outcome.blocked_unchanged
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L T.Root}
    {layout : CellState.ControllerLayout L T}
    {decl : ReactiveController.Declaration U T}
    {obs : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice decl.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized M} {patch : Patch L} :
    (Outcome.blocked (M := M) (layout := layout) (decl := decl) (obs := obs)
      (advice := advice) (proof := proof) (controllerPre := controllerPre)
      (pre := pre) (patch := patch)).logicalPost = pre :=
  rfl

@[simp] theorem Outcome.rejected_unchanged
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L T.Root}
    {layout : CellState.ControllerLayout L T}
    {decl : ReactiveController.Declaration U T}
    {obs : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice decl.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized M} {patch : Patch L}
    (reason : RejectReason) :
    (Outcome.rejected (M := M) (layout := layout) (decl := decl) (obs := obs)
      (advice := advice) (proof := proof) (controllerPre := controllerPre)
      (pre := pre) (patch := patch) reason).logicalPost = pre :=
  rfl

/-! ## Exact declaration-derived binding facts -/

/-- All security-relevant equalities exposed by one accepted transition. -/
structure BindingFacts
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L T.Root}
    {layout : CellState.ControllerLayout L T}
    {decl : ReactiveController.Declaration U T}
    {obs : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice decl.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized M} {patch : Patch L}
    (accepted : Accepted M layout decl obs advice proof controllerPre pre patch) : Prop where
  holeId : accepted.intent.request.holeId = decl.hole.holeId
  code : accepted.intent.request.code = decl.hole.code
  turnId : accepted.intent.request.turnId = decl.hole.turnId
  eagerPreRoot : accepted.intent.request.preRoot = decl.hole.preRoot
  authorityDemand : accepted.intent.request.authorityDemand = decl.hole.authorityDemand
  requestFootprint : accepted.intent.request.footprint = decl.hole.footprint
  guardCommitment : accepted.intent.request.guardCommitment = decl.hole.guardCommitment
  effectCommitment : accepted.intent.request.effectCommitment = decl.hole.effectCommitment
  deadline : accepted.intent.request.deadline = decl.hole.deadline
  continuation : accepted.intent.request.continuation = decl.hole.continuation
  nullifierDomain : accepted.intent.request.nullifierDomain = decl.hole.nullifierDomain
  adviceBytes : accepted.intent.request.adviceBytes =
    decl.hole.codec.encode advice.value
  nullifier : decl.hole.nullifierKey =
    ⟨accepted.intent.request.nullifierDomain, accepted.intent.request.turnId,
      accepted.intent.request.holeId⟩
  observedPreRoot : obs.durableRoot = decl.hole.preRoot
  nullifierFresh : decl.hole.nullifierKey ∉ obs.consumed
  authorityProof : proof.authority = decl.hole.authorityDemand
  guardOpening : proof.guardCommitment = decl.hole.guardCommitment
  guardHolds : decl.guard.eval (decl.hole.codec.encode advice.value) = true
  effectOpening : proof.effectCommitment = decl.hole.effectCommitment
  effectWrites : proof.writes = decl.effect.writes
  effectPostRoot : proof.postRoot = decl.effect.expectedPostRoot
  effectFootprint : decl.effect.touched = decl.hole.footprint
  verifiedPostRoot : accepted.intent.verified.postRoot = proof.postRoot
  patchFootprint : CellState.controllerFootprint layout patch = decl.hole.footprint
  cellPreRoot : accepted.intent.request.preRoot = pre.root
  cellPostRoot : accepted.intent.verified.postRoot = accepted.validated.apply.root

/-- Acceptance exposes exactly the request, proof-opening, nullifier, footprint,
and canonical pre/post bindings derived from the Lean declaration. -/
theorem Accepted.exact_bindings
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L T.Root}
    {layout : CellState.ControllerLayout L T}
    {decl : ReactiveController.Declaration U T}
    {obs : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice decl.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized M} {patch : Patch L}
    (accepted : Accepted M layout decl obs advice proof controllerPre pre patch) :
    BindingFacts accepted := by
  rcases accepted.intent.request_binds_hole with
    ⟨hhole, hcode, hturn, hpre, hguard, heffect, hauthority, hfootprint,
      hdeadline, hcontinuation, hdomain, hadvice, hnullifier⟩
  rcases accepted.intent.proof_data_bound with
    ⟨hauthorityProof, hguardOpening, hguardHolds, heffectOpening,
      heffectWrites, heffectPost, heffectFootprint⟩
  exact
    { holeId := hhole
      code := hcode
      turnId := hturn
      eagerPreRoot := hpre
      authorityDemand := hauthority
      requestFootprint := hfootprint
      guardCommitment := hguard
      effectCommitment := heffect
      deadline := hdeadline
      continuation := hcontinuation
      nullifierDomain := hdomain
      adviceBytes := hadvice
      nullifier := hnullifier
      observedPreRoot := accepted.intent.observed_pre_root
      nullifierFresh := accepted.intent.observed_fresh
      authorityProof := hauthorityProof
      guardOpening := hguardOpening
      guardHolds := hguardHolds
      effectOpening := heffectOpening
      effectWrites := heffectWrites
      effectPostRoot := heffectPost
      effectFootprint := heffectFootprint
      verifiedPostRoot := by
        simpa [ReactiveController.Declaration.verifier] using
          accepted.intent.verified.postRoot_eq
      patchFootprint := accepted.binding.footprint_bound
      cellPreRoot := accepted.validated.preRoot_bound
      cellPostRoot := accepted.binding.postRoot_bound }

/-! ## One explicit physical handler premise -/

/-- First-order receipt emitted by the irreducible durable handler. -/
structure HandlerReceipt (T : ReactiveController.Types.{z}) where
  atomic : Bool
  comparedPreRoot : T.Root
  installedPostRoot : T.Root
  insertedNullifier : GuardedAdvice.NullifierKey T.vocabulary

/-- The sole physical handler premise.  It binds one atomic CAS/nullifier
receipt to the already accepted logical transition. -/
structure HandlerPremise
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L T.Root}
    {layout : CellState.ControllerLayout L T}
    {decl : ReactiveController.Declaration U T}
    {obs : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice decl.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized M} {patch : Patch L}
    (accepted : Accepted M layout decl obs advice proof controllerPre pre patch)
    (receipt : HandlerReceipt T) : Prop where
  atomic : receipt.atomic = true
  preRoot : receipt.comparedPreRoot = accepted.intent.request.preRoot
  postRoot : receipt.installedPostRoot = accepted.intent.verified.postRoot
  nullifier : receipt.insertedNullifier = decl.hole.nullifierKey

/-- Release the logical post-cell only under the one explicit physical handler
premise.  The premise is consumed as evidence; this function performs no I/O. -/
def Accepted.releaseAfterPhysicalCommit
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L T.Root}
    {layout : CellState.ControllerLayout L T}
    {decl : ReactiveController.Declaration U T}
    {obs : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice decl.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized M} {patch : Patch L}
    (accepted : Accepted M layout decl obs advice proof controllerPre pre patch)
    (receipt : HandlerReceipt T) (_handler : HandlerPremise accepted receipt) :
    CellState.Materialized M :=
  accepted.validated.apply

end Minidregg.Theory.ReactiveCellTransition

namespace Minidregg.Theory.CanonicalTransition

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.Store

universe u v w z

/-! ## Adapter into the canonical transition nucleus -/

/-- Reactive acceptance projects into the canonical nucleus using only its
validated typed cell patch.  The parallel controller store is not retained. -/
def PreparedTurn.ofReactiveAccepted
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L T.Root}
    {layout : CellState.ControllerLayout L T}
    {declaration : ReactiveController.Declaration U T}
    {observation : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice declaration.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized M} {patch : Patch L}
    (accepted : ReactiveCellTransition.Accepted M layout declaration observation
      advice proof controllerPre pre patch) :
    PreparedTurn M pre (GuardedAdvice.NullifierKey T.vocabulary) :=
  PreparedTurn.ofValidatedPatch accepted.validated (some declaration.hole.nullifierKey)

@[simp] theorem PreparedTurn.ofReactiveAccepted_nullifier
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L T.Root}
    {layout : CellState.ControllerLayout L T}
    {declaration : ReactiveController.Declaration U T}
    {observation : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice declaration.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized M} {patch : Patch L}
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
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L T.Root}
    {layout : CellState.ControllerLayout L T}
    {declaration : ReactiveController.Declaration U T}
    {observation : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice declaration.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized M} {patch : Patch L}
    (accepted : ReactiveCellTransition.Accepted M layout declaration observation
      advice proof controllerPre pre patch) :
    (PreparedTurn.ofReactiveAccepted accepted).preRoot =
      accepted.intent.request.preRoot :=
  PreparedTurn.ofValidatedPatch_preRoot accepted.validated _

/-- The reactive adapter's post-root is exactly the verified fill root. -/
theorem PreparedTurn.ofReactiveAccepted_postRoot
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L T.Root}
    {layout : CellState.ControllerLayout L T}
    {declaration : ReactiveController.Declaration U T}
    {observation : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice declaration.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized M} {patch : Patch L}
    (accepted : ReactiveCellTransition.Accepted M layout declaration observation
      advice proof controllerPre pre patch) :
    (PreparedTurn.ofReactiveAccepted accepted).postRoot =
      accepted.intent.verified.postRoot :=
  accepted.exact_bindings.cellPostRoot.symm

/-- The adapter preserves the eager unified footprint: the controller image of
the delta's (derived) footprint is the hole's footprint. -/
theorem PreparedTurn.ofReactiveAccepted_footprint
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L T.Root}
    {layout : CellState.ControllerLayout L T}
    {declaration : ReactiveController.Declaration U T}
    {observation : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice declaration.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized M} {patch : Patch L}
    (accepted : ReactiveCellTransition.Accepted M layout declaration observation
      advice proof controllerPre pre patch) :
    (PreparedTurn.ofReactiveAccepted accepted).delta.footprint.image layout.addressKey =
      declaration.hole.footprint :=
  accepted.exact_bindings.patchFootprint

/-- info: 'Minidregg.Theory.CanonicalTransition.PreparedTurn.ofReactiveAccepted_footprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedTurn.ofReactiveAccepted_footprint
/-- info: 'Minidregg.Theory.CanonicalTransition.PreparedTurn.ofReactiveAccepted_postRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedTurn.ofReactiveAccepted_postRoot

end Minidregg.Theory.CanonicalTransition
