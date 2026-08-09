/-
# Theory.ReactiveController -- Lean-authored guarded reaction control

This module removes semantic callbacks from the guarded/reactive boundary.  A
controller declaration is first-order data: one eager `HoleSpec`, a closed guard
term, a finite effect write-set with its expected post-root, and an optional
receipt/turn dependency.  Host inputs are observations only.  The controller
derives the existing `GuardedAdvice.FillVerifier`; a host never supplies one.

The result has exactly three semantic states: pending, rejected, or a dependent
`CommitIntent`.  A commit intent already contains an accepted guarded fill and a
`ReactiveReceipt.ReceiptDelta`.  It is only an intent: the physical durable
compare-and-swap and nullifier insertion remain an external handler which must
recheck the bound pre-root and nullifier atomically.
-/
import Theory.GuardedAdvice
import Theory.ReactiveReceipt

namespace Minidregg.Theory.ReactiveController

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram

universe u v

/-! ## First-order controller vocabulary -/

/-- Abstract first-order carriers.  The only semantic state representation
chosen here is a key/value store; every other carrier remains candidate-neutral. -/
structure Types where
  Key : Type u
  Value : Type u
  HoleId : Type u
  TurnId : Type u
  Root : Type u
  AuthorityDemand : Type u
  Commitment : Type u
  Height : Type u
  Continuation : Type u
  NullifierDomain : Type u

/-- The existing guarded-advice vocabulary instantiated with the controller's
finite key footprint. -/
abbrev Types.vocabulary (T : Types.{u}) : GuardedAdvice.Vocabulary.{u} where
  HoleId := T.HoleId
  TurnId := T.TurnId
  Root := T.Root
  AuthorityDemand := T.AuthorityDemand
  Footprint := Finset T.Key
  Commitment := T.Commitment
  Height := T.Height
  Continuation := T.Continuation
  NullifierDomain := T.NullifierDomain

abbrev HoleSpec (U : FirstOrderUniverse.{u, v}) (T : Types.{u}) :=
  GuardedAdvice.HoleSpec U T.vocabulary

abbrev Advice {U : FirstOrderUniverse.{u, v}} {T : Types.{u}}
    (spec : HoleSpec U T) :=
  GuardedAdvice.Advice spec

/-- Closed first-order guard syntax over the canonical advice bytes.  There are
no semantic closures or host-provided predicates. -/
inductive GuardTerm
  | allow
  | deny
  | bytesEq (expected : List UInt8)
  | lengthLE (bound : Nat)
  | and (left right : GuardTerm)
  | or (left right : GuardTerm)
deriving DecidableEq, Repr

/-- The sole interpretation of `GuardTerm`. -/
def GuardTerm.eval (bytes : List UInt8) : GuardTerm → Bool
  | .allow => true
  | .deny => false
  | .bytesEq expected => decide (bytes = expected)
  | .lengthLE bound => decide (bytes.length ≤ bound)
  | .and left right => left.eval bytes && right.eval bytes
  | .or left right => left.eval bytes || right.eval bytes

/-- A finite, first-order effect declaration.  Its write-set is the executable
effect and `expectedPostRoot` is the root which late proof data must open. -/
structure EffectDecl (T : Types.{u}) where
  writes : List (T.Key × T.Value)
  expectedPostRoot : T.Root

/-- One complete Lean-authored controller declaration.  The request, verifier,
write footprint, and receipt delta below are all derived from this data. -/
structure Declaration (U : FirstOrderUniverse.{u, v}) (T : Types.{u}) where
  hole : HoleSpec U T
  guard : GuardTerm
  effect : EffectDecl T
  wakeAfter : Option T.TurnId

/-! ## Derived request and finite effect interpretation -/

/-- The exact request committed by a guarded fill.  It repeats the eager fields
at the boundary only as a derived first-order projection, never as independent
host-authored data. -/
structure Request (U : FirstOrderUniverse.{u, v}) (T : Types.{u}) where
  holeId : T.HoleId
  code : U.Code
  turnId : T.TurnId
  preRoot : T.Root
  authorityDemand : T.AuthorityDemand
  footprint : Finset T.Key
  guardCommitment : T.Commitment
  effectCommitment : T.Commitment
  deadline : T.Height
  continuation : T.Continuation
  nullifierDomain : T.NullifierDomain
  adviceBytes : List UInt8

/-- Request projection from the exact spec/advice pair. -/
def Request.of
    {U : FirstOrderUniverse.{u, v}} {T : Types.{u}}
    (spec : HoleSpec U T) (advice : Advice spec) : Request U T where
  holeId := spec.holeId
  code := spec.code
  turnId := spec.turnId
  preRoot := spec.preRoot
  authorityDemand := spec.authorityDemand
  footprint := spec.footprint
  guardCommitment := spec.guardCommitment
  effectCommitment := spec.effectCommitment
  deadline := spec.deadline
  continuation := spec.continuation
  nullifierDomain := spec.nullifierDomain
  adviceBytes := spec.codec.encode advice.value

/-- Exact keys named by the effect declaration. -/
def EffectDecl.touched {T : Types.{u}} [DecidableEq T.Key]
    (effect : EffectDecl T) : Finset T.Key :=
  (effect.writes.map Prod.fst).toFinset

/-- Apply a finite write-set in declaration order.  Later duplicate writes to
one key win, while the footprint still names that key once. -/
def applyWrites {T : Types.{u}} [DecidableEq T.Key] :
    List (T.Key × T.Value) → ReactiveReceipt.Store T.Key T.Value →
      ReactiveReceipt.Store T.Key T.Value
  | [], state => state
  | (writeKey, value) :: rest, state =>
      applyWrites rest (fun key => if key = writeKey then value else state key)

/-- The finite effect has the anti-ghost frame property by construction. -/
theorem applyWrites_frame
    {T : Types.{u}} [DecidableEq T.Key]
    (writes : List (T.Key × T.Value)) (pre : ReactiveReceipt.Store T.Key T.Value)
    (key : T.Key) (outside : key ∉ (writes.map Prod.fst).toFinset) :
    applyWrites writes pre key = pre key := by
  induction writes generalizing pre with
  | nil => rfl
  | cons write rest ih =>
      rcases write with ⟨writeKey, value⟩
      simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert, not_or] at outside
      rw [applyWrites, ih _ outside.2]
      simp [outside.1]

/-- The receipt delta is derived from the same finite write declaration as the
post-state; the host does not author a touched mask. -/
def EffectDecl.delta
    {T : Types.{u}} [DecidableEq T.Key]
    (effect : EffectDecl T) (pre : ReactiveReceipt.Store T.Key T.Value) :
    ReactiveReceipt.ReceiptDelta pre (applyWrites effect.writes pre) where
  touched := effect.touched
  frame := fun key outside =>
    applyWrites_frame effect.writes pre key (by simpa [EffectDecl.touched] using outside)

/-! ## Observations and proof data are data, not verdict callbacks -/

/-- External observations sampled for one controller run.  The host may report
availability and observed durable state, but it supplies no predicate or
decision function.  Durable CAS must sample these conditions again atomically. -/
structure HostObservation (T : Types.{u}) where
  now : T.Height
  durableRoot : T.Root
  backendAvailable : Bool
  finalizedTurns : Finset T.TurnId
  consumed : Finset (GuardedAdvice.NullifierKey T.vocabulary)

/-- Late proof/opening data.  Every field is checked against the Lean-authored
declaration; none is itself a verdict bit. -/
structure ProofData (T : Types.{u}) where
  authority : T.AuthorityDemand
  guardCommitment : T.Commitment
  effectCommitment : T.Commitment
  writes : List (T.Key × T.Value)
  postRoot : T.Root

/-- First-order readiness: either no dependency was declared, or its turn id is
present in the observed finalized set. -/
def Declaration.ready
    {U : FirstOrderUniverse.{u, v}} {T : Types.{u}} [DecidableEq T.TurnId]
    (decl : Declaration U T) (obs : HostObservation T) : Bool :=
  match decl.wakeAfter with
  | none => true
  | some turnId => decide (turnId ∈ obs.finalizedTurns)

/-- The one verifier interpretation, derived entirely from first-order
declaration, observation, and proof data. -/
def Declaration.verifier
    {U : FirstOrderUniverse.{u, v}} {T : Types.{u}}
    [DecidableEq (HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    (decl : Declaration U T) (obs : HostObservation T) (proof : ProofData T) :
    GuardedAdvice.FillVerifier U T.vocabulary where
  supports := fun spec => decide (spec = decl.hole)
  backendAvailable := fun _ => obs.backendAvailable
  ready := fun _ _ => decl.ready obs
  authorityAccepts := fun spec _ => decide (proof.authority = spec.authorityDemand)
  guardAccepts := fun spec advice =>
    decide (proof.guardCommitment = spec.guardCommitment) &&
      decl.guard.eval (spec.codec.encode advice.value)
  effectAccepts := fun spec _ =>
    decide (proof.effectCommitment = spec.effectCommitment) &&
      decide (proof.writes = decl.effect.writes) &&
      decide (proof.postRoot = decl.effect.expectedPostRoot) &&
      decide (decl.effect.touched = spec.footprint)
  postRoot := fun _ _ => proof.postRoot

/-! ## Indexed controller result -/

/-- Total rejection reasons at the controller boundary. -/
inductive RejectReason
  | unsupported
  | backendUnavailable
  | expired
  | stalePreRoot
  | alreadyConsumed
  | authority
  | guard
  | effect
deriving DecidableEq, Repr

/-- A commit-ready semantic object.  It binds the exact declaration,
observation, advice, proof data, and pre-state.  It is not evidence that a
physical CAS has occurred. -/
structure CommitIntent
    {U : FirstOrderUniverse.{u, v}} {T : Types.{u}}
    [LinearOrder T.Height]
    [DecidableEq (HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    (decl : Declaration U T) (obs : HostObservation T)
    (advice : Advice decl.hole) (proof : ProofData T)
    (pre : ReactiveReceipt.Store T.Key T.Value) where
  verified : GuardedAdvice.VerifiedFill (decl.verifier obs proof) obs.now decl.hole advice
  verified_outcome :
    GuardedAdvice.verifyFill (decl.verifier obs proof) obs.now decl.hole advice =
      .accepted verified
  observed_pre_root : obs.durableRoot = decl.hole.preRoot
  observed_fresh : decl.hole.nullifierKey ∉ obs.consumed

/-- The exact request carried by an intent. -/
def CommitIntent.request
    {U : FirstOrderUniverse.{u, v}} {T : Types.{u}}
    [LinearOrder T.Height]
    [DecidableEq (HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {decl : Declaration U T} {obs : HostObservation T}
    {advice : Advice decl.hole} {proof : ProofData T}
    {pre : ReactiveReceipt.Store T.Key T.Value}
    (_intent : CommitIntent decl obs advice proof pre) : Request U T :=
  Request.of decl.hole advice

/-- The post-state is the sole finite effect interpretation. -/
def CommitIntent.post
    {U : FirstOrderUniverse.{u, v}} {T : Types.{u}}
    [LinearOrder T.Height]
    [DecidableEq (HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {decl : Declaration U T} {obs : HostObservation T}
    {advice : Advice decl.hole} {proof : ProofData T}
    {pre : ReactiveReceipt.Store T.Key T.Value}
    (_intent : CommitIntent decl obs advice proof pre) :
    ReactiveReceipt.Store T.Key T.Value :=
  applyWrites decl.effect.writes pre

/-- The receipt delta is the declaration-derived delta, not a host event mask. -/
def CommitIntent.delta
    {U : FirstOrderUniverse.{u, v}} {T : Types.{u}}
    [LinearOrder T.Height]
    [DecidableEq (HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {decl : Declaration U T} {obs : HostObservation T}
    {advice : Advice decl.hole} {proof : ProofData T}
    {pre : ReactiveReceipt.Store T.Key T.Value}
    (intent : CommitIntent decl obs advice proof pre) :
    ReactiveReceipt.ReceiptDelta pre intent.post :=
  decl.effect.delta pre

/-- Three-state controller result: not ready, refused, or commit-ready. -/
inductive Outcome
    {U : FirstOrderUniverse.{u, v}} {T : Types.{u}}
    [LinearOrder T.Height]
    [DecidableEq (HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    (decl : Declaration U T) (obs : HostObservation T)
    (advice : Advice decl.hole) (proof : ProofData T)
    (pre : ReactiveReceipt.Store T.Key T.Value) where
  | pending
  | reject (reason : RejectReason)
  | commitIntent (intent : CommitIntent decl obs advice proof pre)

/-- Map the existing guarded rejection vocabulary without inventing another
semantic decision. -/
def RejectReason.ofGuarded : GuardedAdvice.RejectReason → RejectReason
  | .authority => .authority
  | .guard => .guard
  | .effect => .effect

/-- The indexed controller.  Existing guarded verification runs first; observed
root/freshness are then checked before an intent is released.  The durable host
must repeat those latter checks inside its physical CAS. -/
def control
    {U : FirstOrderUniverse.{u, v}} {T : Types.{u}}
    [LinearOrder T.Height]
    [DecidableEq (HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    (decl : Declaration U T) (obs : HostObservation T)
    (advice : Advice decl.hole) (proof : ProofData T)
    (pre : ReactiveReceipt.Store T.Key T.Value) : Outcome decl obs advice proof pre :=
  match hverify : GuardedAdvice.verifyFill (decl.verifier obs proof) obs.now decl.hole advice with
  | .accepted verified =>
      if hroot : obs.durableRoot = decl.hole.preRoot then
        if hfresh : decl.hole.nullifierKey ∉ obs.consumed then
          .commitIntent ⟨verified, hverify, hroot, hfresh⟩
        else
          .reject .alreadyConsumed
      else
        .reject .stalePreRoot
  | .rejected reason => .reject (.ofGuarded reason)
  | .pending => .pending
  | .expired => .reject .expired
  | .unsupported => .reject .unsupported
  | .backendUnavailable => .reject .backendUnavailable

/-! ## Authority and frame theorems -/

/-- A commit intent is evidence of acceptance by the existing guarded-advice
verifier, not a parallel controller-specific verdict. -/
theorem CommitIntent.implies_guarded_verification
    {U : FirstOrderUniverse.{u, v}} {T : Types.{u}}
    [LinearOrder T.Height]
    [DecidableEq (HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {decl : Declaration U T} {obs : HostObservation T}
    {advice : Advice decl.hole} {proof : ProofData T}
    {pre : ReactiveReceipt.Store T.Key T.Value}
    (intent : CommitIntent decl obs advice proof pre) :
    GuardedAdvice.verifyFill (decl.verifier obs proof) obs.now decl.hole advice =
      .accepted intent.verified :=
  intent.verified_outcome

/-- The exact request binds every eager security field and the typed advice. -/
theorem CommitIntent.request_binds_hole
    {U : FirstOrderUniverse.{u, v}} {T : Types.{u}}
    [LinearOrder T.Height]
    [DecidableEq (HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {decl : Declaration U T} {obs : HostObservation T}
    {advice : Advice decl.hole} {proof : ProofData T}
    {pre : ReactiveReceipt.Store T.Key T.Value}
    (intent : CommitIntent decl obs advice proof pre) :
    intent.request.holeId = decl.hole.holeId ∧
      intent.request.code = decl.hole.code ∧
      intent.request.turnId = decl.hole.turnId ∧
      intent.request.preRoot = decl.hole.preRoot ∧
      intent.request.guardCommitment = decl.hole.guardCommitment ∧
      intent.request.effectCommitment = decl.hole.effectCommitment ∧
      intent.request.authorityDemand = decl.hole.authorityDemand ∧
      intent.request.footprint = decl.hole.footprint ∧
      intent.request.deadline = decl.hole.deadline ∧
      intent.request.continuation = decl.hole.continuation ∧
      intent.request.nullifierDomain = decl.hole.nullifierDomain ∧
      intent.request.adviceBytes = decl.hole.codec.encode advice.value ∧
      decl.hole.nullifierKey =
        ⟨intent.request.nullifierDomain, intent.request.turnId, intent.request.holeId⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A commit intent supplies the existing reactive receipt-delta object. -/
theorem CommitIntent.implies_receipt_delta
    {U : FirstOrderUniverse.{u, v}} {T : Types.{u}}
    [LinearOrder T.Height]
    [DecidableEq (HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {decl : Declaration U T} {obs : HostObservation T}
    {advice : Advice decl.hole} {proof : ProofData T}
    {pre : ReactiveReceipt.Store T.Key T.Value}
    (intent : CommitIntent decl obs advice proof pre) :
    Nonempty (ReactiveReceipt.ReceiptDelta pre intent.post) :=
  ⟨intent.delta⟩

/-- The receipt's frame law: every key outside the declaration-derived effect
footprint is unchanged. -/
theorem CommitIntent.frame
    {U : FirstOrderUniverse.{u, v}} {T : Types.{u}}
    [LinearOrder T.Height]
    [DecidableEq (HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {decl : Declaration U T} {obs : HostObservation T}
    {advice : Advice decl.hole} {proof : ProofData T}
    {pre : ReactiveReceipt.Store T.Key T.Value}
    (intent : CommitIntent decl obs advice proof pre)
    (key : T.Key) (outside : key ∉ intent.delta.touched) :
    intent.post key = pre key :=
  intent.delta.frame key outside

/-- The accepted verifier forces the supplied post-root/effect proof data to
open the exact Lean declaration and eager footprint. -/
theorem CommitIntent.proof_data_bound
    {U : FirstOrderUniverse.{u, v}} {T : Types.{u}}
    [LinearOrder T.Height]
    [DecidableEq (HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {decl : Declaration U T} {obs : HostObservation T}
    {advice : Advice decl.hole} {proof : ProofData T}
    {pre : ReactiveReceipt.Store T.Key T.Value}
    (intent : CommitIntent decl obs advice proof pre) :
    proof.authority = decl.hole.authorityDemand ∧
      proof.guardCommitment = decl.hole.guardCommitment ∧
      decl.guard.eval (decl.hole.codec.encode advice.value) = true ∧
      proof.effectCommitment = decl.hole.effectCommitment ∧
      proof.writes = decl.effect.writes ∧
      proof.postRoot = decl.effect.expectedPostRoot ∧
      decl.effect.touched = decl.hole.footprint := by
  have h := GuardedAdvice.verify_accepted_forces_bound_checks intent.verified
  simpa [Declaration.verifier, and_assoc] using h

end Minidregg.Theory.ReactiveController
