/-
# Assurance.SemanticTurnReceipt — the typed receipt admitted to history

`SemanticReceiptRelation` is the fixed algebraic nucleus: pre-state, post-state,
and an exact touched mask.  This file supplies the semantic wrapper that must be
proved before that nucleus is admitted to an outer accumulator.

The wrapper deliberately has one request-indexed authorization judgment.  A
committed outcome carries an `Authorized ... request`, the exact effect list
whose digest occurs in that same request, a semantics proof for the resulting
`ReceiptDelta`, and authorized disclosure events.  A rejected outcome carries
no post-state at all, so rejection atomicity is definitional.

This is a semantic relation, not a receipt byte codec and not a cryptographic
proof system.  Rust currently has no operational semantics, so no Rust
"refinement theorem" can be stated.  `[SEMANTIC-TURN-generated]` is the task of
emitting the receipt encoder/verifier interface from this Lean authority;
handwritten Rust remains unverified compute.  `[PCH-OUTER-ACCUMULATOR]` is
the hiding, knowledge-sound unbounded accumulator over its algebraic core.
-/
import Assurance.SemanticReceiptRelation
import Theory.TypedAuthorization
import Theory.PrivacyProfile

namespace Minidregg.Assurance.SemanticTurnReceipt

open Minidregg.Theory.ReactiveReceipt
open Minidregg.Theory.TypedAuthorization
open Minidregg.Assurance.SemanticReceiptRelation

universe uKey uValue uEffect uDisclosure uError

/-- The semantic state-root function.  A concrete codec/commitment realization
must prove that its public root implements this function. -/
structure StateCommitment (Key : Type uKey) (Value : Type uValue) where
  root : Store Key Value → Digest

/-- An effect interpreter owns both the canonical digest bound into the request
and the exact relation between the effect list and the committed delta. -/
structure EffectSemantics
    (Key : Type uKey) (Value : Type uValue) (Effect : Type uEffect)
    [DecidableEq Key] where
  digest : List Effect → Digest
  Realizes : {kind : ResourceKind} →
    Request kind → List Effect →
    {pre post : Store Key Value} → ReceiptDelta pre post → Prop

/-- Disclosure is an explicit request-indexed policy judgment.  Cryptographic
hiding and executor visibility remain independent obligations. -/
structure DisclosurePolicy (Disclosure : Type uDisclosure) where
  Permitted : {kind : ResourceKind} → Request kind → Disclosure → Prop

/-- Everything that exists only for a committed outcome.  In particular,
authorization evidence is indexed by the exact request in the surrounding
receipt; no credential mode can substitute a different target or effect digest. -/
structure CommittedTurn
    (portal : Portal) (authState : AuthState)
    {kind : ResourceKind} (request : Request kind)
    {Key : Type uKey} {Value : Type uValue} {Effect : Type uEffect}
    {Disclosure : Type uDisclosure} [DecidableEq Key]
    (stateCommitment : StateCommitment Key Value)
    (effectSemantics : EffectSemantics Key Value Effect)
    (disclosurePolicy : DisclosurePolicy Disclosure)
    (pre : Store Key Value) where
  authorization : Authorized portal authState request
  post : Store Key Value
  delta : ReceiptDelta pre post
  postStateRoot : Digest
  postRootBound : postStateRoot = stateCommitment.root post
  effects : List Effect
  effectsDigestBound : effectSemantics.digest effects = request.effectsDigest
  effectsRealize : effectSemantics.Realizes request effects delta
  disclosures : List Disclosure
  disclosuresPermitted :
    ∀ disclosure ∈ disclosures, disclosurePolicy.Permitted request disclosure

/-- The complete semantic turn receipt.  The pre-state root is bound by the
request itself.  Rejection is the left summand and has no post-state field. -/
structure TurnReceipt
    (portal : Portal) (authState : AuthState)
    (kind : ResourceKind)
    {Key : Type uKey} {Value : Type uValue} {Effect : Type uEffect}
    {Disclosure : Type uDisclosure} (Error : Type uError)
    [DecidableEq Key]
    (stateCommitment : StateCommitment Key Value)
    (effectSemantics : EffectSemantics Key Value Effect)
    (disclosurePolicy : DisclosurePolicy Disclosure) where
  request : Request kind
  pre : Store Key Value
  preRootBound : request.preStateRoot = stateCommitment.root pre
  outcome : Error ⊕
    CommittedTurn portal authState request stateCommitment
      effectSemantics disclosurePolicy pre

namespace TurnReceipt

variable
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {Key : Type uKey} {Value : Type uValue} {Effect : Type uEffect}
    {Disclosure : Type uDisclosure} {Error : Type uError}
    [DecidableEq Key]
    {stateCommitment : StateCommitment Key Value}
    {effectSemantics : EffectSemantics Key Value Effect}
    {disclosurePolicy : DisclosurePolicy Disclosure}

/-- Construct a rejected receipt.  There is intentionally no authorization or
post-state argument: a denial is still a causal, replayable attempted receipt. -/
def rejected (request : Request kind) (pre : Store Key Value)
    (preRootBound : request.preStateRoot = stateCommitment.root pre)
    (error : Error) :
    TurnReceipt portal authState kind Error stateCommitment
      effectSemantics disclosurePolicy :=
  ⟨request, pre, preRootBound, .inl error⟩

/-- Construct a committed receipt from the full request-indexed payload. -/
def committed (request : Request kind) (pre : Store Key Value)
    (preRootBound : request.preStateRoot = stateCommitment.root pre)
    (commit : CommittedTurn portal authState request stateCommitment
      effectSemantics disclosurePolicy pre) :
    TurnReceipt portal authState kind Error stateCommitment
      effectSemantics disclosurePolicy :=
  ⟨request, pre, preRootBound, .inr commit⟩

/-- Observable post-state.  Rejection is definitionally the pre-state. -/
def post (receipt : TurnReceipt portal authState kind Error stateCommitment
    effectSemantics disclosurePolicy) : Store Key Value :=
  match receipt.outcome with
  | .inl _ => receipt.pre
  | .inr commit => commit.post

@[simp] theorem rejected_atomic
    (request : Request kind) (pre : Store Key Value)
    (preRootBound : request.preStateRoot = stateCommitment.root pre)
    (error : Error) :
    (rejected (portal := portal) (authState := authState)
      (effectSemantics := effectSemantics)
      (disclosurePolicy := disclosurePolicy)
      request pre preRootBound error).post = pre :=
  rfl

@[simp] theorem committed_post
    (request : Request kind) (pre : Store Key Value)
    (preRootBound : request.preStateRoot = stateCommitment.root pre)
    (commit : CommittedTurn portal authState request stateCommitment
      effectSemantics disclosurePolicy pre) :
    (committed (Error := Error) request pre preRootBound commit).post = commit.post :=
  rfl

/-- A committed receipt's authorization has exactly the receipt request as its
index.  This small theorem is the common-admission seam used by interpreters. -/
def CommittedTurn.authorizedExact
    {request : Request kind} {pre : Store Key Value}
    (commit : CommittedTurn portal authState request stateCommitment
      effectSemantics disclosurePolicy pre) :
    Authorized portal authState request :=
  commit.authorization

/-- No evidence constructor bypasses a rejecting policy portal, because policy
verification is the common final field of `Authorized`. -/
theorem noAuthorized_of_policyReject (request : Request kind)
    (rejects : ∀ witness,
      portal.verifyCommittedPolicy
        (authState.policyAddress request.policyId request.policyEpoch)
        request witness = false) :
    ¬ Nonempty (Authorized portal authState request) := by
  rintro ⟨authorized⟩
  have hfalse := rejects authorized.policyWitness
  have hverified := authorized.policyVerified
  rw [hfalse] at hverified
  exact Bool.false_ne_true hverified

/-- Therefore a policy-rejected request cannot have a committed receipt,
regardless of which evidence constructor the prover tries. -/
theorem noCommitted_of_policyReject (request : Request kind)
    (pre : Store Key Value)
    (rejects : ∀ witness,
      portal.verifyCommittedPolicy
        (authState.policyAddress request.policyId request.policyEpoch)
        request witness = false) :
    ¬ Nonempty (CommittedTurn portal authState request stateCommitment
      effectSemantics disclosurePolicy pre) := by
  rintro ⟨commit⟩
  exact noAuthorized_of_policyReject request rejects
    ⟨commit.authorization⟩

end TurnReceipt

/-! ## Projection into the accumulated algebraic nucleus -/

namespace CommittedTurn

variable
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {Key : Type uKey} {F : Type uValue} {Effect : Type uEffect}
    {Disclosure : Type uDisclosure}
    [Fintype Key] [DecidableEq Key] [Field F] [DecidableEq F]
    {stateCommitment : StateCommitment Key F}
    {effectSemantics : EffectSemantics Key F Effect}
    {disclosurePolicy : DisclosurePolicy Disclosure}
    {request : Request kind} {pre : Store Key F}

/-- Forget only the typed wrapper after it has been checked.  The resulting
claim is the exact fixed-shape language consumed by Selvage's accumulator. -/
def coreClaim
    (commit : CommittedTurn portal authState request stateCommitment
      effectSemantics disclosurePolicy pre) :
    SemanticReceiptClaim Key F :=
  ⟨ReceiptWitness.ofDelta commit.delta,
    ReceiptWitness.ofDelta_satisfies commit.delta⟩

theorem coreRelation
    (commit : CommittedTurn portal authState request stateCommitment
      effectSemantics disclosurePolicy pre) :
    SemanticReceiptRelation commit.coreClaim.witness.encode :=
  ⟨commit.coreClaim.witness, commit.coreClaim.valid, rfl⟩

/-- The projection does not invent a second transition word: it is
definitionally the canonical encoding of the carried `ReceiptDelta`. -/
theorem coreClaim_encode
    (commit : CommittedTurn portal authState request stateCommitment
      effectSemantics disclosurePolicy pre) :
    commit.coreClaim.witness.encode =
      (ReceiptWitness.ofDelta commit.delta).encode :=
  rfl

end CommittedTurn

/-! ## Concrete teeth -/

namespace Example

open Minidregg.Theory.TypedAuthorization

abbrev Key := Fin 2
abbrev F := ZMod 5

def stateCommitment : StateCommitment Key F where
  root := fun state => ⟨8 + (state 0).val + 10 * (state 1).val⟩

def before : Store Key F := fun _ => 0

def after : Store Key F
  | 0 => 3
  | 1 => 0

def delta : ReceiptDelta before after where
  touched := {0}
  frame := by
    intro key h
    fin_cases key <;> simp_all [before, after]

abbrev Effect := Nat
abbrev Disclosure := Nat

def effectSemantics : EffectSemantics Key F Effect where
  digest := fun effects => ⟨effects.sum⟩
  Realizes := by
    intro _ _ effects _ _ _
    exact effects = [6]

def disclosurePolicy : DisclosurePolicy Disclosure where
  Permitted := fun request disclosure => disclosure ≤ request.cost

/-- Same executable portal shape as the authorization example, but the final
policy gate binds the exact target value. -/
def targetPortal : Portal :=
  { demoPortal with
    verifyCommittedPolicy := fun _ _ request _ =>
      decide (request.target.value = demoTarget.value) }

def authorization : Authorized targetPortal demoState demoRequest where
  evidence := .proof () rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := by decide

def commit : CommittedTurn targetPortal demoState demoRequest stateCommitment
    effectSemantics disclosurePolicy before where
  authorization := authorization
  post := after
  delta := delta
  postStateRoot := stateCommitment.root after
  postRootBound := rfl
  effects := [6]
  effectsDigestBound := rfl
  effectsRealize := rfl
  disclosures := [2, 4]
  disclosuresPermitted := by
    intro disclosure h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> norm_num [disclosurePolicy, demoRequest]

def receipt : TurnReceipt targetPortal demoState .object Unit stateCommitment
    effectSemantics disclosurePolicy :=
  TurnReceipt.committed demoRequest before rfl commit

theorem receipt_core_is_real :
    SemanticReceiptRelation commit.coreClaim.witness.encode :=
  commit.coreRelation

/-- Target substitution cannot become a committed receipt by selecting another
evidence mode: every mode reaches the same target-bound policy check. -/
theorem retargeted_commit_rejected :
    ¬ Nonempty (CommittedTurn targetPortal demoState
      (demoRequest.retarget demoOtherTarget) stateCommitment
      effectSemantics disclosurePolicy before) := by
  apply TurnReceipt.noCommitted_of_policyReject
  intro witness
  simp [targetPortal, demoOtherTarget, demoTarget, Request.retarget]

end Example

end Minidregg.Assurance.SemanticTurnReceipt
