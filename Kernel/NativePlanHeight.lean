/-
An opt-in exact-height deadline for a canonical invocation signing plan.

The ordinary plan deliberately tolerates unrelated accepted turns. A caller
relying on a history observation must instead bind admission to that observed
height: first check the observation's world root equals this original plan's
world root, then pin the plan, sign its new headers, and submit it unchanged.
This helper is pure authoring, not a continuity check or an admission receipt.

NativeHost admission reconstructs request.height from the loaded durable
prefix; CredentialSignedEnvelopeController.prepare rejects a greater height.
NativeHost's invocation continuation passes that SAME loaded prefix to
DurableReceiverIO.receiveLoaded: one append against that head, with no rebase.
Thus a commit before admission expires the signature; a competing append after
admission contends. Retry must preserve the signed call; fresh signing requires
fresh continuity. Recorded exact invocation replay precedes deadline admission.
-/
import Kernel.NativeHost

namespace Minidregg.Kernel.NativePlanHeight

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

def pinHeader (height : Nat)
    (header : CredentialSignedEnvelopeController.SignedHeader) :
    CredentialSignedEnvelopeController.SignedHeader :=
  { header with validUntil := min header.validUntil height }

theorem pinHeader_deadline (height : Nat)
    (header : CredentialSignedEnvelopeController.SignedHeader) :
    (pinHeader height header).validUntil ≤ height := Nat.min_le_right _ _

theorem pinHeader_never_extends (height : Nat)
    (header : CredentialSignedEnvelopeController.SignedHeader) :
    (pinHeader height header).validUntil ≤ header.validUntil := Nat.min_le_left _ _

theorem pinHeader_only_deadline (height : Nat)
    (header : CredentialSignedEnvelopeController.SignedHeader) :
    { pinHeader height header with validUntil := header.validUntil } = header := by
  cases header
  rfl

theorem pinHeader_expired_after (height current : Nat)
    (header : CredentialSignedEnvelopeController.SignedHeader)
    (advanced : height < current) :
    (pinHeader height header).validUntil < current :=
  Nat.lt_of_le_of_lt (pinHeader_deadline height header) advanced

def pinSlot (height : Nat) (slot : SigningSlot) : Except String SigningSlot := do
  let some header := CredentialSignedEnvelopeController.headerCodec.decode slot.header
    | .error "noncanonical signing header"
  return { slot with header := (CredentialSignedEnvelopeController.headerCodec.encode
    (pinHeader height header)) }

/-- Reject non-invocations and malformed/empty plans; never change the signed
command, role ordering, subject, nonce, keys, footprint or request bytes. -/
def pin (plan : SigningPlan) : Except String SigningPlan := do
  let .invoke bytes := plan.finalizedDraft
    | .error "height pin requires an invocation plan"
  let some command := DeclaredResourceController.commandCodec.decode bytes
    | .error "noncanonical finalized invocation"
  let targetCount := command.targets.length
  let observeCount := if command.requiresObservation then targetCount else 0
  if command.targets.isEmpty || plan.slots.length != targetCount + observeCount + 1 then
    .error "invocation signing slots mismatch"
  else
    let slots ← plan.slots.mapM (pinSlot plan.height)
    return { plan with slots := slots }

/-- Invert one refusal guard without simplifying any symbolic codec terms. -/
private theorem refusal_else {E A : Type} {condition : Prop} [Decidable condition]
    {reason : E} {rest : Except E A} {value : A}
    (accepted : (if condition then Except.error reason else rest) = .ok value) :
    ¬ condition ∧ rest = .ok value := by
  by_cases selected : condition
  · rw [if_pos selected] at accepted
    contradiction
  · exact ⟨selected, by simpa only [if_neg selected] using accepted⟩

/-- This is the actual receiving controller, not a second deadline predicate.
Successful parsing/admission preparation entails its signed deadline check. -/
theorem receiving_prepare_deadline {NativeError : Type}
    (subject : Nat) (domain message state registry envelope : List UInt8)
    (prepared : CredentialSignedEnvelopeController.Prepared)
    (accepted : CredentialSignedEnvelopeController.prepare (NativeError := NativeError)
      subject domain message state registry envelope = .ok prepared) :
    prepared.state.height ≤ prepared.envelope.header.validUntil := by
  unfold CredentialSignedEnvelopeController.prepare at accepted
  cases stateDecoded : CredentialSignedEnvelopeController.stateCodec.decode state with
  | none => simp only [stateDecoded] at accepted; contradiction
  | some current =>
    simp only [stateDecoded] at accepted
    cases registryDecoded : CredentialSignedEnvelopeController.registryCodec.decode registry with
    | none => simp only [registryDecoded] at accepted; contradiction
    | some keys =>
      simp only [registryDecoded] at accepted
      cases envelopeDecoded : CredentialSignedEnvelopeController.envelopeCodec.decode envelope with
      | none => simp only [envelopeDecoded] at accepted; contradiction
      | some signed =>
        simp only [envelopeDecoded] at accepted
        -- Each inversion retains the original receiver expression. In
        -- particular, it never evaluates symbolic wire re-encoding guards.
        obtain ⟨_, accepted⟩ := refusal_else accepted
        obtain ⟨_, accepted⟩ := refusal_else accepted
        obtain ⟨_, accepted⟩ := refusal_else accepted
        obtain ⟨_, accepted⟩ := refusal_else accepted
        obtain ⟨_, accepted⟩ := refusal_else accepted
        obtain ⟨_, accepted⟩ := refusal_else accepted
        obtain ⟨_, accepted⟩ := refusal_else accepted
        obtain ⟨_, accepted⟩ := refusal_else accepted
        obtain ⟨_, accepted⟩ := refusal_else accepted
        obtain ⟨_, accepted⟩ := refusal_else accepted
        obtain ⟨_, accepted⟩ := refusal_else accepted
        obtain ⟨notExpired, accepted⟩ := refusal_else accepted
        obtain ⟨_, accepted⟩ := refusal_else accepted
        obtain ⟨_, accepted⟩ := refusal_else accepted
        obtain ⟨_, accepted⟩ := refusal_else accepted
        cases keyFound : keys.findKey signed.header.keyId with
        | none => simp only [keyFound] at accepted; contradiction
        | some key =>
          simp only [keyFound] at accepted
          obtain ⟨_, accepted⟩ := refusal_else accepted
          obtain ⟨_, accepted⟩ := refusal_else accepted
          obtain ⟨_, accepted⟩ := refusal_else accepted
          obtain ⟨_, accepted⟩ := refusal_else accepted
          cases accepted
          exact Nat.le_of_not_lt notExpired

/-- Exact historical replay takes the recorded branch before any new
preparation, key verification or deadline check. This is the actual invoked
receiver, so a lost acknowledgement does not require re-signing an old plan. -/
theorem recorded_replay_before_deadline {F : Type} [Field F] [DecidableEq F] {R : Type}
    (deployment : DeclaredResourceController.Deployment)
    (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : DeclaredResourceController.Ambient)
    (native : CredentialSignatureIO.NativeConfig)
    (durable : DeclaredResourceController.Durable)
    (directory : Option (CredentialAuthorityDomainReceiver.LoadedDirectory durable))
    (signed : DeclaredResourceController.SignedCommand)
    (command : DeclaredResourceController.Command)
    (record : DurableCommitProtocol.Intent Digest Digest StableNullifier ReplayEnvelope)
    (acceptedResult : {command : DeclaredResourceController.Command} →
      (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient durable command) →
      (shape : DeclaredResourceController.PhysicalShape prepared) →
      DeclaredResourceController.AcceptedInvocation prepared signed → IO R)
    (ordinaryResult : DeclaredResourceController.ReceiveResult → IO R)
    (decoded : DeclaredResourceController.commandCodec.decode signed.commandBytes = some command)
    (recorded : DeclaredResourceController.recordedInvocation deployment.domain profile.semantics
      command signed durable = .ok (some record)) :
    DeclaredResourceController.withAcceptedLoadedFrom deployment profile ambient native durable
      directory signed acceptedResult ordinaryResult = ordinaryResult (.replayed record) := by
  simp only [DeclaredResourceController.withAcceptedLoadedFrom, decoded, recorded]

end Minidregg.Kernel.NativePlanHeight
