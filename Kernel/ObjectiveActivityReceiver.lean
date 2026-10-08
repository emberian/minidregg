import Kernel.ObjectiveActivityReceiverCore
import Compiler.DurableReceiverIO

namespace Minidregg.Kernel.ObjectiveActivityReceiver

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ObjectiveBendDemandData (Data)
open Minidregg.Kernel.ObjectiveActivity (Config Publication Creation Birth Resolution Delivery TopUp
  Exhaustion Abandonment CreateRequest BirthRequest ResolveRequest DeliverRequest TopUpRequest
  ExhaustRequest AbandonRequest Answer)
open Minidregg.Kernel.ObjectiveKernelConfig (Ambient configOf)
open Minidregg.Compiler.ObjectiveInvocationClaim (Capacity capacityStream)
open Minidregg.Kernel.ObjectiveTariff (zeroCapacity)

set_option autoImplicit false


variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command}
variable [DecidableEq F] {ingress : DecodedIngress}

def receiveLoaded (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable)
    (bytes : List UInt8) : IO Result := do
  let some ingress := decodeIngress bytes
    | return .rejected .malformedIngress
  match replay deployment.domain profile.semantics durable ingress with
  | some (.ok (.exact prior disposition)) => return replayAnswer (.ok ()) (.exact prior disposition)
  | some (.ok (.retry prior disposition)) =>
    return replayAnswer (← verifyRetry deployment profile ambient native durable ingress)
      (.retry prior disposition)
  | some (.error _) => return .transactionConflict
  | none =>
    match ← admitDecodedNative deployment profile ambient durable native ingress with
    | .error reason => return .rejected reason
    | .ok verdict =>
      match ← DurableReceiverIO.receiveObjective transport durable (ObjectiveAdmissible.Proposal.activity verdict) with
      | .confirmed kind _ => return (match verdict with
        | .accepted _ => .confirmed kind (receipt deployment.domain profile.semantics ingress)
        | .failed failed => .charged kind (receipt deployment.domain profile.semantics ingress) failed.cause)
      | .rejected reason => return .durableRejected reason
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

/-- **The deployed receiver routes every recorded operation by replay kind.**
An exact replay returns the durable record's receipt and terminal disposition
unchanged, without running signature verification. A re-signed retry obtains
its answer from exactly the verdict produced by `verifyRetry`; in particular,
the receiver cannot return the recorded receipt before that verdict is known. -/
theorem receiveLoaded_recorded_routes
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable)
    {bytes : List UInt8} {ingress : DecodedIngress} {replayed : Replayed}
    (decoded : decodeIngress bytes = some ingress)
    (recorded : replay deployment.domain profile.semantics durable ingress =
      some (.ok replayed)) :
    match replayed with
    | .exact prior disposition =>
        receiveLoaded deployment profile ambient native transport durable bytes =
            pure (replayAnswer (.ok ()) (.exact prior disposition)) ∧
          AnswersRecorded prior disposition
            (replayAnswer (.ok ()) (.exact prior disposition))
    | .retry prior disposition =>
        receiveLoaded deployment profile ambient native transport durable bytes = (do
          let verified ← verifyRetry deployment profile ambient native durable ingress
          pure (replayAnswer verified (.retry prior disposition))) := by
  cases replayed with
  | exact prior disposition =>
      constructor
      · simp [receiveLoaded, decoded, recorded]
      · exact (replayAnswer_preserves_recorded_disposition prior disposition).1
  | retry prior disposition =>
      simp [receiveLoaded, decoded, recorded]

/-- **The deployed receiver's exact route returns the recorded disposition.**
This is stated over the receiver itself, rather than only over its pure answer
helper; the second conjunct exposes the durable disposition independently of
the equality describing the route. -/
theorem receiveLoaded_exact_returns_recorded_disposition
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable)
    {bytes : List UInt8} {ingress : DecodedIngress} {prior : Receipt}
    {disposition : RecordedDisposition}
    (decoded : decodeIngress bytes = some ingress)
    (recorded : replay deployment.domain profile.semantics durable ingress =
      some (.ok (.exact prior disposition))) :
    receiveLoaded deployment profile ambient native transport durable bytes =
        pure (replayAnswer (.ok ()) (.exact prior disposition)) ∧
      AnswersRecorded prior disposition
        (replayAnswer (.ok ()) (.exact prior disposition)) :=
  receiveLoaded_recorded_routes deployment profile ambient native transport durable decoded recorded

/-- **A failed current-key check on the deployed retry route returns no receipt.**
The result is the named rejection and cannot be either receipt-bearing result
constructor. Nothing reaches the durable transport on this recorded route. -/
theorem receiveLoaded_retry_verification_failure_no_receipt
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable)
    {bytes : List UInt8} {ingress : DecodedIngress} {prior : Receipt}
    {disposition : RecordedDisposition} {reason : Reject}
    (decoded : decodeIngress bytes = some ingress)
    (recorded : replay deployment.domain profile.semantics durable ingress =
      some (.ok (.retry prior disposition)))
    (unverified : verifyRetry deployment profile ambient native durable ingress =
      pure (.error reason)) :
    receiveLoaded deployment profile ambient native transport durable bytes =
      pure (.rejected reason) := by
  have routed := receiveLoaded_recorded_routes deployment profile ambient native transport durable
    decoded recorded
  rw [unverified] at routed
  simpa [replayAnswer, retryAnswer] using routed

/-- **A malformed request is rejected cheaply, with no state change and no charge**: bytes that
are not a canonical signed ingress are refused `malformedIngress` before anything is read,
decided or verified, and nothing reaches the durable layer. -/
theorem malformed_no_charge (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable) {bytes : List UInt8}
    (malformed : decodeIngress bytes = none) :
    receiveLoaded deployment profile ambient native transport durable bytes = pure (.rejected .malformedIngress) := by
  unfold receiveLoaded
  rw [malformed]

/-- **An unauthorized or unfunded request is refused with no state change and no charge**: a
gate refusal (authority, capability over the claimed outcome, funds) reaches neither the
decision, the signature check nor the durable layer. -/
theorem gate_refusal_no_charge (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable) {bytes : List UInt8}
    {ingress : DecodedIngress} {reason : Reject}
    (decoded : decodeIngress bytes = some ingress)
    (fresh : replay deployment.domain profile.semantics durable ingress = none)
    (refused : gate deployment profile ambient durable ingress.command ingress.ingress.outcome = .error reason) :
    receiveLoaded deployment profile ambient native transport durable bytes = pure (.rejected reason) := by
  unfold receiveLoaded
  rw [decoded]
  simp only [fresh]
  rw [gate_refusal_runs_nothing native refused]
  rfl

/-! ## Signing plan -/

/-- What a plan tells its signer a submission at this snapshot would commit: empty when the turn
is admitted; `charged failure: <reason>` when it would be a charged failure (the price of its
envelope, nothing else); `refused: <reason>` when it would be refused with no charge. -/
def planVerdict (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) : String :=
  let refusal (reason : Reject) : String :=
    if chargedCause reason && (failureRequest deployment.domain profile.semantics command).isSome then
      s!"charged failure: {repr reason}" else s!"refused: {repr reason}"
  match configOf deployment profile ambient with
  | .error reason => refusal (.kernel reason)
  | .ok config => match decideTurn config durable.snapshot ambient.height command with
    | .error reason => refusal reason
    | .ok decided => match ActivitySeatEnd.finish config durable.snapshot ambient.height decided with
      | .ok _ => ""
      | .error (.seats reason) => refusal (.seats reason)
      | .error (.kernel reason) => refusal (.kernel reason)

/-- The exact header the signer signs: the signed request over the planned outcome (`planOutcome`). -/
def signingHeader (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) :
    Except String CredentialSignedEnvelopeController.SignedHeader := do
  let some authority := loadDeployment deployment durable.snapshot
    | .error "authority unavailable"
  let outcome := planOutcome deployment profile ambient durable command
  let preRoot := durable.snapshot.model.roots ⟨(signedTarget deployment.domain command).2⟩
  (CredentialSignatureAdmission.signingHeader authority.snapshot
    (marker deployment.domain profile.semantics command)
    (signedRequest authority.snapshot profile.semantics ambient command preRoot outcome)).mapError
      (fun reason => s!"activity signer key: {repr reason}")

/-- What the decided turn returns to its signer, shown before it signs: an
invocation's root result, a delivered message's reply (their data bytes);
nothing for every other turn. It is
a function of the snapshot and the command, so every replay recomputes it. -/
def Decided.report {rootBytes : List UInt8 → Digest} {config : Config} {snapshot : DataSnapshot rootBytes}
    {height : Nat} {command : Command} : Decided config snapshot height command → List UInt8
  | .invoke _ invoked => dataBytes invoked.result
  | .deliverMessage _ delivered => match delivered.outcome with
    | .replied result _ => dataBytes result
    | .failed _ => []
  | _ => []

/-- The report of a command at a durable snapshot (empty when it is refused). -/
def planReport (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) : List UInt8 :=
  match configOf deployment profile ambient with
  | .ok config => match decideTurn config durable.snapshot ambient.height command with
    | .ok decided => decided.report
    | .error _ => []
  | .error _ => []

/-- The front-end work a decided turn drew from its meter (`ObjectiveCall.FrontEnd`): summed over
every replay, what an invocation's envelope must declare (`Invocation.frontEnd_within`), and the
largest delivery root load among its sends, what its postage must (`Deliverable.postagePays`).
Zero for a turn that replays nothing through a meter. -/
def Decided.frontEnd {rootBytes : List UInt8 → Digest} {config : Config} {snapshot : DataSnapshot rootBytes}
    {height : Nat} {command : Command} : Decided config snapshot height command → ObjectiveCall.FrontEnd
  | .invoke _ invoked => invoked.frontEnd
  | _ => ⟨0, 0, 0, 0⟩

/-- The front-end work a command drew at a durable snapshot: the decided turn's
(`Decided.frontEnd`), or, for a refused call tree, what it had drawn at its failure point
(`Reject.call`). A signer plans once over a generous affordable envelope, declares exactly this,
and plans again. -/
def planFrontEnd (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) : ObjectiveCall.FrontEnd :=
  match configOf deployment profile ambient with
  | .ok config => match decideTurn config durable.snapshot ambient.height command with
    | .ok decided => decided.frontEnd
    | .error (.call _ drawn) => drawn
    | .error _ => ⟨0, 0, 0, 0⟩
  | .error _ => ⟨0, 0, 0, 0⟩

structure SigningPlan where
  domain : Digest
  semantics : Digest
  commandBytes : List UInt8
  header : List UInt8
  /-- `Decided.report`: what the turn returns (an invocation's result). Not signed:
  the header binds the turn's posts, and the report is recomputed from them. -/
  report : List UInt8
  /-- The outcome the header signs (`planOutcome`); the assembled ingress carries it. -/
  outcome : Digest
  /-- `planVerdict` (UTF-8): empty, `charged failure: ...` or `refused: ...`. -/
  verdict : List UInt8
  /-- `planFrontEnd`: the source and typed-core bytes the turn's replays drew, and the largest
  delivery root load among its sends (what the postage declares). -/
  frontEnd : ObjectiveCall.FrontEnd
  deriving DecidableEq, Repr

def signingPlanStream : StreamCodec SigningPlan :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream (StreamCodec.product digestStream (StreamCodec.product bytesStream
        (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat StreamCodec.nat))))))))))
    (fun plan => (plan.domain, plan.semantics, plan.commandBytes, plan.header, plan.report, plan.outcome, plan.verdict,
      plan.frontEnd.source, plan.frontEnd.core, plan.frontEnd.postageSource, plan.frontEnd.postageCore))
    (fun (domain, semantics, command, header, report, outcome, verdict, source, core, postageSource, postageCore) =>
      ⟨domain, semantics, command, header, report, outcome, verdict, ⟨source, core, postageSource, postageCore⟩⟩)
    (by intro plan; cases plan; rfl)

/-- v4 carries the front-end work the turn drew, decided or refused (GPT-6 row E, the turn's meter); v3 carried
the signed outcome and the verdict; an earlier plan refuses to decode. -/
def signingPlanCodec : LawfulCodec SigningPlan :=
  ObjectiveActivityWire.framed "DREGG/OBJECTIVE/ACTIVITY/PLAN/v4".toUTF8.toList signingPlanStream

#assert_axioms command_roundtrip
#assert_axioms unfunded_not_gated
#assert_axioms gate_refusal_runs_nothing
#assert_axioms failed_charges_and_rolls_back
#assert_axioms malformed_no_charge
#assert_axioms gate_refusal_no_charge
#assert_axioms command_canonical
#assert_axioms intent_writes_activity_or_book
#assert_axioms intent_writes_lawful
#assert_axioms birth_requires_object_holder
#assert_axioms create_requires_object_holder
#assert_axioms native_birth_on_pinned_object
#assert_axioms stranger_birth_refused
#assert_axioms native_delivery_consumes_once
#assert_axioms native_delivery_fields_bind_checkpoint
#assert_axioms native_end_closes_held_seats
#assert_axioms gate_spent_refused
#assert_axioms command_v9_refuses
#assert_axioms rejectCodec_roundtrip
#assert_axioms rejectStream_prefix_roundtrip
#assert_axioms rejectCodec_injective
#assert_axioms rejectCodec_v1_refuses
#assert_axioms recordedFailureCodec_v1_refuses
#assert_axioms recordedDisposition_event
#assert_axioms recordedDisposition_failedEvent
#assert_axioms replay_invoke_recorded
#assert_axioms replay_exact
#assert_axioms replayAnswer_preserves_recorded_disposition
#assert_axioms replay_routes_recorded_disposition
#assert_axioms receiveLoaded_recorded_routes
#assert_axioms receiveLoaded_exact_returns_recorded_disposition
#assert_axioms receiveLoaded_retry_verification_failure_no_receipt
#assert_axioms callRefusal_encode_roundtrip
#assert_axioms callRefusalStream_prefix_roundtrip
#assert_axioms callRefusalStream_injective
#assert_axioms retry_unverified_refused

end Minidregg.Kernel.ObjectiveActivityReceiver
