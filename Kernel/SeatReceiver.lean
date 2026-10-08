import Kernel.SeatReceiverCore
import Compiler.DurableReceiverIO

namespace Minidregg.Kernel.SeatReceiver

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
open Minidregg.Kernel.ObjectiveActivity (Config)
open Minidregg.Kernel.ObjectiveKernelConfig (Ambient configOf)
open Minidregg.Kernel.SeatStore (Turn Request Decided decideTurn turnStream transactionOf)

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
  | some (.ok prior) => return .confirmed .replayed prior
  | some (.error _) => return .transactionConflict
  | none =>
    match ← admitDecodedNative deployment profile ambient durable native ingress with
    | .error reason => return .rejected reason
    | .ok accepted =>
      match ← DurableReceiverIO.receiveObjective transport durable (ObjectiveAdmissible.Proposal.seat accepted) with
      | .confirmed kind _ => return .confirmed kind (receipt deployment.domain profile.semantics ingress)
      | .rejected reason => return .durableRejected reason
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

/-! ## Signing plan -/

/-- The exact header the signer signs. When the kernel refuses the command, the
header is built over the empty outcome and the submission is refused with the
named reason. -/
def signingHeader (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) :
    Except String CredentialSignedEnvelopeController.SignedHeader := do
  let some authority := loadDeployment deployment durable.snapshot
    | .error "authority unavailable"
  let outcome := match configOf deployment profile ambient with
    | .ok config => match decideTurn config durable.snapshot ambient.height command.request with
      | .ok decided => outcomeDigest decided.posts
      | .error _ => outcomeDigest []
    | .error _ => outcomeDigest []
  let preRoot := durable.snapshot.model.roots ⟨(signedTarget deployment.domain command).2⟩
  (CredentialSignatureAdmission.signingHeader authority.snapshot
    (marker deployment.domain profile.semantics command)
    (signedRequest authority.snapshot profile.semantics ambient command preRoot outcome)).mapError
      (fun reason => s!"seat signer key: {repr reason}")

/-- What the planner says the kernel would do: the decision, or its refusal. -/
def planVerdict (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) : String :=
  match configOf deployment profile ambient with
  | .error reason => s!"refused: {repr reason}"
  | .ok config => match decideTurn config durable.snapshot ambient.height command.request with
    | .ok decided => s!"decided: {decided.posts.length} posts"
    | .error reason => s!"refused: {repr reason}"

structure SigningPlan where
  domain : Digest
  semantics : Digest
  commandBytes : List UInt8
  header : List UInt8
  deriving DecidableEq, Repr

def signingPlanStream : StreamCodec SigningPlan :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product bytesStream bytesStream)))
    (fun plan => (plan.domain, plan.semantics, plan.commandBytes, plan.header))
    (fun (domain, semantics, command, header) => ⟨domain, semantics, command, header⟩)
    (by intro plan; cases plan; rfl)

def signingPlanCodec : LawfulCodec SigningPlan :=
  ObjectiveActivityWire.framed "DREGG/SEAT/PLAN/v1".toUTF8.toList signingPlanStream

#assert_axioms command_roundtrip command_canonical native_turn_is_kernel_turn native_invariant_preserved
  native_turn_conserves intent_writes_seat_or_book intent_writes_lawful offer_requires_account_holder
  reallocate_requires_instance_holder exit_requires_offerer_or_deadline native_offer_spends_invitation_once

end Minidregg.Kernel.SeatReceiver
