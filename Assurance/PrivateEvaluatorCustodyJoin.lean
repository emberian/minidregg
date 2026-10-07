/- Join to the actual native accepted invocation, not a Boolean or digest
standing in for admission. This adds no authority and no audience release. -/
import Kernel.DeclaredResourceController
import Compiler.ObliviousEvaluator
import Compiler.PrivateSuccessorCustodyCodec

namespace Minidregg.Assurance.PrivateEvaluatorCustodyJoin
open Minidregg.Theory
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.PrivateSuccessorCustody
open Minidregg.Kernel.DurableReceiver
set_option autoImplicit false

variable {F : Type} [Field F] [DecidableEq F]
  {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
  {ambient : Ambient} {ground : Ground deployment} {command : Command}
  {prepared : PreparedInvocation deployment profile ambient ground command}
  {signed : SignedCommand}

/-- Holder-private material belongs to the full native intent. Caller-supplied
keys are forced to name its transaction, and candidate bytes retain the exact
signed command. This does not authorize releasing the descriptor publicly. -/
structure NativeBinding (accepted : AcceptedInvocation prepared signed)
    (shape : PhysicalShape prepared) (descriptor : Descriptor) : Prop where
  invocationExact : descriptor.key.invocation = (accepted.dataIntent shape).transactionId
  commandExact : descriptor.key.commandBytes = signed.commandBytes
  successorExact : descriptor.exactSuccessor = IntentRecord.ofIntent (accepted.dataIntent shape)

/-- Construction preserves source admission. Qualification of holder recovery
is deliberately a SEPARATE obligation, not manufactured by this constructor. -/
def ofAccepted (accepted : AcceptedInvocation prepared signed) (shape : PhysicalShape prepared)
    (attempt generation : Nat) (configuration : TypedAuthorization.Digest)
    (holders : List Nat) (threshold : Nat) (recoveryBytes : List UInt8) : Descriptor where
  key := ⟨(accepted.dataIntent shape).transactionId, signed.commandBytes,
    attempt, generation, configuration⟩
  exactSuccessor := IntentRecord.ofIntent (accepted.dataIntent shape)
  holderIds := holders
  threshold := threshold
  recoveryBytes := recoveryBytes

theorem ofAccepted_bound (accepted : AcceptedInvocation prepared signed)
    (shape : PhysicalShape prepared) (attempt generation : Nat)
    (configuration : TypedAuthorization.Digest) (holders : List Nat)
    (threshold : Nat) (recoveryBytes : List UInt8) :
    NativeBinding accepted shape
      (ofAccepted accepted shape attempt generation configuration holders threshold recoveryBytes) :=
  ⟨rfl, rfl, rfl⟩

theorem native_successor_rebinds {accepted : AcceptedInvocation prepared signed}
    {shape : PhysicalShape prepared} {descriptor : Descriptor}
    (binding : NativeBinding accepted shape descriptor) :
    descriptor.exactSuccessor.bind? ResourceBirthCodec.rootBytes =
      some (accepted.dataIntent shape) := by
  rw [binding.successorExact, IntentRecord.bind_ofIntent]

theorem native_binding_survives {accepted : AcceptedInvocation prepared signed}
    {shape : PhysicalShape prepared} {record next : Record} {event : Event}
    (binding : NativeBinding accepted shape record.descriptor)
    (step : transition record event = some next) :
    NativeBinding accepted shape next.descriptor := by
  rw [transition_exact_generation step]
  exact binding

/-- Replay/repair must retain all writes, read-only authority guards, nullifiers,
fees and the exact event. Equal commitment roots alone do not supply this law. -/
theorem native_successor_fields {accepted : AcceptedInvocation prepared signed}
    {shape : PhysicalShape prepared} {descriptor : Descriptor}
    (binding : NativeBinding accepted shape descriptor) :
    descriptor.exactSuccessor.writes = (accepted.dataIntent shape).writes ∧
    descriptor.exactSuccessor.readGuards = (accepted.dataIntent shape).readGuards ∧
    descriptor.exactSuccessor.nullifiers = (accepted.dataIntent shape).nullifiers ∧
    descriptor.exactSuccessor.exactCharge = (accepted.dataIntent shape).exactCharge ∧
    descriptor.exactSuccessor.event = (accepted.dataIntent shape).event := by
  rw [binding.successorExact]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

#assert_axioms ofAccepted_bound
#assert_axioms native_successor_rebinds
#assert_axioms native_binding_survives
#assert_axioms native_successor_fields

end Minidregg.Assurance.PrivateEvaluatorCustodyJoin
