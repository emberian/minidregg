/- Native source serialization seam for the physical private backend.
No cryptographic qualification or Host authority is added here. -/
import Compiler.PrivateSuccessorCustodyCodec
namespace Minidregg.Compiler.PrivateBackendBoundary
open Minidregg.Kernel.PrivateSuccessorCustody
open Minidregg.Compiler.PrivateSuccessorCustodyCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.DurableReceiverCodec
set_option autoImplicit false

structure ReservationRequest where
  correlation : CorrelationId
  generation : GenerationKey
  purpose : CorrelationPurpose

def requestStream : StreamCodec ReservationRequest :=
  StreamCodec.xmap
    (StreamCodec.product correlationStream (StreamCodec.product generationStream purposeStream))
    (fun request => (request.correlation, request.generation, request.purpose))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2⟩)
    (by intro request; cases request; rfl)

/-- Source-native complete descriptor bytes, not a digest-as-equality shortcut. -/
def recoveryBinding (descriptor : Descriptor) : List UInt8 :=
  descriptorStream.encode descriptor

/-- Physical receiver must receive this from the accepted source controller.
The record proves exact bytes and generation; it is not current release authority. -/
structure ExactDescriptorBinding (descriptor : Descriptor) where
  encoded : List UInt8
  generation : GenerationKey
  bytesExact : encoded = recoveryBinding descriptor
  generationExact : generation = descriptor.key

def bindDescriptor (descriptor : Descriptor) : ExactDescriptorBinding descriptor :=
  ⟨recoveryBinding descriptor, descriptor.key, rfl, rfl⟩

theorem descriptor_binding_preserves_native_successor
    {left right : Descriptor}
    (leftBinding : ExactDescriptorBinding left)
    (rightBinding : ExactDescriptorBinding right)
    (same : leftBinding.encoded = rightBinding.encoded) :
    left.exactSuccessor = right.exactSuccessor := by
  have encoded : descriptorStream.encode left = descriptorStream.encode right := by
    simpa only [leftBinding.bytesExact, rightBinding.bytesExact, recoveryBinding] using same
  exact congrArg Descriptor.exactSuccessor (descriptor_bytes_injective encoded)

theorem descriptor_binding_preserves_generation
    {left right : Descriptor}
    (leftBinding : ExactDescriptorBinding left)
    (rightBinding : ExactDescriptorBinding right)
    (same : leftBinding.encoded = rightBinding.encoded) :
    leftBinding.generation = rightBinding.generation := by
  have encoded : descriptorStream.encode left = descriptorStream.encode right := by
    simpa only [leftBinding.bytesExact, rightBinding.bytesExact, recoveryBinding] using same
  rw [leftBinding.generationExact, rightBinding.generationExact,
    descriptor_bytes_injective encoded]

/-- Source controller uses the same immutable descriptor's exact generation. -/
def reservationOfDescriptor (id : CorrelationId) (descriptor : Descriptor)
    (purpose : CorrelationPurpose) : ReservationRequest :=
  ⟨id, descriptor.key, purpose⟩

theorem request_bytes_injective {left right : ReservationRequest}
    (same : requestStream.encode left = requestStream.encode right) :
    left = right := by
  have leftRoundtrip := requestStream.decodePrefix_encode left []
  have rightRoundtrip := requestStream.decodePrefix_encode right []
  simp only [List.append_nil] at leftRoundtrip rightRoundtrip
  have decoded := congrArg requestStream.decodePrefix same
  rw [leftRoundtrip, rightRoundtrip] at decoded
  exact congrArg Prod.fst (Option.some.inj decoded)

theorem physical_relabel_cannot_reissue {journal next : Journal}
    {id : CorrelationId} {generation : GenerationKey} {purpose : CorrelationPurpose}
    (reserved : reserve journal id generation purpose = some next)
    (descriptor : Descriptor) (newPurpose : CorrelationPurpose) :
    reserve next id (reservationOfDescriptor id descriptor newPurpose).generation
      newPurpose = none :=
  reserve_never_reassigns reserved descriptor.key newPurpose

#assert_axioms descriptor_binding_preserves_native_successor
#assert_axioms descriptor_binding_preserves_generation
#assert_axioms request_bytes_injective
#assert_axioms physical_relabel_cannot_reissue
end Minidregg.Compiler.PrivateBackendBoundary
