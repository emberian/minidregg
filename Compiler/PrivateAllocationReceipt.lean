/- Claimed physical allocation bytes and the proof-relevant readback boundary.
A decoded claim is not an actual Host effect or private successor qualification. -/
import Compiler.PrivateBackendBoundary
namespace Minidregg.Compiler.PrivateAllocationReceipt
open Minidregg.Kernel.PrivateSuccessorCustody
open Minidregg.Compiler.PrivateSuccessorCustodyCodec
open Minidregg.Compiler.PrivateBackendBoundary
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.DurableReceiverCodec
set_option autoImplicit false
structure AllocationReceipt where
  requestBytes : List UInt8
  descriptorBytes : List UInt8
  journalBytes : List UInt8
  rowCommitment : List UInt8

def receiptFrame : List UInt8 := "DREGG.PRIVATE.ALLOCATION".toUTF8.toList ++ [1]
def receiptStream : StreamCodec AllocationReceipt :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream (StreamCodec.product bytesStream bytesStream))))
    (fun receipt => (receiptFrame, receipt.requestBytes, receipt.descriptorBytes,
      receipt.journalBytes, receipt.rowCommitment))
    (fun tuple => ⟨tuple.2.1, tuple.2.2.1, tuple.2.2.2.1, tuple.2.2.2.2⟩)
    (by intro receipt; cases receipt; rfl)

structure ReceiptBinding (descriptor : Descriptor) (receipt : AllocationReceipt) where
  request : ReservationRequest
  journal : Journal
  requestExact : receipt.requestBytes = requestStream.encode request
  descriptorExact : receipt.descriptorBytes = recoveryBinding descriptor
  generationExact : request.generation = descriptor.key
  journalDecoded : decodeJournal receipt.journalBytes = some journal
  rowCommitmentLength : receipt.rowCommitment.length = 32
  spent : request.correlation ∈ journal.spent
  allocationExact :
    ⟨request.correlation, request.generation, request.purpose, .reserved⟩ ∈ journal.allocations ∨
    ⟨request.correlation, request.generation, request.purpose, .consumed⟩ ∈ journal.allocations

/-- actualReadback belongs to the actual source-owned Host implementation.
Canonical bytes alone cannot supply this field. The anchor must be independent
of the snapshot's rollback authority. This token supplies no sharing theorem. -/
structure VerifiedAnchoredAllocation (descriptor : Descriptor) (receipt : AllocationReceipt)
    (actualReadback : AllocationReceipt → Prop) : Prop where
  binding : Nonempty (ReceiptBinding descriptor receipt)
  physical : actualReadback receipt

/-- Terminal source promise requires physical allocation AND actual private
successor qualification. An allocation-only first source CAS stays undecided. -/
structure SourcePromiseCustody (descriptor : Descriptor) (receipt : AllocationReceipt)
    (corrupt : Nat → Bool) (privateRecovery : Descriptor → Prop)
    (actualReadback : AllocationReceipt → Prop) : Prop where
  allocated : VerifiedAnchoredAllocation descriptor receipt actualReadback
  successorQualified : Qualified descriptor corrupt privateRecovery

theorem receipt_spent_cannot_reissue {descriptor : Descriptor} {receipt : AllocationReceipt}
    (binding : ReceiptBinding descriptor receipt)
    (otherGeneration : GenerationKey) (otherPurpose : CorrelationPurpose) :
    reserve binding.journal binding.request.correlation otherGeneration otherPurpose = none := by
  simp [reserve, binding.spent]

theorem equal_receipt_descriptor_preserves_exact_successor
    {left right : Descriptor} {receipt : AllocationReceipt}
    (leftBinding : ReceiptBinding left receipt) (rightBinding : ReceiptBinding right receipt) :
    left.exactSuccessor = right.exactSuccessor := by
  have same : descriptorStream.encode left = descriptorStream.encode right := by
    calc
      descriptorStream.encode left = receipt.descriptorBytes := leftBinding.descriptorExact.symm
      _ = descriptorStream.encode right := rightBinding.descriptorExact
  exact congrArg Descriptor.exactSuccessor (descriptor_bytes_injective same)

theorem source_promise_retains_actual_recovery
    {descriptor : Descriptor} {receipt : AllocationReceipt}
    {corrupt : Nat → Bool} {privateRecovery : Descriptor → Prop}
    {actualReadback : AllocationReceipt → Prop}
    (ready : SourcePromiseCustody descriptor receipt corrupt privateRecovery actualReadback) :
    privateRecovery descriptor := ready.successorQualified.recoverable

#assert_axioms receipt_spent_cannot_reissue
#assert_axioms equal_receipt_descriptor_preserves_exact_successor
#assert_axioms source_promise_retains_actual_recovery

/-- Bounded source projection. Full historical/live journal stays in the
physical verifier's private evidence and cannot inflate a prepaid YES record. -/
structure SourceAllocationReceipt where
  requestBytes : List UInt8
  descriptorBytes : List UInt8
  rowCommitment : List UInt8
  originalPrefixDigest : List UInt8
  originalPrefixCount : Nat

def sourceReceiptFrame : List UInt8 :=
  "DREGG.PRIVATE.ALLOCATION.SOURCE".toUTF8.toList ++ [1]

def sourceReceiptStream : StreamCodec SourceAllocationReceipt :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream (StreamCodec.product bytesStream
        (StreamCodec.product bytesStream StreamCodec.nat)))))
    (fun receipt => (sourceReceiptFrame, receipt.requestBytes, receipt.descriptorBytes,
      receipt.rowCommitment, receipt.originalPrefixDigest, receipt.originalPrefixCount))
    (fun tuple => ⟨tuple.2.1, tuple.2.2.1, tuple.2.2.2.1,
      tuple.2.2.2.2.1, tuple.2.2.2.2.2⟩)
    (by intro receipt; cases receipt; rfl)

structure SourceReceiptBinding (descriptor : Descriptor) (receipt : SourceAllocationReceipt) where
  request : ReservationRequest
  originalJournal : Journal
  requestExact : receipt.requestBytes = requestStream.encode request
  descriptorExact : receipt.descriptorBytes = recoveryBinding descriptor
  generationExact : request.generation = descriptor.key
  rowCommitmentLength : receipt.rowCommitment.length = 32
  prefixDigestLength : receipt.originalPrefixDigest.length = 32
  countExact : receipt.originalPrefixCount = originalJournal.allocations.length
  countPositive : 0 < receipt.originalPrefixCount
  countBounded : receipt.originalPrefixCount < 2^64
  spent : request.correlation ∈ originalJournal.spent
  allocationExact :
    ⟨request.correlation, request.generation, request.purpose, .reserved⟩ ∈ originalJournal.allocations

/-- actualReadback must authenticate the ORIGINAL prefix, digest and exact
allocation, and prove retention in the current independent protected anchor.
The codec, an unkeyed checksum, and a different Unix pathname do not do that. -/
structure VerifiedSourceAllocation (descriptor : Descriptor) (receipt : SourceAllocationReceipt)
    (actualReadback : SourceAllocationReceipt → Journal → Prop) : Prop where
  physical : ∃ binding : SourceReceiptBinding descriptor receipt,
    actualReadback receipt binding.originalJournal

def fitsSourceEnvelope (receipt : SourceAllocationReceipt) (preplannedBytes : Nat) : Bool :=
  decide ((sourceReceiptStream.encode receipt).length ≤ preplannedBytes)

theorem checked_source_receipt_fits_preplanned_envelope
    (receipt : SourceAllocationReceipt) (preplannedBytes : Nat)
    (checked : fitsSourceEnvelope receipt preplannedBytes = true) :
    (sourceReceiptStream.encode receipt).length ≤ preplannedBytes := by
  unfold fitsSourceEnvelope at checked
  exact of_decide_eq_true checked

theorem source_receipt_retention_forbids_reissue
    {descriptor : Descriptor} {receipt : SourceAllocationReceipt}
    (binding : SourceReceiptBinding descriptor receipt)
    (live : Journal) (retains : Extends live binding.originalJournal)
    (newGeneration : GenerationKey) (newPurpose : CorrelationPurpose) :
    reserve live binding.request.correlation newGeneration newPurpose = none := by
  have stillSpent := retains binding.request.correlation binding.spent
  simp [reserve, stillSpent]

#assert_axioms checked_source_receipt_fits_preplanned_envelope
#assert_axioms source_receipt_retention_forbids_reissue

/-- The bounded replicated source bundle still requires real qualified sharing;
a replica-local physical receipt cannot by itself supply that common evidence. -/
structure BoundedSourcePromiseCustody (descriptor : Descriptor)
    (receipt : SourceAllocationReceipt) (preplannedBytes : Nat)
    (corrupt : Nat → Bool) (privateRecovery : Descriptor → Prop)
    (actualReadback : SourceAllocationReceipt → Journal → Prop) : Prop where
  allocated : VerifiedSourceAllocation descriptor receipt actualReadback
  envelopeBound : fitsSourceEnvelope receipt preplannedBytes = true
  successorQualified : Qualified descriptor corrupt privateRecovery

theorem bounded_source_promise_retains_actual_recovery
    {descriptor : Descriptor} {receipt : SourceAllocationReceipt} {preplannedBytes : Nat}
    {corrupt : Nat → Bool} {privateRecovery : Descriptor → Prop}
    {actualReadback : SourceAllocationReceipt → Journal → Prop}
    (ready : BoundedSourcePromiseCustody descriptor receipt preplannedBytes
      corrupt privateRecovery actualReadback) : privateRecovery descriptor :=
  ready.successorQualified.recoverable

#assert_axioms bounded_source_promise_retains_actual_recovery

end Minidregg.Compiler.PrivateAllocationReceipt
