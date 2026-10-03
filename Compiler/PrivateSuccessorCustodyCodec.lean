/- Exact persistence codecs for private custody. Canonical decoding protects
identity, NOT rollback freshness; the physical store must preserve Extends. -/
import Kernel.PrivateSuccessorCustody
import Compiler.DurableReceiverCodec

namespace Minidregg.Compiler.PrivateSuccessorCustodyCodec
open Minidregg.Kernel.PrivateSuccessorCustody
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.DurableReceiverCodec
set_option autoImplicit false

def generationStream : StreamCodec GenerationKey :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product bytesStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat digestStream))))
    (fun key => (key.invocation, key.commandBytes, key.attempt, key.generation, key.configuration))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2.1, tuple.2.2.2.2⟩)
    (by intro key; cases key; rfl)

def descriptorStream : StreamCodec Descriptor :=
  StreamCodec.xmap
    (StreamCodec.product generationStream (StreamCodec.product intentStream
      (StreamCodec.product (StreamCodec.list StreamCodec.nat)
        (StreamCodec.product StreamCodec.nat bytesStream))))
    (fun descriptor => (descriptor.key, descriptor.exactSuccessor, descriptor.holderIds,
      descriptor.threshold, descriptor.recoveryBytes))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2.1, tuple.2.2.2.2⟩)
    (by intro descriptor; cases descriptor; rfl)

def purposeCode : CorrelationPurpose → Nat
  | .triple => 0 | .agreementCoin => 1 | .holderOutputPad => 2 | .audienceReleasePad => 3

def purposeOf : Nat → CorrelationPurpose
  | 1 => .agreementCoin | 2 => .holderOutputPad | 3 => .audienceReleasePad | _ => .triple

def purposeStream : StreamCodec CorrelationPurpose :=
  StreamCodec.xmap StreamCodec.nat purposeCode purposeOf (by intro purpose; cases purpose <;> rfl)

def correlationStream : StreamCodec CorrelationId :=
  StreamCodec.xmap (StreamCodec.product digestStream StreamCodec.nat)
    (fun id => (id.pool, id.row)) (fun tuple => ⟨tuple.1, tuple.2⟩)
    (by intro id; cases id; rfl)

def consumptionStream : StreamCodec Consumption :=
  StreamCodec.xmap StreamCodec.nat
    (fun status => match status with | .reserved => 0 | .consumed => 1)
    (fun code => if code = 1 then .consumed else .reserved)
    (by intro status; cases status <;> rfl)

def allocationStream : StreamCodec Allocation :=
  StreamCodec.xmap
    (StreamCodec.product correlationStream (StreamCodec.product generationStream
      (StreamCodec.product purposeStream consumptionStream)))
    (fun allocation => (allocation.correlation, allocation.generation, allocation.purpose, allocation.state))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
    (by intro allocation; cases allocation; rfl)

def journalStream : StreamCodec Journal :=
  StreamCodec.xmap
    (StreamCodec.product (StreamCodec.list correlationStream) (StreamCodec.list allocationStream))
    (fun journal => (journal.spent, journal.allocations))
    (fun tuple => ⟨tuple.1, tuple.2⟩)
    (by intro journal; cases journal; rfl)

/-- Source-owned version/domain framing, not an unbound digest. -/
def journalFrame : List UInt8 := "DREGG.PRIVATE.CORRELATIONS".toUTF8.toList ++ [1]

def framedJournalStream : StreamCodec Journal :=
  StreamCodec.xmap (StreamCodec.product bytesStream journalStream)
    (fun journal => (journalFrame, journal)) Prod.snd (by intro journal; rfl)

def encodeJournal (journal : Journal) : List UInt8 := framedJournalStream.encode journal

def decodeJournal (bytes : List UInt8) : Option Journal :=
  match framedJournalStream.toLawful.decode bytes with
  | none => none
  | some journal => if encodeJournal journal = bytes then some journal else none

@[simp] theorem decode_encode_journal (journal : Journal) :
    decodeJournal (encodeJournal journal) = some journal := by
  have roundtrip := framedJournalStream.decodePrefix_encode journal []
  simp only [List.append_nil] at roundtrip
  simp [decodeJournal, encodeJournal, StreamCodec.toLawful, roundtrip]

theorem decode_journal_canonical {bytes : List UInt8} {journal : Journal}
    (accepted : decodeJournal bytes = some journal) : encodeJournal journal = bytes := by
  unfold decodeJournal at accepted
  cases decoded : framedJournalStream.toLawful.decode bytes with
  | none => simp [decoded] at accepted
  | some result =>
    simp only [decoded] at accepted
    split at accepted
    · cases accepted; assumption
    · cases accepted

/-- A trusted monotonic anchor must live outside the rollback domain of the
snapshot being restored. Passing the snapshot's own spent list is circular. -/
def restoreJournal (anchor : List CorrelationId) (bytes : List UInt8) : Option Journal :=
  match decodeJournal bytes with
  | none => none
  | some journal =>
    if anchor.all (fun id => decide (id ∈ journal.spent)) &&
        journal.allocations.all (fun allocation => decide (allocation.correlation ∈ journal.spent)) then
      some journal
    else none

theorem restore_preserves_anchor {anchor : List CorrelationId} {bytes : List UInt8}
    {journal : Journal} (accepted : restoreJournal anchor bytes = some journal) :
    ∀ id ∈ anchor, id ∈ journal.spent := by
  unfold restoreJournal at accepted
  cases decoded : decodeJournal bytes with
  | none => simp [decoded] at accepted
  | some result =>
    simp only [decoded] at accepted
    split at accepted
    · rename_i checked
      cases accepted
      have checks : anchor.all (fun id => decide (id ∈ journal.spent)) = true ∧
          journal.allocations.all (fun allocation => decide (allocation.correlation ∈ journal.spent)) = true := by
        simpa only [Bool.and_eq_true] using checked
      simpa using checks.1
    · cases accepted

/-- Exact generation, transcript, and monotonic-anchor checking precede the
physical store's atomic durable append. Only AFTER persistence may a caller
release the corresponding secret correlation. This function itself does no IO. -/
def reserveEncoded (anchor : List CorrelationId) (bytes : List UInt8)
    (id : CorrelationId) (generation : GenerationKey) (purpose : CorrelationPurpose) :
    Option (List UInt8) := do
  let journal ← restoreJournal anchor bytes
  let next ← reserve journal id generation purpose
  pure (encodeJournal next)

/-- Equal canonical bytes imply equal complete descriptor, including the
native successor, without assuming any hash collision resistance. -/
theorem descriptor_bytes_injective {left right : Descriptor}
    (same : descriptorStream.encode left = descriptorStream.encode right) : left = right := by
  have leftRoundtrip := descriptorStream.decodePrefix_encode left []
  have rightRoundtrip := descriptorStream.decodePrefix_encode right []
  simp only [List.append_nil] at leftRoundtrip rightRoundtrip
  have decoded := congrArg descriptorStream.decodePrefix same
  rw [leftRoundtrip, rightRoundtrip] at decoded
  exact congrArg Prod.fst (Option.some.inj decoded)

#assert_axioms decode_encode_journal
#assert_axioms decode_journal_canonical
#assert_axioms descriptor_bytes_injective
#assert_axioms restore_preserves_anchor

end Minidregg.Compiler.PrivateSuccessorCustodyCodec
