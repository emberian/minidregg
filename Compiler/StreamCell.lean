/-
# Compiler.StreamCell -- the stream cell: a dense, append-only sequence log

A stream is one `Store` over `layout`: one append-only namespace keyed by the
sequence number `1, 2, …`, each key holding one `StreamRecord`.  An append is
exactly one `Op.allocate` at `nextSeq` (the support's size plus one); the
registry's `StreamLaw` keeps the keys dense, so `nextSeq` is always absent and
every earlier key is present.  A present key is never overwritten or freed
(`append_only`, the store's discipline).

The cell holds the entry's *digest*; the payload bytes stay in the signed
command (`Append.payload`) that the accepted journal already keeps.  The
command never names a sequence number or a digest: the receiver derives both.
-/
import Compiler.StoreCodec
import Compiler.TypedAuthorizationRequestCodec

namespace Minidregg.Compiler.StreamCell

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.StoreCodec
open Minidregg.Theory
open Minidregg.Theory.Store
open Minidregg.Theory.CellState
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

def maxTopicBytes : Nat := 64
/-- Payloads ride in the signed command; the cell stores only their digest. -/
def maxPayloadBytes : Nat := 4096
/-- The append payload's declaration version (`Target.schemaVersion`). -/
def commandVersion : Nat := 1

/-- One stream entry as the cell stores it. `ref` names another entry by
`(cell, sequence)`; `recipient` addresses a subject. -/
structure StreamEntry where
  topic : List UInt8
  payloadDigest : Digest
  recipient : Option SubjectId
  ref : Option (Nat × Nat)
  deriving DecidableEq, Repr

/-- One sequence position: the entry plus what the receiver derived — the
signing subject, the admission height and the exact transaction id. -/
structure StreamRecord where
  author : SubjectId
  height : Nat
  transaction : Digest
  entry : StreamEntry
  deriving DecidableEq, Repr

/-- The append request as the command carries it: the payload BYTES, never a
digest, so the stored digest is always of bytes the signer actually sent. -/
structure Append where
  topic : List UInt8
  payload : List UInt8
  recipient : Option SubjectId
  ref : Option (Nat × Nat)
  deriving DecidableEq, Repr

def payloadCustomization : List UInt8 := "DREGG.STREAM.PAYLOAD/v1".toUTF8.toList

def payloadDigest (payload : List UInt8) : Digest :=
  (Sp800185Cshake256.hash payloadCustomization (bytesStream.encode payload)).digest

def Append.entry (request : Append) : StreamEntry :=
  ⟨request.topic, payloadDigest request.payload, request.recipient, request.ref⟩

def Append.WellFormed (request : Append) : Prop :=
  request.topic.length ≤ maxTopicBytes ∧ request.payload.length ≤ maxPayloadBytes

instance (request : Append) : Decidable request.WellFormed := by
  unfold Append.WellFormed; infer_instance

/-! ## Codecs -/

def refStream : StreamCodec (Nat × Nat) := StreamCodec.product StreamCodec.nat StreamCodec.nat

def entryStream : StreamCodec StreamEntry :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product digestStream
      (StreamCodec.product (StreamCodec.option TypedAuthorizationRequestCodec.subjectIdStream)
        (StreamCodec.option refStream))))
    (fun entry => (entry.topic, entry.payloadDigest, entry.recipient, entry.ref))
    (fun (topic, digest, recipient, ref) => ⟨topic, digest, recipient, ref⟩)
    (by intro entry; cases entry; rfl)

def recordStream : StreamCodec StreamRecord :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream entryStream)))
    (fun record => (record.author, record.height, record.transaction, record.entry))
    (fun (author, height, transaction, entry) => ⟨author, height, transaction, entry⟩)
    (by intro record; cases record; rfl)

def appendStream : StreamCodec Append :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.product (StreamCodec.option TypedAuthorizationRequestCodec.subjectIdStream)
        (StreamCodec.option refStream))))
    (fun request => (request.topic, request.payload, request.recipient, request.ref))
    (fun (topic, payload, recipient, ref) => ⟨topic, payload, recipient, ref⟩)
    (by intro request; cases request; rfl)

/-! ## Layout and wire -/

inductive Namespace where
  | entries
  deriving DecidableEq, Repr

abbrev layout : Layout.{0, 0, 0} where
  Namespace := Namespace
  Key := fun _ => Nat
  Value := fun _ => StreamRecord
  discipline := fun _ => .appendOnly

def namespaceStream : StreamCodec layout.Namespace where
  encode _ := []
  decodePrefix bytes := some (.entries, bytes)
  decodePrefix_encode := by intro space suffix; cases space; rfl

def wire : Wire layout where
  name := "minidregg/stream/v1"
  namespaces := [.entries]
  namespaces_complete := by intro space; cases space; simp
  namespaceStream := namespaceStream
  keyStream := fun _ => StreamCodec.nat
  valueStream := fun _ => recordStream
  keyCodecId := fun _ => "sequence/nat"
  valueCodecId := fun _ => "stream-record/v1"

def materializer : Materializer layout Digest := StoreCodec.materializer wire

/-! ## Sequence positions -/

def address (sequence : Nat) : Address layout := ⟨.entries, sequence⟩

/-- The next sequence position: one past the number of recorded entries. -/
def nextSeq (store : Store layout) : Nat := store.support.card + 1

/-- The one append operation: allocate `record` at `nextSeq`. -/
def appendOp (store : Store layout) (record : StreamRecord) : Op layout :=
  .allocate .entries (nextSeq store) record

/-- Keys are exactly `1 … card`. -/
def Dense (store : Store layout) : Prop :=
  ∀ a ∈ store.support, 1 ≤ a.2 ∧ a.2 ≤ store.support.card

def TopicsBounded (store : Store layout) : Prop :=
  ∀ a ∈ store.support, ((store a).map fun record => record.entry.topic.length).getD 0 ≤ maxTopicBytes

/-- The registry law of a stream cell. -/
def StreamLaw (store : Store layout) : Prop := Dense store ∧ TopicsBounded store

instance streamLawDecidable (store : Store layout) : Decidable (StreamLaw store) := by
  unfold StreamLaw Dense TopicsBounded; infer_instance

theorem empty_lawful : StreamLaw 0 := by
  constructor <;> intro a member <;> simp at member

/-- In a dense stream the next position is absent. -/
theorem nextSeq_fresh (store : Store layout) (dense : Dense store) :
    store (address (nextSeq store)) = none := by
  by_contra present
  have member : address (nextSeq store) ∈ store.support := DFinsupp.mem_support_iff.mpr present
  have bound := (dense _ member).2
  simp [address, nextSeq] at bound

theorem appendOp_enabled (store : Store layout) (dense : Dense store) (record : StreamRecord) :
    (appendOp store record).Enabled store :=
  ⟨by simp, nextSeq_fresh store dense⟩

/-- **`append_only`.** No valid patch overwrites or frees a present sequence
key: the namespace is append-only, so a present entry survives every
admitted patch unchanged. -/
theorem append_only (store : Store layout) (patch : Patch layout) (sequence : Nat)
    (record : StreamRecord) (valid : Patch.ValidFrom store patch)
    (present : store (address sequence) = some record) :
    Patch.run store patch (address sequence) = some record :=
  Patch.appendOnly_present_preserved store patch (address sequence) record valid rfl present

/-- After an append lands, an allocation planned at the same position is not
enabled: two appends planned at one `nextSeq` cannot both commit. -/
theorem same_position_refused (store : Store layout) (first second : StreamRecord) :
    ¬ (Op.allocate (L := layout) .entries (nextSeq store) second).Enabled
        ((appendOp store first).apply store) := by
  intro enabled
  have fresh := enabled.2
  simp [Store.Fresh, appendOp, Op.apply] at fresh

/-- The append's access footprint is the one next-sequence address. -/
theorem appendOp_footprint (store : Store layout) (record : StreamRecord) :
    Patch.accessFootprint [appendOp store record] = {address (nextSeq store)} := by
  simp [Patch.accessFootprint, appendOp, Op.address, address]

/-! ## `tail`: entries from a position -/

/-- At most `count` entries at positions `from, from+1, …`, in sequence order. -/
def tail (store : Store layout) (start count : Nat) : List (Nat × StreamRecord) :=
  (List.range' start count).filterMap fun sequence =>
    (store (address sequence)).map fun record => (sequence, record)

/-- `tail` returns exactly the recorded entries in the window, with their
recorded values. -/
theorem mem_tail (store : Store layout) (start count sequence : Nat) (record : StreamRecord) :
    (sequence, record) ∈ tail store start count ↔
      start ≤ sequence ∧ sequence < start + count ∧ store (address sequence) = some record := by
  simp only [tail, List.mem_filterMap, List.mem_range'_1]
  constructor
  · rintro ⟨k, ⟨lo, hi⟩, found⟩
    cases h : store (address k) with
    | none => simp [h] at found
    | some r =>
        simp [h] at found
        obtain ⟨rfl, rfl⟩ := found
        exact ⟨lo, hi, h⟩
  · rintro ⟨lo, hi, found⟩
    exact ⟨sequence, ⟨lo, hi⟩, by simp [found]⟩

/-- info: 'Minidregg.Compiler.StreamCell.append_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms append_only
/-- info: 'Minidregg.Compiler.StreamCell.nextSeq_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nextSeq_fresh
/-- info: 'Minidregg.Compiler.StreamCell.same_position_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms same_position_refused
/-- info: 'Minidregg.Compiler.StreamCell.appendOp_footprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms appendOp_footprint
/-- info: 'Minidregg.Compiler.StreamCell.mem_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mem_tail

end Minidregg.Compiler.StreamCell
