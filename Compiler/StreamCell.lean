/-
# Compiler.StreamCell -- a stream: one head cell plus one cell per entry

A stream is physically TWO kinds of cell, so that an append writes a bounded
number of bytes however long the stream already is:

| cell                       | namespace | key    | value                     | discipline  |
|----------------------------|-----------|--------|---------------------------|-------------|
| head (kind `stream`)       | `head`    | `Unit` | `Head {binding, count, tail}` | RAM     |
| entry (kind `streamEntry`) | `entry`   | `Unit` | `Entry {head, sequence, parent, record}` | append-only |

* The head holds the number of recorded entries and the key of the last one
  (`tail`).  It never holds an entry.
* Entry `n` of the stream whose head is cell `h` lives at `entryCellId h n`.
  It names its head and position (the registry law checks the cell id against
  them), the key of the entry before it (`parent`, the head's `tail` when it
  was appended) and the record.
* An append is one guarded write of the head (`headWriteOp`, footprint the one
  head address, `headWrite_footprint`) and one fresh entry cell.  Neither
  depends on any earlier entry: the next position and the parent come from the
  head alone (`appendEntry`, `Head.append`).

The previous shape (one `minidregg/stream/v1` store cell holding every entry,
rewritten whole on each append) is gone; its schema reference `91012/1` and wire
name no longer decode (`CanonicalCellRegistry`, schema `91012/2`).

The cell holds the entry's *digest*; the payload bytes stay in the signed
command that the accepted journal already keeps.  The command never names a
digest: the receiver derives it.

A head's `binding` says which writer family appends to it: a room stream born by
resource birth (`room`; its law is the author law installed at birth) or a
fleet topic (`topic stream`; its cell id is derived from `stream`, and only the
fleet receiver appends).  Neither family can append to the other's head.
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

/-- Which writer family appends to a stream. -/
inductive Binding where
  /-- Born by resource birth (`create --storage stream`); appended by
  resource-transaction `append` targets under the installed author law. -/
  | room
  /-- A fleet topic: the head's cell id is `topicHeadCellId stream`, and only
  the fleet receiver appends. -/
  | topic (stream : Digest)
  deriving DecidableEq, Repr

/-- The head: how many entries are recorded and the key of the last. -/
structure Head where
  binding : Binding
  count : Nat
  tail : Option Digest
  deriving DecidableEq, Repr

/-- One entry cell's value. -/
structure Entry where
  head : Nat
  sequence : Nat
  parent : Option Digest
  record : StreamRecord
  deriving DecidableEq, Repr

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

def bindingStream : StreamCodec Binding :=
  StreamCodec.xmap (StreamCodec.option digestStream)
    (fun | .room => none | .topic stream => some stream)
    (fun | none => .room | some stream => .topic stream)
    (by intro binding; cases binding <;> rfl)

def headStream : StreamCodec Head :=
  StreamCodec.xmap
    (StreamCodec.product bindingStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.option digestStream)))
    (fun head => (head.binding, head.count, head.tail))
    (fun (binding, count, tail) => ⟨binding, count, tail⟩)
    (by intro head; cases head; rfl)

def streamEntryStream : StreamCodec Entry :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product (StreamCodec.option digestStream) recordStream)))
    (fun entry => (entry.head, entry.sequence, entry.parent, entry.record))
    (fun (head, sequence, parent, record) => ⟨head, sequence, parent, record⟩)
    (by intro entry; cases entry; rfl)

/-! ## Derived identities -/

private def cshake (customization : String) (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash customization.toUTF8.toList bytes).digest

/-- The key of one entry: a digest of its whole value, so it binds the head,
the position, the parent and the record. The next entry's `parent` is it. -/
def entryKey (entry : Entry) : Digest :=
  cshake "DREGG.STREAM.ENTRY/v1" (streamEntryStream.encode entry)

/-- The cell of entry `sequence` of the stream whose head is cell `head`. -/
def entryCellId (head sequence : Nat) : Nat :=
  (cshake "DREGG.STREAM.ENTRY-CELL/v1"
    ((StreamCodec.product StreamCodec.nat StreamCodec.nat).encode (head, sequence))).value

/-- The head cell of a fleet topic stream. -/
def topicHeadCellId (stream : Digest) : Nat :=
  (cshake "DREGG.STREAM.TOPIC-HEAD/v1" (digestStream.encode stream)).value

/-! ## The head cell: layout and wire -/

inductive HeadNamespace where
  | head
  deriving DecidableEq, Repr

abbrev headLayout : Layout.{0, 0, 0} where
  Namespace := HeadNamespace
  Key := fun _ => Unit
  Value := fun _ => Head
  discipline := fun _ => .ram

def headNamespaceStream : StreamCodec headLayout.Namespace where
  encode _ := []
  decodePrefix bytes := some (.head, bytes)
  decodePrefix_encode := by intro space suffix; cases space; rfl

def headWire : Wire headLayout where
  name := "minidregg/stream-head/v1"
  namespaces := [.head]
  namespaces_complete := by intro space; cases space; simp
  namespaceStream := headNamespaceStream
  keyStream := fun _ => unitStream
  valueStream := fun _ => headStream
  keyCodecId := fun _ => "unit"
  valueCodecId := fun _ => "stream-head/v1"

def headMaterializer : Materializer headLayout Digest := StoreCodec.materializer headWire

abbrev HeadStore := Store headLayout

def headAddress : Address headLayout := ⟨.head, ()⟩

def headOf (store : HeadStore) : Option Head := store headAddress

def headStore (head : Head) : HeadStore := (0 : HeadStore).set headAddress (some head)

@[simp] theorem headOf_headStore (head : Head) : headOf (headStore head) = some head :=
  Store.set_eq _ _ _

/-- A room stream's head at birth: no entries. -/
def emptyRoomHead : Head := ⟨.room, 0, none⟩

/-- A fleet topic's head before its first entry. -/
def emptyTopicHead (stream : Digest) : Head := ⟨.topic stream, 0, none⟩

/-- The head law: a head is present; an empty stream has no tail and a
nonempty one has one; a topic head sits at the cell its stream derives. -/
def Binding.At (cellId : Nat) : Binding → Prop
  | .room => True
  | .topic stream => cellId = topicHeadCellId stream

instance bindingAtDecidable (cellId : Nat) (binding : Binding) : Decidable (binding.At cellId) := by
  cases binding <;> unfold Binding.At <;> infer_instance

def Head.Lawful (cellId : Nat) (head : Head) : Prop :=
  (head.count = 0 ↔ head.tail = none) ∧ head.binding.At cellId

instance headLawfulDecidable (cellId : Nat) (head : Head) : Decidable (head.Lawful cellId) := by
  unfold Head.Lawful; infer_instance

def HeadLaw (cellId : Nat) (store : HeadStore) : Prop :=
  match headOf store with
  | none => False
  | some head => head.Lawful cellId

instance headLawDecidable (cellId : Nat) (store : HeadStore) : Decidable (HeadLaw cellId store) := by
  unfold HeadLaw; split <;> infer_instance

/-! ## The entry cell: layout and wire -/

inductive EntryNamespace where
  | entry
  deriving DecidableEq, Repr

abbrev entryLayout : Layout.{0, 0, 0} where
  Namespace := EntryNamespace
  Key := fun _ => Unit
  Value := fun _ => Entry
  discipline := fun _ => .appendOnly

def entryNamespaceStream : StreamCodec entryLayout.Namespace where
  encode _ := []
  decodePrefix bytes := some (.entry, bytes)
  decodePrefix_encode := by intro space suffix; cases space; rfl

def entryWire : Wire entryLayout where
  name := "minidregg/stream-entry/v1"
  namespaces := [.entry]
  namespaces_complete := by intro space; cases space; simp
  namespaceStream := entryNamespaceStream
  keyStream := fun _ => unitStream
  valueStream := fun _ => streamEntryStream
  keyCodecId := fun _ => "unit"
  valueCodecId := fun _ => "stream-entry/v1"

def entryMaterializer : Materializer entryLayout Digest := StoreCodec.materializer entryWire

abbrev EntryStore := Store entryLayout

def entryAddress : Address entryLayout := ⟨.entry, ()⟩

def entryOf (store : EntryStore) : Option Entry := store entryAddress

def entryStore (entry : Entry) : EntryStore := (0 : EntryStore).set entryAddress (some entry)

@[simp] theorem entryOf_entryStore (entry : Entry) : entryOf (entryStore entry) = some entry :=
  Store.set_eq _ _ _

/-- The entry law: an entry is present, sits at the cell its head and position
derive, has a positive position, a parent exactly when it is not the first, and
a bounded topic. -/
def EntryLaw (cellId : Nat) (store : EntryStore) : Prop :=
  match entryOf store with
  | none => False
  | some entry =>
      cellId = entryCellId entry.head entry.sequence ∧ 1 ≤ entry.sequence ∧
      (entry.sequence = 1 ↔ entry.parent = none) ∧
      entry.record.entry.topic.length ≤ maxTopicBytes

instance entryLawDecidable (cellId : Nat) (store : EntryStore) : Decidable (EntryLaw cellId store) := by
  unfold EntryLaw; split <;> infer_instance

/-! ## Appending -/

/-- The next sequence position: one past the number of recorded entries. -/
def Head.nextSeq (head : Head) : Nat := head.count + 1

/-- The next position of a head store (a store with no head is no lawful cell). -/
def nextSeqOf (store : HeadStore) : Nat := ((headOf store).map Head.nextSeq).getD 1

/-- The entry an append records: the head's next position, its tail as parent. -/
def appendEntry (headCell : Nat) (head : Head) (record : StreamRecord) : Entry :=
  ⟨headCell, head.nextSeq, head.tail, record⟩

/-- The head after recording `entry`. -/
def Head.append (head : Head) (entry : Entry) : Head :=
  { head with count := head.count + 1, tail := some (entryKey entry) }

/-- The one head operation of an append: a guarded write of the head value. -/
def headWriteOp (head : Head) (entry : Entry) : Op headLayout :=
  .write .head () head (head.append entry)

/-- **`headWrite_footprint`.** An append's head patch touches exactly the one
head address, whatever the stream's length. -/
theorem headWrite_footprint (head : Head) (entry : Entry) :
    Patch.accessFootprint [headWriteOp head entry] = {headAddress} := by
  simp [Patch.accessFootprint, headWriteOp, Op.address, headAddress]

/-- The write is enabled exactly at the head it was planned from. -/
theorem headWrite_enabled (head : Head) (entry : Entry) :
    (headWriteOp head entry).Enabled (headStore head) := by
  refine ⟨rfl, ?_⟩
  simp [headStore, headAddress, Store.set]

/-- After an append, the head that planned it is gone: a second append planned
from the same head is not enabled (same-stream appends serialise). -/
theorem same_head_refused (head : Head) (first second : Entry) :
    ¬ (headWriteOp head second).Enabled ((headWriteOp head first).apply (headStore head)) := by
  rintro ⟨_, current⟩
  simp [headWriteOp, Op.apply, headStore, headAddress, Store.set, Head.append] at current
  have := congrArg Head.count current
  simp at this

/-- An append recorded at the head's next position, with the head's tail as
parent, and the new head counts it and points at it. -/
theorem append_advances (headCell : Nat) (head : Head) (record : StreamRecord) :
    (appendEntry headCell head record).sequence = head.count + 1 ∧
    (appendEntry headCell head record).parent = head.tail ∧
    (head.append (appendEntry headCell head record)).count = head.count + 1 ∧
    (head.append (appendEntry headCell head record)).tail =
      some (entryKey (appendEntry headCell head record)) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- An append keeps a lawful head lawful (the binding is unchanged). -/
theorem append_head_lawful (cellId : Nat) (head : Head) (entry : Entry)
    (lawful : head.Lawful cellId) : (head.append entry).Lawful cellId :=
  ⟨by simp [Head.append], lawful.2⟩

/-- The entry an append records is lawful at its derived cell, given a lawful
head (positions start at 1; the first entry has no parent) and a bounded topic. -/
theorem appendEntry_lawful (headCell : Nat) (head : Head) (record : StreamRecord)
    (lawful : head.count = 0 ↔ head.tail = none)
    (topic : record.entry.topic.length ≤ maxTopicBytes) :
    EntryLaw (entryCellId headCell head.nextSeq) (entryStore (appendEntry headCell head record)) := by
  unfold EntryLaw
  rw [entryOf_entryStore]
  refine ⟨rfl, by simp [appendEntry, Head.nextSeq], ?_, topic⟩
  simp only [appendEntry, Head.nextSeq]
  constructor
  · intro one; exact lawful.mp (by omega)
  · intro none; have := lawful.mpr none; omega

/-- info: 'Minidregg.Compiler.StreamCell.headWrite_footprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms headWrite_footprint
/-- info: 'Minidregg.Compiler.StreamCell.headWrite_enabled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms headWrite_enabled
/-- info: 'Minidregg.Compiler.StreamCell.same_head_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms same_head_refused
/-- info: 'Minidregg.Compiler.StreamCell.append_advances' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms append_advances
/-- info: 'Minidregg.Compiler.StreamCell.append_head_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms append_head_lawful
/-- info: 'Minidregg.Compiler.StreamCell.appendEntry_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms appendEntry_lawful

end Minidregg.Compiler.StreamCell
