/-
# Compiler.DurableRecordFast — a ByteArray-indexed decoder for the durable log record

The record frame is decoded through the list-based reference decoder
(`Framed.decode` over `intentStream`): one list cell per input byte, the stream
walked by `List` pattern matching. This module decodes the same stream by
INDEX into a `ByteArray` and proves, for every input, that it is the reference:
`recordFrame_decode_eq`, installed with `@[csimp]` (never `implemented_by`).

The proof is compositional. A `Fast codec` is a decoder `ByteArray → Nat →
Option (α × Nat)` together with its agreement with `codec.decodePrefix` on the
window of the input from the position: it fails exactly when the reference
fails (`none_iff`), and when it succeeds with `(v, j)` the reference returns
`v` and the suffix from `j` (`some_eq`). Primitives (`nat`, `bytes`, `byte`) are
proved once; `product`, `xmap`, `option`, `list` compose; `intentFast` is the
composition of `intentStream`'s own structure.
-/
import Compiler.DurableCheckpointCodec
import Theory.AssertAxioms

namespace Minidregg.Compiler.DurableRecordFast

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.DurableReceiverCodec

set_option autoImplicit false

/-- The input from position `i` on, as the reference decoder sees it. -/
def window (b : ByteArray) (i : Nat) : List UInt8 := b.data.toList.drop i

structure Fast {α : Type} (codec : StreamCodec α) where
  decode : ByteArray → Nat → Option (α × Nat)
  none_iff : ∀ b i, decode b i = none ↔ codec.decodePrefix (window b i) = none
  some_eq : ∀ b i v j, decode b i = some (v, j) →
    codec.decodePrefix (window b i) = some (v, window b j)

namespace Fast

variable {α β : Type}

theorem decode_agrees {codec : StreamCodec α} (fast : Fast codec) (b : ByteArray) (i : Nat) :
    (codec.decodePrefix (window b i)) =
      (fast.decode b i).map fun p => (p.1, window b p.2) := by
  cases h : fast.decode b i with
  | none => simpa using (fast.none_iff b i).mp h
  | some p => simpa using fast.some_eq b i p.1 p.2 h

def product {left : StreamCodec α} {right : StreamCodec β} (l : Fast left) (r : Fast right) :
    Fast (StreamCodec.product left right) where
  decode b i := do
    let (first, j) ← l.decode b i
    let (second, k) ← r.decode b j
    some ((first, second), k)
  none_iff b i := by
    show _ ↔ (do
      let (first, afterFirst) ← left.decodePrefix (window b i)
      let (second, suffix) ← right.decodePrefix afterFirst
      some ((first, second), suffix)) = none
    rw [l.decode_agrees b i]
    cases hl : l.decode b i with
    | none => simp
    | some p =>
        obtain ⟨first, j⟩ := p
        simp only [Option.map_some, bind, Option.bind]
        rw [r.decode_agrees b j]
        cases hr : r.decode b j with
        | none => simp
        | some q => simp
  some_eq b i v j h := by
    cases hl : l.decode b i with
    | none => simp [hl, bind, Option.bind] at h
    | some p =>
        obtain ⟨first, j'⟩ := p
        cases hr : r.decode b j' with
        | none => simp [hl, hr, bind, Option.bind] at h
        | some q =>
            obtain ⟨second, k⟩ := q
            simp only [hl, hr, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            show (do
              let (first, afterFirst) ← left.decodePrefix (window b i)
              let (second, suffix) ← right.decodePrefix afterFirst
              some ((first, second), suffix)) = _
            rw [l.some_eq b i first j' hl]
            simp only [bind, Option.bind]
            rw [r.some_eq b j' second k hr]

def xmap {codec : StreamCodec α} (inner : Fast codec) (toWire : β → α) (fromWire : α → β)
    (roundtrip : ∀ value, fromWire (toWire value) = value) :
    Fast (StreamCodec.xmap codec toWire fromWire roundtrip) where
  decode b i := (inner.decode b i).map fun p => (fromWire p.1, p.2)
  none_iff b i := by
    show _ ↔ (do
      let (wire, suffix) ← codec.decodePrefix (window b i)
      some (fromWire wire, suffix)) = none
    rw [inner.decode_agrees b i]
    cases h : inner.decode b i <;> simp
  some_eq b i v j h := by
    cases hd : inner.decode b i with
    | none => simp [hd] at h
    | some p =>
        obtain ⟨wire, k⟩ := p
        simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        show (do
          let (wire', suffix) ← codec.decodePrefix (window b i)
          some (fromWire wire', suffix)) = _
        rw [inner.some_eq b i wire k hd]
        rfl

/-- The same decoder for a codec with the same prefix decoder. -/
def reindex {c₁ c₂ : StreamCodec α} (f : Fast c₁) (same : c₂.decodePrefix = c₁.decodePrefix) :
    Fast c₂ where
  decode := f.decode
  none_iff b i := by rw [same]; exact f.none_iff b i
  some_eq b i v j h := by rw [same]; exact f.some_eq b i v j h

end Fast

theorem window_cons (b : ByteArray) (i : Nat) (h : i < b.size) :
    window b i = b[i] :: window b (i + 1) := by
  unfold window
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  rfl

theorem window_nil (b : ByteArray) (i : Nat) (h : ¬ i < b.size) : window b i = [] := by
  unfold window
  apply List.drop_of_length_le
  simpa using h

theorem length_window (b : ByteArray) (i : Nat) : (window b i).length = b.size - i := by
  unfold window
  simp [ByteArray.size_data]

def byteAt (b : ByteArray) (i : Nat) : Option (UInt8 × Nat) :=
  if h : i < b.size then some (b[i], i + 1) else none

def byteFast : Fast StreamCodec.byte where
  decode := byteAt
  none_iff b i := by
    unfold byteAt
    by_cases h : i < b.size
    · rw [dif_pos h, window_cons b i h]; simp [StreamCodec.byte]
    · rw [dif_neg h, window_nil b i h]; simp [StreamCodec.byte]
  some_eq b i v j hd := by
    unfold byteAt at hd
    by_cases h : i < b.size
    · rw [dif_pos h] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      rw [window_cons b i h]; rfl
    · rw [dif_neg h] at hd; cases hd

theorem option_decodePrefix_zero {α : Type} (codec : StreamCodec α) (s : List UInt8) :
    (StreamCodec.option codec).decodePrefix (0 :: s) = some (none, s) := rfl

theorem option_decodePrefix_one {α : Type} (codec : StreamCodec α) (s : List UInt8) :
    (StreamCodec.option codec).decodePrefix (1 :: s) =
      (codec.decodePrefix s).map fun p => (some p.1, p.2) := by
  show (do let (value, suffix) ← codec.decodePrefix s; some (some value, suffix)) = _
  cases codec.decodePrefix s <;> rfl

theorem option_decodePrefix_other {α : Type} (codec : StreamCodec α) (t : UInt8) (s : List UInt8)
    (h0 : t ≠ 0) (h1 : t ≠ 1) : (StreamCodec.option codec).decodePrefix (t :: s) = none := by
  show (match t :: s with
    | [] => none
    | 0 :: suffix => some (none, suffix)
    | 1 :: bytes => do let (value, suffix) ← codec.decodePrefix bytes; some (some value, suffix)
    | _ => none) = none
  split <;> first | rfl | simp_all

/-- A one-byte tag, then the payload. -/
def optionFast {α : Type} {codec : StreamCodec α} (inner : Fast codec) :
    Fast (StreamCodec.option codec) where
  decode b i :=
    if h : i < b.size then
      if b[i] = 0 then some (none, i + 1)
      else if b[i] = 1 then (inner.decode b (i + 1)).map fun p => (some p.1, p.2)
      else none
    else none
  none_iff b i := by
    by_cases h : i < b.size
    · rw [dif_pos h, window_cons b i h]
      generalize b[i] = tag
      by_cases t0 : tag = 0
      · subst t0; simp [option_decodePrefix_zero]
      · by_cases t1 : tag = 1
        · subst t1
          simp only [if_neg (by decide : ¬ (1 : UInt8) = 0), if_true, option_decodePrefix_one]
          rw [inner.decode_agrees b (i + 1)]
          cases inner.decode b (i + 1) <;> simp
        · simp [t0, t1, option_decodePrefix_other codec tag _ t0 t1]
    · rw [dif_neg h, window_nil b i h]; simp [StreamCodec.option]
  some_eq b i v j hd := by
    by_cases h : i < b.size
    · rw [dif_pos h] at hd
      rw [window_cons b i h]
      generalize b[i] = tag at hd ⊢
      by_cases t0 : tag = 0
      · subst t0
        simp only [if_true, Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨rfl, rfl⟩ := hd
        rfl
      · by_cases t1 : tag = 1
        · subst t1
          simp only [if_neg (by decide : ¬ (1 : UInt8) = 0), if_true] at hd
          cases hi : inner.decode b (i + 1) with
          | none => simp [hi] at hd
          | some p =>
              obtain ⟨w, k⟩ := p
              simp only [hi, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
              obtain ⟨rfl, rfl⟩ := hd
              rw [option_decodePrefix_one, inner.some_eq b (i + 1) w k hi]
              rfl
        · simp [t0, t1] at hd
    · rw [dif_neg h] at hd; cases hd

/-! ### Compact naturals -/

/-- Base-255 little-endian digits ended by byte 255, read by index. `fuel` bounds
the digits (one per remaining byte at most). -/
def natAux (b : ByteArray) : Nat → Nat → Option (Nat × Nat)
  | 0, _ => none
  | fuel + 1, pos =>
      if h : pos < b.size then
        if b[pos] = 255 then some (0, pos + 1)
        else
          match natAux b fuel (pos + 1) with
          | none => none
          | some (higher, stop) => some (b[pos].toNat + 255 * higher, stop)
      else none

theorem natAux_spec (b : ByteArray) :
    ∀ (fuel pos : Nat), b.size - pos < fuel →
      (natAux b fuel pos = none ↔ StreamCodec.decodeNatPrefix (window b pos) = none) ∧
      (∀ v j, natAux b fuel pos = some (v, j) →
        StreamCodec.decodeNatPrefix (window b pos) = some (v, window b j))
  | 0, pos, lt => by omega
  | fuel + 1, pos, lt => by
      unfold natAux
      by_cases h : pos < b.size
      · rw [dif_pos h, window_cons b pos h]
        by_cases t : b[pos] = 255
        · simp [t, StreamCodec.decodeNatPrefix]
        · have ih := natAux_spec b fuel (pos + 1) (by omega)
          simp only [if_neg t, StreamCodec.decodeNatPrefix]
          cases hr : natAux b fuel (pos + 1) with
          | none =>
              have : StreamCodec.decodeNatPrefix (window b (pos + 1)) = none := ih.1.mp hr
              simp [this]
          | some p =>
              obtain ⟨higher, stop⟩ := p
              have := ih.2 higher stop hr
              simp [this]
      · rw [dif_neg h, window_nil b pos h]
        simp [StreamCodec.decodeNatPrefix]

def natAt (b : ByteArray) (i : Nat) : Option (Nat × Nat) := natAux b (b.size - i + 1) i

def natFast : Fast StreamCodec.nat where
  decode := natAt
  none_iff b i := (natAux_spec b (b.size - i + 1) i (by omega)).1
  some_eq b i v j := (natAux_spec b (b.size - i + 1) i (by omega)).2 v j

/-! ### Length-prefixed bytes -/

/-- The `n` bytes from `j`, as a list, in one pass (prepending from the last). -/
def sliceLoop (b : ByteArray) (j : Nat) : Nat → List UInt8 → List UInt8
  | 0, acc => acc
  | k + 1, acc => sliceLoop b j k (b.get! (j + k) :: acc)

theorem sliceLoop_eq (b : ByteArray) (j : Nat) :
    ∀ (k : Nat) (acc : List UInt8), k ≤ b.size - j →
      sliceLoop b j k acc = (window b j).take k ++ acc
  | 0, acc, _ => by simp [sliceLoop]
  | k + 1, acc, fits => by
      have inRange : j + k < b.size := by omega
      have ih := sliceLoop_eq b j k (b.get! (j + k) :: acc) (by omega)
      rw [sliceLoop, ih, List.take_add_one]
      have get : (window b j)[k]? = some (b.get! (j + k)) := by
        unfold window
        rw [List.getElem?_drop]
        simp only [Array.getElem?_toList, ByteArray.get!, Array.getElem!_eq_getD]
        rw [Array.getElem?_eq_getElem (by simpa [ByteArray.size_data] using inRange)]
        simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa [ByteArray.size_data] using inRange)]
        rfl
      rw [get]
      simp

def bytesAt (b : ByteArray) (i : Nat) : Option (List UInt8 × Nat) :=
  match natAt b i with
  | none => none
  | some (n, j) => if n ≤ b.size - j then some (sliceLoop b j n [], j + n) else none

theorem natFast_decode (b : ByteArray) (i : Nat) : natFast.decode b i = natAt b i := rfl

def bytesFast : Fast bytesStream where
  decode := bytesAt
  none_iff b i := by
    show _ ↔ (do
      let (count, afterCount) ← StreamCodec.nat.decodePrefix (window b i)
      decodeBytesPrefix count afterCount) = none
    rw [natFast.decode_agrees b i, natFast_decode]
    unfold bytesAt
    cases hn : natAt b i with
    | none => simp
    | some p =>
        obtain ⟨n, j⟩ := p
        simp only [Option.map_some, bind, Option.bind, decodeBytesPrefix, length_window]
        by_cases fits : n ≤ b.size - j
        · rw [if_pos fits, if_pos fits]; simp
        · rw [if_neg fits, if_neg fits]; simp
  some_eq b i v j hd := by
    unfold bytesAt at hd
    cases hn : natAt b i with
    | none => simp [hn] at hd
    | some p =>
        obtain ⟨n, j'⟩ := p
        simp only [hn] at hd
        by_cases fits : n ≤ b.size - j'
        · simp only [fits, if_true, Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨rfl, rfl⟩ := hd
          show (do
            let (count, afterCount) ← StreamCodec.nat.decodePrefix (window b i)
            decodeBytesPrefix count afterCount) = _
          rw [natFast.decode_agrees b i, natFast_decode]
          simp only [hn, Option.map_some, bind, Option.bind, decodeBytesPrefix, length_window,
            List.splitAt_eq]
          rw [if_pos fits, sliceLoop_eq b j' n [] fits]
          unfold window
          simp [List.drop_drop, Nat.add_comm]
        · simp [fits] at hd

/-! ### Counted sequences -/

def manyAt {α : Type} {codec : StreamCodec α} (inner : Fast codec) (b : ByteArray) :
    Nat → Nat → Option (List α × Nat)
  | 0, i => some ([], i)
  | count + 1, i =>
      match inner.decode b i with
      | none => none
      | some (value, j) =>
          match manyAt inner b count j with
          | none => none
          | some (values, k) => some (value :: values, k)

theorem manyAt_spec {α : Type} {codec : StreamCodec α} (inner : Fast codec) (b : ByteArray) :
    ∀ (count i : Nat),
      (manyAt inner b count i = none ↔ StreamCodec.decodeMany codec count (window b i) = none) ∧
      (∀ vs j, manyAt inner b count i = some (vs, j) →
        StreamCodec.decodeMany codec count (window b i) = some (vs, window b j))
  | 0, i => by simp [manyAt, StreamCodec.decodeMany]
  | count + 1, i => by
      have ih := manyAt_spec inner b count
      unfold manyAt StreamCodec.decodeMany
      rw [inner.decode_agrees b i]
      cases hd : inner.decode b i with
      | none => simp
      | some p =>
          obtain ⟨value, j⟩ := p
          simp only [Option.map_some, bind, Option.bind]
          cases hm : manyAt inner b count j with
          | none =>
              have := (ih j).1.mp hm
              simp [this]
          | some q =>
              obtain ⟨values, k⟩ := q
              have := (ih j).2 values k hm
              simp [this]

def listFast {α : Type} {codec : StreamCodec α} (inner : Fast codec) :
    Fast (StreamCodec.list codec) where
  decode b i :=
    match natAt b i with
    | none => none
    | some (count, j) => manyAt inner b count j
  none_iff b i := by
    show _ ↔ (do
      let (count, afterCount) ← StreamCodec.nat.decodePrefix (window b i)
      StreamCodec.decodeMany codec count afterCount) = none
    rw [natFast.decode_agrees b i, natFast_decode]
    cases hn : natAt b i with
    | none => simp
    | some p =>
        obtain ⟨count, j⟩ := p
        simp only [Option.map_some, bind, Option.bind]
        exact (manyAt_spec inner b count j).1
  some_eq b i v j hd := by
    cases hn : natAt b i with
    | none => simp [hn] at hd
    | some p =>
        obtain ⟨count, j'⟩ := p
        simp only [hn] at hd
        show (do
          let (count, afterCount) ← StreamCodec.nat.decodePrefix (window b i)
          StreamCodec.decodeMany codec count afterCount) = _
        rw [natFast.decode_agrees b i, natFast_decode]
        simp only [hn, Option.map_some, bind, Option.bind]
        exact (manyAt_spec inner b count j').2 v j hd

/-! ### The record stream, mirrored from `DurableReceiverCodec.intentStream` -/

open Fast

def digestFast : Fast digestStream :=
  reindex (xmap natFast (fun digest : Digest => digest.value) Digest.mk
    (by intro digest; cases digest; rfl)) rfl

def chargeTupleFast : Fast chargeTupleStream :=
  reindex (product natFast (product natFast (product natFast (product natFast (product natFast
    (product natFast (product natFast (product natFast (product natFast natFast))))))))) rfl

def chargeFast : Fast chargeStream :=
  reindex (xmap chargeTupleFast chargeTuple chargeOfTuple chargeOfTuple_tuple) rfl

def writeFast : Fast writeStream :=
  reindex (xmap (product digestFast (product digestFast (product digestFast bytesFast)))
    (fun write : DataWrite => (write.cellId, write.expectedPre, write.exactPost, write.canonicalPostBytes))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
    (by intro value; cases value; rfl)) rfl

def guardFast : Fast guardStream :=
  reindex (xmap (product digestFast digestFast)
    (fun guard : ReadGuard => (guard.cellId, guard.expectedRoot))
    (fun tuple => ⟨tuple.1, tuple.2⟩) (by intro value; cases value; rfl)) rfl

def nullifierFast : Fast nullifierStream :=
  reindex (xmap (product natFast (product digestFast (product digestFast bytesFast)))
    (fun value : StableNullifier => (value.codecVersion, value.domain, value.nullifierId, value.canonicalBytes))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
    (by intro value; cases value; rfl)) rfl

def eventFast : Fast eventStream :=
  reindex (xmap (product natFast (product digestFast (product digestFast bytesFast)))
    (fun value : StableEvent => (value.codecVersion, value.domain, value.eventId, value.canonicalBytes))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
    (by intro value; cases value; rfl)) rfl

def subjectFast : Fast subjectStream :=
  reindex (xmap natFast (fun subject : SubjectId => subject.value) SubjectId.mk
    (by intro value; cases value; rfl)) rfl

def intentFast : Fast intentStream :=
  reindex (xmap
    (product digestFast
      (product (listFast writeFast)
        (product (listFast guardFast)
          (product (listFast nullifierFast)
            (product chargeFast
              (product eventFast
                (optionFast subjectFast)))))))
    (fun record : IntentRecord => (record.transactionId, record.writes, record.readGuards,
      record.nullifiers, record.exactCharge, record.event, record.subject))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2.1,
      tuple.2.2.2.2.1, tuple.2.2.2.2.2.1, tuple.2.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)) rfl

/-! ### The record frame -/

theorem window_zero (bytes : List UInt8) : window bytes.toByteArray 0 = bytes := by
  simp [window]

theorem window_eq_nil_iff (b : ByteArray) (j : Nat) : window b j = [] ↔ b.size ≤ j := by
  have := length_window b j
  constructor
  · intro h; rw [h] at this; simp at this; omega
  · intro h; apply List.eq_nil_of_length_eq_zero; omega

/-- The decoder of the durable log record: `recordFrame.decode`, named so the
compiled code can be replaced by `decodeRecordFast` (`decodeRecord_eq_fast`). -/
def decodeRecord (bytes : List UInt8) : Option IntentRecord :=
  DurableCheckpointCodec.recordFrame.decode bytes

/-- The frame, the record, full consumption, and the canonical re-encoding. -/
def decodeRecordFast (bytes : List UInt8) : Option IntentRecord :=
  let b := bytes.toByteArray
  match (Fast.product bytesFast intentFast).decode b 0 with
  | none => none
  | some ((frame, record), j) =>
      if b.size ≤ j ∧ frame = DurableCheckpointCodec.recordFrame.frame ∧
          DurableCheckpointCodec.recordFrame.encode record = bytes then some record else none

theorem decodeRecordFast_eq (bytes : List UInt8) : decodeRecordFast bytes = decodeRecord bytes := by
  unfold decodeRecordFast decodeRecord DurableCheckpointCodec.Framed.decode
  have agrees := (Fast.product bytesFast intentFast).decode_agrees bytes.toByteArray 0
  rw [window_zero] at agrees
  have lawful : (StreamCodec.product bytesStream DurableCheckpointCodec.recordFrame.stream).toLawful.decode bytes =
      (do
        let p ← (StreamCodec.product bytesStream intentStream).decodePrefix bytes
        if p.2 = [] then some p.1 else none) := rfl
  rw [lawful, agrees]
  dsimp only
  cases hd : (Fast.product bytesFast intentFast).decode bytes.toByteArray 0 with
  | none => simp [hd]
  | some p =>
      obtain ⟨⟨frame, record⟩, j⟩ := p
      simp only [Option.map_some, bind, Option.bind]
      by_cases consumed : bytes.toByteArray.size ≤ j
      · have : window bytes.toByteArray j = [] := (window_eq_nil_iff _ _).mpr consumed
        simp only [this, if_true, consumed, true_and]
      · have : window bytes.toByteArray j ≠ [] := fun h => consumed ((window_eq_nil_iff _ _).mp h)
        have consumed' : ¬ bytes.length ≤ j := by simpa using consumed
        simp [this, consumed']

@[csimp] theorem decodeRecord_eq_fast : @decodeRecord = @decodeRecordFast := by
  funext bytes
  exact (decodeRecordFast_eq bytes).symm

#assert_axioms natAux_spec
#assert_axioms manyAt_spec
#assert_axioms decodeRecordFast_eq
#assert_axioms decodeRecord_eq_fast

end Minidregg.Compiler.DurableRecordFast
