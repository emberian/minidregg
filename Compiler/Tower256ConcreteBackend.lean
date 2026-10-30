/-
# Compiler.Tower256ConcreteBackend -- one shared concrete binary backend

This module owns the single concrete `Backend (binaryTower 8)` intended for
Tower256 LogUp and additive PCS constructions.  It combines:

* the exact recursive Fan--Paar semantic field profile;
* the Lean-owned SP 800-185 cSHAKE256 computation;
* compact, prefix-decodable codecs for Merkle paths and transcript values;
* fixed readable leaf/node/absorb/draw customization strings;
* stable first-order algorithm, suite, codec, and value-type pins.

Consumers should depend on `backend`, `towerExact`, and `cshakeExact` instead
of rebuilding local copies.  Per-column IDs and proof-suite binding premises
remain consumer data.  This file proves functional codec and projection facts,
not collision resistance, a random-oracle theorem, PCS soundness, or any Rust
semantics.
-/

module

public import Compiler.BinaryTower256Profile
public import Compiler.Sp800185Cshake256
public import Compiler.NatDigits255Fast
public import Theory.Bignum
public import Theory.AssertAxioms
meta import Compiler.BinaryTower256Profile
meta import Compiler.Sp800185Cshake256
meta import Compiler.NatDigits255Fast
meta import Theory.Bignum
meta import Theory.AssertAxioms

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Compiler.Tower256ConcreteBackend

open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.NativeKernelPlan (WorkKind)
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-! ## Exact byte comparison -/

/-- Compare two byte lists in tail position, on unboxed octets. The derived
`List UInt8` equality recurses once per octet (stack depth = length) and calls
the element instance through a closure. A `StreamCodec` decoder needs no byte
comparison at all (it is canonical, `StreamCodec.toLawful_canonical`); this is
for the remaining comparisons of whole byte strings (`strictCodec` over a
hand-written decoder, an extracted package against its authored bytes). -/
def bytesEqual : List UInt8 → List UInt8 → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      if left = right then bytesEqual lefts rights else false
  | _, _ => false

theorem bytesEqual_eq_true_iff (left right : List UInt8) :
    bytesEqual left right = true ↔ left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp [bytesEqual]
  | cons left lefts ih =>
      cases right with
      | nil => simp [bytesEqual]
      | cons right rights => simp [bytesEqual, ih]

/-! ## Compact streaming-codec nucleus -/

set_option hygiene false in
/-- Discharges `StreamCodec.encode_decodePrefix` for a hand-written decoder
that matches on a prefix of literal octets (tags, enums), each arm a chain of
prefix decodes ending in `some`: split the decoder's cases, read every inner
decode back as the encoding it consumed, and compare. A decoder with a
defaulting arm, or one that drops what it decoded, is not canonical and this
fails on it. (Unhygienic: it names the `StreamCodec.encode_decodePrefix`
projection, which is declared below it.) -/
macro "stream_canonical" : tactic => `(tactic| (
  first
  | (intro bytes value suffix decoded
     revert decoded
     split <;> intro decoded <;> first
       | (cases decoded; done)
       | (try simp only [Option.bind_eq_bind] at decoded
          repeat' (
           rw [Option.bind_eq_some_iff] at decoded
           obtain ⟨⟨_, _⟩, ok, decoded⟩ := decoded
           have okBytes := Minidregg.Compiler.Tower256ConcreteBackend.StreamCodec.encode_decodePrefix _ _ _ _ ok
           subst okBytes
           try dsimp only at decoded)
          simp only [Option.some.injEq, Prod.mk.injEq] at decoded
          obtain ⟨sameValue, sameSuffix⟩ := decoded
          first | subst sameValue | cases sameValue
          subst sameSuffix
          try dsimp only
          first
            | rfl
            | (simp only [List.cons_append, List.append_assoc]; done)
            | (simp only [List.cons_append, List.append_assoc]; rfl)
            | simp [List.append_assoc]))
  | (intro bytes value suffix decoded
     rcases bytes with _ | ⟨tag, bytes⟩
     · first | cases decoded | simp at decoded
     · revert decoded
       split <;> intro decoded <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at decoded <;>
         (obtain ⟨sameValue, sameSuffix⟩ := decoded; subst sameValue; subst sameSuffix; simp_all))))

/-- Discharges `xmap`'s `wireRoundtrip` for the usual view change: a record
spelled as a nested tuple and rebuilt from it (by projections or by a match). -/
macro "xmap_wire_roundtrip" : tactic => `(tactic| (
  intro wire
  first
    | rfl
    | (casesm* _ × _, _ ⊕ _, Option _ <;> rfl)
    | (casesm* _ × _, _ ⊕ _, Option _ <;> simp_all)
    | (cases wire <;> (try casesm* _ × _, _ ⊕ _, Option _) <;> rfl)))

/-- The cursor reading of a list decoder: decode the octets of `bytes` from
`start` on, and answer where the unread suffix begins. Every
`StreamCodec.decodeAt` agrees with this (`StreamCodec.decodeAt_spec`); it is the
default for a hand-written decoder and the specification a native loop is
proved against. -/
def cursorOfPrefix {alpha : Type} (decode : List UInt8 -> Option (alpha × List UInt8))
    (bytes : ByteArray) (start : Nat) : Option (alpha × Nat) :=
  (decode (bytes.data.toList.drop start)).map fun result => (result.1, bytes.size - result.2.length)

/-- Push every octet of `bytes` onto `out`, in order: the writer of a list of
octets, in place while `out` is unshared. -/
def pushOctets (out : ByteArray) : List UInt8 -> ByteArray
  | [] => out
  | octet :: rest => pushOctets (out.push octet) rest

theorem push_data (out : ByteArray) (octet : UInt8) :
    (out.push octet).data.toList = out.data.toList ++ [octet] := by
  rw [ByteArray.data_push, Array.toList_push]

theorem pushOctets_data (out : ByteArray) (bytes : List UInt8) :
    (pushOctets out bytes).data.toList = out.data.toList ++ bytes := by
  induction bytes generalizing out with
  | nil => simp [pushOctets]
  | cons octet rest ih => rw [pushOctets, ih, push_data, List.append_assoc, List.singleton_append]

/-- Two buffers with the same octets are the same buffer. -/
theorem bytes_ext {left right : ByteArray} (same : left.data.toList = right.data.toList) :
    left = right := by
  cases left
  cases right
  exact congrArg ByteArray.mk (Array.ext' same)

/-- The octets of `bytes[0, index)` consed onto `acc`, read from the end: one cell per
octet, no reversal. -/
def octetsOnto (bytes : ByteArray) : (index : Nat) -> index ≤ bytes.size -> List UInt8 -> List UInt8
  | 0, _, acc => acc
  | index + 1, fits, acc => octetsOnto bytes index (by omega) (bytes[index]'(by omega) :: acc)

theorem octetsOnto_eq (bytes : ByteArray) (index : Nat) (fits : index ≤ bytes.size) (acc : List UInt8) :
    octetsOnto bytes index fits acc = bytes.data.toList.take index ++ acc := by
  induction index generalizing acc with
  | zero => simp [octetsOnto]
  | succ index ih =>
      rw [octetsOnto, ih, List.take_add_one]
      have inside : index < bytes.data.size := by
        rw [ByteArray.size_data]
        omega
      have octet : bytes.data.toList[index]? = some bytes[index] := by
        rw [Array.getElem?_toList, Array.getElem?_eq_getElem inside,
          ByteArray.getElem_eq_getElem_data]
      simp only [octet, Option.toList_some, List.append_assoc, List.singleton_append]

/-- The octets of a buffer as a list. -/
def octetsOf (bytes : ByteArray) : List UInt8 := octetsOnto bytes bytes.size (Nat.le_refl _) []

theorem octetsOf_eq (bytes : ByteArray) : octetsOf bytes = bytes.data.toList := by
  rw [octetsOf, octetsOnto_eq, List.append_nil, List.take_of_length_le]
  rw [Array.length_toList, ByteArray.size_data]

/-- A prefix codec consumes exactly one value and returns the unconsumed
suffix.  The append law makes sequential and list composition mechanical.

It is also CANONICAL (`encode_decodePrefix`): every input the decoder accepts
is the encoding of the value it returns followed by the suffix it returns, so
each value has exactly one spelling.  A strict decoder therefore needs no
re-encode-and-compare: requiring the suffix to be empty is the whole check
(`toLawful_canonical`). -/
structure StreamCodec (alpha : Type) where
  encode : alpha -> List UInt8
  decodePrefix : List UInt8 -> Option (alpha × List UInt8)
  decodePrefix_encode : forall value suffix,
    decodePrefix (encode value ++ suffix) = some (value, suffix)
  encode_decodePrefix : forall bytes value suffix,
    decodePrefix bytes = some (value, suffix) -> encode value ++ suffix = bytes := by
    stream_canonical
  /-- The same decoder over a packed buffer: from octet `start`, the value and
  the position after it. The primitives and combinators read octets by index
  and slice payloads straight out of the buffer; a hand-written decoder gets
  the list decoder run on the suffix (`cursorOfPrefix`). -/
  decodeAt : ByteArray -> Nat -> Option (alpha × Nat) := cursorOfPrefix decodePrefix
  /-- The cursor decodes exactly what the list decoder decodes, from any
  position inside the buffer. -/
  decodeAt_spec : forall bytes start, start ≤ bytes.size ->
    decodeAt bytes start = cursorOfPrefix decodePrefix bytes start := by
    intro _ _ _; rfl
  /-- `decodeAt` is a native loop all the way down (no `cursorOfPrefix`
  fallback anywhere inside). Only then does a top-level decode run on the
  cursor (`toLawfulCursor`); a fallback re-materializes the suffix as a list at
  every call, which inside a repetition would be quadratic. A dispatch bit, not
  a law: `decodeAt_spec` holds either way. -/
  cursorNative : Bool := false
  /-- The encoder as a WRITER: append the encoding of `value` to `out`. The primitives
  and combinators push octets straight into the buffer, so a nested record is written
  in one pass with no intermediate list and no list append; a hand-written encoder gets
  its list pushed (`pushOctets`). The compiled `encode` runs this writer
  (`StreamCodec.encode_eq_encodeViaWriter`). -/
  encodeInto : ByteArray -> alpha -> ByteArray := fun out value => pushOctets out (encode value)
  /-- The writer appends exactly the encoding. -/
  encodeInto_spec : forall out value,
    (encodeInto out value).data.toList = out.data.toList ++ encode value := by
    intro out value
    exact Minidregg.Compiler.Tower256ConcreteBackend.pushOctets_data _ _

/-- Discharges `StreamCodec.encode_decodePrefix` for a decoder that reads a
`StreamCodec.nat` tag and dispatches on it: each known tag's arm is a chain of
prefix decodes ending in `some`, and every other tag is refused (`| _ => none`).
A decoder with a defaulting arm is not canonical and this tactic fails on it. -/
macro "stream_canonical_tagged" : tactic => `(tactic| (
  intro bytes value suffix decoded
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at decoded
  obtain ⟨tag, afterTag, tagOk, decoded⟩ := decoded
  have tagBytes := StreamCodec.encode_decodePrefix _ _ _ _ tagOk
  subst tagBytes
  split at decoded <;> first
    | (cases decoded; done)
    | (repeat' (
          rw [Option.bind_eq_some_iff] at decoded
          obtain ⟨⟨_, _⟩, ok, decoded⟩ := decoded
          have okBytes := StreamCodec.encode_decodePrefix _ _ _ _ ok
          subst okBytes
          try dsimp only at decoded)
       simp only [Option.some.injEq, Prod.mk.injEq] at decoded
       obtain ⟨sameValue, sameSuffix⟩ := decoded
       subst sameValue
       subst sameSuffix
       try dsimp only
       try simp only [List.append_assoc]
       rfl)))

namespace StreamCodec

variable {alpha beta : Type}

/-! ### The compiled encoder -/

/-- The encoding of `value` in a fresh buffer, by the writer. -/
def encodeBytes (codec : StreamCodec alpha) (value : alpha) : ByteArray :=
  codec.encodeInto ByteArray.empty value

theorem encodeBytes_data (codec : StreamCodec alpha) (value : alpha) :
    (codec.encodeBytes value).data.toList = codec.encode value := by
  rw [encodeBytes, codec.encodeInto_spec, ByteArray.data_empty, Array.toList_empty, List.nil_append]

/-- `encode` as compiled: write into a buffer, then read the octets out once. A nested
record costs one pass and one list, where the list encoders cost one append (two
reversals of the left side) per combinator level. -/
def encodeViaWriter (codec : StreamCodec alpha) (value : alpha) : List UInt8 :=
  octetsOf (codec.encodeBytes value)

/-- Same function (`encodeInto_spec`), so no statement about `encode` changes. No
instance loops: a hand-written instance's default writer pushes its OWN encoder's list,
never the `encode` projection of itself. -/
@[csimp] theorem encode_eq_encodeViaWriter : @StreamCodec.encode = @StreamCodec.encodeViaWriter := by
  funext alpha codec value
  rw [encodeViaWriter, octetsOf_eq, encodeBytes_data]

/-- A prefix codec becomes a lawful top-level codec by requiring full input
consumption. -/
def toLawful (codec : StreamCodec alpha) : LawfulCodec alpha where
  encode := codec.encode
  decode bytes := do
    let (value, suffix) ← codec.decodePrefix bytes
    if suffix = [] then some value else none
  decode_encode := by
    intro value
    have hdecode := codec.decodePrefix_encode value []
    simp only [List.append_nil] at hdecode
    simp [hdecode]

/-- The top-level decoder accepts exactly the encodings: no re-encode is needed
to refuse a second spelling, because the stream codec has none. -/
theorem toLawful_canonical (codec : StreamCodec alpha) (bytes : List UInt8) (value : alpha)
    (decoded : codec.toLawful.decode bytes = some value) : codec.encode value = bytes := by
  simp only [toLawful] at decoded
  cases accepted : codec.decodePrefix bytes with
  | none => simp [accepted] at decoded
  | some pair =>
      obtain ⟨decodedValue, rest⟩ := pair
      simp only [accepted, bind, Option.bind] at decoded
      split at decoded
      · rename_i empty
        subst empty
        cases decoded
        simpa using codec.encode_decodePrefix _ _ _ accepted
      · cases decoded

/-- `toLawful` decodes exactly the encodings. -/
theorem toLawful_decode_iff (codec : StreamCodec alpha) (bytes : List UInt8) (value : alpha) :
    codec.toLawful.decode bytes = some value ↔ codec.encode value = bytes := by
  constructor
  · exact codec.toLawful_canonical bytes value
  · intro encoded
    subst encoded
    exact codec.toLawful.decode_encode value

/-! ### The cursor -/

theorem octets_length (bytes : ByteArray) : bytes.data.toList.length = bytes.size := by
  rw [Array.length_toList, ByteArray.size_data]

theorem octets_drop (bytes : ByteArray) {start : Nat} (inside : start < bytes.size) :
    bytes.data.toList.drop start = bytes[start] :: bytes.data.toList.drop (start + 1) := by
  rw [List.drop_eq_getElem_cons (by rwa [octets_length])]
  rfl

theorem octets_drop_end (bytes : ByteArray) {start : Nat} (outside : bytes.size ≤ start) :
    bytes.data.toList.drop start = [] :=
  List.drop_eq_nil_of_le (by rwa [octets_length])

theorem size_sub_drop (bytes : ByteArray) {start : Nat} (inside : start ≤ bytes.size) :
    bytes.size - (bytes.data.toList.drop start).length = start := by
  rw [List.length_drop, octets_length]
  omega

/-- What is left after a prefix of a suffix of `l` is a suffix of `l`, at its own length. -/
theorem drop_sub_length {l front rest : List UInt8} {start : Nat}
    (split : front ++ rest = l.drop start) : l.drop (l.length - rest.length) = rest := by
  have whole : l = (l.take start ++ front) ++ rest := by
    rw [List.append_assoc, split, List.take_append_drop]
  have length : l.length - rest.length = (l.take start ++ front).length := by
    have lengths := congrArg List.length whole
    simp only [List.length_append] at lengths ⊢
    omega
  rw [length]
  calc l.drop (l.take start ++ front).length
      = ((l.take start ++ front) ++ rest).drop (l.take start ++ front).length := by rw [← whole]
    _ = rest := List.drop_left

/-- After a list decode at `start`, the cursor position `size - |rest|` is where `rest` begins. -/
theorem rest_at (codec : StreamCodec alpha) {bytes : ByteArray} {start : Nat} {value : alpha}
    {rest : List UInt8} (decoded : codec.decodePrefix (bytes.data.toList.drop start) = some (value, rest)) :
    bytes.data.toList.drop (bytes.size - rest.length) = rest := by
  have dropped := drop_sub_length (codec.encode_decodePrefix _ _ _ decoded)
  rwa [octets_length] at dropped

/-- A top-level decode on the cursor: from octet 0, accepted only when the
cursor stops exactly at the end. -/
def decodeCursor (codec : StreamCodec alpha) (bytes : ByteArray) : Option alpha :=
  match codec.decodeAt bytes 0 with
  | some (value, next) => if next = bytes.size then some value else none
  | none => none

theorem decodeCursor_eq (codec : StreamCodec alpha) (bytes : ByteArray) :
    codec.decodeCursor bytes = codec.toLawful.decode bytes.data.toList := by
  unfold decodeCursor
  rw [codec.decodeAt_spec bytes 0 (Nat.zero_le _)]
  simp only [cursorOfPrefix, List.drop_zero, toLawful]
  cases decoded : codec.decodePrefix bytes.data.toList with
  | none => rfl
  | some pair =>
      obtain ⟨value, rest⟩ := pair
      have whole := codec.encode_decodePrefix _ _ _ decoded
      have fits : rest.length ≤ bytes.size := by
        rw [← octets_length, ← whole, List.length_append]
        omega
      by_cases empty : rest = []
      · subst empty
        simp
      · have nonzero : rest.length ≠ 0 := by simpa using empty
        have moved : bytes.size - rest.length ≠ bytes.size := by omega
        simp [empty, moved]

theorem _root_.ByteArray.toList_loop_eq (bytes : ByteArray) (index : Nat) (acc : List UInt8) :
    ByteArray.toList.loop bytes index acc = acc.reverse ++ bytes.data.toList.drop index := by
  rw [ByteArray.toList.loop]
  split
  · rename_i inside
    rw [ByteArray.toList_loop_eq bytes (index + 1), octets_drop bytes inside]
    have same : bytes.get! index = bytes[index] := by
      cases bytes with
      | mk data =>
        simp only [ByteArray.get!, ByteArray.getElem_eq_getElem_data]
        exact getElem!_pos data index inside
    simp [same]
  · rename_i outside
    rw [octets_drop_end bytes (by omega)]
    simp
termination_by bytes.size - index

theorem _root_.ByteArray.toList_eq_data_toList (bytes : ByteArray) :
    bytes.toList = bytes.data.toList := by
  simp [ByteArray.toList, ByteArray.toList_loop_eq]

/-- The packed-buffer entry point: the cursor when `codec` is native all the way
down, the list decoder otherwise. Equal to the list decode (`decodeBytes_eq`). -/
def decodeBytes (codec : StreamCodec alpha) (bytes : ByteArray) : Option alpha :=
  if codec.cursorNative then codec.decodeCursor bytes
  else do
    let (value, suffix) ← codec.decodePrefix bytes.data.toList
    if suffix = [] then some value else none

theorem decodeBytes_eq (codec : StreamCodec alpha) (bytes : ByteArray) :
    codec.decodeBytes bytes = codec.toLawful.decode bytes.toList := by
  rw [ByteArray.toList_eq_data_toList]
  unfold decodeBytes
  split
  · exact codec.decodeCursor_eq bytes
  · rfl

/-- `toLawful` as compiled: a native codec converts the list to a buffer once and
decodes on the cursor; any other runs the list decoder. Same function
(`toLawful_eq_toLawfulCursor`), so no statement about `toLawful` changes. -/
def toLawfulCursor (codec : StreamCodec alpha) : LawfulCodec alpha where
  encode := codec.encode
  decode bytes :=
    if codec.cursorNative then codec.decodeCursor bytes.toByteArray
    else do
      let (value, suffix) ← codec.decodePrefix bytes
      if suffix = [] then some value else none
  decode_encode := by
    intro value
    split
    · rw [codec.decodeCursor_eq, List.toList_data_toByteArray]
      exact codec.toLawful.decode_encode value
    · exact codec.toLawful.decode_encode value

@[csimp] theorem toLawful_eq_toLawfulCursor : @toLawful = @toLawfulCursor := by
  funext alpha codec
  unfold toLawful toLawfulCursor
  congr 1
  funext bytes
  split
  · rw [codec.decodeCursor_eq, List.toList_data_toByteArray]
    rfl
  · rfl

/-- Two codecs with the same functions are the same codec. -/
theorem ext_fields {left right : StreamCodec alpha} (encodes : left.encode = right.encode)
    (decodes : left.decodePrefix = right.decodePrefix) (cursors : left.decodeAt = right.decodeAt)
    (natives : left.cursorNative = right.cursorNative) : left = right := by
  obtain ⟨_, _, _, _, _, _, _, leftWriter, leftWrites⟩ := left
  obtain ⟨_, _, _, _, _, _, _, rightWriter, rightWrites⟩ := right
  cases encodes
  cases decodes
  cases cursors
  cases natives
  have writers : leftWriter = rightWriter :=
    funext fun out => funext fun value => bytes_ext (by rw [leftWrites, rightWrites])
  cases writers
  rfl

/-- Change only the value view of a stream codec. -/
def xmap (codec : StreamCodec alpha) (toWire : beta -> alpha)
    (fromWire : alpha -> beta) (roundtrip : forall value, fromWire (toWire value) = value)
    (wireRoundtrip : forall wire, toWire (fromWire wire) = wire := by xmap_wire_roundtrip) :
    StreamCodec beta where
  encode value := codec.encode (toWire value)
  decodePrefix bytes := do
    let (wire, suffix) ← codec.decodePrefix bytes
    some (fromWire wire, suffix)
  decodePrefix_encode := by
    intro value suffix
    simp [codec.decodePrefix_encode, roundtrip]
  encode_decodePrefix := by
    intro bytes value suffix decoded
    cases accepted : codec.decodePrefix bytes with
    | none => simp [accepted] at decoded
    | some pair =>
        obtain ⟨wire, rest⟩ := pair
        simp only [accepted, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at decoded
        obtain ⟨rfl, rfl⟩ := decoded
        rw [wireRoundtrip]
        exact codec.encode_decodePrefix _ _ _ accepted
  decodeAt bytes start :=
    match codec.decodeAt bytes start with
    | some (wire, next) => some (fromWire wire, next)
    | none => none
  decodeAt_spec := by
    intro bytes start inside
    rw [codec.decodeAt_spec bytes start inside]
    simp only [cursorOfPrefix]
    cases codec.decodePrefix (bytes.data.toList.drop start) <;> rfl
  cursorNative := codec.cursorNative
  encodeInto out value := codec.encodeInto out (toWire value)
  encodeInto_spec out value := codec.encodeInto_spec out (toWire value)

/-- Sequential product; no delimiter is needed because both sides are prefix
decodable. -/
def product (left : StreamCodec alpha) (right : StreamCodec beta) :
    StreamCodec (alpha × beta) where
  encode value := left.encode value.1 ++ right.encode value.2
  decodePrefix bytes := do
    let (first, afterFirst) ← left.decodePrefix bytes
    let (second, suffix) ← right.decodePrefix afterFirst
    some ((first, second), suffix)
  decodePrefix_encode := by
    intro value suffix
    simp [List.append_assoc, left.decodePrefix_encode,
      right.decodePrefix_encode]
  encode_decodePrefix := by
    intro bytes value suffix decoded
    cases firstOk : left.decodePrefix bytes with
    | none => simp [firstOk] at decoded
    | some firstPair =>
      obtain ⟨first, afterFirst⟩ := firstPair
      cases secondOk : right.decodePrefix afterFirst with
      | none => simp [firstOk, secondOk] at decoded
      | some secondPair =>
        obtain ⟨second, rest⟩ := secondPair
        simp only [firstOk, secondOk, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at decoded
        obtain ⟨rfl, rfl⟩ := decoded
        rw [List.append_assoc, right.encode_decodePrefix _ _ _ secondOk,
          left.encode_decodePrefix _ _ _ firstOk]
  decodeAt bytes start :=
    match left.decodeAt bytes start with
    | some (first, afterFirst) =>
        match right.decodeAt bytes afterFirst with
        | some (second, after) => some ((first, second), after)
        | none => none
    | none => none
  decodeAt_spec := by
    intro bytes start inside
    rw [left.decodeAt_spec bytes start inside]
    simp only [cursorOfPrefix]
    cases firstOk : left.decodePrefix (bytes.data.toList.drop start) with
    | none => rfl
    | some firstPair =>
        obtain ⟨first, afterFirst⟩ := firstPair
        have dropped := left.rest_at firstOk
        simp only [Option.map_some]
        rw [right.decodeAt_spec bytes _ (Nat.sub_le _ _)]
        simp only [cursorOfPrefix, dropped]
        cases secondOk : right.decodePrefix afterFirst <;> simp [secondOk]
  cursorNative := left.cursorNative && right.cursorNative
  encodeInto out value := right.encodeInto (left.encodeInto out value.1) value.2
  encodeInto_spec := by
    intro out value
    rw [right.encodeInto_spec, left.encodeInto_spec, List.append_assoc]

/-- Prefix-free binary sum. -/
def sum (left : StreamCodec alpha) (right : StreamCodec beta) :
    StreamCodec (Sum alpha beta) where
  encode
    | .inl value => 0 :: left.encode value
    | .inr value => 1 :: right.encode value
  decodePrefix
    | 0 :: bytes => do
        let (value, suffix) ← left.decodePrefix bytes
        some (.inl value, suffix)
    | 1 :: bytes => do
        let (value, suffix) ← right.decodePrefix bytes
        some (.inr value, suffix)
    | _ => none
  decodePrefix_encode := by
    intro value suffix
    cases value with
    | inl value => simp [left.decodePrefix_encode]
    | inr value => simp [right.decodePrefix_encode]
  encode_decodePrefix := by
    intro bytes value suffix decoded
    rcases bytes with _ | ⟨tag, bytes⟩
    · cases decoded
    by_cases zero : tag = 0
    · subst zero
      cases ok : left.decodePrefix bytes with
      | none => simp [ok] at decoded
      | some pair =>
        obtain ⟨v, rest⟩ := pair
        simp only [ok, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at decoded
        obtain ⟨rfl, rfl⟩ := decoded
        simp [left.encode_decodePrefix _ _ _ ok]
    by_cases one : tag = 1
    · subst one
      cases ok : right.decodePrefix bytes with
      | none => simp [ok] at decoded
      | some pair =>
        obtain ⟨v, rest⟩ := pair
        simp only [ok, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at decoded
        obtain ⟨rfl, rfl⟩ := decoded
        simp [right.encode_decodePrefix _ _ _ ok]
    · simp [zero, one] at decoded
  decodeAt bytes start :=
    if inside : start < bytes.size then
      if bytes[start] = 0 then
        match left.decodeAt bytes (start + 1) with
        | some (value, next) => some (.inl value, next)
        | none => none
      else if bytes[start] = 1 then
        match right.decodeAt bytes (start + 1) with
        | some (value, next) => some (.inr value, next)
        | none => none
      else none
    else none
  decodeAt_spec := by
    intro bytes start fits
    simp only [cursorOfPrefix]
    by_cases inside : start < bytes.size
    · rw [dif_pos inside, octets_drop bytes inside]
      generalize bytes[start] = tag
      by_cases zero : tag = 0
      · subst zero
        rw [if_pos rfl, left.decodeAt_spec bytes _ inside]
        simp only [cursorOfPrefix]
        cases left.decodePrefix (bytes.data.toList.drop (start + 1)) <;> rfl
      by_cases one : tag = 1
      · subst one
        rw [if_neg (by decide), if_pos rfl, right.decodeAt_spec bytes _ inside]
        simp only [cursorOfPrefix]
        cases right.decodePrefix (bytes.data.toList.drop (start + 1)) <;> rfl
      · simp [zero, one]
    · rw [dif_neg inside, octets_drop_end bytes (by omega)]
      rfl
  cursorNative := left.cursorNative && right.cursorNative
  encodeInto
    | out, .inl value => left.encodeInto (out.push 0) value
    | out, .inr value => right.encodeInto (out.push 1) value
  encodeInto_spec := by
    intro out value
    cases value with
    | inl value => simp only [left.encodeInto_spec, push_data, List.append_assoc, List.singleton_append]
    | inr value => simp only [right.encodeInto_spec, push_data, List.append_assoc, List.singleton_append]

/-- Booleans as a one-byte tag. -/
def bool : StreamCodec Bool where
  encode value := [if value then 1 else 0]
  decodePrefix
    | 0 :: suffix => some (false, suffix)
    | 1 :: suffix => some (true, suffix)
    | _ => none
  decodePrefix_encode := by
    intro value suffix
    cases value <;> rfl
  decodeAt bytes start :=
    if inside : start < bytes.size then
      if bytes[start] = 0 then some (false, start + 1)
      else if bytes[start] = 1 then some (true, start + 1)
      else none
    else none
  decodeAt_spec := by
    intro bytes start fits
    simp only [cursorOfPrefix]
    by_cases inside : start < bytes.size
    · rw [dif_pos inside, octets_drop bytes inside]
      generalize bytes[start] = tag
      by_cases zero : tag = 0
      · subst zero
        simp; omega
      by_cases one : tag = 1
      · subst one
        simp; omega
      · simp [zero, one]
    · rw [dif_neg inside, octets_drop_end bytes (by omega)]
      rfl
  cursorNative := true
  encodeInto out value := out.push (if value then 1 else 0)
  encodeInto_spec out value := push_data out _

/-- Optional values, tagged.  `none` costs one byte and `some` costs one byte
plus the payload, so the absent case never has to be encoded as a sentinel
inside the payload's own alphabet. -/
def option (codec : StreamCodec alpha) : StreamCodec (Option alpha) where
  encode
    | none => [0]
    | some value => 1 :: codec.encode value
  decodePrefix
    | [] => none
    | 0 :: suffix => some (none, suffix)
    | 1 :: bytes => do
        let (value, suffix) ← codec.decodePrefix bytes
        some (some value, suffix)
    | _ => none
  decodePrefix_encode := by
    intro value suffix
    cases value with
    | none => rfl
    | some value => simp [codec.decodePrefix_encode]
  encode_decodePrefix := by
    intro bytes value suffix decoded
    rcases bytes with _ | ⟨tag, bytes⟩
    · cases decoded
    by_cases zero : tag = 0
    · subst zero
      simp only [Option.some.injEq, Prod.mk.injEq] at decoded
      obtain ⟨rfl, rfl⟩ := decoded
      rfl
    by_cases one : tag = 1
    · subst one
      cases ok : codec.decodePrefix bytes with
      | none => simp [ok] at decoded
      | some pair =>
        obtain ⟨v, rest⟩ := pair
        simp only [ok, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at decoded
        obtain ⟨rfl, rfl⟩ := decoded
        simp [codec.encode_decodePrefix _ _ _ ok]
    · simp [zero, one] at decoded
  decodeAt bytes start :=
    if inside : start < bytes.size then
      if bytes[start] = 0 then some (none, start + 1)
      else if bytes[start] = 1 then
        match codec.decodeAt bytes (start + 1) with
        | some (value, next) => some (some value, next)
        | none => none
      else none
    else none
  decodeAt_spec := by
    intro bytes start fits
    simp only [cursorOfPrefix]
    by_cases inside : start < bytes.size
    · rw [dif_pos inside, octets_drop bytes inside]
      generalize bytes[start] = tag
      by_cases zero : tag = 0
      · subst zero
        simp; omega
      by_cases one : tag = 1
      · subst one
        rw [if_neg (by decide), if_pos rfl, codec.decodeAt_spec bytes _ inside]
        simp only [cursorOfPrefix]
        cases codec.decodePrefix (bytes.data.toList.drop (start + 1)) <;> rfl
      · simp [zero, one]
    · rw [dif_neg inside, octets_drop_end bytes (by omega)]
      rfl
  cursorNative := codec.cursorNative
  encodeInto
    | out, none => out.push 0
    | out, some value => codec.encodeInto (out.push 1) value
  encodeInto_spec := by
    intro out value
    cases value with
    | none => exact push_data out 0
    | some value => simp only [codec.encodeInto_spec, push_data, List.append_assoc, List.singleton_append]

/-- Whether `expected` sits in `bytes` at `start`, octet by octet. -/
def matchesAt (bytes : ByteArray) : Nat -> List UInt8 -> Bool
  | _, [] => true
  | start, octet :: rest =>
      if inside : start < bytes.size then bytes[start] == octet && matchesAt bytes (start + 1) rest
      else false

theorem matchesAt_iff (bytes : ByteArray) (start : Nat) (expected : List UInt8) :
    matchesAt bytes start expected = true ↔
      (bytes.data.toList.drop start).take expected.length = expected := by
  induction expected generalizing start with
  | nil => simp [matchesAt]
  | cons octet rest ih =>
      by_cases inside : start < bytes.size
      · rw [matchesAt, dif_pos inside, octets_drop bytes inside, List.length_cons,
          List.take_succ_cons, Bool.and_eq_true, beq_iff_eq, ih, List.cons.injEq]
      · rw [matchesAt, dif_neg inside, octets_drop_end bytes (by omega)]
        simp

/-- A fixed octet string (a frame, a magic, a version byte), CHECKED: an input
that does not start with exactly these octets is refused.  A codec that wrote a
constant and decoded it into a discarded value accepted every other constant
too; this is the canonical way to spell one. -/
def literal (expected : List UInt8) : StreamCodec Unit where
  encode _ := expected
  decodePrefix bytes :=
    if bytes.take expected.length = expected then some ((), bytes.drop expected.length) else none
  decodePrefix_encode := by
    intro value suffix
    simp [List.take_left', List.drop_left']
  encode_decodePrefix := by
    intro bytes value suffix decoded
    split at decoded
    · rename_i prefixed
      simp only [Option.some.injEq, Prod.mk.injEq] at decoded
      obtain ⟨-, rfl⟩ := decoded
      conv => rhs; rw [← List.take_append_drop expected.length bytes]
      rw [prefixed]
    · cases decoded
  decodeAt bytes start :=
    if matchesAt bytes start expected then some ((), start + expected.length) else none
  decodeAt_spec := by
    intro bytes start fits
    simp only [cursorOfPrefix]
    by_cases found : matchesAt bytes start expected = true
    · have taken := (matchesAt_iff bytes start expected).mp found
      have long : expected.length ≤ (bytes.data.toList.drop start).length := by
        have lengths := congrArg List.length taken
        rw [List.length_take] at lengths
        omega
      rw [if_pos found, if_pos taken]
      simp only [Option.map_some, List.length_drop, octets_length] at long ⊢
      congr 2
      omega
    · rw [if_neg found, if_neg (fun taken => found ((matchesAt_iff bytes start expected).mpr taken))]
      rfl
  cursorNative := true
  encodeInto out _ := pushOctets out expected
  encodeInto_spec out _ := pushOctets_data out expected

/-- `frame`, checked, then one value. -/
def framed (frame : List UInt8) (codec : StreamCodec alpha) : StreamCodec alpha :=
  xmap (product (literal frame) codec) (fun value => ((), value)) Prod.snd (by intro value; rfl)

theorem framed_encode (frame : List UInt8) (codec : StreamCodec alpha) (value : alpha) :
    (framed frame codec).encode value = frame ++ codec.encode value := rfl

/-- The values `accept` holds of, CHECKED: a decoded value outside it is refused.
A wire with more than one spelling per value (an unsorted list for a set, an
unused tag, a padding field) is made canonical by refining it to the canonical
spellings, never by re-encoding what was decoded. -/
def refine (codec : StreamCodec alpha) (accept : alpha -> Prop) [DecidablePred accept] :
    StreamCodec {value // accept value} where
  encode value := codec.encode value.val
  decodePrefix bytes := do
    let (value, suffix) ← codec.decodePrefix bytes
    if accepted : accept value then some (⟨value, accepted⟩, suffix) else none
  decodePrefix_encode := by
    intro value suffix
    simp [codec.decodePrefix_encode, value.property]
  encode_decodePrefix := by
    intro bytes value suffix decoded
    cases ok : codec.decodePrefix bytes with
    | none => simp [ok] at decoded
    | some pair =>
      obtain ⟨wire, rest⟩ := pair
      by_cases accepted : accept wire
      · simp only [ok, bind, Option.bind, dif_pos accepted, Option.some.injEq,
          Prod.mk.injEq] at decoded
        obtain ⟨rfl, rfl⟩ := decoded
        exact codec.encode_decodePrefix _ _ _ ok
      · simp [ok, accepted] at decoded
  decodeAt bytes start :=
    match codec.decodeAt bytes start with
    | some (value, next) => if accepted : accept value then some (⟨value, accepted⟩, next) else none
    | none => none
  decodeAt_spec := by
    intro bytes start inside
    rw [codec.decodeAt_spec bytes start inside]
    simp only [cursorOfPrefix]
    cases codec.decodePrefix (bytes.data.toList.drop start) with
    | none => rfl
    | some pair =>
        obtain ⟨value, rest⟩ := pair
        by_cases accepted : accept value <;> simp [accepted]
  cursorNative := codec.cursorNative
  encodeInto out value := codec.encodeInto out value.val
  encodeInto_spec out value := codec.encodeInto_spec out value.val

theorem refine_encode (codec : StreamCodec alpha) (accept : alpha -> Prop) [DecidablePred accept]
    (value : {value // accept value}) : (refine codec accept).encode value = codec.encode value.val :=
  rfl

/-- A view whose wire map is only a RETRACTION (`fromWire` is total but not
injective: a tag table with a default arm, a label space wider than the
values). Only the wires that are the spelling of their own value are accepted;
for a tag this is a range check on one small natural. -/
def retract [DecidableEq alpha] (codec : StreamCodec alpha) (toWire : beta -> alpha)
    (fromWire : alpha -> beta) (roundtrip : forall value, fromWire (toWire value) = value) :
    StreamCodec beta :=
  xmap (refine codec (fun wire => toWire (fromWire wire) = wire))
    (fun value => ⟨toWire value, by rw [roundtrip]⟩) (fun wire => fromWire wire.val)
    roundtrip (fun wire => Subtype.ext wire.property)

theorem retract_encode [DecidableEq alpha] (codec : StreamCodec alpha) (toWire : beta -> alpha)
    (fromWire : alpha -> beta) (roundtrip : forall value, fromWire (toWire value) = value)
    (value : beta) : (retract codec toWire fromWire roundtrip).encode value = codec.encode (toWire value) :=
  rfl

def byte : StreamCodec UInt8 where
  encode value := [value]
  decodePrefix
    | [] => none
    | value :: suffix => some (value, suffix)
  decodePrefix_encode := by intro value suffix; rfl
  decodeAt bytes start := if inside : start < bytes.size then some (bytes[start], start + 1) else none
  decodeAt_spec := by
    intro bytes start fits
    simp only [cursorOfPrefix]
    by_cases inside : start < bytes.size
    · rw [dif_pos inside, octets_drop bytes inside]
      simp; omega
    · rw [dif_neg inside, octets_drop_end bytes (by omega)]
      rfl
  cursorNative := true
  encodeInto out value := out.push value
  encodeInto_spec out value := push_data out value

/-! ### Compact naturals and finite sequences

Naturals are base-255 little-endian digits followed by byte `255`.  Payload
digits therefore cannot be mistaken for the terminator, and size is
logarithmic rather than unary. -/

def natDigits (value : Nat) : List UInt8 :=
  (Nat.digits 255 value).map UInt8.ofNat

/-- The compiled codec writes digits seven at a time on machine words
(`NatDigits255Fast.digitsBytes_eq`, for every natural); `natDigits` stays the
definition. -/
@[csimp] theorem natDigits_eq_fast : natDigits = NatDigits255Fast.digitsBytes := by
  funext value
  exact (NatDigits255Fast.digitsBytes_eq value).symm

def encodeNat (value : Nat) : List UInt8 := natDigits value ++ [255]

/-- Canonical: the most significant digit is never zero (`[0, 255]` is not a
second spelling of `0`), so the accepted inputs are exactly the encodings
(`encode_decodeNatPrefix`). -/
def decodeNatPrefix : List UInt8 -> Option (Nat × List UInt8)
  | [] => none
  | byte :: bytes =>
      if byte = 255 then some (0, bytes)
      else do
        let (higher, suffix) ← decodeNatPrefix bytes
        if byte = 0 ∧ higher = 0 then none
        else some (byte.toNat + 255 * higher, suffix)

private theorem toNat_ofNat_small {n : Nat} (small : n < 256) : (UInt8.ofNat n).toNat = n := by
  simp only [UInt8.toNat_ofNat']
  omega

private theorem byte_ne_255_lt {byte : UInt8} (ne : ¬ byte = 255) : byte.toNat < 255 := by
  have lt := byte.toNat_lt
  have ne' : byte.toNat ≠ 255 := by
    intro equal
    exact ne (UInt8.toNat_inj.mp (by simpa using equal))
  omega

/-- One digit, then the higher part: the digits of `low + 255 * high` when the
number is not zero. -/
private theorem encodeNat_digit (low high : Nat) (lowLt : low < 255) (nonzero : low ≠ 0 ∨ high ≠ 0) :
    encodeNat (low + 255 * high) = UInt8.ofNat low :: encodeNat high := by
  unfold encodeNat natDigits
  rw [Nat.digits_add 255 (by decide) low high lowLt nonzero]
  rfl

theorem decodeNatPrefix_encode (value : Nat) (suffix : List UInt8) :
    decodeNatPrefix (encodeNat value ++ suffix) = some (value, suffix) := by
  induction value using Nat.strong_induction_on with
  | _ value ih =>
      by_cases zero : value = 0
      · subst zero
        rfl
      · have split := Nat.mod_add_div value 255
        have lowLt : value % 255 < 255 := Nat.mod_lt _ (by decide)
        have nonzero : value % 255 ≠ 0 ∨ value / 255 ≠ 0 := by omega
        have higherLt : value / 255 < value := Nat.div_lt_self (by omega) (by decide)
        have encoded := encodeNat_digit (value % 255) (value / 255) lowLt nonzero
        rw [split] at encoded
        rw [encoded, List.cons_append]
        have low := toNat_ofNat_small (n := value % 255) (by omega)
        have ne : ¬ UInt8.ofNat (value % 255) = 255 := by
          intro equal
          have := congrArg UInt8.toNat equal
          rw [low] at this
          simp at this
          omega
        have lead : ¬ (UInt8.ofNat (value % 255) = 0 ∧ value / 255 = 0) := by
          rintro ⟨lowZero, high⟩
          have := congrArg UInt8.toNat lowZero
          rw [low] at this
          simp at this
          omega
        simp only [decodeNatPrefix, ne, if_false, ih _ higherLt, bind, Option.bind, lead]
        rw [low, split]

/-- Canonicity of the natural codec: whatever `decodeNatPrefix` accepts is the
encoding of the value it returns, followed by the suffix it returns. -/
theorem encode_decodeNatPrefix (bytes : List UInt8) (value : Nat) (suffix : List UInt8)
    (decoded : decodeNatPrefix bytes = some (value, suffix)) : encodeNat value ++ suffix = bytes := by
  induction bytes generalizing value suffix with
  | nil => cases decoded
  | cons byte bytes ih =>
      by_cases terminator : byte = 255
      · simp only [decodeNatPrefix, terminator, if_true, Option.some.injEq, Prod.mk.injEq] at decoded
        obtain ⟨rfl, rfl⟩ := decoded
        subst terminator
        rfl
      · simp only [decodeNatPrefix, terminator, if_false, bind, Option.bind] at decoded
        split at decoded
        · cases decoded
        · rename_i pair higherOk
          obtain ⟨higher, rest⟩ := pair
          by_cases lead : byte = 0 ∧ higher = 0
          · simp [lead] at decoded
          · simp only [lead, if_false, Option.some.injEq, Prod.mk.injEq] at decoded
            obtain ⟨rfl, rfl⟩ := decoded
            have lowLt := byte_ne_255_lt terminator
            have nonzero : byte.toNat ≠ 0 ∨ higher ≠ 0 := by
              by_cases h : higher = 0
              · left
                intro zero
                exact lead ⟨UInt8.toNat_inj.mp (by simpa using zero), h⟩
              · exact Or.inr h
            rw [encodeNat_digit _ _ lowLt nonzero, List.cons_append, ih _ _ higherOk]
            simp

/-- `decodeNatPrefix` on the cursor: the same digits, read by index. -/
def decodeNatAt (bytes : ByteArray) (start : Nat) : Option (Nat × Nat) :=
  if inside : start < bytes.size then
    let byte := bytes[start]
    if byte = 255 then some (0, start + 1)
    else
      match decodeNatAt bytes (start + 1) with
      | some (higher, next) =>
          if byte = 0 ∧ higher = 0 then none else some (byte.toNat + 255 * higher, next)
      | none => none
  else none
termination_by bytes.size - start

theorem decodeNatAt_spec (bytes : ByteArray) (start : Nat) (fits : start ≤ bytes.size) :
    decodeNatAt bytes start = cursorOfPrefix decodeNatPrefix bytes start := by
  rw [decodeNatAt]
  simp only [cursorOfPrefix]
  by_cases inside : start < bytes.size
  · rw [dif_pos inside, octets_drop bytes inside]
    simp only [decodeNatPrefix]
    by_cases terminator : bytes[start] = 255
    · simp [terminator]; omega
    · simp only [terminator, if_false]
      rw [decodeNatAt_spec bytes (start + 1) inside]
      simp only [cursorOfPrefix]
      cases decodeNatPrefix (bytes.data.toList.drop (start + 1)) with
      | none => rfl
      | some pair =>
          obtain ⟨higher, rest⟩ := pair
          by_cases lead : bytes[start] = 0 ∧ higher = 0 <;> simp [lead]
  · rw [dif_neg inside, octets_drop_end bytes (by omega)]
    rfl
termination_by bytes.size - start

/-- `encodeNat` as a writer: the digits, then the terminator, pushed. -/
def encodeNatInto (out : ByteArray) (value : Nat) : ByteArray :=
  (pushOctets out (natDigits value)).push 255

theorem encodeNatInto_data (out : ByteArray) (value : Nat) :
    (encodeNatInto out value).data.toList = out.data.toList ++ encodeNat value := by
  rw [encodeNatInto, push_data, pushOctets_data, encodeNat, List.append_assoc]

def nat : StreamCodec Nat where
  encode := encodeNat
  decodePrefix := decodeNatPrefix
  decodePrefix_encode := decodeNatPrefix_encode
  encode_decodePrefix := encode_decodeNatPrefix
  decodeAt := decodeNatAt
  decodeAt_spec := decodeNatAt_spec
  cursorNative := true
  encodeInto := encodeNatInto
  encodeInto_spec := encodeNatInto_data

def encodeMany (codec : StreamCodec alpha) : List alpha -> List UInt8
  | [] => []
  | value :: values => codec.encode value ++ encodeMany codec values

/-- `encodeMany` as a writer: each element written after the last. -/
def encodeManyInto (codec : StreamCodec alpha) : ByteArray -> List alpha -> ByteArray
  | out, [] => out
  | out, value :: values => encodeManyInto codec (codec.encodeInto out value) values

theorem encodeManyInto_data (codec : StreamCodec alpha) (out : ByteArray) (values : List alpha) :
    (encodeManyInto codec out values).data.toList = out.data.toList ++ encodeMany codec values := by
  induction values generalizing out with
  | nil => simp [encodeManyInto, encodeMany]
  | cons value values ih =>
      rw [encodeManyInto, ih, codec.encodeInto_spec, encodeMany, List.append_assoc]

def decodeMany (codec : StreamCodec alpha) : Nat -> List UInt8 ->
    Option (List alpha × List UInt8)
  | 0, bytes => some ([], bytes)
  | count + 1, bytes => do
      let (value, afterValue) ← codec.decodePrefix bytes
      let (values, suffix) ← decodeMany codec count afterValue
      some (value :: values, suffix)

theorem decodeMany_encodeMany (codec : StreamCodec alpha)
    (values : List alpha) (suffix : List UInt8) :
    decodeMany codec values.length (encodeMany codec values ++ suffix) =
      some (values, suffix) := by
  induction values with
  | nil => simp [encodeMany, decodeMany]
  | cons value values ih =>
      simp [encodeMany, decodeMany, List.append_assoc,
        codec.decodePrefix_encode, ih]

theorem encodeMany_decodeMany (codec : StreamCodec alpha) (count : Nat) (bytes : List UInt8)
    (values : List alpha) (suffix : List UInt8)
    (decoded : decodeMany codec count bytes = some (values, suffix)) :
    values.length = count ∧ encodeMany codec values ++ suffix = bytes := by
  induction count generalizing bytes values suffix with
  | zero =>
      simp only [decodeMany, Option.some.injEq, Prod.mk.injEq] at decoded
      obtain ⟨rfl, rfl⟩ := decoded
      exact ⟨rfl, rfl⟩
  | succ count ih =>
      cases valueOk : codec.decodePrefix bytes with
      | none => simp [decodeMany, valueOk] at decoded
      | some pair =>
        obtain ⟨value, afterValue⟩ := pair
        cases restOk : decodeMany codec count afterValue with
        | none => simp [decodeMany, valueOk, restOk] at decoded
        | some rest =>
          obtain ⟨tail, rest⟩ := rest
          simp only [decodeMany, valueOk, restOk, bind, Option.bind, Option.some.injEq,
            Prod.mk.injEq] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          obtain ⟨length, encoded⟩ := ih _ _ _ restOk
          refine ⟨by simp [length], ?_⟩
          rw [encodeMany, List.append_assoc, encoded, codec.encode_decodePrefix _ _ _ valueOk]

/-- `decodeMany` on the cursor, tail-recursive (the values gather reversed). -/
def decodeManyAt (codec : StreamCodec alpha) (bytes : ByteArray) :
    Nat -> Nat -> List alpha -> Option (List alpha × Nat)
  | 0, start, acc => some (acc.reverse, start)
  | count + 1, start, acc =>
      match codec.decodeAt bytes start with
      | some (value, next) => decodeManyAt codec bytes count next (value :: acc)
      | none => none

theorem decodeManyAt_spec (codec : StreamCodec alpha) (bytes : ByteArray) (count start : Nat)
    (acc : List alpha) (fits : start ≤ bytes.size) :
    decodeManyAt codec bytes count start acc =
      (decodeMany codec count (bytes.data.toList.drop start)).map
        fun result => (acc.reverse ++ result.1, bytes.size - result.2.length) := by
  induction count generalizing start acc with
  | zero => simp [decodeManyAt, decodeMany]; omega
  | succ count ih =>
      rw [decodeManyAt, codec.decodeAt_spec bytes start fits]
      simp only [cursorOfPrefix, decodeMany]
      cases valueOk : codec.decodePrefix (bytes.data.toList.drop start) with
      | none => rfl
      | some pair =>
          obtain ⟨value, rest⟩ := pair
          simp only [Option.map_some]
          rw [ih _ _ (Nat.sub_le _ _), codec.rest_at valueOk]
          cases restOk : decodeMany codec count rest <;> simp [restOk]

def list (codec : StreamCodec alpha) : StreamCodec (List alpha) where
  encode values := nat.encode values.length ++ encodeMany codec values
  decodePrefix bytes := do
    let (count, afterCount) ← nat.decodePrefix bytes
    decodeMany codec count afterCount
  decodePrefix_encode := by
    intro values suffix
    simp [List.append_assoc, nat.decodePrefix_encode,
      decodeMany_encodeMany]
  encode_decodePrefix := by
    intro bytes values suffix decoded
    cases countOk : nat.decodePrefix bytes with
    | none => simp [countOk] at decoded
    | some pair =>
      obtain ⟨count, afterCount⟩ := pair
      simp only [countOk, bind, Option.bind] at decoded
      obtain ⟨length, encoded⟩ := encodeMany_decodeMany codec _ _ _ _ decoded
      rw [List.append_assoc, encoded, length]
      exact nat.encode_decodePrefix _ _ _ countOk
  decodeAt bytes start :=
    match decodeNatAt bytes start with
    | some (count, afterCount) => decodeManyAt codec bytes count afterCount []
    | none => none
  decodeAt_spec := by
    intro bytes start inside
    rw [decodeNatAt_spec bytes start inside]
    simp only [cursorOfPrefix, nat]
    cases countOk : decodeNatPrefix (bytes.data.toList.drop start) with
    | none => rfl
    | some pair =>
        obtain ⟨count, afterCount⟩ := pair
        simp only [Option.map_some]
        rw [decodeManyAt_spec codec bytes _ _ [] (Nat.sub_le _ _), nat.rest_at countOk]
        cases manyOk : decodeMany codec count afterCount <;> simp [manyOk]
  cursorNative := codec.cursorNative
  encodeInto out values := encodeManyInto codec (encodeNatInto out values.length) values
  encodeInto_spec := by
    intro out values
    rw [encodeManyInto_data, encodeNatInto_data, List.append_assoc]
    try rfl

end StreamCodec

/-- The cursor of a decoder that reads one tag octet and nothing after it (a
namespace tag): the list decoder runs on that one octet. -/
def tagCursor {α : Type} (decode : List UInt8 → Option (α × List UInt8)) (bytes : ByteArray)
    (start : Nat) : Option (α × Nat) :=
  if inside : start < bytes.size then
    match decode [bytes[start]] with
    | some (value, _) => some (value, start + 1)
    | none => none
  else none

theorem tagCursor_spec {α : Type} (decode : List UInt8 → Option (α × List UInt8))
    (empty : decode [] = none)
    (oneOctet : ∀ tag rest, decode (tag :: rest) = (decode [tag]).map fun result => (result.1, rest))
    (bytes : ByteArray) (start : Nat) (fits : start ≤ bytes.size) :
    tagCursor decode bytes start = cursorOfPrefix decode bytes start := by
  unfold tagCursor cursorOfPrefix
  by_cases inside : start < bytes.size
  · rw [dif_pos inside, StreamCodec.octets_drop bytes inside,
      oneOctet bytes[start] (bytes.data.toList.drop (start + 1))]
    cases decode [bytes[start]] with
    | none => rfl
    | some pair =>
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
        rw [List.length_drop, StreamCodec.octets_length]
        omega
  · rw [dif_neg inside, StreamCodec.octets_drop_end bytes (by omega), empty]
    rfl

/-- A one-octet tag codec, decoding natively on the cursor. -/
def withTagCursor {α : Type} (codec : StreamCodec α) (empty : codec.decodePrefix [] = none)
    (oneOctet : ∀ tag rest, codec.decodePrefix (tag :: rest) =
      (codec.decodePrefix [tag]).map fun result => (result.1, rest)) : StreamCodec α :=
  { codec with
    decodeAt := tagCursor codec.decodePrefix
    decodeAt_spec := tagCursor_spec codec.decodePrefix empty oneOctet
    cursorNative := true }

set_option hygiene false in
/-- Discharges `withTagCursor`'s `oneOctet` for a decoder that matches one literal
tag octet per arm (`| 3 :: suffix => some (.c, suffix)`) and refuses the rest:
each arm's answer does not depend on what follows the tag. -/
macro "one_octet_tag" : tactic => `(tactic| (
  intro tag rest
  dsimp only
  split
  all_goals first
    | (rename_i same; injection same with tagSame restSame; subst tagSame; subst restSame; rfl)
    | (split <;> rename_i same <;> simp at same <;> simp_all)))


namespace StreamCodec

/-- A natural below `size`, CHECKED: the natural's bytes, and a decoded natural at or above
`size` is refused. -/
def fin (size : Nat) : StreamCodec (Fin size) :=
  xmap (refine nat (· < size)) (fun index => ⟨index.val, index.isLt⟩)
    (fun wire => ⟨wire.val, wire.property⟩) (by intro index; rfl) (by intro wire; rfl)

theorem fin_encode (size : Nat) (index : Fin size) : (fin size).encode index = nat.encode index.val :=
  rfl

end StreamCodec

/-! ## Primitive and controller-record codecs -/

def digestStream : StreamCodec Digest :=
  StreamCodec.xmap StreamCodec.nat (fun digest => digest.value)
    Digest.mk (by intro digest; cases digest; rfl)

/-! ### Fixed-width streams

`StreamCodec.nat` is a variable-length base-255 number, so a 256-bit value is 32
OR 33 octets: the length of a record that carries digests depends on their
values. A record whose length is CHARGED must not have that property
(`Kernel.ObjectiveActivity.storageDeposit`), so its digests and heights go
through these: exactly `width` octets, little-endian, always. A value is a
`Fin (256 ^ width)`, so the codec is total and lawful on its own type and no
out-of-range value exists to be encoded. -/

/-- The low `width` octets of `value`, little-endian. Always exactly `width` long. -/
def fixedOctets (width value : Nat) : List UInt8 :=
  (Minidregg.Theory.Bignum.digitsLE 256 width value).map UInt8.ofNat

@[simp] theorem fixedOctets_length (width value : Nat) :
    (fixedOctets width value).length = width := by
  simp [fixedOctets]

/-- The number `octets` spell, little-endian. -/
def fixedValue (octets : List UInt8) : Nat :=
  Minidregg.Theory.Bignum.denoteNat 256 (octets.map UInt8.toNat)

theorem fixedValue_lt (octets : List UInt8) : fixedValue octets < 256 ^ octets.length := by
  have bound := Minidregg.Theory.Bignum.denoteNat_lt_pow (octets.map UInt8.toNat)
    (by
      intro digit member
      rcases List.mem_map.mp member with ⟨byte, _, rfl⟩
      exact byte.toNat_lt)
  simpa [fixedValue] using bound

theorem fixedValue_fixedOctets (width value : Nat) (fits : value < 256 ^ width) :
    fixedValue (fixedOctets width value) = value := by
  unfold fixedValue fixedOctets
  have same : (Minidregg.Theory.Bignum.digitsLE 256 width value).map (fun digit => (UInt8.ofNat digit).toNat) =
      Minidregg.Theory.Bignum.digitsLE 256 width value := by
    have congr := List.map_congr_left (l := Minidregg.Theory.Bignum.digitsLE 256 width value)
      (f := fun digit => (UInt8.ofNat digit).toNat) (g := id)
      (fun digit member => UInt8.toNat_ofNat_of_lt
        (Minidregg.Theory.Bignum.digitsLE_ranged (by decide) width value digit member))
    simpa only [List.map_id, id_eq] using congr
  rw [List.map_map]
  change Minidregg.Theory.Bignum.denoteNat 256 ((Minidregg.Theory.Bignum.digitsLE 256 width value).map
    (fun digit => (UInt8.ofNat digit).toNat)) = value
  rw [same]
  exact Minidregg.Theory.Bignum.denoteNat_digitsLE (by decide) width value fits

/-- `width` octets spell one value, and that value is spelled by exactly those
octets: the fixed codec has one spelling per value. -/
theorem fixedOctets_fixedValue (octets : List UInt8) :
    fixedOctets octets.length (fixedValue octets) = octets := by
  unfold fixedOctets fixedValue
  have ranged : Minidregg.Theory.Bignum.Ranged 256 (octets.map UInt8.toNat) := by
    intro digit member
    rcases List.mem_map.mp member with ⟨byte, _, rfl⟩
    exact byte.toNat_lt
  have digits := Minidregg.Theory.Bignum.digitsLE_denoteNat (base := 256) (by decide)
    (octets.map UInt8.toNat) ranged
  rw [List.length_map] at digits
  rw [digits, List.map_map]
  conv => rhs; rw [← List.map_id octets]
  apply List.map_congr_left
  intro byte _
  simp

theorem denoteNat_append (base : Nat) (front back : List Nat) :
    Minidregg.Theory.Bignum.denoteNat base (front ++ back) =
      Minidregg.Theory.Bignum.denoteNat base front +
        base ^ front.length * Minidregg.Theory.Bignum.denoteNat base back := by
  induction front with
  | nil => simp [Minidregg.Theory.Bignum.denoteNat]
  | cons digit front ih =>
      simp only [List.cons_append, Minidregg.Theory.Bignum.denoteNat, ih, List.length_cons]
      ring

/-- The little-endian value of `width` octets at `start`, digit by digit. Used for
at most seven octets, so every intermediate is below `2 ^ 56` (machine arithmetic). -/
def smallValueAt (bytes : ByteArray) (start : Nat) :
    (width : Nat) -> start + width ≤ bytes.size -> Nat
  | 0, _ => 0
  | width + 1, fits =>
      (bytes[start]'(by omega)).toNat + 256 * smallValueAt bytes (start + 1) width (by omega)

theorem smallValueAt_eq (bytes : ByteArray) (start width : Nat) (fits : start + width ≤ bytes.size) :
    smallValueAt bytes start width fits = fixedValue ((bytes.data.toList.drop start).take width) := by
  induction width generalizing start with
  | zero => simp [smallValueAt, fixedValue]
  | succ width ih =>
      rw [smallValueAt, ih, StreamCodec.octets_drop bytes (by omega : start < bytes.size)]
      simp [fixedValue]

/-- The little-endian value of `width` octets at `start`, seven octets per step: each
seven-octet chunk is assembled in machine arithmetic and only one big multiply-add per
chunk touches the bignum (a 256-bit digest: four, not thirty-two). -/
def fixedValueAt (bytes : ByteArray) (start width : Nat) (fits : start + width ≤ bytes.size) : Nat :=
  if seven : 7 ≤ width then
    smallValueAt bytes start 7 (by omega) +
      fixedValueAt bytes (start + 7) (width - 7) (by omega) <<< 56
  else smallValueAt bytes start width fits
termination_by width

theorem fixedValueAt_eq (bytes : ByteArray) (start width : Nat) (fits : start + width ≤ bytes.size) :
    fixedValueAt bytes start width fits = fixedValue ((bytes.data.toList.drop start).take width) := by
  rw [fixedValueAt]
  split
  · rename_i seven
    rw [fixedValueAt_eq bytes (start + 7) (width - 7), smallValueAt_eq]
    obtain ⟨rest, rfl⟩ : ∃ rest, width = 7 + rest := ⟨width - 7, by omega⟩
    have long : 7 ≤ (bytes.data.toList.drop start).length := by
      rw [List.length_drop, StreamCodec.octets_length]
      omega
    have dropped : (bytes.data.toList.drop start).drop 7 = bytes.data.toList.drop (start + 7) := by
      rw [List.drop_drop]
    rw [List.take_add, dropped]
    simp only [fixedValue, List.map_append, denoteNat_append, List.length_map, List.length_take,
      Nat.min_eq_left long, Nat.add_sub_cancel_left, Nat.shiftLeft_eq]
    (norm_num; ring)
  · exact smallValueAt_eq bytes start width fits
termination_by width

theorem fixedValueAt_lt (bytes : ByteArray) (start width : Nat) (fits : start + width ≤ bytes.size) :
    fixedValueAt bytes start width fits < 256 ^ width := by
  rw [fixedValueAt_eq]
  have bound := fixedValue_lt ((bytes.data.toList.drop start).take width)
  have long : width ≤ (bytes.data.toList.drop start).length := by
    rw [List.length_drop, StreamCodec.octets_length]
    omega
  rwa [List.length_take, Nat.min_eq_left long] at bound

/-- Exactly `width` octets, strict: a shorter input is refused, and every input of
at least `width` octets spells exactly one value. -/
def fixedStream (width : Nat) : StreamCodec (Fin (256 ^ width)) where
  encode value := fixedOctets width value.val
  decodePrefix octets :=
    if enough : width ≤ octets.length then
      some (⟨fixedValue (octets.take width), by
        have bound := fixedValue_lt (octets.take width)
        simpa [List.length_take, Nat.min_eq_left enough] using bound⟩, octets.drop width)
    else none
  decodePrefix_encode := by
    intro value suffix
    have enough : width ≤ (fixedOctets width value.val ++ suffix).length := by
      simp
    have taken : (fixedOctets width value.val ++ suffix).take width = fixedOctets width value.val :=
      List.take_left' (fixedOctets_length _ _)
    have dropped : (fixedOctets width value.val ++ suffix).drop width = suffix :=
      List.drop_left' (fixedOctets_length _ _)
    simp only [enough, dif_pos, taken, dropped]
    exact congrArg (fun v : Fin (256 ^ width) => some (v, suffix)) (Fin.ext (fixedValue_fixedOctets width value.val value.isLt))
  encode_decodePrefix := by
    intro octets value suffix decoded
    split at decoded
    · rename_i enough
      simp only [Option.some.injEq, Prod.mk.injEq] at decoded
      obtain ⟨rfl, rfl⟩ := decoded
      have length : (octets.take width).length = width := by
        simp [List.length_take, Nat.min_eq_left enough]
      have spelled := fixedOctets_fixedValue (octets.take width)
      rw [length] at spelled
      simp only [spelled, List.take_append_drop]
    · cases decoded
  decodeAt bytes start :=
    if fits : start + width ≤ bytes.size then
      some (⟨fixedValueAt bytes start width fits, fixedValueAt_lt bytes start width fits⟩, start + width)
    else none
  decodeAt_spec := by
    intro bytes start inside
    simp only [cursorOfPrefix]
    have length : (bytes.data.toList.drop start).length = bytes.size - start := by
      rw [List.length_drop, StreamCodec.octets_length]
    by_cases fits : start + width ≤ bytes.size
    · have enough : width ≤ (bytes.data.toList.drop start).length := by omega
      rw [dif_pos fits, dif_pos enough]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      refine ⟨Fin.ext (fixedValueAt_eq bytes start width fits), ?_⟩
      rw [List.length_drop, length]
      omega
    · have short : ¬ width ≤ (bytes.data.toList.drop start).length := by omega
      rw [dif_neg fits, dif_neg short]
      rfl
  cursorNative := true

/-- Executable `fixedStream` decode: split off `width` octets and check that the PREFIX came
out whole. The definition measures `octets.length`, the WHOLE remaining stream, once per
fixed-width field, so a record of `m` digests and heights in `n` octets decoded in
`O(m·n)`; this costs `O(width)` per field, independent of what follows. -/
def fixedDecodePrefixTR (width : Nat) (octets : List UInt8) :
    Option (Fin (256 ^ width) × List UInt8) :=
  let split := octets.splitAt width
  if whole : split.1.length = width then
    some (⟨fixedValue split.1, by
      have bound := fixedValue_lt split.1
      rwa [whole] at bound⟩, split.2)
  else none

theorem fixedDecodePrefixTR_eq (width : Nat) (octets : List UInt8) :
    fixedDecodePrefixTR width octets = (fixedStream width).decodePrefix octets := by
  unfold fixedDecodePrefixTR fixedStream
  simp only [List.splitAt_eq, List.length_take]
  by_cases enough : width ≤ octets.length
  · simp [enough]
  · have short : min width octets.length ≠ width := by omega
    simp [enough, short]

/-- `fixedStream` with the bounded-take decoder; same encoder, same bytes. -/
def fixedStreamTR (width : Nat) : StreamCodec (Fin (256 ^ width)) where
  encode value := fixedOctets width value.val
  decodePrefix := fixedDecodePrefixTR width
  decodePrefix_encode := by
    intro value suffix
    rw [fixedDecodePrefixTR_eq]
    exact (fixedStream width).decodePrefix_encode value suffix
  encode_decodePrefix := by
    intro octets value suffix decoded
    rw [fixedDecodePrefixTR_eq] at decoded
    exact (fixedStream width).encode_decodePrefix octets value suffix decoded
  decodeAt := (fixedStream width).decodeAt
  decodeAt_spec := by
    intro bytes start inside
    rw [(fixedStream width).decodeAt_spec bytes start inside]
    simp only [cursorOfPrefix, fixedDecodePrefixTR_eq]
  cursorNative := true

@[csimp] theorem fixedStream_eq_fixedStreamTR : @fixedStream = @fixedStreamTR := by
  funext width
  exact StreamCodec.ext_fields rfl (funext fun octets => (fixedDecodePrefixTR_eq width octets).symm)
    rfl rfl

theorem fixedStream_encode_length (width : Nat) (value : Fin (256 ^ width)) :
    ((fixedStream width).encode value).length = width := fixedOctets_length _ _

/-- A short input is refused, by name: the decoder never pads. -/
theorem fixedStream_refuses_short (width : Nat) (octets : List UInt8)
    (short : octets.length < width) : (fixedStream width).decodePrefix octets = none := by
  simp [fixedStream, Nat.not_le.mpr short]

/-- A 256-bit digest: exactly 32 octets (the cSHAKE output width). -/
abbrev Digest256 := Fin (256 ^ 32)

/-- A height: exactly 8 octets. -/
abbrev Height64 := Fin (256 ^ 8)

def digest256Stream : StreamCodec Digest256 := fixedStream 32

def height64Stream : StreamCodec Height64 := fixedStream 8

/-- A digest below `256 ^ 32` as a 256-bit value. The bound is an argument: a wider digest has
no such view (nothing is reduced). Every hash output is below it
(`Kernel.ObjectiveActivityWire.tagged_lt`). -/
def toDigest256 (digest : Digest) (fits : digest.value < 256 ^ 32) : Digest256 := ⟨digest.value, fits⟩

def ofDigest256 (value : Digest256) : Digest := ⟨value.val⟩

theorem ofDigest256_toDigest256 (digest : Digest) (fits : digest.value < 256 ^ 32) :
    ofDigest256 (toDigest256 digest fits) = digest := by
  cases digest; rfl

theorem toDigest256_ofDigest256 (value : Digest256) :
    toDigest256 (ofDigest256 value) value.isLt = value := rfl

theorem ofDigest256_lt (value : Digest256) : (ofDigest256 value).value < 256 ^ 32 := value.isLt

/-- A height below `256 ^ 8` as an 8-octet value; the bound is an argument (nothing is reduced). -/
def toHeight64 (height : Nat) (fits : height < 256 ^ 8) : Height64 := ⟨height, fits⟩

theorem toHeight64_val (height : Nat) (fits : height < 256 ^ 8) : (toHeight64 height fits).val = height := rfl

/-- The defect, witnessed on the VARIABLE codec: a 256-bit value and a 240-bit one are spelled in
different numbers of octets, so a record carrying them has a length that depends on the value. -/
theorem nat_width_varies :
    (StreamCodec.nat.encode (2 ^ 256 - 1)).length ≠ (StreamCodec.nat.encode (2 ^ 240)).length := by
  decide +kernel

/-- The fixed codec spells the same two values in the same 32 octets. -/
theorem digest256_width_constant (digest digest' : Digest256) :
    (digest256Stream.encode digest).length = (digest256Stream.encode digest').length := by
  unfold digest256Stream
  rw [fixedStream_encode_length, fixedStream_encode_length]

/-- A short input is refused by name: `digest256Stream` never pads and never reads a 33rd octet. -/
theorem digest256_refuses_short (octets : List UInt8) (short : octets.length < 32) :
    digest256Stream.decodePrefix octets = none := fixedStream_refuses_short 32 octets short

/-- Every digest the decoder yields consumed exactly 32 octets. -/
theorem digest256_consumes_32 (octets : List UInt8) (digest : Digest256) (rest : List UInt8)
    (decoded : digest256Stream.decodePrefix octets = some (digest, rest)) :
    rest = octets.drop 32 := by
  unfold digest256Stream fixedStream at decoded
  simp only at decoded
  split at decoded
  · simp only [Option.some.injEq, Prod.mk.injEq] at decoded
    exact decoded.2.symm
  · cases decoded

#assert_axioms fixedStream_encode_length
#assert_axioms fixedStream_refuses_short
#assert_axioms nat_width_varies
#assert_axioms digest256_width_constant
#assert_axioms digest256_refuses_short
#assert_axioms digest256_consumes_32
#assert_axioms toDigest256_ofDigest256
#assert_axioms fixedStream_eq_fixedStreamTR
#assert_axioms ofDigest256_toDigest256
#assert_axioms StreamCodec.decodeCursor_eq
#assert_axioms StreamCodec.decodeBytes_eq
#assert_axioms StreamCodec.toLawful_eq_toLawfulCursor
#assert_axioms StreamCodec.decodeNatAt_spec
#assert_axioms StreamCodec.decodeManyAt_spec
#assert_axioms StreamCodec.matchesAt_iff
#assert_axioms fixedValueAt_eq
#assert_axioms StreamCodec.encode_eq_encodeViaWriter
/-- The byte specialization of `StreamCodec.encodeMany` has no per-byte
framing. Keep this equality explicit so the faster implementation below stays
on the existing wire format. -/
theorem encodeMany_byte (values : List UInt8) :
    StreamCodec.encodeMany StreamCodec.byte values = values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      change [value] ++ StreamCodec.encodeMany StreamCodec.byte values = value :: values
      simpa only [List.singleton_append] using congrArg (value :: ·) ih

/-- Unlike the general element decoder, a byte consumes exactly one input
byte. Splitting once uses the tail-recursive list implementation. -/
def decodeBytesPrefix (count : Nat) (bytes : List UInt8) :
    Option (List UInt8 × List UInt8) :=
  if count ≤ bytes.length then some (bytes.splitAt count) else none

/-- Executable `decodeBytesPrefix`: split first, then check the prefix came out
whole. The definition measures `bytes.length`, the WHOLE remaining stream, once
per length-prefixed field, so decoding a stream of `k` frames walked the stream
`k` times (an append-only agreement journal of 100 000 frames never finished
reopening). This costs `count` steps, independent of what follows. -/
def decodeBytesPrefixTR (count : Nat) (bytes : List UInt8) :
    Option (List UInt8 × List UInt8) :=
  let split := bytes.splitAt count
  if split.1.length = count then some split else none

@[csimp] theorem decodeBytesPrefix_eq_decodeBytesPrefixTR :
    @decodeBytesPrefix = @decodeBytesPrefixTR := by
  funext count bytes
  simp only [decodeBytesPrefix, decodeBytesPrefixTR, List.splitAt_eq, List.length_take]
  by_cases fits : count ≤ bytes.length
  · simp [fits]
  · have short : min count bytes.length ≠ count := by omega
    simp [fits, short]

theorem decodeMany_byte (count : Nat) (bytes : List UInt8) :
    StreamCodec.decodeMany StreamCodec.byte count bytes =
      decodeBytesPrefix count bytes := by
  induction count generalizing bytes with
  | zero => simp [StreamCodec.decodeMany, decodeBytesPrefix, List.splitAt_eq]
  | succ count ih =>
      cases bytes with
      | nil => simp [StreamCodec.decodeMany, StreamCodec.byte, decodeBytesPrefix]
      | cons value bytes =>
          rw [StreamCodec.decodeMany]
          have tail := ih bytes
          simp only [StreamCodec.byte] at tail
          simp [StreamCodec.byte, tail, decodeBytesPrefix, List.splitAt_eq]
          split_ifs <;> simp_all

/-- `count` octets of `bytes` from `start`, consed from the end onto `acc`: one
cell per octet and nothing else allocated. -/
def sliceOnto (bytes : ByteArray) (start : Nat) :
    (count : Nat) -> start + count ≤ bytes.size -> List UInt8 -> List UInt8
  | 0, _, acc => acc
  | count + 1, fits, acc =>
      sliceOnto bytes start count (by omega) (bytes[start + count]'(by omega) :: acc)

theorem sliceOnto_eq (bytes : ByteArray) (start count : Nat) (fits : start + count ≤ bytes.size)
    (acc : List UInt8) :
    sliceOnto bytes start count fits acc = (bytes.data.toList.drop start).take count ++ acc := by
  induction count generalizing acc with
  | zero => simp [sliceOnto]
  | succ count ih =>
      rw [sliceOnto, ih, List.take_add_one]
      have inside : start + count < bytes.data.size := by
        rw [ByteArray.size_data]
        omega
      have octet : (bytes.data.toList.drop start)[count]? = some bytes[start + count] := by
        rw [List.getElem?_drop, Array.getElem?_toList, Array.getElem?_eq_getElem inside,
          ByteArray.getElem_eq_getElem_data]
      simp only [octet, Option.toList_some, List.append_assoc, List.singleton_append]

/-- Same length-prefixed bytes as `StreamCodec.list StreamCodec.byte`, with
one list split instead of one recursive codec call per payload byte. -/
def bytesStream : StreamCodec (List UInt8) where
  encode values := StreamCodec.nat.encode values.length ++ values
  decodePrefix bytes := do
    let (count, afterCount) ← StreamCodec.nat.decodePrefix bytes
    decodeBytesPrefix count afterCount
  decodePrefix_encode := by
    intro values suffix
    have old := (StreamCodec.list StreamCodec.byte).decodePrefix_encode values suffix
    simpa [StreamCodec.list, encodeMany_byte, decodeMany_byte] using old
  encode_decodePrefix := by
    intro bytes values suffix decoded
    have old := (StreamCodec.list StreamCodec.byte).encode_decodePrefix bytes values suffix
      (by simpa [StreamCodec.list, decodeMany_byte] using decoded)
    simpa [StreamCodec.list, encodeMany_byte] using old
  decodeAt bytes start :=
    match StreamCodec.decodeNatAt bytes start with
    | some (count, afterCount) =>
        if fits : afterCount + count ≤ bytes.size then
          some (sliceOnto bytes afterCount count fits [], afterCount + count)
        else none
    | none => none
  decodeAt_spec := by
    intro bytes start inside
    rw [StreamCodec.decodeNatAt_spec bytes start inside]
    simp only [cursorOfPrefix, StreamCodec.nat]
    cases countOk : StreamCodec.decodeNatPrefix (bytes.data.toList.drop start) with
    | none => rfl
    | some pair =>
        obtain ⟨count, rest⟩ := pair
        have dropped := StreamCodec.nat.rest_at countOk
        have restLength : rest.length ≤ bytes.size := by
          have lengths := congrArg List.length dropped
          rw [List.length_drop, StreamCodec.octets_length] at lengths
          omega
        simp only [Option.map_some]
        by_cases fits : bytes.size - rest.length + count ≤ bytes.size
        · have enough : count ≤ rest.length := by omega
          have split : decodeBytesPrefix count rest = some (rest.take count, rest.drop count) := by
            simp [decodeBytesPrefix, enough, List.splitAt_eq]
          rw [dif_pos fits, sliceOnto_eq, dropped, List.append_nil]
          simp [split]; omega
        · have short : ¬ count ≤ rest.length := by omega
          rw [dif_neg fits]
          simp [decodeBytesPrefix, short]
  cursorNative := true
  encodeInto out values := pushOctets (StreamCodec.encodeNatInto out values.length) values
  encodeInto_spec := by
    intro out values
    rw [pushOctets_data, StreamCodec.encodeNatInto_data, List.append_assoc]
    try rfl

theorem bytesStream_encode_eq_list_byte (values : List UInt8) :
    bytesStream.encode values = (StreamCodec.list StreamCodec.byte).encode values := by
  simp [bytesStream, StreamCodec.list, encodeMany_byte]

theorem bytesStream_decodePrefix_eq_list_byte (bytes : List UInt8) :
    bytesStream.decodePrefix bytes =
      (StreamCodec.list StreamCodec.byte).decodePrefix bytes := by
  simp [bytesStream, StreamCodec.list, decodeMany_byte]

#assert_axioms sliceOnto_eq

def merklePathStream : StreamCodec (List Digest) :=
  StreamCodec.list digestStream

def merklePathCodec : LawfulCodec (List Digest) :=
  merklePathStream.toLawful

def drawRoleStream : StreamCodec DrawRole :=
  withTagCursor
  { encode := fun
      | .roundChallenge => [0]
      | .queryChallenge => [1]
    decodePrefix := fun
      | 0 :: suffix => some (.roundChallenge, suffix)
      | 1 :: suffix => some (.queryChallenge, suffix)
      | _ => none
    decodePrefix_encode := by intro value suffix; cases value <;> rfl }
    rfl (by one_octet_tag)

def columnRoleStream : StreamCodec ColumnRole :=
  withTagCursor
  { encode := fun
      | .semanticTrace => [0]
      | .lookupAddress => [1]
      | .lookupWeight => [2]
      | .lookupTable => [3]
      | .accumulator => [4]
      | .checkpoint => [5]
      | .auxiliary => [6]
    decodePrefix := fun
      | 0 :: suffix => some (.semanticTrace, suffix)
      | 1 :: suffix => some (.lookupAddress, suffix)
      | 2 :: suffix => some (.lookupWeight, suffix)
      | 3 :: suffix => some (.lookupTable, suffix)
      | 4 :: suffix => some (.accumulator, suffix)
      | 5 :: suffix => some (.checkpoint, suffix)
      | 6 :: suffix => some (.auxiliary, suffix)
      | _ => none
    decodePrefix_encode := by intro value suffix; cases value <;> rfl }
    rfl (by one_octet_tag)

def reprEqRoleStream : StreamCodec ReprEqRole :=
  withTagCursor
  { encode := fun
      | .representationEquality => [0]
      | .sameOpening => [1]
    decodePrefix := fun
      | 0 :: suffix => some (.representationEquality, suffix)
      | 1 :: suffix => some (.sameOpening, suffix)
      | _ => none
    decodePrefix_encode := by intro value suffix; cases value <;> rfl }
    rfl (by one_octet_tag)

def workKindStream : StreamCodec WorkKind :=
  withTagCursor
  { encode := fun
      | .arithmetic => [0]
      | .hash => [1]
      | .transform => [2]
    decodePrefix := fun
      | 0 :: suffix => some (.arithmetic, suffix)
      | 1 :: suffix => some (.hash, suffix)
      | 2 :: suffix => some (.transform, suffix)
      | _ => none
    decodePrefix_encode := by intro value suffix; cases value <;> rfl }
    rfl (by one_octet_tag)

abbrev RootSlotWire :=
  Digest × ColumnRole × Digest × Digest × Digest × Digest × Digest ×
    Digest × Digest × Digest

def rootSlotWireStream : StreamCodec RootSlotWire :=
  StreamCodec.product digestStream
    (StreamCodec.product columnRoleStream
      (StreamCodec.product digestStream
        (StreamCodec.product digestStream
          (StreamCodec.product digestStream
            (StreamCodec.product digestStream
              (StreamCodec.product digestStream
                (StreamCodec.product digestStream
                  (StreamCodec.product digestStream digestStream))))))))

def rootSlotStream : StreamCodec RootSlot :=
  StreamCodec.xmap rootSlotWireStream
    (fun slot => (slot.slotId, slot.role, slot.semanticTypeId,
      slot.representationId, slot.carrierProfileId, slot.semanticCodecId,
      slot.representationCodecId, slot.domainId, slot.domainCodecId,
      slot.commitmentSuiteId))
    (fun (slotId, role, semanticTypeId, representationId, carrierProfileId,
        semanticCodecId, representationCodecId, domainId, domainCodecId,
        commitmentSuiteId) =>
      ⟨slotId, role, semanticTypeId, representationId, carrierProfileId,
       semanticCodecId, representationCodecId, domainId, domainCodecId,
       commitmentSuiteId⟩)
    (by intro slot; cases slot; rfl)

def rootRecordStream : StreamCodec RootRecord :=
  StreamCodec.xmap (StreamCodec.product rootSlotStream digestStream)
    (fun record => (record.slot, record.root))
    (fun (slot, root) => ⟨slot, root⟩)
    (by intro record; cases record; rfl)

abbrev NativeRecordWire :=
  Digest × WorkKind × Digest × Digest × Digest × List UInt8 × List UInt8

def nativeRecordWireStream : StreamCodec NativeRecordWire :=
  StreamCodec.product digestStream
    (StreamCodec.product workKindStream
      (StreamCodec.product digestStream
        (StreamCodec.product digestStream
          (StreamCodec.product digestStream
            (StreamCodec.product bytesStream bytesStream)))))

def nativeRecordStream : StreamCodec NativeRecord :=
  StreamCodec.xmap nativeRecordWireStream
    (fun record => (record.callSlotId, record.kind, record.carrierProfileId,
      record.inputCodecId, record.outputCodecId, record.inputBytes,
      record.outputBytes))
    (fun (callSlotId, kind, carrierProfileId, inputCodecId, outputCodecId,
        inputBytes, outputBytes) =>
      ⟨callSlotId, kind, carrierProfileId, inputCodecId, outputCodecId,
       inputBytes, outputBytes⟩)
    (by intro record; cases record; rfl)

abbrev OpeningRecordWire :=
  Digest × RootRecord × List UInt8 × List UInt8 × List UInt8 ×
    Digest × List UInt8

def openingRecordWireStream : StreamCodec OpeningRecordWire :=
  StreamCodec.product digestStream
    (StreamCodec.product rootRecordStream
      (StreamCodec.product bytesStream
        (StreamCodec.product bytesStream
          (StreamCodec.product bytesStream
            (StreamCodec.product digestStream bytesStream)))))

def openingRecordStream : StreamCodec OpeningRecord :=
  StreamCodec.xmap openingRecordWireStream
    (fun record => (record.openingSlotId, record.root, record.indexBytes,
      record.semanticValueBytes, record.representationValueBytes,
      record.proofCodecId, record.proofBytes))
    (fun (openingSlotId, root, indexBytes, semanticValueBytes,
        representationValueBytes, proofCodecId, proofBytes) =>
      ⟨openingSlotId, root, indexBytes, semanticValueBytes,
       representationValueBytes, proofCodecId, proofBytes⟩)
    (by intro record; cases record; rfl)

abbrev ReprEqRecordWire := Digest × ReprEqRole × Digest × Digest

def reprEqRecordWireStream : StreamCodec ReprEqRecordWire :=
  StreamCodec.product digestStream
    (StreamCodec.product reprEqRoleStream
      (StreamCodec.product digestStream digestStream))

def reprEqRecordStream : StreamCodec ReprEqRecord :=
  StreamCodec.xmap reprEqRecordWireStream
    (fun record => (record.bridgeId, record.role, record.sourceOpeningSlotId,
      record.targetOpeningSlotId))
    (fun (bridgeId, role, sourceOpeningSlotId, targetOpeningSlotId) =>
      ⟨bridgeId, role, sourceOpeningSlotId, targetOpeningSlotId⟩)
    (by intro record; cases record; rfl)

def drawLabelStream : StreamCodec GlobalDrawLabel :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product drawRoleStream StreamCodec.nat))
    (fun label => (label.transcriptDomain, label.role, label.ordinal))
    (fun (transcriptDomain, role, ordinal) =>
      ⟨transcriptDomain, role, ordinal⟩)
    (by intro label; cases label; rfl)

def globalDrawLabelCodec : LawfulCodec GlobalDrawLabel :=
  drawLabelStream.toLawful

abbrev GlobalFrameWire :=
  Sum (Digest × List UInt8)
    (Sum RootRecord
      (Sum NativeRecord (Sum OpeningRecord ReprEqRecord)))

def globalFrameWireStream : StreamCodec GlobalFrameWire :=
  StreamCodec.sum (StreamCodec.product digestStream bytesStream)
    (StreamCodec.sum rootRecordStream
      (StreamCodec.sum nativeRecordStream
        (StreamCodec.sum openingRecordStream reprEqRecordStream)))

def globalFrameStream : StreamCodec GlobalFrame :=
  StreamCodec.xmap globalFrameWireStream
    (fun frame => match frame with
      | .publicContext domain bytes => .inl (domain, bytes)
      | .root record => .inr (.inl record)
      | .nativeReply record => .inr (.inr (.inl record))
      | .opening record => .inr (.inr (.inr (.inl record)))
      | .representationEdge record => .inr (.inr (.inr (.inr record))))
    (fun wire => match wire with
      | .inl (domain, bytes) => .publicContext domain bytes
      | .inr (.inl record) => .root record
      | .inr (.inr (.inl record)) => .nativeReply record
      | .inr (.inr (.inr (.inl record))) => .opening record
      | .inr (.inr (.inr (.inr record))) => .representationEdge record)
    (by intro frame; cases frame <;> rfl)

def globalFrameCodec : LawfulCodec GlobalFrame :=
  globalFrameStream.toLawful

/-! ## Stable IDs and domain strings -/

def id (value : Nat) : Digest := ⟨value⟩

def cshakeAlgorithmId : Digest := id 8400
def digestCodecPin : CodecPin := ⟨id 8401, id 8501, 1⟩
def merklePathCodecPin : CodecPin := ⟨id 8402, id 8502, 1⟩
def globalFrameCodecPin : CodecPin := ⟨id 8403, id 8503, 1⟩
def globalDrawLabelCodecPin : CodecPin := ⟨id 8404, id 8504, 1⟩
def merkleSuiteId : Digest := id 8600

def utf8 (value : String) : List UInt8 := value.toUTF8.toList

/-- The leading byte is an explicit suite-local domain tag; the suffix stays
human-readable in traces and manifests. -/
def leafCustomization : List UInt8 :=
  0x01 :: utf8 "MINIDREGG/TOWER256/MERKLE/LEAF/V1"

def nodeCustomization : List UInt8 :=
  0x02 :: utf8 "MINIDREGG/TOWER256/MERKLE/NODE/V1"

def absorbDomain : List UInt8 :=
  0x03 :: utf8 "MINIDREGG/TOWER256/TRANSCRIPT/ABSORB/V1"

def squeezeDomain : List UInt8 :=
  0x04 :: utf8 "MINIDREGG/TOWER256/TRANSCRIPT/DRAW/V1"

def drawFrameTag : UInt8 := 0xd1

theorem customizationDomains_nodup :
    [leafCustomization, nodeCustomization, absorbDomain, squeezeDomain].Nodup := by
  simp [leafCustomization, nodeCustomization, absorbDomain, squeezeDomain]

theorem leaf_node_distinct : leafCustomization ≠ nodeCustomization := by
  simp [leafCustomization, nodeCustomization]

theorem absorb_squeeze_distinct : absorbDomain ≠ squeezeDomain := by
  simp [absorbDomain, squeezeDomain]

/-! ## The unique shared backend -/

noncomputable def cshake : Cshake256 :=
  Sp800185Cshake256.controller cshakeAlgorithmId digestCodecPin

noncomputable def merkleDomains : MerkleDomains cshake where
  suiteId := merkleSuiteId
  proofCodecPin := merklePathCodecPin
  proofCodec := merklePathCodec
  leafCustomization := leafCustomization
  nodeCustomization := nodeCustomization
  customizationsDistinct := leaf_node_distinct

noncomputable def transcriptDomains : TranscriptDomains cshake where
  frameCodec := globalFrameCodec
  labelCodec := globalDrawLabelCodec
  absorbDomain := absorbDomain
  squeezeDomain := squeezeDomain
  drawFrameTag := drawFrameTag
  absorb_squeeze_distinct := absorb_squeeze_distinct

noncomputable def backend : Backend BinaryTower256Profile.Tower256 where
  tower := BinaryTower256Profile.profile
  cshake := cshake
  merkle := merkleDomains
  transcript := transcriptDomains

theorem towerExact : backend.tower = BinaryTower256Profile.profile := rfl

theorem cshakeExact : backend.cshake =
    Sp800185Cshake256.controller cshakeAlgorithmId digestCodecPin := rfl

theorem cshakeAlgorithmExact : backend.cshake.algorithmId = cshakeAlgorithmId := rfl

theorem digestCodecPinExact :
    backend.cshake.digestCodecPin = digestCodecPin := rfl

theorem merkleSuiteExact : backend.merkle.suiteId = merkleSuiteId := rfl

theorem merkleCodecPinExact :
    backend.merkle.proofCodecPin = merklePathCodecPin := rfl

theorem merkleCodecExact : backend.merkle.proofCodec = merklePathCodec := rfl

theorem merkleDomainsExact :
    backend.merkle.leafCustomization = leafCustomization ∧
    backend.merkle.nodeCustomization = nodeCustomization := ⟨rfl, rfl⟩

theorem transcriptCodecsExact :
    backend.transcript.frameCodec = globalFrameCodec ∧
    backend.transcript.labelCodec = globalDrawLabelCodec := ⟨rfl, rfl⟩

theorem transcriptDomainsExact :
    backend.transcript.absorbDomain = absorbDomain ∧
    backend.transcript.squeezeDomain = squeezeDomain ∧
    backend.transcript.drawFrameTag = drawFrameTag := ⟨rfl, rfl, rfl⟩

theorem cshakeOutputExact (customization input : List UInt8) :
    backend.cshake.digestCodec.encode
        (backend.cshake.xofDigest customization input) =
      (Sp800185Cshake256.hash customization input).bytes :=
  Sp800185Cshake256.controller_digest_encode_exact
    cshakeAlgorithmId digestCodecPin customization input

/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.StreamCodec.decodeNatPrefix_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms StreamCodec.decodeNatPrefix_encode
/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.merklePathCodec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms merklePathCodec
/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.globalFrameCodec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms globalFrameCodec
/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.globalDrawLabelCodec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms globalDrawLabelCodec
/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.towerExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms towerExact
/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.cshakeExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cshakeExact
/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.customizationDomains_nodup' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms customizationDomains_nodup
/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.cshakeOutputExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cshakeOutputExact

end Minidregg.Compiler.Tower256ConcreteBackend

/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.StreamCodec.natDigits_eq_fast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.Tower256ConcreteBackend.StreamCodec.natDigits_eq_fast
