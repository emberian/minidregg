/-
# Theory.ByteCodecs -- lawful codecs, buildable

A `LawfulCodec` is required wherever this tree crosses a byte boundary: the
cell-state materializer, the semantic effect family's declaration and outcome,
and `HyperdocumentOperations.Config`, which demands three at once.  The whole
repository contained exactly two, both for `Digest`, and both hand-rolled.  So
every carrier gated on a `Config` was gated on codecs nobody had written.

This supplies the small toolkit that removes that gate.  It is deliberately
UNARY and therefore enormous -- a natural number `n` costs `n` bytes -- because
the point is inhabitation, not transport.  Nothing here is a deployment codec
and nothing should be used as one; the deployed path is
`Compiler.Sp800185Cshake256.digestCodec` and the artifact codec pins.

The construction is one idea applied three times: frame a payload with a unary
length prefix and a `1` delimiter, so a stream can be split back apart, and
then lift along injections.
-/
import Theory.IndexedProgram

namespace Minidregg.Theory.ByteCodecs

open Minidregg.Theory.IndexedProgram

set_option autoImplicit false

/-! ## Framing -/

/-- Unary encoding of a length: `n` zero bytes. -/
def natBytes (n : Nat) : List UInt8 := List.replicate n 0

@[simp] theorem natBytes_length (n : Nat) : (natBytes n).length = n := by
  simp [natBytes]

/-- Frame a payload with its unary length and a `1` delimiter.  The delimiter
is what lets the prefix be read back: the length run is all zeros, so the first
non-zero byte ends it. -/
def frame (payload : List UInt8) : List UInt8 :=
  natBytes payload.length ++ 1 :: payload

theorem takeWhile_zero_natBytes (n : Nat) (rest : List UInt8) :
    (natBytes n ++ 1 :: rest).takeWhile (fun byte => byte == 0) = natBytes n := by
  induction n with
  | zero => simp [natBytes]
  | succ k ih =>
      rw [natBytes, List.replicate_succ, List.cons_append, List.takeWhile_cons]
      simp [natBytes] at ih ⊢

theorem dropWhile_zero_natBytes (n : Nat) (rest : List UInt8) :
    (natBytes n ++ 1 :: rest).dropWhile (fun byte => byte == 0) = 1 :: rest := by
  induction n with
  | zero => simp [natBytes]
  | succ k ih =>
      rw [natBytes, List.replicate_succ, List.cons_append, List.dropWhile_cons]
      simp [natBytes] at ih ⊢

/-- Split one framed payload off the front of a stream. -/
def unframe (stream : List UInt8) : Option (List UInt8 × List UInt8) :=
  let width := (stream.takeWhile (fun byte => byte == 0)).length
  match stream.dropWhile (fun byte => byte == 0) with
  | 1 :: rest => some (rest.take width, rest.drop width)
  | _ => none

/-- **Framing round-trips**, and it does so in the presence of arbitrary
trailing bytes -- which is what makes it composable. -/
theorem unframe_frame (payload rest : List UInt8) :
    unframe (frame payload ++ rest) = some (payload, rest) := by
  have appended : frame payload ++ rest =
      natBytes payload.length ++ 1 :: (payload ++ rest) := by
    simp [frame]
  rw [unframe, appended, takeWhile_zero_natBytes, dropWhile_zero_natBytes,
    natBytes_length]
  simp

/-! ## Codecs -/

/-- The unary natural-number codec. -/
def natCodec : LawfulCodec Nat where
  encode := natBytes
  decode := fun bytes =>
    if bytes.all (fun byte => byte == 0) then some bytes.length else none
  decode_encode := fun value => by simp [natBytes]

variable {alpha beta : Type}

/-- Pairs, by framing the left component. -/
def pairCodec (left : LawfulCodec alpha) (right : LawfulCodec beta) :
    LawfulCodec (alpha × beta) where
  encode := fun value => frame (left.encode value.1) ++ right.encode value.2
  decode := fun bytes =>
    match unframe bytes with
    | none => none
    | some (head, tail) =>
        match left.decode head, right.decode tail with
        | some first, some second => some (first, second)
        | _, _ => none
  decode_encode := fun value => by
    rw [unframe_frame]
    simp [left.decode_encode, right.decode_encode]

/-- Lift a codec along an injection with a chosen retraction.  This is how
records get codecs: encode the tuple of fields, decode it, rebuild. -/
def codecOfRetraction (base : LawfulCodec beta)
    (forward : alpha -> beta) (backward : beta -> alpha)
    (retraction : ∀ value, backward (forward value) = value) :
    LawfulCodec alpha where
  encode := fun value => base.encode (forward value)
  decode := fun bytes => (base.decode bytes).map backward
  decode_encode := fun value => by
    rw [base.decode_encode]
    exact congrArg some (retraction value)

/-- Any subsingleton has a codec, which is the degenerate case the existing
witnesses were hand-rolling. -/
def subsingletonCodec (value : alpha) (unique : ∀ other, other = value) :
    LawfulCodec alpha where
  encode := fun _ => []
  decode := fun _ => some value
  decode_encode := fun other => congrArg some (unique other).symm

/-- Elements, each framed, laid end to end. -/
def encodeList (base : LawfulCodec alpha) : List alpha -> List UInt8
  | [] => []
  | value :: rest => frame (base.encode value) ++ encodeList base rest

/-- Read exactly `count` framed elements. -/
def decodeList (base : LawfulCodec alpha) : Nat -> List UInt8 -> Option (List alpha)
  | 0, _ => some []
  | count + 1, bytes =>
      match unframe bytes with
      | none => none
      | some (head, tail) =>
          match base.decode head, decodeList base count tail with
          | some value, some rest => some (value :: rest)
          | _, _ => none

theorem decodeList_encodeList (base : LawfulCodec alpha) (values : List alpha) :
    decodeList base values.length (encodeList base values) = some values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      rw [List.length_cons, encodeList, decodeList, unframe_frame]
      simp only [base.decode_encode, ih]

/-- Lists, by a framed unary count followed by framed elements. -/
def listCodec (base : LawfulCodec alpha) : LawfulCodec (List alpha) where
  encode := fun values => frame (natBytes values.length) ++ encodeList base values
  decode := fun bytes =>
    match unframe bytes with
    | none => none
    | some (countBytes, rest) =>
        if countBytes.all (fun byte => byte == 0) then
          decodeList base countBytes.length rest
        else none
  decode_encode := fun values => by
    rw [unframe_frame]
    simp [natBytes, decodeList_encodeList]

/-! ## Teeth: the framing is not decoration

If the delimiter or the length prefix could be dropped, concatenated payloads
would run together.  These exhibit the ambiguity that framing removes. -/

/-- Two different payload pairs whose UNFRAMED concatenations are equal, so a
codec built by bare concatenation would not round-trip. -/
theorem concatenation_is_ambiguous :
    ([0], [0, 0]) ≠ (([0, 0], [0]) : List UInt8 × List UInt8) ∧
      [0] ++ [0, 0] = ([0, 0] ++ [0] : List UInt8) :=
  ⟨by decide, by decide⟩

/-- Framed, the same two are distinguished. -/
theorem framing_disambiguates :
    frame [0] ++ [0, 0] ≠ frame [0, 0] ++ [0] := by decide

/-- And each recovers its own payload. -/
theorem framing_recovers :
    unframe (frame [0] ++ [0, 0]) = some ([0], [0, 0]) ∧
      unframe (frame [0, 0] ++ [0]) = some ([0, 0], [0]) :=
  ⟨unframe_frame [0] [0, 0], unframe_frame [0, 0] [0]⟩

#print axioms unframe_frame
#print axioms natCodec
#print axioms pairCodec
#print axioms codecOfRetraction
#print axioms decodeList_encodeList
#print axioms listCodec
#print axioms concatenation_is_ambiguous
#print axioms framing_disambiguates
#print axioms framing_recovers

end Minidregg.Theory.ByteCodecs
