/-
# Compiler.Tower256NativeByteBoundary -- byte-only native Tower256 replies

Native Tower256 kernels are unverified compute.  Their only authority at this
boundary is to return a byte string.  Lean decodes that string with the exact
recursive Fan--Paar coordinate codec, then applies a Lean-authored reflected
predicate before the result can become an accepted semantic field value.

There is deliberately no Rust proposition, verdict, or refinement relation.
An arbitrary runner can reach `AcceptedReply` only through Lean's decoder and
checker.  The boundary does not assert that a successful native answer is the
answer some intended arithmetic kernel should have produced; that fact must be
stated by the selected `Accepts` predicate and established by its reflection
theorem (or by a proof-system verifier instantiated as that predicate).
-/

import Compiler.BinaryTower256Profile

namespace Minidregg.Compiler.Tower256NativeByteBoundary

open Minidregg.Theory

set_option autoImplicit false

abbrev Tower256 := BinaryTower256Profile.Tower256
abbrev Coordinate256 := Fin (2 ^ 256)

/-- The public semantic codec is exactly the inhabited profile's recursive
Fan--Paar value codec. -/
noncomputable abbrev codec :=
  BinaryTower256Profile.profile.valueCodec

/-! ## Canonical byte seam -/

/-- Every byte is a canonical base-256 digit. -/
private theorem byteNats_ranged (bytes : List UInt8) :
    Bignum.Ranged 256 (bytes.map UInt8.toNat) := by
  intro digit member
  simp only [List.mem_map] at member
  rcases member with ⟨byte, _, rfl⟩
  simpa using byte.toNat_lt

/-- The executable coordinate decoder underlying the exact semantic codec. -/
abbrev decodeCoordinate := BinaryTowerFanPaarCodec.decodeFin

/-- Interpret canonical coordinates in Lean's semantic Tower256 field.  This
map is theorem-layer data; the executable boundary below stores coordinates
and does not ask native code to implement this map. -/
noncomputable abbrev semanticValue (coordinate : Coordinate256) : Tower256 :=
  BinaryTowerFanPaarCodec.ofFin coordinate

/-- The exact coordinate decoder accepts only the declared 32-byte width. -/
theorem decodeCoordinate_some_length {bytes : List UInt8}
    {coordinate : Coordinate256}
    (decoded : decodeCoordinate bytes = some coordinate) :
    bytes.length = 32 := by
  simp only [decodeCoordinate, BinaryTowerFanPaarCodec.decodeFin] at decoded
  split at decoded
  · assumption
  · contradiction

/-- Coordinate decoding and re-encoding a successful native byte string
preserves every byte. -/
theorem encodeCoordinate_of_decode_eq_some {bytes : List UInt8}
    {coordinate : Coordinate256}
    (decoded : decodeCoordinate bytes = some coordinate) :
    BinaryTowerFanPaarCodec.encodeFin coordinate = bytes := by
  simp only [decodeCoordinate, BinaryTowerFanPaarCodec.decodeFin] at decoded
  split at decoded
  next widthExact =>
    split at decoded
    next bounded =>
      simp only [Option.some.injEq] at decoded
      subst coordinate
      apply List.map_injective_iff.mpr (fun _ _ equal => UInt8.ext equal)
      rw [BinaryTowerFanPaarCodec.encodeFin_toNats]
      have digitsExact := Bignum.digitsLE_denoteNat (by norm_num : 0 < 256)
        (bytes.map UInt8.toNat) (byteNats_ranged bytes)
      simpa [widthExact] using digitsExact
    next notBounded => contradiction
  next wrongWidth => contradiction

/-- The executable coordinate decode is precisely the semantic Fan--Paar
decode once its coordinate is interpreted in Lean's field. -/
theorem semantic_decode_of_coordinate_decode {bytes : List UInt8}
    {coordinate : Coordinate256}
    (decoded : decodeCoordinate bytes = some coordinate) :
    codec.decode bytes = some (semanticValue coordinate) := by
  simp only [codec, BinaryTower256Profile.profile,
    BinaryTowerFanPaarCodec.codec, BinaryTowerFanPaarCodec.decode,
    semanticValue, decoded, Option.map_some]

/-- The interpreted semantic value re-encodes to the byte-identical native
reply.  Thus the field value cannot be detached from the bytes which crossed
the boundary. -/
theorem encodeSemantic_of_coordinate_decode {bytes : List UInt8}
    {coordinate : Coordinate256}
    (decoded : decodeCoordinate bytes = some coordinate) :
    codec.encode (semanticValue coordinate) = bytes := by
  simp only [codec, BinaryTower256Profile.profile,
    BinaryTowerFanPaarCodec.codec, BinaryTowerFanPaarCodec.encode,
    semanticValue, BinaryTowerFanPaarCodec.toFin_ofFin]
  exact encodeCoordinate_of_decode_eq_some decoded

/-! ## Lean-authored checker and accepted reply -/

/-- A reflected acceptance predicate selected in Lean.  Its executable checker
reads canonical coordinates; its theorem states exactly what acceptance means
for the corresponding semantic Tower256 value.  This object is the only source
of acceptance semantics at the byte boundary. -/
structure SemanticChecker (Input : Type) where
  Accepts : Input → Tower256 → Prop
  check : Input → Coordinate256 → Bool
  check_iff : ∀ input coordinate,
    check input coordinate = true ↔ Accepts input (semanticValue coordinate)

/-- A native byte reply which has passed the canonical coordinate decoder and
the selected Lean checker.  Consumers receive the coordinate with both facts;
the theorem-layer semantic value is derived from it, never supplied by native
code. -/
structure AcceptedReply {Input : Type}
    (checker : SemanticChecker Input) (input : Input) where
  bytes : List UInt8
  coordinate : Coordinate256
  decoded : decodeCoordinate bytes = some coordinate
  accepted : checker.Accepts input (semanticValue coordinate)

namespace AcceptedReply

/-- The semantic Tower256 value fixed by this accepted coordinate. -/
noncomputable abbrev value {Input : Type} {checker : SemanticChecker Input}
    {input : Input} (reply : AcceptedReply checker input) : Tower256 :=
  semanticValue reply.coordinate

theorem semanticDecoded {Input : Type} {checker : SemanticChecker Input}
    {input : Input} (reply : AcceptedReply checker input) :
    codec.decode reply.bytes = some reply.value :=
  semantic_decode_of_coordinate_decode reply.decoded

theorem widthExact {Input : Type} {checker : SemanticChecker Input}
    {input : Input} (reply : AcceptedReply checker input) :
    reply.bytes.length = 32 :=
  decodeCoordinate_some_length reply.decoded

theorem bytesExact {Input : Type} {checker : SemanticChecker Input}
    {input : Input} (reply : AcceptedReply checker input) :
    codec.encode reply.value = reply.bytes :=
  encodeSemantic_of_coordinate_decode reply.decoded

end AcceptedReply

/-! ## Arbitrary opaque runners, checked only after return -/

/-- Native code returns bytes or an opaque error.  It cannot return an
`AcceptedReply`, a proposition, or a continuation. -/
abbrev OpaqueByteRunner (Error Input : Type) :=
  Input → Except Error (List UInt8)

/-- All failures introduced by the Lean boundary. -/
inductive BoundaryFailure (Error : Type)
  | native (error : Error)
  | invalidEncoding
  | rejected
deriving Repr

/-- Run arbitrary native byte compute, then cross the Lean-owned boundary.
The runtime path manipulates only bytes and finite coordinates; the semantic
field interpretation occurs in erased propositions and theorem projections. -/
def run {Error Input : Type}
    (runner : OpaqueByteRunner Error Input)
    (checker : SemanticChecker Input) (input : Input) :
    Except (BoundaryFailure Error) (AcceptedReply checker input) :=
  match runner input with
  | .error error => .error (.native error)
  | .ok bytes =>
      match decoded : decodeCoordinate bytes with
      | none => .error .invalidEncoding
      | some coordinate =>
          if accepted : checker.check input coordinate = true then
            .ok ⟨bytes, coordinate, decoded,
              (checker.check_iff input coordinate).mp accepted⟩
          else
            .error .rejected

/-- A successful boundary result contains the exact byte string returned by
the runner; the Lean boundary neither substitutes nor normalizes it. -/
theorem run_success_runner_bytes {Error Input : Type}
    (runner : OpaqueByteRunner Error Input)
    (checker : SemanticChecker Input) (input : Input)
    (reply : AcceptedReply checker input)
    (success : run runner checker input = .ok reply) :
    runner input = .ok reply.bytes := by
  unfold run at success
  split at success
  next error runnerFailed => simp at success
  next bytes runnerReturned =>
    split at success
    next decodeFailed => simp at success
    next coordinate decodeSucceeded =>
      split at success
      next accepted =>
        simp only [Except.ok.injEq] at success
        subst reply
        exact runnerReturned
      next rejected => simp at success

/-- Control-integrity theorem for a completely arbitrary runner: success gives
the runner's exact bytes, exact executable coordinate decoding, exact semantic
Fan--Paar decoding/re-encoding, the declared width, and the Lean proposition.
It does not claim native arithmetic correctness. -/
theorem arbitrary_runner_integrity {Error Input : Type}
    (runner : OpaqueByteRunner Error Input)
    (checker : SemanticChecker Input) (input : Input)
    (reply : AcceptedReply checker input)
    (success : run runner checker input = .ok reply) :
    runner input = .ok reply.bytes ∧
      decodeCoordinate reply.bytes = some reply.coordinate ∧
      codec.decode reply.bytes = some reply.value ∧
      codec.encode reply.value = reply.bytes ∧
      reply.bytes.length = 32 ∧ checker.Accepts input reply.value := by
  exact ⟨run_success_runner_bytes runner checker input reply success,
    reply.decoded, reply.semanticDecoded, reply.bytesExact, reply.widthExact,
    reply.accepted⟩

#print axioms decodeCoordinate_some_length
#print axioms encodeCoordinate_of_decode_eq_some
#print axioms semantic_decode_of_coordinate_decode
#print axioms encodeSemantic_of_coordinate_decode
#print axioms run_success_runner_bytes
#print axioms arbitrary_runner_integrity

end Minidregg.Compiler.Tower256NativeByteBoundary
