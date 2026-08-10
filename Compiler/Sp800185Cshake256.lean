/-
# Compiler.Sp800185Cshake256 -- proved cSHAKE256 controller integration

This module projects the exact Lean computation in
`Sp800185Cshake256Core` into the repository's `Digest`, lawful codec, and
shared Tower256 controller surfaces.  Byte-exact reply and width theorems stay
here because they are the API consumed by deployed controllers.

The implementation is executable Lean.  It gives Rust no hash semantics:
`checkedXofCall` still treats native output as opaque bytes and accepts only
the digest selected here.  This file proves no collision resistance and no
random-oracle transport.  Executable NIST/FIPS vectors live in the independent
`Sp800185Cshake256Conformance` module.  The `Compiler` umbrella imports them,
so complete builds still check conformance without putting vector constants
and evaluation commands in every API consumer's import surface.
-/

import Theory.Bignum
import Compiler.Tower256CshakeMerkleController
import Compiler.Sp800185Cshake256Core

namespace Minidregg.Compiler.Sp800185Cshake256

open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Theory
open Minidregg.Compiler.SemanticManifest (CodecPin)
open Minidregg.Compiler.Tower256CshakeMerkleController (Cshake256)

set_option autoImplicit false

@[simp] theorem leftEncode_zero : leftEncode 0 = [1, 0] := by decide

@[simp] theorem leftEncode_65536 : leftEncode 65536 = [3, 1, 0, 0] := by decide

@[simp] theorem encodeString_empty : encodeString [] = [1, 0] := by decide

@[simp] theorem bytepad_empty_four : bytepad [] 4 = [1, 4, 0, 0] := by decide

@[simp] theorem squeeze32_length (state : State) :
    (squeeze32 state).length = 32 := by
  simp [squeeze32, outputBytes]

@[simp] theorem cshake256Bytes_length (customization input : List UInt8) :
    (cshake256Bytes customization input).length = 32 := by
  simp [cshake256Bytes]

/-! ## Digest projection and the controller instance -/

/-- Fixed-width little-endian bytes on the 256-bit digest range. -/
def fixedDigestBytesLE (digest : Digest) : List UInt8 :=
  (Bignum.digitsLE 256 32 digest.value).map UInt8.ofNat

/-- Minimal little-endian bytes for the total-codec escape branch. -/
def variableDigestBytesLE (digest : Digest) : List UInt8 :=
  (Nat.digits 256 digest.value).map UInt8.ofNat

/-- A total lawful codec cannot encode the repository's unbounded `Digest`
carrier into 32 bytes.  Values in the cSHAKE range use the exact 32-byte
encoding; larger values use a zero-tagged minimal base-256 escape.  This keeps
the generic carrier honest while making every cSHAKE reply exactly 32 bytes. -/
def digestBytesLE (digest : Digest) : List UInt8 :=
  if digest.value < 256 ^ 32 then fixedDigestBytesLE digest
  else 0 :: variableDigestBytesLE digest

def digestOfBytesLE (bytes : List UInt8) : Digest :=
  ⟨Bignum.denoteNat 256 (bytes.map UInt8.toNat)⟩

def decodeDigestBytes (bytes : List UInt8) : Option Digest :=
  if bytes.length = 32 then some (digestOfBytesLE bytes)
  else match bytes with
    | 0 :: payload => some ⟨Nat.ofDigits 256 (payload.map UInt8.toNat)⟩
    | _ => none

def digestCodec : LawfulCodec Digest where
  encode := digestBytesLE
  decode := decodeDigestBytes
  decode_encode := by
    intro digest
    by_cases hlow : digest.value < 256 ^ 32
    · have hlength : (fixedDigestBytesLE digest).length = 32 := by
        simp [fixedDigestBytesLE]
      simp only [digestBytesLE, hlow, if_true, decodeDigestBytes, hlength]
      apply congrArg some
      apply congrArg Digest.mk
      change Bignum.denoteNat 256
        ((Bignum.digitsLE 256 32 digest.value).map
          (fun digit => (UInt8.ofNat digit).toNat)) = digest.value
      have hmap :
          (Bignum.digitsLE 256 32 digest.value).map
              (fun digit => (UInt8.ofNat digit).toNat) =
            Bignum.digitsLE 256 32 digest.value := by
        have hcongr := List.map_congr_left
          (l := Bignum.digitsLE 256 32 digest.value)
          (f := fun digit => (UInt8.ofNat digit).toNat)
          (g := id) (fun digit hdigit =>
            UInt8.toNat_ofNat_of_lt
              (Bignum.digitsLE_ranged (by decide) 32 digest.value digit hdigit))
        simpa only [List.map_id, id_eq] using hcongr
      rw [hmap]
      exact Bignum.denoteNat_digitsLE (by decide) 32 digest.value hlow
    · have hlength : (0 :: variableDigestBytesLE digest).length ≠ 32 := by
        intro heq
        have hdigitLength : (Nat.digits 256 digest.value).length = 31 := by
          simp only [variableDigestBytesLE, List.length_cons, List.length_map]
            at heq
          omega
        have hfits := Nat.lt_base_pow_length_digits
          (m := digest.value) (b := 256) (by decide)
        rw [hdigitLength] at hfits
        apply hlow
        exact lt_of_lt_of_le hfits
          (Nat.pow_le_pow_right (by decide) (by omega))
      rw [show digestBytesLE digest = 0 :: variableDigestBytesLE digest by
        unfold digestBytesLE
        rw [if_neg hlow]]
      simp only [decodeDigestBytes, hlength, if_false]
      apply congrArg some
      apply congrArg Digest.mk
      simp only [variableDigestBytesLE, List.map_map]
      change Nat.ofDigits 256
        ((Nat.digits 256 digest.value).map
          (fun digit => (UInt8.ofNat digit).toNat)) = digest.value
      have hmap :
          (Nat.digits 256 digest.value).map
              (fun digit => (UInt8.ofNat digit).toNat) =
            Nat.digits 256 digest.value := by
        have hcongr := List.map_congr_left
          (l := Nat.digits 256 digest.value)
          (f := fun digit => (UInt8.ofNat digit).toNat)
          (g := id) (fun digit hdigit =>
            UInt8.toNat_ofNat_of_lt
              (Nat.digits_lt_base (by decide) hdigit))
        simpa only [List.map_id, id_eq] using hcongr
      rw [hmap, Nat.ofDigits_digits]

@[simp] theorem digestCodec_encode (digest : Digest) :
    digestCodec.encode digest = digestBytesLE digest := rfl

/-- A proof-relevant 32-byte result, retained before projecting to the legacy
`Digest` wrapper. -/
structure Output where
  bytes : List UInt8
  length_exact : bytes.length = 32
deriving DecidableEq, Repr

def hash (customization input : List UInt8) : Output :=
  ⟨cshake256Bytes customization input, cshake256Bytes_length _ _⟩

def Output.digest (output : Output) : Digest := digestOfBytesLE output.bytes

/-- Re-encoding any exact 32-byte string through its `Digest` projection
recovers those identical bytes, including leading zero bytes. -/
theorem digestBytesLE_digestOfBytesLE (bytes : List UInt8)
    (hlength : bytes.length = 32) :
    digestBytesLE (digestOfBytesLE bytes) = bytes := by
  have hranged : Bignum.Ranged 256 (bytes.map UInt8.toNat) := by
    intro digit hdigit
    rcases List.mem_map.mp hdigit with ⟨byte, _, rfl⟩
    exact byte.toNat_lt
  have hvalue := Bignum.denoteNat_lt_pow (by decide)
    (bytes.map UInt8.toNat) hranged
  simp only [List.length_map, hlength] at hvalue
  simp only [digestBytesLE, digestOfBytesLE, hvalue, if_true,
    fixedDigestBytesLE]
  have hdigits := Bignum.digitsLE_denoteNat (by decide)
    (bytes.map UInt8.toNat) hranged
  simp only [List.length_map, hlength] at hdigits
  rw [hdigits]
  have hfunction : (UInt8.ofNat ∘ UInt8.toNat) = id := by
    funext byte
    simp
  rw [List.map_map, hfunction, List.map_id]

theorem digestBytesLE_hash (customization input : List UInt8) :
    digestBytesLE (hash customization input).digest =
      (hash customization input).bytes :=
  digestBytesLE_digestOfBytesLE _ (hash customization input).length_exact

/-- The concrete computation layer behind the controller seam.  Identifiers
remain caller-selected first-order manifest data; computation does not invent
their content-addressing policy. -/
def controller (algorithmId : Digest) (digestCodecPin : CodecPin) : Cshake256 where
  algorithmId := algorithmId
  digestCodecPin := digestCodecPin
  digestCodec := digestCodec
  outputBytes := outputBytes
  outputBytesExact := rfl
  xofDigest customization input := (hash customization input).digest

@[simp] theorem controller_digestCodec (algorithmId : Digest)
    (digestCodecPin : CodecPin) :
    (controller algorithmId digestCodecPin).digestCodec = digestCodec := rfl

@[simp] theorem controller_xofDigest (algorithmId : Digest)
    (digestCodecPin : CodecPin) (customization input : List UInt8) :
    (controller algorithmId digestCodecPin).xofDigest customization input =
      (hash customization input).digest := rfl

theorem controller_digest_encode_exact (algorithmId : Digest)
    (digestCodecPin : CodecPin) (customization input : List UInt8) :
    (controller algorithmId digestCodecPin).digestCodec.encode
        ((controller algorithmId digestCodecPin).xofDigest customization input) =
      (hash customization input).bytes := by
  rw [controller_digestCodec, digestCodec_encode, controller_xofDigest,
    digestBytesLE_hash]

/-- For this concrete backend, the generic opaque native XOF seam returns the
literal 32 cSHAKE bytes, not merely some variable-width encoding of a `Nat`. -/
theorem checkedXofCall_reply_bytes_exact (algorithmId : Digest)
    (digestCodecPin requestCodecPin : CodecPin)
    (requestCodec : LawfulCodec
      Tower256CshakeMerkleController.XofRequest)
    (callSlotId carrierProfileId : Digest)
    (request : Tower256CshakeMerkleController.XofRequest)
    (bytes : List UInt8)
    (accepted : (Tower256CshakeMerkleController.checkedXofCall
      (controller algorithmId digestCodecPin) requestCodecPin requestCodec
      callSlotId carrierProfileId request).acceptsReply bytes = true) :
    bytes = (hash request.customization request.input).bytes := by
  calc
    bytes = (controller algorithmId digestCodecPin).digestCodec.encode
        ((controller algorithmId digestCodecPin).xofDigest
          request.customization request.input) :=
      Tower256CshakeMerkleController.checkedXofCall_reply_exact
        (controller algorithmId digestCodecPin) requestCodecPin requestCodec
        callSlotId carrierProfileId request bytes accepted
    _ = (hash request.customization request.input).bytes :=
      controller_digest_encode_exact algorithmId digestCodecPin _ _

theorem checkedXofCall_reply_width (algorithmId : Digest)
    (digestCodecPin requestCodecPin : CodecPin)
    (requestCodec : LawfulCodec
      Tower256CshakeMerkleController.XofRequest)
    (callSlotId carrierProfileId : Digest)
    (request : Tower256CshakeMerkleController.XofRequest)
    (bytes : List UInt8)
    (accepted : (Tower256CshakeMerkleController.checkedXofCall
      (controller algorithmId digestCodecPin) requestCodecPin requestCodec
      callSlotId carrierProfileId request).acceptsReply bytes = true) :
    bytes.length = 32 := by
  rw [checkedXofCall_reply_bytes_exact algorithmId digestCodecPin
    requestCodecPin requestCodec callSlotId carrierProfileId request bytes accepted]
  exact (hash request.customization request.input).length_exact

theorem hash_digest_lt (customization input : List UInt8) :
    (hash customization input).digest.value < 256 ^ 32 := by
  apply Bignum.denoteNat_lt_pow (by decide)
  intro digit hdigit
  rcases List.mem_map.mp hdigit with ⟨byte, _, rfl⟩
  exact byte.toNat_lt

theorem hash_digest_lt_two_pow_256 (customization input : List UInt8) :
    (hash customization input).digest.value < 2 ^ 256 := by
  simpa only [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul,
    Nat.reduceMul] using hash_digest_lt customization input

#print axioms digestCodec
#print axioms cshake256Bytes_length
#print axioms hash_digest_lt
#print axioms hash_digest_lt_two_pow_256
#print axioms checkedXofCall_reply_bytes_exact
#print axioms checkedXofCall_reply_width

end Minidregg.Compiler.Sp800185Cshake256
