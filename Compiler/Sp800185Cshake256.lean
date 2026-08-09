/-
# Compiler.Sp800185Cshake256 -- Lean-owned cSHAKE256 computation

This module supplies the concrete computation which the shared Tower256
controller deliberately left abstract.  It implements the byte-oriented
SP 800-185 cSHAKE256 specialization used by the controller:

* Keccak-f[1600] has twenty-four rounds over twenty-five 64-bit lanes;
* the sponge rate is 1088 bits (136 bytes), hence capacity 512 bits;
* `left_encode`, `encode_string`, and `bytepad` use SP 800-185 framing;
* the function-name string is empty and the controller customization is the
  SP 800-185 customization string;
* empty customization takes the required SHAKE256-compatible `0x1f` suffix;
  nonempty customization takes the cSHAKE `0x04` delimited suffix;
* exactly the first 32 squeezed bytes become the controller `Digest`.

The implementation is executable Lean.  It gives Rust no hash semantics:
`checkedXofCall` still treats native output as opaque bytes and accepts only
the digest selected here.  This file proves no collision resistance and no
random-oracle transport.  SP 800-185 bounds `left_encode` inputs to values
whose byte width fits in one byte; our total Lean function extends framing
outside that standard domain by truncating that width byte.  Every ordinary
finite protocol frame is far inside the standard bound, but a deployment can
carry that first-order length premise explicitly when required.
-/

import Mathlib
import Compiler.Tower256CshakeMerkleController

namespace Minidregg.Compiler.Sp800185Cshake256

open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Compiler.SemanticManifest (CodecPin)
open Minidregg.Compiler.Tower256CshakeMerkleController (Cshake256)

set_option autoImplicit false

/-! ## SP 800-185 byte framing -/

/-- Minimal nonempty big-endian base-256 representation. -/
def natBytesBE (value : Nat) : List UInt8 :=
  let little := Nat.digits 256 value
  let nonempty := if little = [] then [0] else little
  nonempty.reverse.map UInt8.ofNat

/-- SP 800-185 `left_encode`, totalized beyond the standard's 255-byte-width
domain by `UInt8.ofNat`. -/
def leftEncode (value : Nat) : List UInt8 :=
  let bytes := natBytesBE value
  UInt8.ofNat bytes.length :: bytes

/-- SP 800-185 `encode_string`: encode the bit length, then the bytes. -/
def encodeString (bytes : List UInt8) : List UInt8 :=
  leftEncode (8 * bytes.length) ++ bytes

/-- SP 800-185 `bytepad`.  The `width = 0` branch totalizes the helper; the
cSHAKE256 specialization below always selects width 136. -/
def bytepad (bytes : List UInt8) (width : Nat) : List UInt8 :=
  if width = 0 then [] else
    let prefixed := leftEncode width ++ bytes
    let zeroCount := (width - prefixed.length % width) % width
    prefixed ++ List.replicate zeroCount 0

@[simp] theorem leftEncode_zero : leftEncode 0 = [1, 0] := by decide

@[simp] theorem leftEncode_65536 : leftEncode 65536 = [3, 1, 0, 0] := by decide

@[simp] theorem encodeString_empty : encodeString [] = [1, 0] := by decide

@[simp] theorem bytepad_empty_four : bytepad [] 4 = [1, 4, 0, 0] := by decide

/-! ## Keccak-f[1600] -/

abbrev Lane := BitVec 64
abbrev State := Array Lane

def zeroLane : Lane := BitVec.ofNat 64 0
def zeroState : State := Array.replicate 25 zeroLane

/-- Keccak's lane index is `x + 5*y`.  Modulo indexing makes the helper total;
all round callers pass coordinates in `[0,5)`. -/
def lane (state : State) (x y : Nat) : Lane :=
  state.getD (x % 5 + 5 * (y % 5)) zeroLane

def xorColumn (state : State) (x : Nat) : Lane :=
  (List.range 5).foldl (fun acc y => acc ^^^ lane state x y) zeroLane

def theta (state : State) : State :=
  Array.ofFn fun index : Fin 25 =>
    let x := index.val % 5
    let y := index.val / 5
    lane state x y ^^^ xorColumn state (x + 4) ^^^
      (xorColumn state (x + 1)).rotateLeft 1

/-- FIPS 202 rotation offsets, indexed by `x + 5*y`. -/
def rotationOffsets : Array Nat := #[
   0,  1, 62, 28, 27,
  36, 44,  6, 55, 20,
   3, 10, 43, 25, 39,
  41, 45, 15, 21,  8,
  18,  2, 61, 56, 14
]

def rotationOffset (x y : Nat) : Nat :=
  rotationOffsets.getD (x % 5 + 5 * (y % 5)) 0

/-- The fused rho/pi step writes every source lane `(x,y)` to
`(y, 2*x+3*y mod 5)`. -/
def rhoPi (state : State) : State :=
  (List.range 25).foldl (fun output source =>
    let x := source % 5
    let y := source / 5
    let target := y + 5 * ((2 * x + 3 * y) % 5)
    output.setIfInBounds target ((lane state x y).rotateLeft (rotationOffset x y)))
    zeroState

def chi (state : State) : State :=
  Array.ofFn fun index : Fin 25 =>
    let x := index.val % 5
    let y := index.val / 5
    lane state x y ^^^ ((~~~lane state (x + 1) y) &&& lane state (x + 2) y)

/-- FIPS 202 round constants. -/
def roundConstants : List Lane := [
  BitVec.ofNat 64 0x0000000000000001,
  BitVec.ofNat 64 0x0000000000008082,
  BitVec.ofNat 64 0x800000000000808a,
  BitVec.ofNat 64 0x8000000080008000,
  BitVec.ofNat 64 0x000000000000808b,
  BitVec.ofNat 64 0x0000000080000001,
  BitVec.ofNat 64 0x8000000080008081,
  BitVec.ofNat 64 0x8000000000008009,
  BitVec.ofNat 64 0x000000000000008a,
  BitVec.ofNat 64 0x0000000000000088,
  BitVec.ofNat 64 0x0000000080008009,
  BitVec.ofNat 64 0x000000008000000a,
  BitVec.ofNat 64 0x000000008000808b,
  BitVec.ofNat 64 0x800000000000008b,
  BitVec.ofNat 64 0x8000000000008089,
  BitVec.ofNat 64 0x8000000000008003,
  BitVec.ofNat 64 0x8000000000008002,
  BitVec.ofNat 64 0x8000000000000080,
  BitVec.ofNat 64 0x000000000000800a,
  BitVec.ofNat 64 0x800000008000000a,
  BitVec.ofNat 64 0x8000000080008081,
  BitVec.ofNat 64 0x8000000000008080,
  BitVec.ofNat 64 0x0000000080000001,
  BitVec.ofNat 64 0x8000000080008008
]

def round (state : State) (constant : Lane) : State :=
  let mixed := chi (rhoPi (theta state))
  mixed.setIfInBounds 0 (lane mixed 0 0 ^^^ constant)

/-- The exact twenty-four-round Keccak-f[1600] permutation. -/
def keccakF1600 (state : State) : State :=
  roundConstants.foldl round state

/-! ## The 1088-bit-rate sponge and cSHAKE256 -/

def rateBytes : Nat := 136
def rateLanes : Nat := 17
def outputBytes : Nat := 32

def laneFromBlock (block : List UInt8) (laneIndex : Nat) : Lane :=
  (List.range 8).foldl (fun acc offset =>
    acc ^^^ BitVec.ofNat 64
      ((block.getD (8 * laneIndex + offset) 0).toNat * 2 ^ (8 * offset)))
    zeroLane

def xorRateBlock (state : State) (block : List UInt8) : State :=
  Array.ofFn fun index : Fin 25 =>
    if index.val < rateLanes then
      state.getD index.val zeroLane ^^^ laneFromBlock block index.val
    else state.getD index.val zeroLane

/-- Multi-rate padding for a byte-aligned delimited suffix. -/
def padForRate (bytes : List UInt8) (suffix : UInt8) : List UInt8 :=
  let count := rateBytes - bytes.length % rateBytes
  if count = 1 then
    bytes ++ [suffix ^^^ (128 : UInt8)]
  else
    bytes ++ [suffix] ++ List.replicate (count - 2) 0 ++ [128]

/-- Every padded block is absorbed by xor followed by Keccak-f.  The padded
input is a multiple of the rate; division therefore gives the exact block
count. -/
def absorbPadded (padded : List UInt8) : State :=
  (List.range (padded.length / rateBytes)).foldl (fun state blockIndex =>
    let block := (padded.drop (blockIndex * rateBytes)).take rateBytes
    keccakF1600 (xorRateBlock state block)) zeroState

def stateByte (state : State) (index : Nat) : UInt8 :=
  UInt8.ofNat
    ((state.getD (index / 8) zeroLane).toNat / 2 ^ (8 * (index % 8)) % 256)

/-- The first 256 output bits, in Keccak's little-endian lane convention. -/
def squeeze32 (state : State) : List UInt8 :=
  (List.range outputBytes).map (stateByte state)

@[simp] theorem squeeze32_length (state : State) :
    (squeeze32 state).length = 32 := by
  simp [squeeze32, outputBytes]

/-- The SP 800-185 prefix for empty function-name and caller customization. -/
def customizationPrefix (customization : List UInt8) : List UInt8 :=
  bytepad (encodeString [] ++ encodeString customization) rateBytes

/-- cSHAKE256 with empty function-name and a 256-bit output.  SP 800-185
requires the empty-customization case to be exactly SHAKE256. -/
def cshake256Bytes (customization input : List UInt8) : List UInt8 :=
  let shakeCompatible := customization = []
  let framed := if shakeCompatible then input else customizationPrefix customization ++ input
  let suffix : UInt8 := if shakeCompatible then 0x1f else 0x04
  squeeze32 (absorbPadded (padForRate framed suffix))

@[simp] theorem cshake256Bytes_length (customization input : List UInt8) :
    (cshake256Bytes customization input).length = 32 := by
  simp [cshake256Bytes]

/-! ## Digest projection and the controller instance -/

/-- Canonical variable-width little-endian base-256 bytes for the repository's
unbounded `Digest`.  It is intentionally not described as a fixed-width codec:
no lawful 32-byte codec can cover every `Nat`. -/
def digestBytesLE (digest : Digest) : List UInt8 :=
  (Nat.digits 256 digest.value).map UInt8.ofNat

def digestOfBytesLE (bytes : List UInt8) : Digest :=
  ⟨Nat.ofDigits 256 (bytes.map UInt8.toNat)⟩

def digestCodec : LawfulCodec Digest where
  encode := digestBytesLE
  decode bytes := some (digestOfBytesLE bytes)
  decode_encode := by
    intro digest
    apply congrArg some
    apply congrArg Digest.mk
    simp only [digestBytesLE, List.map_map]
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
    change Nat.ofDigits 256
      ((Nat.digits 256 digest.value).map
        (fun digit => (UInt8.ofNat digit).toNat)) = digest.value
    rw [hmap, Nat.ofDigits_digits]

/-- A proof-relevant 32-byte result, retained before projecting to the legacy
`Digest` wrapper. -/
structure Output where
  bytes : List UInt8
  length_exact : bytes.length = 32
deriving DecidableEq, Repr

def hash (customization input : List UInt8) : Output :=
  ⟨cshake256Bytes customization input, cshake256Bytes_length _ _⟩

def Output.digest (output : Output) : Digest := digestOfBytesLE output.bytes

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

@[simp] theorem controller_xofDigest (algorithmId : Digest)
    (digestCodecPin : CodecPin) (customization input : List UInt8) :
    (controller algorithmId digestCodecPin).xofDigest customization input =
      (hash customization input).digest := rfl

theorem hash_digest_lt (customization input : List UInt8) :
    (hash customization input).digest.value < 256 ^ 32 := by
  apply Nat.ofDigits_lt_base_pow_length (by decide)
  · intro digit hdigit
    rcases List.mem_map.mp hdigit with ⟨byte, _, rfl⟩
    exact byte.toNat_lt

theorem hash_digest_lt_two_pow_256 (customization input : List UInt8) :
    (hash customization input).digest.value < 2 ^ 256 := by
  simpa only [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul,
    Nat.reduceMul] using hash_digest_lt customization input

/-! ## NIST SP 800-185 sample tooth

Sample 3 uses `X = 00 01 02 03`, empty function-name, customization
`"Email Signature"`, and a 512-bit output.  The theorem checks the first
256 bits selected by this controller.  This is a conformance vector, not a
security theorem. -/

def emailSignature : List UInt8 :=
  [0x45, 0x6d, 0x61, 0x69, 0x6c, 0x20, 0x53, 0x69,
   0x67, 0x6e, 0x61, 0x74, 0x75, 0x72, 0x65]

def nistSample3Prefix : List UInt8 :=
  [0xd0, 0x08, 0x82, 0x8e, 0x2b, 0x80, 0xac, 0x9d,
   0x22, 0x18, 0xff, 0xee, 0x1d, 0x07, 0x0c, 0x48,
   0xb8, 0xe4, 0xc8, 0x7b, 0xff, 0x32, 0xc9, 0x69,
   0x9d, 0x5b, 0x68, 0x96, 0xee, 0xe0, 0xed, 0xd1]

/-- Executable NIST conformance tooth.  The following build-time evaluation
fails the module instead of introducing `native_decide` as a theorem axiom. -/
def nistSample3Conforms : Bool :=
  cshake256Bytes emailSignature [0, 1, 2, 3] == nistSample3Prefix

def checkNistSample3 : IO Unit := do
  unless nistSample3Conforms do
    throw (IO.userError "SP 800-185 cSHAKE256 sample 3 mismatch")

#eval checkNistSample3

/-- The empty-customization branch is SHAKE256, including its distinct `0x1f`
delimiter.  This is the FIPS 202 empty-message 256-bit prefix. -/
def shake256EmptyPrefix : List UInt8 :=
  [0x46, 0xb9, 0xdd, 0x2b, 0x0b, 0xa8, 0x8d, 0x13,
   0x23, 0x3b, 0x3f, 0xeb, 0x74, 0x3e, 0xeb, 0x24,
   0x3f, 0xcd, 0x52, 0xea, 0x62, 0xb8, 0x1b, 0x82,
   0xb5, 0x0c, 0x27, 0x64, 0x6e, 0xd5, 0x76, 0x2f]

def shake256EmptyConforms : Bool :=
  cshake256Bytes [] [] == shake256EmptyPrefix

def checkShake256Empty : IO Unit := do
  unless shake256EmptyConforms do
    throw (IO.userError "FIPS 202 SHAKE256 empty-message mismatch")

#eval checkShake256Empty

#print axioms digestCodec
#print axioms cshake256Bytes_length
#print axioms hash_digest_lt
#print axioms hash_digest_lt_two_pow_256

end Minidregg.Compiler.Sp800185Cshake256
