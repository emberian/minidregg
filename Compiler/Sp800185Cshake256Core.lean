/-
# Compiler.Sp800185Cshake256Core -- Lean-owned cSHAKE256 computation

This module is the small executable core of the concrete cSHAKE256 backend.
It implements, in Lean:

* Keccak-f[1600], with twenty-four rounds over twenty-five 64-bit lanes;
* the 1088-bit (136-byte) SHAKE256/cSHAKE256 sponge rate;
* SP 800-185 `left_encode`, `encode_string`, and `bytepad` framing;
* the empty-customization SHAKE256 suffix and nonempty cSHAKE suffix; and
* the first 32 squeezed bytes selected by the controller.

The module deliberately has no controller, digest carrier, codec proof, or
build-time conformance vectors.  Keeping this exact computation below those
surfaces lets the vectors run independently and keeps executable definitions
out of the heavy controller module's elaboration unit.  No collision
resistance or random-oracle claim is made here.

SP 800-185 bounds `left_encode` inputs to values whose byte width fits in one
byte.  The total Lean function extends framing outside that standard domain by
truncating the width byte with `UInt8.ofNat`; ordinary finite protocol frames
are far inside the standard bound.
-/

import Init.Data.BitVec
import Mathlib.Data.Nat.Digits.Defs

namespace Minidregg.Compiler.Sp800185Cshake256

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

end Minidregg.Compiler.Sp800185Cshake256
