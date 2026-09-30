/-
# Compiler.Sp800185Kmac256 -- KMAC256 on the Lean-owned Keccak core

NIST SP 800-185 KMAC256 with a 256-bit output:

  KMAC256(K, X, 256, S) = cSHAKE256(bytepad(encode_string(K), 136) ‖ X ‖ right_encode(256),
                                    256, "KMAC", S)

The permutation, padding and `bytepad`/`encode_string` framing are the ones
`Sp800185Cshake256Core` already exports; this module adds `right_encode`, the
function-name field, and nothing else.  It is the host's checkpoint and log
authenticator (`Compiler.DurableCheckpointCodec`).  No unforgeability theorem
is stated here: KMAC's PRF security is the standard's, not a Lean proof.

The two conformance theorems compare against an independent implementation
(pycryptodome 3.x `Crypto.Hash.KMAC256`, `mac_len=32`); NIST publishes KMAC256
samples only at L = 512, and L enters the MAC through `right_encode(L)`.
-/
import Compiler.Sp800185Cshake256Core

namespace Minidregg.Compiler.Sp800185Cshake256

set_option autoImplicit false

/-- SP 800-185 `right_encode`: the minimal big-endian bytes, then their count. -/
def rightEncode (value : Nat) : List UInt8 :=
  let bytes := natBytesBE value
  bytes ++ [UInt8.ofNat bytes.length]

/-- The encoded function name and customization for KMAC. -/
def kmacPrefix (customization : List UInt8) : List UInt8 :=
  bytepad (encodeString "KMAC".toUTF8.toList ++ encodeString customization) rateBytes

/-- KMAC256 with a 32-byte tag. -/
def kmac256Bytes (key customization input : List UInt8) : List UInt8 :=
  let newX := bytepad (encodeString key) rateBytes ++ input ++ rightEncode 256
  squeeze32 (absorbPadded (padForRate (kmacPrefix customization ++ newX) 0x04))

theorem kmac256Bytes_length (key customization input : List UInt8) :
    (kmac256Bytes key customization input).length = 32 := by
  simp [kmac256Bytes, squeeze32, outputBytes]

/-! ## Conformance against an independent implementation -/

def kmacVectorKey : List UInt8 := (List.range 32).map fun i => UInt8.ofNat (0x40 + i)

/-- pycryptodome: `KMAC256.new(key=bytes(range(0x40,0x60)), mac_len=32,
custom=b"My Tagged Application").update(bytes([0,1,2,3]))`. -/
def kmacVectorTagged : List UInt8 :=
  [0xf2, 0xd9, 0x5c, 0x33, 0xc9, 0xa2, 0x01, 0xeb, 0x10, 0xc5, 0x24, 0xb9, 0x08, 0x4b, 0x4b, 0xac,
   0xae, 0x00, 0x92, 0xf8, 0x69, 0x12, 0x2d, 0xf7, 0xd7, 0x87, 0x0b, 0x92, 0xc8, 0x42, 0xe0, 0x5b]

/-- pycryptodome, same key, `custom=b"DREGG/NATIVE-HOST/CHECKPOINT-MAC/v1"`,
message `b"abc"`. -/
def kmacVectorCheckpoint : List UInt8 :=
  [0xb1, 0x86, 0x2d, 0xc6, 0x69, 0x01, 0xcf, 0x8a, 0xd0, 0xde, 0x93, 0x23, 0x5e, 0x93, 0xa4, 0x87,
   0xec, 0x11, 0x0f, 0x46, 0xa6, 0x68, 0xa9, 0xb5, 0x12, 0x2e, 0x0d, 0xcb, 0x1e, 0xfa, 0x71, 0x1f]

theorem kmac256_conforms_tagged :
    kmac256Bytes kmacVectorKey "My Tagged Application".toUTF8.toList [0, 1, 2, 3] =
      kmacVectorTagged := by native_decide

theorem kmac256_conforms_checkpoint_customization :
    kmac256Bytes kmacVectorKey "DREGG/NATIVE-HOST/CHECKPOINT-MAC/v1".toUTF8.toList
      "abc".toUTF8.toList = kmacVectorCheckpoint := by native_decide

/-- The key is load-bearing: the same message and customization under a
different key gives a different tag. -/
theorem kmac256_key_separates :
    kmac256Bytes (kmacVectorKey.map (· + 1)) "My Tagged Application".toUTF8.toList
      [0, 1, 2, 3] ≠ kmacVectorTagged := by native_decide

end Minidregg.Compiler.Sp800185Cshake256

/-- info: 'Minidregg.Compiler.Sp800185Cshake256.kmac256Bytes_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.Sp800185Cshake256.kmac256Bytes_length
/-- info: 'Minidregg.Compiler.Sp800185Cshake256.kmac256_conforms_tagged' depends on axioms: [propext, Classical.choice, Quot.sound, Minidregg.Compiler.Sp800185Cshake256.kmac256_conforms_tagged._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.Sp800185Cshake256.kmac256_conforms_tagged
/-- info: 'Minidregg.Compiler.Sp800185Cshake256.kmac256_conforms_checkpoint_customization' depends on axioms: [propext, Classical.choice, Quot.sound, Minidregg.Compiler.Sp800185Cshake256.kmac256_conforms_checkpoint_customization._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.Sp800185Cshake256.kmac256_conforms_checkpoint_customization
/-- info: 'Minidregg.Compiler.Sp800185Cshake256.kmac256_key_separates' depends on axioms: [propext, Classical.choice, Quot.sound, Minidregg.Compiler.Sp800185Cshake256.kmac256_key_separates._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.Sp800185Cshake256.kmac256_key_separates
