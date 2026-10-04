/-
# Theory.Sp800185Cshake256Conformance -- executable standard vectors

These build-time checks exercise the Lean-owned executable core against the
published NIST SP 800-185 cSHAKE sample and the FIPS 202 SHAKE256 empty-message
prefix.  They are kept out of the controller API's import surface, while the
`Theory` umbrella imports this module so a complete build still executes
both checks.  They live beside the code they check (moved with the cSHAKE256
leaf from `Compiler` to `Theory`, W30-CORE4-DIGEST).

The checks are conformance teeth, not collision-resistance or random-oracle
theorems.  The two `#eval` checks use ordinary Lean evaluation; since
`cshake256Bytes` carries the `@[csimp]` of `Sp800185Cshake256Fast`, they run
the fast path.  The named `native_decide` theorems at the end state the same
vectors of `Fast.cshake256Fast` directly and are pinned with their
`native_decide` axiom.  The kernel cannot evaluate the permutation (one
Keccak-f under `whnf` is far beyond any heartbeat budget), so a vector can only
be a compiled-evaluation fact; the equality of the fast path to the spec for
every input is `Fast.cshake256Fast_eq`, a kernel-checked proof.
-/

import Theory.Sp800185Cshake256Core

namespace Minidregg.Compiler.Sp800185Cshake256

set_option autoImplicit false

/-! ## NIST SP 800-185 sample tooth

Sample 3 uses `X = 00 01 02 03`, empty function-name, customization
`"Email Signature"`, and a 512-bit output.  The check compares the first
256 bits selected by this controller.
-/

def emailSignature : List UInt8 :=
  [0x45, 0x6d, 0x61, 0x69, 0x6c, 0x20, 0x53, 0x69,
   0x67, 0x6e, 0x61, 0x74, 0x75, 0x72, 0x65]

def nistSample3Prefix : List UInt8 :=
  [0xd0, 0x08, 0x82, 0x8e, 0x2b, 0x80, 0xac, 0x9d,
   0x22, 0x18, 0xff, 0xee, 0x1d, 0x07, 0x0c, 0x48,
   0xb8, 0xe4, 0xc8, 0x7b, 0xff, 0x32, 0xc9, 0x69,
   0x9d, 0x5b, 0x68, 0x96, 0xee, 0xe0, 0xed, 0xd1]

def nistSample3Conforms : Bool :=
  cshake256Bytes emailSignature [0, 1, 2, 3] == nistSample3Prefix

def checkNistSample3 : IO Unit := do
  unless nistSample3Conforms do
    throw (IO.userError "SP 800-185 cSHAKE256 sample 3 mismatch")

#eval checkNistSample3

/-! ## FIPS 202 SHAKE256 compatibility tooth -/

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

/-! ## The same vectors, named, on the fast path -/

/-- NIST SP 800-185 cSHAKE256 sample 3 (first 256 bits) on the fast path. -/
theorem cshake256Fast_conforms_nist_sample3 :
    Fast.cshake256Fast emailSignature [0, 1, 2, 3] = nistSample3Prefix := by native_decide

/-- FIPS 202 SHAKE256 of the empty message (first 256 bits) on the fast path. -/
theorem cshake256Fast_conforms_shake256_empty :
    Fast.cshake256Fast [] [] = shake256EmptyPrefix := by native_decide

end Minidregg.Compiler.Sp800185Cshake256

/-- info: 'Minidregg.Compiler.Sp800185Cshake256.cshake256Fast_conforms_nist_sample3' depends on axioms: [propext, Quot.sound, Minidregg.Compiler.Sp800185Cshake256.cshake256Fast_conforms_nist_sample3._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.Sp800185Cshake256.cshake256Fast_conforms_nist_sample3
/-- info: 'Minidregg.Compiler.Sp800185Cshake256.cshake256Fast_conforms_shake256_empty' depends on axioms: [propext, Quot.sound, Minidregg.Compiler.Sp800185Cshake256.cshake256Fast_conforms_shake256_empty._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.Sp800185Cshake256.cshake256Fast_conforms_shake256_empty
