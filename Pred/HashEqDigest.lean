/-
# Pred.HashEqDigest — the commitment the `hashEq` atom opens

`Pred.hashEq value blinder commit` (Pred/Core) is true iff the `commit` slot holds the
cSHAKE256 digest of the canonical encoding of an `Opening`: the cell the step is about (the
`request/target` slot), the three slot names, and the values at `value` and `blinder`.

Encoding, all big-endian and fixed-width, so a client rebuilds it with `int.to_bytes`:

| part    | bytes                         | domain                         |
|---------|-------------------------------|--------------------------------|
| cell    | 8                             | `0 ≤ cell < 2^64`              |
| name ×3 | 4-byte length ‖ UTF-8 bytes   | length `< 2^32`                |
| value   | 32, of `value + 2^255`        | `-2^255 ≤ value < 2^255`       |
| blinder | 32                            | `0 ≤ blinder < 2^256`          |

The digest is the 32 output bytes of `cSHAKE256(N = "", S = "DREGG.PRED.HASHEQ/v1")`, read
big-endian as a natural. The function is `Compiler.Sp800185Cshake256.cshake256Bytes`, the same
executable cSHAKE256 the kernel's request digests use, under this atom's own customization string:
the one-customization-per-purpose discipline of the private-cell envelope
(`native/resource-client/src/private.rs`, `DREGG.PRIVATE-CELL.COMMIT/v1`). The blinder is the
envelope's 32-byte uniform `r`. Outside the domain an opening is undefined and the atom fails
closed (Pred/Core).

Imports: Init and the leaf `Compiler.Sp800185Cshake256Core` (itself Init plus
`Mathlib.Data.Nat.Digits.Defs`, no candidate code), so `Pred` stays inside its boundary in
substance; the module path is the only `Compiler` name `Pred` now imports.
-/
import Compiler.Sp800185Cshake256Core

namespace Minidregg.Pred.HashEqDigest

set_option autoImplicit false

/-! ## §1. Fixed-width big-endian bytes -/

/-- The low `w` bytes of `n`, big-endian. -/
def be : Nat → Nat → List UInt8
  | 0, _ => []
  | w + 1, n => be w (n / 256) ++ [UInt8.ofNat (n % 256)]

/-- Big-endian bytes read back as a natural. -/
def ofBE (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

@[simp] theorem length_be (w n : Nat) : (be w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [be, ih]

theorem be_injective {w n m : Nat} (hn : n < 256 ^ w) (hm : m < 256 ^ w)
    (h : be w n = be w m) : n = m := by
  induction w generalizing n m with
  | zero => simp at hn hm; omega
  | succ w ih =>
    simp only [be] at h
    obtain ⟨hhi, hlo⟩ := List.append_inj h (by simp)
    have hbyte : (UInt8.ofNat (n % 256)).toNat = (UInt8.ofNat (m % 256)).toNat := by
      rw [List.cons.inj hlo |>.1]
    simp only [UInt8.toNat_ofNat'] at hbyte
    have hpow : 256 ^ (w + 1) = 256 ^ w * 256 := Nat.pow_succ ..
    have hn' : n / 256 < 256 ^ w := (Nat.div_lt_iff_lt_mul (by decide)).mpr (hpow ▸ hn)
    have hm' : m / 256 < 256 ^ w := (Nat.div_lt_iff_lt_mul (by decide)).mpr (hpow ▸ hm)
    have hq := ih hn' hm' hhi
    have h8 : (2 : Nat) ^ 8 = 256 := by decide
    rw [h8] at hbyte
    omega

/-! ## §2. Names -/

/-- The UTF-8 bytes of a string. -/
def utf8 (s : String) : List UInt8 := s.toUTF8.data.toList

theorem utf8_injective {s t : String} (h : utf8 s = utf8 t) : s = t := by
  simp only [utf8, String.toUTF8_eq_toByteArray] at h
  exact String.toByteArray_inj.mp (ByteArray.ext (Array.toList_inj.mp h))

/-- A length-prefixed name: 4-byte big-endian UTF-8 length, then the bytes. -/
def name (s : String) : List UInt8 := be 4 (utf8 s).length ++ utf8 s

theorem name_split {s t : String} {rest rest' : List UInt8}
    (hs : (utf8 s).length < 2 ^ 32) (ht : (utf8 t).length < 2 ^ 32)
    (h : name s ++ rest = name t ++ rest') : s = t ∧ rest = rest' := by
  simp only [name, List.append_assoc] at h
  obtain ⟨hlen, htail⟩ := List.append_inj h (by simp)
  have h32 : (2 : Nat) ^ 32 = 256 ^ 4 := by decide
  rw [h32] at hs ht
  have hl := be_injective hs ht hlen
  obtain ⟨hu, hr⟩ := List.append_inj htail hl
  exact ⟨utf8_injective hu, hr⟩

/-! ## §3. The opening and its preimage -/

/-- Everything a commitment binds: the cell, the three slot names, the value and the blinder. -/
structure Opening where
  cell : Int
  valueSlot : String
  blinderSlot : String
  commitSlot : String
  value : Int
  blinder : Int
deriving DecidableEq, Repr

/-- The encoding's domain. -/
def Opening.Admissible (o : Opening) : Prop :=
  0 ≤ o.cell ∧ o.cell < 2 ^ 64 ∧
  (utf8 o.valueSlot).length < 2 ^ 32 ∧ (utf8 o.blinderSlot).length < 2 ^ 32 ∧
  (utf8 o.commitSlot).length < 2 ^ 32 ∧
  -2 ^ 255 ≤ o.value ∧ o.value < 2 ^ 255 ∧
  0 ≤ o.blinder ∧ o.blinder < 2 ^ 256

instance (o : Opening) : Decidable o.Admissible := by
  unfold Opening.Admissible; infer_instance

/-- The canonical preimage. -/
def Opening.preimage (o : Opening) : List UInt8 :=
  be 8 o.cell.toNat ++ name o.valueSlot ++ name o.blinderSlot ++ name o.commitSlot ++
    be 32 (o.value + 2 ^ 255).toNat ++ be 32 o.blinder.toNat

private theorem toNat_eq {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a.toNat = b.toNat) :
    a = b := by
  have := congrArg (fun n : Nat => (n : Int)) h
  simp only [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb] at this
  exact this

private theorem toNat_lt {a : Int} {k : Nat} (ha : 0 ≤ a) (hk : a < (k : Int)) : a.toNat < k := by
  omega

/-- **The encoding is injective on its domain.** Distinct admissible openings have distinct
preimages, so any digest equality between distinct openings is a collision of the hash. -/
theorem preimage_injective {a b : Opening} (ha : a.Admissible) (hb : b.Admissible)
    (h : a.preimage = b.preimage) : a = b := by
  obtain ⟨ac0, ac1, av, ab, acm, ax0, ax1, ar0, ar1⟩ := ha
  obtain ⟨bc0, bc1, bv, bb, bcm, bx0, bx1, br0, br1⟩ := hb
  simp only [Opening.preimage, List.append_assoc] at h
  obtain ⟨hcell, h⟩ := List.append_inj h (by simp)
  obtain ⟨hv, h⟩ := name_split av bv h
  obtain ⟨hbl, h⟩ := name_split ab bb h
  obtain ⟨hcm, h⟩ := name_split acm bcm h
  obtain ⟨hx, hr⟩ := List.append_inj h (by simp)
  have p8 : ((256 ^ 8 : Nat) : Int) = 2 ^ 64 := by decide
  have p32 : ((256 ^ 32 : Nat) : Int) = 2 ^ 256 := by decide
  have hc : a.cell = b.cell :=
    toNat_eq ac0 bc0 (be_injective (toNat_lt ac0 (p8 ▸ ac1)) (toNat_lt bc0 (p8 ▸ bc1)) hcell)
  have hx' : a.value + 2 ^ 255 = b.value + 2 ^ 255 :=
    toNat_eq (by omega) (by omega)
      (be_injective (toNat_lt (by omega) (by rw [p32]; omega))
        (toNat_lt (by omega) (by rw [p32]; omega)) hx)
  have hr' : a.blinder = b.blinder :=
    toNat_eq ar0 br0 (be_injective (toNat_lt ar0 (p32 ▸ ar1)) (toNat_lt br0 (p32 ▸ br1)) hr)
  cases a; cases b
  simp only [Opening.mk.injEq] at *
  exact ⟨hc, hv, hbl, hcm, by omega, hr'⟩

/-- Every admissible preimage has the same length for a fixed set of names: the value and blinder
widths are fixed. (This is what a length hash cannot see past.) -/
theorem preimage_length (o : Opening) :
    o.preimage.length =
      8 + (4 + (utf8 o.valueSlot).length) + (4 + (utf8 o.blinderSlot).length) +
        (4 + (utf8 o.commitSlot).length) + 32 + 32 := by
  simp [Opening.preimage, name]
  omega

/-! ## §4. The digest, generic in the hash, and its deployed instance -/

/-- A byte hash. -/
abbrev Hash := List UInt8 → List UInt8

/-- The digest an opening commits to under `H`, as the integer the commit slot holds. -/
def digestWith (H : Hash) (o : Opening) : Int := (ofBE (H o.preimage) : Int)

/-- The customization string of this atom's cSHAKE256. -/
def customization : List UInt8 := utf8 "DREGG.PRED.HASHEQ/v1"

open Minidregg.Compiler.Sp800185Cshake256 (customizationPrefix cshake256Bytes squeeze32
  absorbPadded padForRate natBytesBE bytepad encodeString leftEncode rateBytes) in
/-- The SP 800-185 prefix `bytepad(encode_string("") ‖ encode_string(S), 136)` for this `S`,
spelled out (`left_encode 136`, `encode_string ""`, `left_encode 160`, the 20 bytes of `S`, 110
zero bytes). `frame_eq` proves it is the cSHAKE module's own `customizationPrefix`; it is spelled
out so the evaluator's definition stays a literal (the core's `natBytesBE` is structural since
CH-CLIENT-1 and no longer reaches `Nat.digits`), which keeps `Pred.eval`'s axiom closure at
`[propext, Quot.sound]`. -/
def frame : List UInt8 := [1, 136, 1, 0, 1, 160] ++ customization ++ List.replicate 110 0

open Minidregg.Compiler.Sp800185Cshake256 (squeeze32 absorbPadded padForRate) in
/-- **The deployed hash**: cSHAKE256 (SP 800-185, empty function name, 256-bit output) under
this atom's customization, through the kernel's executable Keccak-f[1600] sponge. Equal to
`cshake256Bytes customization` (`deployed_eq_cshake256Bytes`). -/
def deployed : Hash := fun input => squeeze32 (absorbPadded (padForRate (frame ++ input) 0x04))

theorem customization_length : customization.length = 20 := by decide

open Minidregg.Compiler.Sp800185Cshake256 in
theorem frame_eq : customizationPrefix customization = frame := by
  decide

open Minidregg.Compiler.Sp800185Cshake256 in
/-- The spelled-out sponge **is** the kernel's cSHAKE256 at this customization: one function, not
a second implementation. -/
theorem deployed_eq_cshake256Bytes : deployed = cshake256Bytes customization := by
  funext input
  have hne : (customization = []) = False := by
    apply propext; constructor
    · intro h; have := congrArg List.length h; rw [customization_length] at this; cases this
    · intro h; cases h
  simp only [deployed, cshake256Bytes, hne, if_false, frame_eq]

open Minidregg.Compiler.Sp800185Cshake256 (absorbPadded padForRate squeeze32) in
open Minidregg.Compiler.Sp800185Cshake256.Fast in
/-- The deployed hash on the compiled path: frame and input pushed once into a
byte array, absorbed by the word permutation (`Compiler.Sp800185Cshake256Fast`). -/
def deployedFast : Hash := fun input =>
  spongeBytes (pushList (pushList ByteArray.empty frame) input) 0x04

open Minidregg.Compiler.Sp800185Cshake256.Fast in
theorem deployedFast_eq : deployedFast = deployed := by
  funext input
  simp only [deployedFast, deployed, sponge_fast_eq, pushList_data, empty_data, List.nil_append]

/-- The compiled `hashEq` atom runs the fast path; `deployed` stays the definition. -/
@[csimp] theorem deployed_eq_fast : deployed = deployedFast := deployedFast_eq.symm

/-- A collision of `H` at the integer reading of its output. -/
def Collision (H : Hash) : Prop := ∃ a b : List UInt8, a ≠ b ∧ ofBE (H a) = ofBE (H b)

/-- **Binds or collides.** Two admissible openings with equal digests are equal, or `H` has a
collision. Nothing about cSHAKE is assumed here; the disjunct is where its collision resistance
enters. -/
theorem binds_or_collides (H : Hash) {a b : Opening} (ha : a.Admissible) (hb : b.Admissible)
    (h : digestWith H a = digestWith H b) : a = b ∨ Collision H := by
  by_cases hab : a = b
  · exact .inl hab
  · refine .inr ⟨a.preimage, b.preimage, fun hp => hab (preimage_injective ha hb hp), ?_⟩
    simpa [digestWith, Int.ofNat_inj] using h

/-! ## §5. The refutable pole: a length hash -/

/-- The weakest hash that still reads its input: the 32-byte length. -/
def lengthHash : Hash := fun bytes => be 32 bytes.length

/-- The collision disjunct is not vacuous: the length hash has one. -/
theorem lengthHash_collides : Collision lengthHash :=
  ⟨[0], [1], by decide, rfl⟩

/-- **Under a length hash, binding fails for every opening**: changing the value (or the blinder)
inside the domain never changes the digest. So `binds_or_collides` is carried by the hash, not by
the encoding. -/
theorem lengthHash_binding_fails (o : Opening) (value blinder : Int) :
    digestWith lengthHash { o with value := value, blinder := blinder } =
      digestWith lengthHash o := by
  simp only [digestWith, lengthHash, preimage_length]

/-! ## §6. Axiom pins — `deployed` (and so `Pred.eval`) reaches no `Classical.choice`. -/

/-- info: 'Minidregg.Pred.HashEqDigest.deployed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployed
/-- info: 'Minidregg.Pred.HashEqDigest.deployed_eq_cshake256Bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_eq_cshake256Bytes
/-- info: 'Minidregg.Pred.HashEqDigest.preimage_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms preimage_injective
/-- info: 'Minidregg.Pred.HashEqDigest.binds_or_collides' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms binds_or_collides
/-- info: 'Minidregg.Pred.HashEqDigest.lengthHash_binding_fails' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lengthHash_binding_fails
/-- info: 'Minidregg.Pred.HashEqDigest.lengthHash_collides' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms lengthHash_collides
/-- info: 'Minidregg.Pred.HashEqDigest.deployed_eq_fast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_eq_fast

end Minidregg.Pred.HashEqDigest
