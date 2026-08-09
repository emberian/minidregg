/-
# `Compiler/WideDigestAir.lean` — nine-limb digest absorption in the emitted AIR

The runtime representation in `prover/src/wide.rs` is a fixed-width integer with nine
canonical BabyBear limbs, least significant first.  Its Fiat--Shamir encoding is the
eleven-field sequence

`WDG1 || domain || limb[0] || ... || limb[8]`.

This file realizes exactly that *representation boundary* in the existing compiler IR.
`wideDigestAbsorbGadget` pins the tag, domain, and all nine limb copies; it is flattened
and emitted by `Compiler.emit`, not by a second descriptor language.  Accepted digest
limbs are packaged as `Theory.Bignum.Canonical babyBearP 9`, the source and absorbed
limb lists are equal over natural canonical representatives, and therefore their
little-endian denotations are equal.

No cryptographic claim is made.  In particular this does not prove that the runtime's
demo `hash_fields` realizes a collision-resistant hash or that a Rust byte parser
rejects non-canonical `u32` limbs before field conversion.  The latter is the exact
remaining `[AIR-wide-digest-byte-decode]` residual: once a value is already a `ZMod p`,
its canonical representative is intrinsic and a raw `p` cannot be distinguished from
raw `0`.  A 30-bit `rangeGadget` would reject valid BabyBear values, while its 31-bit
form lacks the `2^31 <= p` lift hypothesis.  Closing the raw seam needs a `< p`
comparison/lookup or a proved strict byte decoder, not a lossy bit-range surrogate.

Nor does this gadget execute `Transcript::absorb`'s add-then-permute duplex schedule: it
pins the exact eleven-field input sequence that schedule must consume.  Identifying the
runtime sponge transition with a Lean-authored AIR permutation remains
`[RECURSE-fs-sponge]`; composing this encoding vector with that transition must use the
same wires.  Thus representation is closed here while scheduling, permutation parameters,
unverified Rust execution/generated-code authority, and `[COMMIT-CR]` remain separate and explicit.
-/
import Compiler.AirBignum
import Compiler.EmitSerialize

namespace Minidregg.Compiler.WideDigestAir

open Minidregg.Compiler
open Minidregg.Theory

set_option autoImplicit false

/-- Runtime digest width (`prover/src/wide.rs::DIGEST_LIMBS`). -/
def digestWidth : Nat := 9

/-- Runtime transcript width: tag, domain, and nine digest limbs. -/
def encodedWidth : Nat := digestWidth + 2

/-- Runtime transcript tag `"WDG1"` (`prover/src/wide.rs::DIGEST_ENCODING_TAG`). -/
def digestEncodingTag : Nat := 0x57444731

theorem digestEncodingTag_lt_babyBearP : digestEncodingTag < babyBearP := by
  norm_num [digestEncodingTag, babyBearP]

/-- Nine BabyBear limbs have enough positional capacity for every 248-bit value. -/
theorem digest_capacity_248 : 2 ^ 248 <= babyBearP ^ digestWidth := by
  exact Bignum.bits_248_fit_nine_radix_2013265921_limbs

/-- Why a 30-bit `rangeGadget` is not the runtime's canonical-limb predicate. -/
theorem valid_babyBear_limbs_exceed_30_bits : 2 ^ 30 < babyBearP := by
  norm_num [babyBearP]

/-- Why the existing prime-field range lift cannot certify a 31-bit decomposition. -/
theorem thirty_one_bit_range_does_not_fit_babyBear : babyBearP < 2 ^ 31 := by
  norm_num [babyBearP]

/-- Wires at the digest-to-transcript absorption boundary. -/
structure AbsorbWires (Idx : Type) where
  digest : Fin digestWidth -> Idx
  domain : Idx
  encoded : Fin encodedWidth -> Idx

/-- Position of digest limb `i` after the two-field transcript prefix. -/
def encodedLimb (i : Fin digestWidth) : Fin encodedWidth :=
  ⟨i.val + 2, by
    have := i.isLt
    simp [digestWidth, encodedWidth] at this ⊢
    omega⟩

/-- Tag position in the eleven-field encoding. -/
def tagPos : Fin encodedWidth := ⟨0, by norm_num [encodedWidth, digestWidth]⟩

/-- Domain position in the eleven-field encoding. -/
def domainPos : Fin encodedWidth := ⟨1, by norm_num [encodedWidth, digestWidth]⟩

variable {F : Type} [Field F] {Idx : Type}

/-- Equality assertion `lhs = rhs` in the one arithmetic term DSL. -/
def eqTerm (lhs rhs : Idx) : Term (AirSig F Idx) :=
  add' (vr lhs) (mul' (cst (-1)) (vr rhs))

/-- Constant pin assertion `wire = value` in the same DSL. -/
def pinTerm (wire : Idx) (value : F) : Term (AirSig F Idx) :=
  add' (vr wire) (cst (-value))

theorem eqTerm_correct (asg : Idx -> F) (lhs rhs : Idx) :
    accepts asg (eqTerm lhs rhs) <-> asg lhs = asg rhs := by
  unfold accepts eqTerm
  simp only [eval_add', eval_mul', eval_cst, eval_vr, neg_one_mul, add_neg_eq_zero]

theorem pinTerm_correct (asg : Idx -> F) (wire : Idx) (value : F) :
    accepts asg (pinTerm wire value) <-> asg wire = value := by
  unfold accepts pinTerm
  simp only [eval_add', eval_cst, eval_vr, add_neg_eq_zero]

/-- Pointwise limb-copy constraints. -/
def limbCopySystem (w : AbsorbWires Idx) : ConstraintSystem F Idx :=
  (List.finRange digestWidth).map fun i => eqTerm (w.encoded (encodedLimb i)) (w.digest i)

theorem limbCopySystem_correct (asg : Idx -> F) (w : AbsorbWires Idx) :
    systemAccepts asg (limbCopySystem w) <->
      forall i, asg (w.encoded (encodedLimb i)) = asg (w.digest i) := by
  constructor
  · intro h i
    apply (eqTerm_correct asg _ _).mp
    apply h _
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  · intro h t ht
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht
    exact (eqTerm_correct asg _ _).mpr (h i)

/-- The exact runtime absorption shape: `WDG1 || domain || nine limbs`. -/
def wideDigestAbsorbGadget (w : AbsorbWires Idx) : ConstraintSystem BabyBear Idx :=
  [pinTerm (w.encoded tagPos) (digestEncodingTag : BabyBear),
    eqTerm (w.encoded domainPos) w.domain] ++ limbCopySystem w

/-- Keystone iff: every accepted field is precisely the runtime absorption sequence. -/
theorem wideDigestAbsorbGadget_correct (asg : Idx -> BabyBear) (w : AbsorbWires Idx) :
    systemAccepts asg (wideDigestAbsorbGadget w) <->
      asg (w.encoded tagPos) = (digestEncodingTag : BabyBear) /\
      asg (w.encoded domainPos) = asg w.domain /\
      (forall i, asg (w.encoded (encodedLimb i)) = asg (w.digest i)) := by
  rw [wideDigestAbsorbGadget, systemAccepts_append, limbCopySystem_correct]
  simp only [systemAccepts_cons, systemAccepts_nil, and_true, pinTerm_correct, eqTerm_correct]
  tauto

/-! ## Canonical natural-number reading through `Theory.Bignum` -/

/-- Canonical representatives of a nine-limb field word, little-endian. -/
def digestVals (asg : Idx -> BabyBear) (limb : Fin digestWidth -> Idx) : List Nat :=
  AirBignum.limbVals asg limb

/-- Every BabyBear field word has a canonical base-`p`, width-nine bignum reading. -/
theorem digestVals_canonical (asg : Idx -> BabyBear) (limb : Fin digestWidth -> Idx) :
    Bignum.Canonical babyBearP digestWidth (digestVals asg limb) := by
  constructor
  · intro digit hdigit
    rw [digestVals, AirBignum.limbVals, List.mem_ofFn] at hdigit
    obtain ⟨i, rfl⟩ := hdigit
    exact ZMod.val_lt _
  · simp [digestVals, AirBignum.limbVals, digestWidth]

/-- Casting a canonical natural representative back into BabyBear is exact. -/
theorem digestVal_cast_exact (asg : Idx -> BabyBear) (limb : Fin digestWidth -> Idx)
    (i : Fin digestWidth) : ((asg (limb i)).val : BabyBear) = asg (limb i) :=
  ZMod.natCast_zmod_val _

/-- **Representation soundness.** Acceptance yields canonical source and absorbed
nine-limb bignums, equality of their natural limbs, and equality of their positional
denotations.  This is the exact field-to-integer boundary; no hash property is used. -/
theorem wideDigestAbsorbGadget_sound (asg : Idx -> BabyBear) (w : AbsorbWires Idx)
    (h : systemAccepts asg (wideDigestAbsorbGadget w)) :
    Bignum.Canonical babyBearP digestWidth (digestVals asg w.digest) /\
    Bignum.Canonical babyBearP digestWidth
      (digestVals asg (fun i => w.encoded (encodedLimb i))) /\
    digestVals asg (fun i => w.encoded (encodedLimb i)) = digestVals asg w.digest /\
    Bignum.denoteNat babyBearP
        (digestVals asg (fun i => w.encoded (encodedLimb i))) =
      Bignum.denoteNat babyBearP (digestVals asg w.digest) := by
  obtain ⟨-, -, hlimb⟩ := (wideDigestAbsorbGadget_correct asg w).mp h
  have hfun :
      (fun i => (asg (w.encoded (encodedLimb i))).val) =
        (fun i => (asg (w.digest i)).val) := by
    funext i
    exact congrArg ZMod.val (hlimb i)
  have hlists : digestVals asg (fun i => w.encoded (encodedLimb i)) =
      digestVals asg w.digest := by
    simp only [digestVals, AirBignum.limbVals, hfun]
  exact ⟨digestVals_canonical asg w.digest,
    digestVals_canonical asg (fun i => w.encoded (encodedLimb i)), hlists,
    congrArg (Bignum.denoteNat babyBearP) hlists⟩

/-! ## The existing first-order emit seam -/

/-- No duplicate descriptor language: the generic proved emitter consumes this gadget. -/
theorem emit_wideDigestAbsorb_iff (ix : Idx -> Nat) (hinj : Function.Injective ix)
    (nPublic nVars : Nat) (hbound : forall i, ix i < nVars)
    (asg : Idx -> BabyBear) (w : AbsorbWires Idx) :
    (exists wv : Nat -> BabyBear, (forall i, wv (ix i) = asg i) /\
      descriptorHolds (emit ix nPublic nVars (wideDigestAbsorbGadget w)) wv) <->
      systemAccepts asg (wideDigestAbsorbGadget w) :=
  emit_accepts_iff ix hinj nPublic nVars hbound asg (wideDigestAbsorbGadget w)

/-! ## Positive and tamper teeth on the exact 21-wire runtime shape -/

/-- Layout: digest `0..8`, domain `9`, encoded transcript `10..20`. -/
def demoWires : AbsorbWires (Fin 21) where
  digest := fun i => ⟨i.val, by
    have := i.isLt
    simp [digestWidth] at this ⊢
    omega⟩
  domain := 9
  encoded := fun i => ⟨10 + i.val, by
    have := i.isLt
    simp [encodedWidth, digestWidth] at this ⊢
    omega⟩

/-- Honest `WDG1 || 17 || [1,2,...,9]` absorption. -/
def demoGood : Fin 21 -> BabyBear :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 17,
    digestEncodingTag, 17, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- Tamper one absorbed limb while keeping the source digest fixed. -/
def demoTampered : Fin 21 -> BabyBear :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 17,
    digestEncodingTag, 17, 1, 2, 3, 4, 5, 99, 7, 8, 9]

/-- Positive pole: the honest encoding is accepted. -/
example : systemAccepts demoGood (wideDigestAbsorbGadget demoWires) := by decide

/-- Negative pole: changing one absorbed limb is rejected. -/
example : ¬ systemAccepts demoTampered (wideDigestAbsorbGadget demoWires) := by decide

/-- The positive pole survives the real emitter. -/
example : exists wv : Nat -> BabyBear,
    (forall i : Fin 21, wv i.val = demoGood i) /\
    descriptorHolds (emit Fin.val 11 21 (wideDigestAbsorbGadget demoWires)) wv :=
  (emit_accepts_iff_fin 21 11 demoGood (wideDigestAbsorbGadget demoWires)).mpr (by decide)

/-- Strong emitted tooth: no auxiliary-wire choices can repair the tampered encoding. -/
example : ¬ (exists wv : Nat -> BabyBear,
    (forall i : Fin 21, wv i.val = demoTampered i) /\
    descriptorHolds (emit Fin.val 11 21 (wideDigestAbsorbGadget demoWires)) wv) := fun h =>
  (by decide : ¬ systemAccepts demoTampered (wideDigestAbsorbGadget demoWires))
    ((emit_accepts_iff_fin 21 11 demoTampered (wideDigestAbsorbGadget demoWires)).mp h)

#print axioms wideDigestAbsorbGadget_correct
#print axioms digestVals_canonical
#print axioms digestVal_cast_exact
#print axioms wideDigestAbsorbGadget_sound
#print axioms emit_wideDigestAbsorb_iff

end Minidregg.Compiler.WideDigestAir
