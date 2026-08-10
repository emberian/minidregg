/-
# Compiler.Ext6Conformance — a genuine BabyBear⁶ challenge field

This file pins the scalar proposed by `[PROVER-challenge-field-unification]`:

  BabyBear[u] / (u⁶ - 31).

Unlike the historical Ext4 fold ring, fieldness is closed here.  Mathlib does
not currently expose the general even-degree binomial criterion, so the proof
uses a Kummer tower:

1. `X³ - 31` is irreducible because 31 is not a cube in BabyBear;
2. if its root were a square in the cubic extension, its norm would make 31 a
   square in BabyBear;
3. `X_pow_mul_sub_C_irreducible` composes the cubic and quadratic steps.

The two large modular-power facts use an explicit 26-step square chain.  Every
step is discharged by `norm_num`; there is no `native_decide` or opaque CAS
certificate in the theorem.  The lane multiplication is then proved equal to
multiplication in the irreducible `AdjoinRoot`, and two known-answer vectors are
shared with the Rust tests.
-/

import Compiler.EmitSerialize
import Mathlib.FieldTheory.KummerExtension

namespace Minidregg.Compiler

open Polynomial IntermediateField

/-! ## §1. Exact nonresidue certificates -/

/-- Turn a natural modular-power equality into the corresponding BabyBear
equality.  This lets each square-chain step remain small and kernel checked. -/
private theorem babyBear_pow_eq_of_mod {a e r : ℕ}
    (h : a ^ e % babyBearP = r % babyBearP) :
    (a : BabyBear) ^ e = (r : BabyBear) := by
  rw [← Nat.cast_pow]
  exact (ZMod.natCast_eq_natCast_iff' _ _ babyBearP).2 h

/-- One step of a repeated-square certificate. -/
private theorem pow_two_succ_congr {a b : BabyBear} (h : a ^ 2 = b) (k : ℕ) :
    a ^ (2 ^ (k + 1)) = b ^ (2 ^ k) := by
  calc
    a ^ (2 ^ (k + 1)) = a ^ (2 * 2 ^ k) := by rw [pow_succ, mul_comm]
    _ = (a ^ 2) ^ (2 ^ k) := by rw [pow_mul]
    _ = b ^ (2 ^ k) := by rw [h]

/-- The sixth-power residue used by the Rabin/Kummer certificate:
`31^((p-1)/6) = 1314723124`. -/
theorem thirty_one_pow_sixth :
    (31 : BabyBear) ^ 335544320 = 1314723124 := by
  have h0 : (31 : BabyBear) ^ 5 = 28629151 := by
    norm_num [BabyBear, babyBearP]
  have h1 : (28629151 : BabyBear) ^ 2 = 1558084728 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h2 : (1558084728 : BabyBear) ^ 2 = 1422208504 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h3 : (1422208504 : BabyBear) ^ 2 = 1678705229 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h4 : (1678705229 : BabyBear) ^ 2 = 1771892767 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h5 : (1771892767 : BabyBear) ^ 2 = 940487245 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h6 : (940487245 : BabyBear) ^ 2 = 1516982208 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h7 : (1516982208 : BabyBear) ^ 2 = 792115306 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h8 : (792115306 : BabyBear) ^ 2 = 452791590 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h9 : (452791590 : BabyBear) ^ 2 = 1605829134 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h10 : (1605829134 : BabyBear) ^ 2 = 2008025366 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h11 : (2008025366 : BabyBear) ^ 2 = 456279664 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h12 : (456279664 : BabyBear) ^ 2 = 1492617483 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h13 : (1492617483 : BabyBear) ^ 2 = 1252078097 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h14 : (1252078097 : BabyBear) ^ 2 = 12770214 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h15 : (12770214 : BabyBear) ^ 2 = 1812738875 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h16 : (1812738875 : BabyBear) ^ 2 = 1048536409 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h17 : (1048536409 : BabyBear) ^ 2 = 434152628 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h18 : (434152628 : BabyBear) ^ 2 = 1734511292 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h19 : (1734511292 : BabyBear) ^ 2 = 839726776 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h20 : (839726776 : BabyBear) ^ 2 = 629262984 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h21 : (629262984 : BabyBear) ^ 2 = 1502726565 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h22 : (1502726565 : BabyBear) ^ 2 = 48459945 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h23 : (48459945 : BabyBear) ^ 2 = 288916259 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h24 : (288916259 : BabyBear) ^ 2 = 503591070 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h25 : (503591070 : BabyBear) ^ 2 = 782862608 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  have h26 : (782862608 : BabyBear) ^ 2 = 1314723124 := by
    apply babyBear_pow_eq_of_mod
    norm_num [babyBearP]
  calc
    (31 : BabyBear) ^ 335544320 = (28629151 : BabyBear) ^ (2 ^ 26) := by
      rw [show 335544320 = 5 * 2 ^ 26 by norm_num, pow_mul, h0]
    _ = (1558084728 : BabyBear) ^ (2 ^ 25) := pow_two_succ_congr h1 25
    _ = (1422208504 : BabyBear) ^ (2 ^ 24) := pow_two_succ_congr h2 24
    _ = (1678705229 : BabyBear) ^ (2 ^ 23) := pow_two_succ_congr h3 23
    _ = (1771892767 : BabyBear) ^ (2 ^ 22) := pow_two_succ_congr h4 22
    _ = (940487245 : BabyBear) ^ (2 ^ 21) := pow_two_succ_congr h5 21
    _ = (1516982208 : BabyBear) ^ (2 ^ 20) := pow_two_succ_congr h6 20
    _ = (792115306 : BabyBear) ^ (2 ^ 19) := pow_two_succ_congr h7 19
    _ = (452791590 : BabyBear) ^ (2 ^ 18) := pow_two_succ_congr h8 18
    _ = (1605829134 : BabyBear) ^ (2 ^ 17) := pow_two_succ_congr h9 17
    _ = (2008025366 : BabyBear) ^ (2 ^ 16) := pow_two_succ_congr h10 16
    _ = (456279664 : BabyBear) ^ (2 ^ 15) := pow_two_succ_congr h11 15
    _ = (1492617483 : BabyBear) ^ (2 ^ 14) := pow_two_succ_congr h12 14
    _ = (1252078097 : BabyBear) ^ (2 ^ 13) := pow_two_succ_congr h13 13
    _ = (12770214 : BabyBear) ^ (2 ^ 12) := pow_two_succ_congr h14 12
    _ = (1812738875 : BabyBear) ^ (2 ^ 11) := pow_two_succ_congr h15 11
    _ = (1048536409 : BabyBear) ^ (2 ^ 10) := pow_two_succ_congr h16 10
    _ = (434152628 : BabyBear) ^ (2 ^ 9) := pow_two_succ_congr h17 9
    _ = (1734511292 : BabyBear) ^ (2 ^ 8) := pow_two_succ_congr h18 8
    _ = (839726776 : BabyBear) ^ (2 ^ 7) := pow_two_succ_congr h19 7
    _ = (629262984 : BabyBear) ^ (2 ^ 6) := pow_two_succ_congr h20 6
    _ = (1502726565 : BabyBear) ^ (2 ^ 5) := pow_two_succ_congr h21 5
    _ = (48459945 : BabyBear) ^ (2 ^ 4) := pow_two_succ_congr h22 4
    _ = (288916259 : BabyBear) ^ (2 ^ 3) := pow_two_succ_congr h23 3
    _ = (503591070 : BabyBear) ^ (2 ^ 2) := pow_two_succ_congr h24 2
    _ = (782862608 : BabyBear) ^ (2 ^ 1) := pow_two_succ_congr h25 1
    _ = (1314723124 : BabyBear) ^ (2 ^ 0) := pow_two_succ_congr h26 0
    _ = 1314723124 := by norm_num

/-- `31^((p-1)/3)` is nontrivial, so 31 is not a cube. -/
theorem thirty_one_pow_third :
    (31 : BabyBear) ^ 671088640 = 1314723123 := by
  calc
    (31 : BabyBear) ^ 671088640 = ((31 : BabyBear) ^ 335544320) ^ 2 := by
      rw [show 671088640 = 335544320 * 2 by norm_num, pow_mul]
    _ = (1314723124 : BabyBear) ^ 2 := by rw [thirty_one_pow_sixth]
    _ = 1314723123 := by
      apply babyBear_pow_eq_of_mod
      norm_num [babyBearP]

/-- Euler's criterion witness: 31 is a quadratic nonresidue. -/
theorem thirty_one_pow_half :
    (31 : BabyBear) ^ 1006632960 = 2013265920 := by
  calc
    (31 : BabyBear) ^ 1006632960 = ((31 : BabyBear) ^ 335544320) ^ 3 := by
      rw [show 1006632960 = 335544320 * 3 by norm_num, pow_mul]
    _ = (1314723124 : BabyBear) ^ 3 := by rw [thirty_one_pow_sixth]
    _ = 2013265920 := by
      apply babyBear_pow_eq_of_mod
      norm_num [babyBearP]

theorem thirty_one_not_cube (b : BabyBear) : b ^ 3 ≠ 31 := by
  intro h
  have hb : b ≠ 0 := by
    intro hb
    subst b
    have hne : (0 : BabyBear) ≠ 31 := by decide
    exact hne (by simpa using h)
  have hfermat := ZMod.pow_card_sub_one_eq_one hb
  have hp := congrArg (fun z : BabyBear => z ^ 671088640) h
  change (b ^ 3) ^ 671088640 = (31 : BabyBear) ^ 671088640 at hp
  rw [← pow_mul] at hp
  norm_num [babyBearP] at hfermat hp
  rw [hfermat, thirty_one_pow_third] at hp
  have hne : (1 : BabyBear) ≠ 1314723123 := by decide
  exact hne hp

theorem thirty_one_not_square (b : BabyBear) : b ^ 2 ≠ 31 := by
  intro h
  have hb : b ≠ 0 := by
    intro hb
    subst b
    have hne : (0 : BabyBear) ≠ 31 := by decide
    exact hne (by simpa using h)
  have hfermat := ZMod.pow_card_sub_one_eq_one hb
  have hp := congrArg (fun z : BabyBear => z ^ 1006632960) h
  change (b ^ 2) ^ 1006632960 = (31 : BabyBear) ^ 1006632960 at hp
  rw [← pow_mul] at hp
  norm_num [babyBearP] at hfermat hp
  rw [hfermat, thirty_one_pow_half] at hp
  have hne : (1 : BabyBear) ≠ 2013265920 := by decide
  exact hne hp

/-! ## §2. Irreducibility and cardinality -/

noncomputable def ext6Polynomial : Polynomial BabyBear := X ^ 6 - C 31

theorem ext6Polynomial_monic : ext6Polynomial.Monic := by
  exact monic_X_pow_sub_C _ (by norm_num)

theorem ext3Polynomial_irreducible :
    Irreducible ((X : Polynomial BabyBear) ^ 3 - C 31) :=
  X_pow_sub_C_irreducible_of_prime (by norm_num) thirty_one_not_cube

/-- **Fieldness closed:** `X⁶ - 31` is irreducible over BabyBear. -/
theorem ext6Polynomial_irreducible : Irreducible ext6Polynomial := by
  unfold ext6Polynomial
  rw [show 6 = 2 * 3 by norm_num]
  apply X_pow_mul_sub_C_irreducible ext3Polynomial_irreducible
  intro E _ _ x hx
  apply X_pow_sub_C_irreducible_of_prime (by norm_num)
  intro b hb
  have hxint : IsIntegral BabyBear x := by
    rw [← minpoly.ne_zero_iff]
    rw [hx]
    exact X_pow_sub_C_ne_zero (by norm_num) _
  have hnorm := congrArg (Algebra.norm BabyBear) hb
  simp only [map_pow] at hnorm
  rw [← IntermediateField.adjoin.powerBasis_gen hxint,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly] at hnorm
  simp [minpoly_gen, hx] at hnorm
  exact thirty_one_not_square (Algebra.norm BabyBear b) hnorm

noncomputable instance : Fact (Irreducible ext6Polynomial) :=
  ⟨ext6Polynomial_irreducible⟩

/-- The concrete challenge field. -/
noncomputable abbrev Ext6Q : Type := AdjoinRoot ext6Polynomial

noncomputable instance : Module.Finite BabyBear Ext6Q :=
  ext6Polynomial_monic.finite_adjoinRoot

theorem ext6Q_finrank : Module.finrank BabyBear Ext6Q = 6 := by
  have hne : ext6Polynomial ≠ 0 := ext6Polynomial_irreducible.ne_zero
  rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim]
  norm_num [ext6Polynomial]

/-! ## §3. Lane multiplication and known answers -/

/-- Six-lane multiplication reduced by `u⁶ = 31`. -/
def ext6Mul (a b : Fin 6 → BabyBear) : Fin 6 → BabyBear
  | 0 => a 0 * b 0 + 31 * (a 1 * b 5 + a 2 * b 4 + a 3 * b 3 + a 4 * b 2 + a 5 * b 1)
  | 1 => a 0 * b 1 + a 1 * b 0 + 31 * (a 2 * b 5 + a 3 * b 4 + a 4 * b 3 + a 5 * b 2)
  | 2 => a 0 * b 2 + a 1 * b 1 + a 2 * b 0 + 31 * (a 3 * b 5 + a 4 * b 4 + a 5 * b 3)
  | 3 => a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0 + 31 * (a 4 * b 5 + a 5 * b 4)
  | 4 => a 0 * b 4 + a 1 * b 3 + a 2 * b 2 + a 3 * b 1 + a 4 * b 0 + 31 * (a 5 * b 5)
  | 5 => a 0 * b 5 + a 1 * b 4 + a 2 * b 3 + a 3 * b 2 + a 4 * b 1 + a 5 * b 0

noncomputable def ext6Root : Ext6Q := AdjoinRoot.root ext6Polynomial

noncomputable def toExt6 (v : Fin 6 → BabyBear) : Ext6Q :=
  AdjoinRoot.of ext6Polynomial (v 0) +
    AdjoinRoot.of ext6Polynomial (v 1) * ext6Root +
    AdjoinRoot.of ext6Polynomial (v 2) * ext6Root ^ 2 +
    AdjoinRoot.of ext6Polynomial (v 3) * ext6Root ^ 3 +
    AdjoinRoot.of ext6Polynomial (v 4) * ext6Root ^ 4 +
    AdjoinRoot.of ext6Polynomial (v 5) * ext6Root ^ 5

theorem ext6Root_pow_six :
    ext6Root ^ 6 = AdjoinRoot.of ext6Polynomial (31 : BabyBear) := by
  have h := AdjoinRoot.mk_self (f := ext6Polynomial)
  rw [ext6Polynomial, map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    sub_eq_zero] at h
  exact h

private theorem ext6_mul_ring {R : Type*} [CommRing R]
    (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 r w : R) (h : r ^ 6 = w) :
    a0 * b0 + w * (a1 * b5 + a2 * b4 + a3 * b3 + a4 * b2 + a5 * b1) +
      (a0 * b1 + a1 * b0 + w * (a2 * b5 + a3 * b4 + a4 * b3 + a5 * b2)) * r +
      (a0 * b2 + a1 * b1 + a2 * b0 + w * (a3 * b5 + a4 * b4 + a5 * b3)) * r ^ 2 +
      (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 + w * (a4 * b5 + a5 * b4)) * r ^ 3 +
      (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0 + w * (a5 * b5)) * r ^ 4 +
      (a0 * b5 + a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1 + a5 * b0) * r ^ 5 =
    (a0 + a1 * r + a2 * r ^ 2 + a3 * r ^ 3 + a4 * r ^ 4 + a5 * r ^ 5) *
      (b0 + b1 * r + b2 * r ^ 2 + b3 * r ^ 3 + b4 * r ^ 4 + b5 * r ^ 5) := by
  linear_combination
    (-(a1 * b5 + a2 * b4 + a3 * b3 + a4 * b2 + a5 * b1) -
      (a2 * b5 + a3 * b4 + a4 * b3 + a5 * b2) * r -
      (a3 * b5 + a4 * b4 + a5 * b3) * r ^ 2 -
      (a4 * b5 + a5 * b4) * r ^ 3 - a5 * b5 * r ^ 4) * h

/-- The Rust lane formula is multiplication in the proved field. -/
theorem ext6Mul_correct (a b : Fin 6 → BabyBear) :
    toExt6 (ext6Mul a b) = toExt6 a * toExt6 b := by
  simp only [toExt6, ext6Mul, map_add, map_mul]
  exact ext6_mul_ring
    (AdjoinRoot.of ext6Polynomial (a 0)) (AdjoinRoot.of ext6Polynomial (a 1))
    (AdjoinRoot.of ext6Polynomial (a 2)) (AdjoinRoot.of ext6Polynomial (a 3))
    (AdjoinRoot.of ext6Polynomial (a 4)) (AdjoinRoot.of ext6Polynomial (a 5))
    (AdjoinRoot.of ext6Polynomial (b 0)) (AdjoinRoot.of ext6Polynomial (b 1))
    (AdjoinRoot.of ext6Polynomial (b 2)) (AdjoinRoot.of ext6Polynomial (b 3))
    (AdjoinRoot.of ext6Polynomial (b 4)) (AdjoinRoot.of ext6Polynomial (b 5))
    ext6Root (AdjoinRoot.of ext6Polynomial (31 : BabyBear)) ext6Root_pow_six

def ext6A : Fin 6 → BabyBear :=
  ![123456789, 987654321, 555555555, 2013265920, 314159265, 271828182]
def ext6B : Fin 6 → BabyBear :=
  ![1999999999, 42, 1414213562, 777000777, 1618033988, 42424242]
def ext6Product : Fin 6 → BabyBear :=
  ![1935082458, 589685295, 173991560, 1528914995, 1641578725, 1780603210]

theorem ext6_known_product : ext6Mul ext6A ext6B = ext6Product := by decide

def ext6EdgeA : Fin 6 → BabyBear :=
  ![2013265920, 2013265919, 2013265918, 2013265917, 2013265916, 2013265915]
def ext6EdgeB : Fin 6 → BabyBear :=
  ![1, 2, 3, 2013265920, 2013265919, 2013265918]
def ext6EdgeProduct : Fin 6 → BabyBear :=
  ![2013265579, 120, 858, 822, 540, 2013265903]

theorem ext6_edge_product : ext6Mul ext6EdgeA ext6EdgeB = ext6EdgeProduct := by decide

#check @ext6Polynomial_irreducible
#check @ext6Q_finrank
#check @ext6Mul_correct
#check @ext6_known_product
#check @ext6_edge_product

/-- info: 'Minidregg.Compiler.ext6Polynomial_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ext6Polynomial_irreducible
/-- info: 'Minidregg.Compiler.ext6Q_finrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ext6Q_finrank
/-- info: 'Minidregg.Compiler.ext6Mul_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ext6Mul_correct

end Minidregg.Compiler
