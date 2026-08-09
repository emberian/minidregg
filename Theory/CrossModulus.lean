/-
# `Theory.CrossModulus` — one canonical integer, two modular views

This is the candidate-independent integer layer needed before connecting RNS/FHE rings to
an auxiliary proof field.  A `CommonInteger` is a canonical fixed-width little-endian limb
word.  A `ModularView m x` carries the explicit Euclidean witnesses

`x = residue + quotient * m`,  `residue < m`.

`CrossModulus Q P` packages two such views of one word, for positive coprime moduli.  The
theorems below prove exact recomposition, quotient bounds, uniqueness of each view, and CRT
uniqueness in `[0,Q*P)`.  The final teeth show why congruence without that interval, and
limbs without canonicity, cannot identify an integer.
-/
import Theory.Bignum
import Mathlib.Data.Nat.ChineseRemainder

namespace Minidregg.Theory.CrossModulus

open Minidregg.Theory

set_option autoImplicit false

/-- A fixed-width canonical little-endian natural number. -/
structure CommonInteger (base width : Nat) where
  limbs : List Nat
  canonical : Bignum.Canonical base width limbs
deriving DecidableEq

namespace CommonInteger

def value {base width : Nat} (x : CommonInteger base width) : Nat :=
  Bignum.denoteNat base x.limbs

theorem value_lt_capacity {base width : Nat} (hbase : 0 < base)
    (x : CommonInteger base width) : x.value < base ^ width := by
  have h := Bignum.denoteNat_lt_pow hbase x.limbs x.canonical.1
  simpa [value, x.canonical.2] using h

/-- Canonical limb words are determined by their unreduced integer value. -/
theorem eq_of_value_eq {base width : Nat} (hbase : 0 < base)
    {x y : CommonInteger base width} (hvalue : x.value = y.value) : x = y := by
  cases x with
  | mk xl xc =>
      cases y with
      | mk yl yc =>
          have hl : xl = yl := Bignum.canonical_eq_of_denoteNat_eq hbase xc yc hvalue
          subst yl
          rfl

/-- The value-to-limbs direction, available exactly on the canonical capacity interval. -/
def ofValue {base width : Nat} (hbase : 0 < base) (value : Nat)
    (_hvalue : value < base ^ width) : CommonInteger base width :=
  ⟨Bignum.digitsLE base width value, Bignum.digitsLE_canonical hbase width value⟩

@[simp] theorem value_ofValue {base width value : Nat} (hbase : 0 < base)
    (hvalue : value < base ^ width) : (ofValue hbase value hvalue).value = value := by
  exact Bignum.denoteNat_digitsLE hbase width value hvalue

end CommonInteger

/-- Explicit quotient/remainder witnesses for viewing the same natural number modulo `m`. -/
structure ModularView (m x : Nat) where
  residue : Nat
  quotient : Nat
  residue_lt : residue < m
  recompose : x = residue + quotient * m
deriving DecidableEq

namespace ModularView

/-- The canonical modular view obtained by Euclidean division. -/
def canonical (m x : Nat) (hm : 0 < m) : ModularView m x where
  residue := x % m
  quotient := x / m
  residue_lt := Nat.mod_lt x hm
  recompose := by
    simpa [Nat.mul_comm] using (Nat.mod_add_div x m).symm

@[simp] theorem residue_eq_mod {m x : Nat} (v : ModularView m x) :
    v.residue = x % m := by
  calc
    v.residue = v.residue % m := (Nat.mod_eq_of_lt v.residue_lt).symm
    _ = (v.residue + v.quotient * m) % m := by
      symm
      rw [Nat.add_mul_mod_self_right]
    _ = x % m := by rw [← v.recompose]

@[simp] theorem quotient_eq_div {m x : Nat} (hm : 0 < m) (v : ModularView m x) :
    v.quotient = x / m := by
  calc
    v.quotient = (v.residue + v.quotient * m) / m := by
      rw [Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt v.residue_lt, Nat.zero_add]
    _ = x / m := congrArg (fun n => n / m) v.recompose.symm

/-- The witness really is a congruence, but the exact equation is stronger. -/
theorem modEq_residue {m x : Nat} (v : ModularView m x) :
    Nat.ModEq m x v.residue := by
  change x % m = v.residue % m
  rw [← v.residue_eq_mod, Nat.mod_eq_of_lt v.residue_lt]

/-- A quotient of a bounded common integer is itself below the same capacity. -/
theorem quotient_lt {m x capacity : Nat} (hm : 0 < m) (hx : x < capacity)
    (v : ModularView m x) : v.quotient < capacity := by
  calc
    v.quotient ≤ v.quotient * m := Nat.le_mul_of_pos_right _ hm
    _ ≤ v.residue + v.quotient * m := Nat.le_add_left _ _
    _ = x := v.recompose.symm
    _ < capacity := hx

/-- Quotient and remainder witnesses are unique once the remainder is in `[0,m)`. -/
theorem unique {m x : Nat} (hm : 0 < m) (a b : ModularView m x) : a = b := by
  cases a with
  | mk ar aq arlt arec =>
      cases b with
      | mk br bq brlt brec =>
          have hr : ar = br := by
            simpa using (residue_eq_mod ⟨ar, aq, arlt, arec⟩).trans
              (residue_eq_mod ⟨br, bq, brlt, brec⟩).symm
          have hq : aq = bq := by
            simpa using (quotient_eq_div hm ⟨ar, aq, arlt, arec⟩).trans
              (quotient_eq_div hm ⟨br, bq, brlt, brec⟩).symm
          subst br
          subst bq
          rfl

end ModularView

/-- One canonical integer together with its two exact positive-coprime modular views. -/
structure Bridge (base width Q P : Nat) where
  q_pos : 0 < Q
  p_pos : 0 < P
  coprime : Q.Coprime P
  common : CommonInteger base width
  qView : ModularView Q common.value
  pView : ModularView P common.value
deriving DecidableEq

namespace Bridge

/-- Both residue systems recompose to literally the same unreduced integer. -/
theorem views_recompose_same {base width Q P : Nat} (x : Bridge base width Q P) :
    x.qView.residue + x.qView.quotient * Q =
      x.pView.residue + x.pView.quotient * P := by
  rw [← x.qView.recompose, ← x.pView.recompose]

theorem qQuotient_lt_capacity {base width Q P : Nat} (hbase : 0 < base)
    (x : Bridge base width Q P) : x.qView.quotient < base ^ width :=
  x.qView.quotient_lt x.q_pos (x.common.value_lt_capacity hbase)

theorem pQuotient_lt_capacity {base width Q P : Nat} (hbase : 0 < base)
    (x : Bridge base width Q P) : x.pView.quotient < base ^ width :=
  x.pView.quotient_lt x.p_pos (x.common.value_lt_capacity hbase)

/-- **CRT uniqueness in the canonical interval.** Equal Q- and P-residues determine one
integer below `Q*P`. -/
theorem value_unique_below_product {Q P x y : Nat} (hcoprime : Q.Coprime P)
    (hx : x < Q * P) (hy : y < Q * P)
    (xQ : ModularView Q x) (yQ : ModularView Q y)
    (xP : ModularView P x) (yP : ModularView P y)
    (hQ : xQ.residue = yQ.residue) (hP : xP.residue = yP.residue) : x = y := by
  have hmodQ : Nat.ModEq Q x y := by
    change x % Q = y % Q
    rw [← xQ.residue_eq_mod, ← yQ.residue_eq_mod, hQ]
  have hmodP : Nat.ModEq P x y := by
    change x % P = y % P
    rw [← xP.residue_eq_mod, ← yP.residue_eq_mod, hP]
  exact ((Nat.modEq_and_modEq_iff_modEq_mul hcoprime).mp ⟨hmodQ, hmodP⟩).eq_of_lt_of_lt hx hy

/-- The two residues determine a canonical limb word whenever its value lies in the CRT
interval. -/
theorem common_unique_below_product {base width Q P : Nat} (hbase : 0 < base)
    {x y : Bridge base width Q P}
    (hx : x.common.value < Q * P) (hy : y.common.value < Q * P)
    (hQ : x.qView.residue = y.qView.residue)
    (hP : x.pView.residue = y.pView.residue) : x.common = y.common := by
  apply CommonInteger.eq_of_value_eq hbase
  exact value_unique_below_product x.coprime hx hy x.qView y.qView x.pView y.pView hQ hP

end Bridge

/-! ## Why the hypotheses are load-bearing -/

/-- Congruence alone never identifies an unrestricted integer: `0` and `m` alias modulo
every positive modulus. -/
theorem congruence_without_range_not_unique {m : Nat} (hm : 0 < m) :
    Nat.ModEq m 0 m ∧ 0 ≠ m := by
  constructor
  · change 0 % m = m % m
    simp
  · omega

/-- Limb canonicity is equally load-bearing: `[0]` and the out-of-range digit `[base]`
have distinct lists but congruent denotations modulo `base`. -/
theorem noncanonical_limbs_alias {base : Nat} (hbase : 0 < base) :
    ([0] : List Nat) ≠ [base] ∧
      Nat.ModEq base (Bignum.denoteNat base [0]) (Bignum.denoteNat base [base]) ∧
      ¬ Bignum.Ranged base [base] := by
  constructor
  · simp
    omega
  constructor
  · change 0 % base = base % base
    simp
  · simp [Bignum.Ranged]

end Minidregg.Theory.CrossModulus
