/-
# `Theory.CompressedLinearEquation` — exact signed equations over canonical integers

FHEgg's compressed BFV checks are integer equations, not equations in BabyBear or Ext6.
This file gives their candidate-independent statement.  Signed terms are normalized into
two natural-number masses, and a centered fixed-width limb word represents the signed
quotient without field wraparound.  The resulting balance equations are the form an
unsigned limb/carry AIR can consume honestly.
-/
import Theory.Bignum

namespace Minidregg.Theory.CompressedLinearEquation

open Minidregg.Theory

set_option autoImplicit false

/-- Nonnegative and negative magnitudes of an integer. -/
def posPart (z : Int) : Nat := z.toNat
def negPart (z : Int) : Nat := (-z).toNat

theorem eq_posPart_sub_negPart (z : Int) :
    z = (posPart z : Int) - (negPart z : Int) := by
  cases z with
  | ofNat n => simp [posPart, negPart]
  | negSucc n =>
      simp [posPart, negPart]
      omega

/-- One exact public signed linear equation. -/
structure Equation (n : Nat) where
  modulus : Nat
  modulus_pos : 0 < modulus
  publicConstant : Int
  coefficient : Fin n → Int

def Equation.eval {n : Nat} (e : Equation n) (value : Fin n → Int) : Int :=
  e.publicConstant + ∑ i, e.coefficient i * value i

/-- Sum of the positive contributions to an equation. -/
def Equation.positiveMass {n : Nat} (e : Equation n) (value : Fin n → Int) : Nat :=
  posPart e.publicConstant + ∑ i, posPart (e.coefficient i * value i)

/-- Sum of the absolute values of its negative contributions. -/
def Equation.negativeMass {n : Nat} (e : Equation n) (value : Fin n → Int) : Nat :=
  negPart e.publicConstant + ∑ i, negPart (e.coefficient i * value i)

/-- Splitting every signed term loses no information. -/
theorem Equation.eval_eq_mass_sub {n : Nat} (e : Equation n) (value : Fin n → Int) :
    e.eval value = (e.positiveMass value : Int) - (e.negativeMass value : Int) := by
  unfold Equation.eval Equation.positiveMass Equation.negativeMass
  nth_rewrite 1 [eq_posPart_sub_negPart e.publicConstant]
  calc
    ((posPart e.publicConstant : Int) - (negPart e.publicConstant : Int)) +
        ∑ i, e.coefficient i * value i =
      ((posPart e.publicConstant : Int) - (negPart e.publicConstant : Int)) +
        ∑ i, ((posPart (e.coefficient i * value i) : Int) -
          (negPart (e.coefficient i * value i) : Int)) := by
            apply congrArg (fun z : Int =>
              ((posPart e.publicConstant : Int) - (negPart e.publicConstant : Int)) + z)
            apply Finset.sum_congr rfl
            intro i _
            exact eq_posPart_sub_negPart _
    _ = ((posPart e.publicConstant + ∑ i, posPart (e.coefficient i * value i) : Nat) : Int) -
        ((negPart e.publicConstant + ∑ i, negPart (e.coefficient i * value i) : Nat) : Int) := by
          rw [Finset.sum_sub_distrib]
          push_cast
          ring

/-- A signed integer represented by canonical offset-binary limbs.  For the deployed
quotient this is four radix-64 limbs, capacity `2^24`, centered at `2^23`. -/
structure CenteredLimbs (base width shift bound : Nat) where
  encoded : Bignum.Limbs base width
  shift_lt : shift < base ^ width
  abs_le : Int.natAbs ((encoded.toNat : Int) - (shift : Int)) ≤ bound

namespace CenteredLimbs

def value {base width shift bound : Nat} (x : CenteredLimbs base width shift bound) : Int :=
  (x.encoded.toNat : Int) - (shift : Int)

theorem encoded_lt_capacity {base width shift bound : Nat} (hbase : 0 < base)
    (x : CenteredLimbs base width shift bound) : x.encoded.toNat < base ^ width :=
  x.encoded.toNat_lt_pow hbase

theorem value_abs_le {base width shift bound : Nat}
    (x : CenteredLimbs base width shift bound) : x.value.natAbs ≤ bound := x.abs_le

/-- Offset-binary is injective because the underlying canonical limb codec is injective. -/
theorem eq_of_value_eq {base width shift bound : Nat} (hbase : 0 < base)
    {x y : CenteredLimbs base width shift bound} (h : x.value = y.value) : x = y := by
  have hnat : x.encoded.toNat = y.encoded.toNat := by
    unfold value at h
    omega
  cases x with
  | mk xe xs xa =>
      cases y with
      | mk ye ys ya =>
          have he : xe = ye := Bignum.Limbs.toNat_injective hbase hnat
          subst ye
          rfl

end CenteredLimbs

/-- A witness for one exact compressed equation. -/
structure Witness {n base width shift bound : Nat} (e : Equation n) where
  value : Fin n → Int
  quotient : CenteredLimbs base width shift bound
  exact : e.eval value = (e.modulus : Int) * quotient.value

namespace Witness

/-- The exact runtime-friendly balance for an offset-binary quotient.  Instead of proving
the sign of `k`, range-check `shifted = k + shift` and check

`positiveMass + modulus*shift = negativeMass + modulus*shifted`.

This is the key signed-to-unsigned bridge: every quantity in the displayed equation is a
natural number suitable for canonical limb/carry constraints. -/
theorem shifted_balance {n base width shift bound : Nat} {e : Equation n}
    (w : Witness (base := base) (width := width) (shift := shift) (bound := bound) e) :
    e.positiveMass w.value + e.modulus * shift =
      e.negativeMass w.value + e.modulus * w.quotient.encoded.toNat := by
  have hmass := e.eval_eq_mass_sub w.value
  have hexact := w.exact
  unfold CenteredLimbs.value at hexact
  have hint :
      (e.positiveMass w.value + e.modulus * shift : Nat) =
        (e.negativeMass w.value + e.modulus * w.quotient.encoded.toNat : Nat) := by
    apply Int.ofNat_inj.mp
    push_cast
    nlinarith [hexact, hmass]
  exact hint

/-- A nonnegative quotient turns the signed equation into an exact natural balance. -/
theorem positive_balance {n base width shift bound : Nat} {e : Equation n}
    (w : Witness (base := base) (width := width) (shift := shift) (bound := bound) e)
    (hq : 0 ≤ w.quotient.value) :
    e.positiveMass w.value =
      e.negativeMass w.value + e.modulus * w.quotient.value.toNat := by
  have hmass := e.eval_eq_mass_sub w.value
  have hqcast : (w.quotient.value.toNat : Int) = w.quotient.value := by
    exact Int.toNat_of_nonneg hq
  have hint : (e.positiveMass w.value : Int) =
      (e.negativeMass w.value + e.modulus * w.quotient.value.toNat : Nat) := by
    push_cast
    rw [hqcast]
    nlinarith [w.exact, hmass]
  exact_mod_cast hint

/-- A nonpositive quotient moves its modulus product to the opposite natural mass. -/
theorem negative_balance {n base width shift bound : Nat} {e : Equation n}
    (w : Witness (base := base) (width := width) (shift := shift) (bound := bound) e)
    (hq : w.quotient.value ≤ 0) :
    e.negativeMass w.value =
      e.positiveMass w.value + e.modulus * (-w.quotient.value).toNat := by
  have hmass := e.eval_eq_mass_sub w.value
  have hqcast : ((-w.quotient.value).toNat : Int) = -w.quotient.value := by
    exact Int.toNat_of_nonneg (by omega)
  have hint : (e.negativeMass w.value : Int) =
      (e.positiveMass w.value + e.modulus * (-w.quotient.value).toNat : Nat) := by
    push_cast
    rw [hqcast]
    nlinarith [w.exact, hmass]
  exact_mod_cast hint

end Witness

end Minidregg.Theory.CompressedLinearEquation
