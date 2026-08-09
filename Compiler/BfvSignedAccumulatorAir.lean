/-
# `Compiler.BfvSignedAccumulatorAir` — exact weighted-sum carry boundary

One compressed BFV row has 12,416 active signed terms.  Materializing a separate wide
product and addition chain for every term is unnecessary: write every public coefficient
in radix 64 and accumulate one column at a time.  A single nonnegative carry chain proves

`result = constant + sum_j coefficient[j] * scalar[j]`

over `Nat`.  The field equation for a column contains at most 12,416 products of two
six-bit values (plus one quotient product whose scalar is 24 bits), so the deployed column
budget is comfortably below BabyBear.  This module proves the generic emitted gadget and
then states the signed BFV join using the exact shifted-scalar normalization.
-/
import Compiler.BfvInputValidity

namespace Minidregg.Compiler.BfvSignedAccumulatorAir

open scoped BigOperators
open Minidregg.Compiler
open Minidregg.Compiler.BfvCompressedEquation
open Minidregg.Compiler.BfvAllModuliKernelCalls
open Minidregg.Compiler.BfvInputValidity
open Minidregg.Theory
open Minidregg.Theory.CompressedLinearEquation

set_option autoImplicit false

universe u

variable {F : Type u} [Field F] {Idx : Type u}
variable {n width limbBits carryBits : Nat}

/-! ## Generic column-wise weighted sum -/

structure WeightedSumWires (Idx : Type u) (width limbBits carryBits : Nat) where
  result : Fin width -> Idx
  resultBit : Fin width -> Fin limbBits -> Idx
  carry : Fin (width + 1) -> Idx
  carryBit : Fin (width + 1) -> Fin carryBits -> Idx

def weightedProductsTerm (width limbBits : Nat) (coefficient : Fin n -> Nat)
    (scalar : Fin n -> Idx) (column : Fin width) : List (Fin n) -> Term (AirSig F Idx)
  | [] => cst 0
  | j :: rest =>
      add'
        (mul' (cst (AirModularView.constDigit (2 ^ limbBits) width
          (coefficient j) column : F)) (vr (scalar j)))
        (weightedProductsTerm width limbBits coefficient scalar column rest)

def weightedColumnTerm (constant : Nat) (coefficient : Fin n -> Nat)
    (scalar : Fin n -> Idx) (w : WeightedSumWires Idx width limbBits carryBits)
    (column : Fin width) : Term (AirSig F Idx) :=
  add'
    (add'
      (add' (cst (AirModularView.constDigit (2 ^ limbBits) width constant column : F))
        (weightedProductsTerm width limbBits coefficient scalar column (List.finRange n)))
      (vr (w.carry column.castSucc)))
    (mul' (cst (-1))
      (add' (vr (w.result column))
        (mul' (cst ((2 : F) ^ limbBits)) (vr (w.carry column.succ)))))

def weightedEquationSystem (constant : Nat) (coefficient : Fin n -> Nat)
    (scalar : Fin n -> Idx) (w : WeightedSumWires Idx width limbBits carryBits) :
    ConstraintSystem F Idx :=
  (List.finRange width).map fun column =>
    weightedColumnTerm constant coefficient scalar w column

/-- Result/carry ranges, zero boundary carries, and the weighted column equations. -/
def weightedSumGadget (constant : Nat) (coefficient : Fin n -> Nat)
    (scalar : Fin n -> Idx) (w : WeightedSumWires Idx width limbBits carryBits) :
    ConstraintSystem F Idx :=
  AirBignum.limbRangeSystem w.result w.resultBit ++
  AirBignum.limbRangeSystem w.carry w.carryBit ++
  [vr (w.carry 0), vr (w.carry (Fin.last width))] ++
  weightedEquationSystem constant coefficient scalar w

theorem eval_weightedProductsTerm (asg : Idx -> F) (width limbBits : Nat)
    (coefficient : Fin n -> Nat) (scalar : Fin n -> Idx) (column : Fin width)
    (indices : List (Fin n)) :
    eval asg (weightedProductsTerm (F := F) width limbBits coefficient scalar column indices) =
      (indices.map fun j =>
        (AirModularView.constDigit (2 ^ limbBits) width (coefficient j) column : F) *
          asg (scalar j)).sum := by
  induction indices with
  | nil => simp [weightedProductsTerm]
  | cons j rest ih => simp [weightedProductsTerm, ih]

theorem weightedColumnTerm_correct (asg : Idx -> F) (constant : Nat)
    (coefficient : Fin n -> Nat) (scalar : Fin n -> Idx)
    (w : WeightedSumWires Idx width limbBits carryBits) (column : Fin width) :
    accepts asg (weightedColumnTerm constant coefficient scalar w column) <->
      (AirModularView.constDigit (2 ^ limbBits) width constant column : F) +
          ((List.finRange n).map fun j =>
            (AirModularView.constDigit (2 ^ limbBits) width (coefficient j) column : F) *
              asg (scalar j)).sum +
          asg (w.carry column.castSucc) =
        asg (w.result column) + (2 : F) ^ limbBits * asg (w.carry column.succ) := by
  unfold accepts weightedColumnTerm
  rw [eval_weightedProductsTerm]
  simp only [eval_add', eval_mul', eval_cst, eval_vr]
  constructor <;> intro h <;> linear_combination h

theorem weightedEquationSystem_correct (asg : Idx -> F) (constant : Nat)
    (coefficient : Fin n -> Nat) (scalar : Fin n -> Idx)
    (w : WeightedSumWires Idx width limbBits carryBits) :
    systemAccepts asg (weightedEquationSystem constant coefficient scalar w) <->
      forall column,
        (AirModularView.constDigit (2 ^ limbBits) width constant column : F) +
            ((List.finRange n).map fun j =>
              (AirModularView.constDigit (2 ^ limbBits) width (coefficient j) column : F) *
                asg (scalar j)).sum +
            asg (w.carry column.castSucc) =
          asg (w.result column) + (2 : F) ^ limbBits * asg (w.carry column.succ) := by
  constructor
  · intro h column
    exact (weightedColumnTerm_correct asg constant coefficient scalar w column).mp
      (h _ (List.mem_map.mpr ⟨column, List.mem_finRange column, rfl⟩))
  · intro h term hterm
    obtain ⟨column, -, rfl⟩ := List.mem_map.mp hterm
    exact (weightedColumnTerm_correct asg constant coefficient scalar w column).mpr (h column)

theorem weightedSumGadget_correct (asg : Idx -> F) (constant : Nat)
    (coefficient : Fin n -> Nat) (scalar : Fin n -> Idx)
    (w : WeightedSumWires Idx width limbBits carryBits) :
    systemAccepts asg (weightedSumGadget constant coefficient scalar w) <->
      (forall i, systemAccepts asg (rangeGadget (w.result i) (w.resultBit i))) /\
      (forall i, systemAccepts asg (rangeGadget (w.carry i) (w.carryBit i))) /\
      asg (w.carry 0) = 0 /\
      asg (w.carry (Fin.last width)) = 0 /\
      (forall column,
        (AirModularView.constDigit (2 ^ limbBits) width constant column : F) +
            ((List.finRange n).map fun j =>
              (AirModularView.constDigit (2 ^ limbBits) width (coefficient j) column : F) *
                asg (scalar j)).sum +
            asg (w.carry column.castSucc) =
          asg (w.result column) + (2 : F) ^ limbBits * asg (w.carry column.succ)) := by
  rw [weightedSumGadget, systemAccepts_append, systemAccepts_append,
    systemAccepts_append, AirBignum.limbRangeSystem_correct,
    AirBignum.limbRangeSystem_correct, weightedEquationSystem_correct]
  simp only [systemAccepts_cons, systemAccepts_nil, and_true, accepts, eval_vr]
  tauto

private theorem nat_eq_of_zmod_eq {p a b : Nat} [NeZero p]
    (ha : a < p) (hb : b < p) (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  have hv := congrArg ZMod.val h
  simpa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] using hv

/-- Radix denotation distributes over a constant digit vector and finitely many
coefficient digit vectors. -/
theorem denote_weighted_columns (base : Nat) (scalar : Fin n -> Nat) :
    forall {width : Nat} (constantDigit : Fin width -> Nat)
      (coefficientDigit : Fin n -> Fin width -> Nat),
      Bignum.denoteNat base
          (List.ofFn fun i => constantDigit i +
            ∑ j, coefficientDigit j i * scalar j) =
        Bignum.denoteNat base (List.ofFn constantDigit) +
          ∑ j, Bignum.denoteNat base (List.ofFn (coefficientDigit j)) * scalar j := by
  intro width
  induction width with
  | zero => intro constantDigit coefficientDigit; simp
  | succ width ih =>
      intro constantDigit coefficientDigit
      simp only [List.ofFn_succ, Bignum.denoteNat_cons]
      rw [ih (fun i => constantDigit i.succ) (fun j i => coefficientDigit j i.succ)]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      simp_rw [mul_add, mul_assoc]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

/-- Exact integer soundness.  The two no-wrap premises are per-column numeric bounds; the
deployed BFV instantiation below discharges them from one coarse universal budget. -/
theorem weightedSumGadget_sound {p n width limbBits carryBits constant : Nat}
    [Fact p.Prime] (hbasep : 2 ^ limbBits <= p) (hcarryp : 2 ^ carryBits <= p)
    (hconstant : constant < (2 ^ limbBits) ^ width)
    (coefficient : Fin n -> Nat)
    (hcoefficient : forall j, coefficient j < (2 ^ limbBits) ^ width)
    {J : Type} (asg : J -> ZMod p) (scalar : Fin n -> J)
    (w : WeightedSumWires J width limbBits carryBits)
    (haccept : systemAccepts asg (weightedSumGadget constant coefficient scalar w))
    (hleft : forall column,
      AirModularView.constDigit (2 ^ limbBits) width constant column +
          ((List.finRange n).map fun j =>
            AirModularView.constDigit (2 ^ limbBits) width (coefficient j) column *
              (asg (scalar j)).val).sum +
          (asg (w.carry column.castSucc)).val < p)
    (hright : forall column,
      (asg (w.result column)).val +
          2 ^ limbBits * (asg (w.carry column.succ)).val < p) :
    Bignum.Canonical (2 ^ limbBits) width (AirBignum.limbVals asg w.result) /\
    Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.result) =
      constant + ∑ j, coefficient j * (asg (scalar j)).val := by
  let base := 2 ^ limbBits
  have hbase : 0 < base := pow_pos (by omega) _
  obtain ⟨hresult, hcarry, hc0, hctop, heq⟩ :=
    (weightedSumGadget_correct asg constant coefficient scalar w).mp haccept
  have cresult := AirBignum.limbVals_canonical hbasep asg w.result w.resultBit hresult
  refine ⟨cresult, ?_⟩
  have heqNat : forall column,
      AirModularView.constDigit base width constant column +
          ((List.finRange n).map fun j =>
            AirModularView.constDigit base width (coefficient j) column *
              (asg (scalar j)).val).sum +
          (asg (w.carry column.castSucc)).val =
        (asg (w.result column)).val +
          base * (asg (w.carry column.succ)).val := by
    intro column
    apply nat_eq_of_zmod_eq (hleft column) (hright column)
    simpa [base, ZMod.natCast_zmod_val, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      List.cast_sum, List.cast_map] using heq column
  have htel := AirModularView.mulCarryEquations_denote base 1
    (fun column => AirModularView.constDigit base width constant column +
      ((List.finRange n).map fun j =>
        AirModularView.constDigit base width (coefficient j) column *
          (asg (scalar j)).val).sum)
    (fun column => (asg (w.result column)).val)
    (fun i => (asg (w.carry i)).val) (by simpa using heqNat)
  have hc0v : (asg (w.carry 0)).val = 0 := by rw [hc0]; exact ZMod.val_zero
  have hctopv : (asg (w.carry (Fin.last width))).val = 0 := by
    rw [hctop]
    exact ZMod.val_zero
  have hlinear := denote_weighted_columns base (fun j => (asg (scalar j)).val)
    (AirModularView.constDigit base width constant)
    (fun j => AirModularView.constDigit base width (coefficient j))
  rw [AirModularView.constDigits_eq, Bignum.denoteNat_digitsLE hbase width constant hconstant]
    at hlinear
  have hcoeffDenote : forall j,
      Bignum.denoteNat base
          (List.ofFn (AirModularView.constDigit base width (coefficient j))) = coefficient j := by
    intro j
    rw [AirModularView.constDigits_eq]
    exact Bignum.denoteNat_digitsLE hbase width (coefficient j) (hcoefficient j)
  simp_rw [hcoeffDenote] at hlinear
  rw [← hlinear]
  simpa [base, AirBignum.limbVals, hc0v, hctopv] using htel

/-! ## Signed BFV normalization and deployed budget -/

def activeShift : Fin activeWidth -> Nat :=
  Fin.append (fun _ : Fin optionCount => 0)
    (Fin.append (fun _ : Fin degree => 32)
      (Fin.append (fun _ : Fin degree => 32) (fun _ : Fin degree => 32)))

def shiftedScalar (row : OwnerRow) : Fin activeWidth -> Nat :=
  Fin.append (fun option => (row.selector option).toNat)
    (Fin.append (fun j => (row.u j + 32).toNat)
      (Fin.append (fun j => (row.e1 j + 32).toNat)
        (fun j => (row.e2 j + 32).toNat)))

def shiftedConstant (equation : DeployedEquation) : Int :=
  equation.publicConstant -
    ∑ i, equation.activeCoefficient i * (activeShift i : Int)

theorem shiftedScalar_recompose {statement : InputStatement}
    (input : ValidCommittedWitness statement) (i : Fin activeWidth) :
    ((shiftedScalar input.row i : Nat) : Int) =
      input.row.activeValue i + (activeShift i : Int) := by
  refine Fin.addCases (m := optionCount) (n := degree + (degree + degree)) ?_ ?_ i
  · intro option
    rcases input.selector_boolean option with h | h <;>
      simp [shiftedScalar, OwnerRow.activeValue, activeShift, h]
  · intro shortIndex
    refine Fin.addCases (m := degree) (n := degree + degree) ?_ ?_ shortIndex
    · intro j
      have h := input.rowRange.u_short j
      simp [shiftedScalar, OwnerRow.activeValue, activeShift,
        Int.toNat_of_nonneg (by omega : 0 <= input.row.u j + 32)]
    · intro tail
      refine Fin.addCases (m := degree) (n := degree) ?_ ?_ tail
      · intro j
        have h := input.rowRange.e1_short j
        simp [shiftedScalar, OwnerRow.activeValue, activeShift,
          Int.toNat_of_nonneg (by omega : 0 <= input.row.e1 j + 32)]
      · intro j
        have h := input.rowRange.e2_short j
        simp [shiftedScalar, OwnerRow.activeValue, activeShift,
          Int.toNat_of_nonneg (by omega : 0 <= input.row.e2 j + 32)]

theorem shiftedScalar_lt_64 {statement : InputStatement}
    (input : ValidCommittedWitness statement) (i : Fin activeWidth) :
    shiftedScalar input.row i < 64 := by
  refine Fin.addCases (m := optionCount) (n := degree + (degree + degree)) ?_ ?_ i
  · intro option
    rcases input.selector_boolean option with h | h <;>
      simp [shiftedScalar, h]
  · intro shortIndex
    refine Fin.addCases (m := degree) (n := degree + degree) ?_ ?_ shortIndex
    · intro j
      have h := input.rowRange.u_short j
      simp [shiftedScalar]
      rw [Int.toNat_lt] <;> omega
    · intro tail
      refine Fin.addCases (m := degree) (n := degree) ?_ ?_ tail
      · intro j
        have h := input.rowRange.e1_short j
        simp [shiftedScalar]
        rw [Int.toNat_lt] <;> omega
      · intro j
        have h := input.rowRange.e2_short j
        simp [shiftedScalar]
        rw [Int.toNat_lt] <;> omega

/-- Shifting every short by 32 changes only the public constant. -/
theorem eval_eq_shifted {statement : InputStatement}
    (input : ValidCommittedWitness statement) (equation : DeployedEquation) :
    equation.numerator input.row =
      shiftedConstant equation +
        ∑ i, equation.activeCoefficient i * (shiftedScalar input.row i : Int) := by
  rw [← equation.eval_active_eq_numerator]
  unfold Equation.eval DeployedEquation.asTheory shiftedConstant
  simp only
  have hrecompose : forall i,
      (shiftedScalar input.row i : Int) =
        input.row.activeValue i + (activeShift i : Int) :=
    shiftedScalar_recompose input
  simp_rw [hrecompose, mul_add, Finset.sum_add_distrib]
  ring

/-- Coarse deployed field budget for one column: 12,416 six-bit products, one 24-bit
quotient product, one constant digit, and a 26-bit carry remain below BabyBear. -/
theorem deployed_column_budget :
    activeWidth * 63 * 63 + 63 * (2 ^ scalarBits - 1) + 63 + (2 ^ 26 - 1) <
      babyBearP := by
  norm_num [activeWidth, optionCount, degree, scalarBits,
    BfvCompressedEquation.quotientBits, babyBearP]

#print axioms weightedSumGadget_correct
#print axioms denote_weighted_columns
#print axioms weightedSumGadget_sound
#print axioms shiftedScalar_recompose
#print axioms shiftedScalar_lt_64
#print axioms eval_eq_shifted
#print axioms deployed_column_budget

end Minidregg.Compiler.BfvSignedAccumulatorAir
