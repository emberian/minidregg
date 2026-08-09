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
  simp only [eval_add', eval_mul', eval_cst, eval_vr]
  rw [eval_weightedProductsTerm]
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
      simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
      ring

private theorem cast_weightedList {p n : Nat} [NeZero p] {J : Type} (asg : J -> ZMod p)
    (digit : Fin n -> Nat) (scalar : Fin n -> J) (indices : List (Fin n)) :
    (((indices.map fun j => digit j * (asg (scalar j)).val).sum : Nat) : ZMod p) =
      (indices.map fun j => (digit j : ZMod p) * asg (scalar j)).sum := by
  induction indices with
  | nil => simp
  | cons j rest ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul, ih,
        ZMod.natCast_zmod_val]

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
    have hcast := cast_weightedList asg
      (fun j => AirModularView.constDigit base width (coefficient j) column)
      scalar (List.finRange n)
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_mul, hcast]
    simp only [ZMod.natCast_zmod_val]
    simpa [base] using heq column
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

/-- The generic weighted accumulator is consumed by the existing descriptor emitter. -/
theorem emit_weightedSumGadget_iff (ix : Idx -> Nat) (hinj : Function.Injective ix)
    (nPublic nVars : Nat) (hbound : forall i, ix i < nVars)
    (asg : Idx -> F) (constant : Nat) (coefficient : Fin n -> Nat)
    (scalar : Fin n -> Idx) (w : WeightedSumWires Idx width limbBits carryBits) :
    (exists wireValues : Nat -> F, (forall i, wireValues (ix i) = asg i) /\
      descriptorHolds
        (emit ix nPublic nVars (weightedSumGadget constant coefficient scalar w))
        wireValues) <->
      systemAccepts asg (weightedSumGadget constant coefficient scalar w) :=
  emit_accepts_iff ix hinj nPublic nVars hbound asg _

/-! ## Signed BFV normalization and deployed budget -/

def activeShift : Fin activeWidth -> Nat :=
  Fin.append (fun _ : Fin optionCount => 0)
    (Fin.append (fun _ : Fin degree => 32)
      (Fin.append (fun _ : Fin degree => 32) (fun _ : Fin degree => 32)))

def shiftedScalar (row : OwnerRow) : Fin activeWidth -> Nat :=
  fun i => (row.activeValue i + (activeShift i : Int)).toNat

def shiftedConstant (equation : DeployedEquation) : Int :=
  equation.publicConstant -
    ∑ i, equation.activeCoefficient i * (activeShift i : Int)

private theorem activeValue_add_shift_bounds {statement : InputStatement}
    (input : ValidCommittedWitness statement) (i : Fin activeWidth) :
    0 <= input.row.activeValue i + (activeShift i : Int) /\
      input.row.activeValue i + (activeShift i : Int) < 64 := by
  refine Fin.addCases (m := optionCount) (n := degree + (degree + degree)) ?_ ?_ i
  · intro option
    simp only [OwnerRow.activeValue, activeShift, Fin.append_left, Nat.cast_zero, add_zero]
    rcases input.selector_boolean option with h | h <;> omega
  · intro shortIndex
    refine Fin.addCases (m := degree) (n := degree + degree) ?_ ?_ shortIndex
    · intro j
      have h := input.rowRange.u_short j
      simp only [OwnerRow.activeValue, activeShift, Fin.append_left, Fin.append_right,
        Nat.cast_ofNat]
      omega
    · intro tail
      refine Fin.addCases (m := degree) (n := degree) ?_ ?_ tail
      · intro j
        have h := input.rowRange.e1_short j
        simp only [OwnerRow.activeValue, activeShift, Fin.append_left, Fin.append_right,
          Nat.cast_ofNat]
        omega
      · intro j
        have h := input.rowRange.e2_short j
        simp only [OwnerRow.activeValue, activeShift, Fin.append_left, Fin.append_right,
          Nat.cast_ofNat]
        omega

theorem shiftedScalar_recompose {statement : InputStatement}
    (input : ValidCommittedWitness statement) (i : Fin activeWidth) :
    ((shiftedScalar input.row i : Nat) : Int) =
      input.row.activeValue i + (activeShift i : Int) := by
  unfold shiftedScalar
  exact Int.toNat_of_nonneg (activeValue_add_shift_bounds input i).1

theorem shiftedScalar_lt_64 {statement : InputStatement}
    (input : ValidCommittedWitness statement) (i : Fin activeWidth) :
    shiftedScalar input.row i < 64 := by
  unfold shiftedScalar
  exact (Int.toNat_lt_of_ne_zero (by omega : (64 : Nat) ≠ 0)).2
    (activeValue_add_shift_bounds input i).2

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

/-! ## One committed row joined to two exact unsigned accumulators -/

/-- Natural positive and negative masses after the deployed `+32` short normalization. -/
def shiftedPositiveMass (equation : DeployedEquation) (row : OwnerRow) : Nat :=
  CompressedLinearEquation.posPart (shiftedConstant equation) +
    ∑ i, CompressedLinearEquation.posPart (equation.activeCoefficient i) * shiftedScalar row i

def shiftedNegativeMass (equation : DeployedEquation) (row : OwnerRow) : Nat :=
  CompressedLinearEquation.negPart (shiftedConstant equation) +
    ∑ i, CompressedLinearEquation.negPart (equation.activeCoefficient i) * shiftedScalar row i

/-- The positive accumulator includes the public offset product and a zero coefficient for
the quotient scalar.  The negative accumulator gives that same scalar coefficient `q`. -/
def positiveAccumulatorConstant (equation : DeployedEquation) : Nat :=
  CompressedLinearEquation.posPart (shiftedConstant equation) +
    equation.rns.value * quotientShift

def negativeAccumulatorConstant (equation : DeployedEquation) : Nat :=
  CompressedLinearEquation.negPart (shiftedConstant equation)

def positiveAccumulatorCoefficient (equation : DeployedEquation) :
    Fin (activeWidth + 1) -> Nat :=
  Fin.append (fun i => CompressedLinearEquation.posPart (equation.activeCoefficient i))
    (fun _ => 0)

def negativeAccumulatorCoefficient (equation : DeployedEquation) :
    Fin (activeWidth + 1) -> Nat :=
  Fin.append (fun i => CompressedLinearEquation.negPart (equation.activeCoefficient i))
    (fun _ => equation.rns.value)

def accumulatorScalarWire (active : Fin activeWidth -> Idx) (quotient : Idx) :
    Fin (activeWidth + 1) -> Idx :=
  Fin.append active (fun _ => quotient)

private theorem positiveAccumulator_sum {J : Type} (asg : J -> BabyBear)
    (equation : DeployedEquation) (active : Fin activeWidth -> J) (quotient : J) :
    (∑ j, positiveAccumulatorCoefficient equation j *
      (asg (accumulatorScalarWire active quotient j)).val) =
      ∑ i, CompressedLinearEquation.posPart (equation.activeCoefficient i) *
        (asg (active i)).val := by
  unfold positiveAccumulatorCoefficient accumulatorScalarWire
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Fin.sum_univ_one, zero_mul, add_zero]

private theorem negativeAccumulator_sum {J : Type} (asg : J -> BabyBear)
    (equation : DeployedEquation) (active : Fin activeWidth -> J) (quotient : J) :
    (∑ j, negativeAccumulatorCoefficient equation j *
      (asg (accumulatorScalarWire active quotient j)).val) =
      (∑ i, CompressedLinearEquation.negPart (equation.activeCoefficient i) *
        (asg (active i)).val) + equation.rns.value * (asg quotient).val := by
  unfold negativeAccumulatorCoefficient accumulatorScalarWire
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Fin.sum_univ_one]

/-- Splitting the normalized signed coefficients into public positive/negative digit
vectors is exact; there is no field cast in this identity. -/
theorem shifted_masses_sub_eq_numerator {statement : InputStatement}
    (input : ValidCommittedWitness statement) (equation : DeployedEquation) :
    ((shiftedPositiveMass equation input.row : Nat) : Int) -
        (shiftedNegativeMass equation input.row : Int) =
      equation.numerator input.row := by
  rw [eval_eq_shifted input equation]
  unfold shiftedPositiveMass shiftedNegativeMass
  have hc := eq_posPart_sub_negPart (shiftedConstant equation)
  have hi : forall i, equation.activeCoefficient i =
      (CompressedLinearEquation.posPart (equation.activeCoefficient i) : Int) -
        (CompressedLinearEquation.negPart (equation.activeCoefficient i) : Int) :=
    fun i => eq_posPart_sub_negPart _
  push_cast
  calc
    (CompressedLinearEquation.posPart (shiftedConstant equation) : Int) +
          ∑ i, (CompressedLinearEquation.posPart (equation.activeCoefficient i) : Int) *
            (shiftedScalar input.row i : Int) -
        ((CompressedLinearEquation.negPart (shiftedConstant equation) : Int) +
          ∑ i, (CompressedLinearEquation.negPart (equation.activeCoefficient i) : Int) *
            (shiftedScalar input.row i : Int)) =
      ((CompressedLinearEquation.posPart (shiftedConstant equation) : Int) -
          (CompressedLinearEquation.negPart (shiftedConstant equation) : Int)) +
        ((∑ i, (CompressedLinearEquation.posPart
              (equation.activeCoefficient i) : Int) * (shiftedScalar input.row i : Int)) -
          (∑ i, (CompressedLinearEquation.negPart
              (equation.activeCoefficient i) : Int) * (shiftedScalar input.row i : Int))) := by
        ring
    _ = ((CompressedLinearEquation.posPart (shiftedConstant equation) : Int) -
          (CompressedLinearEquation.negPart (shiftedConstant equation) : Int)) +
        ∑ i, ((CompressedLinearEquation.posPart
              (equation.activeCoefficient i) : Int) * (shiftedScalar input.row i : Int) -
          (CompressedLinearEquation.negPart
              (equation.activeCoefficient i) : Int) * (shiftedScalar input.row i : Int)) := by
        rw [Finset.sum_sub_distrib]
    _ = shiftedConstant equation +
        ∑ i, equation.activeCoefficient i * (shiftedScalar input.row i : Int) := by
      rw [← hc]
      apply congrArg (fun z : Int => shiftedConstant equation + z)
      apply Finset.sum_congr rfl
      intro i _
      rw [← sub_mul, ← hi i]

set_option maxRecDepth 10000 in
/-- Two accepted weighted AIR instances sharing their result limbs enforce the exact
unsigned positive/negative balance.  All capacity and no-wrap obligations are explicit;
they are compile-time/range facts, not an additional acceptance relation. -/
theorem signedAccumulatorGadgets_sound {p width carryBits : Nat} [Fact p.Prime]
    (hbasep : 2 ^ limbBits <= p) (hcarryp : 2 ^ carryBits <= p)
    (equation : DeployedEquation)
    (hpositiveConstant : positiveAccumulatorConstant equation < (2 ^ limbBits) ^ width)
    (hnegativeConstant : negativeAccumulatorConstant equation < (2 ^ limbBits) ^ width)
    (hpositiveCoefficient : forall j,
      positiveAccumulatorCoefficient equation j < (2 ^ limbBits) ^ width)
    (hnegativeCoefficient : forall j,
      negativeAccumulatorCoefficient equation j < (2 ^ limbBits) ^ width)
    {J : Type} (asg : J -> ZMod p) (active : Fin activeWidth -> J) (quotient : J)
    (left right : WeightedSumWires J width limbBits carryBits)
    (hresult : left.result = right.result)
    (hleftAccept : systemAccepts asg
      (weightedSumGadget (positiveAccumulatorConstant equation)
        (positiveAccumulatorCoefficient equation) (accumulatorScalarWire active quotient)
        left))
    (hrightAccept : systemAccepts asg
      (weightedSumGadget (negativeAccumulatorConstant equation)
        (negativeAccumulatorCoefficient equation) (accumulatorScalarWire active quotient)
        right))
    (hleftNoWrap : forall column,
      AirModularView.constDigit (2 ^ limbBits) width
          (positiveAccumulatorConstant equation) column +
        ((List.finRange (activeWidth + 1)).map fun j =>
          AirModularView.constDigit (2 ^ limbBits) width
              (positiveAccumulatorCoefficient equation j) column *
            (asg (accumulatorScalarWire active quotient j)).val).sum +
        (asg (left.carry column.castSucc)).val < p)
    (hleftResultNoWrap : forall column,
      (asg (left.result column)).val +
        2 ^ limbBits * (asg (left.carry column.succ)).val < p)
    (hrightNoWrap : forall column,
      AirModularView.constDigit (2 ^ limbBits) width
          (negativeAccumulatorConstant equation) column +
        ((List.finRange (activeWidth + 1)).map fun j =>
          AirModularView.constDigit (2 ^ limbBits) width
              (negativeAccumulatorCoefficient equation j) column *
            (asg (accumulatorScalarWire active quotient j)).val).sum +
        (asg (right.carry column.castSucc)).val < p)
    (hrightResultNoWrap : forall column,
      (asg (right.result column)).val +
        2 ^ limbBits * (asg (right.carry column.succ)).val < p) :
    positiveAccumulatorConstant equation +
        ∑ j, positiveAccumulatorCoefficient equation j *
          (asg (accumulatorScalarWire active quotient j)).val =
      negativeAccumulatorConstant equation +
        ∑ j, negativeAccumulatorCoefficient equation j *
          (asg (accumulatorScalarWire active quotient j)).val := by
  have hleft := weightedSumGadget_sound hbasep hcarryp hpositiveConstant
    (positiveAccumulatorCoefficient equation) hpositiveCoefficient asg
    (accumulatorScalarWire active quotient) left hleftAccept hleftNoWrap hleftResultNoWrap
  have hright := weightedSumGadget_sound hbasep hcarryp hnegativeConstant
    (negativeAccumulatorCoefficient equation) hnegativeCoefficient asg
    (accumulatorScalarWire active quotient) right hrightAccept hrightNoWrap hrightResultNoWrap
  calc
    positiveAccumulatorConstant equation +
          ∑ j, positiveAccumulatorCoefficient equation j *
            (asg (accumulatorScalarWire active quotient j)).val =
        Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg left.result) := hleft.2.symm
    _ = Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg right.result) := by
      rw [hresult]
    _ = negativeAccumulatorConstant equation +
          ∑ j, negativeAccumulatorCoefficient equation j *
            (asg (accumulatorScalarWire active quotient j)).val := hright.2

set_option maxRecDepth 10000 in
/-- The substantive join: both accumulators use the shifted cells of the one committed
`ValidCommittedWitness`, while their extra scalar is the scalar in the already accepted
all-moduli kernel call.  AIR acceptance therefore implies the exact deployed signed BFV
integer equation for that same row and quotient. -/
theorem acceptedRowCall_accumulator_sound {statement : InputStatement}
    (input : ValidCommittedWitness statement) (rowIndex : Fin equationsPerOwner)
    (accepted : AcceptedRowCall statement input rowIndex)
    {width carryBits : Nat}
    (hpositiveConstant : positiveAccumulatorConstant accepted.equation <
      (2 ^ BfvAllModuliKernelCalls.limbBits) ^ width)
    (hnegativeConstant : negativeAccumulatorConstant accepted.equation <
      (2 ^ BfvAllModuliKernelCalls.limbBits) ^ width)
    (hpositiveCoefficient : forall j,
      positiveAccumulatorCoefficient accepted.equation j <
        (2 ^ BfvAllModuliKernelCalls.limbBits) ^ width)
    (hnegativeCoefficient : forall j,
      negativeAccumulatorCoefficient accepted.equation j <
        (2 ^ BfvAllModuliKernelCalls.limbBits) ^ width)
    {J : Type} (asg : J -> BabyBear) (active : Fin activeWidth -> J) (quotient : J)
    (left right : WeightedSumWires J width BfvAllModuliKernelCalls.limbBits carryBits)
    (hactive : forall i, (asg (active i)).val = shiftedScalar input.row i)
    (hquotient : (asg quotient).val =
      (accepted.assignment
        (BignumKernelABI.scalarMulWires (productWidth (modulusAt rowIndex))
          BfvAllModuliKernelCalls.limbBits scalarBits).scalar).val)
    (hresult : left.result = right.result)
    (hleftAccept : systemAccepts asg
      (weightedSumGadget (positiveAccumulatorConstant accepted.equation)
        (positiveAccumulatorCoefficient accepted.equation)
        (accumulatorScalarWire active quotient) left))
    (hrightAccept : systemAccepts asg
      (weightedSumGadget (negativeAccumulatorConstant accepted.equation)
        (negativeAccumulatorCoefficient accepted.equation)
        (accumulatorScalarWire active quotient) right))
    (hleftNoWrap : forall column,
      AirModularView.constDigit (2 ^ BfvAllModuliKernelCalls.limbBits) width
          (positiveAccumulatorConstant accepted.equation) column +
        ((List.finRange (activeWidth + 1)).map fun j =>
          AirModularView.constDigit (2 ^ BfvAllModuliKernelCalls.limbBits) width
              (positiveAccumulatorCoefficient accepted.equation j) column *
            (asg (accumulatorScalarWire active quotient j)).val).sum +
        (asg (left.carry column.castSucc)).val < babyBearP)
    (hleftResultNoWrap : forall column,
      (asg (left.result column)).val +
        2 ^ BfvAllModuliKernelCalls.limbBits *
          (asg (left.carry column.succ)).val < babyBearP)
    (hrightNoWrap : forall column,
      AirModularView.constDigit (2 ^ BfvAllModuliKernelCalls.limbBits) width
          (negativeAccumulatorConstant accepted.equation) column +
        ((List.finRange (activeWidth + 1)).map fun j =>
          AirModularView.constDigit (2 ^ BfvAllModuliKernelCalls.limbBits) width
              (negativeAccumulatorCoefficient accepted.equation j) column *
            (asg (accumulatorScalarWire active quotient j)).val).sum +
        (asg (right.carry column.castSucc)).val < babyBearP)
    (hrightResultNoWrap : forall column,
      (asg (right.result column)).val +
        2 ^ BfvAllModuliKernelCalls.limbBits *
          (asg (right.carry column.succ)).val < babyBearP)
    (hcarryp : 2 ^ carryBits <= babyBearP) :
    accepted.equation.numerator input.row =
      (accepted.equation.rns.value : Int) * accepted.witness.quotient.value := by
  have hair := signedAccumulatorGadgets_sound
    (p := babyBearP)
    (by norm_num [BfvAllModuliKernelCalls.limbBits, babyBearP]) hcarryp accepted.equation
    hpositiveConstant hnegativeConstant hpositiveCoefficient hnegativeCoefficient
    asg active quotient left right hresult hleftAccept hrightAccept
    hleftNoWrap hleftResultNoWrap hrightNoWrap hrightResultNoWrap
  have hq : (asg quotient).val = accepted.witness.quotient.encoded.toNat := by
    rw [hquotient]
    exact accepted.scalar_matches
  have hbalance :
      shiftedPositiveMass accepted.equation input.row +
          accepted.equation.rns.value * quotientShift =
        shiftedNegativeMass accepted.equation input.row +
          accepted.equation.rns.value * accepted.witness.quotient.encoded.toNat := by
    rw [positiveAccumulator_sum, negativeAccumulator_sum] at hair
    simp_rw [hactive] at hair
    rw [hq] at hair
    unfold positiveAccumulatorConstant negativeAccumulatorConstant at hair
    unfold shiftedPositiveMass shiftedNegativeMass
    omega
  have hmass := shifted_masses_sub_eq_numerator input accepted.equation
  have hbalanceInt := congrArg (fun z : Nat => (z : Int)) hbalance
  have hvalue : accepted.witness.quotient.value =
      (accepted.witness.quotient.encoded.toNat : Int) - quotientShift := rfl
  rw [hvalue]
  push_cast at hbalanceInt
  nlinarith

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
