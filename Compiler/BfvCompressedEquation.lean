/-
# `Compiler.BfvCompressedEquation` — one deployed compressed BFV equation

The deployed private-book check is an equality over `Int`, not over BabyBear (and not
over an Ext6 field of the same characteristic):

`C + sum selectorCoeff*selector + sum (G0+G1)*u + sum s0*e1 + sum s1*e2 = k*q`.

This module pins that statement, its 12,435-coordinate owner layout, the three ordered
RNS moduli, the centered 24-bit quotient codec, and the 384-row iteration order.  It then
joins one `q0` row to `AirModularView.scalarMulGadget`: accepted BabyBear constraints
prove the exact integer product `q0 * (k + 2^23)`.  The signed equation is normalized to
an unsigned balance before it reaches the AIR boundary.

The exact signed 12,416-term accumulator, its limb/carry lowering, the tighter runtime
quotient derivation, transcript-derived coefficients, and generated witness encoding remain
explicit residuals.  In particular, this file never casts the BFV numerator or a BFV
modulus to one BabyBear/Ext6 element and never claims that the three RNS moduli are one
BabyBear modular view.
-/
import Compiler.AirModularView
import Theory.CompressedLinearEquation

namespace Minidregg.Compiler.BfvCompressedEquation

open scoped BigOperators
open Minidregg.Compiler
open Minidregg.Theory

set_option autoImplicit false

/-! ## Deployed layout and modulus order -/

def degree : Nat := 4096
def optionCount : Nat := 128
def semanticWidth : Nat := 9
def rootWidth : Nat := 8

def kindIndex : Nat := 0
def quantityIndex : Nat := 1
def selectorBase : Nat := 2
def semanticBase : Nat := 130
def uBase : Nat := 139
def e1Base : Nat := 4235
def e2Base : Nat := 8331
def rootBase : Nat := 12427
def ownerWitnessWidth : Nat := 12435

def compressionRounds : Nat := 128
def rnsCount : Nat := 3
def equationsPerOwner : Nat := 384
def ownerCount : Nat := 4
def allOwnerEquationCount : Nat := 1536

def quotientBits : Nat := 24
def quotientShift : Nat := 8388608
def quotientAbsBound : Nat := 1130496

/-- The active equation coordinates: 128 selectors followed by three degree-4096 short
vectors.  The other 19 deployed owner coordinates have coefficient zero. -/
def activeWidth : Nat := optionCount + (degree + (degree + degree))

theorem deployed_layout_counts :
    semanticBase = selectorBase + optionCount /\
    uBase = semanticBase + semanticWidth /\
    e1Base = uBase + degree /\
    e2Base = e1Base + degree /\
    rootBase = e2Base + degree /\
    ownerWitnessWidth = rootBase + rootWidth /\
    activeWidth = 12416 := by
  norm_num [semanticBase, selectorBase, optionCount, uBase, semanticWidth,
    e1Base, e2Base, rootBase, degree, ownerWitnessWidth, rootWidth, activeWidth]

theorem deployed_batch_counts :
    equationsPerOwner = rnsCount * compressionRounds /\
    allOwnerEquationCount = ownerCount * equationsPerOwner := by
  norm_num [equationsPerOwner, rnsCount, compressionRounds, allOwnerEquationCount,
    ownerCount]

inductive RnsModulus where
  | q0
  | q1
  | q2
deriving DecidableEq, Repr

def RnsModulus.value : RnsModulus -> Nat
  | .q0 => 68719403009
  | .q1 => 68719230977
  | .q2 => 137438822401

theorem RnsModulus.value_pos (q : RnsModulus) : 0 < q.value := by
  cases q <;> norm_num [RnsModulus.value]

/-- Runtime order is modulus-major: 128 `q0` rows, then 128 `q1`, then 128 `q2`. -/
def modulusAt (i : Fin equationsPerOwner) : RnsModulus :=
  if i.val < compressionRounds then .q0
  else if i.val < 2 * compressionRounds then .q1
  else .q2

def roundAt (i : Fin equationsPerOwner) : Fin compressionRounds :=
  ⟨i.val % compressionRounds, Nat.mod_lt _ (by norm_num [compressionRounds])⟩

theorem modulusAt_first (i : Fin equationsPerOwner) (h : i.val < 128) :
    modulusAt i = .q0 := by
  simp [modulusAt, compressionRounds, h]

theorem modulusAt_middle (i : Fin equationsPerOwner)
    (hlo : 128 <= i.val) (hhi : i.val < 256) : modulusAt i = .q1 := by
  simp [modulusAt, compressionRounds, Nat.not_lt.mpr hlo, hhi]

theorem modulusAt_last (i : Fin equationsPerOwner) (h : 256 <= i.val) :
    modulusAt i = .q2 := by
  simp [modulusAt, compressionRounds, Nat.not_lt.mpr (by omega : 128 <= i.val),
    Nat.not_lt.mpr h]

/-! ## One generated row and its exact integer witness -/

/-- Public data generated for one compressed row.  `uCoefficient = G0+G1` is deliberately
a natural below `2q`, not a residue reduced a second time. -/
structure DeployedEquation where
  rns : RnsModulus
  publicConstant : Int
  publicConstant_fits_i128 : publicConstant.natAbs < 2 ^ 127
  selectorCoefficient : Fin optionCount -> Int
  selectorCoefficient_fits_i128 : forall a, (selectorCoefficient a).natAbs < 2 ^ 127
  uCoefficient : Fin degree -> Nat
  uCoefficient_lt : forall j, uCoefficient j < 2 * rns.value
  e1Sign : Fin degree -> Int
  e1Sign_pm_one : forall j, e1Sign j = -1 \/ e1Sign j = 1
  e2Sign : Fin degree -> Int
  e2Sign_pm_one : forall j, e2Sign j = -1 \/ e2Sign j = 1

/-- The full 12,435-coordinate owner witness, before the 384 quotient coordinates and
power-of-two padding are appended by the distributed frontend. -/
structure OwnerRow where
  kind : Int
  quantity : Int
  selector : Fin optionCount -> Int
  semantic : Fin semanticWidth -> Int
  u : Fin degree -> Int
  e1 : Fin degree -> Int
  e2 : Fin degree -> Int
  root : Fin rootWidth -> Int

/-- Runtime decoding/range facts used by one equation.  Upstream linked R1CS additionally
enforces the semantic table relation and selector one-hotness; those are not needed to
turn this row's already-generated equation into an exact integer statement. -/
structure OwnerRow.RuntimeRange (row : OwnerRow) : Prop where
  kind_u64 : 0 <= row.kind /\ row.kind < 2 ^ 64
  quantity_range : 0 <= row.quantity /\ row.quantity <= 15
  selector_bit : forall a, row.selector a = 0 \/ row.selector a = 1
  semantic_u64 : forall i, 0 <= row.semantic i /\ row.semantic i < 2 ^ 64
  u_short : forall j, -32 <= row.u j /\ row.u j < 32
  e1_short : forall j, -32 <= row.e1 j /\ row.e1 j < 32
  e2_short : forall j, -32 <= row.e2 j /\ row.e2 j < 32
  root_babyBear : forall i, 0 <= row.root i /\ row.root i < babyBearP

/-- Exact active-coordinate order inherited from the deployed 12,435-coordinate vector. -/
def OwnerRow.activeValue (row : OwnerRow) : Fin activeWidth -> Int :=
  Fin.append row.selector (Fin.append row.u (Fin.append row.e1 row.e2))

def DeployedEquation.activeCoefficient (e : DeployedEquation) : Fin activeWidth -> Int :=
  Fin.append e.selectorCoefficient
    (Fin.append (fun j => (e.uCoefficient j : Int)) (Fin.append e.e1Sign e.e2Sign))

private theorem sum_mul_append_four {n0 n1 n2 n3 : Nat}
    (a0 b0 : Fin n0 -> Int) (a1 b1 : Fin n1 -> Int)
    (a2 b2 : Fin n2 -> Int) (a3 b3 : Fin n3 -> Int) :
    (∑ i, Fin.append a0 (Fin.append a1 (Fin.append a2 a3)) i *
      Fin.append b0 (Fin.append b1 (Fin.append b2 b3)) i) =
      (∑ i, a0 i * b0 i) + (∑ i, a1 i * b1 i) +
        (∑ i, a2 i * b2 i) + (∑ i, a3 i * b3 i) := by
  simp [Fin.sum_univ_add]
  ring

/-- Candidate-independent exact equation consumed by `Theory.CompressedLinearEquation`. -/
def DeployedEquation.asTheory (e : DeployedEquation) :
    CompressedLinearEquation.Equation activeWidth where
  modulus := e.rns.value
  modulus_pos := e.rns.value_pos
  publicConstant := e.publicConstant
  coefficient := e.activeCoefficient

/-- The exact deployed numerator, with no field cast or modular reduction. -/
def DeployedEquation.numerator (e : DeployedEquation) (row : OwnerRow) : Int :=
  e.publicConstant +
    (∑ a, e.selectorCoefficient a * row.selector a) +
    (∑ j, (e.uCoefficient j : Int) * row.u j) +
    (∑ j, e.e1Sign j * row.e1 j) +
    (∑ j, e.e2Sign j * row.e2 j)

theorem DeployedEquation.eval_active_eq_numerator (e : DeployedEquation) (row : OwnerRow) :
    e.asTheory.eval row.activeValue = e.numerator row := by
  unfold CompressedLinearEquation.Equation.eval DeployedEquation.asTheory
    DeployedEquation.activeCoefficient OwnerRow.activeValue
    DeployedEquation.numerator activeWidth
  rw [sum_mul_append_four]
  ring

/-- Four canonical radix-64 limbs encode `k+2^23`; the stored value is the signed `k`. -/
abbrev DeployedQuotient :=
  CompressedLinearEquation.CenteredLimbs 64 4 quotientShift quotientAbsBound

theorem deployedQuotient_capacity (q : DeployedQuotient) :
    q.encoded.toNat < 2 ^ quotientBits := by
  simpa [quotientBits] using q.encoded_lt_capacity (by norm_num : 0 < 64)

theorem deployedQuotient_abs (q : DeployedQuotient) :
    q.value.natAbs <= quotientAbsBound := q.value_abs_le

/-- Each runtime short becomes one canonical radix-64 digit after the deployed `+32`
shift.  This is the local signed-limb fact required by a future exact accumulator. -/
theorem short_shift_is_radix64_digit (x : Int) (h : -32 <= x /\ x < 32) :
    0 <= x + 32 /\ (x + 32).toNat < 64 /\ ((x + 32).toNat : Int) = x + 32 := by
  constructor
  · omega
  constructor
  · have hnonneg : 0 <= x + 32 := by omega
    rw [Int.toNat_lt] <;> omega
  · exact Int.toNat_of_nonneg (by omega)

/-- One exact deployed witness.  This is the checked-i128 equality computed by Rust. -/
structure RuntimeWitness (e : DeployedEquation) where
  row : OwnerRow
  rowRange : row.RuntimeRange
  quotient : DeployedQuotient
  equation_holds : e.numerator row = (e.rns.value : Int) * quotient.value

def RuntimeWitness.toTheory {e : DeployedEquation} (w : RuntimeWitness e) :
    CompressedLinearEquation.Witness (base := 64) (width := 4)
      (shift := quotientShift) (bound := quotientAbsBound) e.asTheory where
  value := w.row.activeValue
  quotient := w.quotient
  exact := by
    rw [e.eval_active_eq_numerator]
    exact w.equation_holds

/-- Signed terms and the centered quotient normalize to the exact unsigned equality that
a limb/carry accumulator must enforce. -/
theorem RuntimeWitness.shifted_balance {e : DeployedEquation} (w : RuntimeWitness e) :
    e.asTheory.positiveMass w.row.activeValue + e.rns.value * quotientShift =
      e.asTheory.negativeMass w.row.activeValue +
        e.rns.value * w.quotient.encoded.toNat := by
  exact w.toTheory.shifted_balance

/-! ## The 384-row iterable generalization -/

/-- This is deliberately an iterable schema, not a claim that one row proves all 384. -/
structure OwnerBatch where
  equation : Fin equationsPerOwner -> DeployedEquation
  modulus_order : forall i, (equation i).rns = modulusAt i

structure OwnerBatch.Witness (batch : OwnerBatch) where
  row : forall i, RuntimeWitness (batch.equation i)

/-- The four-owner frontend has 1,536 independently exact equations. -/
abbrev FullFrontend := Fin ownerCount -> OwnerBatch

/-! ## One honest q0 AIR product boundary -/

variable {Idx : Type}

/-- The emittable block used by a q0 row.  Width ten is enough for
`q0 * (2^24-1)` in radix 64. -/
def q0ProductGadget (w : AirModularView.ScalarMulWires Idx 10 6 quotientBits) :
    ConstraintSystem BabyBear Idx :=
  AirModularView.scalarMulGadget RnsModulus.q0.value w

theorem q0ProductGadget_sound (asg : Idx -> BabyBear)
    (w : AirModularView.ScalarMulWires Idx 10 6 quotientBits)
    (h : systemAccepts asg (q0ProductGadget w)) :
    (asg w.scalar).val < 2 ^ quotientBits /\
    Bignum.Canonical 64 10 (AirBignum.limbVals asg w.product) /\
    Bignum.denoteNat 64 (AirBignum.limbVals asg w.product) =
      RnsModulus.q0.value * (asg w.scalar).val := by
  obtain ⟨hcap, -, hleft, hright⟩ := AirModularView.fheggQ0_scalar24_base64_fits
  exact AirModularView.scalarMulGadget_sound
    (p := babyBearP) (modulus := RnsModulus.q0.value)
    (width := 10) (limbBits := 6) (quotientBits := quotientBits)
    (by norm_num [babyBearP]) (by norm_num [babyBearP, quotientBits]) hcap
    (by simpa [quotientBits] using hleft)
    (by simpa [quotientBits] using hright) asg w h

/-- Package the accepted product limbs as the existing canonical common-integer object.
This does not add a second modular view; it records the unreduced integer proved by the
AIR carries. -/
def q0ProductCommonInteger (asg : Idx -> BabyBear)
    (w : AirModularView.ScalarMulWires Idx 10 6 quotientBits)
    (h : systemAccepts asg (q0ProductGadget w)) :
    CrossModulus.CommonInteger 64 10 where
  limbs := AirBignum.limbVals asg w.product
  canonical := (q0ProductGadget_sound asg w h).2.1

theorem q0ProductCommonInteger_value (asg : Idx -> BabyBear)
    (w : AirModularView.ScalarMulWires Idx 10 6 quotientBits)
    (h : systemAccepts asg (q0ProductGadget w)) :
    (q0ProductCommonInteger asg w h).value =
      RnsModulus.q0.value * (asg w.scalar).val := by
  exact (q0ProductGadget_sound asg w h).2.2

/-- **The one-row join.** If the scalar wire is the canonical shifted quotient, accepted
AIR constraints replace the right-hand `q0*shifted` term by their exact radix-64 product.
The scalar-link premise is the precise interface a combined accumulator gadget must wire;
it is not hidden as a field-level integer cast. -/
theorem q0_row_bridge_sound {e : DeployedEquation} (witness : RuntimeWitness e)
    (hq0 : e.rns = .q0) (asg : Idx -> BabyBear)
    (w : AirModularView.ScalarMulWires Idx 10 6 quotientBits)
    (haccept : systemAccepts asg (q0ProductGadget w))
    (hscalar : (asg w.scalar).val = witness.quotient.encoded.toNat) :
    e.asTheory.positiveMass witness.row.activeValue +
        RnsModulus.q0.value * quotientShift =
      e.asTheory.negativeMass witness.row.activeValue +
        Bignum.denoteNat 64 (AirBignum.limbVals asg w.product) := by
  have hbalance := witness.shifted_balance
  have hproduct := (q0ProductGadget_sound asg w haccept).2.2
  rw [hq0] at hbalance
  have hproduct' :
      Bignum.denoteNat 64 (AirBignum.limbVals asg w.product) =
        RnsModulus.q0.value * witness.quotient.encoded.toNat := by
    simpa [hscalar] using hproduct
  rw [← hproduct'] at hbalance
  exact hbalance

/-- The same one-row join stated through `Theory.CrossModulus.CommonInteger`: both sides
name one canonical unreduced integer, not a BabyBear residue. -/
theorem q0_row_commonInteger_bridge_sound {e : DeployedEquation}
    (witness : RuntimeWitness e) (hq0 : e.rns = .q0) (asg : Idx -> BabyBear)
    (w : AirModularView.ScalarMulWires Idx 10 6 quotientBits)
    (haccept : systemAccepts asg (q0ProductGadget w))
    (hscalar : (asg w.scalar).val = witness.quotient.encoded.toNat) :
    e.asTheory.positiveMass witness.row.activeValue +
        RnsModulus.q0.value * quotientShift =
      e.asTheory.negativeMass witness.row.activeValue +
        (q0ProductCommonInteger asg w haccept).value := by
  simpa [q0ProductCommonInteger, CrossModulus.CommonInteger.value] using
    q0_row_bridge_sound witness hq0 asg w haccept hscalar

/-- The q0 block is emitted through the existing descriptor IR. -/
theorem emit_q0ProductGadget_iff (ix : Idx -> Nat) (hinj : Function.Injective ix)
    (nPublic nVars : Nat) (hbound : forall i, ix i < nVars)
    (asg : Idx -> BabyBear)
    (w : AirModularView.ScalarMulWires Idx 10 6 quotientBits) :
    (exists wv : Nat -> BabyBear, (forall i, wv (ix i) = asg i) /\
      descriptorHolds (emit ix nPublic nVars (q0ProductGadget w)) wv) <->
      systemAccepts asg (q0ProductGadget w) := by
  exact AirModularView.emit_scalarMulGadget_iff ix hinj nPublic nVars hbound asg
    RnsModulus.q0.value w

/-! ## Characteristic refuter -/

/-- A single BabyBear cell aliases distinct integers.  Any Ext6 over BabyBear has the
same characteristic, so extension degree cannot turn this cast into a wide integer. -/
theorem babyBear_integer_cast_not_injective :
    (0 : BabyBear) = (babyBearP : BabyBear) /\ 0 != babyBearP := by
  constructor
  · simp
  · norm_num [babyBearP]

/-- info: 'Minidregg.Compiler.BfvCompressedEquation.DeployedEquation.eval_active_eq_numerator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DeployedEquation.eval_active_eq_numerator
/-- info: 'Minidregg.Compiler.BfvCompressedEquation.RuntimeWitness.shifted_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RuntimeWitness.shifted_balance
/-- info: 'Minidregg.Compiler.BfvCompressedEquation.q0ProductGadget_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms q0ProductGadget_sound
/-- info: 'Minidregg.Compiler.BfvCompressedEquation.q0ProductCommonInteger_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms q0ProductCommonInteger_value
/-- info: 'Minidregg.Compiler.BfvCompressedEquation.q0_row_bridge_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms q0_row_bridge_sound
/-- info: 'Minidregg.Compiler.BfvCompressedEquation.q0_row_commonInteger_bridge_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms q0_row_commonInteger_bridge_sound
/-- info: 'Minidregg.Compiler.BfvCompressedEquation.emit_q0ProductGadget_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms emit_q0ProductGadget_iff
/-- info: 'Minidregg.Compiler.BfvCompressedEquation.babyBear_integer_cast_not_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms babyBear_integer_cast_not_injective

end Minidregg.Compiler.BfvCompressedEquation
