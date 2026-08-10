/-
# `Assurance.BfvNativeBufferAdmission` -- checked BFV arithmetic buffers

This module gives one concrete end-to-end boundary for the deployed compressed-BFV
arithmetic.  For each of the 384 rows, Lean authors one descriptor containing the fixed
q0/q1/q2 scalar-product gadget and both signed accumulators.  An opaque `PlanRunner`
returns only the bounded wire buffer.  `NativeKernelPlan.run` checks registration,
layout, and the emitted descriptor; a second Lean Boolean checks the exact committed-row
and no-wrap links required by `BfvReceiptClause.CheckedRowBuffer`.

Successful admission constructs the existing `AcceptedToken` and hence the existing
private-computation evidence.  No meaning is assigned to how a runner computed its
candidate buffer, and no native correspondence, privacy, knowledge, proof-suite, or
controller-soundness claim is made.
-/
import Assurance.BfvPrivateComputationJoin
import Compiler.NativeKernelPlan

namespace Minidregg.Assurance.BfvNativeBufferAdmission

open Minidregg.Assurance.PrivateComputationReceiptClause
open Minidregg.Assurance.BfvPrivateComputationJoin
open Minidregg.Compiler
open Minidregg.Compiler.BignumKernelABI
open Minidregg.Compiler.BfvAllModuliKernelCalls
open Minidregg.Compiler.BfvCompressedEquation
open Minidregg.Compiler.BfvInputValidity
open Minidregg.Compiler.BfvReceiptClause
open Minidregg.Compiler.BfvSignedAccumulatorAir
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.SemanticManifest
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-! ## One shared scalar/accumulator wire layout -/

def mapScalarMulWires {A B : Type} {width limbBits quotientBits : Nat}
    (f : A -> B) (w : AirModularView.ScalarMulWires A width limbBits quotientBits) :
    AirModularView.ScalarMulWires B width limbBits quotientBits where
  scalar := f w.scalar
  scalarBit := fun i => f (w.scalarBit i)
  product := fun i => f (w.product i)
  productBit := fun i j => f (w.productBit i j)
  carry := fun i => f (w.carry i)
  carryBit := fun i j => f (w.carryBit i j)

def mapWeightedSumWires {A B : Type} {width limbBits carryBits : Nat}
    (f : A -> B) (w : WeightedSumWires A width limbBits carryBits) :
    WeightedSumWires B width limbBits carryBits where
  result := fun i => f (w.result i)
  resultBit := fun i j => f (w.resultBit i j)
  carry := fun i => f (w.carry i)
  carryBit := fun i j => f (w.carryBit i j)

def scalarCellCount (rowIndex : Fin equationsPerOwner) : Nat :=
  scalarMulWireCount (productWidth (modulusAt rowIndex)) limbBits scalarBits

def activeBase (rowIndex : Fin equationsPerOwner) : Nat := scalarCellCount rowIndex
def resultBase (rowIndex : Fin equationsPerOwner) : Nat := activeBase rowIndex + activeWidth
def resultBitBase (rowIndex : Fin equationsPerOwner) (width : Nat) : Nat :=
  resultBase rowIndex + width
def leftCarryBase (rowIndex : Fin equationsPerOwner) (width : Nat) : Nat :=
  resultBitBase rowIndex width + width * limbBits
def leftCarryBitBase (rowIndex : Fin equationsPerOwner) (width carryBits : Nat) : Nat :=
  leftCarryBase rowIndex width + (width + 1)
def rightCarryBase (rowIndex : Fin equationsPerOwner) (width carryBits : Nat) : Nat :=
  leftCarryBitBase rowIndex width carryBits + (width + 1) * carryBits
def rightCarryBitBase (rowIndex : Fin equationsPerOwner) (width carryBits : Nat) : Nat :=
  rightCarryBase rowIndex width carryBits + (width + 1)
def accumulatorCellCount (width carryBits : Nat) : Nat :=
  activeWidth + width + width * limbBits +
    (width + 1) + (width + 1) * carryBits +
    (width + 1) + (width + 1) * carryBits
def rowWireCount (rowIndex : Fin equationsPerOwner) (width carryBits : Nat) : Nat :=
  scalarCellCount rowIndex + accumulatorCellCount width carryBits

def liftScalarWire (rowIndex : Fin equationsPerOwner) (width carryBits : Nat)
    (i : Fin (scalarCellCount rowIndex)) : Fin (rowWireCount rowIndex width carryBits) :=
  ⟨i.val, by
    have hi := i.isLt
    simp only [rowWireCount, accumulatorCellCount]
    omega⟩

def rowScalarWires (rowIndex : Fin equationsPerOwner) (width carryBits : Nat) :
    AirModularView.ScalarMulWires (Fin (rowWireCount rowIndex width carryBits))
      (productWidth (modulusAt rowIndex)) limbBits scalarBits :=
  mapScalarMulWires (liftScalarWire rowIndex width carryBits)
    (scalarMulWires (productWidth (modulusAt rowIndex)) limbBits scalarBits)

def rowActiveWire (rowIndex : Fin equationsPerOwner) (width carryBits : Nat)
    (i : Fin activeWidth) : Fin (rowWireCount rowIndex width carryBits) :=
  ⟨activeBase rowIndex + i.val, by
    have hi := i.isLt
    simp only [rowWireCount, accumulatorCellCount, activeBase]
    omega⟩

def rowResultWire (rowIndex : Fin equationsPerOwner) (width carryBits : Nat)
    (i : Fin width) : Fin (rowWireCount rowIndex width carryBits) :=
  ⟨resultBase rowIndex + i.val, by
    have hi := i.isLt
    simp only [rowWireCount, accumulatorCellCount, resultBase, activeBase]
    omega⟩

def rowResultBitWire (rowIndex : Fin equationsPerOwner) (width carryBits : Nat)
    (i : Fin width) (j : Fin limbBits) : Fin (rowWireCount rowIndex width carryBits) :=
  let ij : Fin (width * limbBits) := finProdFinEquiv (i, j)
  ⟨resultBitBase rowIndex width + ij.val, by
    have hij := ij.isLt
    simp only [rowWireCount, accumulatorCellCount, resultBitBase, resultBase, activeBase]
    omega⟩

def rowLeftCarryWire (rowIndex : Fin equationsPerOwner) (width carryBits : Nat)
    (i : Fin (width + 1)) : Fin (rowWireCount rowIndex width carryBits) :=
  ⟨leftCarryBase rowIndex width + i.val, by
    have hi := i.isLt
    simp only [rowWireCount, accumulatorCellCount, leftCarryBase, resultBitBase,
      resultBase, activeBase]
    omega⟩

def rowLeftCarryBitWire (rowIndex : Fin equationsPerOwner) (width carryBits : Nat)
    (i : Fin (width + 1)) (j : Fin carryBits) :
    Fin (rowWireCount rowIndex width carryBits) :=
  let ij : Fin ((width + 1) * carryBits) := finProdFinEquiv (i, j)
  ⟨leftCarryBitBase rowIndex width carryBits + ij.val, by
    have hij := ij.isLt
    simp only [rowWireCount, accumulatorCellCount, leftCarryBitBase, leftCarryBase,
      resultBitBase, resultBase, activeBase]
    omega⟩

def rowRightCarryWire (rowIndex : Fin equationsPerOwner) (width carryBits : Nat)
    (i : Fin (width + 1)) : Fin (rowWireCount rowIndex width carryBits) :=
  ⟨rightCarryBase rowIndex width carryBits + i.val, by
    have hi := i.isLt
    simp only [rowWireCount, accumulatorCellCount, rightCarryBase, leftCarryBitBase,
      leftCarryBase, resultBitBase, resultBase, activeBase]
    omega⟩

def rowRightCarryBitWire (rowIndex : Fin equationsPerOwner) (width carryBits : Nat)
    (i : Fin (width + 1)) (j : Fin carryBits) :
    Fin (rowWireCount rowIndex width carryBits) :=
  let ij : Fin ((width + 1) * carryBits) := finProdFinEquiv (i, j)
  ⟨rightCarryBitBase rowIndex width carryBits + ij.val, by
    have hij := ij.isLt
    simp only [rowWireCount, accumulatorCellCount, rightCarryBitBase, rightCarryBase,
      leftCarryBitBase, leftCarryBase, resultBitBase, resultBase, activeBase]
    omega⟩

def rowLeftWires (rowIndex : Fin equationsPerOwner) (width carryBits : Nat) :
    WeightedSumWires (Fin (rowWireCount rowIndex width carryBits)) width limbBits carryBits where
  result := rowResultWire rowIndex width carryBits
  resultBit := rowResultBitWire rowIndex width carryBits
  carry := rowLeftCarryWire rowIndex width carryBits
  carryBit := rowLeftCarryBitWire rowIndex width carryBits

def rowRightWires (rowIndex : Fin equationsPerOwner) (width carryBits : Nat) :
    WeightedSumWires (Fin (rowWireCount rowIndex width carryBits)) width limbBits carryBits where
  result := rowResultWire rowIndex width carryBits
  resultBit := rowResultBitWire rowIndex width carryBits
  carry := rowRightCarryWire rowIndex width carryBits
  carryBit := rowRightCarryBitWire rowIndex width carryBits

def rowQuotientWire (rowIndex : Fin equationsPerOwner) (width carryBits : Nat) :
    Fin (rowWireCount rowIndex width carryBits) :=
  (rowScalarWires rowIndex width carryBits).scalar

def rowArithmeticSystem (rowIndex : Fin equationsPerOwner) (equation : DeployedEquation)
    (width carryBits : Nat) :
    ConstraintSystem BabyBear (Fin (rowWireCount rowIndex width carryBits)) :=
  AirModularView.scalarMulGadget (modulusAt rowIndex).value
      (rowScalarWires rowIndex width carryBits) ++
  weightedSumGadget (positiveAccumulatorConstant equation)
      (positiveAccumulatorCoefficient equation)
      (accumulatorScalarWire (rowActiveWire rowIndex width carryBits)
        (rowQuotientWire rowIndex width carryBits))
      (rowLeftWires rowIndex width carryBits) ++
  weightedSumGadget (negativeAccumulatorConstant equation)
      (negativeAccumulatorCoefficient equation)
      (accumulatorScalarWire (rowActiveWire rowIndex width carryBits)
        (rowQuotientWire rowIndex width carryBits))
      (rowRightWires rowIndex width carryBits)

def rowSegments (rowIndex : Fin equationsPerOwner) (width carryBits : Nat) :
    List WireSegment :=
  scalarMulSegments (productWidth (modulusAt rowIndex)) limbBits scalarBits ++
    [{ name := "bfv_signed_accumulators",
       offset := scalarCellCount rowIndex,
       length := accumulatorCellCount width carryBits,
       visibility := .witness,
       encoding := .fieldElement }]

/-- One row is one Lean-emitted call: the deployed fixed-modulus scalar product and both
signed accumulators share a single original-variable buffer. -/
def rowKernelCall (rowIndex : Fin equationsPerOwner) (equation : DeployedEquation)
    (width carryBits : Nat) : KernelCall where
  abiVersion := 1
  entry := .constraintDescriptorV1
  segments := rowSegments rowIndex width carryBits
  calls := [scalarMulWitnessCall (modulusAt rowIndex).value
    (productWidth (modulusAt rowIndex)) limbBits scalarBits]
  descriptor := emit Fin.val 0 (rowWireCount rowIndex width carryBits)
    (rowArithmeticSystem rowIndex equation width carryBits)

theorem rowKernelCall_fullyWellFormed (rowIndex : Fin equationsPerOwner)
    (equation : DeployedEquation) (width carryBits : Nat) :
    (rowKernelCall rowIndex equation width carryBits).FullyWellFormed := by
  constructor
  · constructor
    · exact emit_wellFormed Fin.val 0 (rowWireCount rowIndex width carryBits)
        (by omega) (fun i => i.isLt) _
    · simp [rowKernelCall, rowSegments, scalarMulSegments, segmentsCoverFrom, emit,
        WireSegment.visibilityFits, scalarCellCount, rowWireCount, rightCarryBitBase,
        rightCarryBase, leftCarryBitBase, leftCarryBase, resultBitBase, resultBase,
        activeBase, accumulatorCellCount, scalarMulWireCount, mulCarryBitBase, mulCarryBase, productBitBase,
        productBase, scalarBitBase, scalarBase]
      all_goals omega
  · simp [KernelCall.CallsWellShaped, rowKernelCall, scalarMulWitnessCall, emit,
      WitnessCall.WellShaped, ScalarMulConstCall.WellShaped, WireSpan.inBounds,
      rowWireCount, rightCarryBitBase, rightCarryBase, leftCarryBitBase, leftCarryBase,
      resultBitBase, resultBase, activeBase, scalarCellCount, scalarMulWireCount,
      accumulatorCellCount,
      mulCarryBitBase, mulCarryBase, productBitBase, productBase, scalarBitBase, scalarBase]
    all_goals omega

/-! ## A row template and its executable Lean checks -/

/-- All non-buffer BFV data for one row.  Acceptance fields are deliberately absent. -/
structure RowTemplate (statement : InputStatement)
    (input : ValidCommittedWitness statement) (rowIndex : Fin equationsPerOwner) where
  source : EquationSource
  source_eq : source = statement.equationSource rowIndex
  rowReference : WitnessReference
  callReference : WitnessReference
  row_reference_eq : rowReference = statement.reference
  call_reference_eq : callReference = statement.reference
  equation : DeployedEquation
  equation_modulus : equation.rns = modulusAt rowIndex
  witness : RuntimeWitness equation
  witness_row_eq : witness.row = input.row
  width : Nat
  carryBits : Nat

def RowTemplate.instruction {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (template : RowTemplate statement input rowIndex) : Instruction :=
  Instruction.arithmetic bfvClauseId
    (rowKernelCall rowIndex template.equation template.width template.carryBits) []

def RowTemplate.plan {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (manifest : Manifest) (template : RowTemplate statement input rowIndex) : Plan where
  manifestEncoding := manifest.canonicalEncoding
  instructions := [template.instruction]

def RowTemplate.candidate {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (template : RowTemplate statement input rowIndex)
    (response : KernelResponse template.instruction) : Nat -> BabyBear :=
  response.totalWires

def RowTemplate.natLeftWires {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (template : RowTemplate statement input rowIndex) :
    WeightedSumWires Nat template.width limbBits template.carryBits :=
  mapWeightedSumWires Fin.val (rowLeftWires rowIndex template.width template.carryBits)

def RowTemplate.natRightWires {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (template : RowTemplate statement input rowIndex) :
    WeightedSumWires Nat template.width limbBits template.carryBits :=
  mapWeightedSumWires Fin.val (rowRightWires rowIndex template.width template.carryBits)

def RowTemplate.scalarAssignment {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (template : RowTemplate statement input rowIndex)
    (response : KernelResponse template.instruction) :
    Fin (scalarCellCount rowIndex) -> BabyBear := fun i =>
  template.candidate response (liftScalarWire rowIndex template.width template.carryBits i).val

/-- Cross-buffer and integer no-wrap facts not expressed by the field descriptor. -/
def RowTemplate.ResponseBounds {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (template : RowTemplate statement input rowIndex)
    (response : KernelResponse template.instruction) : Prop :=
  (forall i : Fin activeWidth,
    (template.candidate response
      (rowActiveWire rowIndex template.width template.carryBits i).val).val =
        shiftedScalar input.row i) /\
  (template.candidate response
    (rowQuotientWire rowIndex template.width template.carryBits).val).val =
      template.witness.quotient.encoded.toNat /\
  positiveAccumulatorConstant template.equation < (2 ^ limbBits) ^ template.width /\
  negativeAccumulatorConstant template.equation < (2 ^ limbBits) ^ template.width /\
  (forall j : Fin (activeWidth + 1),
    positiveAccumulatorCoefficient template.equation j < (2 ^ limbBits) ^ template.width) /\
  (forall j : Fin (activeWidth + 1),
    negativeAccumulatorCoefficient template.equation j < (2 ^ limbBits) ^ template.width) /\
  (forall column : Fin template.width,
    AirModularView.constDigit (2 ^ limbBits) template.width
        (positiveAccumulatorConstant template.equation) column +
      ((List.finRange (activeWidth + 1)).map fun j =>
        AirModularView.constDigit (2 ^ limbBits) template.width
            (positiveAccumulatorCoefficient template.equation j) column *
          (template.candidate response
            (accumulatorScalarWire
              (fun i => (rowActiveWire rowIndex template.width template.carryBits i).val)
              (rowQuotientWire rowIndex template.width template.carryBits).val j)).val).sum +
      (template.candidate response
        ((template.natLeftWires).carry column.castSucc)).val < babyBearP) /\
  (forall column : Fin template.width,
    (template.candidate response ((template.natLeftWires).result column)).val +
      2 ^ limbBits *
        (template.candidate response ((template.natLeftWires).carry column.succ)).val <
      babyBearP) /\
  (forall column : Fin template.width,
    AirModularView.constDigit (2 ^ limbBits) template.width
        (negativeAccumulatorConstant template.equation) column +
      ((List.finRange (activeWidth + 1)).map fun j =>
        AirModularView.constDigit (2 ^ limbBits) template.width
            (negativeAccumulatorCoefficient template.equation j) column *
          (template.candidate response
            (accumulatorScalarWire
              (fun i => (rowActiveWire rowIndex template.width template.carryBits i).val)
              (rowQuotientWire rowIndex template.width template.carryBits).val j)).val).sum +
      (template.candidate response
        ((template.natRightWires).carry column.castSucc)).val < babyBearP) /\
  (forall column : Fin template.width,
    (template.candidate response ((template.natRightWires).result column)).val +
      2 ^ limbBits *
        (template.candidate response ((template.natRightWires).carry column.succ)).val <
      babyBearP) /\
  2 ^ template.carryBits <= babyBearP

/-- Executable acceptance of an existing Lean AIR system. -/
def systemAcceptsCheck (asg : Nat -> BabyBear) (system : ConstraintSystem BabyBear Nat) : Bool :=
  system.all fun term => decide (accepts asg term)

theorem systemAcceptsCheck_eq_true_iff (asg : Nat -> BabyBear)
    (system : ConstraintSystem BabyBear Nat) :
    systemAcceptsCheck asg system = true <-> systemAccepts asg system := by
  simp [systemAcceptsCheck, systemAccepts]

def RowTemplate.ResponseValid {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (template : RowTemplate statement input rowIndex)
    (response : KernelResponse template.instruction) : Prop :=
  systemAccepts (template.candidate response)
      (weightedSumGadget (positiveAccumulatorConstant template.equation)
        (positiveAccumulatorCoefficient template.equation)
        (accumulatorScalarWire
          (fun i => (rowActiveWire rowIndex template.width template.carryBits i).val)
          (rowQuotientWire rowIndex template.width template.carryBits).val)
        template.natLeftWires) /\
  systemAccepts (template.candidate response)
      (weightedSumGadget (negativeAccumulatorConstant template.equation)
        (negativeAccumulatorCoefficient template.equation)
        (accumulatorScalarWire
          (fun i => (rowActiveWire rowIndex template.width template.carryBits i).val)
          (rowQuotientWire rowIndex template.width template.carryBits).val)
        template.natRightWires) /\
  template.ResponseBounds response

def RowTemplate.responseValidCheck {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (template : RowTemplate statement input rowIndex)
    (response : KernelResponse template.instruction) : Bool :=
  systemAcceptsCheck (template.candidate response)
      (weightedSumGadget (positiveAccumulatorConstant template.equation)
        (positiveAccumulatorCoefficient template.equation)
        (accumulatorScalarWire
          (fun i => (rowActiveWire rowIndex template.width template.carryBits i).val)
          (rowQuotientWire rowIndex template.width template.carryBits).val)
        template.natLeftWires) &&
  (systemAcceptsCheck (template.candidate response)
      (weightedSumGadget (negativeAccumulatorConstant template.equation)
        (negativeAccumulatorCoefficient template.equation)
        (accumulatorScalarWire
          (fun i => (rowActiveWire rowIndex template.width template.carryBits i).val)
          (rowQuotientWire rowIndex template.width template.carryBits).val)
        template.natRightWires) &&
  @decide (template.ResponseBounds response) (by
    unfold RowTemplate.ResponseBounds
    infer_instance))

theorem RowTemplate.responseValidCheck_eq_true_iff {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (template : RowTemplate statement input rowIndex)
    (response : KernelResponse template.instruction) :
    template.responseValidCheck response = true <-> template.ResponseValid response := by
  simp only [responseValidCheck, Bool.and_eq_true, systemAcceptsCheck_eq_true_iff,
    decide_eq_true_eq, ResponseValid]

/-! ## Lean-owned row admission -/

structure RowAdmission {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (manifest : Manifest) (template : RowTemplate statement input rowIndex)
    (response : KernelResponse template.instruction) where
  certified : CertifiedResponse manifest template.instruction response
  responseValid : template.responseValidCheck response = true

/-- The row controller uses the generic fallible native boundary.  The error payload is
opaque; the success payload is only the instruction-indexed bounded buffer. -/
abbrev FallibleRowRunner (Error : Type) := PlanRunner Error

inductive RowFailure
  | check (failure : NativeKernelPlan.Failure)
  | responseLink
deriving Repr

inductive RowOutcome (Error : Type) {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (manifest : Manifest) (template : RowTemplate statement input rowIndex)
    (runner : FallibleRowRunner Error)
  | blocked (error : Error)
  | rejected (failure : RowFailure)
  | admitted {response : KernelResponse template.instruction}
      (token : RowAdmission manifest template response)

/-- The runner contributes only buffers.  Both the descriptor and the remaining exact
integer links are checked before the sole admitted constructor is returned. -/
def runRow {Error : Type} {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (manifest : Manifest) (template : RowTemplate statement input rowIndex)
    (runner : FallibleRowRunner Error) : RowOutcome Error manifest template runner :=
  match runner template.instruction with
  | .error error => .blocked error
  | .ok response =>
      match checkInstruction manifest template.instruction response with
      | .inl failure => .rejected (.check failure)
      | .inr certified =>
          if h : template.responseValidCheck response = true then
            .admitted ⟨certified, h⟩
          else .rejected .responseLink

def RowOutcome.IsAdmitted {Error : Type} {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    {manifest : Manifest} {template : RowTemplate statement input rowIndex}
    {runner : FallibleRowRunner Error} : RowOutcome Error manifest template runner -> Prop
  | .blocked _ => False
  | .rejected _ => False
  | .admitted _ => True

/-- Positive controller path: an actual successful native buffer that passes the existing
descriptor checker and the exact response-link checker reaches admission. -/
theorem checkedResponse_reaches_admitted {Error : Type} {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (manifest : Manifest) (template : RowTemplate statement input rowIndex)
    (runner : FallibleRowRunner Error) (response : KernelResponse template.instruction)
    (returned : runner template.instruction = .ok response)
    {certified : CertifiedResponse manifest template.instruction response}
    (checked : checkInstruction manifest template.instruction response = .inr certified)
    (linked : template.responseValidCheck response = true) :
    (runRow manifest template runner).IsAdmitted := by
  simp [runRow, returned, checked, linked, RowOutcome.IsAdmitted]

/-- A native error on the sole row instruction also blocks the generic one-instruction
plan before any certificate can be constructed. -/
theorem nativeFailure_blocks_plan {Error : Type} {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (manifest : Manifest) (template : RowTemplate statement input rowIndex)
    (runner : FallibleRowRunner Error) (error : Error)
    (failed : runner template.instruction = .error error) :
    NativeKernelPlan.run manifest (template.plan manifest) runner = .blocked error :=
  firstInstructionError_blocks manifest (template.plan manifest) runner
    template.instruction [] error rfl rfl failed

theorem nativeFailure_stops {Error : Type} {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (manifest : Manifest) (template : RowTemplate statement input rowIndex)
    (runner : FallibleRowRunner Error) (error : Error)
    (failed : runner template.instruction = .error error) :
    runRow manifest template runner = .blocked error := by
  unfold runRow
  rw [failed]

theorem RowAdmission.descriptorAcceptance {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    {manifest : Manifest} {template : RowTemplate statement input rowIndex}
    {response : KernelResponse template.instruction}
    (admission : RowAdmission manifest template response) :
    template.instruction.call.Accepts response.totalWires :=
  admission.certified.descriptorAcceptance

theorem RowAdmission.systemsAccept {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    {manifest : Manifest} {template : RowTemplate statement input rowIndex}
    {response : KernelResponse template.instruction}
    (admission : RowAdmission manifest template response) :
    systemAccepts
        (fun i : Fin (rowWireCount rowIndex template.width template.carryBits) =>
          template.candidate response i.val)
        (rowArithmeticSystem rowIndex template.equation template.width template.carryBits) := by
  apply (emit_accepts_iff_fin
    (rowWireCount rowIndex template.width template.carryBits) 0
    (fun i => template.candidate response i.val)
    (rowArithmeticSystem rowIndex template.equation template.width template.carryBits)).mp
  refine ⟨template.candidate response, fun _ => rfl, ?_⟩
  simpa [RowTemplate.instruction, rowKernelCall] using admission.descriptorAcceptance

theorem RowAdmission.threeSystemsAccept {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    {manifest : Manifest} {template : RowTemplate statement input rowIndex}
    {response : KernelResponse template.instruction}
    (admission : RowAdmission manifest template response) :
    systemAccepts
        (fun i : Fin (rowWireCount rowIndex template.width template.carryBits) =>
          template.candidate response i.val)
        (AirModularView.scalarMulGadget (modulusAt rowIndex).value
          (rowScalarWires rowIndex template.width template.carryBits)) /\
    systemAccepts
        (fun i : Fin (rowWireCount rowIndex template.width template.carryBits) =>
          template.candidate response i.val)
        (weightedSumGadget (positiveAccumulatorConstant template.equation)
          (positiveAccumulatorCoefficient template.equation)
          (accumulatorScalarWire (rowActiveWire rowIndex template.width template.carryBits)
            (rowQuotientWire rowIndex template.width template.carryBits))
          (rowLeftWires rowIndex template.width template.carryBits)) /\
    systemAccepts
        (fun i : Fin (rowWireCount rowIndex template.width template.carryBits) =>
          template.candidate response i.val)
        (weightedSumGadget (negativeAccumulatorConstant template.equation)
          (negativeAccumulatorCoefficient template.equation)
          (accumulatorScalarWire (rowActiveWire rowIndex template.width template.carryBits)
            (rowQuotientWire rowIndex template.width template.carryBits))
          (rowRightWires rowIndex template.width template.carryBits)) := by
  simpa [rowArithmeticSystem, systemAccepts_append] using admission.systemsAccept

noncomputable def RowAdmission.toAcceptedRowCall {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    {manifest : Manifest} {template : RowTemplate statement input rowIndex}
    {response : KernelResponse template.instruction}
    (admission : RowAdmission manifest template response) :
    AcceptedRowCall statement input rowIndex where
  source := template.source
  source_eq := template.source_eq
  rowReference := template.rowReference
  callReference := template.callReference
  row_reference_eq := template.row_reference_eq
  call_reference_eq := template.call_reference_eq
  equation := template.equation
  equation_modulus := template.equation_modulus
  witness := template.witness
  witness_row_eq := template.witness_row_eq
  assignment := template.scalarAssignment response
  callAccepted := by
    apply (scalarMulKernelCall_accepts_iff (modulusAt rowIndex).value
      (productWidth (modulusAt rowIndex)) limbBits scalarBits
      (template.scalarAssignment response)).mpr
    have h := admission.threeSystemsAccept.1
    rw [AirModularView.scalarMulGadget_correct] at h ⊢
    simp_rw [rangeGadget_correct] at h ⊢
    simpa only [RowTemplate.scalarAssignment, rowScalarWires, mapScalarMulWires,
      liftScalarWire] using h
  scalar_matches := by
    have valid := (template.responseValidCheck_eq_true_iff response).mp admission.responseValid
    simpa [RowTemplate.scalarAssignment, rowScalarWires, mapScalarMulWires,
      rowQuotientWire, liftScalarWire] using valid.2.2.2.1

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 10000 in
noncomputable def RowAdmission.toCheckedRowBuffer {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    {manifest : Manifest} {template : RowTemplate statement input rowIndex}
    {response : KernelResponse template.instruction}
    (admission : RowAdmission manifest template response) :
    CheckedRowBuffer input rowIndex admission.toAcceptedRowCall := by
  have valid := (template.responseValidCheck_eq_true_iff response).mp admission.responseValid
  rcases valid with ⟨leftAccept, rightAccept, bounds⟩
  rcases bounds with ⟨activeMatches, quotientMatches, positiveConstantFits,
    negativeConstantFits, positiveCoefficientFits, negativeCoefficientFits,
    leftNoWrap, leftResultNoWrap, rightNoWrap, rightResultNoWrap, carryFitsField⟩
  refine {
    width := template.width
    carryBits := template.carryBits
    candidate := template.candidate response
    activeWire := fun i => (rowActiveWire rowIndex template.width template.carryBits i).val
    quotientWire := (rowQuotientWire rowIndex template.width template.carryBits).val
    left := template.natLeftWires
    right := template.natRightWires
    positiveConstant_fits := positiveConstantFits
    negativeConstant_fits := negativeConstantFits
    positiveCoefficient_fits := positiveCoefficientFits
    negativeCoefficient_fits := negativeCoefficientFits
    active_matches := activeMatches
    quotient_matches := by
      rfl
    shared_result := rfl
    left_accepts := leftAccept
    right_accepts := rightAccept
    left_noWrap := leftNoWrap
    left_result_noWrap := leftResultNoWrap
    right_noWrap := rightNoWrap
    right_result_noWrap := rightResultNoWrap
    carry_fits_field := carryFitsField }

/-! ## All 384 rows and the existing BFV evidence -/

structure BatchTemplate (claim : PublicStatement) where
  input : ValidCommittedWitness claim.input
  row : forall rowIndex, RowTemplate claim.input input rowIndex
  equation_eq : forall rowIndex, (row rowIndex).equation = claim.equations.equation rowIndex

structure BatchAdmission (manifest : Manifest) (claim : PublicStatement)
    (template : BatchTemplate claim) where
  response : forall rowIndex, KernelResponse (template.row rowIndex).instruction
  row : forall rowIndex,
    RowAdmission manifest (template.row rowIndex) (response rowIndex)

noncomputable def BatchAdmission.acceptedToken {manifest : Manifest}
    {claim : PublicStatement} {template : BatchTemplate claim}
    (admission : BatchAdmission manifest claim template) : AcceptedToken claim where
  input := template.input
  batch := { rowCall := fun rowIndex => (admission.row rowIndex).toAcceptedRowCall }
  equation_eq := template.equation_eq
  checked := fun rowIndex => (admission.row rowIndex).toCheckedRowBuffer

noncomputable def BatchAdmission.evidence {manifest : Manifest}
    {claim : PublicStatement} {template : BatchTemplate claim}
    (admission : BatchAdmission manifest claim template) (commitmentId : Digest) :
    BfvPrivateComputationJoin.Evidence where
  claim := claim
  token := admission.acceptedToken
  inputRepresentation := ⟨claim.input.reference, claim.equations⟩
  input_reference_eq := rfl
  input_equation_eq := fun _ => rfl
  outputRepresentation :=
    ⟨outputRepresentationId, commitmentId, claim.input.reference, claim.equations⟩
  output_representation_id := rfl
  output_reference_eq := rfl
  output_equation_eq := fun _ => rfl

def BatchAdmission.statement {manifest : Manifest}
    {claim : PublicStatement} {template : BatchTemplate claim}
    (admission : BatchAdmission manifest claim template) (commitmentId : Digest) :
    ComputationStatement where
  program := program
  inputValue := claim
  inputArtifact := ⟨claim.input.reference, claim.equations⟩
  outputCommitment := commitmentId
  outputArtifact :=
    ⟨outputRepresentationId, commitmentId, claim.input.reference, claim.equations⟩
  privateOutput := ()

theorem BatchAdmission.evidence_accepts {manifest : Manifest}
    {claim : PublicStatement} {template : BatchTemplate claim}
    (admission : BatchAdmission manifest claim template) (commitmentId : Digest) :
    Accepts (admission.statement commitmentId) (admission.evidence commitmentId) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

noncomputable def BatchAdmission.checkedPrivateEvidence {manifest : Manifest}
    {claim : PublicStatement} {template : BatchTemplate claim}
    (admission : BatchAdmission manifest claim template) (commitmentId : Digest) :
    CheckedPrivateEvidence evidencePortal (admission.statement commitmentId) where
  witness := admission.evidence commitmentId
  verified := by
    classical
    simp [evidencePortal, admission.evidence_accepts commitmentId]

theorem BatchAdmission.every_exact_integer_equation {manifest : Manifest}
    {claim : PublicStatement} {template : BatchTemplate claim}
    (admission : BatchAdmission manifest claim template) (rowIndex) :
    (claim.equations.equation rowIndex).numerator template.input.row =
      ((claim.equations.equation rowIndex).rns.value : Int) *
        ((admission.acceptedToken).batch.rowCall rowIndex).witness.quotient.value :=
  admission.acceptedToken.every_exact_integer_equation rowIndex

/-! ## An inhabited local BFV controller/receipt binding -/

def bfvInputBridgeId : Digest := ⟨951⟩
def bfvOutputBridgeId : Digest := ⟨952⟩

/-- This pin names the Lean `runRow` admission controller in this module.  It is not a
claim about any native implementation or proof suite. -/
def bfvBufferControllerDigest : Digest := ⟨970⟩

def bfvAdmissionClauseDecl : DialectClauseDecl :=
  { bfvClauseDecl with
    verifierControllerDigest := bfvBufferControllerDigest
    requiredBridgeIds := [bfvInputBridgeId, bfvOutputBridgeId] }

theorem bfvAdmissionClause_suite_unassigned_controller_assigned :
    bfvAdmissionClauseDecl.proofSuiteId = ⟨0⟩ /\
    bfvAdmissionClauseDecl.verifierControllerDigest = bfvBufferControllerDigest /\
    bfvBufferControllerDigest ≠ ⟨0⟩ := by
  decide

def bfvInputBridge : NamedBridgeRequirement where
  bridgeId := bfvInputBridgeId
  relationId := ⟨953⟩
  sourceCarrierId := bfvResidueCarrierId
  targetCarrierId := bfvResidueCarrierId
  sourceCodecId := bfvStatementCodecReservation
  targetCodecId := bfvStatementCodecReservation

def bfvOutputBridge : NamedBridgeRequirement where
  bridgeId := bfvOutputBridgeId
  relationId := ⟨954⟩
  sourceCarrierId := bfvResidueCarrierId
  targetCarrierId := bfvResidueCarrierId
  sourceCodecId := bfvStatementCodecReservation
  targetCodecId := bfvStatementCodecReservation

def bfvManifest : Manifest where
  manifestVersion := 1
  abiId := ⟨960⟩
  semanticProgramId := ⟨961⟩
  semanticRelationId := bfvRelationId
  receiptCodecId := bfvStatementCodecReservation
  codecs :=
    [⟨bfvStatementCodecReservation, ⟨962⟩, 1⟩,
     ⟨unassignedProofCodecId, ⟨963⟩, 0⟩]
  carriers :=
    [.residueRing bfvResidueCarrierId degree 1032193
      [RnsModulus.q0.value, RnsModulus.q1.value, RnsModulus.q2.value] ⟨964⟩ ⟨965⟩]
  bridges := [bfvInputBridge, bfvOutputBridge]
  dialectClauses := [bfvAdmissionClauseDecl]
  transcriptControllerDigest := bfvBufferControllerDigest
  dimensions := []
  bounds := []

theorem bfvManifest_wellFormed : bfvManifest.WellFormed := by
  constructor <;>
    simp [bfvManifest, bfvAdmissionClauseDecl, bfvClauseDecl, bfvInputBridge,
      bfvOutputBridge, bfvInputBridgeId, bfvOutputBridgeId,
      Manifest.CodecIdsUnique, Manifest.CarrierIdsUnique, Manifest.BridgeIdsUnique,
      Manifest.ClauseIdsUnique, Manifest.lookupCodec, Manifest.lookupCarrier,
      Manifest.lookupBridge, CarrierProfile.id, bfvStatementCodecReservation,
      unassignedProofCodecId, bfvResidueCarrierId]

theorem bfvManifest_clause_registered :
    bfvManifest.lookupClause bfvClauseId = some bfvAdmissionClauseDecl := by
  decide

theorem bfvManifest_controller_exact :
    bfvManifest.transcriptControllerDigest = bfvBufferControllerDigest /\
    bfvAdmissionClauseDecl.verifierControllerDigest = bfvBufferControllerDigest := by
  decide

noncomputable def concreteBinding
    {Observer Policy Recipient Purpose AuthorizationContext CanonicalInput
      InputSourceWitness InputTargetWitness AuthorizationWitness OutputSourceWitness
      OutputTargetWitness ReleaseAuthorizationWitness DeclassificationAuthority Release : Type*}
    (authority : Authority Observer Policy Recipient Purpose AuthorizationContext
      CanonicalInput InputSourceWitness InputTargetWitness AuthorizationWitness
      OutputSourceWitness OutputTargetWitness ReleaseAuthorizationWitness
      DeclassificationAuthority Release)
    (inputBridgeExact : authority.inputBridge.name = bfvInputBridgeId) :
    ClauseBinding bfvManifest authority.declaration where
  manifestWellFormed := bfvManifest_wellFormed
  clause := bfvAdmissionClauseDecl
  clauseRegistered := bfvManifest_clause_registered
  controllerBound := rfl
  inputBridge := bfvInputBridge
  inputBridgeRegistered := by decide
  inputBridgeNameExact := by
    simpa [Authority.declaration] using inputBridgeExact
  inputBridgeRequired := by
    simp [bfvAdmissionClauseDecl, bfvClauseDecl, bfvInputBridge, bfvInputBridgeId,
      bfvOutputBridgeId]
  outputBridge := bfvOutputBridge
  outputBridgeRegistered := by decide
  outputBridgeRequired := by
    simp [bfvAdmissionClauseDecl, bfvClauseDecl, bfvOutputBridge, bfvInputBridgeId,
      bfvOutputBridgeId]

/-- Positive non-vacuity tooth: every actual semantic completion can be issued as a BFV
receipt event under the concrete well-formed manifest.  Its manifest controller pin names
the Lean buffer checker above, while the proof-suite pin remains explicitly unassigned. -/
noncomputable def issueReceiptEvent
    {Observer Policy Recipient Purpose AuthorizationContext CanonicalInput
      InputSourceWitness InputTargetWitness AuthorizationWitness OutputSourceWitness
      OutputTargetWitness ReleaseAuthorizationWitness DeclassificationAuthority Release : Type*}
    (authority : Authority Observer Policy Recipient Purpose AuthorizationContext
      CanonicalInput InputSourceWitness InputTargetWitness AuthorizationWitness
      OutputSourceWitness OutputTargetWitness ReleaseAuthorizationWitness
      DeclassificationAuthority Release)
    (inputBridgeExact : authority.inputBridge.name = bfvInputBridgeId)
    [DecidableEq Release]
    {kind : Minidregg.Theory.TypedAuthorization.ResourceKind}
    (turnRequest : Minidregg.Theory.TypedAuthorization.Request kind)
    {request : authority.declaration.Request} {outcome : authority.declaration.Outcome}
    (completion : authority.declaration.Completion request outcome) :
    ReceiptEvent (concreteBinding authority inputBridgeExact) :=
  ReceiptEvent.ofCompletion turnRequest completion

/-- The inhabited local receipt path exposes the same exact 384-row semantics.  The
nonzero controller pin identifies this Lean admission layer; it adds no privacy or proof
suite claim. -/
theorem receiptEvent_every_exact_integer_equation
    {Observer Policy Recipient Purpose AuthorizationContext CanonicalInput
      InputSourceWitness InputTargetWitness AuthorizationWitness OutputSourceWitness
      OutputTargetWitness ReleaseAuthorizationWitness DeclassificationAuthority Release : Type*}
    (authority : Authority Observer Policy Recipient Purpose AuthorizationContext
      CanonicalInput InputSourceWitness InputTargetWitness AuthorizationWitness
      OutputSourceWitness OutputTargetWitness ReleaseAuthorizationWitness
      DeclassificationAuthority Release)
    (inputBridgeExact : authority.inputBridge.name = bfvInputBridgeId)
    [DecidableEq Release]
    (event : ReceiptEvent (concreteBinding authority inputBridgeExact)) :
    event.evidence.clauseId = bfvClauseId /\
    bfvManifest.transcriptControllerDigest = bfvBufferControllerDigest /\
    (forall rowIndex,
      (event.outcome.output.representation.equations.equation rowIndex).numerator
          event.evidence.checked.witness.token.input.row =
        ((event.outcome.output.representation.equations.equation rowIndex).rns.value : Int) *
          (event.evidence.checked.witness.token.batch.rowCall rowIndex).witness.quotient.value) := by
  have accepted : Accepts
      (authority.declaration.statementOf event.privateRequest event.outcome)
      event.evidence.checked.witness := by
    simpa only [Authority.declaration] using event.evidence.checked.accepts
  rcases accepted with ⟨-, -, -, outputEq, -, -⟩
  have outputEq' : event.outcome.output.representation =
      event.evidence.checked.witness.outputRepresentation := by
    simpa only [PrivateComputationDeclaration.statementOf] using outputEq
  refine ⟨?_, rfl, ?_⟩
  · simpa [concreteBinding, bfvAdmissionClauseDecl, bfvClauseDecl] using
      event.evidence.clauseIdExact
  · intro rowIndex
    rw [outputEq']
    exact event.evidence.checked.witness.every_exact_integer_equation rowIndex

/-- info: 'Minidregg.Assurance.BfvNativeBufferAdmission.rowKernelCall_fullyWellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rowKernelCall_fullyWellFormed
/-- info: 'Minidregg.Assurance.BfvNativeBufferAdmission.RowAdmission.descriptorAcceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RowAdmission.descriptorAcceptance
/-- info: 'Minidregg.Assurance.BfvNativeBufferAdmission.RowAdmission.toCheckedRowBuffer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RowAdmission.toCheckedRowBuffer
/-- info: 'Minidregg.Assurance.BfvNativeBufferAdmission.BatchAdmission.every_exact_integer_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BatchAdmission.every_exact_integer_equation
/-- info: 'Minidregg.Assurance.BfvNativeBufferAdmission.bfvManifest_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bfvManifest_wellFormed
/-- info: 'Minidregg.Assurance.BfvNativeBufferAdmission.issueReceiptEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms issueReceiptEvent
/-- info: 'Minidregg.Assurance.BfvNativeBufferAdmission.receiptEvent_every_exact_integer_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms receiptEvent_every_exact_integer_equation

end Minidregg.Assurance.BfvNativeBufferAdmission
