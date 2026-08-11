/-
# `Assurance.BfvConcreteBatchAdmission` -- one checked 384-row BFV batch

`BfvNativeBufferAdmission` proves the important per-row theorem and defines the
abstract `BatchTemplate`/`BatchAdmission` carriers.  This module closes the
remaining construction seam:

* one `PreparedBatch` owns the committed input and all 384 exact runtime
  witnesses for that same owner row;
* `PreparedBatch.template` constructs the actual `RowTemplate` at every index
  in the modulus-major `Fin 384` family;
* one opaque, fallible batch runner returns only the dependent family of bounded
  row buffers;
* a finite Lean Boolean checks every row and is the only route to
  `BatchAdmission`.

The positive result is arithmetic admission, not proof-suite admission.  No
native correspondence, PCS, polynomial commitment, extraction, proof of
knowledge, zero knowledge, hiding, or FHE security theorem is introduced here.
-/
import Assurance.BfvNativeBufferAdmission

namespace Minidregg.Assurance.BfvConcreteBatchAdmission

open Minidregg.Assurance.BfvNativeBufferAdmission
open Minidregg.Compiler
open Minidregg.Compiler.BfvAllModuliKernelCalls
open Minidregg.Compiler.BfvCompressedEquation
open Minidregg.Compiler.BfvInputValidity
open Minidregg.Compiler.BfvReceiptClause
open Minidregg.Compiler.BfvSignedAccumulatorAir
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.SemanticManifest

set_option autoImplicit false

/-! ## The actual all-row template -/

/-- Twenty-three radix-64 limbs cover the signed-accumulator values carried by
the deployed descriptor.  The exact per-equation fit remains checked in
`RowTemplate.ResponseBounds`; this numeral does not assert a coefficient bound
that was not supplied by the generated equation. -/
def deployedAccumulatorWidth : Nat := 23

/-- The deployed coarse column budget uses 26-bit carries. -/
def deployedAccumulatorCarryBits : Nat := 26

theorem deployedCarry_fits_babyBear :
    2 ^ deployedAccumulatorCarryBits <= babyBearP := by
  norm_num [deployedAccumulatorCarryBits, babyBearP]

/-- Semantic inputs needed before native buffer generation.  This is not a
proof: every `RuntimeWitness` contains the exact integer BFV equation, and the
shared-row equation prevents 384 independently chosen owner rows. -/
structure PreparedBatch (claim : PublicStatement) where
  input : ValidCommittedWitness claim.input
  witnesses : claim.equations.Witness
  sharedRow : forall rowIndex,
    (witnesses.row rowIndex).row = input.row

namespace PreparedBatch

/-- The concrete row template at an arbitrary one of the 384 indices.  All
identity fields are authored from the one public claim, never by the native
runner. -/
def rowTemplate {claim : PublicStatement} (prepared : PreparedBatch claim)
    (rowIndex : Fin equationsPerOwner) :
    RowTemplate claim.input prepared.input rowIndex where
  source := claim.input.equationSource rowIndex
  source_eq := rfl
  rowReference := claim.input.reference
  callReference := claim.input.reference
  row_reference_eq := rfl
  call_reference_eq := rfl
  equation := claim.equations.equation rowIndex
  equation_modulus := claim.equations.modulus_order rowIndex
  witness := prepared.witnesses.row rowIndex
  witness_row_eq := prepared.sharedRow rowIndex
  width := deployedAccumulatorWidth
  carryBits := deployedAccumulatorCarryBits

/-- The previously abstract batch template is now populated at every `Fin 384`
index. -/
def template {claim : PublicStatement} (prepared : PreparedBatch claim) :
    BatchTemplate claim where
  input := prepared.input
  row := prepared.rowTemplate
  equation_eq := fun _ => rfl

@[simp] theorem rowTemplate_equation {claim : PublicStatement}
    (prepared : PreparedBatch claim) (rowIndex : Fin equationsPerOwner) :
    (prepared.rowTemplate rowIndex).equation =
      claim.equations.equation rowIndex := rfl

@[simp] theorem rowTemplate_source {claim : PublicStatement}
    (prepared : PreparedBatch claim) (rowIndex : Fin equationsPerOwner) :
    (prepared.rowTemplate rowIndex).source =
      claim.input.equationSource rowIndex := rfl

theorem rowTemplate_identity_exact {claim : PublicStatement}
    (prepared : PreparedBatch claim) (rowIndex : Fin equationsPerOwner) :
    (prepared.rowTemplate rowIndex).rowReference = claim.input.reference /\
    (prepared.rowTemplate rowIndex).callReference = claim.input.reference /\
    (prepared.rowTemplate rowIndex).source.publicInputs =
      claim.input.reference.publicInputs /\
    (prepared.rowTemplate rowIndex).source.rowIndex = rowIndex := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem rowTemplate_uses_shared_row {claim : PublicStatement}
    (prepared : PreparedBatch claim) (rowIndex : Fin equationsPerOwner) :
    (prepared.rowTemplate rowIndex).witness.row = prepared.input.row :=
  prepared.sharedRow rowIndex

/-- Wrong-row teeth: an alleged generated witness with a distinct owner row
contradicts the load-bearing shared-row premise before any buffer is run. -/
theorem wrong_row_refuted {claim : PublicStatement}
    (prepared : PreparedBatch claim) (rowIndex : Fin equationsPerOwner)
    (wrong : (prepared.witnesses.row rowIndex).row ≠ prepared.input.row) : False :=
  wrong (prepared.sharedRow rowIndex)

/-- Identity teeth: a foreign witness reference cannot be the reference of a
concrete generated row. -/
theorem foreign_reference_refuted {claim : PublicStatement}
    (prepared : PreparedBatch claim) (rowIndex : Fin equationsPerOwner)
    (foreign : WitnessReference) (different : foreign ≠ claim.input.reference) :
    foreign ≠ (prepared.rowTemplate rowIndex).rowReference := by
  simpa using different

end PreparedBatch

/-- The finite controller visits exactly the deployed 384 row indices. -/
def deployedRowIndices : List (Fin equationsPerOwner) :=
  List.finRange equationsPerOwner

theorem deployedRowIndices_length : deployedRowIndices.length = 384 := by
  simp [deployedRowIndices, equationsPerOwner]

theorem deployedRowIndices_complete (rowIndex : Fin equationsPerOwner) :
    rowIndex ∈ deployedRowIndices := by
  simp [deployedRowIndices]

/-! ## One opaque/fallible all-row buffer boundary -/

/-- Native output for a batch is only one bounded buffer at each Lean-selected
row instruction.  The dependent result type prevents changing the instruction
family or returning an acceptance bit. -/
structure NativeBatchResponse {claim : PublicStatement}
    (template : BatchTemplate claim) where
  row : forall rowIndex,
    KernelResponse (template.row rowIndex).instruction

/-- The opaque runner sees the Lean-authored template and can only fail or
return the dependent buffer family.  It cannot construct `RowAdmission` or
`BatchAdmission`. -/
abbrev FallibleBatchRunner (Error : Type) (claim : PublicStatement) :=
  (template : BatchTemplate claim) ->
    Except Error (NativeBatchResponse template)

/-- Executable row check used by the finite batch check. -/
def rowAdmittedCheck {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (manifest : Manifest) (template : RowTemplate statement input rowIndex)
    (response : KernelResponse template.instruction) : Bool :=
  match checkInstruction manifest template.instruction response with
  | .inl _ => false
  | .inr _ => template.responseValidCheck response

/-- A true row Boolean constructs the proof-relevant admission.  The native
buffer contributes no proof field. -/
def rowAdmissionOfCheck {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (manifest : Manifest) (template : RowTemplate statement input rowIndex)
    (response : KernelResponse template.instruction)
    (checked : rowAdmittedCheck manifest template response = true) :
    RowAdmission manifest template response := by
  unfold rowAdmittedCheck at checked
  split at checked
  next failure rejected => simp at checked
  next certified accepted =>
    exact ⟨certified, checked⟩

/-- Finite conjunction of all 384 row checks. -/
def NativeBatchResponse.admittedCheck {claim : PublicStatement}
    {template : BatchTemplate claim} (response : NativeBatchResponse template)
    (manifest : Manifest) : Bool :=
  deployedRowIndices.all fun rowIndex =>
    rowAdmittedCheck manifest (template.row rowIndex) (response.row rowIndex)

theorem NativeBatchResponse.admittedCheck_eq_true_iff
    {claim : PublicStatement} {template : BatchTemplate claim}
    (response : NativeBatchResponse template) (manifest : Manifest) :
    response.admittedCheck manifest = true <->
      forall rowIndex,
        rowAdmittedCheck manifest (template.row rowIndex)
          (response.row rowIndex) = true := by
  simp [NativeBatchResponse.admittedCheck, deployedRowIndices]

inductive BatchOutcome (Error : Type) (manifest : Manifest)
    {claim : PublicStatement} (template : BatchTemplate claim)
  | blocked (error : Error)
  | rejected
  | admitted (token : BatchAdmission manifest claim template)

def BatchOutcome.IsAdmitted {Error : Type} {manifest : Manifest}
    {claim : PublicStatement} {template : BatchTemplate claim} :
    BatchOutcome Error manifest template -> Prop
  | .blocked _ => False
  | .rejected => False
  | .admitted _ => True

/-- One fallible native call followed by the finite Lean conjunction.  Only
the true branch constructs `BatchAdmission`. -/
def runBatch {Error : Type} (manifest : Manifest) {claim : PublicStatement}
    (template : BatchTemplate claim) (runner : FallibleBatchRunner Error claim) :
    BatchOutcome Error manifest template :=
  match runner template with
  | .error error => .blocked error
  | .ok response =>
      if checked : response.admittedCheck manifest = true then
        .admitted
          { response := response.row
            row := fun rowIndex =>
              rowAdmissionOfCheck manifest (template.row rowIndex)
                (response.row rowIndex)
                ((response.admittedCheck_eq_true_iff manifest).mp checked rowIndex) }
      else .rejected

theorem native_failure_blocks {Error : Type} (manifest : Manifest)
    {claim : PublicStatement} (template : BatchTemplate claim)
    (runner : FallibleBatchRunner Error claim) (error : Error)
    (failed : runner template = .error error) :
    runBatch manifest template runner = .blocked error := by
  unfold runBatch
  rw [failed]

theorem checked_buffers_reach_admission {Error : Type} (manifest : Manifest)
    {claim : PublicStatement} (template : BatchTemplate claim)
    (runner : FallibleBatchRunner Error claim)
    (response : NativeBatchResponse template)
    (returned : runner template = .ok response)
    (checked : response.admittedCheck manifest = true) :
    (runBatch manifest template runner).IsAdmitted := by
  unfold runBatch
  rw [returned]
  simp [checked, BatchOutcome.IsAdmitted]

/-! ## Rejection teeth -/

theorem some_row_invalid_rejects {Error : Type} (manifest : Manifest)
    {claim : PublicStatement} (template : BatchTemplate claim)
    (runner : FallibleBatchRunner Error claim)
    (response : NativeBatchResponse template)
    (returned : runner template = .ok response)
    (rowIndex : Fin equationsPerOwner)
    (invalid : rowAdmittedCheck manifest (template.row rowIndex)
      (response.row rowIndex) = false) :
    runBatch manifest template runner = .rejected := by
  unfold runBatch
  rw [returned]
  have notAll : response.admittedCheck manifest ≠ true := by
    intro all
    have atRow := (response.admittedCheck_eq_true_iff manifest).mp all rowIndex
    rw [invalid] at atRow
    contradiction
  have checkFalse : response.admittedCheck manifest = false :=
    Bool.eq_false_of_not_eq_true notAll
  simp [checkFalse]

/-- An emitted-descriptor failure can never pass the row Boolean. -/
theorem descriptor_failure_row_invalid {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (manifest : Manifest) (template : RowTemplate statement input rowIndex)
    (response : KernelResponse template.instruction)
    (failure : ¬ template.instruction.call.Accepts response.totalWires) :
    rowAdmittedCheck manifest template response = false := by
  unfold rowAdmittedCheck
  split
  next rejected => rfl
  next certified accepted =>
    exact (failure certified.descriptorAcceptance).elim

/-- Any failed cross-buffer or no-wrap conjunct forces rejection, even if the
generic emitted descriptor itself happened to accept the field cells. -/
theorem response_bounds_failure_row_invalid {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (manifest : Manifest) (template : RowTemplate statement input rowIndex)
    (response : KernelResponse template.instruction)
    (failure : ¬ template.ResponseBounds response) :
    rowAdmittedCheck manifest template response = false := by
  unfold rowAdmittedCheck
  split
  next rejected => rfl
  next certified accepted =>
    cases valid : template.responseValidCheck response with
    | false => rfl
    | true =>
        have semantic :=
          (template.responseValidCheck_eq_true_iff response).mp valid
        exact (failure semantic.2.2).elim

/-- Explicit no-wrap tooth for a corrupt left-accumulator column. -/
theorem left_noWrap_failure_row_invalid {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (manifest : Manifest) (template : RowTemplate statement input rowIndex)
    (response : KernelResponse template.instruction)
    (column : Fin template.width)
    (failure : ¬(
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
          ((template.natLeftWires).carry column.castSucc)).val < babyBearP)) :
    rowAdmittedCheck manifest template response = false := by
  apply response_bounds_failure_row_invalid manifest template response
  intro bounds
  rcases bounds with ⟨_, _, _, _, _, _, leftNoWrap, _, _, _, _⟩
  exact failure (leftNoWrap column)

/-- Explicit wrong-row-buffer tooth: a mismatching active cell forces rejection
for the row at which that buffer was supplied. -/
theorem active_row_mismatch_invalid {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    (manifest : Manifest) (template : RowTemplate statement input rowIndex)
    (response : KernelResponse template.instruction)
    (activeIndex : Fin activeWidth)
    (mismatch :
      (template.candidate response
        (rowActiveWire rowIndex template.width template.carryBits activeIndex).val).val ≠
          shiftedScalar input.row activeIndex) :
    rowAdmittedCheck manifest template response = false := by
  apply response_bounds_failure_row_invalid manifest template response
  intro bounds
  exact mismatch (bounds.1 activeIndex)

/-! ## Successful all-row semantics -/

theorem BatchAdmission.every_row_identity_exact {manifest : Manifest}
    {claim : PublicStatement} {template : BatchTemplate claim}
    (admission : BatchAdmission manifest claim template)
    (rowIndex : Fin equationsPerOwner) :
    ((admission.acceptedToken).batch.rowCall rowIndex).rowReference =
        claim.input.reference /\
    ((admission.acceptedToken).batch.rowCall rowIndex).callReference =
        claim.input.reference /\
    ((admission.acceptedToken).batch.rowCall rowIndex).equation =
        claim.equations.equation rowIndex := by
  have bound := admission.acceptedToken.every_row_bound rowIndex
  exact ⟨bound.2.1, bound.2.2.1, bound.2.2.2.2⟩

/-- The accepted result covers the exact finite family, not one selected row. -/
theorem BatchAdmission.all_384_exact {manifest : Manifest}
    {claim : PublicStatement} {template : BatchTemplate claim}
    (admission : BatchAdmission manifest claim template) :
    forall rowIndex : Fin 384,
      (claim.equations.equation
          (Fin.cast (by simp [equationsPerOwner]) rowIndex)).numerator
          template.input.row =
        ((claim.equations.equation
          (Fin.cast (by simp [equationsPerOwner]) rowIndex)).rns.value : Int) *
          ((admission.acceptedToken).batch.rowCall
            (Fin.cast (by simp [equationsPerOwner]) rowIndex)).witness.quotient.value := by
  intro rowIndex
  exact admission.every_exact_integer_equation
    (Fin.cast (by simp [equationsPerOwner]) rowIndex)

/-- info: 'Minidregg.Assurance.BfvConcreteBatchAdmission.PreparedBatch.template' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedBatch.template
/-- info: 'Minidregg.Assurance.BfvConcreteBatchAdmission.rowAdmissionOfCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rowAdmissionOfCheck
/-- info: 'Minidregg.Assurance.BfvConcreteBatchAdmission.runBatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runBatch
/-- info: 'Minidregg.Assurance.BfvConcreteBatchAdmission.BatchAdmission.all_384_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BatchAdmission.all_384_exact

end Minidregg.Assurance.BfvConcreteBatchAdmission
