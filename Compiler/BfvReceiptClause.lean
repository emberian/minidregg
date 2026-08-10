/-
# `Compiler.BfvReceiptClause` — proof-relevant compressed-BFV receipt clause

This module packages the already-landed BFV input-validity and signed-accumulator AIR
theorems as one receipt-admission clause.  Its public statement fixes one complete set of
collective-key/ciphertext/message-table/parameter/relation identifiers, one committed
witness reference, and the modulus-major family of all 384 deployed equations.

An accepted token contains no native acceptance callback.  Per-row native work may supply
only a candidate BabyBear wire buffer; the token additionally carries acceptance by the
existing emitted weighted AIR and the existing all-moduli scalar-product call.  The final
theorem therefore derives every exact signed integer equation from
`acceptedRowCall_accumulator_sound`.

The manifest declaration below is only a reserved clause pin.  Its proof-suite and
controller identifiers are explicitly unassigned, so registration does not claim that a
proof suite, PCS, serializer, or controller implementation exists.
-/
import Compiler.BfvSignedAccumulatorAir
import Compiler.SemanticManifest

namespace Minidregg.Compiler.BfvReceiptClause

open Minidregg.Compiler
open Minidregg.Compiler.BfvCompressedEquation
open Minidregg.Compiler.BfvAllModuliKernelCalls
open Minidregg.Compiler.BfvInputValidity
open Minidregg.Compiler.BfvSignedAccumulatorAir
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.BignumKernelABI
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-! ## Exact public statement -/

/-- One public BFV clause instance.  `input.reference.publicInputs` contains the collective
key, ciphertext set/rows, message table, BFV parameters, and relation identifiers;
`input.reference` is the unique committed layout/root identity. -/
structure PublicStatement where
  input : InputStatement
  equations : OwnerBatch

theorem PublicStatement.every_modulus_ordered (claim : PublicStatement)
    (rowIndex : Fin equationsPerOwner) :
    (claim.equations.equation rowIndex).rns = modulusAt rowIndex :=
  claim.equations.modulus_order rowIndex

/-- Concrete teeth that the public family contains each of the three deployed moduli in
the audited modulus-major order. -/
def q0Row : Fin equationsPerOwner := ⟨0, by norm_num [equationsPerOwner]⟩
def q1Row : Fin equationsPerOwner := ⟨128, by norm_num [equationsPerOwner]⟩
def q2Row : Fin equationsPerOwner := ⟨256, by norm_num [equationsPerOwner]⟩

theorem PublicStatement.all_three_moduli_present (claim : PublicStatement) :
    (claim.equations.equation q0Row).rns = .q0 /\
    (claim.equations.equation q1Row).rns = .q1 /\
    (claim.equations.equation q2Row).rns = .q2 := by
  constructor
  · simpa [q0Row, modulusAt, compressionRounds] using
      claim.equations.modulus_order q0Row
  constructor
  · simpa [q1Row, modulusAt, compressionRounds] using
      claim.equations.modulus_order q1Row
  · simpa [q2Row, modulusAt, compressionRounds] using
      claim.equations.modulus_order q2Row

/-! ## Per-row checked candidate buffer -/

/-- A candidate wire buffer together with the exact Lean checks needed by the two signed
accumulators.  The only data-facing field is `candidate`; every semantic conclusion comes
from `systemAccepts` for the already emitted AIR. -/
structure CheckedRowBuffer {statement : InputStatement}
    (input : ValidCommittedWitness statement) (rowIndex : Fin equationsPerOwner)
    (accepted : AcceptedRowCall statement input rowIndex) where
  width : Nat
  carryBits : Nat
  candidate : Nat -> BabyBear
  activeWire : Fin activeWidth -> Nat
  quotientWire : Nat
  left : WeightedSumWires Nat width limbBits carryBits
  right : WeightedSumWires Nat width limbBits carryBits
  positiveConstant_fits : positiveAccumulatorConstant accepted.equation <
    (2 ^ limbBits) ^ width
  negativeConstant_fits : negativeAccumulatorConstant accepted.equation <
    (2 ^ limbBits) ^ width
  positiveCoefficient_fits : forall j,
    positiveAccumulatorCoefficient accepted.equation j < (2 ^ limbBits) ^ width
  negativeCoefficient_fits : forall j,
    negativeAccumulatorCoefficient accepted.equation j < (2 ^ limbBits) ^ width
  active_matches : forall i,
    (candidate (activeWire i)).val = shiftedScalar input.row i
  quotient_matches : (candidate quotientWire).val =
    (accepted.assignment
      (scalarMulWires (productWidth (modulusAt rowIndex)) limbBits scalarBits).scalar).val
  shared_result : left.result = right.result
  left_accepts : systemAccepts candidate
    (weightedSumGadget (positiveAccumulatorConstant accepted.equation)
      (positiveAccumulatorCoefficient accepted.equation)
      (accumulatorScalarWire activeWire quotientWire) left)
  right_accepts : systemAccepts candidate
    (weightedSumGadget (negativeAccumulatorConstant accepted.equation)
      (negativeAccumulatorCoefficient accepted.equation)
      (accumulatorScalarWire activeWire quotientWire) right)
  left_noWrap : forall column,
    AirModularView.constDigit (2 ^ limbBits) width
        (positiveAccumulatorConstant accepted.equation) column +
      ((List.finRange (activeWidth + 1)).map fun j =>
        AirModularView.constDigit (2 ^ limbBits) width
            (positiveAccumulatorCoefficient accepted.equation j) column *
          (candidate (accumulatorScalarWire activeWire quotientWire j)).val).sum +
      (candidate (left.carry column.castSucc)).val < babyBearP
  left_result_noWrap : forall column,
    (candidate (left.result column)).val +
      2 ^ limbBits * (candidate (left.carry column.succ)).val < babyBearP
  right_noWrap : forall column,
    AirModularView.constDigit (2 ^ limbBits) width
        (negativeAccumulatorConstant accepted.equation) column +
      ((List.finRange (activeWidth + 1)).map fun j =>
        AirModularView.constDigit (2 ^ limbBits) width
            (negativeAccumulatorCoefficient accepted.equation j) column *
          (candidate (accumulatorScalarWire activeWire quotientWire j)).val).sum +
      (candidate (right.carry column.castSucc)).val < babyBearP
  right_result_noWrap : forall column,
    (candidate (right.result column)).val +
      2 ^ limbBits * (candidate (right.carry column.succ)).val < babyBearP
  carry_fits_field : 2 ^ carryBits <= babyBearP

theorem CheckedRowBuffer.exact_integer_equation {statement : InputStatement}
    {input : ValidCommittedWitness statement} {rowIndex : Fin equationsPerOwner}
    {accepted : AcceptedRowCall statement input rowIndex}
    (checked : CheckedRowBuffer input rowIndex accepted) :
    accepted.equation.numerator input.row =
      (accepted.equation.rns.value : Int) * accepted.witness.quotient.value := by
  exact acceptedRowCall_accumulator_sound input rowIndex accepted
    checked.positiveConstant_fits checked.negativeConstant_fits
    checked.positiveCoefficient_fits checked.negativeCoefficient_fits
    checked.candidate checked.activeWire checked.quotientWire checked.left checked.right
    checked.active_matches checked.quotient_matches checked.shared_result
    checked.left_accepts checked.right_accepts checked.left_noWrap
    checked.left_result_noWrap checked.right_noWrap checked.right_result_noWrap
    checked.carry_fits_field

/-! ## One proof-relevant token for all 384 rows -/

/-- Successful clause admission.  There is one committed witness, one accepted batch in
the fixed 384-row order, and one checked accumulator buffer per row. -/
structure AcceptedToken (claim : PublicStatement) where
  input : ValidCommittedWitness claim.input
  batch : AcceptedBatch claim.input input
  equation_eq : forall rowIndex,
    (batch.rowCall rowIndex).equation = claim.equations.equation rowIndex
  checked : forall rowIndex,
    CheckedRowBuffer input rowIndex (batch.rowCall rowIndex)

/-- Every accepted row is bound to the public statement's identifiers, the statement's
single committed witness reference, and its pinned equation. -/
theorem AcceptedToken.every_row_bound {claim : PublicStatement}
    (token : AcceptedToken claim) (rowIndex : Fin equationsPerOwner) :
    (token.batch.rowCall rowIndex).source.publicInputs =
        claim.input.reference.publicInputs /\
    (token.batch.rowCall rowIndex).rowReference = claim.input.reference /\
    (token.batch.rowCall rowIndex).callReference = claim.input.reference /\
    (token.batch.rowCall rowIndex).witness.row = token.input.row /\
    (token.batch.rowCall rowIndex).equation = claim.equations.equation rowIndex := by
  refine ⟨?_, (token.batch.rowCall rowIndex).row_reference_eq,
    (token.batch.rowCall rowIndex).call_reference_eq,
    (token.batch.rowCall rowIndex).witness_row_eq, token.equation_eq rowIndex⟩
  rw [(token.batch.rowCall rowIndex).source_eq]
  rfl

/-- Receipt-grade semantic consequence: all 384 rows are exact equations over `Int`, not
BabyBear or Ext6 congruences. -/
theorem AcceptedToken.every_exact_integer_equation {claim : PublicStatement}
    (token : AcceptedToken claim) (rowIndex : Fin equationsPerOwner) :
    (claim.equations.equation rowIndex).numerator token.input.row =
      ((claim.equations.equation rowIndex).rns.value : Int) *
        (token.batch.rowCall rowIndex).witness.quotient.value := by
  have exact := (token.checked rowIndex).exact_integer_equation
  simpa [token.equation_eq rowIndex] using exact

/-! ## Honest manifest pin and admission wrapper -/

def bfvClauseId : Digest := ⟨901⟩
def bfvRelationId : Digest := ⟨911⟩
def bfvResidueCarrierId : Digest := ⟨921⟩
def bfvStatementCodecReservation : Digest := ⟨931⟩
def unassignedProofCodecId : Digest := ⟨0⟩
def unassignedProofSuiteId : Digest := ⟨0⟩
def unassignedControllerDigest : Digest := ⟨0⟩

inductive ProofSuiteStatus
  | unassigned
deriving DecidableEq, Repr

/-- First-order clause pin.  Zero proof/controller pins are deliberate sentinels, not
claims of a proof system.  Admission below still requires the proof-relevant AIR token. -/
def bfvClauseDecl : DialectClauseDecl where
  clauseId := bfvClauseId
  relationId := bfvRelationId
  carrierProfileId := bfvResidueCarrierId
  statementCodecId := bfvStatementCodecReservation
  proofCodecId := unassignedProofCodecId
  proofSuiteId := unassignedProofSuiteId
  verifierControllerDigest := unassignedControllerDigest
  requiredBridgeIds := []

structure ClausePin where
  declaration : DialectClauseDecl
  proofSuiteStatus : ProofSuiteStatus

def bfvClausePin : ClausePin := ⟨bfvClauseDecl, .unassigned⟩

theorem bfvClausePin_unassigned :
    bfvClausePin.proofSuiteStatus = .unassigned /\
    bfvClausePin.declaration.proofCodecId = ⟨0⟩ /\
    bfvClausePin.declaration.proofSuiteId = ⟨0⟩ /\
    bfvClausePin.declaration.verifierControllerDigest = ⟨0⟩ := by
  decide

/-- Register the clause data without asserting that the resulting manifest is closed.
Closure additionally requires an eventual concrete statement codec, carrier profile, and
proof-suite/controller selection. -/
def register (manifest : Manifest) : Manifest :=
  { manifest with dialectClauses := bfvClauseDecl :: manifest.dialectClauses }

theorem lookup_register (manifest : Manifest) :
    (register manifest).lookupClause bfvClauseId = some bfvClauseDecl := by
  simp [register, Manifest.lookupClause, bfvClauseDecl, bfvClauseId]

/-- Minimal admission object suitable for a receipt layer: manifest registration plus the
proof-relevant semantic token.  No proof bytes or native verifier result appear here. -/
structure Admitted (manifest : Manifest) (claim : PublicStatement) where
  clause_registered : manifest.lookupClause bfvClauseId = some bfvClauseDecl
  token : AcceptedToken claim

theorem Admitted.every_exact_integer_equation {manifest : Manifest}
    {claim : PublicStatement} (admitted : Admitted manifest claim)
    (rowIndex : Fin equationsPerOwner) :
    (claim.equations.equation rowIndex).numerator admitted.token.input.row =
      ((claim.equations.equation rowIndex).rns.value : Int) *
        (admitted.token.batch.rowCall rowIndex).witness.quotient.value :=
  admitted.token.every_exact_integer_equation rowIndex

/-- info: 'Minidregg.Compiler.BfvReceiptClause.CheckedRowBuffer.exact_integer_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CheckedRowBuffer.exact_integer_equation
/-- info: 'Minidregg.Compiler.BfvReceiptClause.AcceptedToken.every_row_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AcceptedToken.every_row_bound
/-- info: 'Minidregg.Compiler.BfvReceiptClause.AcceptedToken.every_exact_integer_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AcceptedToken.every_exact_integer_equation
/-- info: 'Minidregg.Compiler.BfvReceiptClause.bfvClausePin_unassigned' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms bfvClausePin_unassigned
/-- info: 'Minidregg.Compiler.BfvReceiptClause.lookup_register' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms lookup_register
/-- info: 'Minidregg.Compiler.BfvReceiptClause.Admitted.every_exact_integer_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Admitted.every_exact_integer_equation

end Minidregg.Compiler.BfvReceiptClause
