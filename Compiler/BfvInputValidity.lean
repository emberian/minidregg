/-
# `Compiler.BfvInputValidity` — one committed input behind every BFV row

The deployed owner vector is shared by three logically distinct checks:

* selector Booleanity/one-hotness and the `(kind, quantity)` table index;
* the nine deterministic semantic slots and the three bounded short vectors;
* 384 exact compressed equations and their modulus-major scalar-product calls.

This module states that join without introducing a new constraint language.  Public input
identifiers name the collective key, four-ciphertext set, deterministic message table, BFV
parameters, and their relation digest.  A witness reference additionally names the exact
distributed layout and owner commitment root.  Every accepted equation row and emitted
call is required to carry that same reference and the same `OwnerRow`.

Hash computation, byte parsing, commitment binding, and coefficient generation remain
outside this statement.  The theorem here is the identity/composition edge: once those
identifiers are supplied, no accepted row may silently switch tables, keys, ciphertexts,
layouts, roots, owners, or private vectors.
-/
import Compiler.BfvAllModuliKernelCalls

namespace Minidregg.Compiler.BfvInputValidity

open scoped BigOperators
open Minidregg.Compiler
open Minidregg.Compiler.BignumKernelABI
open Minidregg.Compiler.BfvCompressedEquation
open Minidregg.Compiler.BfvAllModuliKernelCalls

set_option autoImplicit false

/-! ## Public and committed identities -/

/-- Canonical 32-byte identifier shape. -/
abbrev Digest32 := Fin 32 -> Fin 256

/-- The public objects from which the deployed coefficient family is generated.  These are
identifiers, not a claim about a particular hash implementation. -/
structure PublicInputIdentifiers where
  collectiveKeyId : Digest32
  ciphertextSetId : Digest32
  ciphertextRowId : Fin ownerCount -> Digest32
  messageTableId : Digest32
  bfvParametersId : Digest32
  relationDigest : Digest32
deriving DecidableEq

/-- Exact transcript layout identifier in `private_book_distributed_inputs.rs`. -/
def deployedLayoutId : String :=
  "FHEGG-PB-BFV-DISTRIBUTED-BASE-INPUT-N4K4-V4-SHORT"

/-- The exact relation codec identifier mixed into the public relation digest. -/
def deployedRelationCodecId : String := "FHEGG-PRIVATE-BOOK-BFV-N4K4-V1!!"

/-- One owner vector's stable reference.  `rootId` names its vector commitment; it is
distinct from the eight root-blinding field lanes inside the vector. -/
structure WitnessReference where
  publicInputs : PublicInputIdentifiers
  sessionId : Digest32
  challengeId : Digest32
  owner : Fin ownerCount
  layoutId : String
  rootId : Digest32
deriving DecidableEq

structure InputStatement where
  reference : WitnessReference
  layout_is_deployed : reference.layoutId = deployedLayoutId
  relationCodecId : String
  relation_codec_is_deployed : relationCodecId = deployedRelationCodecId

/-! ## Exact finite-table semantics of the derived owner prefix -/

def kindCount : Nat := 8
def quantityCount : Nat := 16
def priceCount : Nat := 4

def optionIndex (kind : Fin kindCount) (quantity : Fin quantityCount) :
    Fin optionCount :=
  ⟨kind.val * quantityCount + quantity.val, by
    have hk := kind.isLt
    have hq := quantity.isLt
    norm_num [kindCount, quantityCount, optionCount] at hk hq ⊢
    omega⟩

/-- The exact nine-slot table: four demand slots, four supply slots, then
`kind + 8*quantity`. -/
def semanticSlotValue (kind : Fin kindCount) (quantity : Fin quantityCount)
    (slot : Fin semanticWidth) : Nat :=
  if slot.val < 2 * priceCount then
    if kind.val < priceCount then
      if slot.val <= kind.val then quantity.val else 0
    else
      if kind.val <= slot.val then quantity.val else 0
  else
    kind.val + kindCount * quantity.val

/-- One committed owner vector satisfying the selector/table/range layer. -/
structure ValidCommittedWitness (statement : InputStatement) where
  reference : WitnessReference
  reference_eq : reference = statement.reference
  row : OwnerRow
  rowRange : row.RuntimeRange
  kind : Fin kindCount
  quantity : Fin quantityCount
  kind_eq : row.kind = kind.val
  quantity_eq : row.quantity = quantity.val
  selector_eq : forall option,
    row.selector option = if option = optionIndex kind quantity then 1 else 0
  semantic_eq : forall slot,
    row.semantic slot = semanticSlotValue kind quantity slot

namespace ValidCommittedWitness

theorem selector_boolean {statement : InputStatement}
    (input : ValidCommittedWitness statement) (option : Fin optionCount) :
    input.row.selector option = 0 \/ input.row.selector option = 1 := by
  rw [input.selector_eq]
  split <;> simp

theorem selector_oneHot {statement : InputStatement}
    (input : ValidCommittedWitness statement) :
    (∑ option, input.row.selector option) = 1 := by
  simp_rw [input.selector_eq]
  simp

theorem kind_quantity_consistent {statement : InputStatement}
    (input : ValidCommittedWitness statement) :
    input.row.kind = input.kind.val /\
    input.row.quantity = input.quantity.val :=
  ⟨input.kind_eq, input.quantity_eq⟩

theorem semantic_slots_consistent {statement : InputStatement}
    (input : ValidCommittedWitness statement) (slot : Fin semanticWidth) :
    input.row.semantic slot = semanticSlotValue input.kind input.quantity slot :=
  input.semantic_eq slot

theorem shorts_bounded {statement : InputStatement}
    (input : ValidCommittedWitness statement) (j : Fin degree) :
    (-32 <= input.row.u j /\ input.row.u j < 32) /\
    (-32 <= input.row.e1 j /\ input.row.e1 j < 32) /\
    (-32 <= input.row.e2 j /\ input.row.e2 j < 32) :=
  ⟨input.rowRange.u_short j, input.rowRange.e1_short j,
    input.rowRange.e2_short j⟩

theorem has_statement_reference {statement : InputStatement}
    (input : ValidCommittedWitness statement) : input.reference = statement.reference :=
  input.reference_eq

end ValidCommittedWitness

/-! ## One accepted equation row and its emitted call -/

/-- Public provenance carried by a generated equation row. -/
structure EquationSource where
  publicInputs : PublicInputIdentifiers
  sessionId : Digest32
  challengeId : Digest32
  owner : Fin ownerCount
  rowIndex : Fin equationsPerOwner
deriving DecidableEq

def InputStatement.equationSource (statement : InputStatement)
    (rowIndex : Fin equationsPerOwner) : EquationSource where
  publicInputs := statement.reference.publicInputs
  sessionId := statement.reference.sessionId
  challengeId := statement.reference.challengeId
  owner := statement.reference.owner
  rowIndex := rowIndex

/-- One exact row, its shifted quotient product call, and both identity references. -/
structure AcceptedRowCall (statement : InputStatement)
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
  assignment : Fin
    (scalarMulWireCount (productWidth (modulusAt rowIndex)) limbBits scalarBits) -> BabyBear
  callAccepted : exists wireValues : Nat -> BabyBear,
    (forall j, wireValues j.val = assignment j) /\
    (kernelCallFor (modulusAt rowIndex)).Accepts wireValues
  scalar_matches :
    (assignment
      (scalarMulWires (productWidth (modulusAt rowIndex)) limbBits scalarBits).scalar).val =
      witness.quotient.encoded.toNat

/-- All 384 rows are checked against one validity object, not 384 independently chosen
owner vectors. -/
structure AcceptedBatch (statement : InputStatement)
    (input : ValidCommittedWitness statement) where
  rowCall : forall rowIndex : Fin equationsPerOwner, AcceptedRowCall statement input rowIndex

namespace AcceptedBatch

/-- Every equation witness is literally the same committed owner row. -/
theorem every_row_uses_shared_witness {statement : InputStatement}
    {input : ValidCommittedWitness statement} (batch : AcceptedBatch statement input)
    (rowIndex : Fin equationsPerOwner) :
    (batch.rowCall rowIndex).witness.row = input.row :=
  (batch.rowCall rowIndex).witness_row_eq

/-- Every row and call carry the statement's exact layout/root reference. -/
theorem every_row_call_uses_shared_identity {statement : InputStatement}
    {input : ValidCommittedWitness statement} (batch : AcceptedBatch statement input)
    (rowIndex : Fin equationsPerOwner) :
    (batch.rowCall rowIndex).rowReference.layoutId = statement.reference.layoutId /\
    (batch.rowCall rowIndex).callReference.layoutId = statement.reference.layoutId /\
    (batch.rowCall rowIndex).rowReference.rootId = statement.reference.rootId /\
    (batch.rowCall rowIndex).callReference.rootId = statement.reference.rootId := by
  rw [(batch.rowCall rowIndex).row_reference_eq,
    (batch.rowCall rowIndex).call_reference_eq]
  simp

/-- Pairwise form: any two accepted rows/calls have the same complete witness reference. -/
theorem row_call_references_pairwise_equal {statement : InputStatement}
    {input : ValidCommittedWitness statement} (batch : AcceptedBatch statement input)
    (i j : Fin equationsPerOwner) :
    (batch.rowCall i).rowReference = (batch.rowCall j).rowReference /\
    (batch.rowCall i).callReference = (batch.rowCall j).callReference /\
    (batch.rowCall i).rowReference = (batch.rowCall j).callReference := by
  rw [(batch.rowCall i).row_reference_eq, (batch.rowCall j).row_reference_eq,
    (batch.rowCall i).call_reference_eq, (batch.rowCall j).call_reference_eq]
  simp

/-- Consequently every generated row names the same collective key, ciphertext set,
message table, parameter set, and relation digest. -/
theorem every_row_uses_statement_public_inputs {statement : InputStatement}
    {input : ValidCommittedWitness statement} (batch : AcceptedBatch statement input)
    (rowIndex : Fin equationsPerOwner) :
    (batch.rowCall rowIndex).source.publicInputs.collectiveKeyId =
        statement.reference.publicInputs.collectiveKeyId /\
    (batch.rowCall rowIndex).source.publicInputs.ciphertextSetId =
        statement.reference.publicInputs.ciphertextSetId /\
    (batch.rowCall rowIndex).source.publicInputs.ciphertextRowId =
        statement.reference.publicInputs.ciphertextRowId /\
    (batch.rowCall rowIndex).source.publicInputs.messageTableId =
        statement.reference.publicInputs.messageTableId /\
    (batch.rowCall rowIndex).source.publicInputs.bfvParametersId =
        statement.reference.publicInputs.bfvParametersId /\
    (batch.rowCall rowIndex).source.publicInputs.relationDigest =
        statement.reference.publicInputs.relationDigest := by
  rw [(batch.rowCall rowIndex).source_eq]
  simp [InputStatement.equationSource]

/-- Accepted call means the existing nested descriptor holds; identity metadata adds no
second acceptance relation. -/
theorem every_call_is_descriptorHolds {statement : InputStatement}
    {input : ValidCommittedWitness statement} (batch : AcceptedBatch statement input)
    (rowIndex : Fin equationsPerOwner) :
    exists wireValues : Nat -> BabyBear,
      (forall j, wireValues j.val = (batch.rowCall rowIndex).assignment j) /\
      descriptorHolds (kernelCallFor (modulusAt rowIndex)).descriptor wireValues := by
  simpa [KernelCall.Accepts] using (batch.rowCall rowIndex).callAccepted

/-- Each equation and call use the common modulus-major row order. -/
theorem every_row_uses_ordered_modulus {statement : InputStatement}
    {input : ValidCommittedWitness statement} (batch : AcceptedBatch statement input)
    (rowIndex : Fin equationsPerOwner) :
    (batch.rowCall rowIndex).equation.rns = modulusAt rowIndex :=
  (batch.rowCall rowIndex).equation_modulus

end AcceptedBatch

/-! ## Small exact table teeth -/

example : (optionIndex ⟨7, by norm_num [kindCount]⟩
    ⟨15, by norm_num [quantityCount]⟩).val = 127 := by decide

example : semanticSlotValue ⟨2, by norm_num [kindCount]⟩
    ⟨5, by norm_num [quantityCount]⟩ =
    ![5, 5, 5, 0, 0, 0, 0, 0, 42] := by decide

example : semanticSlotValue ⟨6, by norm_num [kindCount]⟩
    ⟨3, by norm_num [quantityCount]⟩ =
    ![0, 0, 0, 0, 0, 0, 3, 3, 30] := by decide

/-- info: 'Minidregg.Compiler.BfvInputValidity.ValidCommittedWitness.selector_boolean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ValidCommittedWitness.selector_boolean
/-- info: 'Minidregg.Compiler.BfvInputValidity.ValidCommittedWitness.selector_oneHot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ValidCommittedWitness.selector_oneHot
/-- info: 'Minidregg.Compiler.BfvInputValidity.ValidCommittedWitness.shorts_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ValidCommittedWitness.shorts_bounded
/-- info: 'Minidregg.Compiler.BfvInputValidity.AcceptedBatch.every_row_uses_shared_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AcceptedBatch.every_row_uses_shared_witness
/-- info: 'Minidregg.Compiler.BfvInputValidity.AcceptedBatch.every_row_call_uses_shared_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AcceptedBatch.every_row_call_uses_shared_identity
/-- info: 'Minidregg.Compiler.BfvInputValidity.AcceptedBatch.every_row_uses_statement_public_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AcceptedBatch.every_row_uses_statement_public_inputs
/-- info: 'Minidregg.Compiler.BfvInputValidity.AcceptedBatch.every_call_is_descriptorHolds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AcceptedBatch.every_call_is_descriptorHolds

end Minidregg.Compiler.BfvInputValidity
