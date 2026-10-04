/-
# Compiler.DeclaredEffectCellRegistry -- one-kind effect-cell lifecycle exhibit

The unified receiving path selects `Compiler.CanonicalCellRegistry`, whose
fixed semantic roles and final-state laws determine whether a declared cell is
an object, program, or account-metadata cell.  This one-kind exhibit does not
provide production kind dispatch or a second monetary store.

It is the heterogeneous-cell boundary for the declared-effect cell
(`Compiler.DeclaredEffectCell`): it pins one stable kind tag and a schema
reference, installs the store-codec materializer, round-trips a nonempty
32-field cell, and executes create/delete through `CellRegistry`.

Schema reference `91004` moved from version 1 (the four-slot, sixteen-shard
page frame `LOOM/EFFECT/PAGE`) to version 2 (the `DREGG/STORE` frame at the
declared-effect wire), and to version 4 when the wire's key codec carried both the
blinding and a cell's field declaration (`state-key/tagged-v3`), and to version 5
when the declaration gained its tail `fieldsFrom` (`state-key/tagged-v4`).  Version-1
through -4 cells refuse to decode (their layout digests differ).  Retirement
prevents identifier resurrection; physical stable-media installation and
digest collision resistance remain the existing explicit refinement ceilings.
-/
import Compiler.DeclaredEffectCell
import Theory.CellSlot

namespace Minidregg.Compiler.DeclaredEffectCellRegistry

open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Theory
open Minidregg.Theory.CausalVersionDag
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

inductive Kind where
  | declaredEffect
  deriving DecidableEq, Repr

def Kind.tag : Kind -> UInt8
  | .declaredEffect => 5

def kindAtTag : UInt8 -> Option Kind
  | 5 => some .declaredEffect
  | _ => none

@[simp] theorem kindAtTag_tag (kind : Kind) :
    kindAtTag kind.tag = some kind := by
  cases kind
  rfl

/-- Schema id 91004, version 4: the store frame at `DeclaredEffectCell.wire`. -/
def effectCellSchemaRef : SchemaRef := ⟨⟨91004⟩, 5⟩

def schemaRef : Kind -> SchemaRef
  | .declaredEffect => effectCellSchemaRef

theorem schemaRef_injective : Function.Injective schemaRef := by
  intro left right _same
  cases left
  cases right
  rfl

def layout : Kind -> Store.Layout.{0, 0, 0}
  | .declaredEffect => EffectDeclaration.effectLayout

def materializer : (kind : Kind) -> Materializer (layout kind) Digest
  | .declaredEffect => DeclaredEffectCell.materializer

/-- `DREGG.EFFECT.CELL.REGISTRY.ROOT/v1`. -/
def directoryRootCustomization : List UInt8 :=
  [68, 82, 69, 71, 71, 46, 69, 70, 70, 69, 67, 84, 46, 67, 69, 76, 76, 46,
    82, 69, 71, 73, 83, 84, 82, 89, 46, 82, 79, 79, 84, 47, 118, 49]

def directoryRoot (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash directoryRootCustomization bytes).digest

theorem directory_payload_domains_distinct :
    directoryRootCustomization ≠ StoreCodec.rootCustomization := by
  unfold StoreCodec.rootCustomization
  decide +kernel

def registry : TypeRegistry Digest where
  Kind := Kind
  tag := Kind.tag
  kindAtTag := kindAtTag
  kindAtTag_tag := kindAtTag_tag
  schemaRef := schemaRef
  schemaRef_injective := schemaRef_injective
  layout := layout
  materializer := materializer
  rootBytes := directoryRoot

@[simp] theorem registry_schemaRef :
    registry.schemaRef .declaredEffect = effectCellSchemaRef :=
  rfl

@[simp] theorem registry_materializer :
    registry.materializer .declaredEffect = DeclaredEffectCell.materializer :=
  rfl

/-- A 32-field object resource, as one cell. -/
def witnessCell : DeclaredEffectCell.Cell :=
  CellState.materialize DeclaredEffectCell.materializer
    (DeclaredEffectCell.objectFields ⟨204⟩ 32)

def packedCell : PackedCell registry :=
  ⟨.declaredEffect, witnessCell⟩

@[simp] theorem packedCell_roundtrip :
    PackedCell.decode registry (PackedCell.bytes registry packedCell) =
      some packedCell :=
  PackedCell.decode_bytes registry packedCell

theorem witnessCell_fields : witnessCell.logical.support.card = 32 :=
  (DeclaredEffectCell.resource_32_fields_roundtrip ⟨204⟩).1

/-! ## Executable create/delete/retire lifecycle -/

abbrev CellId := Nat

def cellId : CellId := 204

def emptyDirectory : Directory CellId registry :=
  Directory.empty registry

def createRequest : CreateRequest (CellId := CellId) registry where
  cellId := cellId
  expectedPreRoot := CellSlot.root registry .absent
  cell := packedCell

def afterCreate : Directory CellId registry :=
  Directory.insert registry emptyDirectory cellId packedCell

theorem create_succeeds :
    create registry emptyDirectory createRequest = .ok afterCreate := by
  apply create_of_fresh registry
  · rfl
  · simp [emptyDirectory]
  · rfl

@[simp] theorem created_slot :
    afterCreate.slots cellId = .present packedCell := by
  simp [afterCreate]

def deleteRequest : DeleteRequest (CellId := CellId) registry where
  cellId := cellId
  expectedPreRoot := CellSlot.root registry (.present packedCell)
  expectedSchema := effectCellSchemaRef

def afterDelete : Directory CellId registry :=
  Directory.retire registry afterCreate cellId

theorem delete_succeeds :
    delete registry afterCreate deleteRequest = .ok afterDelete := by
  apply delete_of_exact registry (cell := packedCell)
  · exact created_slot
  · rfl
  · rfl

@[simp] theorem deleted_slot_absent :
    afterDelete.slots cellId = .absent := by
  simp [afterDelete]

@[simp] theorem deleted_identifier_used :
    cellId ∈ afterDelete.used := by
  simp [afterDelete, afterCreate]

theorem duplicate_create_rejected :
    create registry afterCreate createRequest =
      .error RejectReason.duplicateCreate := by
  apply CellRegistry.duplicate_create_rejected registry
    (existing := packedCell)
  exact created_slot

theorem recreate_after_delete_rejected :
    create registry afterDelete createRequest =
      .error RejectReason.retiredIdentifier := by
  simpa [afterDelete, afterCreate] using
    (CellRegistry.recreate_after_retire_rejected registry emptyDirectory
      createRequest createRequest rfl)

/-- Logical lifecycle success is not a stable-media claim. -/
abbrev PersistenceCeiling (PhysicalState InstallError : Type) :=
  PersistenceRefinement (CellId := CellId)
    PhysicalState InstallError registry

/-- cSHAKE binding remains a cryptographic premise. -/
abbrev RootBindingCeiling : Prop := RootBindingPremise registry

/-! ## Axiom audit -/

/-- info: 'Minidregg.Compiler.DeclaredEffectCellRegistry.create_succeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms create_succeeds
/-- info: 'Minidregg.Compiler.DeclaredEffectCellRegistry.delete_succeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms delete_succeeds
/-- info: 'Minidregg.Compiler.DeclaredEffectCellRegistry.recreate_after_delete_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recreate_after_delete_rejected

end Minidregg.Compiler.DeclaredEffectCellRegistry
