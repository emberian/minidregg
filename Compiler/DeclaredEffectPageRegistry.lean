/-
# Compiler.DeclaredEffectPageRegistry -- effect-shard lifecycle

This is the heterogeneous-cell boundary for the bounded declared-effect page.
It pins one stable kind tag and V1 schema reference, installs the exact framed
cSHAKE materializer, round-trips a nonempty accepted-effect page, and executes
create/delete through `CellRegistry`.

The registry contains a representation shard, not the unbounded
`DeclaredTurn.effectSchema`.  Retirement prevents identifier resurrection;
physical stable-media installation and digest collision resistance remain the
existing explicit refinement ceilings.
-/
import Compiler.DeclaredEffectPageMaterializer
import Theory.CellSlot

namespace Minidregg.Compiler.DeclaredEffectPageRegistry

open Minidregg.Compiler.DeclaredEffectPageMaterializer
open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Theory
open Minidregg.Theory.CausalVersionDag
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

inductive Kind where
  | declaredEffectShard
  deriving DecidableEq, Repr

def Kind.tag : Kind -> UInt8
  | .declaredEffectShard => 5

def kindAtTag : UInt8 -> Option Kind
  | 5 => some .declaredEffectShard
  | _ => none

@[simp] theorem kindAtTag_tag (kind : Kind) :
    kindAtTag kind.tag = some kind := by
  cases kind
  rfl

/-- Schema id 91004 extends the three bounded page ids 91001--91003.  Version
one is the exact V1/capacity-4/modulus-16 frame in the materializer. -/
def effectShardSchemaRef : SchemaRef := ⟨⟨91004⟩, 1⟩

def schemaRef : Kind -> SchemaRef
  | .declaredEffectShard => effectShardSchemaRef

theorem schemaRef_injective : Function.Injective schemaRef := by
  intro left right _same
  cases left
  cases right
  rfl

def schema : Kind -> CellState.Schema.{0, 0, 0, 0}
  | .declaredEffectShard =>
      Minidregg.Compiler.DeclaredEffectPageMaterializer.schema

def materializer : (kind : Kind) -> Materializer (schema kind) Digest
  | .declaredEffectShard =>
      Minidregg.Compiler.DeclaredEffectPageMaterializer.materializer

def directoryRootCustomization : List UInt8 :=
  [76, 79, 79, 77, 46, 69, 70, 70, 69, 67, 84, 46, 80, 65, 71, 69,
    46, 82, 69, 71, 73, 83, 84, 82, 89, 46, 82, 79, 79, 84, 47, 118, 49]

def directoryRoot (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash directoryRootCustomization bytes).digest

theorem directory_payload_domains_distinct :
    directoryRootCustomization ≠
      Minidregg.Compiler.DeclaredEffectPageMaterializer.rootCustomization := by
  decide

def registry : TypeRegistry Digest where
  Kind := Kind
  tag := Kind.tag
  kindAtTag := kindAtTag
  kindAtTag_tag := kindAtTag_tag
  schemaRef := schemaRef
  schemaRef_injective := schemaRef_injective
  schema := schema
  materializer := materializer
  rootBytes := directoryRoot

@[simp] theorem registry_schemaRef :
    registry.schemaRef .declaredEffectShard = effectShardSchemaRef :=
  rfl

@[simp] theorem registry_materializer :
    registry.materializer .declaredEffectShard =
      Minidregg.Compiler.DeclaredEffectPageMaterializer.materializer :=
  rfl

def witnessCell :
    Materialized
      Minidregg.Compiler.DeclaredEffectPageMaterializer.materializer :=
  CellState.materialize
    Minidregg.Compiler.DeclaredEffectPageMaterializer.materializer
    (stateOfOption (some Witness.postPage))

def packedCell : PackedCell registry :=
  ⟨.declaredEffectShard, witnessCell⟩

@[simp] theorem packedCell_roundtrip :
    PackedCell.decode registry (PackedCell.bytes registry packedCell) =
      some packedCell :=
  PackedCell.decode_bytes registry packedCell

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
  expectedSchema := effectShardSchemaRef

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

/-- info: 'Minidregg.Compiler.DeclaredEffectPageRegistry.create_succeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms create_succeeds
/-- info: 'Minidregg.Compiler.DeclaredEffectPageRegistry.delete_succeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms delete_succeeds
/-- info: 'Minidregg.Compiler.DeclaredEffectPageRegistry.recreate_after_delete_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recreate_after_delete_rejected

end Minidregg.Compiler.DeclaredEffectPageRegistry
