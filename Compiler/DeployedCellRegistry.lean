/-
# Compiler.DeployedCellRegistry -- logical heterogeneous lifecycle exhibit

This registry is a scoped lifecycle witness.  The unified receiving path uses
`Compiler.CanonicalCellRegistry`; it does not select this witness as a
production registry configuration.

`Theory.CellSlot`'s deployed registry configuration is inhabited here with the
deployed cell materializers -- each one `StoreCodec` at its declared wire:

* declared effects (`DeclaredEffectCell.materializer`);
* credential authority (`CredentialAuthorityCell.materializer`);
* Hyperdocument content (`HyperdocumentCell.contentMaterializer`); and
* the append-only Hyperdocument event log (`HyperdocumentCell.eventMaterializer`).

Only the registry's own directory/slot root remains the byte-length root; it is
intentionally non-cryptographic, and `rootBytes_collision` exhibits that
ceiling below.  The lifecycle witnesses are logical only.  An actual store must
separately inhabit the existing `PersistenceRefinement` boundary.
-/
import Compiler.CredentialAuthorityCell
import Compiler.DeclaredEffectCell
import Compiler.HyperdocumentCell
import Theory.CellSlot
import Theory.DeployedMaterializerWitness

namespace Minidregg.Compiler.DeployedCellRegistry

open Minidregg.Theory
open Minidregg.Theory.CausalVersionDag
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Stable schema identities -/

/-- These values are wire pins.  Version 2 is the `DREGG/STORE` frame at each
kind's declared wire; version-1 cells (countability-selected witness codecs)
are retired; the declared-effect wire is version 3 since its key codec carries a
cell's field declaration (K-FIELD-CLOSURE, `state-key/tagged-v2`).  Schema id 14 is the document schema every hyperdocument witness
names (`HyperdocumentOperationIntent.documentSchema`); `documentSchema_deployed`
checks the two against each other. -/
def declaredEffectSchemaRef : SchemaRef := ⟨⟨11⟩, 3⟩
def credentialAuthoritySchemaRef : SchemaRef := ⟨⟨12⟩, 4⟩
def hyperdocumentContentSchemaRef : SchemaRef := ⟨⟨14⟩, 2⟩
def hyperdocumentEventSchemaRef : SchemaRef := ⟨⟨15⟩, 2⟩

/-- **Drift gate.**  The document schema every hyperdocument witness names (by
the one Theory constant) is the deployed content cell's schema ref.  Bumping
either the wire pin or the witnesses' schema without the other turns this red. -/
theorem documentSchema_deployed :
    HyperdocumentOperationIntent.documentSchema = hyperdocumentContentSchemaRef := rfl

theorem schemaRefs_nodup :
    [declaredEffectSchemaRef, credentialAuthoritySchemaRef,
      hyperdocumentContentSchemaRef, hyperdocumentEventSchemaRef].Nodup := by
  decide

/-! ## The exact three-kind `Theory` deployment configuration -/

def theorySchemaRef : DeployedKind -> SchemaRef
  | .declaredEffect => declaredEffectSchemaRef
  | .credentialAuthority => credentialAuthoritySchemaRef
  | .hyperdocument => hyperdocumentContentSchemaRef

theorem theorySchemaRef_injective : Function.Injective theorySchemaRef := by
  intro left right same
  cases left <;> cases right <;>
    simp [theorySchemaRef, declaredEffectSchemaRef,
      credentialAuthoritySchemaRef, hyperdocumentContentSchemaRef] at same ⊢

def theoryMaterializer :
    (kind : DeployedKind) -> Materializer (deployedLayout kind) Digest
  | .declaredEffect => DeclaredEffectCell.materializer
  | .credentialAuthority => CredentialAuthorityCell.materializer
  | .hyperdocument => HyperdocumentCell.contentMaterializer

/-- A concrete outside-home producer of the previously open
`DeployedRegistryConfig` carrier. -/
def theoryConfig : DeployedRegistryConfig Digest where
  schemaRef := theorySchemaRef
  schemaRef_injective := theorySchemaRef_injective
  materializer := theoryMaterializer
  rootBytes := Minidregg.Theory.DeployedMaterializerWitness.lengthRoot

/-- The exact generic registry induced by the three-kind Theory configuration. -/
def theoryRegistry : TypeRegistry Digest :=
  deployedRegistry theoryConfig

theorem theory_config_nonempty : Nonempty (DeployedRegistryConfig Digest) :=
  ⟨theoryConfig⟩

theorem theory_registry_nonempty : Nonempty (TypeRegistry Digest) :=
  ⟨theoryRegistry⟩

/-! ## The four-kind content plus event-log registry -/

/-- Stable one-byte registry tags.  Adding a constructor consumes a new tag
and requires a schema migration decision. -/
inductive Kind where
  | declaredEffect
  | credentialAuthority
  | hyperdocumentContent
  | hyperdocumentEvent
  deriving DecidableEq, Repr

def Kind.tag : Kind -> UInt8
  | .declaredEffect => 1
  | .credentialAuthority => 2
  | .hyperdocumentContent => 3
  | .hyperdocumentEvent => 4

def kindAtTag : UInt8 -> Option Kind
  | 1 => some .declaredEffect
  | 2 => some .credentialAuthority
  | 3 => some .hyperdocumentContent
  | 4 => some .hyperdocumentEvent
  | _ => none

@[simp] theorem kindAtTag_tag (kind : Kind) :
    kindAtTag kind.tag = some kind := by
  cases kind <;> rfl

def schemaRef : Kind -> SchemaRef
  | .declaredEffect => declaredEffectSchemaRef
  | .credentialAuthority => credentialAuthoritySchemaRef
  | .hyperdocumentContent => hyperdocumentContentSchemaRef
  | .hyperdocumentEvent => hyperdocumentEventSchemaRef

theorem schemaRef_injective : Function.Injective schemaRef := by
  intro left right same
  cases left <;> cases right <;>
    simp [schemaRef, declaredEffectSchemaRef, credentialAuthoritySchemaRef,
      hyperdocumentContentSchemaRef, hyperdocumentEventSchemaRef] at same ⊢

def layout : Kind -> Store.Layout.{0, 0, 0}
  | .declaredEffect => EffectDeclaration.effectLayout
  | .credentialAuthority => CredentialAuthorityState.layout
  | .hyperdocumentContent => Hyperdocument.layout
  | .hyperdocumentEvent => Minidregg.Kernel.HyperdocumentEventLog.Sparse.layout

def materializer : (kind : Kind) -> Materializer (layout kind) Digest
  | .declaredEffect => DeclaredEffectCell.materializer
  | .credentialAuthority => CredentialAuthorityCell.materializer
  | .hyperdocumentContent => HyperdocumentCell.contentMaterializer
  | .hyperdocumentEvent => HyperdocumentCell.eventMaterializer

/-- The full heterogeneous registry.  Its dependent payload type is selected
by `Kind`; no `Dynamic`, erased bytes, or cast participates in storage. -/
def registry : TypeRegistry Digest where
  Kind := Kind
  tag := Kind.tag
  kindAtTag := kindAtTag
  kindAtTag_tag := kindAtTag_tag
  schemaRef := schemaRef
  schemaRef_injective := schemaRef_injective
  layout := layout
  materializer := materializer
  rootBytes := Minidregg.Theory.DeployedMaterializerWitness.lengthRoot

theorem registry_nonempty : Nonempty (TypeRegistry Digest) :=
  ⟨registry⟩

@[simp] theorem registry_schemaRef (kind : Kind) :
    registry.schemaRef kind = schemaRef kind :=
  rfl

@[simp] theorem registry_tag (kind : Kind) :
    registry.tag kind = kind.tag :=
  rfl

/-! ## One exact packed cell for every registered schema -/

def packedCell : (kind : Kind) -> PackedCell registry
  | .declaredEffect =>
      ⟨.declaredEffect, CellState.materialize DeclaredEffectCell.materializer
        (DeclaredEffectCell.objectFields ⟨101⟩ 32)⟩
  | .credentialAuthority =>
      ⟨.credentialAuthority, CredentialAuthorityCell.Witness.ownerCell⟩
  | .hyperdocumentContent =>
      ⟨.hyperdocumentContent, CellState.materialize HyperdocumentCell.contentMaterializer
        (HyperdocumentCell.linksStore 17)⟩
  | .hyperdocumentEvent =>
      ⟨.hyperdocumentEvent, CellState.materialize HyperdocumentCell.eventMaterializer 0⟩

@[simp] theorem packedCell_kind (kind : Kind) :
    (packedCell kind).kind = kind := by
  cases kind <;> rfl

/-- Dependent decoding returns the exact registered payload without a cast. -/
@[simp] theorem packedCell_roundtrip (kind : Kind) :
    PackedCell.decode registry (PackedCell.bytes registry (packedCell kind)) =
      some (packedCell kind) :=
  PackedCell.decode_bytes registry (packedCell kind)

/-! ## Executable create/delete lifecycle -/

abbrev CellId := Nat

def cellId : Kind -> CellId
  | .declaredEffect => 101
  | .credentialAuthority => 102
  | .hyperdocumentContent => 103
  | .hyperdocumentEvent => 104

def createRequest (kind : Kind) :
    CreateRequest (CellId := CellId) registry where
  cellId := cellId kind
  expectedPreRoot := CellSlot.root registry .absent
  cell := packedCell kind

def emptyDirectory : Directory CellId registry :=
  Directory.empty registry

def afterCreate (kind : Kind) : Directory CellId registry :=
  Directory.insert registry emptyDirectory (cellId kind) (packedCell kind)

/-- Every registered schema crosses the actual executable create boundary. -/
theorem create_succeeds (kind : Kind) :
    create registry emptyDirectory (createRequest kind) =
      .ok (afterCreate kind) := by
  apply create_of_fresh registry
  · rfl
  · simp [emptyDirectory]
  · rfl

@[simp] theorem created_slot (kind : Kind) :
    (afterCreate kind).slots (cellId kind) = .present (packedCell kind) := by
  simp [afterCreate]

def deleteRequest (kind : Kind) :
    DeleteRequest (CellId := CellId) registry where
  cellId := cellId kind
  expectedPreRoot := CellSlot.root registry (.present (packedCell kind))
  expectedSchema := schemaRef kind

def afterDelete (kind : Kind) : Directory CellId registry :=
  Directory.retire registry (afterCreate kind) (cellId kind)

/-- Deletion checks the exact stable schema pin and exact current slot root. -/
theorem delete_succeeds (kind : Kind) :
    delete registry (afterCreate kind) (deleteRequest kind) =
      .ok (afterDelete kind) := by
  apply delete_of_exact registry (cell := packedCell kind)
  · exact created_slot kind
  · simp [deleteRequest]
  · rfl

@[simp] theorem deleted_slot_absent (kind : Kind) :
    (afterDelete kind).slots (cellId kind) = .absent := by
  simp [afterDelete]

@[simp] theorem deleted_identifier_used (kind : Kind) :
    cellId kind ∈ (afterDelete kind).used := by
  simp [afterDelete, afterCreate]

/-! ## Exact regression teeth through this registry -/

/-- A second create cannot overwrite the exact heterogeneous payload. -/
theorem duplicate_create_rejected (kind : Kind) :
    create registry (afterCreate kind) (createRequest kind) =
      .error RejectReason.duplicateCreate := by
  apply CellRegistry.duplicate_create_rejected registry
    (existing := packedCell kind)
  exact created_slot kind

/-- Retirement preserves allocation history, so the absent slot cannot be
resurrected under the same stable identifier. -/
theorem recreate_after_delete_rejected (kind : Kind) :
    create registry (afterDelete kind) (createRequest kind) =
      .error RejectReason.retiredIdentifier := by
  simpa [afterDelete, afterCreate] using
    (CellRegistry.recreate_after_retire_rejected registry emptyDirectory
      (createRequest kind) (createRequest kind) rfl)

@[simp] theorem absent_root_exact :
    CellSlot.root registry (.absent : CellSlot registry) = ⟨4⟩ :=
  rfl

def staleCreateRequest (kind : Kind) :
    CreateRequest (CellId := CellId) registry where
  cellId := cellId kind
  expectedPreRoot := ⟨0⟩
  cell := packedCell kind

/-- Even a genuinely fresh absent slot rejects a caller's stale root. -/
theorem stale_create_rejected (kind : Kind) :
    create registry emptyDirectory (staleCreateRequest kind) =
      .error RejectReason.stalePreRoot := by
  apply CellRegistry.stale_create_rejected registry
  · rfl
  · simp [emptyDirectory]
  · change (⟨0⟩ : Digest) ≠ CellSlot.root registry .absent
    rw [absent_root_exact]
    decide

theorem present_root_ne_zero (kind : Kind) :
    CellSlot.root registry (.present (packedCell kind)) ≠ ⟨0⟩ := by
  intro same
  have values := congrArg Digest.value same
  simp [CellSlot.root, registry,
    Minidregg.Theory.DeployedMaterializerWitness.lengthRoot,
    CellSlot.codec, CellSlot.bytes, PackedCell.codec, PackedCell.bytes] at values

def staleDeleteRequest (kind : Kind) :
    DeleteRequest (CellId := CellId) registry where
  cellId := cellId kind
  expectedPreRoot := ⟨0⟩
  expectedSchema := schemaRef kind

/-- A correct schema pin cannot rescue a stale current-slot root. -/
theorem stale_delete_rejected (kind : Kind) :
    delete registry (afterCreate kind) (staleDeleteRequest kind) =
      .error RejectReason.stalePreRoot := by
  apply CellRegistry.stale_delete_rejected registry
    (cell := packedCell kind)
  · exact created_slot kind
  · simp [staleDeleteRequest]
  · exact (present_root_ne_zero kind).symm

def wrongSchemaDeleteRequest :
    DeleteRequest (CellId := CellId) registry where
  cellId := cellId .hyperdocumentContent
  expectedPreRoot :=
    CellSlot.root registry (.present (packedCell .hyperdocumentContent))
  expectedSchema := credentialAuthoritySchemaRef

/-- Stable schema identities have teeth at deletion; a content payload cannot
be retired under the authority schema pin. -/
theorem schema_mismatch_delete_rejected :
    delete registry (afterCreate .hyperdocumentContent)
        wrongSchemaDeleteRequest =
      .error RejectReason.schemaMismatch := by
  simp [delete, wrongSchemaDeleteRequest, afterCreate, schemaRef, registry,
    hyperdocumentContentSchemaRef, credentialAuthoritySchemaRef]

/-! ## Explicit security and persistence ceilings -/

/-- The exhibited root function is intentionally not collision resistant,
even on one-byte inputs.  It proves carrier inhabitation and nothing more. -/
theorem rootBytes_collision :
    registry.rootBytes [0] = registry.rootBytes [1] ∧ [0] ≠ [1] := by
  constructor
  · rfl
  · decide

/-- A cryptographic deployment must separately discharge this premise for its
replacement registry root; this module supplies no inhabitant. -/
abbrev RootBindingCeiling : Prop := RootBindingPremise registry

/-- Likewise, logical lifecycle success does not imply bytes reached stable
media.  A physical implementation must separately inhabit this exact existing
boundary. -/
abbrev PersistenceCeiling (PhysicalState InstallError : Type) :=
  PersistenceRefinement (CellId := CellId)
    PhysicalState InstallError registry

/-! ## Axiom audit -/

/-- info: 'Minidregg.Compiler.DeployedCellRegistry.theory_config_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theory_config_nonempty
/-- info: 'Minidregg.Compiler.DeployedCellRegistry.registry_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms registry_nonempty
/-- info: 'Minidregg.Compiler.DeployedCellRegistry.create_succeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms create_succeeds
/-- info: 'Minidregg.Compiler.DeployedCellRegistry.delete_succeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms delete_succeeds
/-- info: 'Minidregg.Compiler.DeployedCellRegistry.recreate_after_delete_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recreate_after_delete_rejected
/-- info: 'Minidregg.Compiler.DeployedCellRegistry.rootBytes_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rootBytes_collision

end Minidregg.Compiler.DeployedCellRegistry
/-- info: 'Minidregg.Compiler.DeployedCellRegistry.documentSchema_deployed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DeployedCellRegistry.documentSchema_deployed
