/-
# Compiler.DeployedCellRegistry -- one concrete heterogeneous cell registry

`Theory.CellSlot` deliberately leaves its deployed registry configuration
uninhabited: a registry must choose exact schemas, lawful materializers, stable
wire tags, and stable schema identities.  This module makes that choice for the
four cell families which currently cross the sparse-state boundary:

* declared effects;
* credential authority;
* Hyperdocument content; and
* the append-only Hyperdocument event log.

The materializers are the existing exhibited materializers.  In particular,
this file does not invent a codec, cast a dependent payload, or pretend that a
bounded page codec can round-trip an unbounded sparse schema.  Their shared
byte-length root is intentionally non-cryptographic; `rootBytes_collision`
exhibits that ceiling below.  The lifecycle witnesses are logical only.  An
actual store must separately inhabit the existing `PersistenceRefinement`
boundary.
-/
import Kernel.DeployedMaterializerWitness
import Theory.CellSlot

namespace Minidregg.Compiler.DeployedCellRegistry

open Minidregg.Theory
open Minidregg.Theory.CausalVersionDag
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Stable schema identities -/

/-- These values are wire pins.  Changing either component is a migration,
not a local refactor.  Schema id 14 agrees with the Hyperdocument causal-family
witnesses already emitted by this tree. -/
def declaredEffectSchemaRef : SchemaRef := ⟨⟨11⟩, 1⟩
def credentialAuthoritySchemaRef : SchemaRef := ⟨⟨12⟩, 1⟩
def hyperdocumentContentSchemaRef : SchemaRef := ⟨⟨14⟩, 1⟩
def hyperdocumentEventSchemaRef : SchemaRef := ⟨⟨15⟩, 1⟩

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

noncomputable def theoryMaterializer :
    (kind : DeployedKind) -> Materializer (deployedSchema kind) Digest
  | .declaredEffect =>
      Minidregg.Theory.DeployedMaterializerWitness.effectMaterializer
  | .credentialAuthority =>
      Minidregg.Theory.DeployedMaterializerWitness.authorityMaterializer
  | .hyperdocument =>
      Minidregg.Theory.DeployedMaterializerWitness.hyperdocumentMaterializer

/-- A concrete outside-home producer of the previously open
`DeployedRegistryConfig` carrier. -/
noncomputable def theoryConfig : DeployedRegistryConfig Digest where
  schemaRef := theorySchemaRef
  schemaRef_injective := theorySchemaRef_injective
  materializer := theoryMaterializer
  rootBytes := Minidregg.Theory.DeployedMaterializerWitness.lengthRoot

/-- The exact generic registry induced by the three-kind Theory configuration. -/
noncomputable def theoryRegistry : TypeRegistry Digest :=
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

def schema : Kind -> CellState.Schema.{0, 0, 0, 0}
  | .declaredEffect => DeclaredTurn.effectSchema
  | .credentialAuthority => CredentialAuthorityState.schema
  | .hyperdocumentContent => Hyperdocument.cellSchema
  | .hyperdocumentEvent =>
      Minidregg.Kernel.HyperdocumentEventLog.cellSchema

noncomputable def materializer :
    (kind : Kind) -> Materializer (schema kind) Digest
  | .declaredEffect =>
      Minidregg.Theory.DeployedMaterializerWitness.effectMaterializer
  | .credentialAuthority =>
      Minidregg.Theory.DeployedMaterializerWitness.authorityMaterializer
  | .hyperdocumentContent =>
      Minidregg.Theory.DeployedMaterializerWitness.hyperdocumentMaterializer
  | .hyperdocumentEvent =>
      Minidregg.Kernel.DeployedMaterializerWitness.eventLogCellMaterializer

/-- The full heterogeneous registry.  Its dependent payload type is selected
by `Kind`; no `Dynamic`, erased bytes, or cast participates in storage. -/
noncomputable def registry : TypeRegistry Digest where
  Kind := Kind
  tag := Kind.tag
  kindAtTag := kindAtTag
  kindAtTag_tag := kindAtTag_tag
  schemaRef := schemaRef
  schemaRef_injective := schemaRef_injective
  schema := schema
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

noncomputable def packedCell : (kind : Kind) -> PackedCell registry
  | .declaredEffect =>
      ⟨.declaredEffect,
        Minidregg.Theory.DeployedMaterializerWitness.effectCell⟩
  | .credentialAuthority =>
      ⟨.credentialAuthority,
        Minidregg.Theory.DeployedMaterializerWitness.authorityCell⟩
  | .hyperdocumentContent =>
      ⟨.hyperdocumentContent,
        Minidregg.Theory.DeployedMaterializerWitness.hyperdocumentCell⟩
  | .hyperdocumentEvent =>
      ⟨.hyperdocumentEvent,
        Minidregg.Kernel.DeployedMaterializerWitness.eventLogCell⟩

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

noncomputable def createRequest (kind : Kind) :
    CreateRequest (CellId := CellId) registry where
  cellId := cellId kind
  expectedPreRoot := CellSlot.root registry .absent
  cell := packedCell kind

noncomputable def emptyDirectory : Directory CellId registry :=
  Directory.empty registry

noncomputable def afterCreate (kind : Kind) : Directory CellId registry :=
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

noncomputable def deleteRequest (kind : Kind) :
    DeleteRequest (CellId := CellId) registry where
  cellId := cellId kind
  expectedPreRoot := CellSlot.root registry (.present (packedCell kind))
  expectedSchema := schemaRef kind

noncomputable def afterDelete (kind : Kind) : Directory CellId registry :=
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

noncomputable def staleCreateRequest (kind : Kind) :
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

noncomputable def staleDeleteRequest (kind : Kind) :
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

noncomputable def wrongSchemaDeleteRequest :
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
