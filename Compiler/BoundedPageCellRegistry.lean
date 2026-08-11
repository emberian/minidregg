/-
# Compiler.BoundedPageCellRegistry -- concrete sparse page cells

`BoundedPageExtensionCatalog` pins three production page codecs, but a catalog
row alone does not show that the selected schema crosses the heterogeneous
cell boundary.  This module closes that gap.  The registry below uses the
catalog's exact kinds and schema/version pins, the three actual page
materializers (not `codecOfCountable`), and one nonempty page cell for every
kind.  Each registered schema has both:

* an accepted, nonempty typed patch under its exact materializer; and
* an executable create/delete lifecycle through `CellRegistry`.

The page schemas are bounded representation shards which project into the
unbounded canonical Hyperdocument, event-log, and authority semantics.  This
does not relabel the older countability-selected materializers as production
wire formats.  The directory root is a separately domain-separated Lean
cSHAKE256 computation.  Collision resistance and physical persistence remain
the explicit `RootBindingPremise` and `PersistenceRefinement` boundaries.
-/
import Compiler.BoundedPageExtensionCatalog
import Theory.CellSlot

namespace Minidregg.Compiler.BoundedPageCellRegistry

open Minidregg.Compiler.BoundedPageExtensionCatalog
open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CausalVersionDag
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Kind := PageKind

/-! ## Exact catalog-selected schemas and materializers -/

def schema : Kind -> CellState.Schema.{0, 0, 0, 0}
  | .content =>
      Minidregg.Compiler.HyperdocumentContentPageMaterializer.schema
  | .eventHistory =>
      Minidregg.Compiler.HyperdocumentEventPageMaterializer.schema
  | .authorityPolicy =>
      Minidregg.Compiler.CredentialAuthorityPageMaterializer.schema

def materializer : (kind : Kind) -> Materializer (schema kind) Digest
  | .content =>
      Minidregg.Compiler.HyperdocumentContentPageMaterializer.materializer
  | .eventHistory =>
      Minidregg.Compiler.HyperdocumentEventPageMaterializer.materializer
  | .authorityPolicy =>
      Minidregg.Compiler.CredentialAuthorityPageMaterializer.materializer

/-- The registry schema reference is projected from the same controller row
which supplies the codec/root pins. -/
def schemaRef (kind : Kind) : SchemaRef :=
  ⟨(BoundedPageExtensionCatalog.controller kind).schemaId,
    (BoundedPageExtensionCatalog.controller kind).wireVersion⟩

theorem schemaRef_injective : Function.Injective schemaRef := by
  intro left right same
  cases left <;> cases right <;>
    simp [schemaRef, BoundedPageExtensionCatalog.controller,
      contentController, eventHistoryController, authorityPolicyController]
      at same ⊢

@[simp] theorem schemaRef_schemaId (kind : Kind) :
    (schemaRef kind).schemaId =
      (BoundedPageExtensionCatalog.controller kind).schemaId :=
  rfl

@[simp] theorem schemaRef_version (kind : Kind) :
    (schemaRef kind).version =
      (BoundedPageExtensionCatalog.controller kind).wireVersion :=
  rfl

/-- Stable outer slot-root customization, distinct from every page payload
root domain. -/
def directoryRootCustomization : List UInt8 :=
  [76, 79, 79, 77, 46, 80, 65, 71, 69, 46, 67, 69, 76, 76, 46, 82, 69, 71,
    73, 83, 84, 82, 89, 46, 82, 79, 79, 84, 47, 118, 49]

def directoryRoot (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash directoryRootCustomization bytes).digest

theorem directory_domain_distinct (kind : Kind) :
    directoryRootCustomization !=
      (BoundedPageExtensionCatalog.controller kind).rootCustomization := by
  cases kind <;> decide

def registry : TypeRegistry Digest where
  Kind := Kind
  tag := PageKind.tag
  kindAtTag := kindAtTag
  kindAtTag_tag := kindAtTag_tag
  schemaRef := schemaRef
  schemaRef_injective := schemaRef_injective
  schema := schema
  materializer := materializer
  rootBytes := directoryRoot

@[simp] theorem registry_materializer_content :
    registry.materializer .content =
      Minidregg.Compiler.HyperdocumentContentPageMaterializer.materializer :=
  rfl

@[simp] theorem registry_materializer_event :
    registry.materializer .eventHistory =
      Minidregg.Compiler.HyperdocumentEventPageMaterializer.materializer :=
  rfl

@[simp] theorem registry_materializer_authority :
    registry.materializer .authorityPolicy =
      Minidregg.Compiler.CredentialAuthorityPageMaterializer.materializer :=
  rfl

/-! ## One nonempty canonical page cell per row -/

def packedCell : (kind : Kind) -> PackedCell registry
  | .content =>
      ⟨.content,
        Minidregg.Compiler.HyperdocumentContentPageMaterializer.linkCell⟩
  | .eventHistory =>
      ⟨.eventHistory,
        Minidregg.Compiler.HyperdocumentEventPageMaterializer.exampleCell⟩
  | .authorityPolicy =>
      ⟨.authorityPolicy,
        Minidregg.Compiler.CredentialAuthorityPageMaterializer.postCell⟩

@[simp] theorem packedCell_kind (kind : Kind) :
    (packedCell kind).kind = kind := by
  cases kind <;> rfl

/-- Every concrete catalog row round-trips through dependent registry decoding;
there is no erased payload or cast. -/
@[simp] theorem packedCell_roundtrip (kind : Kind) :
    PackedCell.decode registry (PackedCell.bytes registry (packedCell kind)) =
      some (packedCell kind) :=
  PackedCell.decode_bytes registry (packedCell kind)

/-! ## Every page materializer accepts an effective typed patch -/

def AcceptedTransition : Kind -> Prop
  | .content =>
      ∃ validated : ValidatedPatch
          Minidregg.Compiler.HyperdocumentContentPageMaterializer.materializer
          Minidregg.Compiler.HyperdocumentContentPageMaterializer.genesisCell
          Minidregg.Compiler.HyperdocumentContentPageMaterializer.linkPatch,
        validate
            Minidregg.Compiler.HyperdocumentContentPageMaterializer.materializer
            Minidregg.Compiler.HyperdocumentContentPageMaterializer.genesisCell
            Minidregg.Compiler.HyperdocumentContentPageMaterializer.linkPatch =
          ValidationOutcome.accepted validated
  | .eventHistory =>
      ∃ validated : ValidatedPatch
          Minidregg.Compiler.HyperdocumentEventPageMaterializer.materializer
          Minidregg.Compiler.HyperdocumentEventPageMaterializer.emptyCell
          Minidregg.Compiler.HyperdocumentEventPageMaterializer.installPatch,
        validate
            Minidregg.Compiler.HyperdocumentEventPageMaterializer.materializer
            Minidregg.Compiler.HyperdocumentEventPageMaterializer.emptyCell
            Minidregg.Compiler.HyperdocumentEventPageMaterializer.installPatch =
          ValidationOutcome.accepted validated
  | .authorityPolicy =>
      ∃ validated : ValidatedPatch
          Minidregg.Compiler.CredentialAuthorityPageMaterializer.materializer
          Minidregg.Compiler.CredentialAuthorityPageMaterializer.preCell
          Minidregg.Compiler.CredentialAuthorityPageMaterializer.updatePatch,
        validate
            Minidregg.Compiler.CredentialAuthorityPageMaterializer.materializer
            Minidregg.Compiler.CredentialAuthorityPageMaterializer.preCell
            Minidregg.Compiler.CredentialAuthorityPageMaterializer.updatePatch =
          ValidationOutcome.accepted validated

theorem acceptedTransition (kind : Kind) : AcceptedTransition kind := by
  cases kind with
  | content =>
      exact
        Minidregg.Compiler.HyperdocumentContentPageMaterializer.linkPatch_accepted
  | eventHistory =>
      exact
        Minidregg.Compiler.HyperdocumentEventPageMaterializer.installPatch_accepted
  | authorityPolicy =>
      exact
        Minidregg.Compiler.CredentialAuthorityPageMaterializer.updatePatch_accepted

/-- These are not accepted no-op witnesses: every patch has a nonempty exact
field footprint. -/
def PatchFootprintNonempty : Kind -> Prop
  | .content =>
      () ∈
        Minidregg.Compiler.HyperdocumentContentPageMaterializer.linkPatch.{0, 0}.fieldFootprint
  | .eventHistory =>
      () ∈
        Minidregg.Compiler.HyperdocumentEventPageMaterializer.installPatch.{0, 0}.fieldFootprint
  | .authorityPolicy =>
      () ∈
        Minidregg.Compiler.CredentialAuthorityPageMaterializer.updatePatch.{0, 0}.fieldFootprint

theorem patchFootprintNonempty (kind : Kind) : PatchFootprintNonempty kind := by
  cases kind <;> exact Finset.mem_singleton_self ()

/-- The accepted payloads project to real canonical semantics, not merely
different page bytes. -/
def CanonicalProjectionEffective : Kind -> Prop
  | .content =>
      Minidregg.Theory.Hyperdocument.lookup
          Minidregg.Compiler.HyperdocumentContentPageMaterializer.linkPage.toCanonicalState
          .links
          Minidregg.Compiler.HyperdocumentContentPageMaterializer.forwardLinkId =
        some
          Minidregg.Compiler.HyperdocumentContentPageMaterializer.forwardLink.toCanonical
  | .eventHistory =>
      Minidregg.Compiler.HyperdocumentEventPageMaterializer.examplePage.toSparseStore
          .events
          Minidregg.Compiler.HyperdocumentEventPageMaterializer.exampleEntry.key =
        some Minidregg.Compiler.HyperdocumentEventPageMaterializer.exampleRecord
  | .authorityPolicy =>
      Minidregg.Compiler.CredentialAuthorityPageMaterializer.postPage.policyEpochAt
          Minidregg.Compiler.CredentialAuthorityPageMaterializer.examplePolicy = 3

theorem canonicalProjectionEffective (kind : Kind) :
    CanonicalProjectionEffective kind := by
  cases kind with
  | content =>
      exact
        Minidregg.Compiler.HyperdocumentContentPageMaterializer.link_post_lookup_exact
  | eventHistory =>
      exact
        Minidregg.Compiler.HyperdocumentEventPageMaterializer.exampleSparseStore_contains
  | authorityPolicy =>
      exact
        Minidregg.Compiler.CredentialAuthorityPageMaterializer.post_policy_epoch_exact

/-! ## Executable heterogeneous lifecycle for every catalog row -/

abbrev CellId := Nat

def cellId : Kind -> CellId
  | .content => 201
  | .eventHistory => 202
  | .authorityPolicy => 203

def emptyDirectory : Directory CellId registry :=
  Directory.empty registry

def createRequest (kind : Kind) : CreateRequest (CellId := CellId) registry where
  cellId := cellId kind
  expectedPreRoot := CellSlot.root registry .absent
  cell := packedCell kind

def afterCreate (kind : Kind) : Directory CellId registry :=
  Directory.insert registry emptyDirectory (cellId kind) (packedCell kind)

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

def deleteRequest (kind : Kind) : DeleteRequest (CellId := CellId) registry where
  cellId := cellId kind
  expectedPreRoot := CellSlot.root registry (.present (packedCell kind))
  expectedSchema := schemaRef kind

def afterDelete (kind : Kind) : Directory CellId registry :=
  Directory.retire registry (afterCreate kind) (cellId kind)

theorem delete_succeeds (kind : Kind) :
    delete registry (afterCreate kind) (deleteRequest kind) =
      .ok (afterDelete kind) := by
  apply delete_of_exact registry (cell := packedCell kind)
  · exact created_slot kind
  · change schemaRef (packedCell kind).kind = schemaRef kind
    rw [packedCell_kind]
  · rfl

/-- Logical lifecycle success does not imply stable media. -/
abbrev PersistenceCeiling (PhysicalState InstallError : Type) :=
  PersistenceRefinement (CellId := CellId)
    PhysicalState InstallError registry

/-- cSHAKE binding is a computational premise, not a theorem of the finite
carrier construction. -/
abbrev RootBindingCeiling : Prop := RootBindingPremise registry

/-! ## Axiom audit -/

/-- info: 'Minidregg.Compiler.BoundedPageCellRegistry.schemaRef_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms schemaRef_injective
/-- info: 'Minidregg.Compiler.BoundedPageCellRegistry.packedCell_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms packedCell_roundtrip
/-- info: 'Minidregg.Compiler.BoundedPageCellRegistry.acceptedTransition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms acceptedTransition
/-- info: 'Minidregg.Compiler.BoundedPageCellRegistry.canonicalProjectionEffective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canonicalProjectionEffective
/-- info: 'Minidregg.Compiler.BoundedPageCellRegistry.create_succeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms create_succeeds
/-- info: 'Minidregg.Compiler.BoundedPageCellRegistry.delete_succeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms delete_succeeds

end Minidregg.Compiler.BoundedPageCellRegistry
