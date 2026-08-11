/-
# Compiler.FiniteSparseMaterializerAudit -- exact registered-schema census

This is the executable audit for the finite sparse migration.  Its scope is
deliberately closed: the four schemas in `DeployedCellRegistry` and the three
bounded production schemas in `BoundedPageExtensionCatalog`.  Generic
`Materializer` parameters elsewhere are interfaces, not silently counted as
deployments.

The result is seven inhabited sparse schemas and seven nonempty accepted typed
transitions.  It also records the important wire-grade distinction instead of
papering over it:

* the four original unbounded schema materializers use the openly documented
  countability-selected inhabitation codecs; and
* the three bounded page schemas have stable framed codecs and Lean cSHAKE256
  roots, and now cross the concrete heterogeneous registry boundary in
  `BoundedPageCellRegistry`.

Thus no registered carrier is vacuous.  The four original codecs remain
existence witnesses rather than production wire formats; callers that require
stable physical bytes must select the bounded representations or supply a new
audited codec.  This module does not promote them by terminology.
-/
import Compiler.BoundedPageCellRegistry
import Compiler.DeployedCellRegistry
import Kernel.DeclaredHyperedgeWitness
import Kernel.HyperdocumentTwoParentWitness

namespace Minidregg.Compiler.FiniteSparseMaterializerAudit

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Closed seven-schema census -/

inductive Surface where
  | declaredEffect
  | credentialAuthority
  | hyperdocumentContent
  | hyperdocumentEvent
  | boundedContentPage
  | boundedEventPage
  | boundedAuthorityPage
  deriving DecidableEq, Repr

def allSurfaces : List Surface :=
  [.declaredEffect, .credentialAuthority, .hyperdocumentContent,
    .hyperdocumentEvent, .boundedContentPage, .boundedEventPage,
    .boundedAuthorityPage]

theorem allSurfaces_length : allSurfaces.length = 7 := by decide
theorem allSurfaces_nodup : allSurfaces.Nodup := by decide
theorem mem_allSurfaces (surface : Surface) : surface ∈ allSurfaces := by
  cases surface <;> simp [allSurfaces]

inductive WireGrade where
  | inhabitationOnly
  | concretePinned
  deriving DecidableEq, Repr

/-- This classification is intentionally honest about the actual definitions,
not inferred from a filename containing the word "deployed". -/
def wireGrade : Surface -> WireGrade
  | .declaredEffect => .inhabitationOnly
  | .credentialAuthority => .inhabitationOnly
  | .hyperdocumentContent => .inhabitationOnly
  | .hyperdocumentEvent => .inhabitationOnly
  | .boundedContentPage => .concretePinned
  | .boundedEventPage => .concretePinned
  | .boundedAuthorityPage => .concretePinned

theorem inhabitation_only_exact (surface : Surface) :
    wireGrade surface = .inhabitationOnly <->
      surface = .declaredEffect \/ surface = .credentialAuthority \/
      surface = .hyperdocumentContent \/ surface = .hyperdocumentEvent := by
  cases surface <;> simp [wireGrade]

theorem concrete_pinned_exact (surface : Surface) :
    wireGrade surface = .concretePinned <->
      surface = .boundedContentPage \/ surface = .boundedEventPage \/
      surface = .boundedAuthorityPage := by
  cases surface <;> simp [wireGrade]

/-! ## The missing authority transition under the exact registry materializer -/

noncomputable abbrev authorityMaterializer :=
  Minidregg.Theory.DeployedMaterializerWitness.authorityMaterializer

theorem authorityMaterializer_registry_exact :
    authorityMaterializer =
      Minidregg.Compiler.DeployedCellRegistry.materializer
        Minidregg.Compiler.DeployedCellRegistry.Kind.credentialAuthority :=
  rfl

noncomputable def authorityPre :
    Materialized authorityMaterializer :=
  Minidregg.Theory.DeployedMaterializerWitness.authorityCell

def authorityNullifier : Nat := 424242

noncomputable def authorityPatch :
    Patch Minidregg.Theory.CredentialAuthorityState.schema Digest where
  expectedPreRoot := authorityPre.root
  fieldFootprint :=
    {Minidregg.Theory.CredentialAuthorityState.AuthorityField.nullifier
      authorityNullifier}
  resourceFootprint := ∅
  fieldWrites :=
    [{ field :=
          Minidregg.Theory.CredentialAuthorityState.AuthorityField.nullifier
            authorityNullifier
       value := some true }]
  resourceWrites := []

theorem authorityPatch_accepted :
    ∃ validated : ValidatedPatch authorityMaterializer authorityPre authorityPatch,
      validate authorityMaterializer authorityPre authorityPatch =
        ValidationOutcome.accepted validated := by
  unfold validate
  rw [dif_pos (show authorityPatch.expectedPreRoot = authorityPre.root from rfl)]
  rw [dif_pos
    (show authorityPatch.fieldFootprint = authorityPatch.namedFields by decide)]
  rw [dif_pos
    (show authorityPatch.resourceFootprint = authorityPatch.namedResources by
      decide)]
  exact ⟨_, rfl⟩

@[simp] theorem authorityPatch_post_exact
    (validated :
      ValidatedPatch authorityMaterializer authorityPre authorityPatch) :
    Minidregg.Theory.CredentialAuthorityState.isNullified
        validated.apply authorityNullifier = true := by
  simp [Minidregg.Theory.CredentialAuthorityState.isNullified,
    ValidatedPatch.apply, authorityPatch, applyFieldWrites, materialize,
    FieldStore.assign]

/-! ## One accepted transition for every registered schema -/

def AcceptedCarrier : Surface -> Prop
  | .declaredEffect =>
      Nonempty (ValidatedPatch
        Minidregg.Theory.DeployedMaterializerWitness.effectMaterializer
        Minidregg.Kernel.DeclaredHyperedgeWitness.preCell
        Minidregg.Kernel.DeclaredHyperedgeWitness.Migration.debitPatch)
  | .credentialAuthority =>
      Nonempty (ValidatedPatch authorityMaterializer authorityPre authorityPatch)
  | .hyperdocumentContent =>
      Nonempty (ValidatedPatch
        Minidregg.Theory.DeployedMaterializerWitness.hyperdocumentMaterializer
        Minidregg.Kernel.HyperdocumentTwoParentWitness.baseCell
        (Minidregg.Kernel.HyperdocumentTwoParentWitness.mergeDeclaration.patch
          Minidregg.Kernel.HyperdocumentTwoParentWitness.mergeConfig))
  | .hyperdocumentEvent =>
      Nonempty (ValidatedPatch
        Minidregg.Kernel.DeployedMaterializerWitness.eventLogCellMaterializer
        Minidregg.Kernel.HyperdocumentTwoParentWitness.logCell
        ((Minidregg.Kernel.HyperdocumentMergePublication.derivedEventDeclaration
            Minidregg.Kernel.HyperdocumentTwoParentWitness.mergeAccepted
            Minidregg.Kernel.HyperdocumentTwoParentWitness.logCell.root).patch
          Minidregg.Kernel.HyperdocumentTwoParentWitness.eventConfig))
  | .boundedContentPage =>
      Nonempty (ValidatedPatch
        Minidregg.Compiler.HyperdocumentContentPageMaterializer.materializer
        Minidregg.Compiler.HyperdocumentContentPageMaterializer.genesisCell
        Minidregg.Compiler.HyperdocumentContentPageMaterializer.linkPatch)
  | .boundedEventPage =>
      Nonempty (ValidatedPatch
        Minidregg.Compiler.HyperdocumentEventPageMaterializer.materializer
        Minidregg.Compiler.HyperdocumentEventPageMaterializer.emptyCell
        Minidregg.Compiler.HyperdocumentEventPageMaterializer.installPatch)
  | .boundedAuthorityPage =>
      Nonempty (ValidatedPatch
        Minidregg.Compiler.CredentialAuthorityPageMaterializer.materializer
        Minidregg.Compiler.CredentialAuthorityPageMaterializer.preCell
        Minidregg.Compiler.CredentialAuthorityPageMaterializer.updatePatch)

theorem acceptedCarrier (surface : Surface) : AcceptedCarrier surface := by
  cases surface with
  | declaredEffect =>
      exact
        ⟨Minidregg.Kernel.DeclaredHyperedgeWitness.Migration.debitPatch_accepted.choose⟩
  | credentialAuthority =>
      exact ⟨authorityPatch_accepted.choose⟩
  | hyperdocumentContent =>
      exact Minidregg.Kernel.HyperdocumentTwoParentWitness.mergeValidatedNonempty
  | hyperdocumentEvent =>
      exact Minidregg.Kernel.HyperdocumentTwoParentWitness.eventValidatedNonempty
  | boundedContentPage =>
      exact
        ⟨Minidregg.Compiler.HyperdocumentContentPageMaterializer.linkPatch_accepted.choose⟩
  | boundedEventPage =>
      exact
        ⟨Minidregg.Compiler.HyperdocumentEventPageMaterializer.installPatch_accepted.choose⟩
  | boundedAuthorityPage =>
      exact
        ⟨Minidregg.Compiler.CredentialAuthorityPageMaterializer.updatePatch_accepted.choose⟩

/-- The three production rows additionally cross the exact dependent outer
registry and execute create/delete. -/
theorem bounded_registry_lifecycle
    (kind : Minidregg.Compiler.BoundedPageExtensionCatalog.PageKind) :
    Minidregg.Theory.CellRegistry.create
        Minidregg.Compiler.BoundedPageCellRegistry.registry
        Minidregg.Compiler.BoundedPageCellRegistry.emptyDirectory
        (Minidregg.Compiler.BoundedPageCellRegistry.createRequest kind) =
      .ok (Minidregg.Compiler.BoundedPageCellRegistry.afterCreate kind) /\
    Minidregg.Theory.CellRegistry.delete
        Minidregg.Compiler.BoundedPageCellRegistry.registry
        (Minidregg.Compiler.BoundedPageCellRegistry.afterCreate kind)
        (Minidregg.Compiler.BoundedPageCellRegistry.deleteRequest kind) =
      .ok (Minidregg.Compiler.BoundedPageCellRegistry.afterDelete kind) :=
  ⟨Minidregg.Compiler.BoundedPageCellRegistry.create_succeeds kind,
    Minidregg.Compiler.BoundedPageCellRegistry.delete_succeeds kind⟩

/-! ## Axiom audit -/

/-- info: 'Minidregg.Compiler.FiniteSparseMaterializerAudit.allSurfaces_nodup' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms allSurfaces_nodup
/-- info: 'Minidregg.Compiler.FiniteSparseMaterializerAudit.authorityPatch_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms authorityPatch_accepted
/-- info: 'Minidregg.Compiler.FiniteSparseMaterializerAudit.authorityPatch_post_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms authorityPatch_post_exact
/-- info: 'Minidregg.Compiler.FiniteSparseMaterializerAudit.acceptedCarrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms acceptedCarrier
/-- info: 'Minidregg.Compiler.FiniteSparseMaterializerAudit.bounded_registry_lifecycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bounded_registry_lifecycle

end Minidregg.Compiler.FiniteSparseMaterializerAudit
