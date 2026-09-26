/-
The authority preparation shared by grain-backed birth authoring and receiving.
The marker supplied here must be derived and bound by the enclosing composite
source. This module grants no authorization and emits no durable intent.
-/
import Compiler.CredentialAuthorityDomainReceiver

namespace Minidregg.Compiler.GrainResourceBirthAuthority

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler

set_option autoImplicit false

def edits (snapshot : CredentialAuthorityDomain.Snapshot)
    (descriptor : Descriptor CanonicalCellRegistry.registry) (operationMarker : Nat) :
    List CredentialAuthorityDomain.Edit :=
  CredentialAuthorityDomainReceiver.grantEdits snapshot descriptor ++
    [CredentialAuthorityDomain.nullifierEdit snapshot operationMarker]

theorem edits_birth_prefix (snapshot : CredentialAuthorityDomain.Snapshot)
    (descriptor : Descriptor CanonicalCellRegistry.registry) (operationMarker : Nat) :
    (edits snapshot descriptor operationMarker).take
      (CredentialAuthorityDomainReceiver.grantEdits snapshot descriptor).length =
        CredentialAuthorityDomainReceiver.grantEdits snapshot descriptor := by
  simp [edits]

theorem edits_operation_suffix (snapshot : CredentialAuthorityDomain.Snapshot)
    (descriptor : Descriptor CanonicalCellRegistry.registry) (operationMarker : Nat) :
    (edits snapshot descriptor operationMarker).drop
      (CredentialAuthorityDomainReceiver.grantEdits snapshot descriptor).length =
        [CredentialAuthorityDomain.nullifierEdit snapshot operationMarker] := by
  simp [edits]

/-- Both replay markers are checked on the same OLD authority state, then
prepared and physically lowered as one update. The checked birth grant
template is retained separately for the eventual birth policy admission. -/
structure Prepared {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (profile : CanonicalPolicyAdmission.PolicyCompilerProfile F)
    (deployment : CanonicalCellRegistry.Deployment)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (loaded : CredentialAuthorityDomainReceiver.Loaded deployment.authorityAnchor durable.snapshot)
    (descriptor : Descriptor CanonicalCellRegistry.registry) (operationMarker : Nat) where
  private mk ::
  markersDistinct : descriptor.authorityNullifier ≠ operationMarker
  initialSources : PolicySourceCell.CheckedInitials deployment.domain profile
    descriptor.initialPolicies
  birthReady : CredentialAuthorityDomainReceiver.BatchReady loaded.snapshot descriptor
  operationMarkerFresh : CredentialAuthorityState.isNullified loaded.snapshot.cell
    operationMarker = false
  checked : CredentialAuthorityDomain.Prepared loaded.snapshot
    (edits loaded.snapshot descriptor operationMarker)
  physical : CredentialAuthorityDomainReceiver.Lowered directory loaded
    (edits loaded.snapshot descriptor operationMarker) checked
    (CredentialAuthorityDomainReceiver.allocationReservedIds deployment descriptor)

def prepare {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (profile : CanonicalPolicyAdmission.PolicyCompilerProfile F)
    (deployment : CanonicalCellRegistry.Deployment)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (loaded : CredentialAuthorityDomainReceiver.Loaded deployment.authorityAnchor durable.snapshot)
    (descriptor : Descriptor CanonicalCellRegistry.registry) (operationMarker : Nat) :
    Option (Prepared profile deployment directory loaded descriptor operationMarker) := do
  if distinct : descriptor.authorityNullifier ≠ operationMarker then
    let initialSources ← PolicySourceCell.checkInitials deployment.domain profile
      descriptor.initialPolicies
    if ready : CredentialAuthorityDomainReceiver.BatchReady loaded.snapshot descriptor then
      if fresh : CredentialAuthorityState.isNullified loaded.snapshot.cell operationMarker = false then
        let checked ← CredentialAuthorityDomain.prepare loaded.snapshot
          (edits loaded.snapshot descriptor operationMarker)
        let physical ← CredentialAuthorityDomainReceiver.lower directory loaded checked
          (CredentialAuthorityDomainReceiver.allocationReservedIds deployment descriptor)
        some ⟨distinct, initialSources, ready, fresh, checked, physical⟩
      else none
    else none
  else none

def Prepared.auxiliaryCreates {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : CanonicalCellRegistry.Deployment}
    {directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {loaded : CredentialAuthorityDomainReceiver.Loaded deployment.authorityAnchor durable.snapshot}
    {descriptor : Descriptor CanonicalCellRegistry.registry} {operationMarker : Nat}
    (prepared : Prepared profile deployment directory loaded descriptor operationMarker) :
    List (CreateRequest (CellId := Nat) CanonicalCellRegistry.registry) :=
  CanonicalCellRegistry.initialSourceCreates deployment.domain prepared.initialSources.records ++
    prepared.physical.placement.auxiliaryCreates

/-- The routed physical authority post is the exact logical result of the
single combined checked edit list. It is not the bare birth-only post. -/
theorem Prepared.physical_post_exact {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : CanonicalCellRegistry.Deployment}
    {directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {loaded : CredentialAuthorityDomainReceiver.Loaded deployment.authorityAnchor durable.snapshot}
    {descriptor : Descriptor CanonicalCellRegistry.registry} {operationMarker : Nat}
    (prepared : Prepared profile deployment directory loaded descriptor operationMarker) :
    prepared.physical.post.logical = prepared.checked.postLogical := by
  change CredentialAuthorityDomain.logicalOfPages prepared.physical.post.pages =
    CredentialAuthorityDomain.logicalOfPages prepared.checked.postPages
  rw [prepared.physical.postPages]

private theorem applyFieldWrites_append
    (first second : List (FieldWrite CredentialAuthorityState.schema.{0, 0}))
    (fields : FieldStore CredentialAuthorityState.schema.{0, 0}) :
    applyFieldWrites (first ++ second) fields =
      applyFieldWrites second (applyFieldWrites first fields) := by
  induction first generalizing fields with
  | nil => rfl
  | cons write rest ih =>
      simp only [List.cons_append, applyFieldWrites]
      exact ih _

private theorem nullifierEdit_sets (snapshot : CredentialAuthorityDomain.Snapshot)
    (marker : Nat) (fields : FieldStore CredentialAuthorityState.schema.{0, 0}) :
    applyFieldWrites (CredentialAuthorityDomain.nullifierEdit snapshot marker).writes
      fields (.nullifier marker) = some true := by
  let beforeWrites : List (FieldWrite CredentialAuthorityState.schema.{0, 0}) :=
    ((CredentialAuthorityDomain.nullifierEdit snapshot marker).before.toList.flatMap
      CredentialAuthorityPageMaterializer.Entry.fields).map
      (fun field => ⟨field, none⟩)
  have lastWrite : (CredentialAuthorityDomain.nullifierEdit snapshot marker).writes =
      beforeWrites ++ [⟨.nullifier marker, some true⟩] := by
    simp [beforeWrites, CredentialAuthorityDomain.Edit.writes,
      CredentialAuthorityDomain.entryWrites_nullifier,
      CredentialAuthorityDomain.nullifierEdit]
    rfl
  rw [lastWrite]
  rw [applyFieldWrites_append]
  simp [applyFieldWrites, FieldStore.assign]
  rfl

theorem Prepared.operation_marker_consumed {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : CanonicalCellRegistry.Deployment}
    {directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {loaded : CredentialAuthorityDomainReceiver.Loaded deployment.authorityAnchor durable.snapshot}
    {descriptor : Descriptor CanonicalCellRegistry.registry} {operationMarker : Nat}
    (prepared : Prepared profile deployment directory loaded descriptor operationMarker) :
    prepared.physical.post.logical.fields (.nullifier operationMarker) = some true := by
  rw [prepared.physical_post_exact]
  rw [show prepared.checked.postLogical = prepared.checked.validated.apply.logical from
    prepared.checked.projectionExact]
  simp [CredentialAuthorityDomain.editPatch, edits,
    CredentialAuthorityDomain.Edit.writes,
    CredentialAuthorityDomain.entryWrites_nullifier,
    applyFieldWrites_append, ValidatedPatch.apply,
    CredentialAuthorityDomain.nullifierEdit, applyFieldWrites, materialize,
    FieldStore.assign]
  rfl

/-- Appending the separate operation marker cannot erase any birth grant,
initial policy, or the birth's own nullifier field. Their exact values remain
the result of the existing birth grant batch's source edits. -/
theorem Prepared.birth_fields_preserved {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : CanonicalCellRegistry.Deployment}
    {directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {loaded : CredentialAuthorityDomainReceiver.Loaded deployment.authorityAnchor durable.snapshot}
    {descriptor : Descriptor CanonicalCellRegistry.registry} {operationMarker : Nat}
    (prepared : Prepared profile deployment directory loaded descriptor operationMarker)
    (field : CredentialAuthorityState.AuthorityField)
    (different : field ≠ .nullifier operationMarker) :
    prepared.physical.post.logical.fields field =
      applyFieldWrites
        ((CredentialAuthorityDomainReceiver.grantEdits loaded.snapshot descriptor).flatMap
          CredentialAuthorityDomain.Edit.writes)
        loaded.snapshot.cell.logical.fields field := by
  rw [prepared.physical_post_exact]
  rw [show prepared.checked.postLogical = prepared.checked.validated.apply.logical from
    prepared.checked.projectionExact]
  let last := CredentialAuthorityDomain.nullifierEdit loaded.snapshot operationMarker
  have outside : field ∉ (last.writes.map FieldWrite.field).toFinset := by
    have lastFields : last.writes.map FieldWrite.field =
        (if (loaded.snapshot.logical.fields (.nullifier operationMarker)).isSome then
          [.nullifier operationMarker, .nullifier operationMarker]
        else [.nullifier operationMarker]) := by
      dsimp [last, CredentialAuthorityDomain.nullifierEdit,
        CredentialAuthorityDomain.Edit.writes, CredentialAuthorityDomain.entryWrites]
      cases loaded.snapshot.logical.fields (.nullifier operationMarker) <;> rfl
    rw [lastFields]
    split <;> simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_idem]
    all_goals
      change field ∉ ({.nullifier operationMarker} : Finset _)
      simpa only [Finset.mem_singleton] using different
  simp only [ValidatedPatch.apply, materialize, CredentialAuthorityDomain.editPatch,
    edits, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change applyFieldWrites
      (((CredentialAuthorityDomainReceiver.grantEdits loaded.snapshot descriptor).flatMap
        CredentialAuthorityDomain.Edit.writes) ++ last.writes)
      loaded.snapshot.cell.logical.fields field = _
  rw [applyFieldWrites_append]
  exact applyFieldWrites_frame last.writes _ field outside

theorem Prepared.birth_marker_consumed {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : CanonicalCellRegistry.Deployment}
    {directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {loaded : CredentialAuthorityDomainReceiver.Loaded deployment.authorityAnchor durable.snapshot}
    {descriptor : Descriptor CanonicalCellRegistry.registry} {operationMarker : Nat}
    (prepared : Prepared profile deployment directory loaded descriptor operationMarker) :
    prepared.physical.post.logical.fields (.nullifier descriptor.authorityNullifier) =
      some true := by
  have different : (.nullifier descriptor.authorityNullifier :
      CredentialAuthorityState.AuthorityField) ≠ .nullifier operationMarker := by
    intro same
    exact prepared.markersDistinct (by cases same; rfl)
  rw [prepared.birth_fields_preserved _ different]
  unfold CredentialAuthorityDomainReceiver.grantEdits
  simp only [List.flatMap_append, applyFieldWrites_append, List.flatMap_singleton]
  exact nullifierEdit_sets loaded.snapshot descriptor.authorityNullifier _

end Minidregg.Compiler.GrainResourceBirthAuthority
