/-
The authority preparation shared by grain-backed birth authoring and receiving.
The marker supplied here must be derived and bound by the enclosing composite
source. This module grants no authorization and emits no durable intent.
-/
import Compiler.CredentialAuthorityDomainReceiver

namespace Minidregg.Compiler.GrainResourceBirthAuthority

open Minidregg.Theory
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

end Minidregg.Compiler.GrainResourceBirthAuthority
