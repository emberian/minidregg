/-
The authority preparation shared by grain-backed birth authoring and receiving.
The marker supplied here must be derived and bound by the enclosing composite
source. This module grants no authorization and emits no durable intent.

The birth's grant batch and the composite operation's marker are one patch of
the one authority cell: the batch entries, then the marker's nullifier, each a
guarded assignment read at the store its prefix produced.
-/
import Compiler.CredentialAuthorityDomainReceiver

namespace Minidregg.Compiler.GrainResourceBirthAuthority

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState (layout isNullified)
open Minidregg.Theory.CredentialAuthorityEffects
  (Entry assignAll setAll run_assignAll nullifierEntry)
open Minidregg.Compiler

set_option autoImplicit false

/-- The birth batch's entries followed by the operation marker's nullifier. -/
def entries (descriptor : Descriptor CanonicalCellRegistry.registry) (operationMarker : Nat) :
    List Entry :=
  ResourceBirthAuthority.entries descriptor ++ [nullifierEntry operationMarker]

def patch (snapshot : CredentialAuthorityDomain.Snapshot)
    (descriptor : Descriptor CanonicalCellRegistry.registry) (operationMarker : Nat) :
    Patch layout :=
  assignAll snapshot.logical (entries descriptor operationMarker)

private theorem setAll_append (store : Store layout) (first second : List Entry) :
    setAll store (first ++ second) = setAll (setAll store first) second := by
  induction first generalizing store with
  | nil => rfl
  | cons entry rest ih => exact ih _

/-- Both replay markers are checked on the same OLD authority cell, then
prepared as one patch of it. The checked birth grant template is retained
separately for the eventual birth policy admission. -/
structure Prepared {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (profile : CanonicalPolicyAdmission.PolicyCompilerProfile F)
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (descriptor : Descriptor CanonicalCellRegistry.registry) (operationMarker : Nat) where
  private mk ::
  markersDistinct : descriptor.authorityNullifier ≠ operationMarker
  initialSources : PolicySourceCell.CheckedInitials deployment.domain profile
    descriptor.initialPolicies
  birthReady : CredentialAuthorityDomainReceiver.BatchReady loaded.snapshot descriptor
  operationMarkerFresh : isNullified loaded.snapshot.cell operationMarker = false
  checked : CredentialAuthorityDomain.Prepared loaded.snapshot
    (patch loaded.snapshot descriptor operationMarker)

def prepare {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (profile : CanonicalPolicyAdmission.PolicyCompilerProfile F)
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (descriptor : Descriptor CanonicalCellRegistry.registry) (operationMarker : Nat) :
    Option (Prepared profile deployment loaded descriptor operationMarker) := do
  if distinct : descriptor.authorityNullifier ≠ operationMarker then
    let initialSources ← PolicySourceCell.checkInitials deployment.domain profile
      descriptor.initialPolicies
    if ready : CredentialAuthorityDomainReceiver.BatchReady loaded.snapshot descriptor then
      if fresh : isNullified loaded.snapshot.cell operationMarker = false then
        let checked ← CredentialAuthorityDomain.prepare loaded.snapshot
          (patch loaded.snapshot descriptor operationMarker)
        some ⟨distinct, initialSources, ready, fresh, checked⟩
      else none
    else none
  else none

section Prepared

variable {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : CanonicalCellRegistry.Deployment}
    {loaded : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot}
    {descriptor : Descriptor CanonicalCellRegistry.registry} {operationMarker : Nat}

/-- The post authority cell of the combined patch. -/
def Prepared.post (prepared : Prepared profile deployment loaded descriptor operationMarker) :
    CredentialAuthorityDomain.Cell :=
  prepared.checked.validated.apply

/-- The one physical authority write. -/
def Prepared.writes (prepared : Prepared profile deployment loaded descriptor operationMarker) :
    List Kernel.DurableDataIntent.DataWrite :=
  loaded.writes prepared.post

/-- Authority allocates no cells; the only auxiliary creates are the birth's
initial policy sources. -/
def Prepared.auxiliaryCreates
    (prepared : Prepared profile deployment loaded descriptor operationMarker) :
    List (CreateRequest (CellId := Nat) CanonicalCellRegistry.registry) :=
  CanonicalCellRegistry.initialSourceCreates deployment.domain prepared.initialSources.records

theorem Prepared.post_logical
    (prepared : Prepared profile deployment loaded descriptor operationMarker) :
    prepared.post.logical =
      (setAll loaded.snapshot.logical (ResourceBirthAuthority.entries descriptor)).set
        ⟨.nullifier, operationMarker⟩ (some ()) := by
  change Patch.run loaded.snapshot.logical (patch loaded.snapshot descriptor operationMarker) = _
  rw [patch, run_assignAll, entries, setAll_append]
  rfl

theorem Prepared.operation_marker_consumed
    (prepared : Prepared profile deployment loaded descriptor operationMarker) :
    prepared.post.logical ⟨.nullifier, operationMarker⟩ = some () := by
  rw [prepared.post_logical, Store.set_eq]
  rfl

/-- Appending the separate operation marker cannot erase any birth grant,
initial policy, or the birth's own nullifier. Their exact values remain the
result of the birth grant batch's entries. -/
theorem Prepared.birth_fields_preserved
    (prepared : Prepared profile deployment loaded descriptor operationMarker)
    (address : Address layout) (different : address ≠ ⟨.nullifier, operationMarker⟩) :
    prepared.post.logical address =
      setAll loaded.snapshot.logical (ResourceBirthAuthority.entries descriptor) address := by
  rw [prepared.post_logical]
  exact Store.set_ne _ _ _ _ different

theorem Prepared.birth_marker_consumed
    (prepared : Prepared profile deployment loaded descriptor operationMarker) :
    prepared.post.logical ⟨.nullifier, descriptor.authorityNullifier⟩ = some () := by
  have different : (⟨.nullifier, descriptor.authorityNullifier⟩ : Address layout) ≠
      ⟨.nullifier, operationMarker⟩ := by
    intro same
    exact prepared.markersDistinct (eq_of_heq (Sigma.mk.inj same).2)
  rw [prepared.birth_fields_preserved _ different]
  have last : nullifierEntry descriptor.authorityNullifier ∈ ResourceBirthAuthority.entries descriptor := by
    simp [ResourceBirthAuthority.entries]
  exact CredentialAuthorityEffects.setAll_member _ _ prepared.birthReady.1 _ last

end Prepared

/-- info: 'Minidregg.Compiler.GrainResourceBirthAuthority.Prepared.birth_marker_consumed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Prepared.birth_marker_consumed
/-- info: 'Minidregg.Compiler.GrainResourceBirthAuthority.Prepared.birth_fields_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Prepared.birth_fields_preserved

end Minidregg.Compiler.GrainResourceBirthAuthority
