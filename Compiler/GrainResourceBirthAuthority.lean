/-
The authority preparation shared by grain-backed birth authoring and receiving.
The marker supplied here must be derived and bound by the enclosing composite
source. This module grants no authorization and emits no durable intent.

The birth's grant batch is one patch of the one authority cell, each entry a
guarded assignment read at the store its prefix produced.  The birth's and the
composite operation's markers are both checked unspent in the durable consumed
set here and consumed there by the receiver's intent (`replayMarkers`); neither
is written to the cell.
-/
module

public import Compiler.CredentialAuthorityDomainReceiver

@[expose] public section

namespace Minidregg.Compiler.GrainResourceBirthAuthority

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState (layout)
open Minidregg.Theory.CredentialAuthorityEffects
  (assignAll setAll run_assignAll)
open Minidregg.Compiler

set_option autoImplicit false

def patch (snapshot : CredentialAuthorityDomain.Snapshot)
    (descriptor : Descriptor CanonicalCellRegistry.registry) : Patch layout :=
  assignAll snapshot.logical (ResourceBirthAuthority.entries descriptor)

/-- Both replay markers are checked unspent in the consumed set the OLD
authority snapshot carries (a ground answers them only when it declares them:
the controller refuses an undeclared marker before this); the batch is one patch of the cell. The checked birth grant template is retained
separately for the eventual birth policy admission. -/
structure Prepared {F : Type} [Field F]
    (profile : CanonicalPolicyAdmission.PolicyCompilerProfile F)
    (deployment : CanonicalCellRegistry.Deployment)
    (authority : CredentialAuthorityDomain.Snapshot)
    (descriptor : Descriptor CanonicalCellRegistry.registry) (operationMarker : Nat) where
  private mk ::
  markersDistinct : descriptor.authorityNullifier ≠ operationMarker
  initialSources : PolicySourceCell.CheckedInitials deployment.domain profile
    descriptor.initialPolicies
  birthReady : CredentialAuthorityDomainReceiver.BatchReady authority descriptor
  operationMarkerFresh : authority.spent operationMarker = false
  checked : CredentialAuthorityDomain.Prepared authority
    (patch authority descriptor)

def prepare {F : Type} [Field F]
    (profile : CanonicalPolicyAdmission.PolicyCompilerProfile F)
    (deployment : CanonicalCellRegistry.Deployment)
    (authority : CredentialAuthorityDomain.Snapshot)
    (descriptor : Descriptor CanonicalCellRegistry.registry) (operationMarker : Nat) :
    Option (Prepared profile deployment authority descriptor operationMarker) := do
  if distinct : descriptor.authorityNullifier ≠ operationMarker then
    let initialSources ← PolicySourceCell.checkInitials deployment.domain profile
      descriptor.initialPolicies
    if ready : CredentialAuthorityDomainReceiver.BatchReady authority descriptor then
      if fresh : authority.spent operationMarker = false then
        let checked ← CredentialAuthorityDomain.prepare authority
          (patch authority descriptor)
        some ⟨distinct, initialSources, ready, fresh, checked⟩
      else none
    else none
  else none

section Prepared

variable {F : Type} [Field F]
    {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : CanonicalCellRegistry.Deployment}
    {authority : CredentialAuthorityDomain.Snapshot}
    {descriptor : Descriptor CanonicalCellRegistry.registry} {operationMarker : Nat}

/-- The post authority cell of the combined patch. -/
def Prepared.post (prepared : Prepared profile deployment authority descriptor operationMarker) :
    CredentialAuthorityDomain.Cell :=
  prepared.checked.validated.apply

/-- Authority allocates no cells; the only auxiliary creates are the birth's
initial policy sources. -/
def Prepared.auxiliaryCreates
    (prepared : Prepared profile deployment authority descriptor operationMarker) :
    List (CreateRequest (CellId := Nat) CanonicalCellRegistry.registry) :=
  CanonicalCellRegistry.initialSourceCreates deployment.domain prepared.initialSources.records

theorem Prepared.post_logical
    (prepared : Prepared profile deployment authority descriptor operationMarker) :
    prepared.post.logical =
      setAll authority.logical (ResourceBirthAuthority.entries descriptor) := by
  change Patch.run authority.logical (patch authority descriptor) = _
  rw [patch, run_assignAll]

/-- **What a prepared grain-birth authority guarantees about its indices**: the birth's authority
nullifier differs from `operationMarker`, `descriptor` is batch-ready at the `authority`
snapshot (slots and grant ids distinct, initial policies fresh, the authority nullifier unspent,
every grant ready, parent rows absent), `operationMarker` is unspent there, and every initial policy
decodes to a record satisfying `InitialFacts` for `deployment`'s domain and `profile`. -/
theorem Prepared.sound
    (prepared : Prepared profile deployment authority descriptor operationMarker) :
    descriptor.authorityNullifier ≠ operationMarker ∧
      CredentialAuthorityDomainReceiver.BatchReady authority descriptor ∧
      authority.spent operationMarker = false ∧
      ∀ initial ∈ descriptor.initialPolicies, ∃ record,
        PolicyRecordCodec.decode initial.canonicalBytes = some record ∧
          PolicySourceCell.InitialFacts deployment.domain profile initial record :=
  ⟨prepared.markersDistinct, prepared.birthReady, prepared.operationMarkerFresh,
    fun initial member => by
      obtain ⟨record, _, decoded, facts⟩ := prepared.initialSources.record_of_member initial member
      exact ⟨record, decoded, facts⟩⟩

end Prepared

/-- info: 'Minidregg.Compiler.GrainResourceBirthAuthority.Prepared.post_logical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Prepared.post_logical

end Minidregg.Compiler.GrainResourceBirthAuthority
