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
import Compiler.CredentialAuthorityDomainReceiver

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

/-- Both replay markers are checked unspent in the durable consumed set the
OLD authority snapshot was loaded with; the batch is one patch of the cell. The checked birth grant template is retained
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
  operationMarkerFresh : loaded.snapshot.spent operationMarker = false
  checked : CredentialAuthorityDomain.Prepared loaded.snapshot
    (patch loaded.snapshot descriptor)

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
      if fresh : loaded.snapshot.spent operationMarker = false then
        let checked ← CredentialAuthorityDomain.prepare loaded.snapshot
          (patch loaded.snapshot descriptor)
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
      setAll loaded.snapshot.logical (ResourceBirthAuthority.entries descriptor) := by
  change Patch.run loaded.snapshot.logical (patch loaded.snapshot descriptor) = _
  rw [patch, run_assignAll]

end Prepared

/-- info: 'Minidregg.Compiler.GrainResourceBirthAuthority.Prepared.post_logical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Prepared.post_logical

end Minidregg.Compiler.GrainResourceBirthAuthority
