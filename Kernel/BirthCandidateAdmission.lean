/- Joint newborn source-graph validation, distinct from export-law evaluation.
The accepted authority batch supplies one post and all exact staged records.
Sealed or unsatisfiable new local laws remain legal sources. -/
module

public import Compiler.ServedBasis
public import Compiler.CandidateLawResolution
public import Compiler.PhysicalLawResolution
public import Compiler.CredentialAuthorityDomainReceiver

@[expose] public section

namespace Minidregg.Kernel.BirthCandidateAdmission

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Compiler.ServedBasis (Ground)
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry

set_option autoImplicit false

abbrev Deployment := CanonicalCellRegistry.Deployment

/-- Exclude exactly the sources staged by this same birth. Existing selected
heads and every predecessor fetched for a pin remain physical dependencies. -/
def existingAddresses (records : List PolicyRecord) (addresses : List Digest) : List Digest :=
  addresses.filter fun address => !(records.map policyRecordDigest).contains address

def physicalGuards (pairs : List (Nat × Digest)) : List ReadGuard :=
  pairs.map fun pair => ⟨⟨pair.1⟩, pair.2⟩

variable {F : Type} [Field F]

structure Checked (profile : PolicyCompilerProfile F) (deployment : Deployment)
    (ground : Ground deployment)
    (post : CredentialAuthorityDomain.Cell) (records : List PolicyRecord) where
  private mk ::
  graph : PolicyComponentResolution.LoadedRoots
    (CredentialAuthorityDomain.Snapshot.ofCell ground.authority.domain ground.authority.revision
      ground.authority.spent post)
    (CandidateLawResolution.overlayRecords
      (PhysicalLawResolution.payloadStore ground.authority ground.directory) records)
    profile.semantics (CandidateLawResolution.changedRecordRoots records)
  graphExact : CandidateLawResolution.validateRecords ground.authority
    (PhysicalLawResolution.payloadStore ground.authority ground.directory) post profile.semantics records
    PhysicalLawResolution.resolutionBudget = .ok graph
  supported : Minidregg.Compiler.supported profile.compiler
    (ResolvedLawCompilation.predicate graph.resolved) = true
  sourceGuards : List (Nat × Digest)
  sourcesExact : PhysicalLawResolution.loadGuards ground.authority ground.directory
    (existingAddresses records (PhysicalLawResolution.addresses graph)) = some sourceGuards
  guardsExact : ∀ guard ∈ physicalGuards sourceGuards,
    guard.expectedRoot = ground.view.model.roots guard.cellId

def Checked.readGuards {profile : PolicyCompilerProfile F} {deployment : Deployment}
    {ground : Ground deployment}
    {post : CredentialAuthorityDomain.Cell} {records : List PolicyRecord}
    (checked : Checked profile deployment ground post records) : List ReadGuard :=
  physicalGuards checked.sourceGuards

def check (profile : PolicyCompilerProfile F) (deployment : Deployment)
    (ground : Ground deployment)
    (post : CredentialAuthorityDomain.Cell) (records : List PolicyRecord) :
    Option (Checked profile deployment ground post records) := do
  match graphExact : CandidateLawResolution.validateRecords ground.authority
      (PhysicalLawResolution.payloadStore ground.authority ground.directory) post profile.semantics records
      PhysicalLawResolution.resolutionBudget with
  | .error _ => none
  | .ok graph =>
      if supported : Minidregg.Compiler.supported profile.compiler
          (ResolvedLawCompilation.predicate graph.resolved) = true then do
        match sourcesExact : PhysicalLawResolution.loadGuards ground.authority ground.directory
            (existingAddresses records (PhysicalLawResolution.addresses graph)) with
        | none => none
        | some sourceGuards =>
            if guardsExact : ∀ guard ∈ physicalGuards sourceGuards,
                guard.expectedRoot = ground.view.model.roots guard.cellId then
              some ⟨graph, graphExact, supported, sourceGuards, sourcesExact, guardsExact⟩
            else none
      else none

/-- A dependency not staged by the joint birth cannot disappear from the
physical read set merely because another candidate has the same policy id. -/
theorem existingAddress_retained (records : List PolicyRecord) (addresses : List Digest)
    (address : Digest) (member : address ∈ addresses)
    (unstaged : address ∉ records.map policyRecordDigest) :
    address ∈ existingAddresses records addresses := by
  simp only [existingAddresses, List.mem_filter]
  exact ⟨member, by simpa using unstaged⟩

end Minidregg.Kernel.BirthCandidateAdmission
