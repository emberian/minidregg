/- Joint newborn source-graph validation, distinct from export-law evaluation.
The accepted authority batch supplies one post and all exact staged records.
Sealed or unsatisfiable new local laws remain legal sources. -/
import Compiler.CandidateLawResolution
import Compiler.PhysicalLawResolution
import Compiler.CredentialAuthorityDomainReceiver

namespace Minidregg.Kernel.BirthCandidateAdmission

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry

set_option autoImplicit false

abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes

/-- Exclude exactly the sources staged by this same birth. Existing selected
heads and every predecessor fetched for a pin remain physical dependencies. -/
def existingAddresses (records : List PolicyRecord) (addresses : List Digest) : List Digest :=
  addresses.filter fun address => !(records.map policyRecordDigest).contains address

def physicalGuards (pairs : List (Nat × Digest)) : List ReadGuard :=
  pairs.map fun pair => ⟨⟨pair.1⟩, pair.2⟩

variable {F : Type} [Field F]

structure Checked (profile : PolicyCompilerProfile F) (deployment : Deployment)
    (durable : Durable) (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (post : CredentialAuthorityDomain.Cell) (records : List PolicyRecord) where
  private mk ::
  graph : PolicyComponentResolution.LoadedRoots
    (CredentialAuthorityDomain.Snapshot.ofCell authority.snapshot.domain authority.snapshot.revision
      authority.snapshot.spent post)
    (CandidateLawResolution.overlayRecords
      (PhysicalLawResolution.payloadStore authority.snapshot directory.directory) records)
    profile.semantics (CandidateLawResolution.changedRecordRoots records)
  graphExact : CandidateLawResolution.validateRecords authority.snapshot
    (PhysicalLawResolution.payloadStore authority.snapshot directory.directory) post profile.semantics records
    PhysicalLawResolution.resolutionBudget = .ok graph
  supported : Minidregg.Compiler.supported profile.compiler
    (ResolvedLawCompilation.predicate graph.resolved) = true
  sourceGuards : List (Nat × Digest)
  sourcesExact : PhysicalLawResolution.loadGuards authority.snapshot directory.directory
    (existingAddresses records (PhysicalLawResolution.addresses graph)) = some sourceGuards
  guardsExact : ∀ guard ∈ physicalGuards sourceGuards,
    guard.expectedRoot = durable.snapshot.model.roots guard.cellId

def Checked.readGuards {profile : PolicyCompilerProfile F} {deployment : Deployment}
    {durable : Durable} {directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot}
    {post : CredentialAuthorityDomain.Cell} {records : List PolicyRecord}
    (checked : Checked profile deployment durable directory authority post records) : List ReadGuard :=
  physicalGuards checked.sourceGuards

def check (profile : PolicyCompilerProfile F) (deployment : Deployment)
    (durable : Durable) (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (post : CredentialAuthorityDomain.Cell) (records : List PolicyRecord) :
    Option (Checked profile deployment durable directory authority post records) := do
  match graphExact : CandidateLawResolution.validateRecords authority.snapshot
      (PhysicalLawResolution.payloadStore authority.snapshot directory.directory) post profile.semantics records
      PhysicalLawResolution.resolutionBudget with
  | .error _ => none
  | .ok graph =>
      if supported : Minidregg.Compiler.supported profile.compiler
          (ResolvedLawCompilation.predicate graph.resolved) = true then do
        match sourcesExact : PhysicalLawResolution.loadGuards authority.snapshot directory.directory
            (existingAddresses records (PhysicalLawResolution.addresses graph)) with
        | none => none
        | some sourceGuards =>
            if guardsExact : ∀ guard ∈ physicalGuards sourceGuards,
                guard.expectedRoot = durable.snapshot.model.roots guard.cellId then
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
