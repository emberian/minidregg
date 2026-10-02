/- Canonical physical source guards for the shared authenticated law closure. -/
import Compiler.CanonicalCellRegistry
import Compiler.ComposedPolicyAdmission

namespace Minidregg.Compiler.PhysicalLawResolution

open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.LawComposition
open Minidregg.Theory.PermanentCellAllocation
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.PolicyComponentResolution
open Minidregg.Kernel.CanonicalPolicyRegistry

set_option autoImplicit false

def payloadStore (snapshot : Snapshot)
    (directory : Directory Nat CanonicalCellRegistry.registry) : PayloadStore :=
  ⟨CanonicalCellRegistry.fetchPolicySource snapshot.domain directory⟩

/-- Includes every actual historical predecessor read, not only the pin and
head. Parentage and head selection also require the receiver's authority guard. -/
def addresses {snapshot : Snapshot} {store : PayloadStore} {semantics : Digest}
    {refs : List PolicyRef} (graph : LoadedRoots snapshot store semantics refs) : List Digest :=
  (graph.sources.flatMap fun loaded =>
    loaded.source.history.records.map CommittedPolicy.address).eraseDups

def loadGuards (snapshot : Snapshot)
    (directory : Directory Nat CanonicalCellRegistry.registry)
    (addresses : List Digest) : Option (List (Nat × Digest)) :=
  addresses.mapM fun address => do
    let source ← CanonicalCellRegistry.loadPolicySource snapshot.domain directory address
    pure source.readGuard

structure GuardedRoots (snapshot : Snapshot)
    (directory : Directory Nat CanonicalCellRegistry.registry)
    (semantics : Digest) (refs : List PolicyRef) where
  graph : LoadedRoots snapshot (payloadStore snapshot directory) semantics refs
  sourceGuards : List (Nat × Digest)
  guardsExact : loadGuards snapshot directory (addresses graph) = some sourceGuards

def loadRoots (snapshot : Snapshot)
    (directory : Directory Nat CanonicalCellRegistry.registry)
    (semantics : Digest) (refs : List PolicyRef) (budget : Nat) :
    Option (GuardedRoots snapshot directory semantics refs) := do
  let graph ← (PolicyComponentResolution.loadRoots snapshot (payloadStore snapshot directory)
    semantics refs budget).toOption
  match exact : loadGuards snapshot directory (addresses graph) with
  | none => none
  | some guards => pure ⟨graph, guards, exact⟩

def loadTarget (snapshot : Snapshot)
    (directory : Directory Nat CanonicalCellRegistry.registry)
    (semantics : Digest) (target budget : Nat) (additional : List PolicyRef := []) :
    Option (GuardedRoots snapshot directory semantics (targetRoots snapshot target additional)) :=
  loadRoots snapshot directory semantics (targetRoots snapshot target additional) budget

end Minidregg.Compiler.PhysicalLawResolution
