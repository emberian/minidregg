/- Validate exactly the proposed policy head against a source-owned candidate
snapshot. This check supplies no authority: the old management law must first
admit the update. Deliberately unsatisfiable intersections remain meaningful. -/
import Compiler.PolicyComponentResolution

namespace Minidregg.Compiler.CandidateLawResolution

open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.LawComposition
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.PolicyComponentResolution
open Minidregg.Kernel.CanonicalPolicyRegistry

set_option autoImplicit false

/-- Only exact source bytes of the signed prepared candidate are overlaid. This
is not an alternate resolver accepted from the request. -/
def overlay (store : PayloadStore) (record : PolicyRecord) : PayloadStore where
  fetch address := if address = policyRecordDigest record then
    some (policyRecordCodec.encode record) else store.fetch address

def changedRoots (record : PolicyRecord) : List PolicyRef :=
  [⟨record.policyId, .local, .head⟩, ⟨record.policyId, .descendants, .head⟩]

/-- The controller supplies its validated post authority cell. Both source
facets are checked, including exports that the local law itself does not use.
No old downstream client must remain satisfiable after this update. -/
def validate (snapshot : Snapshot) (store : PayloadStore)
    (post : CredentialAuthorityDomain.Cell) (record : PolicyRecord) (budget : Nat) :
    Except PolicyComponentResolution.Refusal (LoadedRoots
      (CredentialAuthorityDomain.Snapshot.ofCell snapshot.domain snapshot.revision snapshot.spent post)
      (overlay store record) record.semantics (changedRoots record)) :=
  loadRoots
    (CredentialAuthorityDomain.Snapshot.ofCell snapshot.domain snapshot.revision snapshot.spent post)
    (overlay store record) record.semantics (changedRoots record) budget

/-- A simultaneous candidate source map for one accepted birth batch. Every
staged head can resolve every other staged source, independent of list order.
The birth allocator separately enforces unique fresh physical source addresses. -/
def overlayRecords (store : PayloadStore) (records : List PolicyRecord) : PayloadStore where
  fetch address :=
    match records.find? (fun record => policyRecordDigest record == address) with
    | some record => some (policyRecordCodec.encode record)
    | none => store.fetch address

def changedRecordRoots (records : List PolicyRecord) : List PolicyRef :=
  records.flatMap changedRoots

/-- All new local/export facets resolve against the one actual joint post.
Graph well-formedness is checked without evaluating the new restrictions. -/
def validateRecords (snapshot : Snapshot) (store : PayloadStore)
    (post : CredentialAuthorityDomain.Cell) (semantics : Digest)
    (records : List PolicyRecord) (budget : Nat) :
    Except PolicyComponentResolution.Refusal (LoadedRoots
      (CredentialAuthorityDomain.Snapshot.ofCell snapshot.domain snapshot.revision snapshot.spent post)
      (overlayRecords store records) semantics (changedRecordRoots records)) :=
  loadRoots
    (CredentialAuthorityDomain.Snapshot.ofCell snapshot.domain snapshot.revision snapshot.spent post)
    (overlayRecords store records) semantics (changedRecordRoots records) budget

end Minidregg.Compiler.CandidateLawResolution
