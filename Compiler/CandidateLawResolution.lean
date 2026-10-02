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

end Minidregg.Compiler.CandidateLawResolution
