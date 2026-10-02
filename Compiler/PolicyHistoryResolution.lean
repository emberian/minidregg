/-
# Compiler.PolicyHistoryResolution -- authenticated predecessor selection

The live authority table retains only the current revision address. Historical
pins therefore follow immutable source predecessors from an actual LoadedPolicy.
These edges authenticate old records; they are not law-inheritance edges.

This same-profile loader does not cross a checked-carry boundary. Such a boundary
requires the carry lane's explicit authenticated source mapping and prior codec.
-/
import Compiler.CredentialAuthorityPolicyRegistry

namespace Minidregg.Compiler.PolicyHistoryResolution

open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Kernel.CanonicalPolicyRegistry
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- Every predecessor coordinate is checked against the selected newer record;
the fetched bytes have canonical spelling and their recomputed address matches. -/
structure Previous (store : PayloadStore) (newer : CommittedPolicy) where
  committed : CommittedPolicy
  link : newer.record.previous = some committed.address
  revision : committed.record.version + 1 = newer.record.version
  identifier : committed.record.policyId = newer.record.policyId
  domain : committed.record.domain = newer.record.domain
  semantics : committed.record.semantics = newer.record.semantics
  digest : policyRecordDigest committed.record = committed.address
  fetched : store.fetch committed.address = some (policyRecordCodec.encode committed.record)

def loadPrevious (store : PayloadStore) (newer : CommittedPolicy) :
    Option (Previous store newer) :=
  match link : newer.record.previous with
  | none => none
  | some address =>
      match fetched : store.fetch address with
      | none => none
      | some bytes =>
          match decoded : policyRecordCodec.decode bytes with
          | none => none
          | some record =>
              if checked : record.version + 1 = newer.record.version ∧
                  record.policyId = newer.record.policyId ∧
                  record.domain = newer.record.domain ∧
                  record.semantics = newer.record.semantics ∧
                  policyRecordDigest record = address then
                some
                  { committed := ⟨address, record⟩
                    link := link
                    revision := checked.1
                    identifier := checked.2.1
                    domain := checked.2.2.1
                    semantics := checked.2.2.2.1
                    digest := checked.2.2.2.2
                    fetched := by
                      have canonical := policyRecordCodec_canonical decoded
                      simpa only [canonical] using fetched }
              else none

/-- A finite chain rooted at the actually authenticated current head. -/
inductive Historical (store : PayloadStore) (head : CommittedPolicy) : CommittedPolicy → Prop
  | current : Historical store head head
  | previous {newer : CommittedPolicy} (earlier : Historical store head newer)
      (step : Previous store newer) : Historical store head step.committed

structure Selected (store : PayloadStore) (head : CommittedPolicy)
    (revision : PolicyRevision) (address : Digest) where
  committed : CommittedPolicy
  history : Historical store head committed
  revisionExact : committed.record.version = revision
  addressExact : committed.address = address

private def descend (store : PayloadStore) (head : CommittedPolicy)
    (revision : PolicyRevision) (address : Digest) :
    Nat → (current : CommittedPolicy) → Historical store head current →
      Option (Selected store head revision address)
  | 0, _, _ => none
  | fuel + 1, current, history =>
      if revisionExact : current.record.version = revision then
        if addressExact : current.address = address then
          some ⟨current, history, revisionExact, addressExact⟩
        else none
      else if revision < current.record.version then
        match loadPrevious store current with
        | none => none
        | some earlier =>
            descend store head revision address fuel earlier.committed
              (.previous history earlier)
      else none

/-- Public pin selection starts from the actual current snapshot resolver, not
an arbitrary caller-selected blob. Fuel follows strictly descending revisions. -/
def loadPinned {snapshot : Snapshot} {store : PayloadStore}
    {policyId : PolicyId} {currentRevision : PolicyRevision}
    (head : LoadedPolicy snapshot store policyId currentRevision)
    (revision : PolicyRevision) (address : Digest) :
    Option (Selected store head.committed revision address) :=
  descend store head.committed revision address (head.committed.record.version + 1)
    head.committed .current

/-- Pin selection never turns a revision mismatch into a winner-selection rule. -/
theorem selected_revision_exact {store : PayloadStore} {head : CommittedPolicy}
    {revision : PolicyRevision} {address : Digest}
    (selected : Selected store head revision address) :
    selected.committed.record.version = revision := selected.revisionExact

theorem selected_address_exact {store : PayloadStore} {head : CommittedPolicy}
    {revision : PolicyRevision} {address : Digest}
    (selected : Selected store head revision address) :
    selected.committed.address = address := selected.addressExact

end Minidregg.Compiler.PolicyHistoryResolution
