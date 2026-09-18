/-
# Compiler.CredentialAuthorityPageProbe -- inhabitation and authority teeth

These are concrete poles for the actual page projection and shared capability
admission relation. They do not fabricate a signature verifier or claim that
birth is authorized merely because the newly created owner cap is usable.
The insertion batch is a representation operation; the outer accepted effect
must authorize it against the original shared pre-state.
-/
import Compiler.CredentialAuthorityPageMaterializer

namespace Minidregg.Compiler.CredentialAuthorityPageProbe

open Minidregg.Compiler.CredentialAuthorityPageMaterializer
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

def ownerStored : StoredCapability .object := ⟨demoCapability, []⟩
def ownerEntry : Entry := .capability .object ownerStored

def ownerPage : Page where
  authorityDomain := ⟨9200⟩
  pageNumber := 0
  slot0 := some ownerEntry
  slot1 := some (.policy demoCapability.policyId demoCapability.policyEpoch ⟨9201⟩)
  slot2 := some (.issuerEpoch demoCapability.issuer demoCapability.issuerEpoch)
  slot3 := some (.subjectKeyEpoch demoRequest.subject demoRequest.subjectKeyEpoch)

theorem ownerPage_valid : ownerPage.Valid := by decide

theorem owner_entry_exact :
    ownerPage.readCapability .object demoCapability.id = some ownerStored :=
  ownerPage.capability_exact ownerPage_valid .object ownerStored (by decide)

theorem owner_lineage_valid : LineageValid ownerStored :=
  .root demoCapability rfl rfl rfl

theorem owner_issuer_exact :
    ownerPage.issuerEpochAt demoCapability.issuer = demoCapability.issuerEpoch :=
  ownerPage.issuerEpoch_exact ownerPage_valid _ _ (by decide)

theorem owner_subject_key_exact :
    ownerPage.subjectKeyEpochAt demoRequest.subject = demoRequest.subjectKeyEpoch :=
  ownerPage.subjectKeyEpoch_exact ownerPage_valid _ _ (by decide)

theorem owner_policy_exact :
    ownerPage.policyEpochAt demoCapability.policyId = demoCapability.policyEpoch := by
  simp [Page.policyEpochAt, Page.toCanonicalState, Page.entries, ownerPage,
    ownerEntry, ownerStored, Entry.install, demoCapability]
  rfl

theorem owner_revoked_empty : ownerPage.revoked = ∅ := by
  simp [Page.revoked, Page.entries, ownerPage, ownerEntry, Entry.revokedKey?]

/-- Positive semantic capability admission reads epochs from committed page
data; the root parameter is not a substitute for any signature premise. -/
theorem owner_admissible (root : Digest) :
    demoCapability.Admissible (ownerPage.authState root) demoRequest := by
  refine
    { holder := demoCapability_admissible.holder
      scope := demoCapability_admissible.scope
      validFrom := demoCapability_admissible.validFrom
      validUntil := demoCapability_admissible.validUntil
      policyId := demoCapability_admissible.policyId
      policyEpoch := demoCapability_admissible.policyEpoch
      policyCurrent := owner_policy_exact.symm
      issuerCurrent := owner_issuer_exact.symm
      selfNotRevoked := ?_
      ancestorNotRevoked := ?_
      channelNotRevoked := ?_ }
  · simp [Page.authState, owner_revoked_empty]
  · intro ancestor member
    simp [Page.authState, owner_revoked_empty]
  · intro channel member
    simp [Page.authState, owner_revoked_empty]

/-- The same committed owner capability refuses a different subject. -/
theorem other_subject_refused (root : Digest) :
    ¬ demoCapability.Admissible (ownerPage.authState root)
      { demoRequest with subject := ⟨99⟩ } := by
  intro admitted
  have holder := admitted.holder
  simp [demoCapability, Holder.Covers] at holder

theorem other_target_refused (root : Digest) :
    ¬ demoCapability.Admissible (ownerPage.authState root)
      (demoRequest.retarget demoOtherTarget) :=
  target_substitution_rejected demoCapability _ _ _ (by decide)

def rotatedOwnerPage : Page :=
  { ownerPage with slot2 := some (.issuerEpoch demoCapability.issuer 4) }

theorem rotatedOwnerPage_valid : rotatedOwnerPage.Valid := by decide

theorem rotated_issuer_exact :
    rotatedOwnerPage.issuerEpochAt demoCapability.issuer = 4 :=
  rotatedOwnerPage.issuerEpoch_exact rotatedOwnerPage_valid _ _ (by decide)

/-- A real issuer-epoch change in the page invalidates the old grant. -/
theorem rotated_issuer_refused (root : Digest) :
    ¬ demoCapability.Admissible (rotatedOwnerPage.authState root) demoRequest := by
  intro admitted
  have current := admitted.issuerCurrent
  change demoCapability.issuerEpoch =
    rotatedOwnerPage.issuerEpochAt demoCapability.issuer at current
  rw [rotated_issuer_exact] at current
  contradiction

def preIssuePage : Page :=
  { ownerPage with slot0 := none, slot3 := none }

def issuedPage : Page :=
  { preIssuePage with
      slot0 := some ownerEntry
      slot3 := some (.nullifier 81 true) }

theorem preIssuePage_valid : preIssuePage.Valid := by decide
theorem issuedPage_valid : issuedPage.Valid := by decide

/-- A capability and its single-use marker arrive in one returned page. -/
theorem issue_batch_complete :
    preIssuePage.admitInsertMany [ownerEntry, .nullifier 81 true] =
      .ok ⟨issuedPage, issuedPage_valid⟩ := by decide

theorem issued_capability_exact :
    issuedPage.readCapability .object demoCapability.id = some ownerStored :=
  issuedPage.capability_exact issuedPage_valid .object ownerStored (by decide)

theorem issued_marker_exact : issuedPage.isNullified 81 = true :=
  issuedPage.nullifier_exact issuedPage_valid 81 true (by decide)

theorem issued_marker_not_fresh : issuedPage.isNullified 81 ≠ false := by
  rw [issued_marker_exact]
  decide

/-- Repeating a capability in a single batch is refused, before any partial
page can be exposed. Capacity exhaustion is likewise explicit. -/
theorem duplicate_grant_refused :
    preIssuePage.admitInsertMany [ownerEntry, ownerEntry] =
      .error .addressConflict := by decide

def forgedOwnerEntry : Entry :=
  .capability .object ⟨{ demoCapability with holder := .bearer }, []⟩

/-- A distinct payload with the same capability address is also a conflict;
checking equality of the complete records alone would miss this case. -/
theorem conflicting_holder_grant_refused :
    preIssuePage.admitInsertMany [ownerEntry, forgedOwnerEntry] =
      .error .addressConflict := by decide

theorem owner_page_overflow_refused :
    ownerPage.admitInsertMany [.nullifier 81 true] = .error .full := by decide

theorem owner_state_roundtrip :
    stateCodec.decode (stateCodec.encode (stateOfOption (some ownerPage))) =
      some (stateOfOption (some ownerPage)) :=
  stateCodec.decode_encode _

def main : IO Unit := do
  let bytes := stateCodec.encode (stateOfOption (some ownerPage))
  let exact := match stateCodec.decode bytes with
    | some state => decide (pageAt state = some ownerPage)
    | none => false
  IO.println s!"authority-page-v2 bytes={bytes.length} exact-roundtrip={exact}"
  IO.println s!"owner-capability={decide (ownerPage.readCapability .object demoCapability.id = some ownerStored)}"
  IO.println s!"issuer-epoch={ownerPage.issuerEpochAt demoCapability.issuer} subject-key-epoch={ownerPage.subjectKeyEpochAt demoRequest.subject}"
  IO.println s!"issue-marker={issuedPage.isNullified 81} duplicate-grant-refused={decide (preIssuePage.admitInsertMany [ownerEntry, ownerEntry] = .error .addressConflict)}"

/-- info: 'Minidregg.Compiler.CredentialAuthorityPageProbe.owner_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms owner_admissible
/-- info: 'Minidregg.Compiler.CredentialAuthorityPageProbe.conflicting_holder_grant_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms conflicting_holder_grant_refused

end Minidregg.Compiler.CredentialAuthorityPageProbe
