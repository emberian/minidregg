/- A present-tense authorization to add the first next-key commitment.
This neither rotates a key nor asserts that the commitment existed earlier. -/
import Theory.KeyPreRotation

namespace Minidregg.Theory.KeyCommitmentAdoption
open TypedAuthorization CredentialSigningKey CredentialAuthorityState Store
set_option autoImplicit false

structure Adoption where
  subject : SubjectId
  expectedCurrent : KeyRecord
  nextPublicKey : List UInt8
  deriving DecidableEq, Repr

/-- The existing signer must still be selected, live, and active now. -/
def Eligible (logical : Store layout) (revision : Nat) (adoption : Adoption) : Prop :=
  currentSigningKey logical adoption.subject = some adoption.expectedCurrent ∧
  adoption.expectedCurrent.nextKeyDigest = none ∧
  logical ⟨.registered, signingKeyRevocation adoption.expectedCurrent⟩ = some () ∧
  logical ⟨.revoked, signingKeyRevocation adoption.expectedCurrent⟩ = none ∧
  adoption.expectedCurrent.algorithm = 1 ∧
  adoption.expectedCurrent.publicKey.length = 32 ∧
  adoption.expectedCurrent.activeFrom ≤ revision ∧ revision ≤ adoption.expectedCurrent.activeUntil ∧
  adoption.nextPublicKey.length = 32 ∧ adoption.nextPublicKey ≠ adoption.expectedCurrent.publicKey

instance (logical : Store layout) (revision : Nat) (adoption : Adoption) :
    Decidable (Eligible logical revision adoption) := by unfold Eligible; infer_instance

inductive Reject where
  | ineligible | currentNotSigned | nextNotSigned
  deriving DecidableEq, Repr

def gate (logical : Store layout) (revision : Nat) (adoption : Adoption)
    (currentSigned nextSigned : List UInt8 → Bool) : Except Reject Unit :=
  if Eligible logical revision adoption then
    if currentSigned adoption.expectedCurrent.publicKey then
      if nextSigned adoption.nextPublicKey then .ok () else .error .nextNotSigned
    else .error .currentNotSigned
  else .error .ineligible

theorem gate_ok_iff (logical : Store layout) (revision : Nat) (adoption : Adoption)
    (currentSigned nextSigned : List UInt8 → Bool) :
    gate logical revision adoption currentSigned nextSigned = .ok () ↔
      Eligible logical revision adoption ∧
      currentSigned adoption.expectedCurrent.publicKey = true ∧
      nextSigned adoption.nextPublicKey = true := by
  unfold gate
  split_ifs <;> simp_all

def adopted (digestOf : List UInt8 → Digest) (adoption : Adoption) : KeyRecord :=
  { adoption.expectedCurrent with nextKeyDigest := some (digestOf adoption.nextPublicKey) }

/-- Exactly one guarded row changes; no epoch pointer or revocation is edited. -/
def patch (digestOf : List UInt8 → Digest) (adoption : Adoption) : Patch layout :=
  [.write .subjectKey (adoption.subject, adoption.expectedCurrent.keyEpoch)
    adoption.expectedCurrent (adopted digestOf adoption)]

def post (digestOf : List UInt8 → Digest) (logical : Store layout) (adoption : Adoption) : Store layout :=
  Patch.run logical (patch digestOf adoption)

theorem post_eq (digestOf : List UInt8 → Digest) (logical : Store layout) (adoption : Adoption) :
    post digestOf logical adoption = logical.set
      ⟨.subjectKey, (adoption.subject, adoption.expectedCurrent.keyEpoch)⟩ (some (adopted digestOf adoption)) := by
  simp [post, patch, Patch.run, Op.apply]

theorem post_frame (digestOf : List UInt8 → Digest) (logical : Store layout) (adoption : Adoption)
    (address : Address layout)
    (other : address ≠ ⟨.subjectKey, (adoption.subject, adoption.expectedCurrent.keyEpoch)⟩) :
    post digestOf logical adoption address = logical address := by
  rw [post_eq, Store.set_ne _ _ _ _ other]

theorem post_current (digestOf : List UInt8 → Digest) (logical : Store layout) (adoption : Adoption)
    (selected : currentSigningKey logical adoption.subject = some adoption.expectedCurrent) :
    currentSigningKey (post digestOf logical adoption) adoption.subject = some (adopted digestOf adoption) := by
  obtain ⟨subject, epoch, record⟩ := KeyPreRotation.currentSigningKey_facts selected
  have sameSubject : (⟨(adopted digestOf adoption).subject⟩ : SubjectId) = adoption.subject := by
    simp only [adopted]; cases adoption.subject; simp_all
  have result := currentSigningKey_exact (post digestOf logical adoption) (adopted digestOf adoption)
    (by rw [sameSubject]; simpa [adopted, post_eq, Store.set_ne] using epoch)
    (by rw [sameSubject]; simpa [adopted, post_eq] using
      Store.set_eq logical ⟨.subjectKey, (adoption.subject, adoption.expectedCurrent.keyEpoch)⟩
        (some (adopted digestOf adoption)))
  rwa [sameSubject] at result

theorem identity_preserved (digestOf : List UInt8 → Digest) (adoption : Adoption) :
    (adopted digestOf adoption).subject = adoption.expectedCurrent.subject ∧
    (adopted digestOf adoption).keyId = adoption.expectedCurrent.keyId ∧
    (adopted digestOf adoption).keyEpoch = adoption.expectedCurrent.keyEpoch ∧
    (adopted digestOf adoption).publicKey = adoption.expectedCurrent.publicKey ∧
    (adopted digestOf adoption).algorithm = adoption.expectedCurrent.algorithm ∧
    (adopted digestOf adoption).activeFrom = adoption.expectedCurrent.activeFrom ∧
    (adopted digestOf adoption).activeUntil = adoption.expectedCurrent.activeUntil := by
  simp [adopted]

theorem existing_commitment_refused (logical : Store layout) (revision : Nat) (adoption : Adoption)
    (present : adoption.expectedCurrent.nextKeyDigest ≠ none) (currentSigned nextSigned : List UInt8 → Bool) :
    gate logical revision adoption currentSigned nextSigned = .error .ineligible := by
  simp [gate, Eligible, present]

theorem stale_record_refused (logical : Store layout) (revision : Nat) (adoption : Adoption)
    (stale : currentSigningKey logical adoption.subject ≠ some adoption.expectedCurrent)
    (currentSigned nextSigned : List UInt8 → Bool) :
    gate logical revision adoption currentSigned nextSigned = .error .ineligible := by
  simp [gate, Eligible, stale]

theorem current_signature_required (logical : Store layout) (revision : Nat) (adoption : Adoption)
    (eligible : Eligible logical revision adoption) (currentSigned nextSigned : List UInt8 → Bool)
    (absent : currentSigned adoption.expectedCurrent.publicKey = false) :
    gate logical revision adoption currentSigned nextSigned = .error .currentNotSigned := by
  simp [gate, eligible, absent]

theorem next_signature_required (logical : Store layout) (revision : Nat) (adoption : Adoption)
    (eligible : Eligible logical revision adoption) (currentSigned nextSigned : List UInt8 → Bool)
    (current : currentSigned adoption.expectedCurrent.publicKey = true)
    (absent : nextSigned adoption.nextPublicKey = false) :
    gate logical revision adoption currentSigned nextSigned = .error .nextNotSigned := by
  simp [gate, eligible, current, absent]

/-- The existing rotation gate consumes the new commitment without any
change to its authority rule. A successor still needs its own next commitment
and its own possession signature. -/
theorem adoption_enables_rotation (digestOf : List UInt8 → Digest)
    (logical : Store layout) (revision : Nat) (adoption : Adoption)
    (currentSigned nextSigned : List UInt8 → Bool)
    (accepted : gate logical revision adoption currentSigned nextSigned = .ok ())
    (rotation : KeyPreRotation.Rotation)
    (sameSubject : rotation.subject = adoption.subject)
    (sameNext : rotation.key.publicKey = adoption.nextPublicKey)
    (successor : KeyPreRotation.Successor (adopted digestOf adoption) rotation)
    (commits : rotation.key.nextKeyDigest.isSome = true)
    (signed : List UInt8 → Bool) (possession : signed rotation.key.publicKey = true) :
    KeyPreRotation.gate digestOf (post digestOf logical adoption) rotation signed =
      .ok (adopted digestOf adoption) := by
  have eligibility := ((gate_ok_iff _ _ _ _ _).1 accepted).1
  apply (KeyPreRotation.gate_ok_iff _ _ _ _ _).2
  exact ⟨sameSubject ▸ post_current digestOf logical adoption eligibility.1,
    by simp [adopted, sameNext], successor, commits, possession⟩

namespace Witness
private def daily := List.replicate 32 (1 : UInt8)
private def next := List.replicate 32 (2 : UInt8)
private def old : KeyRecord := ⟨17, 4, 1, 9, daily, 0, 100, none⟩
private def adoption : Adoption := ⟨⟨9⟩, old, next⟩
private def store : Store layout :=
  (((0 : Store layout).set ⟨.subjectKeyEpoch, ⟨9⟩⟩ (some 4)).set
    ⟨.subjectKey, (⟨9⟩, 4)⟩ (some old)).set ⟨.registered, .signingKey ⟨9⟩ 4⟩ (some ())
private def yes : List UInt8 → Bool := fun _ => true
private def digestOf (_ : List UInt8) : Digest := ⟨77⟩
theorem admitted : gate store 7 adoption yes yes = .ok () := by decide
theorem no_current_signature : gate store 7 adoption (fun _ => false) yes = .error .currentNotSigned := by decide
theorem no_next_possession : gate store 7 adoption yes (fun _ => false) = .error .nextNotSigned := by decide
theorem patch_valid : Patch.ValidFrom store (patch digestOf adoption) := by decide
theorem same_key_committed : currentSigningKey (post digestOf store adoption) ⟨9⟩ =
    some { old with nextKeyDigest := some ⟨77⟩ } := by decide
theorem replay_not_fresh : gate (post digestOf store adoption) 8 adoption yes yes = .error .ineligible := by decide
theorem wrong_subject : gate store 7 { adoption with subject := ⟨10⟩ } yes yes = .error .ineligible := by decide
theorem revoked : gate (store.set ⟨.revoked, .signingKey ⟨9⟩ 4⟩ (some ())) 7 adoption yes yes =
    .error .ineligible := by decide
theorem same_key_refused : gate store 7 { adoption with nextPublicKey := daily } yes yes =
    .error .ineligible := by decide
theorem expired : gate store 101 adoption yes yes = .error .ineligible := by decide
end Witness

#assert_axioms gate_ok_iff
#assert_axioms post_current
#assert_axioms adoption_enables_rotation
#assert_axioms identity_preserved
#assert_axioms post_frame
#assert_axioms Witness.admitted
#assert_axioms Witness.patch_valid
#assert_axioms Witness.replay_not_fresh
end Minidregg.Theory.KeyCommitmentAdoption
