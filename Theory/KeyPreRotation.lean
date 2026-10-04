/-
# Theory.KeyPreRotation -- KERI-style key pre-rotation on the authority cell

Every signing-key record may commit to the digest of the subject's NEXT public
key (`KeyRecord.nextKeyDigest`).  A rotation names the new key record (whose own
`nextKeyDigest` commits to the key after it) and is admitted iff

* the subject's current record (`currentSigningKey`) carries a commitment,
* the new public key's digest IS that commitment,
* the new record is the current one's successor (same subject, same key line
  `keyId`, epoch + 1) and itself commits to a next key, and
* a signature by the NEW key over the rotation's possession frame verifies.

The current key's signature is neither necessary nor sufficient: `gate` never
consults the signature oracle at any key but the new one
(`gate_signatures_only_at_new_key`), so a thief holding the current daily key
cannot rotate to a key of its own (`rotate_current_keys_irrelevant`).  A
subject enrolled without a commitment cannot rotate at all
(`no_prerotation_subject_unchanged`), which is what every subject could do
before rotation existed.

The accepted rotation writes exactly the subject's key rows: the current-epoch
pointer moves to the successor, the successor's record and registration are
allocated, and the old key version is revoked in the append-only `revoked`
plane.  Capabilities bind a `Holder.subject`, never a key, and no capability,
issuer, policy or other subject's row is in the patch's footprint
(`grants_survive_rotation`, `rotation_preserves_other_subjects`).

`digestOf` is a parameter here; the host instantiates it with cSHAKE256 under
the tag `DREGG.SIGNING-KEY.NEXT/v1` (`Kernel.Receivers.SubjectKeyRotation`'s `nextKeyDigest`).
"The digest pins the key" is its collision resistance; nothing below assumes it:
the theorems are stated over digest (in)equality, as admission is.
-/
import Theory.CredentialAuthorityState
import Theory.AssertAxioms

namespace Minidregg.Theory.KeyPreRotation

open TypedAuthorization
open CredentialSigningKey
open CredentialAuthorityState
open Minidregg.Theory.Store

set_option autoImplicit false

/-- One rotation event: the subject and its complete successor key record. -/
structure Rotation where
  subject : SubjectId
  key : KeyRecord
  deriving DecidableEq, Repr

inductive Reject where
  /-- The subject has no current key (unenrolled, or a keyless epoch). -/
  | noCurrentKey
  /-- The current record carries no commitment: the subject enrolled without
  pre-rotation, and such a subject cannot rotate. -/
  | notPrerotated
  /-- The new public key's digest is not the committed one. -/
  | notPrecommitted
  /-- The new record is not the current record's successor. -/
  | wrongSuccessor
  /-- The new record names no next-key commitment. -/
  | nextNotCommitted
  /-- No signature by the new key over the possession frame verified. -/
  | noPossession
  deriving DecidableEq, Repr

/-- The successor shape: same subject, same key line, the next epoch. -/
def Successor (current : KeyRecord) (rotation : Rotation) : Prop :=
  rotation.key.subject = rotation.subject.value ∧
    rotation.key.keyId = current.keyId ∧
    rotation.key.keyEpoch = current.keyEpoch + 1

instance (current : KeyRecord) (rotation : Rotation) :
    Decidable (Successor current rotation) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The key-side admission of a rotation over one authority store.
`signed pk` is whether a presented signature over the rotation's possession
frame verifies under `pk`; the host computes it for the new key only.  On
success it returns the current record being rotated away. -/
def gate (digestOf : List UInt8 → Digest) (logical : Store layout) (rotation : Rotation)
    (signed : List UInt8 → Bool) : Except Reject KeyRecord :=
  match currentSigningKey logical rotation.subject with
  | none => .error .noCurrentKey
  | some current =>
    match current.nextKeyDigest with
    | none => .error .notPrerotated
    | some committed =>
      if digestOf rotation.key.publicKey = committed then
        if Successor current rotation then
          if rotation.key.nextKeyDigest.isSome then
            if signed rotation.key.publicKey then .ok current
            else .error .noPossession
          else .error .nextNotCommitted
        else .error .wrongSuccessor
      else .error .notPrecommitted

/-- Exact characterization of an admitted rotation. -/
theorem gate_ok_iff (digestOf : List UInt8 → Digest) (logical : Store layout)
    (rotation : Rotation) (signed : List UInt8 → Bool) (current : KeyRecord) :
    gate digestOf logical rotation signed = .ok current ↔
      currentSigningKey logical rotation.subject = some current ∧
      current.nextKeyDigest = some (digestOf rotation.key.publicKey) ∧
      Successor current rotation ∧
      rotation.key.nextKeyDigest.isSome = true ∧
      signed rotation.key.publicKey = true := by
  constructor
  · intro admitted
    unfold gate at admitted
    split at admitted
    · cases admitted
    · rename_i found selected
      split at admitted
      · cases admitted
      · rename_i committed next
        split_ifs at admitted with digest successor hasNext possession <;> cases admitted
        exact ⟨selected, by rw [next, digest], successor, hasNext, possession⟩
  · rintro ⟨selected, next, successor, hasNext, possession⟩
    simp [gate, selected, next, successor, hasNext, possession]

/-- What `currentSigningKey` selecting a record says about the store. -/
theorem currentSigningKey_facts {logical : Store layout} {subject : SubjectId}
    {key : KeyRecord} (selected : currentSigningKey logical subject = some key) :
    key.subject = subject.value ∧
      logical ⟨.subjectKeyEpoch, subject⟩ = some key.keyEpoch ∧
      logical ⟨.subjectKey, (subject, key.keyEpoch)⟩ = some key := by
  unfold currentSigningKey at selected
  cases epochRead : logical ⟨.subjectKeyEpoch, subject⟩ with
  | none => simp [epochRead, bind, Option.bind] at selected
  | some epoch =>
    cases recordRead : logical ⟨.subjectKey, (subject, epoch)⟩ with
    | none => simp [epochRead, recordRead, bind, Option.bind] at selected
    | some record =>
      simp only [epochRead, recordRead, bind, Option.bind] at selected
      split_ifs at selected with facts
      cases selected
      obtain ⟨subjectEq, epochEq⟩ := facts
      subst epochEq
      exact ⟨subjectEq, rfl, recordRead⟩

/-! ## The four teeth of the gate -/

/-- **Admitted ⇒ pre-committed.**  An admitted rotation's new key is the one
whose digest the subject's current record committed to. -/
theorem rotation_requires_precommitted_key {digestOf : List UInt8 → Digest}
    {logical : Store layout} {rotation : Rotation} {signed : List UInt8 → Bool}
    {current : KeyRecord}
    (admitted : gate digestOf logical rotation signed = .ok current) :
    currentSigningKey logical rotation.subject = some current ∧
      current.nextKeyDigest = some (digestOf rotation.key.publicKey) :=
  let facts := (gate_ok_iff digestOf logical rotation signed current).1 admitted
  ⟨facts.1, facts.2.1⟩

/-- **Signatures count only at the new key.**  Two signature oracles that agree
on the new key give the same verdict, whatever else they say -- in particular
whatever the current key has signed. -/
theorem gate_signatures_only_at_new_key (digestOf : List UInt8 → Digest)
    (logical : Store layout) (rotation : Rotation) (signed signed' : List UInt8 → Bool)
    (agree : signed rotation.key.publicKey = signed' rotation.key.publicKey) :
    gate digestOf logical rotation signed = gate digestOf logical rotation signed' := by
  unfold gate
  rw [agree]

/-- **The stolen daily key cannot rotate.**  For a pre-rotated subject, no set
of presented signatures -- by the current key or any other -- admits a
rotation to a key whose digest differs from the commitment.  The verdict is
`notPrecommitted`, by name. -/
theorem rotate_current_keys_irrelevant (digestOf : List UInt8 → Digest)
    (logical : Store layout) (rotation : Rotation) (current : KeyRecord)
    (committed : Digest)
    (selected : currentSigningKey logical rotation.subject = some current)
    (precommitted : current.nextKeyDigest = some committed)
    (differs : digestOf rotation.key.publicKey ≠ committed)
    (signed : List UInt8 → Bool) :
    gate digestOf logical rotation signed = .error .notPrecommitted := by
  simp [gate, selected, precommitted, differs]

/-- **Possession of the new key is necessary.** -/
theorem rotation_requires_new_key_possession (digestOf : List UInt8 → Digest)
    (logical : Store layout) (rotation : Rotation) (signed : List UInt8 → Bool)
    (unsigned : signed rotation.key.publicKey = false) (current : KeyRecord) :
    gate digestOf logical rotation signed ≠ .ok current := by
  intro admitted
  have := ((gate_ok_iff digestOf logical rotation signed current).1 admitted).2.2.2.2
  rw [unsigned] at this
  cases this

/-- **A subject without a commitment is unchanged.**  Its rotation is refused
by name, for every rotation and every signature oracle: such a subject can do
exactly what every subject could do before rotation existed. -/
theorem no_prerotation_subject_unchanged (digestOf : List UInt8 → Digest)
    (logical : Store layout) (subject : SubjectId) (current : KeyRecord)
    (selected : currentSigningKey logical subject = some current)
    (uncommitted : current.nextKeyDigest = none)
    (rotation : Rotation) (same : rotation.subject = subject)
    (signed : List UInt8 → Bool) :
    gate digestOf logical rotation signed = .error .notPrerotated := by
  subst same
  simp [gate, selected, uncommitted]

/-! ## The rotation patch -/

def epochAddress (subject : SubjectId) : Address layout := ⟨.subjectKeyEpoch, subject⟩
def recordAddress (subject : SubjectId) (epoch : Epoch) : Address layout :=
  ⟨.subjectKey, (subject, epoch)⟩
def registeredAddress (subject : SubjectId) (epoch : Epoch) : Address layout :=
  ⟨.registered, .signingKey subject epoch⟩
def revokedAddress (subject : SubjectId) (epoch : Epoch) : Address layout :=
  ⟨.revoked, .signingKey subject epoch⟩

/-- The old key version's revocation, allocated unless it is already revoked
(revocation is append-only; an already-revoked daily key may still be rotated
away from by its committed successor). -/
def revokeOld (logical : Store layout) (subject : SubjectId) (epoch : Epoch) :
    Patch layout :=
  match logical ⟨.revoked, .signingKey subject epoch⟩ with
  | some _ => []
  | none => [.allocate .revoked (.signingKey subject epoch) ()]

/-- Move the epoch pointer (guarded at the current epoch), allocate the
successor's record and registration, revoke the old version. -/
def patch (logical : Store layout) (current : KeyRecord) (rotation : Rotation) :
    Patch layout :=
  [.write .subjectKeyEpoch rotation.subject current.keyEpoch rotation.key.keyEpoch,
   .allocate .subjectKey (rotation.subject, rotation.key.keyEpoch) rotation.key,
   .allocate .registered (.signingKey rotation.subject rotation.key.keyEpoch) ()] ++
  revokeOld logical rotation.subject current.keyEpoch

/-- The store after a rotation. -/
def post (logical : Store layout) (current : KeyRecord) (rotation : Rotation) :
    Store layout :=
  Patch.run logical (patch logical current rotation)

/-- The rotation's post is four point updates of the pre-store. -/
theorem post_eq (logical : Store layout) (current : KeyRecord) (rotation : Rotation) :
    post logical current rotation =
      (((logical.set (epochAddress rotation.subject) (some rotation.key.keyEpoch)).set
          (recordAddress rotation.subject rotation.key.keyEpoch) (some rotation.key)).set
          (registeredAddress rotation.subject rotation.key.keyEpoch) (some ())).set
          (revokedAddress rotation.subject current.keyEpoch) (some ()) := by
  unfold post patch revokeOld
  cases present : logical ⟨.revoked, .signingKey rotation.subject current.keyEpoch⟩ with
  | none =>
      simp [Patch.run, Op.apply, epochAddress, recordAddress, registeredAddress,
        revokedAddress]
  | some value =>
      simp only [List.append_nil, Patch.run, Op.apply]
      apply DFinsupp.ext
      intro address
      by_cases at_revoked : address = revokedAddress rotation.subject current.keyEpoch
      · subst at_revoked
        rw [Store.set_eq]
        rw [Store.set_ne _ _ _ _ (by intro same; cases same),
          Store.set_ne _ _ _ _ (by intro same; cases same),
          Store.set_ne _ _ _ _ (by intro same; cases same)]
        show logical ⟨.revoked, .signingKey rotation.subject current.keyEpoch⟩ = some ()
        rw [present]
        cases value
        rfl
      · rw [Store.set_ne _ _ _ _ at_revoked]
        rfl

/-- Every address outside the subject's four key rows is untouched. -/
theorem post_frame (logical : Store layout) (current : KeyRecord) (rotation : Rotation)
    (address : Address layout)
    (notEpoch : address ≠ epochAddress rotation.subject)
    (notRecord : address ≠ recordAddress rotation.subject rotation.key.keyEpoch)
    (notRegistered : address ≠ registeredAddress rotation.subject rotation.key.keyEpoch)
    (notRevoked : address ≠ revokedAddress rotation.subject current.keyEpoch) :
    post logical current rotation address = logical address := by
  rw [post_eq, Store.set_ne _ _ _ _ notRevoked, Store.set_ne _ _ _ _ notRegistered,
    Store.set_ne _ _ _ _ notRecord, Store.set_ne _ _ _ _ notEpoch]

theorem post_epoch (logical : Store layout) (current : KeyRecord) (rotation : Rotation) :
    post logical current rotation ⟨.subjectKeyEpoch, rotation.subject⟩ =
      some rotation.key.keyEpoch := by
  rw [post_eq, Store.set_ne _ _ _ _ (by intro same; cases same),
    Store.set_ne _ _ _ _ (by intro same; cases same),
    Store.set_ne _ _ _ _ (by intro same; cases same)]
  exact Store.set_eq _ _ _

theorem post_record (logical : Store layout) (current : KeyRecord) (rotation : Rotation) :
    post logical current rotation ⟨.subjectKey, (rotation.subject, rotation.key.keyEpoch)⟩ =
      some rotation.key := by
  rw [post_eq, Store.set_ne _ _ _ _ (by intro same; cases same),
    Store.set_ne _ _ _ _ (by intro same; cases same)]
  exact Store.set_eq _ _ _

theorem post_registered (logical : Store layout) (current : KeyRecord) (rotation : Rotation) :
    post logical current rotation ⟨.registered, .signingKey rotation.subject rotation.key.keyEpoch⟩ =
      some () := by
  rw [post_eq, Store.set_ne _ _ _ _ (by intro same; cases same)]
  exact Store.set_eq _ _ _

theorem post_revoked (logical : Store layout) (current : KeyRecord) (rotation : Rotation) :
    post logical current rotation ⟨.revoked, .signingKey rotation.subject current.keyEpoch⟩ =
      some () := by
  rw [post_eq]
  exact Store.set_eq _ _ _

/-! ## What an admitted rotation leaves behind -/

/-- **The old key is refused after rotation.**  The subject's current key is
the successor -- a different version from the old one -- and the old version's
standing is `revoked` in the append-only plane, so `CredentialSignatureAdmission.select`
(which selects only `currentSigningKey` and requires a `live` standing) never
selects it again (`revocation_monotone` keeps it revoked forever). -/
theorem old_key_refused_after_rotation {digestOf : List UInt8 → Digest}
    {logical : Store layout} {rotation : Rotation} {signed : List UInt8 → Bool}
    {current : KeyRecord}
    (admitted : gate digestOf logical rotation signed = .ok current) :
    currentSigningKey (post logical current rotation) rotation.subject = some rotation.key ∧
      rotation.key.keyEpoch ≠ current.keyEpoch ∧
      (post logical current rotation) ⟨.revoked, signingKeyRevocation current⟩ = some () := by
  obtain ⟨selected, -, ⟨subjectExact, -, epochNext⟩, -, -⟩ :=
    (gate_ok_iff digestOf logical rotation signed current).1 admitted
  have currentSubject : current.subject = rotation.subject.value :=
    (currentSigningKey_facts selected).1
  have subjectId : (⟨rotation.key.subject⟩ : SubjectId) = rotation.subject := by
    rw [subjectExact]
  refine ⟨?_, by omega, ?_⟩
  · have exact := currentSigningKey_exact (post logical current rotation) rotation.key
      (by rw [subjectId]; exact post_epoch logical current rotation)
      (by rw [subjectId]; exact post_record logical current rotation)
    rwa [subjectId] at exact
  · have : signingKeyRevocation current = .signingKey rotation.subject current.keyEpoch := by
      simp [signingKeyRevocation, currentSubject]
    rw [this]
    exact post_revoked logical current rotation

/-- **Grants survive rotation.**  Capabilities bind a `Holder.subject`, never a
key; the rotation writes no capability, issuer, policy or non-signing-key
standing row, so every grant record, every epoch a grant is checked against,
and the standing of every capability or channel is exactly as before. -/
theorem grants_survive_rotation (logical : Store layout) (current : KeyRecord)
    (rotation : Rotation) :
    (∀ kind (id : CapabilityId),
      post logical current rotation ⟨.capability kind, id⟩ = logical ⟨.capability kind, id⟩) ∧
    (∀ issuer : IssuerId,
      post logical current rotation ⟨.issuerEpoch, issuer⟩ = logical ⟨.issuerEpoch, issuer⟩) ∧
    (∀ policy : PolicyId,
      post logical current rotation ⟨.policyEpoch, policy⟩ = logical ⟨.policyEpoch, policy⟩ ∧
      post logical current rotation ⟨.policyRevision, policy⟩ = logical ⟨.policyRevision, policy⟩) ∧
    (∀ (policy : PolicyId) (revision : PolicyRevision),
      post logical current rotation ⟨.policyAddress, (policy, revision)⟩ =
        logical ⟨.policyAddress, (policy, revision)⟩) ∧
    (∀ id : CapabilityId,
      post logical current rotation ⟨.registered, .capability id⟩ = logical ⟨.registered, .capability id⟩ ∧
      post logical current rotation ⟨.revoked, .capability id⟩ = logical ⟨.revoked, .capability id⟩) ∧
    (∀ id : ChannelId,
      post logical current rotation ⟨.registered, .channel id⟩ = logical ⟨.registered, .channel id⟩ ∧
      post logical current rotation ⟨.revoked, .channel id⟩ = logical ⟨.revoked, .channel id⟩) := by
  have frame := post_frame logical current rotation
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro kind id
    exact frame _ (by intro same; cases same) (by intro same; cases same)
      (by intro same; cases same) (by intro same; cases same)
  · intro issuer
    exact frame _ (by intro same; cases same) (by intro same; cases same)
      (by intro same; cases same) (by intro same; cases same)
  · intro policy
    exact ⟨frame _ (by intro same; cases same) (by intro same; cases same)
      (by intro same; cases same) (by intro same; cases same),
      frame _ (by intro same; cases same) (by intro same; cases same)
      (by intro same; cases same) (by intro same; cases same)⟩
  · intro policy revision
    exact frame _ (by intro same; cases same) (by intro same; cases same)
      (by intro same; cases same) (by intro same; cases same)
  · intro id
    exact ⟨frame _ (by intro same; cases same) (by intro same; cases same)
      (by intro same; cases same) (by intro same; cases same),
      frame _ (by intro same; cases same) (by intro same; cases same)
      (by intro same; cases same) (by intro same; cases same)⟩
  · intro id
    exact ⟨frame _ (by intro same; cases same) (by intro same; cases same)
      (by intro same; cases same) (by intro same; cases same),
      frame _ (by intro same; cases same) (by intro same; cases same)
      (by intro same; cases same) (by intro same; cases same)⟩

/-- **Only the rotated subject's rows move.**  Every key row of every other
subject -- its epoch pointer, every record, every version's registration and
revocation -- is exactly as before, so its current signing key is too. -/
theorem rotation_preserves_other_subjects (logical : Store layout) (current : KeyRecord)
    (rotation : Rotation) (other : SubjectId) (distinct : other ≠ rotation.subject) :
    post logical current rotation ⟨.subjectKeyEpoch, other⟩ = logical ⟨.subjectKeyEpoch, other⟩ ∧
    (∀ epoch : Epoch,
      post logical current rotation ⟨.subjectKey, (other, epoch)⟩ =
        logical ⟨.subjectKey, (other, epoch)⟩ ∧
      post logical current rotation ⟨.registered, .signingKey other epoch⟩ =
        logical ⟨.registered, .signingKey other epoch⟩ ∧
      post logical current rotation ⟨.revoked, .signingKey other epoch⟩ =
        logical ⟨.revoked, .signingKey other epoch⟩) ∧
    currentSigningKey (post logical current rotation) other = currentSigningKey logical other := by
  have frame := post_frame logical current rotation
  have epochRow : post logical current rotation ⟨.subjectKeyEpoch, other⟩ =
      logical ⟨.subjectKeyEpoch, other⟩ :=
    frame _ (by intro same; cases same; exact distinct rfl) (by intro same; cases same)
      (by intro same; cases same) (by intro same; cases same)
  have rows : ∀ epoch : Epoch,
      post logical current rotation ⟨.subjectKey, (other, epoch)⟩ =
        logical ⟨.subjectKey, (other, epoch)⟩ ∧
      post logical current rotation ⟨.registered, .signingKey other epoch⟩ =
        logical ⟨.registered, .signingKey other epoch⟩ ∧
      post logical current rotation ⟨.revoked, .signingKey other epoch⟩ =
        logical ⟨.revoked, .signingKey other epoch⟩ := by
    intro epoch
    refine ⟨frame _ (by intro same; cases same) ?_ (by intro same; cases same)
        (by intro same; cases same),
      frame _ (by intro same; cases same) (by intro same; cases same) ?_
        (by intro same; cases same),
      frame _ (by intro same; cases same) (by intro same; cases same)
        (by intro same; cases same) ?_⟩
    · intro same; cases same; exact distinct rfl
    · intro same; cases same; exact distinct rfl
    · intro same; cases same; exact distinct rfl
  refine ⟨epochRow, rows, ?_⟩
  unfold currentSigningKey
  rw [epochRow]
  cases logical ⟨.subjectKeyEpoch, other⟩ with
  | none => rfl
  | some epoch =>
      simp only [bind, Option.bind]
      rw [(rows epoch).1]

/-! ## Enrollment: the committed next key must sign

An enrollment installs a fresh record whose `nextKeyDigest` is the subject's
pre-rotation commitment.  Whoever authors the enrollment chooses that digest,
so a sponsor could commit a key it merely NAMES -- a digest copied from
elsewhere, or one it made up -- and the subject would carry a commitment no one
it trusts can open.  `enrollGate` closes that: a record that commits to a next
key is admitted only with that key's public half (whose digest IS the
commitment) and a signature by it, the same possession rule `gate` imposes on
a rotation.  A record that commits to nothing takes no next key.

What this does NOT stop: a sponsor that generates a next keypair of its own,
commits to it and signs with it.  Possession is then genuine -- the sponsor's.
The kernel cannot know whose key a key is; the subject's own client refuses a
subject whose commitment is not the digest of ITS next key
(`workspace init`, and every later load).  That client check is the tooth
against a hostile sponsor; this gate is the tooth against a commitment nobody
can open. -/

inductive EnrollReject where
  /-- The presented next public key's digest is not the record's commitment. -/
  | nextNotCommitted
  /-- No signature by the committed next key over the next-possession frame verified. -/
  | nextNoPossession
  /-- A next key was presented for a record that commits to none. -/
  | nextUnexpected
  deriving DecidableEq, Repr

/-- The next-key side of an enrollment.  `nextPublicKey` is the presented next
public half (`[]` when none); `signed pk` is whether the presented next-possession
signature verifies under `pk` -- the host computes it at the presented key only. -/
def enrollGate (digestOf : List UInt8 → Digest) (key : KeyRecord) (nextPublicKey : List UInt8)
    (signed : List UInt8 → Bool) : Except EnrollReject Unit :=
  match key.nextKeyDigest with
  | none => if nextPublicKey = [] then .ok () else .error .nextUnexpected
  | some committed =>
    if digestOf nextPublicKey = committed then
      if signed nextPublicKey then .ok () else .error .nextNoPossession
    else .error .nextNotCommitted

/-- Exact characterization of an admitted enrollment's next-key side. -/
theorem enrollGate_ok_iff (digestOf : List UInt8 → Digest) (key : KeyRecord)
    (nextPublicKey : List UInt8) (signed : List UInt8 → Bool) :
    enrollGate digestOf key nextPublicKey signed = .ok () ↔
      (key.nextKeyDigest = none ∧ nextPublicKey = []) ∨
      (key.nextKeyDigest = some (digestOf nextPublicKey) ∧ signed nextPublicKey = true) := by
  unfold enrollGate
  cases committed : key.nextKeyDigest with
  | none => by_cases empty : nextPublicKey = [] <;> simp [empty]
  | some digest =>
    by_cases same : digestOf nextPublicKey = digest
    · by_cases possession : signed nextPublicKey = true
      · simp [same, possession]
      · simp [same, possession]
    · have other : ¬ digest = digestOf nextPublicKey := fun back => same back.symm
      simp [same, other]

/-- **Enrollment requires possession of the committed next key.**  An admitted
enrollment whose record commits to `committed` presented a next key whose
digest is `committed`, and that key signed. -/
theorem enroll_requires_next_key_possession {digestOf : List UInt8 → Digest} {key : KeyRecord}
    {nextPublicKey : List UInt8} {signed : List UInt8 → Bool} {committed : Digest}
    (admitted : enrollGate digestOf key nextPublicKey signed = .ok ())
    (precommitted : key.nextKeyDigest = some committed) :
    digestOf nextPublicKey = committed ∧ signed nextPublicKey = true := by
  rcases (enrollGate_ok_iff digestOf key nextPublicKey signed).1 admitted with
    ⟨absent, -⟩ | ⟨present, possession⟩
  · rw [precommitted] at absent; cases absent
  · rw [precommitted] at present
    exact ⟨(Option.some.inj present).symm, possession⟩

/-- Satisfiable pole: a record co-signed by its committed next key is admitted. -/
theorem enroll_cosigned_admitted (digestOf : List UInt8 → Digest) (key : KeyRecord)
    (nextPublicKey : List UInt8) (signed : List UInt8 → Bool)
    (precommitted : key.nextKeyDigest = some (digestOf nextPublicKey))
    (cosigned : signed nextPublicKey = true) :
    enrollGate digestOf key nextPublicKey signed = .ok () :=
  (enrollGate_ok_iff digestOf key nextPublicKey signed).2 (Or.inr ⟨precommitted, cosigned⟩)

/-- Refuting pole: the committed next key named but not signing is refused by name. -/
theorem enroll_unsigned_next_refused (digestOf : List UInt8 → Digest) (key : KeyRecord)
    (nextPublicKey : List UInt8) (signed : List UInt8 → Bool)
    (precommitted : key.nextKeyDigest = some (digestOf nextPublicKey))
    (unsigned : signed nextPublicKey = false) :
    enrollGate digestOf key nextPublicKey signed = .error .nextNoPossession := by
  simp [enrollGate, precommitted, unsigned]

/-- Refuting pole: a presented key that is not the commitment is refused by
name, whatever was signed. -/
theorem enroll_named_next_refused (digestOf : List UInt8 → Digest) (key : KeyRecord)
    (nextPublicKey : List UInt8) (committed : Digest)
    (precommitted : key.nextKeyDigest = some committed)
    (differs : digestOf nextPublicKey ≠ committed) (signed : List UInt8 → Bool) :
    enrollGate digestOf key nextPublicKey signed = .error .nextNotCommitted := by
  simp [enrollGate, precommitted, differs]

/-- Signatures count only at the presented next key: the sponsor's, the new
daily key's, or anyone else's change nothing. -/
theorem enroll_signatures_only_at_next_key (digestOf : List UInt8 → Digest) (key : KeyRecord)
    (nextPublicKey : List UInt8) (signed signed' : List UInt8 → Bool)
    (agree : signed nextPublicKey = signed' nextPublicKey) :
    enrollGate digestOf key nextPublicKey signed = enrollGate digestOf key nextPublicKey signed' := by
  unfold enrollGate
  rw [agree]

/-! ## Both poles on a small state

A toy digest (the byte sum) stands in for cSHAKE256: the gate is generic in
`digestOf`, and evaluating cSHAKE256 under `decide` is not feasible. -/

namespace Witness

def toyDigest (bytes : List UInt8) : Digest := ⟨(bytes.map UInt8.toNat).sum⟩

def daily : List UInt8 := [1, 1]
def next : List UInt8 := [2, 2]
def thief : List UInt8 := [9, 9]
def after : List UInt8 := [3, 3]

def friend : SubjectId := ⟨8⟩

/-- Friend's enrolled record at epoch 1, committing to `next`. -/
def enrolled : KeyRecord :=
  ⟨70, 1, 1, 8, daily, 0, 100, some (toyDigest next)⟩

/-- A no-prerotation subject's record at epoch 1. -/
def plain : KeyRecord := ⟨71, 1, 1, 9, [5, 5], 0, 100, none⟩

def store : Store layout :=
  ((((((0 : Store layout).set ⟨.subjectKeyEpoch, friend⟩ (some (1 : Nat))).set
      ⟨.subjectKey, (friend, 1)⟩ (some enrolled)).set
      ⟨.registered, .signingKey friend 1⟩ (some ())).set
      ⟨.subjectKeyEpoch, ⟨9⟩⟩ (some (1 : Nat))).set
      ⟨.subjectKey, (⟨9⟩, 1)⟩ (some plain))

/-- The friend's rotation to the committed next key. -/
def honest : Rotation := ⟨friend, ⟨70, 2, 1, 8, next, 0, 100, some (toyDigest after)⟩⟩

/-- The thief's rotation to its own key. -/
def stolen : Rotation := ⟨friend, ⟨70, 2, 1, 8, thief, 0, 100, some (toyDigest thief)⟩⟩

/-- Every key signed: the strongest a thief holding the daily key can claim. -/
def everyone : List UInt8 → Bool := fun _ => true

/-- Satisfiable pole: the committed next key, signing, rotates. -/
theorem honest_admitted : gate toyDigest store honest everyone = .ok enrolled := by decide

/-- Satisfiable pole: the admitted rotation's patch validates at the store. -/
theorem honest_patch_valid : Patch.ValidFrom store (patch store enrolled honest) := by decide

/-- Refuting pole: the thief's own key, with every signature it likes, is refused by name. -/
theorem stolen_refused : gate toyDigest store stolen everyone = .error .notPrecommitted := by
  decide

/-- Refuting pole: the committed key without its possession signature is refused. -/
theorem unsigned_refused :
    gate toyDigest store honest (fun pk => decide (pk = daily)) = .error .noPossession := by
  decide

/-- Refuting pole: a no-prerotation subject cannot rotate. -/
theorem plain_refused :
    gate toyDigest store ⟨⟨9⟩, ⟨71, 2, 1, 9, next, 0, 100, some (toyDigest after)⟩⟩ everyone =
      .error .notPrerotated := by decide

/-- After the honest rotation the old daily version is revoked and the next key is current. -/
theorem honest_post :
    currentSigningKey (post store enrolled honest) friend = some honest.key ∧
      ((post store enrolled honest) ⟨.revoked, .signingKey friend 1⟩).isSome = true := by
  decide

/-- Satisfiable pole: the enrolled record, co-signed by its committed next key. -/
theorem enroll_cosigned : enrollGate toyDigest enrolled next (fun pk => decide (pk = next)) = .ok () := by
  decide

/-- Refuting pole: the sponsor names the next key but holds only the daily key
(and its own): every signature it can make is at a key other than `next`. -/
theorem enroll_named_only_refused :
    enrollGate toyDigest enrolled next (fun pk => decide (pk = daily) || decide (pk = thief)) =
      .error .nextNoPossession := by decide

/-- Refuting pole: a key it holds, presented as the next key, is not the commitment. -/
theorem enroll_other_key_refused :
    enrollGate toyDigest enrolled thief everyone = .error .nextNotCommitted := by decide

/-- A record without a commitment takes no next key, and admits none. -/
theorem enroll_plain_admitted : enrollGate toyDigest plain [] everyone = .ok () := by decide
theorem enroll_plain_with_next_refused :
    enrollGate toyDigest plain next everyone = .error .nextUnexpected := by decide

end Witness

#assert_axioms gate_ok_iff
#assert_axioms currentSigningKey_facts
#assert_axioms rotation_requires_precommitted_key
#assert_axioms gate_signatures_only_at_new_key
#assert_axioms rotate_current_keys_irrelevant
#assert_axioms rotation_requires_new_key_possession
#assert_axioms no_prerotation_subject_unchanged
#assert_axioms post_eq
#assert_axioms old_key_refused_after_rotation
#assert_axioms grants_survive_rotation
#assert_axioms rotation_preserves_other_subjects
#assert_axioms Witness.honest_admitted
#assert_axioms Witness.honest_patch_valid
#assert_axioms Witness.stolen_refused
#assert_axioms Witness.unsigned_refused
#assert_axioms Witness.plain_refused
#assert_axioms Witness.honest_post
#assert_axioms enrollGate_ok_iff
#assert_axioms enroll_requires_next_key_possession
#assert_axioms enroll_cosigned_admitted
#assert_axioms enroll_unsigned_next_refused
#assert_axioms enroll_named_next_refused
#assert_axioms enroll_signatures_only_at_next_key
#assert_axioms Witness.enroll_cosigned
#assert_axioms Witness.enroll_named_only_refused
#assert_axioms Witness.enroll_other_key_refused
#assert_axioms Witness.enroll_plain_admitted
#assert_axioms Witness.enroll_plain_with_next_refused

end Minidregg.Theory.KeyPreRotation
