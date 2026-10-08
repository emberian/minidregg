/-
# Assurance.RenounceAudit — `Theory.Renounce` on the host's own values

Every statement here is about the Host's `CapabilityRenounce.Accepted` value:
the one `admitNative` returns and the receiver installs. The renounce is
admitted only for an authenticated signer (its current key, at its current key
epoch, registered and live) who is the holder the renounced capability names;
the committed authority cell is the theory's post (`RevokedOne`); the renounced
capability and its delegates are refused afterwards; every other capability's
admissibility is unchanged; the revocation is permanent.
-/
import Kernel.CapabilityRenounce

namespace Minidregg.Assurance.RenounceAudit

open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.CapabilityRenounce
open Minidregg.Theory
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Renounce

set_option autoImplicit false

variable {deployment : CapabilityRenounce.Deployment} {semantics : Digest}
  {ambient : CapabilityRenounce.Ambient} {ground : CapabilityRenounce.Ground deployment}
  {command : Command} {prepared : Prepared deployment semantics ambient ground command}
  {envelope : List UInt8}

/-- **`renounce_requires_holder`, at the host.** The checked signature is over
exactly the renounce request, whose subject is the command's signer, and the
renounced capability is the one stored at the named id, held by that signer. -/
theorem accepted_signer_is_holder (accepted : Accepted prepared envelope) :
    accepted.receipt.request = ⟨.program, prepared.request⟩ ∧
      prepared.request.subject = command.subject ∧
      (readCapability ground.authority.cell command.kind command.capability).map
        StoredCapability.head = some accepted.victim ∧
      accepted.victim.id = command.capability ∧
      accepted.victim.holder = .subject command.subject := by
  obtain ⟨requestExact, _⟩ :=
    CredentialSignatureAdmission.verified_request_exact _ _ _ _ accepted.bound
  obtain ⟨stored, idExact, holderExact⟩ := renounce_requires_holder accepted.gated
  exact ⟨requestExact, rfl, stored, idExact, holderExact⟩

/-- The renounce is signed by the signer's CURRENT key: the key record at the
subject's current key epoch, registered and not revoked. After a key rotation
(K-PREROTATE) this is the new key; the old key's signature does not verify. -/
theorem accepted_signed_by_current_key (accepted : Accepted prepared envelope) :
    ∃ key, currentSigningKey ground.authority.logical command.subject = some key ∧
      key.keyEpoch = ground.authority.authState.subjectKeyEpoch command.subject ∧
      isRegistered ground.authority.cell (signingKeyRevocation key) = true ∧
      isRevoked ground.authority.cell (signingKeyRevocation key) = false := by
  obtain ⟨requestExact, _⟩ :=
    CredentialSignatureAdmission.verified_request_exact _ _ _ _ accepted.bound
  have subjectExact : accepted.receipt.request.2.subject = command.subject := by
    rw [requestExact]; rfl
  have live := CredentialSignatureAdmission.checked_signer_live _ accepted.receipt
  refine ⟨accepted.receipt.prepared.controller.key, ?_, ?_, live.1, live.2⟩
  · rw [← subjectExact]
    exact CredentialSignatureAdmission.checked_key_from_same_snapshot _ _
  · rw [accepted.receipt.prepared.keyExact, accepted.receipt.prepared.source.epochExact,
      accepted.receipt.prepared.source.epochCurrent, subjectExact]

/-- The committed authority cell is the theory's post: the revoked set grows
by exactly the renounced capability's key, and nothing else moves. -/
theorem accepted_revokedOne (accepted : Accepted prepared envelope) :
    RevokedOne (authState ground.authority.cell) (authState accepted.authorityPost)
      (.capability command.capability) :=
  revokedOne_of_patch accepted.validated

/-- **`renounce_revokes_exactly_lineage`, at the host.** -/
theorem accepted_revokes_exactly_lineage (accepted : Accepted prepared envelope) :
    (∀ key, key ∈ (authState accepted.authorityPost).revoked ↔
      key = .capability command.capability ∨ key ∈ (authState ground.authority.cell).revoked) ∧
    (∀ (kind : ResourceKind) (cap : Capability kind) (request : Request kind),
      InLineage command.capability cap → ¬ cap.Admissible (authState accepted.authorityPost) request) ∧
    (∀ (kind : ResourceKind) (cap : Capability kind) (request : Request kind),
      ¬ InLineage command.capability cap →
        (cap.Admissible (authState accepted.authorityPost) request ↔
          cap.Admissible (authState ground.authority.cell) request)) :=
  renounce_revokes_exactly_lineage (accepted_revokedOne accepted)

/-- **`renounce_then_use_refused`, at the host.** The renounced capability is
refused for every request after the renounce. -/
theorem accepted_renounced_refused (accepted : Accepted prepared envelope)
    (request : Request command.kind) :
    ¬ accepted.victim.Admissible (authState accepted.authorityPost) request :=
  renounce_then_use_refused (accepted_revokedOne accepted) accepted.victim
    (accepted_signer_is_holder accepted).2.2.2.1 request

/-- Everything the holder delegated from the renounced capability dies with it. -/
theorem accepted_delegates_refused (accepted : Accepted prepared envelope)
    {kind : ResourceKind} (cap : Capability kind) (delegated : command.capability ∈ cap.ancestors)
    (request : Request kind) :
    ¬ cap.Admissible (authState accepted.authorityPost) request :=
  renounce_kills_delegates (accepted_revokedOne accepted) cap delegated request

/-- **`renounce_preserves_others`, at the host.** -/
theorem accepted_preserves_others (accepted : Accepted prepared envelope)
    {kind : ResourceKind} (cap : Capability kind) (outside : ¬ InLineage command.capability cap)
    (request : Request kind) :
    cap.Admissible (authState accepted.authorityPost) request ↔
      cap.Admissible (authState ground.authority.cell) request :=
  renounce_preserves_others (accepted_revokedOne accepted) cap outside request

/-- **`renounced_stays_revoked`, at the host.** -/
theorem accepted_stays_revoked (accepted : Accepted prepared envelope) :
    RevocationKey.capability command.capability ∈ (authState accepted.authorityPost).revoked ∧
      ∀ patch : Store.Patch layout, Store.Patch.ValidFrom accepted.authorityPost.logical patch →
        Store.Patch.run accepted.authorityPost.logical patch
          ⟨.revoked, .capability command.capability⟩ = some () :=
  renounced_stays_revoked accepted.validated

/-- **`holder_cannot_renounce_others`, at the host.** If the capability stored
at the named id names any holder but the signer (or none is stored), no
renounce of it is ever accepted. -/
theorem nonholder_never_accepted
    (other : ∀ stored, readCapability ground.authority.cell command.kind
      command.capability = some stored → stored.head.holder ≠ .subject command.subject) :
    IsEmpty (Accepted prepared envelope) := by
  constructor
  intro accepted
  obtain ⟨_, _, stored, _, holder⟩ := accepted_signer_is_holder accepted
  obtain ⟨found, readExact, headExact⟩ := Option.map_eq_some_iff.mp stored
  exact other found readExact (by rw [headExact]; exact holder)

/-- A capability already revoked is never renounced again (its holder is
refused `alreadyRevoked` by the gate). -/
theorem revoked_never_accepted
    (revoked : isRevoked ground.authority.cell (.capability command.capability) = true) :
    IsEmpty (Accepted prepared envelope) := by
  constructor
  intro accepted
  have admitted := (gate_ok_iff _ _ _ _ _ _).1 accepted.gated
  rw [revoked] at admitted
  exact Bool.noConfusion admitted.2.2.2.2

/-- info: 'Minidregg.Assurance.RenounceAudit.accepted_signer_is_holder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_signer_is_holder
/-- info: 'Minidregg.Assurance.RenounceAudit.accepted_signed_by_current_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_signed_by_current_key
/-- info: 'Minidregg.Assurance.RenounceAudit.accepted_revokedOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_revokedOne
/-- info: 'Minidregg.Assurance.RenounceAudit.accepted_revokes_exactly_lineage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_revokes_exactly_lineage
/-- info: 'Minidregg.Assurance.RenounceAudit.accepted_renounced_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_renounced_refused
/-- info: 'Minidregg.Assurance.RenounceAudit.accepted_delegates_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_delegates_refused
/-- info: 'Minidregg.Assurance.RenounceAudit.accepted_preserves_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_preserves_others
/-- info: 'Minidregg.Assurance.RenounceAudit.accepted_stays_revoked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_stays_revoked
/-- info: 'Minidregg.Assurance.RenounceAudit.nonholder_never_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonholder_never_accepted
/-- info: 'Minidregg.Assurance.RenounceAudit.revoked_never_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revoked_never_accepted

end Minidregg.Assurance.RenounceAudit
