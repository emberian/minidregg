/-
# Assurance.KeyPreRotationAudit -- the host's rotation admission carries the theory

`Kernel.Receivers.SubjectKeyRotation` admits through `Theory.KeyPreRotation.gate`
and writes `Theory.KeyPreRotation.patch`, as a `Kernel.Receiving` family.  These
statements are about the host's own `Prepared` values and admissions, so the
theory's teeth are the deployed admission's, not a model's.
-/
import Kernel.Receivers.SubjectKeyRotation

namespace Minidregg.Assurance.KeyPreRotationAudit

open Minidregg.Kernel.SubjectKeyRotation
open Minidregg.Theory
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

variable {env : Env} {durable : Durable} {command : Command} {ingress : DecodedIngress}

/-- The authority cell an accepted rotation commits is exactly the theory's
rotation post of the loaded cell. -/
theorem authorityPost_is_rotation_post (prepared : Prepared env durable command) :
    prepared.authorityPost.logical =
      KeyPreRotation.post prepared.authority.snapshot.logical prepared.current command.rotation :=
  rfl

/-- **On the host: the old key is refused after an accepted rotation.**  The
committed cell's current key for the subject is the new record, at a different
epoch, and the old version is in the append-only `revoked` plane, so
`CredentialSignatureAdmission.select` (current key only, `live` standing only)
never selects it again. -/
theorem accepted_old_key_refused {laws : Minidregg.Kernel.ReceivingLaw.Laws Durable}
    {m : Type → Type} {oracle : Minidregg.Compiler.CredentialSignatureIO.Oracle m}
    (admission : (receiver laws oracle).Admitted env durable ingress) :
    let prepared : Prepared env durable ingress.command := admission.accepted.prepared
    currentSigningKey prepared.authorityPost.logical ingress.command.subject =
        some ingress.command.key ∧
      ingress.command.key.keyEpoch ≠ prepared.current.keyEpoch ∧
      prepared.authorityPost.logical ⟨.revoked, signingKeyRevocation prepared.current⟩ = some () :=
  KeyPreRotation.old_key_refused_after_rotation admission.accepted.prepared.gated

/-- **On the host: a stolen daily key cannot rotate.**  Whatever the native
verifier says about the one presented signature, the host's gate refuses a
rotation naming a key whose digest is not the subject's commitment, by name. -/
theorem host_stolen_daily_key_refused (logical : Store.Store CredentialAuthorityState.layout)
    (current : KeyRecord) (committed : Digest)
    (selected : currentSigningKey logical command.subject = some current)
    (precommitted : current.nextKeyDigest = some committed)
    (differs : nextKeyDigest command.key.publicKey ≠ committed) (verified : Bool) :
    KeyPreRotation.gate nextKeyDigest logical command.rotation (presented command verified) =
      .error .notPrecommitted :=
  KeyPreRotation.rotate_current_keys_irrelevant nextKeyDigest logical command.rotation current
    committed selected precommitted differs _

/-- The host's signature oracle vouches only for the key the rotation names. -/
theorem presented_only_new_key (verified : Bool) (publicKey : List UInt8)
    (vouched : presented command verified publicKey = true) :
    publicKey = command.key.publicKey ∧ verified = true := by
  simp only [presented, Bool.and_eq_true, decide_eq_true_eq] at vouched
  exact vouched

/-- Grants survive an accepted rotation on the host. -/
theorem accepted_grants_survive (prepared : Prepared env durable command) :
    ∀ kind (id : CapabilityId),
      prepared.authorityPost.logical ⟨.capability kind, id⟩ =
        prepared.authority.snapshot.logical ⟨.capability kind, id⟩ :=
  (KeyPreRotation.grants_survive_rotation _ _ _).1

#assert_axioms authorityPost_is_rotation_post
#assert_axioms accepted_old_key_refused
#assert_axioms host_stolen_daily_key_refused
#assert_axioms presented_only_new_key
#assert_axioms accepted_grants_survive
#assert_axioms Prepared.precommitted
#assert_axioms admitted_possession
#assert_axioms Prepared.gated_by_possession
#assert_axioms refused_possession_before_gate

end Minidregg.Assurance.KeyPreRotationAudit
