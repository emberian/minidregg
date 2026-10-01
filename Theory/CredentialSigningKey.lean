/-
# Theory.CredentialSigningKey — one committed signing-key record

This is the existing signed-envelope key record, moved to the candidate-
independent authority layer so physical authority pages and the envelope
controller select the same data. Algorithm interpretation and cryptographic
verification remain executable boundaries, not axioms of this record.

Activation bounds are authority-registry epochs, not wall-clock timestamps.
The authority schema keys this record by its subject and exact key epoch;
the controller separately requires that epoch to be current.

The record has no revocation field.  Whether a key version is registered or
revoked is read from the authority cell's append-only `registered` and
`revoked` planes at `RevocationKey.signingKey subject epoch`
(`CredentialAuthorityState.keyStanding`): a guarded write to this record can
never un-revoke a key.

`nextKeyDigest` is the subject's pre-rotation commitment (KERI): the digest of
the NEXT public key under the deployment's next-key digest
(`Kernel.SubjectKeyRotation.nextKeyDigest`).  A rotation is admitted only by
exhibiting a key whose digest it is (`Theory.KeyPreRotation.gate`), so whoever
holds the current key cannot rotate.  `none` is a subject enrolled without
pre-rotation: it cannot rotate at all, exactly as before rotation existed.
-/
import Theory.TypedAuthorization

namespace Minidregg.Theory.CredentialSigningKey

set_option autoImplicit false

structure KeyRecord where
  keyId : Nat
  keyEpoch : Nat
  algorithm : Nat
  subject : Nat
  publicKey : List UInt8
  activeFrom : Nat
  activeUntil : Nat
  nextKeyDigest : Option TypedAuthorization.Digest
  deriving DecidableEq, Repr

/-- Used only by the existing logical materializer witness's value-tree
countability; the production codec is the explicit shared stream. -/
local instance : Countable UInt8 :=
  Function.Injective.countable (f := UInt8.toNat)
    (by intro left right same; exact UInt8.toNat.inj same)

local instance : Countable TypedAuthorization.Digest :=
  Function.Injective.countable (f := TypedAuthorization.Digest.value)
    (by intro left right same; cases left; cases right; cases same; rfl)

deriving instance Countable for KeyRecord

end Minidregg.Theory.CredentialSigningKey
