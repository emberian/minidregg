/-
# Theory.CredentialSigningKey — one committed signing-key record

This is the existing signed-envelope key record, moved to the candidate-
independent authority layer so physical authority pages and the envelope
controller select the same data. Algorithm interpretation and cryptographic
verification remain executable boundaries, not axioms of this record.

Activation bounds are authority-registry epochs, not wall-clock timestamps.
The authority schema keys this record by its subject and exact key epoch;
the controller separately requires that epoch to be current.
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
  revoked : Bool
  deriving DecidableEq, Repr

/-- Used only by the existing logical materializer witness's value-tree
countability; the production codec is the explicit shared stream. -/
local instance : Countable UInt8 :=
  Function.Injective.countable (f := UInt8.toNat)
    (by intro left right same; exact UInt8.toNat.inj same)

deriving instance Countable for KeyRecord

end Minidregg.Theory.CredentialSigningKey
