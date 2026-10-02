# Establishing the first next-key commitment

A carried legacy signing key can have no next-key commitment. Rotation remains
unavailable until its current holder explicitly adopts one. Adoption is a new,
signed action at the current profile; it does not reinterpret old enrollment or
pretend that a precommitment existed before the carry.

The command binds the subject, a nonce, the complete expected current key record,
and the proposed next public key. The current key signs the authorization frame,
and the next key signs a separate possession frame. Both frames include the
deployment domain, current semantics, and exact canonical command bytes.

Admission requires:

- The expected record is still the subject's current record.
- That key version is registered, unrevoked, active, and Ed25519.
- Its next-key commitment is absent.
- The new public key is distinct, has the required shape, and appears in no
  existing key record, including historical and revoked versions.
- Both independently verified signatures authorize this exact action.

The guarded patch changes only the current record's nextKeyDigest. It
preserves the subject, key ID, epoch, public key, algorithm, activation bounds,
epoch pointer, registrations, revocations, and grants. Normal rotation then
requires the adopted key's possession and opens this commitment through the
existing rotation gate.

This is current-key authority. If an uncommitted current key is already stolen,
possession of that key can authorize adoption. This action cannot provide
retroactive protection; it enables the holder to establish protection now.
A revoked or expired current key cannot use adoption as recovery, and an
existing next-key commitment cannot be replaced by this action.

The operation publishes its authority patch and durable marker in one CAS.
Exact replay returns the original receipt. A stale record or repeated fresh
admission is refused; changing the proposal under the same nonce/epoch marker
is a transaction conflict. Receipt lookup is read-only.

The reserved transport operations are 187 plan, 188 detached assembly, 189
submit, and 190 receipt lookup. The plan request is exactly
{subject, nonce, currentPublicKey, nextPublicKey}. Canonical signing plans and
ingresses remain Lean-owned. Introducing this receiving action changes the
runtime semantic identity.

Clients retain the exact plan, both signatures, and sealed ingress before
submission. Once submission may have occurred, recovery uses that exact
receipt lookup rather than generating a new nonce or resigning. A verified
receipt and current source status precede changing local commitment metadata.
The workspace's signing key and SSH identity remain unchanged by adoption.
