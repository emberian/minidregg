# Selective private sharing: two verifier claims

This is a construction proposal, not an implemented receiver, an approved
publication policy, or a decision to weaken the current native-prefix claim.
It was checked against `Kernel/FnEvidence.lean` (SHA-256 `c95e7be8`),
`Kernel/NativeHostReplay.lean` (`03d2b9b2`),
`Compiler/NativeHostCodec.lean` (`a3f2c825`), and
`Compiler/DurableReceiverCodec.lean` (`70db2bd1`) on 2026-09-26. The current
disclosure contract is described in [FN-PUBLICATION-DISCLOSURE.md](FN-PUBLICATION-DISCLOSURE.md).

## State the claim before choosing an envelope

There are two different useful statements:

1. **Historical Mini-origin acceptance.** An exact signed call was admitted at
   its original source height under the pinned genesis, domain, profile,
   authority, policy, parent state, read guards, nullifiers, journal and charge
   state. Its original-prefix receipt is the one computed by replay. Today's
   `FnEvidence.verify` proves this by replaying the entire original accepted
   prefix, not by trusting the carried receipt or fn.
2. **Authorized release and receiving.** A resource-governed owner authorized
   these exact bytes for this receiver and destination, and the recipient Mini
   admitted that release under its *own current* policy and one-use conflict
   rule. This can be independently checked without publishing the private
   source history. It does **not**, by itself, prove that any claimed private
   source operation was historically admitted. The public result must not be
   labelled an original Mini operation receipt.

The second statement is useful for a private workroom in its own right. It
lets the source owner publish chosen content while the recipient independently
checks the owner's authority and performs a native receiving transition.
Neither fn's hybrid signature nor its Store position substitutes for this
authorization. Fn is a semi-untrusted transport of the exact signed release.

## Why the current receipt cannot be selectively opened

`NativeHostCodec.imageBoundary` hashes the complete canonical image bytes.
`FnEvidence.Package.acceptedPrefix` carries the genesis and every original
record through the receipt; `NativeHostReplay.verifyBytes` re-admits each
record's original ingress and compares every resulting intent. Individual
`rootBytes` values bind cell bytes but are not an authenticated global
membership/nonmembership map. A hash of the omitted prefix, a log Merkle
inclusion path, or a selected signed call proves neither authority at that
height nor absence of an intervening policy change, revocation, spent
nullifier, same-ID journal conflict, changed parent, or stale read guard.

For the exact historical claim, the smallest kernel relation is a selected
step inside `NativeHostReplay.AdmittedReplay`: split the verified trace into
prior records, the selected `AdmittedStep`, and later records; require that
the selected step's `Derived.admission` is the relevant native receiver's
admission, its `recordMatches` holds for the complete journal record, its
signed ingress is the exact selected call, and its receipt is the boundary
of the original prefix. A selection lemma can be proved using the existing
`AdmittedReplay.cons`/`append` and `Verified.accepted_history` without
changing the receiver. This defines the proposition a selective proof must
establish; it does not create a cryptographic witness or hide the trace.

For repeated exchanges with a recipient that **already** holds a
verifier-minted `Verified` checkpoint, `NativeHostReplay.extendVerified`
provides an immediate, narrower disclosure mode: transport only the exact
new suffix, check the canonical prior prefix against that checkpoint, and
freshly admit the suffix. The recipient must retain the authenticated old
image and stable verifier/config semantics. This is not a first-contact
selective proof and cannot be advertised as concealing history from that
recipient.

## First executable construction: resource-owned release

Add a distinct, versioned `Release` message and receiving operation. Its
domain-separated signed bytes should bind at least: source owner-policy
identity and key epoch; source deployment/domain, semantics and resource
coordinate, plus a *claimed* private operation identity if one is shown;
receiver deployment/domain and semantics; destination resource and routing
group; a separate audience visibility, policy/keyset root and epoch; exact
released content bytes (or a digest and length checked against those bytes);
parent/context commitment; one-use release nonce; and an expiry or explicit
one-shot validity rule. The source owner or a delegated release principal
signs those bytes. A declaration about a private source receipt remains a
claim unless the historical proof above is also supplied.

`recipientOnly` is signed audience intent, **not** confidentiality once bytes
enter fn. A confidential delivery profile must encrypt before fn publication
and sign the ciphertext, plaintext commitment and format; the receiver must
check the intended recipient keyset before disclosure. This proposal does
not define or approve an encryption suite.

The recipient config or a governed receiver resource pins the owner-policy
root. Its native receiver verifies the signature and complete bounded
delegation chain with the pinned native verifier, checks the local *current*
release law/grant and parent/read roots, requires the exact content bytes,
and atomically writes the released object, consumed nonce, receipt and any
outbox record as one `DataIntent`. The gateway that fetched the fn article
may have separate local write authority, but gateway participation alone
cannot replace the owner signature. All owner-key changes and delegations
must have explicit versions; old wire versions retain their old meanings.

For a one-shot owner signature, the honest claim is authorization by that
key for these bytes under the receiver's pinned policy. It makes no claim
about the **current source Mini state**. If current source revocation/policy
is required, add a source-state checkpoint with its own separately selected
trust anchor: a source sequencer or independent verifier signs a bounded
resource-scoped state root, sequence, policy epoch and receiver challenge;
the receiver checks monotonicity against its retained checkpoint and a
membership/nonmembership witness for grants and revocations. This is an
explicit attestation assumption about the checkpoint signer, not a proof
deduced from fn transport or a bare Merkle root. First contact cannot infer
that no newer revocation exists without such a freshness authority or a
locally retained checkpoint. Choosing that authority and validity window is
a product/security decision, not an implicit implementation detail.

The initial kernel work can remain small and testable:

* `Kernel/FnSelectiveRelease.lean`: strict release codec, domain-separated
  signed preimage, receiver pin and validity predicate. Prove that accepted
  release binds every destination/content/policy/nonce field and that changing
  one field changes the checked message bytes; do not use a supplied
  `signatureValid` Boolean as evidence.
* A native admission carrier for the actual signature helper and governed
  receiving resource, then one `DataIntent` joining content, nonce and
  receipt/outbox. Prove accepted fresh nonce versus exact-call replay and
  conflicting bytes, and retain the current-law check at admission.
* A separate `SelectedHistoricalStep` theorem over `AdmittedReplay`, with
  exact call/record/receipt decomposition, as the specification for a later
  historical proof. Keep it out of the release receiver's current claim.

Refusal gates should include a forged owner signature, a valid signature
with changed content/destination/receiver, unrelated fn header changes,
gateway-only submission, revoked local grant, stale parent root, conflicting
nonce, old key epoch, wrong source/receiver domain, replay with altered
bytes, and an asserted source receipt unsupported by historical evidence.
An exact retry must recover the same receiving receipt without a second
effect. A valid log inclusion proof for an otherwise invalid source event
must not upgrade the release to historical-origin status.

## Long-term independent historical proof

First-contact selective **historical** verification needs a proof of the
entire hidden transition relation, not just inclusion of the selected
event. A candidate new-version commitment is a domain-separated append
chain over canonical records plus an authenticated state root with openings
and absence proofs for every read, write, authority, parent, journal and
nullifier coordinate touched by each step. A recursive or otherwise
succinct proof would establish genesis-to-selected-step replay under the
actual native admission rules while keeping unrelated witnesses private.
Public inputs must include the independently pinned genesis, domain,
semantics/verifier identity, selected call and receipt, exact released bytes,
destination, final commitment and proof-system verification key. The
verifier must check the proof and original-receipt selection itself.

This requires new commitment binding assumptions and an implementation of
canonical decoding, cSHAKE, hybrid signature verification and each relevant
native receiver relation inside the proof system, or a rigorously stated
refinement to them. The existing AIR/Merkle components are not currently a
proof of `NativeHostReplay`'s IO replay or of signature-helper behavior.
Moving to this profile needs an explicit genesis/profile migration and
adversarial soundness gates; it must not silently reinterpret v1/v2
full-prefix packages or existing receipts. An attested checkpoint can be an
interim contract only if its verifier/signer is explicitly pinned and the
claim is labelled as attested rather than independently re-admitted.
