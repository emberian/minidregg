# Explicit first next-key commitment

An existing subject whose current signing key has no `nextKeyDigest` can adopt
one explicitly, then use the existing `rotate-key` command. Adoption requires a
signature by the exact current key and a separate proof of possession by the
proposed next key. It changes only `None` to `Some(nextDigest)`: the subject,
current key ID, epoch, public key, activation interval and SSH binding remain.
An already committed key cannot use this operation to replace its commitment.

```
mini adopt-next-key --workspace WORKSPACE --next-key NEXT --action prepare
mini adopt-next-key --workspace WORKSPACE --attempt adopt-next-KEYID-EPOCH
mini adopt-next-key --workspace WORKSPACE --attempt adopt-next-KEYID-EPOCH --action lookup
mini rotate-key --workspace WORKSPACE --next-key NEXT
```

Without `--action`, the client prepares and submits once. `--attempt CHILD`
selects a direct private workspace attempt child; the default includes the
source-reported current key ID and epoch. A sealed explicit attempt can submit
or look up without `--next-key`. The Mini shell provides `adopt-next-key NEXTFILE`
and `adopt-next-key lookup ATTEMPT`; key files stay under the session's keys
directory.

## Trust and source boundary

Adoption requires existing authenticated receipt-continuity custody. A missing
anchor, verifier, enabled custody or trusted lineage is a refusal, not an
occasion to enroll a new authority. Legacy workspaces with neither pre-rotation
metadata field are accepted only through this explicit operation, after the
source identifies the local signer as the unrevoked, uncommitted current key.
Ordinary workspace loading keeps its commitment checks.

Before signing, the source profile must agree with the locally checked
continuity identity's domain, semantics and expected seed. Plan inspection must
match that identity, subject, nonce, current public key, key ID and epoch, and
proposed next public key. Lean supplies and checks the full current KeyRecord,
canonical command bytes and separate command-bound authorization/possession
headers. Rust does not encode a Lean command or derive a semantic commitment.
Enrollment's pair-only possession co-signature is not used for adoption.

The public routes are 187 (bounded JSON plan request), 188 (plan plus two raw
64-byte signatures), 189 (exact ingress submit) and 190 (exact ingress lookup).
The plan request uses `currentPublicKey`; inspections use
`currentAuthorizationHeader` and `nextPossessionHeader`. The source plan request
bound is 4096 bytes. Existing general frame bounds apply to assembly and ingress.

## Retained attempts and recovery

Each owner-private attempt retains its request, transport/profile pins, original
source status, source plan and inspection, both signatures, assembled ingress
and inspection, seal hashes, and response frames. A durable may-have-submitted
marker precedes the sole submit. Every later retry uses exact lookup, including
after an absent/refused lookup; it never silently creates a new nonce, signs
again, or resubmits. Missing submitted custody refuses while preserving the
remaining files.

A confirmed outcome must pass receipt continuity. The source must then confirm
that the same current key ID/epoch is still current and that the requested next
key matches its commitment. Only then does an atomic, directory-synced manifest
update publish `prerotation:true` and `nextPublicKey`. It preserves unrelated
workspace fields and enrollment provenance and never changes either secret.
The durable result follows that update. A crash before the result is written can
finish by exact lookup; source key changes prevent stale local finalization.
Adoption and rotation serialize through the same private workspace transition
lock.

A completed attempt can recover its original receipt after rotation without
resetting the later commitment. Explicit completed `lookup` also permits a
changed local current-key path; subject, deployment and transport must still
match. Its retained original signatures remain authoritative for the old
attempt. A subsequent semantics/transport migration is not an automatic retry
path for this specialized ingress; any mismatched pins refuse and retain the
attempt.

## Verification scope

Focused Rust tests use injected source codecs to test binding checks and actual
private file persistence, signatures, submit markers, crash boundaries, stale
finalization and replay. Socket tests exercise exact pinned-envelope requests;
subprocess tests cover remote Host pins and the real client entry point's
completed lookup after the original secrets disappear. These fixtures do not
establish native semantic admission.

`journey-key-adoption.py` runs the actual native composition against a caller's
new disposable, already-carried legacy workspace. It refuses paths outside that
fixture and requires a `KEY-ADOPTION-DISPOSABLE` ownership marker. It uses the
native source for every plan, assembly, inspection and mutation; OpenSSL signs
the source-supplied headers using fixture keys. It retains private evidence in a
new `key-adoption-evidence` directory:

```
python3 native/resource-client/journey-key-adoption.py \
  --fixture-root /private/new-fixture \
  --workspace /private/new-fixture/workspace \
  --next-key /private/new-fixture/next.key \
  --mini /absolute/path/to/mini
```

The fixture must already have a valid current key with no commitment, an
adoption-capable Host serving its pinned private Unix socket, and authenticated
continuity custody. The harness checks prepare preservation, wrong current key,
wrong current signature, missing/wrong next possession, conflicting retained
request, actual adoption, a separately signed stale pre-adoption plan, lookup
without secrets, rotation, and old adoption replay without metadata rollback.
It records artifact hashes and per-check evidence. Until this harness passes on
an actual matched Host, native adoption-to-rotation remains unverified. No
cross-domain receiving claim is made without a second-domain source fixture.
