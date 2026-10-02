# Protected authored annotation fragments

A comment is authored content. Adding or removing a document member must not
reattribute every comment to the membership administrator, or permit that
administrator to substitute a different body under an earlier author's name.

`AnnotationBody.sealed` separates immutable signed ciphertext from encrypted
fragment-key wrapping. The original annotation author, operation, document,
anchor and ciphertext stay unchanged. `rewrapAnnotation` accepts the exact
canonical complete prior record, refuses retired/nonsealed records, and changes
only wrapping plus its source-authored `wrappedBy` and `wrappedAt` provenance.
The enclosing resource controller still checks the actual entire post against
all current keyholders; a local key or roster hint establishes no authority.

The fragment uses a fresh independent 256-bit content key. Its signed encrypted
record is bound to the document, annotation, atom, original anchor revision and
retained command nonce. The epoch-encrypted wrapping binds the same annotation,
the hash of the exact immutable ciphertext, and its own maintenance command
nonce. Opening requires the current signed resource read, the relevant epoch
key, a valid wrapper binding, and successful authentication/decryption of the
original fragment. A malicious replacement wrap can cause unreadability, but
cannot substitute body text beneath retained authorship. It conveys no original
whole-document epoch key and grants no source read or disclosure authority.

Custody persists the fragment key and exact original ciphertext before emission.
An exact creation retry returns those same bytes; different plaintext/context
for that operation refuses. Each later wrapper has a distinct command/epoch
identity in the existing exact-emission journal. Participant custody backup
includes this state through the existing protected-document backup contract.

Membership recovery drains uncertain exact requests before planning new work.
It includes every nonretired annotation, including comments whose anchor became
stale after text edits. It validates openability before considering an epoch
already current. It does not publish completion until all current placed text
and all live authored comments have reached the target epoch and remain readable.
Exact record and target-root guards detect concurrent changes; plans never
resurrect a deleted or replaced record. Historical ciphertext and wrappers remain
in admitted history. Historical key possession does not replace current read
entitlement, and revocation cannot erase already disclosed plaintext or keys.

The existing protected atom path still reseals placed text through `editAtom`
on membership changes. This advances atom revisions even when text is unchanged,
so an immutable comment correctly becomes stale rather than being silently
reanchored. Preserving freshness through custody-only text rotation requires the
same typed immutable-fragment/key-wrapper separation for atoms. The current
annotation work does not assert that key rotation leaves atom revision unchanged.

This changes the annotation record codec to v3, content wire to v6, and content
mutation grammar to v8. Current deployments use teardown/rebuild. Public inline
comments are not silently reattributed by protection or membership recovery;
these paths refuse unsupported plaintext comments and retain their original
public history. A separate deliberate conversion contract can preserve that
public origin if required.

The receiving journey exercises private comment creation, authorized new-member
reads, immutable authored ciphertext across invitation/revocation, stale anchors,
rendered comments and absence of plaintext in persisted source/submitted intents.
Rust custody tests additionally exercise current-epoch-only recipients, exact
creation/wrapper retries, and wrong anchor/object/tampered-cipher refusals.
Source proofs describe guarded replacement, preservation of authored fields and
framing of document text/structure. Those obligations do not replace a successful
native receiving run against the combined source.
