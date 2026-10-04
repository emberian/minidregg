# Protected authored fragments

A comment is authored content. Adding or removing a document member must not
reattribute every comment to the membership administrator, or permit that
administrator to substitute a different body under an earlier author's name.

Shared `AuthoredFragment`, used by `AnnotationBody.sealed` and
`AtomKind.sealedObject`, separates immutable signed ciphertext from encrypted
fragment-key wrapping. The original annotation author, operation, document,
anchor and ciphertext stay unchanged. `rewrapAnnotation` accepts the exact
canonical complete prior store entry (address and record, the `canonical` of a signed
view's entry, which must name the rewrapped annotation), refuses retired/nonsealed records, and changes
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

Protected text stores its entire authored fragment in the typed sealed atom
kind; its outer payload must be empty, checked by the source create/edit path.
Atom birth attribution remains in `createdBy`/`createdAt`. Fragment `author` and
`operation` identify the latest genuine semantic edit, normalized from the
receiving actor and operation. Initial wrapping gets the same provenance.
`rewrapAtom` requires the complete exact prior record and preserves its entire
semantic identity: document, schema, original ciphertext and fragment origin,
outer payload, birth, revision and death. Only wrapping and maintenance provenance
change. It refuses retired or unprotected records. A genuine edit creates a new
immutable fragment and advances the atom revision; a tombstone retains the
existing authored fragment while recording the semantic retirement.

The source `KeepsAt` relation now preserves exact semantic records, omitting
only key wrapping and its maintenance provenance. Its former full-record equality
was false for custody-only updates at unchanged revisions. `transclusion_pinned`
consumes the semantic relation and proves that a pin retains the same authored
bytes or reports movement. Sealed source rendering projects immutable encrypted
capsule bytes, never empty outer payload or plaintext. Independent source read,
source opening and explicit disclosure authority remain required by receiving
consumers. Maintenance does not rebase any anchor; existing comments and marks
stay fresh, while genuine edits make their old revisions honestly stale.

Fresh membership recovery emits only source-guarded wrapping changes for authored
atoms and comments, without plaintext staging or formatting reconstruction.
Prospective conversion of previously public text still creates a genuinely new
protected representation and retains its original signed history. Unsupported
old private formats can remain historical; no legacy migration is a release gate.

High-level edit/push lowering refreshes a retained raw atom guard from its
fresh authorized signed source only when the complete semantic record is exactly
equal. The comparison removes only wrapping and wrapping provenance, preserving
ciphertext, schema, origin, birth, revision and retirement. This happens before
initial command emission; raw content action guards and uncertain emitted calls
are never rewritten. A real edit, origin change or deletion retains the old guard
and gets the ordinary stale refusal. Signed history retains maintenance events;
semantic document diff does not label a wrapper update as a content edit.

This successor changes atom records to v3, annotation records to v4, content wire
to v7 and mutation grammar to v9. Current deployments use teardown/rebuild. Public inline
comments are not silently reattributed by protection or membership recovery;
these paths refuse unsupported plaintext comments and retain their original
public history. A separate deliberate conversion contract can preserve that
public origin if required.

The receiving journey exercises private comment creation, authorized new-member
reads, immutable authored ciphertext across invitation/revocation, stable maintenance anchors, genuine-edit stale anchors,
rendered comments and absence of plaintext in persisted source/submitted intents.
Rust custody tests exercise both atom and annotation current-epoch-only recipients, exact
creation/wrapper retries, and wrong anchor/object/tampered-cipher refusals.
Source proofs describe guarded replacement, preservation of authored fields and
framing of document text/structure. Those obligations do not replace a successful
native receiving run against the combined source.
