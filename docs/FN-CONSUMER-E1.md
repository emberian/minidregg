# Bounded local fn E1 consumer experiment

`Kernel/FnConsumerOperation.lean` owns the first Mini processing transaction
for a public `DREGG/FN/NATIVE-PREFIX/v1` report. The origin pin is selected
independently of the report and its Mini history is re-admitted by
`FnEvidence.verify`. The local operator separately selects a consumer
application, subject, content target and capability in `POLICY.json`. The
fetched report cannot select another local subject to evade operation
uniqueness. Its fn verdict reference is explicitly a **trusted test adapter**
input until fn's native T10 authorship and E2 consumer fetch interfaces can
supply independently checked, exact carrier/source identity and Store
history/incarnation/sequence.

The operation key is `(consumer Mini domain, consumer semantics, application,
operation)`. `operationNonce` derives an even nonce from these four fields;
fn source identity is absent. The existing native invocation receiver uses
that nonce with the selected consumer subject to form its durable transaction
ID and nullifier. One signed content-resource invocation atomically creates a
typed binding atom holding exact report provenance/package and a second atom
holding immutable typed application reply Q. The original signed invocation
and both payloads remain in the verified accepted-event history. An exact
repeat recovers Q from that original history event, even if current page
presentation later changes. A changed source under the same operation selects
an odd, separately domain-separated nonce and writes typed conflict evidence,
including the exact conflicting package, in a different transaction; it
cannot update the original operation effect or Q. A repeated conflict returns
`historical-conflict-evidence`. Atom IDs occupy disjoint residue classes for
operation binding, Q, and conflict evidence. Hash collisions remain an
explicit primitive assumption; a marker occupied by another decoded binding
is refused, not interpreted as a repeat.

`minidregg-host CONSUMER-CONFIG.json consumer-decide-test ORIGIN-PIN.json
POLICY.json REPORT.json PACKAGE.bin INTENT.bin DECISION.json` is the local
source-owned decision route. It caps the origin package at 17,408 bytes and
the consumer history at 16 accepted events, refuses an unpinned namespace or
grant, and emits a canonical native observation intent for a fresh operation
or conflict. The decision JSON says `proposed-*` until the normal signed
`mini submit --intent-kind binary` call is confirmed. `mini submit
--prepare-only true` retains a fully signed call without publishing it, for
deterministic stale-prestate and crash tests; `mini retry --mode submit|lookup`
then uses those exact bytes. Current grant and target root admission belong
to the ordinary `NativeHost.submit` / `DeclaredResourceController` path,
not to this adapter. A failed preflight, refused receiver, or ambiguous
physical commit must not become a fn ack or a reply publication.

This is intentionally finite: one content page holds at most 16 entries,
each new operation consumes two, each conflict consumes one, and this adapter
refuses histories over 16 accepted events. It has no automatic page expansion
or compaction. The native SQLite CAS, OS fsync and signature helper are trusted
physical boundaries already documented by Mini. Proofs in
`Kernel/FnConsumerOperationProofs.lean` concern the actual `decide` function
called by the host and the source-owned command nonce; they do not certify
collision resistance, physical durability, external fn verdicts, or a live
fn-to-Mini connector. The fn consumer cursor and ack remain in fn; ack is
allowed only after the Mini operation/conflict transaction is durably settled.
The separate signed fn posting artifact for Q belongs to the later publication
step and must be persisted before any post or retry.

The later [portable authorship join](FN-PORTABLE-E1.md) adds
`portable-consumer-decide`. It replaces the synthetic source/verdict input
for a scoped offline experiment with the real fn hybrid verifier's exact
source identity, an E1 package decoded only from those source bytes, and
the P0 origin re-admission. Its operation identifier commits to the origin
domain, semantics, genesis pin and original transaction ID, so a changed
fn source carrying the same origin operation selects the same stable
operation nonce. `evaluate` also scans bounded accepted history for an
existing application/operation binding under another local subject, target
or capability and refuses policy drift before proposing another intent.
The portable binding explicitly records Store admission as unestablished;
it is not a native fn Store fetched report. The portable route also adds a
third atom in the same signed operation transaction: a separately bounded
36,864-byte typed inbox containing the exact fn carrier, authenticated
source identity, principal, and both full public keys. Its carrier is bounded
at 32,768 bytes before decoding an accepted historical atom. The unchanged
18,432-byte binding cap does not absorb this full article. The original
accepted event, not a mutable page view, is the source for read-only
`consumer-export-inbox TRANSACTION-ID INBOX.bin CARRIER.eml RESULT.json` and
`consumer-export-reply TRANSACTION-ID REPLY.bin`. Exact repetition recovers
Q; a different relay projection with the same signed source preserves another
carrier in a separate evidence transaction and recovers the same Q; a changed
authenticated source preserves conflict evidence without a second effect.
The added inbox atoms use residue 3 of the existing operation/conflict nonce
layout; existing binding, Q, and conflict atom IDs are unchanged.

The native portable command checks the fn signature, Mini origin, and local
consumer history once each before deriving the operation intent. Its JSON
`timingNs` records bounded stage measurements, not an assurance claim. The
same native signed receiver still performs current grant admission and atomic
SQLite CAS. On reopen, `NativeHostReplay` re-admits the original signed calls;
the policy step now uses the existing exact-selector constructor with a proved
equality to the original prepared tuple, avoiding reconstruction of unused
large request hashes for a pre-cell lookup. Physical-shape admission also
constructs its full write list once and uses a proved Boolean iff for the
original `PhysicalShape` proposition; it does not skip any clause. The
admitted invocation reuses those exact writes and guards for its durable
intent and charge lanes; `dataIntent_original_exact` proves equality of the
complete result with the original construction. The remaining full history
replay and cryptographic cost are measured in the fn evidence note. No Mini commit
implies fn Store acceptance, consumer cursor progress, or a posted reply.

The public synthetic fixture and exact native results are in fn
`tests/fixtures/dregg-e1/consumer-p1/` and
`planning/evidence/dregg-e1-consumer-p1.md`. Two reports with different fn
source identities and the same application/operation were decided and signed
against one pre-state. The first call installed the binding and Q; the second
call was refused by the ordinary receiver and produced no second effect.
After reopen, the first source recovered byte-identical Q. The changed source
then installed one conflict atom with a separate nonce; after another reopen,
both historical results were recovered without proposed writes. The public
native refusal is generic, so this run does not distinguish a stale-root
failure from a duplicate transaction marker or other guarded admission rule.
The two simultaneously prepared calls and resulting accepted-event count are
the relevant atomic admission observation. A policy/report grant mismatch was
refused before an intent existed; a separately selected but unavailable grant
was refused in the native observation stage. These tests do not prove SQLite
or filesystem crash durability. Preparing an exact signed call, exiting, and
later submitting it exercises the process-reopen retry path without claiming
an injected process-death or power-loss cut.
