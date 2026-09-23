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
