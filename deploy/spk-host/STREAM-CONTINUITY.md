# Read-only stream continuity

The resident can keep an admitted human browser WebSocket alive without adding
another app dispatch or billing record. It begins a continuity probe halfway
through each authority lease. The old deadline still applies while the probe
runs. Failure, revocation, expiry or a changed checked projection closes the
stream. A successful probe extends the deadline from **request start**, never
from response arrival. The default lease remains 60 seconds; operators can
configure its positive lifetime as described in `WS-AUTHORITY-LEASES.md`.

## Source receiving protocol

Private operator opcode **152** accepts a canonical
`DREGG/APPLICATION/STREAM-CONTINUITY-REQUEST/v1` request containing:

- Domain and runtime semantics, exact app/process generation, human web session
  resource/generation, subject, ticket and checked session fingerprint.
- A random 32-byte stream nonce, a new random 32-byte attempt nonce, and the
  stream's minimum accepted-history height/world root.
- A freshly signed authority ingress. Its entire canonical challenge is inside
  the signed request bytes, using the reserved subprotocol
  `dregg.authority.continuity.v1`. Unsigned authoring opcode36 supplies no grant.

`ApplicationStreamContinuity.receiveVerified` uses
`NativeHostReplay.admitDispatchVerified`, retaining the verifier's historical
share-issue provenance and its `CheckedCurrent` native admission. App serving
state, session state, enrollment, ticket, permissions and issuer lineage are
checked against that current verified image. Its private `Attestation` type
requires exact challenge/signature binding, namespace, human web origin,
current fingerprint/custody and non-regressing history. Its retained verified
image and receipts are unchanged.

The attestation reaches the physical host only inside `withFreshTip`: the
source rereads the exact last physical entry and compares its record, height
and MAC for the verified chain. The response is a separate
`DREGG/APPLICATION/STREAM-CONTINUITY-ATTESTATION/v1` frame, containing the exact
challenge plus height, chain and world root. This is authenticated by the
pinned private operator path, not a portable bearer token or caller JSON.
Inspection is representation only and does not authenticate a supplied frame.

There is no call to Store CAS/append, checkpoint, app fd3, or dispatch delivery
in this receiver. Live opcode34 explicitly refuses the reserved probe shape,
preventing a continuity request from accidentally becoming a billed app open.
The generic current-admission logic is reused without weakening its predicate
or adding an owner override. Future changes to that source law remain effective.

## Physical receiving and lifecycle

The physical host obtains namespace metadata from its pinned Host executable
and binds the exact committed open's custody, fingerprint and receipt tip once.
It allows one outstanding attempt per lease. The native probe pipeline alone
constructs the opaque reply object: private op152 response, exact retained
challenge and source inspector output. The Rust receiver rejects mismatching
frame echoes, duplicate/noncanonical fields, another delegate or stream,
nonce replay, superseded attempts, changed fingerprints, regressing heights,
and a different root/known chain at the same height.

Only a checked single-use result can renew. The lease cannot be rebound, and
an expired or revoked lease cannot be revived even by a previously verified
reply. Regrant requires a newly admitted open. Frame handoff guards and the
watch/timer remain active during all authoring and verification. This remains
bounded asynchronous revocation: bytes already forwarded may finish, and a
later authority change does not atomically undo prior admission.

Renewal scheduling runs on the existing fd3 LocalSet, with at most one blocking
native job per live stream. Local helper subprocesses and Unix connect/read/
write use the old lease's absolute deadline; an unresponsive helper is killed
and reaped. Full Unix accept backlogs cannot leave connect waiting forever.
These are bounded local transport/process waits, not repeated Mini authority
polls. Pump closure signals the lease on all exits, ending its renewal worker.
Local filesystem stalls and OS scheduling are not hard realtime guarantees;
the independent handoff guard still refuses new work after observed expiry.

Each attempt owns a fresh private temporary directory and removes only its own
artifacts after inspection. No active-dispatch marker, operation ledger entry,
or per-frame Mini event is created. The admitted open's existing one-shot
journal semantics remain intact, including failed late delivery.

## Qualification boundary

Rust tests cover exact source-frame matching, delegate/nonce isolation,
replay/supersession, tip rollback/fork, delayed replies, expiry during probes,
and actual Unix/Cap'n Proto traffic continuing beyond its initial lease then
stopping in both directions on revocation. Existing RPC regressions, bounded
private transport tests and the operator-only opcode152 gate also pass.

These are physical receiving tests, not evidence that a joined live Mini
candidate performs seamless two-delegate editing. Source compilation and the
actual wire/Store journey must be recorded separately. Required common-candidate
journey: two delegated EtherCalc clients survive multiple renewals; accepted
record count stays unchanged during renewal; owner revokes A; A's new writes
stop within the configured bound and new opens refuse while B continues;
regrant cannot revive A's old socket; generation STOP closes all streams.
Measure renewal latency and capacity under concurrent streams. Contention or
slow verification fails closed; it must not be hidden by extending stale leases.
