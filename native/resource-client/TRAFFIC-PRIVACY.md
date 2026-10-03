# Native scheduled traffic construction

This native tranche carries exact Mini Host envelopes through a persistent,
authenticated, fixed-shape duplex stream. It supplies a public-endpoint traffic
profile and native integration substrate. It does not claim source anonymity,
Host-blind execution, a full post-quantum stack, or a completed alpha privacy
qualification. The stronger mix construction remains a required active workstream.

## Native boundary

`mini traffic --action client` exposes an owner-private Unix facade. Existing
participant commands use that facade with their ordinary `--socket`, preserving
config/Host pins, original signatures, canonical ingress, current-authority checks,
and exact retry bytes. No new semantic evaluator or transport authority is added.
The server uses `transport::public_envelope` and `exchange_unix` against the same
source-owned Host boundary as the existing public byte proxy. Operator-only calls
remain outside this gate. The network cannot confer authority by possessing its
transport key.

This includes ordinary say/read/query, source fetch, withdraw, status, origin
outbox, selected-release submit/lookup, recipient admission and custody/recovery
calls that the existing public surface accepts. `say`, `withdraw`, and paid
addressed status notices remain distinct semantic room entries. A status notice
is not a final result; transport never parses those bodies to decide otherwise.

The existing `FnOriginOutbox.Prepared` retains the exact carrier and separately
re-admitted origin receipt; that is not a recipient receipt. Likewise a physical
traffic reply is not disclosure authorization, remote application, custody
qualification, Commit/Abort, or Ready/Applied. Private share material must be an
opaque already-authorized carrier; current clear Host RPC exposes its selected
semantic request to the server. Private computation/custody adapters are separate
source-owned joins.

## Commands and capacity

All options take values. Example using a provisioned per-peer 32-byte key:

```
mini traffic --action key --state /private/key-state --key /private/peer.key
mini traffic --action server --state /private/server-state --key /private/peer.key \
  --listen 127.0.0.1:23091 --target /existing/mini.sock --config /existing/operator.json \
  --cell-bytes 65536 --tick-ms 1000 --pending 16 --retained 4096 --max-envelope-bytes 65536
mini traffic --action client --state /private/client-state --key /private/peer.key \
  --connect 127.0.0.1:23091 --local-socket /private/traffic.sock \
  --cell-bytes 65536 --tick-ms 1000 --pending 16 --retained 4096 --max-envelope-bytes 65536
```

The client maintains one connection while resident, including idle periods.
A new connection uses fresh server and client nonces, direction-separated HMAC
keys and sequence-bound XChaCha20-Poly1305 cells. The native call length, ticket,
class, sequence and fragment positions stay inside encryption. Every cell has
exactly `cell-bytes` bytes in either direction. A startup handshake has two fixed
32-byte messages. Enrollment/session start/stop, endpoints, key/profile epochs,
cell size, configured opportunities, IP/TCP faults and presence are public.

The public cycle has two application opportunities, one control opportunity and
one recovery/repair opportunity. Empty opportunities carry authenticated dummy
cells. Each direction sends at most one cell per configured interval, including
after delay; no debt-driven catch-up burst is allowed. Response computation runs
in a separate bounded worker. Completion does not emit an additional packet.

Three local sockets select the public service class without parsing semantic
bodies: `/private/traffic.sock`, `.control`, `.repair`. Status/discovery/rekey
callers can use `.control`; canonical decision recovery, exact lookups, fetch and
repair use `.repair`. Ordinary native callers retain their existing `--socket`
API. The source recovery job owns its continuation and service entitlement;
skipping optional status cannot cancel canonical recovery. Neither recovery nor
control borrows the other's reserved opportunities during overload.

Raw payload capacity per cell is `cell-bytes - 58` (42 encrypted framing bytes,
16 authentication bytes). At 65,536 bytes and 1Hz, the application class gets
32,739 raw carrier B/s each direction; control and repair each get16,369.5B/s.
This excludes native envelope overhead, handshake, link framing/TCP/IP, retransmit,
retained-response polling and cryptographic computation. Two directions cost
339.738624GB per30day month per peer before those extra legs. This is a parameter
calculation, not a Mini benchmark. Larger observed narrowed proofs (~65KB) and
maximum native12MB frames fragment under the same profile; the body bound comes
from the existing native transport, not a reduced privacy-specific semantic limit.

Population is provisioned as independent peer profiles/listeners with independent
keys and state, rather than one room-wide transport secret. The command currently
serves one independently keyed resident peer per listener. Multiplexing a variable
cohort behind one visible endpoint requires an authenticated profile inventory and
per-peer queue/schedule quotas; it must not share the key between peers or make
only active participants connect. That deployment integration remains explicit.

## Exact uncertainty and retention

Before forwarding any Host frame, the server fsyncs an immutable dispatch marker.
It then retains the exact native reply. A replay with the same transport ticket
must carry identical original bytes. A restored marker without a complete reply
returns transport uncertainty and never dispatches the call again. Cached replies
are returned as the original bytes. The client closes the local facade on that
uncertainty; it never returns synthetic Host refusal/absence/Commit/Abort. Existing
native lookup and exact-resubmit authorization govern semantic recovery.

Local caller loss does not cancel a retained call. Restart queues the same ticket
and exact envelope; fresh session keys/sequence do not authorize a fresh effect.
Even signed valid snapshots from another custody/attempt generation cannot be
inferred as current by this wrapper. Candidate, InvocationID, AttemptID and
custody-generation relations remain source-owned inside the body.

Files are owner-private and immutable. A fsynced temporary file is linked into
place without overwriting prior material; crash-left temporary files are not
receipts. There is an explicit retained-obligation ceiling. New admission applies
backpressure before sending; it does not erase accepted requests, dispatch markers
or reply records. The tranche deliberately does not implement unauthenticated GC,
unilateral expiry or truncation of history. A safe epoch retirement/transport-ticket
closure construction must retain semantic dedup and canonical recovery rights.

The process assumes trusted owner/root and honest local durable storage. Filesystem
rollback, administrative key exposure, swap/snapshot leakage and shared-UID
compromise defeat those premises. A service lock prevents two local owners from
consuming the same journal. The PSK profile has no forward secrecy against later
PSK compromise; it needs trusted confidential provisioning. Native signatures,
SSH, provider execution and earlier stored data retain their own assurance models.

## Active observation game and explicit limits

Compare executions with the same public profile/endpoints/presence, network fault
schedule, provisioned quotas and deliberately allowed application outputs. Change
which secret method/object/member/dependency/result/status/repair item occupies
scheduled cells. A network observer sees the same cell-size/opportunity classes
and learns no plaintext through authenticated encryption under its assumptions.
Replay, tamper, direction/epoch substitution and fragment conflict refuse. Dropping
or delaying messages can deny progress; this module does not make an anonymous
reliable network out of an adversarial TCP peer. Scheduling under load still needs
WCET/headroom and observer-trace qualification, especially durable I/O at admission.
A fixed logical cell is not a theorem about TCP segmentation or total trace privacy.

Authorized callers see their actual outputs, latency, refusal, absence and Pending
when the source interface releases them. This is not automatically legitimate
leakage merely because current code exposes it. The source disclosure/privacy
relation must declare which output/failure/partition observations are permitted.
A chosen partition may correlate Pending across different resources participating
in one joint call; that is not proof of aliasing, but may reveal a required-set
relationship. This transport cannot mask that plaintext semantic leak by padding
packets. Current decision and release owners must qualify the observation game.

This profile exposes source-to-server enrollment/endpoint association. It hides
activity/size classes only within public resident scheduling and cryptographic
premises; padding alone does not provide mix anonymity. The server sees decrypted
ordinary Host requests and its native graph. Private computation, hidden participant
selection and oblivious state access must live behind the exact private receiver.
Public validator/worker schedules are compatible; privately selected duties need
additional participation-hiding construction.

## Source-identity hiding construction remains active

The same native byte facade, ticket/fragment journal and independent repair quotas
are the receiving contract for a stronger anonymous mailbox endpoint. Its next
construction tranche must instantiate an actual mix packet/scheduler, not an
arbitrary relay labeled anonymous. Current positive primary options are Echomix's
symmetric courier/echo protocol, Outfox's PQ packet format, and NymHS's active
opposite-party reply defenses. They are mechanisms with distinct models; their
composition, codec and active rewrap/seed behavior must be qualified in source.

Required executable joins: one opaque mailbox operation instead of object-specific
routes; scheduled polling/status/ACK/backfill/discovery; fixed-epoch fresh reply
capability replenishment; durable reply-capability consumption; fresh outer handles
with stable encrypted inner identity; independent worker/control/repair scheduling;
bounded catch-up after public rejoin; malicious courier/contact/mix tests including
SURB draining and repeated-path/opening history. Direct public committee links can
continue this first profile without sending every MPC gate through the user mix.
The client/server core will need a packet transport adapter whose receive semantics
deliver authenticated opaque cells without causing packet-driven semantic retries.
No existing protocol proof is inherited simply by plugging in a new socket.

## Verification and integration

Scoped Rust tests cover authenticated shape/replay/tamper/direction/epoch, native
frame fragmentation/conflict, exact durable dispatch recovery and retention
pressure, original native public gating + cached replies, reserve service, and an
actual TCP/Unix duplex carrying all three classes followed by idle opportunities.
Those tests establish their named receiving behavior, not malicious MPC, Mini law
validity, anonymity or a whole-world traffic theorem.

Next native acceptance uses a source-matched Host/private test Store and the same
selected-release and message/read/status/withdraw journeys through `.sock`,
`.control`, `.repair`. Interleave lost reply, proxy restart, revoke before fresh
release, exact native lookup, recipient outage, control pressure and return with
backlog1/1000. Compare full public traces while preserving authorized output
leakage. Native selected-release submit cannot be auto-replayed from transport
absence; its existing retained absent-lookup fence remains mandatory.

### Measured receiving evidence, 2026-10-03

Seven scoped Rust release tests passed (760 other tests filtered, 0.40s). The
native binary build passed. `rustfmt` subsequently changed layout only. Tests and
build ran through `swarm-build` and `cargo-bounded`, using the assigned shared
Rust seat; the binary was copied before releasing that seat.

A provider-free receiving experiment used the existing supplied family-90562d76
Host, store and signature verifier with fresh private source/recipient deployments.
An external test supervisor changes only `mini serve`'s socket plumbing: ordinary
Mini authoring/signing/admission remains native, and the receiver's facade goes
through this implementation's TCP stream to the original Unix Host service.
An original selected release installed through application slots. After process
restart, a typed native exact lookup through `.repair` returned `confirmation:
replayed` with identical transactionId, eventId, acceptedCount and worldRoot;
this is the source's lookup response, not byte-equality to the earlier installed
response. A signed native resource read through `.control` returned exactly one
atom containing the original selected packet bytes. The local experiment used
65,536-byte cells at10ms intervals, not the default production cost example.

The unmodified older selected-release acceptance script failed before transport
because its content command schemaVersion1 differs from current commandVersion9.
A private script copy corrected that fixture alone; its original receiving step
passed, then the legacy logical-image `store read-to` failed (`published byte
record is missing`) because the supplied Host uses durable journal state. Therefore
full conflict/wrong-signer/lost-reply/revoke acceptance is not qualified here.
Existing script and existing supplied-world services were not modified.

Evidence in the isolated snapshot: `traffic-test.log`, `traffic-build.log`,
`traffic-native-acceptance.log`, `traffic-native-acceptance-v9.log`,
`traffic-native-recovery.log`, plus the test-only `qualification/` supervisors.
Private evidence contains generated test keys and must not be copied into a
public repository; copy only source, logs with appropriate content review, and
this contract. The binary is `artifacts/mini-traffic`.

### Integration obligations and recurring latency

The reserved repair slot guarantees link capacity, not that a busy native Host
or the single backend worker can execute recovery while another call blocks.
Source recovery admission/service fairness must join the new typed receiver.
The frame gate accepts only existing public-authorized native operations; new
private-custody/controller endpoints require kernel/source-authority ownership,
not a relaxed gate or raw internal JournalEvent handler.

For size L and raw payload P, a request needs ceil(L/P) opportunities in its class.
Application opportunities receive half the stream; control and repair each receive
one quarter. At the default1Hz profile a maximum-size native carrier can exceed
the ordinary600s native caller deadline, especially on reserved classes; response
fragmentation adds further latency. Caller timeout does not cancel or resend an
accepted call. Deployment must select a public faster profile or smaller admitted
carrier class and use source-owned continuation/lookup to retain progress. Do not
quote the maximum decoder bound as a successful600s delivery guarantee.

The stronger source-identity hiding endpoint remains unfinished, with real open
construction obligations: a qualified authenticated mix packet and scheduler;
reply capability inventory and recovery independent of user activity; malicious
relay/contact defenses; and proof that private required-holder selection does not
reappear as link duties or authorized Pending. This code is the exact native
receiving substrate for that work, not its anonymity theorem.

### Frozen second scheduled tranche

Nine scheduled transport tests pass, including resident schedule beyond2^32
ticks, deadline-incompatible public profiles, and reserved retained-record capacity.
Schedule arithmetic now uses checked128-bit multiplication/full64-bit duration,
not truncating tick index. Public KDF context binds pending/retained/max-carrier
limits as well as cell/rate. `--max-envelope-bytes` defaults65,536, bounded by
original native maximum; profile admission refuses two worst-size reserved-class
transfers requiring >570s, leaving30s margin under native600s caller deadline.
This is a transfer budget, not a backend execution-time guarantee. Oversized
backend reply is uncertain after possible effect, never a false predispatch refusal.

Retained history now has application/control/repair quotas1/2,1/4,1/4, respectively
(the remainder goes to repair). Both client and backend enforce them; application
retention cannot consume mandatory recovery space. Exact tickets bind immutable
class files as well as bodies. Earlier journals lacking this class binding fail
closed and are preserved; they need explicit evidence-preserving migration, not
silent reinterpretation, deletion, or a fresh semantic effect. No unilateral GC
or rollback-resistant external spent anchor is claimed.
