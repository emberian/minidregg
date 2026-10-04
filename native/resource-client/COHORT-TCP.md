# Guarded cohort TCP adapter (source WIP)

`cohort_tcp.rs` connects the guarded PQ packet/registrar/relay/mailbox path to
fixed enrolled TCP links. It carries exact source frames; enrollment slots are
not Mini sender authority. Every link key comes from a roster enrollment (below)
and authenticates each slot/generation/stage/profile/epoch record and encrypts
private route commitments on the client-to-registrar links. The honest
noncolluding registrar remains an explicit additional trust premise; receiver
still sees ordinary native signatures/graph.

## Roster enrollment (MCE3, hybrid X25519 + ML-KEM-768)

The public cohort roster (`minidregg-cohort-roster-v2` JSON: `generation`,
`width`, `members[width]`, `operators[5]`, each `{native, linkKey}` hex, `linkKey`
being the 1,216-byte hybrid public key X25519 || ML-KEM-768) is the
only admission authority. Phase 0 slot i is sent by member i; phase k>0 by
operator k-1 (registrar, relay0, relay1, relay2, mailbox); phase k<5 is received
by operator k and phase 5 slot i by member i. Its exact-byte SHA-256 enters
every transcript and pin, so both ends must hold the same roster.

The receiver sends `MCE3 | nonce32 | ephemeral hybrid public key` (1,252 bytes).
The sender answers with a hybrid encapsulation to the receiver's roster link key,
a hybrid encapsulation to the ephemeral key (each 1,120 bytes: an ephemeral
X25519 key and an ML-KEM-768 ciphertext), and an Ed25519 signature by its own
roster native key over (domain, profile identity, roster digest, start epoch,
the whole challenge, both ciphertexts) (2,304 bytes). Each encapsulation is
`hybrid_kem` (one cSHAKE256 over BOTH shared secrets and the full transcript,
the combiner private rooms use; either primitive alone keeps the key secret).
The link key is HMAC-derived from both encapsulation keys and the signed
transcript; the receiver's 32-byte
acknowledgement proves it holds the roster link secret. Garbage, a non-roster
or wrong-slot key, a response replayed from an earlier challenge and a stalled
peer are dropped and the listener re-accepts until the public start deadline;
none consumes the link. Handshake reads/writes are bounded at 3 s (a LAN round
trip must fit). Native signatures are classical Ed25519: the key exchange is
hybrid, the signer authentication is not yet. A v1 roster, an `MCE2` challenge
and a bare ML-KEM link key refuse by name.

The receiver retains the signed transcript (`enrollment-*.signed`, admission
evidence) and writes `enrolled-link` into its record directory before adopting
any record. Network-fed workers (`registrar`, `relay`, `mailbox`, `scan`) take
`--roster` and consume an input directory only if its marker names the exact
upstream link (phase, slot) and the roster's sender key: an operator directory
list cannot relabel slots. Senders take `--native-key SEED` (a `mini keygen`
seed); receivers take `--link-secret/--link-public` (a `mini mix --action key`
pair, the secret a 96-byte seed that regenerates the public key, checked against
it and against the roster). Outer wires are
sealed under the connection's key and never persisted; a resumed link re-enrolls
and reseals its durable inner inventory. Profile pins carry codec `MCE3`: state
from the pre-shared-key codec and from MCE2 refuses to resume.
This is neither a full private evaluator nor a formal active/lifetime anonymity
proof. See `PQ-MAILBOX.md` for the restricted shuffle/exact-set construction.

`mini mix-live` has `send`, `receive`, `cover`, `registrar`, `relay`,
`mailbox`, and `scan` actions. Common public arguments are `--generation HEX16`,
`--slot`, `--phase`, `--width`, `--payload-bytes`, `--origin-ms`, `--tick-ms`,
`--first-epoch`, `--epochs`, `--state` and `--records`; links add `--roster`.
Phases0..5 mean client contribution, registrar batch0, relay0/1/2 output, and
whole broadcast. The bounded public lifetime is1..4096 epochs. Explicit
`--resume-epoch` starts a future slot inside the original pinned lifetime;
historical obligations remain intact and missed slots never create catch-up
bursts or semantic retries. Each role/slot requires separate private state and
record directories; client caps are separate from the actor's lock directory.

Client `cover` provisions one valid packet plus secret160-byte route vector for
every configured epoch before TCP transmission. Private admission exhaustion,
absent real work and oversize requests retain this cover inventory. An optional
source-authored `epoch-E.intent` is mode1/id16/initial-cap32/exact-native-envelope,
or mode2/id16/original-traffic-class1/body-digest32/recovery-access32/fresh-reply-cap32.
Mode2 is fetch-only and restricted to reserved repair epochs. It grants no native
authority and cannot dispatch another semantic operation. Real reply caps use
the original128/64/64 class quota and exact retry fence.

Registrar reads all authenticated contribution files and invokes the actual
guarded exact-set registration function. Relay workers verify their independent
operator MAC and exact input/peeled-output sets before claim or forwarding.
Mailbox verifies all cores before offering to the source-owned `AsyncDispatch`.
The gateway durably reserves class/access/exact request; fixed workers perform
the native exchange independently. A physical continuation is kind3, outside
the original native frame; it is not Mini Pending or an admission receipt.
Source-native frames remain kind0; unknown effects remain fenced. Fetch binds
the immutable original access, class and body digest to a fresh reply cap.
No mix slot is relabeled as backend sender authority.

Every client downloads the same full broadcast. `scan` releases only private
capability-authenticated physical outcomes and preserves spent/opened fences.
Mailbox remains resident for a public `--custody-hold-ms` after the configured
lifetime (default600000); source responsibility remains durable on later crash.
Original source authority still owns canonical recovery and final evidence.

The fixed link plaintext contains private ready/unavailable marker, length and
one public-capacity payload. Wire overhead is89bytes. Contribution capacity is
P+4640+160; stage capacities include the exact manifest and complete padded
batch; broadcast is19+W*P. Endpoints/cohort/clock/lifetime/capacity are public.
The precomputed valid contribution fallback is distinct from physical unavailable
stage records. Neither becomes an invented source status.

## Qualification at immediate source shipment

Authored source, five cohort tests and five async custody tests compiled and
passed10/10 (776 skipped,0.809s); owned mini release passed under8G/jobs2,
offline/locked independent target. Original PQ regression passed9/9 on the
already compiled test executable with no additional Cargo build.

The longer actual1-second TCP experiment REFUTED this WIP sender: after ten
all-cover slots, synchronous per-slot durability/crypto preparation missed the
public send deadline and twelve links stopped. No native workload participated.
The two-slot loopback test had passed; it did not establish sustained cadence.
This source is being shipped as WIP, not reported as a functioning full cohort
service. The owner is replacing the disk-dependent emission loop with precomputed
durable fallback wires and asynchronous preparation, retaining source journals
and no-second-effect fences. Increasing the phase length is not that repair.

The reusable receiving script accepts explicitly supplied native fixtures and
socket; no generated keys, journals, native requests, captures or live fixtures
belong in the source packet. Independent-host deployment, trusted initial clock/
resource qualification, public rekey/lifecycle service, source-endpoint ABI,
private execution/custody composition and a full observation-game proof remain
required. Source-visible Pending is leakage only where explicitly declared.

## Incremental emission repair

Sender seals its fallback inventory in memory before the public lifetime (since
MCE2/MCE3 the outer wires are never persisted; the inner cover is the durable inventory);
client fallbacks are valid registered cover contributions, later stages use padded
physical unavailable records. A separate worker prepares exact ready wires. The
clocked network loop only reads in-memory buffers and writes the socket; no fsync,
native execution, packet sealing or private producer runs on that loop. Lifetime
inventory is publicly bounded64MiB (ready buffers may temporarily add a matching
amount). A fixed25ms operating-system scheduling allowance applies to every slot
with minimum public tick100ms; exceeding it declares a fault with no catch-up.
This is an explicit scheduling premise, not a native worst-case time certificate.
Repeated historical slots are never emitted on resume. Persisted source/capability/
custody state remains authority; ready/fallback files are not delivery receipts.

Five focused cohort tests PASS after repair (781 skipped,0.807s). Release rebuild
and actual sustained1s matched TCP/native receiving qualification are pending at
this incremental publication. Earlier failed evidence is preserved separately.


## Sustained pipeline repair (incremental source)

The first emission repair compiled and its owned release passed. A12-epoch,
1Hz all-cover receiving run then delivered ALL144 fixed TCP records without
shape/timing failure, but useful authenticated relay processing missed release
preparation in some epochs. Physical cadence alone is not useful delivery.
The retained failed evidence includes that processing refutation.

The current source reduces durable receive storage to one authenticated canonical
record and one ready wire, and bounds the asynchronous adoption queue to64MiB.
A local uncertain adoption drains the full public network lifetime before reporting
its local fault; consumers never see unfsynced input. Live relays now combine the
profile, clock, exact manifest/input hashes and shuffle claim into one immutable
admission, followed by one exact full output. A claim without output stays uncertain;
legacy ordinary CLI journals are refused by the live codec rather than replayed.
Ordinary CLI persistence is unchanged. Relay output remains durable before publication.

`--processing-slots` is a public1..32 profile field (default2). Every stage still
emits one record per second at a1Hz tick, but its fixed stage latency is2 ticks:
the contribution-to-broadcast path is11 ticks after the public origin. This is not
1-second end-to-end delivery and is not a worst-case processing certificate.
The receiving script now uses64 epochs,32 two-slot buffer lengths, complete
fill/steady/drain, and separate all-cover/native poles. It requires a valid broadcast
for every epoch, two exact historical native lookups behind a byte-transparent
2-second delay, physical continuations, fresh-cap reserved repair fetches, and
no second dispatch. These latest source changes are uncompiled at this shipment;
actual sustained receiving remains pending. No source-private raw ingress is enabled:
its native current-enrollment/funded ordered endpoint is separately being constructed.


The grouped-admission/pipeline source compiled: nine focused tests PASS9/9
(779 skipped,0.852s), covering6 cohort tests, original active exact-set guard,
new live journal crash/replay/refusal fences, and actual async multihop
continuation/fetch. Owned release PASS under8G/jobs2/offline/locked independent
target. Frozen cohort5f32fe/PQ5014081e; scheduledc2b6/async8220 unchanged.
First contribution is at origin+1 tick; first broadcast at origin+11 ticks with
processing-slots2, so contribution-to-broadcast latency is10 ticks. Sustained
receiving is running and remains unqualified; proof/measurement claims above
are intentionally separated. The exact-set check reuses its authenticated
peeled packets before the durable claim, removing a duplicate ML-KEM pass.


## Outer preparation and durable input publication repair

The64epoch all-cover experiment observed ALL768 fixed TCP records, lateness
0.08..1.73ms. However only33/64 useful broadcasts completed; registrar/relay
output counts were64/49/44/39. No native work ran. This refutes useful sustained
service for that source despite successful physical cadence. Some prepared inner
outputs existed well before wire generation while the redundant outer-cache
fsync blocked publication; other outputs arrived after premature half-tick sampling.

The next source keeps durable valid cover inventory and original relay/native/cap
journals, but seals real outer wires into bounded memory. A readiness producer
can provide an exact inner body until the fixed public25ms cutoff. The independent
emitter selects one prepared wire or fallback at each original public deadline.
No encrypted real-wire cache is a source receipt, and none is now persisted.
A pre-emission crash may reseal with a fresh outer nonce; future-only resume
cannot retransmit released epochs. Public processing slack is still2 ticks.

Durable record adoption additionally publishes an empty availability token only
AFTER record fsync succeeds: hard-link visibility alone does not prove directory
durability. Tokens are not journal receipts; a crash-lost token stays fail-closed
until exact re-adoption. Eight focused cohort tests are authored, including late
producer selection past the old half-tick sample and visible-unqualified input
refusal. This latest source is uncompiled at publication. Full sustained receiving,
native/recovery consumer and independently hosted privacy qualification remain active.


The in-memory preparation source passed8/8 focused checks and owned release.
Actual renewed all-cover receiving then caught a newly joined consumer bug:
its wait condition woke on the visible record before its post-fsync token, so
it immediately treated input as unavailable. Fixed physical records still all
emitted; useful pipeline qualification failed. The worker now waits for the
adoption token, and the existing unqualified-record test exercises the actual
waiter until real adoption. The narrow consumer repair is source WIP pending
one targeted check/release and renewed64epoch paired receiving.
