# Guarded cohort TCP adapter (source WIP)

`cohort_tcp.rs` connects the guarded PQ packet/registrar/relay/mailbox path to
fixed enrolled TCP links. It carries exact source frames; enrollment slots are
not Mini sender authority. Independently provisioned PSKs authenticate each
slot/generation/stage/profile/epoch and encrypt private route commitments on the
client-to-registrar links. The honest noncolluding registrar remains an explicit
additional trust premise; receiver still sees ordinary native signatures/graph.
This is neither a full private evaluator nor a formal active/lifetime anonymity
proof. See `PQ-MAILBOX.md` for the restricted shuffle/exact-set construction.

`mini mix-live` has `key`, `send`, `receive`, `cover`, `registrar`, `relay`,
`mailbox`, and `scan` actions. Common public arguments are `--generation HEX16`,
`--slot`, `--phase`, `--width`, `--payload-bytes`, `--origin-ms`, `--tick-ms`,
`--first-epoch`, `--epochs`, `--state`, `--records`, and `--key`.
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
