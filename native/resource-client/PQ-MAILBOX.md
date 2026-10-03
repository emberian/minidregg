# Restricted PQ cohort cascade and broadcast mailbox

`pq_mailbox.rs` adds a concrete source-compatible traffic construction. It is a
new restricted batch composition using the PQ-KEM/AEAD packet ingredients studied
in Outfox; it is not the Outfox packet format, Echomix protocol, NymHS protocol,
or an inherited proof of their security. The existing scheduled native facade is
separate; this module is a batch codec/operator path, not a deployed resident mix
network or a whole-world privacy theorem.

## Profile and trust

A public fixed cohort contributes exactly one equal-size packet per epoch,
including dummy traffic. Epoch classes repeat application/application/control/
repair. Three fixed independent relay operators process complete batches before a
separate mailbox receiver. Every hop has an ML-KEM768 key pinned outside the
packet. At least two honest client inputs, at least one honest whole-batch shuffle,
an honest noncolluding registrar, an honest receiver, authenticated confidential
client-to-registrar enrollment/commitment submission, bounded processing before
public release, trusted private durable storage, and static corruption throughout
the protected epochs are explicit premises. Presence, cohort, public failure,
capacity, epoch/key inventory, relay endpoint chain and broadcast audiences are
public. The registrar is an additional substantive trust choice, not a hidden
consequence of 'one honest relay'. It sees private paired route commitments and
could identify mappings if compromised/colluding. Receiver sees ordinary native
signatures and graph; this does not hide source author from that receiver.

All four layers instantiate AWS-LC's existing ML-KEM768 with XChaCha20Poly1305,
HMAC-SHA256 context key derivation and key/cipher binding. The complete next packet
is AEAD-covered at each layer. Public epoch, cohort width, payload capacity and hop
are bound as associated data. Every encapsulation and nonce is fresh. A layer adds
1,160 bytes:1088 KEM,24 nonce,32 key/cipher binding,16 AEAD tag. Logical body
payload P defaults65,536 and is publicly bounded1,024..262,144. The core includes
an immutable operation ID and random32-byte reply capability. Native carrier size
must fit P-66 before dispatch. Large native frames require a future matched
fragmented batch adapter or a larger qualified public profile; they are not
silently truncated. Existing full-frame scheduled facade is still available.

## Active admission guard

AEAD plus a shuffle alone does NOT close valid injection/replacement or n-minus-1
attacks. Each client privately submits hashes of all five successive packet forms
along with its authenticated cohort slot. The honest registrar authenticates one
slot per enrolled client, then publishes independently sorted EXACT hash sets for
all stages, with separate registrar/operator MACs under independently provisioned
keys. Those published sets do not pair a source/input hash with a successor hash.
The registrar must not disclose the private pairing vectors; `*.route` files are
secret test/client evidence, not public routing material. This CLI uses protected
file handoff for that operator boundary; live authenticated enrollment/transport
is a required deployment adapter, not implied by CSV paths.

Each relay and receiver checks its own manifest MAC/pinned epoch/profile, the
complete admitted input hash set, and the complete peeled output set before any
batch claim, forwarding or native effect. Corrupt operator0's MAC key cannot forge
operator1's manifest. Any dropped/duplicated/injected/changed valid packet refuses
the entire epoch rather than releasing a distinguishable partial batch. Hash
collision/preimage resistance and independent MAC authentication are cryptographic
premises. An honest client's faulty core or a malicious enrolled participant can
abort a cohort; this is availability failure. Do not treat the implementation
checks as a formal active/longitudinal anonymity theorem. The precise reduction
from these checks plus hidden registration and honest shuffle to the declared
observation game remains a cryptographic composition proof obligation.

Complete batch input hash is journaled, then a claim is fsynced before processing;
exact complete output is cached. Changed replay refuses. A claim without full
output after crash is uncertain and never authorizes reprocessing or semantic
mutation. All decrypted cores are validated before any native dispatch. Original
native public-envelope gate and source service remain the final authority; the
mailbox uses `scheduled_transport::dispatch_once` with immutable native dispatch
marker, exact bytes, reserved class retention, cached reply and uncertainty fence.
No raw internal recovery event is admitted as an external native command.

## Broadcast replies and capabilities

Receiver publishes exactly W equal-size reply ciphertexts in a single broadcast
batch, in secret shuffled order. Every cohort client receives/scans the same whole
batch; retrieval does not name a mailbox/item/recipient. The intended client opens
its reply using the one-time32-byte capability embedded only inside receiver
protection. This removes contact-created SURB routes, seeds and SURB rewrapping
from this profile entirely; it does not pretend to implement NymHS defenses.
Reply epoch/class/operation identity are authenticated; no public recipient tag.

Client journals `spent` BEFORE releasing decrypted reply, then caches exact opened
bytes. Duplicate independently encrypted replies under one capability refuse
without consuming it. A spent record without full cached opened bytes after crash
is uncertain and cannot reuse the capability. Source-owned fresh canonical lookup
through reserved repair is required, with stable inner operation but a fresh outer
capability/packet. Existing source exact-resubmit authorization still governs
semantic mutation. Capability class quotas are application128/control64/repair64;
application can't drain repair. No unilateral retirement, deletion, external
antirollback anchor, filesystem rollback defense or forward secrecy is claimed.

## Executable operator path

`mini mix --action key --state PRIVATE --secret SK --public PK` generates an
ML-KEM768 operator/receiver key. `registrar-key --state PRIVATE --secret KEY`
generates an independent32-byte registrar/operator authentication pin. There are
three relay pairs plus the separate receiver, and FOUR distinct registrar pins.

Every ordinary action requires `--epoch E --width W --payload-bytes P --state S`.
`seal --keys PK0,PK1,PK2,PK3 --output PACKET [--request EXACT_NATIVE_ENVELOPE]`
creates one real/dummy packet and secret PACKET.route; real calls retain immutable
body/operation ID/capability. Optional `--operation-id` binds a previously retained
exact body; changing it refuses. This option is not source mutation retry authority.

Trusted registrar: `batch --inputs PACKET_PATHS --commitments ROUTE_PATHS
--auth-keys AUTH0,AUTH1,AUTH2,AUTH3 --manifest MANIFEST --output BATCH0`.
Relay i: `relay --hop i --secret SKi --auth-key AUTHi --manifest MANIFEST
--input BATCHi --output BATCHi+1`. Receiver: `mailbox --secret SK3 --auth-key AUTH3
--manifest MANIFEST --input BATCH3 --output BROADCAST --target EXISTING_UNIX_HOST
--config EXACT_NATIVE_CONFIG`. All batch/relay/mailbox outputs require public
`--origin-ms ORIGIN --tick-ms T`: admission and argument validation precede
processing, release occurs at the configured epoch/stage time; missed epoch fails
closed with retained uncertainty, no catch-up bursts. Operator must supply complete
cohorts each epoch; the CLI does not create a resident daemon or repair a missing
peer by traffic-triggered membership changes.

Client: `scan --input BROADCAST --output OPENED_RECORDS`. Output is a sequence of
length-prefixed private transport outcomes:0 exact original native Host frame,
1 uncertainty,2 known predispatch refusal. It is not itself a Mini receipt or
Commit/Abort/Ready/Applied; native source decodes/adopts any actual outcome. No
proxy/native status is inferred from a missing reply or packet.

## Costs and proof boundaries

Each client uploads P+4,640 bytes per batch before access framing; internal layers
are P+3,480/P+2,320/P+1,160 bytes per packet. Each client receives W*P+19 bytes of
broadcast. Registrar manifest is18+160*W+128 bytes, plus secret160-byte commitment
submission per client and authenticated enrollment/control framing. MAC/KEM key
provision and public key rollover are extra. At P65,536,W16,T1s, client raw request
plus broadcast is1,118,771B/s, or2,899.854432GB/30days; app/control/repair ratios
split useful opportunities1/2,1/4,1/4. These are parameter calculations, not Mini
measurements. P4,096,W4,T1s gives25,139B/s/client,65.160288GB/30days. Broadcast
fanout and scans grow linearly PER CLIENT; aggregate downlink is quadratic in W.
This buys retrieval privacy without assuming an undefined malicious/PQ PIR.

One batch has four per-packet ML-KEM encapsulations at the client and four
operator decapsulations across the chain. Current guard also decapsulates for
preflight then processes, so operator computation repeats twice; this is an
implementation cost, not a paper performance claim. Operator release lag is five
public stages from client aggregate to receiver. Backend may take longer than its
public processing allowance; source async continuation/service fairness and WCET
must be qualified. Variable native Host work is not private MPC or hidden access.
All key histories, later opening, compromised endpoints, side channels, public
application outputs and authorized Pending retain their declared leakage/trust.
Ordinary native signatures remain classical: PQ packet encryption is not a full
PQ OO/agreement stack. Fixed routes avoid independent-route bad-event accumulation
but require an honest shuffle operator over the entire claimed lifetime. Historical
key compromise or disclosed registrar pairing invalidates that lifetime premise.

`qualification/pq-native-pipeline.py` is a provider-free receiving orchestrator:
two real canonical native repair lookups, two cover clients, three distinct relay
processes +receiver, scheduled release, exact source frames recovered through full
broadcast scans, and a valid injected ML-KEM packet rejected before relay claim.
It is a local process/file handoff experiment, not a deployed multi-host network
trace qualification. Focused tests additionally cover key/epoch/tag tamper,
changed replay, crash claims, duplicate capability drain, consumed crash recovery,
independent operator authentication and admitted-set substitution. Full source
privacy work remains active: live authenticated cohort adapters, network lifecycle
and fixed polling/rekey/recovery, source-private custody/evaluator, source-visible
Pending relation, WCET/full trace experiment, and formal composition reduction.

### Review corrections before integration

A real carrier over its public body/capability quota now substitutes a valid
same-shape COVER packet and records an owner-private `*.private-refusal`; it never
removes the cohort slot or deletes previous obligations. The refusal is a physical
predispatch carrier outcome, not a source-authored Mini Pending/Commit/refusal.
Native journal admission errors become private conservative uncertainty inside the
fixed broadcast rather than dropping the whole batch after possible partial
native effects. Two identical immutable transport operations may receive separate
reply capabilities while the native journal preserves one dispatch; identity/body
conflict is fenced. Keys must be distinct within both KEM and registrar pin lists.
Registrar and operators durably bind manifest digest and local public clock/profile
for each epoch; changed registration/clock on recovery refuses. This does not make
an unimplemented live enrollment channel authentic by itself.

Adversarial review confirms the exact-set check precedes native effects and closes
valid replacement under the declared honest-registrar/static model. It also
identifies the remaining timed-work pole: synchronous variable Host work may miss
a release. A deadline is privacy ONLY with established WCET or a source-owned
private async continuation with same-shaped scheduled progress. Neither source
Pending nor backend completion may be synthesized by this mailbox to claim that
pole closed. Full live privacy qualification remains open.

### Receiving results, 2026-10-03

Seven final focused PQ tests passed (769 other tests filtered,0.03s); release
binary passed. Both were under assigned8G swarm-build/jobs2 in an independent
warm target; scheduled tranche nine tests/common integrated build also passed.
Final source SHA256957ae0605ec868732bb851f350d0b29379264c9d9677c25fd2d06104773fa344.
Captured guarded binary SHA256a5fe4ee00684ff80d71690ffdb0cc261794b6fe4310ba24e8791980bd291739c.

Native guarded pipeline at1s phase FAILED its receiver release allowance: two
real canonical repair lookups exceeded that budget, after exact journals were
retained. No broadcast/catch-up was emitted. This is decisive observed evidence
for the WCET/async continuation gap, not a hypothetical warning. No source mutation
was retried. A fresh cohort at5s phase PASSED: two genuine native repair lookups,
two cover slots, three distinct ML-KEM relay processes, separate receiver, all
per-stage manifest guards, exact original source reply frames recovered by local
broadcast capability scans, repeated local read returning identical cached bytes,
and a fully VALID freshly encrypted injected packet rejected BEFORE relay claim.

Native receiving log traffic-pq-native-5s.log; negative pole traffic-pq-native.log;
full supervisors/pytest-free test orchestration qualification/pq-native-pipeline*.py.
Generated test keys/paired routes stay private on hbox. This was process/file
handoff with actual native Host authority; no independent-host/TCP mix deployment,
source-visible status/privacy reduction or malicious MPC experiment is implied.
At P4,096,W4,T5s, derived raw request+broadcast65.160288/5=13.0320576GB/client-month,
excluding manifest/enrollment/link overhead; useful repair opportunity1per20s.
This parameter is a measured successful receiving profile, not a demonstrated
worst-case private-world service or blanket anonymity claim.
