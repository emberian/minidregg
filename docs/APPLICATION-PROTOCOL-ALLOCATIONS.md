# Application protocol allocations

Coordination record, September 27, 2026. These allocations prevent concurrent
application and publication implementations from choosing the same tags. A
reservation does not establish an implemented or accepted native path.

## Stable event tags

| `StableEvent.codecVersion` | Family | State at allocation |
| --- | --- | --- |
| 10 | Selected release, original v1 | Earlier source implementation; no qualified native v1 acceptance |
| 11 | Application dispatch | Existing candidate ingress |
| 12 | Application lifecycle BEGIN | New receiver; native routing in progress |
| 13 | Selected release, atom-bound v2 | Assigned replacement for the colliding proposed tag 11 |
| 14 | Source publication authorization | Reserved for source-side admission |
| 15 | Application share issuance | Reserved for special issuance admission |
| 16 | Application lifecycle current claim | Reserved for durable claim admission |
| 17 | Selected fn poll coverage | Reserved for bounded local scan coverage tied to an admitted selected release; no remote completeness claim |
| 18 | Checked application lifecycle completion | Reserved for configured-host attestation and atomic app/manifest completion |
| 19 | Ordered empty-page consumer progress | Reserved for v2 special admission sharing the selected-coverage frontier; legacy content atom tag 9 remains a distinct namespace |
| 20 | Consumer namespace registration | Reserved for a gateway-authorized durable namespace, gateway-independent uniqueness nullifier, and explicit authenticated initial anchor; not native-qualified |
| 21 | Agent dispatch with a claimed reservation | Reserved for replayable dispatch binding the exact delegated purse reservation and consuming its one-use claim; not native-qualified |
| 22 | Grain-backed application share issuance | Reserved for atomic ticket issuance with composite grain birth, current app delegation authority and grain settlement; distinct from bare event15 |

Wire frame revisions, content-object type tags, nullifier codec versions, and
event tags are separate namespaces. Changing a wire frame to v2 does not mean
incrementing its event tag into another family's allocation. Each family must
retain its domain-separated canonical bytes and exact decoding checks.

Event 21 is distinct from ordinary event 11: a private physical permit cannot
add payment authority absent from the admitted durable intent. Its claim must
bind the full application/session/ticket/parent/request context, current signed
payer authority, original admitted reserve, physical purse guard, and a one-use
reserve-claim nullifier. Charging remains deferred until a definite application
response or explicit audited reconciliation; admission does not imply delivery
or automatic settlement. Hard disconnect fences the caller, not the shared app.

Event 20 selects a consumer lineage explicitly. Unrelated historical tag-9
records cannot claim or poison another namespace through copied scope fields.
Fresh registration starts at zero; adopting legacy progress requires the exact
authenticated receipt named by the signed registration. A transport ACK is not
an initial authority witness. The current receiver and replay require a fixed
operator gateway pin for the deployment. That pin is not encoded in runtime
parameters today: changing it can invalidate historical replay even when a new
namespace is selected. In-deployment rotation therefore remains unimplemented;
it needs authenticated historical issuer provenance and an explicit migration
rule. A new namespace alone does not implement rotation or justify a cursor reset.

## Native stdio operations

| Opcode | Operation |
| --- | --- |
| 20 | Selected-release submit |
| 21 | Selected-release lookup |
| 22 | Lifecycle BEGIN submit (reserved) |
| 23 | Lifecycle BEGIN lookup (reserved) |
| 24 | Source-publication submit (reserved) |
| 25 | Source-publication lookup (reserved) |
| 26 | Current lifecycle launch claim (reserved) |
| 27 | Current lifecycle launch claim lookup (reserved) |
| 28 | Application share-issue submit (reserved) |
| 29 | Application share-issue lookup (reserved) |
| 30 | Current-image application birth intent authoring (reserved; no commit) |
| 31 | Current-image application-session birth intent authoring (reserved; no commit) |
| 32 | Current-image application share-issue signing plan (reserved; no commit) |
| 33 | Application share-issue detached signature assembly (reserved; no commit) |
| 34 | Fresh checked application dispatch (source route; native qualification pending) |
| 35 | Historical dispatch receipt-only lookup (never a delivery permit) |
| 36 | Application dispatch signing plan (reserved private authoring; no commit) |
| 37 | Application dispatch detached signature assembly (reserved private authoring; no commit) |
| 38 | Checked lifecycle completion submit (reserved) |
| 39 | Checked lifecycle completion receipt-only lookup (reserved) |
| 40 | Consumer namespace registration submit (reserved) |
| 41 | Consumer namespace registration receipt-only lookup (reserved) |
| 42 | Consumer namespace registration signing plan (reserved private authoring; no commit) |
| 43 | Consumer namespace registration detached signature assembly (reserved private authoring; no commit) |
| 44 | Verified-current-image lifecycle completion signing plan (reserved private authoring; no commit) |
| 45 | Lifecycle completion detached signature assembly (reserved private authoring; no commit) |
| 46 | Fresh event21 agent dispatch with one-use reserve claim (reserved private admission) |
| 47 | Event21 historical receipt-only lookup (reserved; never a delivery permit) |
| 48 | Verified-current-image event21 agent dispatch signing plan (reserved private authoring; no commit) |
| 49 | Event21 agent dispatch detached signature assembly (reserved private authoring; no commit) |
| 50 | Current-image resident lifecycle BEGIN signing plan (private authoring) |
| 51 | Resident lifecycle BEGIN detached signature assembly (private authoring) |
| 52 | Current-image lifecycle claim signing plan (private authoring) |
| 53 | Lifecycle claim detached signature assembly (private authoring) |
| 54 | Grain-backed application share-issue submit (reserved) |
| 55 | Grain-backed share-issue historical receipt-only lookup (reserved) |
| 56 | Current-image grain-backed share-issue signing plan (reserved private authoring) |
| 57 | Grain-backed share-issue detached signature assembly (reserved private authoring) |
| 58 | Current-image event21 full-context purse reserve signing plan (reserved private authoring) |
| 59 | Event21 full-context purse reserve detached signature assembly (reserved private authoring) |
| 60 | Event17 selected fn coverage submit (reserved operator-private admission) |
| 61 | Event17 historical coverage receipt-only lookup (reserved operator-private) |
| 62 | Event19 ordered empty fn progress submit (reserved operator-private admission) |
| 63 | Event19 historical progress receipt-only lookup (reserved operator-private) |
| 64 | Verified-current-image fn progress signing plan, selected or empty variant (reserved operator-private authoring) |
| 65 | Fn progress detached gateway-signature assembly (reserved operator-private authoring) |

Operations60–65 are reserved for the fn integration continuation. They are not
implemented or native-qualified by this allocation. The selected variant must
bind both the originally admitted event13 release and its event17 coverage;
the empty variant uses event19 and the same verifier-derived frontier. ACK
requires the accepted progress receipt and exact retained local poll evidence,
with a fresh pinned-consumer check. Neither a historical lookup nor a transport
cursor permits installation or physical delivery. Existing adjacent-only CLI
behavior must not be relaxed before the coverage receiving path is connected.

Operations58/59 author an ordinary signed reserve bound to the full event21
context and a preallocated reserve operation ID. They do not submit it or
authorize delivery. Operations48/49 subsequently author the paid dispatch using
the admitted reserve; these two stages must not share a digest-only legacy nonce.

Event22 and operations54–57 are additive. Existing event15 and operations28/29
retain their original meaning. Dispatch may consume a grain-backed ticket only
after Replay has admitted that exact variant against its original prefix and
produced corresponding historical issuance evidence. Reusing an event15 tag or
loosening the factory's grain-backed-only rule is not this migration.

The fresh event21 response must have its own strict committed-permit frame and
source inspector. Agent callers cannot substitute the human event11 operations
34/36/37 or convert an operation47 historical receipt into physical delivery.

Selected fn coverage must bind the configured local consumer scope, prior ACK,
bounded first-match scan, exact projected article and an originally admitted
selected-release transaction. A transport cursor alone is not authority to
advance Mini progress or install content. Coverage says what the pinned local
consumer observed; it does not prove that a remote provider delivered every
article. The precise signed carrier and native route remain under construction.

Replay must decode the original ingress, admit it against its original verified
prefix, and compare the entire derived intent, including writes, read guards,
charges, event and nullifiers. A recognized tag or an equal journal event alone
does not establish admission. A lifecycle receipt records pending work; physical
launch additionally requires a current claim and generation check.
