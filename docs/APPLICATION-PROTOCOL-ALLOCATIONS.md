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

Wire frame revisions, content-object type tags, nullifier codec versions, and
event tags are separate namespaces. Changing a wire frame to v2 does not mean
incrementing its event tag into another family's allocation. Each family must
retain its domain-separated canonical bytes and exact decoding checks.

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
