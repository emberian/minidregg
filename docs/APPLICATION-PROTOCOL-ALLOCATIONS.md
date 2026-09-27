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

Replay must decode the original ingress, admit it against its original verified
prefix, and compare the entire derived intent, including writes, read guards,
charges, event and nullifiers. A recognized tag or an equal journal event alone
does not establish admission. A lifecycle receipt records pending work; physical
launch additionally requires a current claim and generation check.
