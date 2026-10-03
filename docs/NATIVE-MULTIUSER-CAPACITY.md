# Native multiuser capacity

The participant browser and remote proxy use the existing persistent native
Host. Lean still owns signed observations, current authority, canonical plans,
admission, and exact historical lookup. These physical bounds do not introduce
an alternate resource state or authorize an operation.

## Browser ingress

Each browser process admits at most 16 connections, including header/body
readers, active native views or form operations, and response writers. A new
connection at capacity receives the same `503`/`Retry-After: 1` response before
request dispatch. This public overload result depends on physical connection
occupancy; it is not a traffic-private scheduler or a member entitlement.

Each accepted header and complete form body share a ten-second deadline from
acceptance. Sending a byte periodically cannot renew it. Response writes have
a ten-second socket timeout. The native Host exchange retains its existing
bounded queue and 600-second response bound. The browser connection permit
covers that wait. Sixteen stalled native views therefore saturate this one
browser process; they cannot create an unbounded worker or page queue.

Idle readers cannot hold the browser accept loop. Independent signed views,
history and inspection can progress concurrently. POST operations and GETs
that open document/Studio drafts serialize owner-private custody after complete
ingress. Their exact retained intent, call, response and recovery rules are
unchanged. The Host still serializes the world's actual exchanges and decides
stale observations under current law. Concurrent page views are individually
authorized reads, not a common atomic snapshot.

Host decisions, line refusals and command endings are caller-thread scratch.
One read cannot consume another caller's refusal and thereby change its
recovery classification. The selected Host image cache remains keyed by the
opened file's actual identity; config and image envelopes retain their pins.

## Remote session isolation

The process retains at most 32 remote `(destination, SSH credential)` slots.
The registry lock covers slot discovery only. Each slot serializes its own
framed requests and owns one persistent SSH process, so a blocked world does
not hold unrelated destinations or credentials. The existing endpoint still
applies its frame bounds, operation filtering, exact config/image pins, and
native authority checks. A slot is a physical connection, not a signing identity.

A failed exchange closes only that session and reports the original uncertain
result. It never sends the failed frame again. The next explicitly requested
operation may open a replacement connection; an uncertain effect still requires
the existing retained-call lookup/recovery path. At the destination limit,
new slots refuse before launch/transmission; existing slots remain usable.

## Qualification boundary

Source and scoped Rust tests establish ingress/resource isolation and preserve
the exact-call recovery receiving paths. Full native member journeys and
history-growth latency require separate measurements with a matched Host,
client and Store. Queue capacity does not imply a latency or member-fairness
guarantee, and this change does not claim the 1000-record five-second write or
sixty-second cold-reopen target.
