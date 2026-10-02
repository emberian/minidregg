# Resident request custody

The production driver is `grain-runtime hermes-room resident CONFIG` against a
provisioned controller and the same participant Store/workspace as its room.
Its `inbox` is the accepted assignment directory returned by the registered
handoff dispatcher. `toolTask.room.account` must equal that assignment's account
alias, including its generation. A replacement must be provisioned with matching
inbox and account coordinates before any new provider work.

Omitted or null `maxPrompts` runs continuously. An explicit value1..1000 limits
qualified completed turns for a bounded assignment or fixture; restarting does
not reset the count. There is no fixture-sized lifetime limit by default.
`intervalSeconds` defaults30, within5..3600.

Admission limits are configurable per controller: `maxPendingRequests` defaults64
(range1..1024), `maxRequestsPerAuthor` defaults8 (range1..pending limit), and
`discoveryPageSize` defaults64 (range1..256 source entries per member stream per
poll). Custody also has a16MiB serialized byte bound, with512KiB reserved for cursor and prompt metadata; oversized requests receive a typed byte-admission refusal. These are resource controls, not a platform population claim. Each author
has FIFO requests, with round robin selection across eligible authors. Overflow
has an immutable `request-ID-refused.json` outcome and structured driver output;
it does not displace an admitted request. The member can post a new request after
capacity becomes available. Refusals are currently inspectable in controller
custody/output rather than automatically published into the room.

Before discovery, the client revalidates the accepted signed handoff, current
room assignment, recipient/task, room cell, world and delegated references.
Requests begin after the actual accepted assignment height. Dismissal has its
own exact signed accepted-origin check and refunds through native account
admission. Display aliases do not identify assignment custody.

`requests.json` is a bounded local cache of signed source identities, pending
requests, per-stream sequence cursors and the last served author. It grants no
authority. `tail --discover CURSOR_FILE` makes bounded native signed reads from
each current member stream's last sequence plus one; newly visible streams start
from their own sequence1. It separately rereads retained pending cell/sequence
refs. Discovery progress commits after request admission/refusal records, so a
crash cannot skip an unrecorded request. Global height is never a paging cursor;
same-height entries and interleaved streams therefore cannot skip one another.
Unreadable streams retain their cursors while other eligible authors advance.
There is no total room-history admission ceiling.

A request whose escaped prompt plus program exceeds the framed control byte bound receives a retained refusal before provider dispatch, allowing the next author to advance.

Selection is fsynced before the unique resident prompt enters the existing framed
controller. Exactly one addressed entry enters its prompt and final routing.
Current membership is revalidated before generation; revoked queued work receives
a retained cancellation. Replaced assignments cannot reuse started requests.
The existing pending prompt and source origin retain uncertain execution without
another model call. This blocks only that resident/controller.

The queue completes only from the source completion plus native final-delivery
receipt with the exact author and stable stream-cell/sequence reply proof. A lost
driver completion frame is recovered by the existing no-model source receiver.
Exact final retries preserve operation IDs, charges and native receipts. An exact allocated native final operation that is proven refused receives a distinct `mini-resident-final-refused-v1` receipt, clears its pending marker and lets the next author advance; uncertain operations retain the marker. The refused receipt preserves any already paid model/tool/account charges and does not claim a delivered answer. The
source-only `tail --entry CELL:SEQUENCE` reads that exact native stream window,
updates the observed reply cache, and does not depend on the entry remaining in a
recent tail or on replaying the entire room's history. The ordinal in the observed
feed is transient; the native stable reply guard remains mandatory.

When no addressed request is waiting, the summoned program can still perform
maintenance on changed role/document inputs. Such work has no invented addressed
recipient. A separate maintenance revision is committed from the matching source completion, including addressed turns, so an unchanged empty queue does not buy a second model turn solely because the last turn addressed a request. Native tools continue to enforce grants, budgets and exact effects.
