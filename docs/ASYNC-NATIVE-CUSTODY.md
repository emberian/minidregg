# Asynchronous native request custody

`scheduled_transport::AsyncDispatch` separates physical responsibility for an
exact native request from the native source's semantic admission and result.
The resident cohort mailbox uses it; the original blocking CLI remains available.

An offer runs the existing public envelope gate, reserves an immutable class
slot, and persists the original recovery capability and exact request through
the existing fsynced Journal. Only then can it report physical `Accepted`.
Application, control, and repair have separate native workers. Workers publish
a dispatch claim before the original native exchange and retain its exact reply.
Startup resumes unclaimed requests. A claim without a reply never authorizes
another dispatch, including after restart.

`Accepted` is not Mini admission or semantic `Pending`. Only native source bytes
provide that decision. Transport result 0 carries the original native frame,
1 indicates physical uncertainty, 2 indicates transport refusal, and 3 indicates
durable physical custody with a later fetch required.

Fetch requires the immutable original recovery capability, original traffic
class, and SHA256 digest of the exact original envelope. It reads status or the
cached result and never dispatches a native request. An unknown native effect
still requires a separate source-authorized exact native lookup. Fetch cannot
manufacture a missing receipt.

The original traffic class is a reservation class, not a Mini authority category.
The gateway pins its native endpoint, exact deployment config, reply bound and
public capacities. One service lock prevents concurrent owners of a Journal.
Immutable class reservations count against retained capacity even when a crash
precedes request publication. Quota refusal cannot allocate recovery files.
No uncertain obligation is deleted to make room.

The resident PQ helpers reuse the existing manifest, strict input/output stage
sets, epoch/profile binding, native envelope gate, and batch claims. Ordinary
core mode 1 carries the original native envelope. Recovery core mode 2 is a
fetch-only request in the reserved recovery class. Its fixed private payload
binds original class, request digest, and recovery access. Its fresh outer reply
capability must differ from the original access capability.

The first offer's reply capability is its immutable recovery access. Clients
retain that secret and original request after consuming a continuation. A later
fetch uses a fresh per-epoch reply capability. `live_save_cap` and `live_scan`
share the existing service lock, immutable capability records, and spent/opened
drain fences. New records obey the existing 128/64/64 per-class limits; exact
retained retries remain permitted at quota.

The emission loop must run independently of these helpers and native workers.
It must select from ready or precomputed padded buffers without waiting for
native work, disk publication, or per-slot cryptographic preparation. Valid
precomputed cover is distinct from a transport-unavailable marker. Custody code
alone does not establish the emission deadline or a privacy theorem.

## Checks and qualification

The five `async_custody` checks cover held native work with reserved repair
progress, restart fencing and unclaimed resumption, crash-left reservation
capacity, four-hop continuation followed by capability-bound fetch, and client
reply-capacity limits. Joined cohort tests additionally cover authentication,
fixed record shape, durable selection, public profile binding and cover supply.
The original PQ regression checks exercise exact stage sets, substitution and
operator forgery, replay/drain fences, claim/shuffle crash handling, valid cover
under private refusal, and native multihop delivery.

These checks passed on the authored source. Longer native traffic qualification
has exposed sender-side synchronous disk/crypto preparation as a remaining
deadline dependency. The traffic consumer owns that repair. No fixed-schedule
privacy, WCET, source anonymity, deployment, or external settlement claim follows
from this custody implementation.
