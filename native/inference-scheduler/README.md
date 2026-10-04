# Shared homelab inference placement

This service allocates physical inference capacity among Mini controllers. Mini's
existing provider purse, signed reserve, current authority checks, tariff and
exact response journal remain the authorization and accounting path. The broker
has no API keys and no credit ledger. It receives request digests and bounds,
not prompt text.

`grain-runtime` can opt a homelab provider task into this service. A gateway asks
its controller to prepare placement, waits outside the controller loop, then
uses the normal reserve and before-send path. Historical exact response replay
does not queue or allocate new capacity. The controller checks the selected
endpoint against named homelab rows in its existing root-owned provider table;
the worker cannot supply a destination.

## Configuration

Build on the designated Mini build host:

```sh
cargo build --release -j2 --manifest-path native/inference-scheduler/Cargo.toml
mini-inference-scheduler /etc/mini/inference.json /var/lib/mini/inference /var/lib/mini/inference/control.sock
```

Create the socket's parent directory with mode 0700, owned by the service uid.
The configuration must be a root-owned regular file, not group/other writable.
The state directory is private and locked to one broker process. Controllers
and broker initially share a trusted service uid; socket permissions and Linux
peer credentials reject unregistered users. Controller registration is an
operator pin, not a claim made by a model. This is not a remote public API.

Example inventory (replace uid, domain/principal and endpoints with the actual
deployment; this file is not an assertion of Pug's hardware):

```json
{
  "version": 1,
  "max_jobs": 10000,
  "max_terminal_receipts": 1000000,
  "max_receipt_bytes": 8589934592,
  "max_queued_per_principal": 16,
  "max_active_per_principal": 2,
  "lease_ms": 60000,
  "groups": { "gpu-a": 1, "gpu-b": 2 },
  "controllers": {
    "hermes-alice": { "uid": 991, "principal": "42", "pool": "residents" },
    "hermes-bob": { "uid": 991, "principal": "43", "pool": "residents" }
  },
  "backends": {
    "host-a": {
      "pool": "residents", "group": "gpu-a",
      "endpoint": "http://127.0.0.1:18081/v1/chat/completions",
      "models": { "resident-model": {
        "context": 32768, "max_output": 4096, "tools": true,
        "input_us": 2000, "output_us": 40000
      } }
    },
    "host-b": {
      "pool": "residents", "group": "gpu-b",
      "endpoint": "http://127.0.0.1:18082/v1/chat/completions",
      "models": { "resident-model": {
        "context": 32768, "max_output": 4096, "tools": true,
        "input_us": 1000, "output_us": 20000
      } }
    }
  }
}
```

Two URLs sharing one accelerator must name the same capacity group. Model names
mean operator-declared compatible instances; there is no automatic quality
substitution, model loading, or capacity discovery. Input/output microseconds
are conservative scheduling estimates, not prices. Configure real measurements
before making throughput promises.

The corresponding optional `providerTask.homelab` field is:

```json
{
  "socket": "/var/lib/mini/inference/control.sock",
  "controller": "hermes-alice",
  "domain": "actual-mini-domain-and-genesis-identity",
  "principal": "42",
  "pool": "residents",
  "backends": ["homelab-a", "homelab-b"],
  "queueTimeoutMs": 120000
}
```

`backends` are names in the existing provider table. Each selected row must have
`credential: "homelab"`, list the exact task model, and match the broker-selected
endpoint exactly. `principal` must match the provider task's pinned `onBehalfOf`
subject, or its subject when no on-behalf-of pin exists. Give all agents for one
member that same principal. The queue deadline cannot exceed the task timeout;
reconnecting an exact job retains its first deadline instead of extending it.

## Allocation and recovery

Admission checks model, context including output headroom, tool support, pool,
per-principal queue and active bounds, and shared group capacity. Among eligible
principals it chooses least accumulated virtual service, preserving order among
feasible requests for that principal/model; placement reserves the configured request cost. Completed
work reconciles that estimate against occupied wall time. There is no mid-call
preemption. An independent host can work while another model is unavailable.
Idle members rejoin at a persisted virtual service floor, so historical idle
time does not accumulate an unlimited catch-up preference.
This is an initial equal-weight, request-boundary policy; no stronger latency
or adversarial scheduling theorem is claimed.

Allocation states are durable before replies:

* **Queued:** no slot and no inference token charge. Cancel/expiry is final.
* **Placed:** unsent, expiring slot reservation. A failed Mini reserve releases
  it as not-sent. Broker restart returns it to queue with a fresh lease, making
  the old lease unusable for dispatch. The broker retains an exact unsent
  tombstone for that old lease: an older Mini journal can acknowledge no-send
  without accidentally releasing the replacement lease.
* **Dispatched:** exact broker lease bound to a provider attempt. Mini's durable
  send boundary still precedes gateway I/O. A repeated dispatch request is
  refused; inspecting a state is never new send permission.
* **Uncertain:** possibly running or unconfirmed stop. It keeps the physical
  slot across restart, and cannot be dispatched again. A timeout is not evidence
  that a generic OpenAI-compatible backend stopped.
* **Terminal:** exact lease and physical outcome retained for idempotent
  reconciliation. This does not assert Mini settlement or response delivery.

`ProviderAttempt` retains placement coordinates for the existing source-audited
provider reconciliation path. A retained complete response proves physical
completion; proven no-send can release an unsent attempt. Uncertain execution
requires actual backend/transport evidence before capacity can be released.
The gateway does not retry on another endpoint or route. Losing a response can
leave Mini accounting unresolved even when physical completion freed the slot.

The broker uses atomic file replacement plus file/directory fsync and an
exclusive state lock. A persistence failure poisons the running service; it
must restart and reconcile rather than granting more capacity from uncertain
memory. Configuration changes against retained state are refused until an
explicit drain/migration: changing capacity or identity under running leases
is not an implicit operator reload.

## Operation and supervision

The candidate build ships `bin/mini-inference-scheduler` and records its hash in
`provenance.json` and `SHA256SUMS`. The deployment unit is
[`deploy/hermes/mini-inference.service`](../../deploy/hermes/mini-inference.service).
Dregg infrastructure vendors that same unit and installs its private
`/var/lib/mini/inference` directory through the existing installer. The optional
component enables only when the candidate binary and valid inventory exist.
Install an operator-authored inventory as root-owned mode 0644 at
`/etc/mini/inference.json`, then use the existing `mini-components --apply`.
It contains endpoint/identity metadata, never credentials or prompts.

```sh
B=/var/lib/mini/candidate/current/bin/mini-inference-scheduler
S=/var/lib/mini/inference/control.sock
sudo "$B" check /etc/mini/inference.json
sudo "$B" status "$S"
sudo "$B" drain "$S" 50
sudo "$B" resume "$S"
```

Root or the trusted service uid can operate the owner-private socket. Status
reports global counts and capacity occupancy with paginated active job summaries
(controller, pinned principal and model); it omits request digests, endpoints,
attempts and prompt material. Follow `next_after` with `status SOCKET AFTER_ID`.
Group pagination is described by `next_group_after`; use
`status-groups SOCKET AFTER_GROUP` to continue that independent page. Counts
always cover the entire retained state, even when detail pages are truncated.

Drain is durable before acknowledgment. It refuses fresh jobs, terminalizes
queued and placed-unsent jobs as `Drained`, and retains running/uncertain leases.
Controllers report `homelab-draining` or `homelab-drained-before-send` explicitly;
these are admission/queue refusals before provider I/O. Exact old jobs remain
terminal: after resume, retry with a fresh explicit prompt/request, not an
automatic resend of the old job. Historical completed response replay still
uses Mini's retained response without admission or capacity.

The optional wait reports success only when no placed, running or uncertain
allocation remains. A timeout exits nonzero while retaining drain and physical
occupancy. `uncertain` requires actual transport/backend evidence and controller
reconciliation; resume never erases it. A page with `quiescent: true` describes
physical occupancy, not completion of Mini settlement or response delivery.

When the lease holder of dispatched or uncertain work is gone for good (its
controller died or was retired), only the operator can release the slot:
`sudo "$B" resolve "$S" JOB_ID` attests that the physical execution is over
(the backend was stopped or checked), terminalizes the job as
`operator-resolved`, frees its group slot and charges the elapsed wall time as
service. It refuses queued and placed work (cancel or drain those). A late
report from the old holder is then a no-op. Snapshots carrying
`operator-resolved` do not load in older binaries.

The unit drains on intentional stop/restart, waits up to 50 seconds, then stops.
Restart retains that flag until explicit resume. `mini-components --apply` and
`--check` surface `DRAINED; explicit resume required` and return nonzero instead
of calling this ready. A crash restarts automatically; dispatched work becomes
uncertain and keeps its slots, while previously unsent placements receive fresh
leases. A snapshot written by this version adds drain state; older binaries
which reject unknown fields cannot read it. Keep the compatible binary and
snapshot together when planning rollback. Inventory changes still require a
separate retained-state migration; drain alone does not rewrite its identity pin.

## Checks and remaining deployment work

```sh
cargo test -j2 --manifest-path native/inference-scheduler/Cargo.toml
cargo test -j2 --manifest-path native/grain-runtime/Cargo.toml provider::homelab_tests::
cargo test -j2 --manifest-path native/grain-runtime/Cargo.toml provider::tests::
```

Core/socket checks cover shared aliases, same-member controllers, fair service,
eligibility, independent hosts, exact identities, cancellation, daemon death,
stale lease refusal and uncertain occupancy. Receiving tests connect two actual
gateway instances to the real private broker and local fake HTTP providers;
their controller acknowledgements stand in for Mini signed admission. They are
not a combined native-host or real-model qualification.

Before deployment, exercise the joined controller against the current Mini host,
inventory Pug's machines, measure safe concurrency,
and test backend stop/restart under load. Member-visible queue state, backend health, resident-model changes and live-token
forwarding remain work.

## Terminal retention and archive capacity

`max_jobs` bounds nonterminal work (queued, placed, running and uncertain), not
lifetime completions. The service writes immutable exact terminal receipts into
its private `receipts/` archive before removing full jobs from the hot snapshot.
The complete terminal transition, including fairness refund/elapsed counters,
is first fsynced in the hot snapshot. Receipt file and directory fsync then
precede a second snapshot that retires it. Restart finishes an interrupted
archive/retirement cut with those same counters; it never redispatches completed
work. A newer receipt paired with an unresolved older snapshot is an incomplete
backup and is refused. Addressed retries load only
that exact receipt. Changed content, another controller, another lease and
another completion outcome remain refused; stale unsent lease guards survive.
Running and uncertain records are never archived or evicted.

The archive has independent count and byte limits, defaulting to one million
receipts and 8 GiB. Admission reserves 128 KiB of archive space for each live job
so completion can remain durable even near the configured budget. Status exposes
`terminal_receipts`, `receipt_bytes`, `max_terminal_receipts` and
`max_receipt_bytes`; historical terminal/drained counts include the archive.
Completed jobs therefore keep releasing live capacity, while an exhausted
archive explicitly refuses fresh admission. Exact historical inspection and
reconciliation still work. Operators may increase the archive budgets and
restart: these resource limits do not change the identity/placement fingerprint.
Snapshot and **the whole receipts directory** must be backed up together; loss of
previously recorded archive capacity fails startup rather than forgetting IDs.
No operator command deletes receipts. Destructive retention needs a separate,
explicit generation/retirement contract that can refuse all expired IDs; arbitrary
request digests cannot safely be forgotten merely because a receipt is old.

The bounded hot snapshot and durable archive support a finite declared operating
budget, not an infinite-disk promise. Reopen scans bounded receipt metadata;
normal startup uses saved outcome summaries, rebuilding them after an interrupted
archive/snapshot cut. A configured per-receipt bound is also fail closed: unusually
large stale-lease history requires preservation and reconciliation, never eviction.
The direct core API enforces the same64 KiB request bound as the socket, and each
request retains at most1024 exact unsent restart guards. Reaching that guard
bound terminalizes only that definitely-unsent placement as `NotSent`, preserving
every old guard and the current exact lease. Other principals continue receiving;
the retired request needs a fresh explicit prompt rather than automatic retry.
Running/uncertain work is never terminalized by this bound, and no old lease
becomes newly dispatchable.
