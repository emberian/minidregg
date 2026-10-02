# Separately stoppable public ingress

`mini serve-public-proxy --socket /NODE/public/mini.sock --upstream /NODE/operator/mini.sock --config /NODE/deployment/config.json`

The owner-private `mini serve-operator --host HOST --config CONFIG --socket
/NODE/operator/mini.sock` owns the sole Host process. Its peer-UID check still
requires the service owner; it accepts the union of the existing central public
and operator operation filters. Public ingress has no Host child and accepts
only `transport::public_envelope`, forwarding exact envelope bytes (including
config and Host-image pins) to the private socket. It introduces no admission,
request retry, deployment selection or independent opcode table. New continuity
or receipt operations must be added in the central public filter, while private
operations such as SPK stream renewal remain excluded there.

Both socket directories must be service-owned mode 0700, and both sockets mode
0600. Upstream must already have owner-private `mini.mode` equal to `operator-v1`
and `mini.config` byte-identical to CONFIG. Each request rechecks those pins and
the upstream peer UID. Public pins retain the existing `public-v1`/exact config
format. A previously stopped monolithic public service can therefore be replaced
by this relay using the same path; an `operator-v1` path cannot silently become
public. The public service lock prevents two owners. Stale owned sockets are
recovered using the existing transport check, and graceful exit removes only
the inode this process bound.

## Service and readiness interface

Run the command directly as the service owner in a dedicated Type=simple unit,
with KillMode=control-group and ordinary SIGTERM stop. There are no child
processes. The current process writes
`mini: serving public proxy PUBLIC -> PRIVATE` to stderr only after validating
pins, verifying a live same-UID upstream peer, taking its service lock and binding
the protected listener. This log line is a startup observation; readiness still
requires a successful current signed read. A leftover socket or older log line is
not readiness.

Stopping ingress closes its listener and all accepted/upstream connections;
workers are cancelled and joined before exit. An already executing SSH
`socket-proxy` cannot bypass the stopped relay: each exchange still connects to
the public socket. Its next exchange fails and ends that stdio session. The
private listener remains available for operator lifecycle work. Restart ingress
explicitly only after the intended private service/config is ready.

Ingress stop does **not** cancel a turn already delivered to the Host. Such a
turn may finish without its client receiving a reply. Quiescence must separately
close other writers and establish the private Host's final head; exact retry
handles uncertain client results. The relay never emits a synthetic definite
refusal after its upstream write begins, never resends that request, and never
kills the private Host.

## Bounds

There are at most 64 accepted workers, one bounded frame per request/reply, and
no detached tasks or unbounded request queue. Frame limits use the existing
transport codec (Host payload 12,102,760 bytes, plus bounded envelope fields).
Whole-envelope reads, upstream connection attempts and whole-frame writes each
have a 10-second deadline; upstream responses have the existing 600-second
allowance. A saturated Unix listen backlog is bounded too. Nonblocking I/O polls
cancellation at most every 100 milliseconds. Excess clients receive a bounded
busy refusal and close. Completed workers are reaped during normal operation.

## Receiving checks

On persvati, with a separate Cargo target and `nice -n 10 cargo ... -j2`:

- `cargo test -j2 proxy:: -- --test-threads=1` covers the original stdio relay
  and new real-Unix-socket relay checks: exact forwarding, pre-forward refusal,
  upstream pin changes, frame deadlines, connection ceilings, saturated backlog,
  stalled responses, large replies to a nonreading client, and prompt stop.
- `cargo test -j2 transport:: -- --test-threads=1` checks the shared framing,
  public/operator filters, server ownership and existing bounded Host transport.
- `python3 public-ingress-process.py /absolute/path/to/mini` runs actual Mini
  CLI processes and 20 receiving assertions. It verifies public/private routes,
  pin refusal before the Host, SIGTERM while idle/in flight, an existing stdio
  client's failed reconnect, surviving private operator access, explicit restart,
  duplicate-owner refusal and refusal to reuse an operator path as public.

The process check's Host is a framed echo fixture, explicitly not evidence of
Lean admission or a deployed service. Joined native journeys and infrastructure
quiescence/resume qualification are separate consumers of this interface. The
script leaves its isolated evidence directory and cleans up only the process
groups it started.

## Private admission close and drain

Before stopping any managed service, capability-check the live private endpoint:

```
mini operator-status --socket /NODE/operator/mini.sock --host HOST --config CONFIG
```

Compare its `processId` with the service manager's live MainPID (and executable
pin); retain `instanceId`, `configSha256` and `hostSha256`. After closing public
ingress and quiescing managed apps, agents, schedulers and other writers, request:

```
mini drain-operator --socket /NODE/operator/mini.sock --host HOST --config CONFIG \
  --instance INSTANCE --pid PID --timeout-seconds 600
```

This uses a separate owner-private Unix control socket, `mini.control`, beside
the private `mini.sock`. Both directions check same UID; the request pins the
random process instance, process PID and exact configuration/Host hashes. A
fresh request nonce binds each response. This is a local process lifecycle
protocol, not a Host opcode and not available through public ingress. It adds
no Mini authorization or semantics. Neither command accepts a remote address.

Drain closes the **actual private listener** first. Every already accepted
worker retains its normal frame deadline and may complete its one request.
The Host processes queued work normally; a client disconnect does not cancel
its worker's wait for the Host answer. After a worker has attempted its bounded
reply delivery, it drops its queue sender. Only after the queue receiver ends
(all accepted workers and the accept loop have dropped their senders), and the
accept thread has joined, does the service report `drained: true`. A zero live
connection snapshot or an intervening signed read is insufficient.

The Host remains alive and owned by this process, while private admission stays
closed. Control status/drain remain available, so the same instance can be
queried and drained idempotently. There is intentionally no reopen command;
explicit service restart creates a fresh instance and reopens admission. An
old instance's drain request cannot affect the replacement. Service stop should
use KillMode=control-group, as with the existing private Host wrapper.

Successful drain stdout is one JSON object:

```
{
  "format": "mini-operator-drain-v1",
  "processId": 123,
  "instanceId": "64 lowercase hex digits",
  "configSha256": "64 lowercase hex digits",
  "hostSha256": "64 lowercase hex digits",
  "requestNonce": "64 lowercase hex digits",
  "hostProcessId": 124,
  "phase": "drained",
  "admissionClosed": true,
  "drained": true,
  "unresolvedConnections": 0,
  "acceptedConnections": 0,
  "queuedRequests": 0,
  "activeRequests": 0
}
```

`phase` is `serving`, `closing`, `draining` or `drained`. `unresolvedConnections`
counts live accepted work connections. The final three counts are null before
the channel-disconnection proof, and exactly zero afterward; they do not count
control connections. A timeout (1–3600 seconds) emits the latest observed JSON
and exits nonzero. Admission remains closed, and retry uses the same instance.
A lost control reply is uncertain about whether closing began; query that same
live instance instead of restarting or selecting a new one automatically.

The drain receipt certifies physical quiescence of this private service. It is
not an admission receipt, a statement that clients received their replies, or a
replacement for exact recovery and final Store audit. Only after this receipt
and closure of every other writer may orchestration stop the private unit and
run its cold checkpoint/upgrade checks.

The process receiving check now includes timeout with a stalled Host, an
already accepted idle reader, queued work, disconnected clients, exact-instance
retry, unchanged live Host PID, explicit restart and refusal of stale instance
requests (32 assertions total). Unit checks additionally reject changed
PID/instance/profile pins and unknown control fields before closing admission,
and distinguish an empty connection snapshot from a drained queue.
