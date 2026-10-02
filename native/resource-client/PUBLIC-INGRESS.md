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
