# Bounded authority for open WebSockets

A Mini-admitted WebSocket open no longer permits an indefinitely live stream.
The resident gives it a physical authority lease, default **60 seconds**. The
clock starts immediately before `author_and_submit`, not after Mini returns,
not at HTTP 101, and not on the first frame. Admission latency consumes the
lease. Only a fresh source-checked continuity response may extend it; frame
traffic never does. See `STREAM-CONTINUITY.md` for the receiving protocol.
An expired late result cannot reach `openWebSocket` or emit a 101;
expiry while app setup or handshake output is pending cancels that wait.

The operator can set a positive `wsAuthorityLeaseSeconds` in the private
`mini-spk-grain-host-v2` profile. `grain start` copies an explicit setting to
its derived resident configuration; omission retains the 60-second default.
An existing resident's value is fixed for that generation. Zero and values
outside the platform clock's representable duration are refused. Larger values
increase the maximum silent-revocation exposure by the same amount. Sixty
seconds accommodates the measured ~15-second admission on the older qualified
kernel while bounding silent stale access to a minute; it is an intermediate
operating choice, not the desired permanent editing experience.

## Exact contract

- Every fresh open still passes current Mini admission. Frame traffic and
  lease expiry write no Mini records, create no additional billing events,
  and cannot renew the lease. Separate checked continuity is read-only.
- A later successfully admitted request whose session projection changes
  invalidates existing streams for the same app, process generation, session,
  subject and session kind. Projection equality uses the existing checked
  fingerprint plus physical WebSession parameters, not caller authorization
  claims. Workflow-only session changes retain the source fingerprint.
- A failed current admission at a pinned human entrance immediately signals
  all streams of that entrance's exact app/session/subject to end. Unavailable
  authority is treated conservatively in the same way. Another subject's
  streams are not cancelled. This is a local notification, not a global Store
  subscription; a revocation performed elsewhere may produce no notification.
- Without a notification, the last checked lease deadline still bounds access.
  Each successful renewal anchors its replacement deadline before its source
  check starts; the old deadline applies until that reply is received. An
  authority change therefore leaves at most the configured lifetime of stale
  access. A subsequent renewal must pass current authority again. New opens
  after revocation must pass Mini's independent current-authority check.
- Both pumps check validity immediately before handing a new byte chunk to
  the app or client. A biased watch/timer branch also cancels blocked I/O at
  expiry or invalidation. The pumps are watch/timer driven; only the separate
  bounded renewal schedule calls Mini, never individual frames.
  As with all process timers, actual close notification can be delayed by
  scheduling or suspension; resumed pumps check the monotonic deadline before
  another handoff. Bytes already handed to Cap'n Proto or the OS can finish
  later. App effects already requested are not undone. This is neither an
  instantaneous atomic revocation barrier nor a transaction around each frame.
- Closure drops the app stream, both Unix halves, and the generation socket
  slot. The TLS proxy observes EOF. It does not manufacture an RFC6455 close
  frame. Regrant cannot revive the old lease: reconnect requires another
  admitted open. A new app generation has a new driver and no inherited streams.

The stream registry keeps weak references only to live leases, bounded by
existing generation concurrency caps. The fd3 worker's 101 output is now
asynchronous and bounded, so a stalled handshake cannot block other sockets'
expiry timers on its shared LocalSet.

## Evidence and remaining qualification

`cargo test --lib rpc_adapter::tests` includes an actual Unix/Cap'n Proto byte
pump with two distinct delegate bindings. Both send before invalidation; A's
queued ingress and app egress stop after exact A invalidation; B continues in
both directions and then expires without notification. Removing the pump's
lease guards/timer causes this test to fail. Additional tests cover projection
change, unrelated subject isolation, regrant, an already-expired late upgrade,
a backpressured handshake, and configured lifetime/default/zero refusal.

This receiving-boundary fixture does not impersonate a two-delegate Mini
journey: real owner revoke, new-open refusal, distinct-member EtherCalc editing
and generation STOP still need the combined kernel/resident candidate. The
existing old-kernel TLS fixture was left running unchanged for browser use.

## Continuous authorization renewal

The fixed-only lease was the first enforcement step. Source-owned read-only
renewal is now implemented in `ApplicationStreamContinuity` and the physical
resident, preserving the same fail-closed fallback. It uses fresh signed
current admission and verified share history; unsigned op36 planning remains
insufficient. `STREAM-CONTINUITY.md` records the protocol, lifecycle, proof
boundary and remaining common-candidate qualification. Lease/frame tests alone
do not establish successful real-Mini renewal or editing capacity.
