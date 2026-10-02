# Bounded authority for open WebSockets

A Mini-admitted WebSocket open no longer permits an indefinitely live stream.
The resident gives it a physical authority lease, default **60 seconds**. The
clock starts immediately before `author_and_submit`, not after Mini returns,
not at HTTP 101, and not on the first frame. Admission latency consumes the
lease. An expired late result cannot reach `openWebSocket` or emit a 101;
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
  and cannot renew the lease.
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
- Without a notification, the fixed deadline still ends the stream. If an
  authority change occurs after this stream's admission began, the remaining
  stale-access window is at most the configured lifetime. New opens after
  revocation must fail Mini's independent current-authority check.
- Both pumps check validity immediately before handing a new byte chunk to
  the app or client. A biased watch/timer branch also cancels blocked I/O at
  expiry or invalidation. There is no polling and no per-frame Mini call.
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

Periodic forced reconnect is an intermediate fail-closed contract. Mature
editing needs a source-owned, read-only continuity receiver rather than a new
paid dispatch every minute or an unsigned planning response used as authority.
The source seam is `ApplicationDispatchAdmission.checkCurrent`: its private
`CheckedCurrent` already requires the signed invocation, current app/manifest/
enrollment/ticket observations, permissions and issuer lineage.
`NativeHostReplay.admitDispatchVerified` adds selected share-issue provenance
from the verified chronological prefix. The existing receiver then performs
`DurableReceiverIO.receiveLoadedDetailed` and returns a CAS-backed permit;
that mutating half must not be reused silently as free renewal.

A dedicated continuity receiver should validate freshly signed, domain-separated
continuity intent against the warm verified image, check the physical Store tip
before handoff, and return a bounded attestation tied to the resident's fresh
stream nonce, app/generation/session/subject, ticket/enrollment and projection
fingerprint. Its request must start the renewed local deadline, so stale replies
cannot extend access. Replayed replies or permission changes must never renew
an old app-side capability; renewal failure closes the stream. It must preserve
the distinction between checked observation, session workflow and billable app
dispatch, with no app RPC effect and no fake dispatch history. Tip freshness
remains point-in-time; bounded expiry is still needed if later invalidation is
missed. That receiver/API and its source proofs are not implemented here.
