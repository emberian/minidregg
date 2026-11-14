## Small extension to the existing contract

Could the documentation-side ChatBackend suite in #19 gain a companion room-log contract? Reuse its signed rows, AnchorRef, canonical encoding and known-red controls. Do not replace its signing/anchoring interface or put backend metadata into signed rows. This request supplies a candidate wrapper schema and deterministic vectors, not a new storage implementation or a claim that the proposed methods already exist.

The concrete need is an append-only room log with resumable bounded reads, a seven-day hot RAM window backed by a durable journal, history reads from that journal, and subscription wakes containing the new rows inline. A wake that only says "something changed" still requires another lookup and read. Hash-chain replay should detect missing, reordered or changed entries without treating an external anchor as a prerequisite for local signing.

## What is already present

At PR #19 head 90b4cd7d9449adb019f92b6eabc07d706c4f9507:
- docs/fleet-interfaces/chat_backend.py:3-16 defines sign, anchor, verify, status and refresh, plus three deliberately broken controls. Lines 125-189 check local signing, retry identity, unanchored validity, monotonic anchors, unchanged row bytes and visible outage backlog. It does not define room history or subscriptions.
- docs/fleet-interfaces/README.md:79-94 describes LandRecord append/get/by_sha; :156-168 describes read-set-bound VerdictStore records. These are useful existing seams, not additional endpoints requested here.

At main c492c4dd3da8409ac13b5ff97a9a46bbb2d4cc5b, native/resource-client/src/chat.rs already has sequence-window reads (:125, :1226), per-stream discovery cursors (:1086-1096, :1930), the documented merge order (height, author, cell, sequence) (:882), and append proposals (:1534). Follow sleeps for a three-second interval (:123, :2001). Please extend or expose those mechanisms rather than adding a competing log. This file alone does not establish the server's journal durability or all available subscription APIs.

## Four client seams

This sanitized integration map states generic client requirements, not implemented adapters. Public anchors refer to the #19 head above; unverified endpoints are explicitly absent from the inspected contract.

| Seam | Verified public #19 surface | Client contract / requested extension |
| --- | --- | --- |
| Room log / ChatBackend | docs/fleet-interfaces/chat_backend.py:3-16,125-189: signing, anchoring and invariants; no room-history/subscription contract. | Preserve local signing and unchanged signed rows; request bounded cursor/history reads, durable-ack semantics and inline subscription pages. |
| Task ledger | No task-ledger endpoint verified in the inspected #19 contract. | Request canonical snapshots and bounded incremental reads, explicit unknown/gap states, current authorization and short read/admission critical sections. |
| LandRecord / VerdictStore | docs/fleet-interfaces/README.md:79-94: LandRecord append/get/by_sha; :156-168: immutable subject/read-set-bound verdict records. | Reuse those record kinds; room-log ordering does not itself establish verdict freshness or finality. |
| Append-only events | No event-log endpoint verified in the inspected #19 contract. | Request bounded cursor reads and named gaps. Independent append requests retain distinct event identities even for equal payloads; room retry-key deduplication must not collapse them. |

## Why this matters to one client runtime

Relay-supplied observations, not newly reproduced upstream benchmarks:
- 10-35 MB/s of reads reported while at rest; 401 MB of RAM room data and 106 MB pinned. The reporting convention for MB, overlap between those memory figures, workload shape and measurement instruments were not supplied. These motivate a bounded hot window; they are not measurements of Mini.
- A separate task-read stall reached about 3.5 seconds when a roughly 14,000-step identity read held the shared store/writer mutex and ran a budget callback at every VM step. Candidate accounting changes remain under comparison: batched callbacks can miss many short statements, while exact callbacks exceeded a two-second convoy target in another reported load window (about five seconds). No final cure or global performance verdict is claimed. The requirement is cheap transaction-wide accounting that remains bounded across many short statements, plus short read/admission critical sections without stale authorization. This is a client-side lesson, not an allegation about Mini's implementation.

### Proposed native SQL VM-step accounting

One relay-supplied diagnostic window compared budget accounting over 10,000 `SELECT 1` statements with a 20,000-step limit. Batched callbacks missed that limit; exact counting refused at statement 4,000. In the paired show/comment workload at 197 keys and 630 grants, batched callbacks took 1.590/1.412 seconds versus exact counting at 2.077/2.740 seconds. These are one diagnostic window, not universal benchmarks; the full harness, callback interval, cache/load conditions and counter method are not attached.

Please expose native SQL VM-step accounting suitable for cheap transaction-wide admission budgets. The preferred proposal is bounded statement-boundary chunk charging plus batched callbacks, prioritizing the two-second latency bar over exact per-step counting. Acceptance must state and test an explicit overshoot bound, including many short statements, a single long statement and refusal/rollback behavior; chunk charging must not reset the transaction budget or weaken authorization. This is a feature request, not an implemented or qualified cure. The measurements above compare batching and exact counting only, not the proposed hybrid.

## Minimal contract questions and vectors

The attached schema names illustrative result shapes, not existing API methods. Each vector follows #19's {name, why, input, expect} style.

1. Ordering and resume. What durable ordering frontier makes a cursor safe when streams become visible late? Preserve the current merge rule or explicitly define a compatible admission frontier. A resumed page must not silently skip late rows, duplicate already consumed rows as new events, or restart parsing at byte zero. Display numbers and current file byte offsets are not stable identities.
2. Compaction and retention. A cursor should survive moving rows from the hot window to the journal. If journal history is unavailable or deleted by an explicit retention policy, return a named gap with the last usable checkpoint; never return an empty successful page. Specify the clock and hot-window boundary, journal retention policy, page row/byte limits and behavior when one row exceeds a page budget. A seven-day hot window does not promise seven days of unlimited RAM: byte and pin budgets also need bounds.
3. Subscribe/read race and slow consumers. Define the subscribe frontier so an append during registration is delivered inline or recovered by the next cursor read, without a lost interval. Replayed notifications may be deduplicated by stable entry identity. Bound each subscriber's queued rows and bytes. On overflow, a bounded disconnect/gap plus journal resume is preferable to an unbounded queue or silent loss. Inline rows remain subject to room authorization; subscription must not grant broader access.
4. Replay and durability. A chain wrapper must preserve the original signed row unchanged and bind room, logical position, previous link and row bytes. State the durable-ack point and how restart recovery treats a torn journal tail. A missing link or changed predecessor must fail verification. A valid hash chain alone is not proof of completeness without a trusted checkpoint, signature or anchor; cross-room cursors must refuse rather than disclose rows.

The candidate vectors cover these decisions, exact retry versus conflicting retry, cold history, row/byte limits and synthetic chain tampering. Their wrapper hashes are executable fixture checks; no real adapter, signature implementation, server subscription or crash recovery has been exercised. The existing ChatBackend signature/anchor suite should continue to run unchanged, and each new invariant should have a deliberately broken control before an adapter can be called conformant.

## Suggested scope

One companion schema/vector suite beside docs/fleet-interfaces/chat_backend.py, with a short mapping to existing sequence reads and admission receipts. Keep physical storage, pipe/socket choice and proof scheduling out of this request. Also document whether task-ledger reads and append-only event consumers can use the same bounded reader seam without sharing a long-held writer mutex. No new task schema or event API is claimed to exist in #19.

Missing evidence: sanitized standalone workload and raw counter method for the reported pains; backend-specific append/read latency and work counters; durable-ack/fsync behavior; subscription permission revocation and overflow policy; checkpoint/compaction translation. Those are explicit questions, not implemented guarantees.
