# Hyperdocument performance and replacement evidence plan

Status: benchmark contract; no performance result is claimed here.

This plan turns the source-grounded Hyperdreggmedia audit into measurable replacement gates. The
semantic rules remain Lean-owned. Native implementations receive bounded, generated work profiles
and return candidate buffers or errors; a fast Rust result is not an accepted semantic event.

## Baseline pathologies to retire

The Breadstuffs audit found several costs that grow with the whole document or whole history:

- classic full-matrix LCS for an edit: `O(old_bytes * new_bytes)` time and memory;
- full history replay before editing and whole-history serialization/reseal after editing;
- sequential heap addresses whose early insertion shifts later authenticated leaves;
- mark rendering that scans every mark for every visible atom;
- conflict discovery with pairwise successor reachability and repeated graph traversals;
- repeated linear patch-id lookup and history rescans for dependency queries; and
- decoders which allocate from untrusted counts without a declared quota.

The full source ledger is
`/Users/ember/dev/HYPERDREGGMEDIA_MINIDREGG_SUBSUMPTION_AUDIT_2026-08-09.md`.

## Intended asymptotic shape

These are architecture targets to validate, not benchmark results:

| Operation | Semantic/native shape | Cost that must be measured |
|---|---|---|
| Local content edit | stable run/range edit plus `k` typed sparse writes | `O(k log N)` authenticated-map work, plus bounded local diff |
| Mark/annotation query | range index keyed by stable run/endpoints | output-sensitive `O(log M + matches)` |
| Forward link | one canonical link event and target-keyed index write | `O(log L)` state/index work |
| Backlink query | authenticated target bucket over a stated completeness epoch | `O(log L + matches)` plus opening/proof work |
| Version append | one causal-DAG event plus frontier update | proportional to parent count, event bytes, and touched roots |
| Checkpoint | canonical state snapshot plus exact prefix/suffix equivalence | amortized over a declared event interval |
| Merge/settlement | changed regions and explicit conflict alternatives only | proportional to compared frontier/delta, not full history |
| Render refresh | observer dependency intersection with exact receipt footprint | proportional to dirty views and changed data |

No implementation may obtain these shapes by weakening conflict preservation, provenance,
authorization, backlink completeness, or canonical-root binding.

## Workload families

Every implementation candidate must run the same deterministic, generated workload descriptions:

1. **Long prose:** 1 KiB through 256 MiB, local inserts/deletes at beginning, middle, and end.
2. **Structured document:** shallow and deeply nested elements, fields, embeds, and sparse metadata.
3. **Annotation density:** 0.1%, 1%, 10%, and 100% of visible runs covered, including overlapping
   and endpoint-death cases.
4. **Link graph:** uniform, hub-heavy, and adversarial target distributions; snapshot and live
   transclusions; backlink pagination under a fixed completeness epoch.
5. **Causal history:** linear, wide concurrent, long-lived fork, missing-parent arrival, duplicate
   event, checkpoint plus suffix, and rollback/replay attempts.
6. **Conflict stress:** many alternatives, nested conflicts, ambiguous rejoins, and resolution
   which retains the exact rejected alternatives in history.
7. **Reactive surface:** many observers with sparse and dense dependency sets, measuring clean cache
   reuse and exact dirty reprojection.
8. **Agent authoring:** one gesture touching content, program/view source, links, authority, and
   indexes through a flat typed hyperedge.

## Measurements

Record at least:

- canonical event bytes and touched-key count;
- logical validation time and peak memory;
- native candidate-kernel time and peak memory, separately;
- authenticated-state update/hash work and proof-witness bytes;
- proof generation, verification, proof size, and security parameters;
- history append and checkpoint costs;
- renderer/index invalidation count and refreshed bytes;
- rejected/blocked operation cost and confirmation that no logical post was exposed; and
- cold, warm, and checkpoint-reopen behavior.

Report median, p95, p99, worst observed, input distributions, host/toolchain/commit hashes, and exact
generated profile identifiers. Throughput without memory and tail latency is insufficient.

## Correctness oracle

For every measured candidate execution:

1. Lean owns the canonical workload/event/profile bytes.
2. Native code receives only the declared bounded task and returns bytes or an error.
3. Lean decodes and checks the result before constructing accepted evidence.
4. A reference Lean interpreter checks exact post-state, footprint, conflict alternatives, ranges,
   link events, and history entry for the exercised input.
5. Reopen/checkpoint tests reconstruct the same canonical state and history frontier.

Exercised-input agreement is regression evidence only. It is not a Rust semantics or refinement
theorem.

## Remote evidence

Use `scripts/remote-check.sh` on explicit committed snapshots. hbox and persvati are independent CPU
workers; neither currently has an admitted GPU compute environment. A performance record must retain
the exact source archive, dependency revisions, command argv, environment, raw output, source
integrity, generated-output allowlist, and result hashes. No result is copied back automatically.

## First implementation sequence

1. Benchmark canonical sparse writes and root updates for content, range, annotation, and link
   namespaces.
2. Add checkpoint/suffix replay and compare cold replay against checkpoint reopen.
3. Add range and backlink indexes with exact output/completeness checks.
4. Measure conflict-preserving merge and Grain settlement on changed regions.
5. Attach the actual lookup/history proof controller and measure witness/proof costs separately from
   semantic execution.
6. Only then optimize native hot paths (SIMD/GPU/parallel hashing) behind the same generated plans.

## Replacement gates

- No keystroke requires whole-history replay or serialization.
- Sparse local edits do not rewrite addresses for unrelated semantic keys.
- Every decoder and traversal has declared byte/item/depth/work limits.
- Conflicts and annotations are never dropped to improve a benchmark.
- Backlink results identify whether they are complete for an authenticated epoch or best effort.
- Checkpoint reopen is definitionally tied to the same semantic state/frontier, not only equal host
  bytes.
- Production workload evidence includes the proof/history path, not just the native data structure.

