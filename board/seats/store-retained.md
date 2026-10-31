# Seat: store-retained

Agent: a9b54e85e4a194b91 (formerly a13f0c9ab4513b2d7; about 425K tokens at 2026-10-31 night; tell root at ~500K)
Worktrees: /Users/ember/dev/minidregg-lanes/retained (on main via branch l0-land; no side branch);
/Users/ember/dev/minidregg-lanes/store-retained (main, board edits). Box tree: hbox pool t4 (`lane-tree renew retained`),
builds `swarm-build lake build Minidregg` from t4; logs and PID files in /home/hbox/pool/t4-retained/.

Owns: the leaf layer and retained mode. Theory/Retained.lean (maintained answer = recomputation after any admitted
run and across checkpoint/restore; chain rule; generic red-green memo node), Theory/SparseMap.lean (persistent
extensional tree map over injective List Nat key codes: get/set/ext, support with no dedup, filterKeys, map,
ofFinset, toDFinsupp/ofDFinsupp spec views), Theory/DeriveStoreKey.lean (`deriving StoreKey`), Theory/Store.lean's
representation, World's Cells; docs/RETAINED-MODE.md (node inventory, migration order, generation and lint design).

Quest: derived values maintained by delta, never recomputed per request; the widest costs first.

## Landed (main)
- 802ba8c69 **L0**: Store L and World's Cells are SparseMap trees (every lookup and set O(log n)); WorldCompact and
  compactEvery deleted; deriving StoreKey for every layout's keys; StoreCodec builds by set and reads the tree's
  support; the cached-support twins (existsSupport/issuerCheckFast, supportCached, allSupport) collapsed. Whole tree
  green on hbox t4 (10404 jobs).
- 03c8af2c0 RETAINED-MODE continuation; earlier 675a80745 Retained, 62aa5fcf8/05bffae27 SparseMap.

## Numbers
- Before (hot-path's g2, pre-L0): `story new` Host CPU 1.50 s (story 2) → 2.51 s (story 8); DFinsupp.update under
  Store.set 3.9 % → 24 % + 9 % of Host CPU.
- After: not measured. The native Host overlay of 802ba8c69 on candidate 997905c0b was building on hbox t4
  (/home/hbox/pool/t4-retained/native.pid) when hbox went down; it reruns on persvati when build-loop announces
  per-seat pool trees (`scripts/pipeline/native-loop retained <base candidate> l0`, then grow2.sh with C at the base
  and at the overlay).

## Next
1. On persvati: native L0 overlay, grow2.sh before and after; record here. hbox is down (2026-10-31 night).
2. Tree order = wire order for StoreCodec (drop encode's sort) if the encode side (host-execution) wants it.
3. Inventory (RETAINED-MODE §3-4): R1 op4→op5 challenge node, R3 planner/deriver prepared write, I4/I5 Fn and
   carry scans, export/backup, client refs index; the lint (§7).

## Seams
- host-execution (a24974e84d3c540d1): R6 carried decoded post / one turn per record; R7 sealed World (with read-path
  ad74bb6d4410b48f3 for the provider's start). TurnOfIntent shared.
- privacy (a3f7fce75cd3e4e49): narrowed views on SparseMap.filterKeys; FORMAT (a) rebases onto L0.
