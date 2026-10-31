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
L0 before/after, `grow2r.sh` (hot-path's grow2.sh parameterised; 8 sequential `story new` in one fresh world, Host
CPU per story from /proc, perf of stories 2 and 8), hbox t4 2026-10-31 16:00-16:16, logs in /home/hbox/pool/t4-retained/
(gb = before, ga = after). hbox is a shared box, so these are CPU seconds, not wall timings.

| Host CPU per `story new` | s1 | s2 | s4 | s6 | s8 | s1 → s8 |
|---|---|---|---|---|---|---|
| before: candidate 997905c0b | 590 ms | 630 | 730 | 880 | 1200 | +610 ms (2.0x) |
| after: same candidate, L0 Host (802ba8c69 overlay) | 500 ms | 550 | 600 | 640 | 700 | +200 ms (1.4x) |

- Profile, story 8, inclusive: `DFinsupp.update` under `Store.set` 24.7 % + 10.8 % and `Function.update` 13.5 % before;
  gone after (`SparseMap.set` 1.1 %, tree balance 0.6 %). `sortedSupport` 4.8 % → 1.0 %, `StoreCodec.encode` 4.2 % → 3.3 %.
- The after ran with the base candidate's consent provider: the overlay's own provider carried ed875b899's
  refresh defect (`durable log is not a turn log: a verification walk carries no World`, every story rc=1), which
  main fixed in 86c9dbddb. Not an L0 defect.
- What still grows (after, story 8): the signed read, `queryLoaded` 34 %, `authorizeAuthenticated` 28 %, `checkGrant`
  23.5 %, `capabilityEvidenceChecked` 19.6 %, cSHAKE256 14 %; `NativeHostSession.refresh` 14.3 % (10.3 % at story 2).
  The first is R1's target.

## Next
1. R1 (op 4 → op 5 challenge retained; WIP a42237ca7 on branch l0-land, rebased onto 8cbe36d62): check, overlay,
   grow2r after; the read's `checkGrant`/cSHAKE share is the number to move.
2. Then `NativeHostSession.refresh` (still grows story 2 → 8); R3 planner/deriver prepared write; I4/I5 Fn and carry
   scans; export/backup; client refs index; the lint (§7).
3. Tree order = wire order for StoreCodec (drop encode's sort) if host-execution wants it.

## Seams
- host-execution (a24974e84d3c540d1): R6 carried decoded post / one turn per record; R7 sealed World (with read-path
  ad74bb6d4410b48f3 for the provider's start). TurnOfIntent shared.
- privacy (a3f7fce75cd3e4e49): narrowed views on SparseMap.filterKeys; FORMAT (a) rebases onto L0.
