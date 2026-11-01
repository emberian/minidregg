# Seat: store-retained

Agent: a9b54e85e4a194b91 (formerly a13f0c9ab4513b2d7; about 425K tokens at 2026-10-31 night; tell root at ~500K)
Worktrees: /Users/ember/dev/minidregg-lanes/retained (lands on main; WIP rides `wip/retained-*` on origin);
/Users/ember/dev/minidregg-lanes/store-retained (main, board edits). Box: hbox pool tree t4 (lease `retained`):
`git fetch origin <branch>` there, `scripts/pipeline/lane-check FILE` per file; logs and PID files in
/home/hbox/pool/t4-retained/. Measurement on persvati. bb2 belongs to obend (t7 released).

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
1. **In flight: the held served state** (origin/wip/retained-held d6468ecaf, on main 1b0f7cb25; whole tree green
   on hbox t4). `DurableServed.Served` keeps `Held`, a `SparseMap CellId (bytes × root)` plus the allowance as a
   `ChargeTuple`, advanced per record (`Held.install_agrees`, `replayed_agrees`, `ofState_agrees`,
   `ofSnapshot_agrees`, `bare_viewAt_ofLoaded`), instead of a `DataSnapshot` whose `canonicalBytes`/`roots`/
   `available` were a closure per installed record. Overlay `hbox:/home/hbox/pool/lanes/retained/candidates/
   4f60d20e9ef7` (base 4b750eb67). The first overlay, d5c4b3cf2a41, was defective and is withdrawn:
   `flatCharge`'s lets were floated back into its match arms, so each lane read re-walked the history (story 3:
   852 s of Host CPU). **The verdict is member-side's persvati `doc new` blocks** (ab7b4fe7fb687e0ca has the
   pair). hbox Host-CPU tracks load here (the base read 700 -> 990 ms at load 8 and 1760 -> 2010 ms at load 14;
   the overlay 1150 -> 1350 ms at load 14), so no hbox number decides it. Land it only on a persvati result
   that is not slower.
2. Next in DurableServed (from he-births ac49ca4075452034f): `Opening.world` as a `WorldTrack` advanced by
   `WorldTrack.advance` on the light append, so `foldRecords`'s `World.admit` -> `pinFails` -> `cellRoot` stops
   re-encoding the authority cell per append; `snapPinFails` reads `model.roots` through `coherent`.
3. Authority nodes: a maintained digest -> capability-address index beside the authority cell (`issuerCheck`
   scans the support and hashes every capability, twice per evidence via `domainPortal`); the rest of R6(i)
   (the other writers pass `none`); member-side's `Patch.diff` (a014ff501, reviewed sound) is the bytes-only
   fallback, and the O(delta) form is the walk carrying the record's own patch.
4. Tree order = wire order for StoreCodec (drop encode's sort).
5. R3 planner/deriver prepared write; I4/I5 Fn and carry scans; export/backup; client refs index; the lint (section 7).

Landed 10-31 night: f937f2b38, `mini serve` writes its Host's PID beside the socket (`mini.host.pid`), so a Host
orphaned by a signalled server is stoppable by its PID file (root's ask; one orphan was stopped by root's word and
logged in hbox:/home/hbox/pool/t4-retained/kills.log). grow2r stops it the same way.

## Seams
- host-execution (a24974e84d3c540d1): R6 carried decoded post / one turn per record; R7 sealed World (with read-path
  ad74bb6d4410b48f3 for the provider's start). TurnOfIntent shared.
- privacy (a3f7fce75cd3e4e49): narrowed views on SparseMap.filterKeys; FORMAT (a) rebases onto L0.
