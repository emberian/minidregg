# Seat: store-retained

Agent: a9b54e85e4a194b91 (formerly a13f0c9ab4513b2d7; about 365K tokens at 2026-10-31 evening; tell root at ~500K)
Worktrees: /Users/ember/dev/minidregg-lanes/retained (branch lane/retained-l0, lands on main when the whole tree builds,
then deleted); /Users/ember/dev/minidregg-lanes/store-retained (main, for board edits). Box tree: hbox pool t4
(`. /home/hbox/pool/pool.env; lane-tree renew retained`), builds `swarm-build lake build Minidregg` from t4, logs and
PID files in /home/hbox/pool/t4-retained/bN.{log,pid}.

Owns: the leaf layer and retained mode. Theory/Retained.lean (the maintained-node statement: maintained answer =
recomputation after any admitted run and across checkpoint/restore; the chain rule; the generic red-green memo node),
Theory/SparseMap.lean (persistent extensional tree map over injective List Nat key codes), Theory/DeriveStoreKey.lean
(`deriving StoreKey`), Theory/Store.lean's representation, World's Cells; docs/RETAINED-MODE.md (node inventory,
migration order, generation design, lint design). L0 touches DFinsupp-on-store call sites across Kernel/Compiler
mechanically; those files stay their owners'.

Quest: L0, the tree-backed Store (every get/set O(log n); WorldCompact deleted), then the derived values onto
maintained nodes, widest cost first.

## Landed (main)
- 675a80745 Theory/Retained.lean; 1d4ff4efb docs/RETAINED-MODE.md; 62aa5fcf8 footprint renames, pins, Theory/SparseMap;
  05bffae27 transport lemmas; 7f42f6445 RETAINED-MODE continuation.

## In flight: L0 on lane/retained-l0 (not on main yet)
- Theory: every file green per file. SparseMap gains `deriving StoreKey`, `ofDFinsupp` (audit a4d9a6f4: inverse
  view), `toDFinsupp_zero'`, `ofFinset` (computable DFinsupp.mk), `filterKeys` (DFinsupp.filter), `map` (mapRange),
  UInt32/UInt64 codes; `set` is one `alter`, so `set` terms unify argument by argument.
- Kernel/Compiler: key types of every layout derive StoreKey with a keyCode per key family; World's TxId/D binders gain
  StoreKey; Cells is a SparseMap; WorldCompact and compactEvery deleted; StoreCodec builds by `set` and reads the tree's
  support; the cached-support twins (existsSupport/issuerCheckFast, supportCached reads) collapse.
- Whole-tree builds on t4: b1..b10, reds down to 3 files at b10; b11 running (90f765bff).

## Next
1. b11 green → merge main into lane/retained-l0, rebuild, land on main, delete the branch; tell host-execution
   (a0fee5643746e520c) and privacy (a8da2b953507b402b) to rebase. Port perf-client's DeployedRepresentsCheck allSupport
   to `w.system.keys` in the merge.
2. Measure: persvati standing world, `story new` 2 → 8 Host CPU and birth op2 per height, before (main) and after L0.
3. Then the inventory (docs/RETAINED-MODE.md §3-4): R1 op4→op5 challenge node, R3 planner/deriver prepared write,
   I4/I5 Fn and carry scans, export/backup, the client refs index; the lint (§7).

## Seams
- host-execution: R6 (carried decoded post; one derived turn per record) and R7 (sealed World) are theirs; TurnOfIntent
  shared (my edits: run_of_distinct's ext, the StoreKey D variable).
- privacy: FORMAT (a) rebases onto L0; narrowed views now `SparseMap.filterKeys`.
