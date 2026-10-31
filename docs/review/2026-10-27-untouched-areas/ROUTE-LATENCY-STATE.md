# Route latency: state (lane/un-route-latency; present state, rewritten whole 2026-10-28)

Red: a request through a grain route takes 6 to 17 s wall (TextEditor login POST 11 s alone; the app waits
about 10 s). Written during the 2026-10-28 demo ship freeze, which has since lifted; the Owed list below stands.

## Finding (perf profile, hbox, candidate 349e59ef1, SandMD qualify)

- Plan (op36, 0.03 s) and assemble (op37, no append) are cheap. The cost is the SUBMIT turn: about 5.3 s of
  single-thread CPU in the Host (114 s utime over the qualify, 0.8 s stime; not run-queue wait).
- It is whole-image recomputation: salted roots of whole cells (`StoreCodec.rootBytes` -> `saltedRoot` ->
  `leaves` -> `opening`), `List UInt8` codec churn (`List.reverseAux` 19% self, `lean_cstr_to_nat` from
  `NatDigits255Fast.digitsBytes`), `receiverSemanticsFrom` over the whole manifest, and a charge closure that
  re-derived the ordinary intent per lane query. Stacks came from gdb snapshots (the Host runs from a memfd,
  so perf could not unwind); raw samples are not kept.
- Head-of-line: no fix to build. One resident serves one grain; same-grain requests share one CAS chain and one
  rpc handle; a websocket open does not hold the loop after admission. Do not re-propose parallel dispatch.

## Landed on main

- 94b8de93c: `chargeOf` takes the ordinary intent as a parameter (Pending, Agent, Lifetime dispatch cores);
  `candidateIntent_exactCharge`; no statement changed.
- f90726140: `ExactReadback.ofAppended` runs `Loaded.prepare` (engine) instead of `DurableCheckpoint.prepare`.
- 3de917395: `scripts/spk-platform/route-cpu-probe.sh WORLD.env ROUTE_DIR [N]` (Host CPU per GET).
- b1.sh `write_SandMD` times `POST /new`, published, fails only above `ROUTE_POST_BUDGET_S` (90 s); unrun.
- The perf-rake lane (ae523f43aa7bfc923) owns: cell.root / Materialized caching, `receiverSemanticsFrom` via
  Config/Profile caching, nullifier payloads, the `NatDigits255Fast` literal, StoreCodec root/blinding key, the
  ByteArray StreamCodec writer.

## Owed

1. Before/after CPU on the first candidate carrying f90726140, against 349e59ef1: bring up a SandMD world on
   hbox (`flock -o /tank/lanes/world-up.lock`, MINI_OPERATOR_UID=1000, fresh run root, staging under
   /tank/lanes/un-route-latency chmod go-w), run `featured-qualify.sh` (b1 table, letter j), then
   `route-cpu-probe.sh` and the timed POST row. Baseline: about 5.3 s Host CPU per submit; 6 to 17 s wall per
   GET. Publish both numbers; they are not a gate.
2. Remaining `ofAppended` cuts (Kernel/NativeHostReplay.lean, near `ExactReadback.ofAppended`): the
   `derived.judge` re-run, `validateLoadedFrom`, and the second `Loaded.extend` (`exactCandidate`). Decide
   after (1).
3. Open question, ember's: should a read through an enrolled route make a chain turn at all (login mutates
   state, so only a cheaper submit fixes TextEditor and Wekan).

## Ruling in force

Ember via root: cuts need not be statement-neutral equalities. A statement or def phrased so that it forces
recomputation may be rephrased efficiently and re-proved downstream; weakening what a statement guarantees is
never allowed; a keystone change gets a short note to the deputy for root.

## Hygiene

hbox umask is 0002 (`chmod -R go-w` staged trees; fresh run root; world-up lock queue can be long). On dregg-ref
run lake and git as lanes, in your own worktree, and call `scripts/pipeline/lane-check` bare (it takes
closure-lock itself; wrapping it deadlocks). Worktree: /Users/ember/dev/minidregg-lanes/un-ns-owner holds this
branch.
