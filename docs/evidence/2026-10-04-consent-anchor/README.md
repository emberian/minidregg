# Consent anchor and named Store epochs — evidence (2026-10-04, lane SCHEMA-V2-2)

Box: burst-lane1 (Latitude f4-metal-small, AMD EPYC 4484PX, 24 threads, 93 GB), shared with other
lanes; every row carries the box's 1-minute load at the time. Lean builds of other lanes were
running throughout (column `lean_builds` in `q1-sweep.tsv` counts `lake build` processes).

Binaries (sha256 prefixes in `binaries-*.sha256`):
- **main** = GitHub main 3b709c87 (the predecessor SCHEMA-V2 range landed), built in
  /srv/lanes/schema-v2-2-main.
- **mine** = this lane before its rebase: Lean executables from the tree of 7e96c66a, `mini` from
  4e250db9 (the Rust difference between them is only where the retained anchor file lives). The
  rebase onto 4795b657 (commit b2a8d31a) applied cleanly and changes no measured code path.

## Q1 — the client re-checked the whole history at every start

Cause (read): every `mini` invocation starts `minidregg-client-consent`, whose first frame ran
`NativeHostReplay.verifyLoaded`, the genesis re-admission of every accepted record. Measured on main
(`q1-sweep.tsv`, column `genesis_s`): 0.98 s at 10 records, 2.11 s at 25, 4.19 s at 50, 10.4 s at
100, i.e. ~0.1 s per record per client start. A write runs several client starts (propose and
submit each start one and refresh), which is the CI journey finding (9.6 s -> 59 s per write between
10 and 100 records): main's propose+submit below goes 7.8 s at 25 -> 32 s at 100 -> 80 s at 200.

Fix: the provider leaves an anchor (height, genesis log start, log chain, world root) under client
custody; the next provider checks the Store against it, re-validates the image at the anchor and
reproduces its root, then admits only the later records (`Kernel/ConsentAnchor.lean`).

`q1-sweep.tsv` (fresh world, one provider start per row, `consent-admit.py`):

| records | anchored admission s | genesis admission s (= main behaviour) | propose s | submit s |
|---|---|---|---|---|
| 10 | 0.26 | 0.98 | 0.61 | 0.72 |
| 25 | 0.27 | 2.11 | 0.63 | 0.75 |
| 50 | 0.27 | 4.19 | 0.62 | 0.74 |
| 100 | 0.41 | 10.43 | 0.86 | 0.97 |
| 150 | 0.36 | – | 0.74 | 0.94 |
| 200 | 0.40 | – | 0.73 | 0.88 |
| 250 | 0.40 | – | 0.74 | 0.89 |
| 300 | 0.41 | – | 0.79 | 0.90 |

Acceptance "under 1 s at every size from 10 to 300": met (0.26–0.41 s). EXECUTED.
Beyond 300 the anchored admission is bounded by the Store open (Q2): 0.65–0.73 s at 1131 records,
2.54 s at 3020 (box load 42).

Still detected (`fork-test.txt`, EXECUTED, fresh world, own anchor dir):
- a ROLLBACK (Store and its head-anchor sidecar restored to height 5 under an anchor at 6) refuses:
  "the Store's head 5 is below the retained consent anchor at 6: the accepted history was rolled back";
- a FORK (a different valid history B6, B7 written on the height-5 Store — a genesis re-admission
  accepts it; `audit` on that Store: "audited 8 accepted records") refuses under the old anchor:
  "the Store's accepted history up to height 6 differs from the retained consent anchor: the prefix
  this client admitted was rewritten";
- control: the fork's own anchor accepts the next write.
Crash consistency of the retained anchor: Rust test
`client_consent::tests::retained_anchor_survives_a_crash_at_every_stage` (mini_sdk::durable Stage
MidWrite..AfterDirectorySync: old or new anchor, whole), with
`retained_anchor_is_offered_only_under_its_exact_binding` and
`retained_anchor_file_refuses_foreign_or_exposed_bytes`: 7 passed, 1 ignored (worker).

## Q2 — growth, main vs this lane (`growth-table.md`)

| binaries | records | Store open (load) ms | kept roots checked/differing | propose s (median of 20) | submit s (median of 20) | receipt lookup s | lookup = original | box load1 |
|---|---|---|---|---|---|---|---|---|
| main | 25 | 112 | 25/0 | 3.69 | 4.07 | mid=0.12 last=0.12 | equal | 5.50 |
| main | 50 | 106 | 50/0 | 5.74 | 6.06 | mid=0.13 last=0.12 | equal | 4.36 |
| main | 100 | 282 | 20/0 | 15.81 | 16.28 | mid=0.14 last=0.13 | equal | 19.79 |
| main | 200 | 249 | 20/0 | 39.44 | 40.60 | mid=0.15 last=0.16 | equal | 23.56 |
| mine | 25 | 113 | 25/0 | 0.67 | 0.80 | mid=0.12 last=0.12 | equal | 8.10 |
| mine | 50 | 120 | 50/0 | 0.70 | 0.83 | mid=0.12 last=0.12 | equal | 10.70 |
| mine | 100 | 172 | 20/0 | 0.74 | 0.86 | mid=0.14 last=0.14 | equal | 9.80 |
| mine | 200 | 207 | 20/0 | 0.73 | 0.84 | mid=0.11 last=0.11 | equal | 9.14 |
| mine | 300 | 228 | 30/0 | 0.78 | 0.90 | mid=0.12 last=0.12 | equal | 11.20 |
| mine | 1000 | 427 | 20/0 | 0.96 | 1.07 | mid=0.11 last=0.10 | equal | 1.19 |
| mine | 2000 | 1366 | 20/0 | 2.22 | 2.41 | mid=0.15 last=0.15 | equal | 19.95 |
| mine | 3000 | 2104 | 30/0 | 3.14 | 3.38 | mid=0.16 last=0.14 | equal | 38.35 |

Store open = store-bench `load:` (DurableReceiverIO.load). Kept receipt roots vs the specification
root: 0 differing at every level (stride in `bench-*.txt`). Lookup = the receipt lookup of the middle
and last write, equal to the original outcome at every level. Main stopped at the level shown: its
per-write cost grows ~0.2 s per record (propose+submit 80 s at 200), so 3000 would be ~10 min per
write; the main side of 300 -> 3000 is unreachable, as recorded.

Acceptance "open at 300 and 3000 within 2x of 50": **300 met (228 vs 120 ms, 1.9x); 3000 NOT met
(2104 ms, 17.5x, at box load 38; 1000: 427 ms, 3.6x at load 1.2).** Breakdown at 3000
(`bench-3000.txt`): decode every record 618 ms, the log chain over every record 300 ms, open the
sealed checkpoint 605 ms (its body carries every consumed nullifier, O(history)), root cache 77 ms.
All three large terms are O(history) work the open does to bind the in-memory image (every record
decoded, chained and tag-checked; Loaded holds the whole accepted list). Removing them from the open
means either a lazy prefix (each prefix record verified when first used, so a tampered old record
refuses at use, not at open: a check moves) or a ByteArray codec/hash path with csimp refinements
(no check moves; a constant factor, not flat). That is a design decision for the root, recorded as
remaining work, not done here.

## Q3 — a refused Store names its epoch (`epoch-breaks.txt`, EXECUTED)

One Store copy per break, one label component rewritten in its seed, opened by this lane's Host:
- state-key: "this Store was born in another epoch (state-key codec: Store state-key/tagged-v3, this Host state-key/tagged-v4)"
- schema refs: "(cell schema references: Store schema-refs/v4, this Host schema-refs/v5)"
- log tags: "(log tags: Store DREGG/NATIVE-HOST/LOG-TAG/v1, this Host DREGG/NATIVE-HOST/LOG-TAG/v2)"
- control (label unchanged): opens, 8 records.
- a real main-born Store (seed frame v1): refused as unlabelled before the head anchor (previously
  "durable head anchor refused: genesis or retained head conflicts"). The message recorded here was
  produced by an earlier build that claimed the v1 Store's component versions; the committed text
  says they are unknown (a v1 Store may be of this epoch's components, e.g. born on 3b709c87).
Each break also has a theorem: `StoreEpoch.differing_stateKey/_schemaRefs/_logTag`,
`seedEpoch_current`, `seedEpoch_v1_refused` (#assert_axioms).

## Files
`q1-sweep.tsv`, `admit.jsonl`, `fork-test.txt`, `epoch-breaks.txt`, `growth-table.md`,
`grow-{main,mine}/` (bench-N, writes-at-N, lookup-N, open.txt), `scripts/` (grow-world.sh, grow.sh,
growth-levels.sh, q1-sweep.sh, consent-admit.py, fork-test.sh, epoch-breaks.sh, table.py).
