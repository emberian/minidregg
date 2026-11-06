# Reds (owned by the builder, rewritten whole each round)

Tip: `87b6c82dc0a6` (builder: the board-only skip line without the doubled prefix). Round finished 2026-11-06T05:53Z.
green: `f5d5df8145a6`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-87b6c82d`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| gate:composed:documents | composed documents fail | not rerun | no | infra, member-side | fail: documents:protected: no stderr; see /ci-composed/c-87b6c8/composed/state/evidence/01 |
| gate:composed:store-restart | composed store-restart blocked | not rerun | no | host-execution | blocked: prerequisite documents has not passed |

Suspect commits since green (`git log f5d5df8145a6..87b6c82dc0a6`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `87b6c82d` builder: the board-only skip line without the doubled prefix (owner: build-loop)
- `b6e9886c` builder: REDS.md for a37e28146c77 (2 red) (owner: build-loop)
- `2d8d130a` builder: REDS.md for a37e28146c77 (7 red) (owner: build-loop)
- `bf3dd3a7` builder: REDS.md for a37e28146c77 (2 red) (owner: build-loop)
- `a37e2814` grain-runtime: a resident prompt lost at a controller restart gets an outcome, and the resident clos (owner: apps-hermes)
- `e412be01` board: build-loop row: the 2026-11-06 plain ships and what they taught
- `04d28aa5` builder: REDS.md for f5d5df8145a6 (0 red) (owner: build-loop)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.212 | 0.223 | 1.053 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 37.903 | 64.917 | 1.713 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.157 | 0.222 | 1.413 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_wall_ms | 112.575 | 82.839 | 0.736 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.310 | 0.323 | 1.042 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 250.034 | 139.035 | 0.556 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-87b6c82d/flatness.log | - | - | - | - | host-execution, store-retained |
