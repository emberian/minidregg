# Reds (owned by the builder, rewritten whole each round)

Tip: `87b6c82dc0a6` (builder: the board-only skip line without the doubled prefix). Round finished 2026-11-06T06:02Z.
green: `f5d5df8145a6`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-87b6c82d`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| pack | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |

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
| flatness-submit | PASS | submit_cpu_ms | 0.200 | 0.322 | 1.613 | 1.849 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 61.343 | 257.759 | 4.202 | 1.849 | host-execution, store-retained |
| flatness-submit | FAIL | propose_cpu_ms | 0.175 | 0.440 | 2.518 | 1.849 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 72.884 | 331.263 | 4.545 | 1.849 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.373 | 0.318 | 0.851 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 164.664 | 150.897 | 0.916 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-87b6c82d/flatness.log | - | - | - | - | host-execution, store-retained |
