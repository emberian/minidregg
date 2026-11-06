# Reds (owned by the builder, rewritten whole each round)

Tip: `a37e28146c77` (grain-runtime: a resident prompt lost at a controller restart gets an outcome, and the res). Round finished 2026-11-06T05:44Z.
green: `f5d5df8145a6`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-a37e2814`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| pack | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| umbrella-tree | running | - | no | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log f5d5df8145a6..a37e28146c77`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `a37e2814` grain-runtime: a resident prompt lost at a controller restart gets an outcome, and the resident clos (owner: apps-hermes)
- `e412be01` board: build-loop row: the 2026-11-06 plain ships and what they taught
- `04d28aa5` builder: REDS.md for f5d5df8145a6 (0 red) (owner: build-loop)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.193 | 0.212 | 1.099 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 36.389 | 69.062 | 1.898 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.148 | 0.178 | 1.205 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_wall_ms | 144.402 | 82.637 | 0.572 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.353 | 0.584 | 1.653 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 164.443 | 204.301 | 1.242 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-a37e2814/flatness.log | - | - | - | - | host-execution, store-retained |
