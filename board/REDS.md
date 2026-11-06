# Reds (owned by the builder, rewritten whole each round)

Tip: `a37e28146c77` (grain-runtime: a resident prompt lost at a controller restart gets an outcome, and the res). Round finished 2026-11-06T05:35Z.
green: `f5d5df8145a6`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-a37e2814`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| gate:composed:documents | composed documents fail | not rerun | no | infra, member-side | fail: documents:protected: no stderr; see /ci-composed/c-a37e28/composed/state/evidence/01 |
| gate:composed:store-restart | composed store-restart blocked | not rerun | no | host-execution | blocked: prerequisite documents has not passed |

Suspect commits since green (`git log f5d5df8145a6..a37e28146c77`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `a37e2814` grain-runtime: a resident prompt lost at a controller restart gets an outcome, and the resident clos (owner: apps-hermes)
- `e412be01` board: build-loop row: the 2026-11-06 plain ships and what they taught
- `04d28aa5` builder: REDS.md for f5d5df8145a6 (0 red) (owner: build-loop)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.255 | 0.274 | 1.074 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 64.292 | 137.214 | 2.134 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.207 | 0.290 | 1.398 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 42.641 | 169.343 | 3.971 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.587 | 0.367 | 0.625 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 215.075 | 158.001 | 0.735 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-a37e2814/flatness.log | - | - | - | - | host-execution, store-retained |
