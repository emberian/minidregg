# Reds (owned by the builder, rewritten whole each round)

Tip: `d54f4f38197c` (builder: REDS.md for 19264a688e23 (1 red)). Round finished 2026-11-07T00:27Z.
green: `03708c9a373e`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-d54f4f38`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log 03708c9a373e..d54f4f38197c`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `d54f4f38` builder: REDS.md for 19264a688e23 (1 red) (owner: build-loop)
- `e99cc891` builder: REDS.md for 03708c9a373e (0 red) (owner: build-loop)
- `0dc4b11c` builder: REDS.md for 03708c9a373e (1 red) (owner: build-loop)
- `588536fd` PERF-CLIENT: row 19 through full readiness (236), the Host image unchanged
- `469d84d9` Merge remote-tracking branch 'origin/main' into lane/perf-client
- `7d809f34` consent catch-up: the thread ends with its resident; the relay test's provider acknowledges 236 (owner: apps-hermes)
- `7b20a137` consent catch-up through full readiness (236): the served Host image unchanged (owner: apps-hermes)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.198 | 0.237 | 1.196 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 40.470 | 93.067 | 2.300 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.134 | 0.197 | 1.474 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 52.426 | 110.345 | 2.105 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.412 | 0.375 | 0.909 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 147.092 | 143.224 | 0.974 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-d54f4f38/flatness.log | - | - | - | - | host-execution, store-retained |
