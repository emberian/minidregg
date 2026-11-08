# Reds (owned by the builder, rewritten whole each round)

Tip: `7b40901067ef` (builder: REDS.md for 7f80be31654a (0 red)). Round finished 2026-11-08T20:30Z.
green: `7f80be31654a`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-7b409010`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | no | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log 7f80be31654a..7b40901067ef`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `7b409010` builder: REDS.md for 7f80be31654a (0 red) (owner: build-loop)
- `96ae631f` query: a stream window's payloads and a since read come through the held log's newest end; PERF-CLIE (owner: apps-hermes)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.193 | 0.225 | 1.168 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 61.052 | 114.003 | 1.867 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.148 | 0.231 | 1.554 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 37.069 | 136.470 | 3.682 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.620 | 0.602 | 0.972 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 282.046 | 232.635 | 0.825 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-7b409010/flatness.log | - | - | - | - | host-execution, store-retained |
