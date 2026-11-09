# Reds (owned by the builder, rewritten whole each round)

Tip: `fd1f1b33a35f` (builder: REDS.md for 980d80c5dba8 (0 red)). Round finished 2026-11-09T02:20Z.
green: `980d80c5dba8`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-fd1f1b33`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | no | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log 980d80c5dba8..fd1f1b33a35f`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `fd1f1b33` builder: REDS.md for 980d80c5dba8 (0 red) (owner: build-loop)
- `760fdf33` held directory, held index rows, seal off the member's path (PERF-CLIENT rows 36, 37, 38) (owner: bytes-repr)
- `23f7df18` world-migrate verify: a seed account whose balance only grew lost nothing
- `4e7a094f` seed: house-rules' link and note go on its last line, whatever the text's length

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.193 | 0.210 | 1.089 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 51.944 | 83.900 | 1.615 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.149 | 0.212 | 1.421 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 34.550 | 61.136 | 1.769 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.583 | 0.474 | 0.812 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 199.604 | 177.514 | 0.889 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-fd1f1b33/flatness.log | - | - | - | - | host-execution, store-retained |
