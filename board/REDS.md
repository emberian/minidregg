# Reds (owned by the builder, rewritten whole each round)

Tip: `55d0721c587e` (builder: REDS.md for fd1f1b33a35f (1 red)). Round finished 2026-11-09T02:44Z.
green: `980d80c5dba8`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-55d0721c`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log 980d80c5dba8..55d0721c587e`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `55d0721c` builder: REDS.md for fd1f1b33a35f (1 red) (owner: build-loop)
- `5f6cc3ef` seal encodes its body once; the light open holds the whole index trie (PERF-CLIENT rows 37, 38) (owner: read-path)
- `fd1f1b33` builder: REDS.md for 980d80c5dba8 (0 red) (owner: build-loop)
- `760fdf33` held directory, held index rows, seal off the member's path (PERF-CLIENT rows 36, 37, 38) (owner: bytes-repr)
- `23f7df18` world-migrate verify: a seed account whose balance only grew lost nothing
- `4e7a094f` seed: house-rules' link and note go on its last line, whatever the text's length

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.190 | 0.241 | 1.267 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 35.377 | 94.630 | 2.675 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.153 | 0.230 | 1.506 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 36.403 | 73.300 | 2.014 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.497 | 0.703 | 1.415 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 510.873 | 280.948 | 0.550 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-55d0721c/flatness.log | - | - | - | - | host-execution, store-retained |
