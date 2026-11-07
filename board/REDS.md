# Reds (owned by the builder, rewritten whole each round)

Tip: `893ccd7293de` (builder: REDS.md for b4e212ca447f (1 red)). Round finished 2026-11-07T01:19Z.
green: `eb932b7c6547`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-893ccd72`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log eb932b7c6547..893ccd7293de`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `893ccd72` builder: REDS.md for b4e212ca447f (1 red) (owner: build-loop)
- `df08e974` transport: one verified sealed snapshot per pinned image per process (owner: apps-hermes)
- `93b2bf25` builder: REDS.md for eb932b7c6547 (0 red) (owner: build-loop)
- `72ec2542` PERF-CLIENT: row 19 through an empty intent; rows 26 (236 upgrade spin) and 27 (op 5 grows with birt

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.153 | 0.179 | 1.172 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 33.170 | 63.726 | 1.921 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.127 | 0.170 | 1.345 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_wall_ms | 47.903 | 75.474 | 1.576 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.315 | 0.557 | 1.769 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 390.118 | 239.397 | 0.614 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-893ccd72/flatness.log | - | - | - | - | host-execution, store-retained |
