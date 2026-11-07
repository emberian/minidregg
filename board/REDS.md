# Reds (owned by the builder, rewritten whole each round)

Tip: `1c71a6fe2d94` (builder: REDS.md for 976f31067e01 (1 red)). Round finished 2026-11-07T01:56Z.
green: `eb932b7c6547`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-1c71a6fe`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log eb932b7c6547..1c71a6fe2d94`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `1c71a6fe` builder: REDS.md for 976f31067e01 (1 red) (owner: build-loop)
- `a0ad8559` PERF-CLIENT: row 28, receipt continuity verifier processes
- `3e6b24eb` Merge remote-tracking branch 'origin/main' into lane/perf-client
- `9b117157` receipt continuity: no verifier process for a read whose point is already known (owner: apps-hermes)
- `200cb5f5` builder: REDS.md for 893ccd7293de (1 red) (owner: build-loop)
- `893ccd72` builder: REDS.md for b4e212ca447f (1 red) (owner: build-loop)
- `df08e974` transport: one verified sealed snapshot per pinned image per process (owner: apps-hermes)
- `93b2bf25` builder: REDS.md for eb932b7c6547 (0 red) (owner: build-loop)
- `72ec2542` PERF-CLIENT: row 19 through an empty intent; rows 26 (236 upgrade spin) and 27 (op 5 grows with birt

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.165 | 0.190 | 1.149 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 37.221 | 79.501 | 2.136 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.134 | 0.162 | 1.209 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 27.583 | 97.198 | 3.524 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.285 | 0.282 | 0.990 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 364.823 | 150.610 | 0.413 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-1c71a6fe/flatness.log | - | - | - | - | host-execution, store-retained |
