# Reds (owned by the builder, rewritten whole each round)

Tip: `8b019bd95d5b` (Use the QSAG Keccak permutation across the native cSHAKE root seam). Round finished 2026-11-23T06:01Z.
green: `1db75a1dba5d`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-8b019bd9`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | no | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log 1db75a1dba5d..8b019bd95d5b`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `8b019bd9` Use the QSAG Keccak permutation across the native cSHAKE root seam
- `3c04b71d` builder: REDS.md for 1db75a1dba5d (0 red) (owner: build-loop)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.343 | 0.315 | 0.917 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | submit_wall_ms | 160.720 | 177.932 | 1.107 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.254 | 0.306 | 1.205 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 90.021 | 147.820 | 1.642 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.838 | 0.576 | 0.688 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 581.523 | 254.689 | 0.438 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-8b019bd9/flatness.log | - | - | - | - | host-execution, store-retained |
