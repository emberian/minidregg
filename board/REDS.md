# Reds (owned by the builder, rewritten whole each round)

Tip: `03708c9a373e` (builder: REDS.md for 0a92413139bd (1 red)). Round finished 2026-11-07T00:05Z.
green: `477bf8e9eb81`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-03708c9a`.

No reds: `green` moves to `03708c9a373e`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.220 | 0.240 | 1.090 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 50.842 | 88.404 | 1.739 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.165 | 0.235 | 1.425 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 37.046 | 104.788 | 2.829 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.419 | 0.459 | 1.096 | 1.856 | read-path |
| flatness-get | FAIL | get_wall_ms | 147.573 | 280.601 | 1.901 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-03708c9a/flatness.log | - | - | - | - | host-execution, store-retained |
