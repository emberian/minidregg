# Reds (owned by the builder, rewritten whole each round)

Tip: `d6f873639367` (builder: REDS.md for a08f00d6e4fb (3 red)). Round finished 2026-11-01T11:30Z.
green: `93d8a0a0f144`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-d6f87363`.

No reds: `green` moves to `d6f873639367`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | FAIL | submit_cpu_ms | 0.142 | 0.235 | 1.655 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 29.425 | 59.524 | 2.023 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_cpu_ms | 0.124 | 0.200 | 1.619 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 24.127 | 75.567 | 3.132 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.452 | 0.389 | 0.860 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 235.843 | 287.788 | 1.220 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-d6f87363/flatness.log | - | - | - | - | host-execution, store-retained |
