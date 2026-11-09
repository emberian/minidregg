# Reds (owned by the builder, rewritten whole each round)

Tip: `905e181b2c97` (demo reds: unit-owned residents, prompt publication hand-off, door makes a kept member's w). Round finished 2026-11-09T01:17Z.
green: `e8e3bb8c83cc`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-905e181b`.

No reds: `green` moves to `905e181b2c97`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.236 | 0.259 | 1.099 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 66.873 | 123.075 | 1.840 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.255 | 0.313 | 1.224 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 24.001 | 95.692 | 3.987 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.734 | 0.630 | 0.858 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 271.873 | 303.218 | 1.115 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-905e181b/flatness.log | - | - | - | - | host-execution, store-retained |
