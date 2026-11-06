# Reds (owned by the builder, rewritten whole each round)

Tip: `d69889188860` (grain-runtime: the failed-resident reconciliation accepts the resident's selectedRequest; ). Round finished 2026-11-06T03:37Z.
green: `e7145c9c170e`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-d6988918`.

No reds: `green` moves to `d69889188860`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.153 | 0.197 | 1.285 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 29.833 | 64.782 | 2.171 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.147 | 0.155 | 1.055 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 38.607 | 74.518 | 1.930 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.493 | 0.590 | 1.198 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 174.357 | 178.608 | 1.024 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-d6988918/flatness.log | - | - | - | - | host-execution, store-retained |
