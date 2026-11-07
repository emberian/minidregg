# Reds (owned by the builder, rewritten whole each round)

Tip: `eb932b7c6547` (Merge remote-tracking branch 'origin/main' into lane/perf-client). Round finished 2026-11-07T00:52Z.
green: `03708c9a373e`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-eb932b7c`.

No reds: `green` moves to `eb932b7c6547`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.188 | 0.194 | 1.034 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 32.560 | 68.192 | 2.094 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.121 | 0.174 | 1.442 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 26.709 | 69.482 | 2.601 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.353 | 0.282 | 0.799 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 150.611 | 135.667 | 0.901 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-eb932b7c/flatness.log | - | - | - | - | host-execution, store-retained |
