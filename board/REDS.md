# Reds (owned by the builder, rewritten whole each round)

Tip: `f5d5df8145a6` (spk-host broker: a generation's runtime pin is written once; a later rendering keeps it). Round finished 2026-11-06T03:57Z.
green: `d69889188860`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-f5d5df81`.

No reds: `green` moves to `f5d5df8145a6`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.165 | 0.178 | 1.079 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 29.333 | 61.383 | 2.093 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.147 | 0.180 | 1.225 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 23.659 | 114.345 | 4.833 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.333 | 0.351 | 1.054 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 144.353 | 129.446 | 0.897 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-f5d5df81/flatness.log | - | - | - | - | host-execution, store-retained |
