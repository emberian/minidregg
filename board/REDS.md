# Reds (owned by the builder, rewritten whole each round)

Tip: `5e9aa1778312` (grain-runtime: the operator refuses a never-admitted resident prompt (admin `resident refu). Round finished 2026-11-06T03:06Z.
green: `0d7e1a2ce82f`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-5e9aa177`.

No reds: `green` moves to `5e9aa1778312`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.227 | 0.236 | 1.039 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 41.195 | 94.615 | 2.297 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_cpu_ms | 0.177 | 0.284 | 1.602 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 31.663 | 114.409 | 3.613 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.528 | 0.472 | 0.894 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 171.319 | 155.443 | 0.907 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-5e9aa177/flatness.log | - | - | - | - | host-execution, store-retained |
