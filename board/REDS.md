# Reds (owned by the builder, rewritten whole each round)

Tip: `453aba535878` (Judge inspect byte comparisons from the exact retained renderer inputs). Round finished 2026-11-23T08:07Z.
green: `1db75a1dba5d`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-453aba53`.

No reds: `green` moves to `453aba535878`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.218 | 0.267 | 1.224 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 49.063 | 112.891 | 2.301 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.249 | 0.385 | 1.548 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 27.049 | 119.408 | 4.415 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.862 | 0.633 | 0.735 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 1017.445 | 957.508 | 0.941 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-453aba53/flatness.log | - | - | - | - | host-execution, store-retained |
