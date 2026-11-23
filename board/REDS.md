# Reds (owned by the builder, rewritten whole each round)

Tip: `da18c2ec37cf` (Record hbox append and GET measurements and the remaining content-size cost). Round finished 2026-11-23T20:13Z.
green: `453aba535878`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-da18c2ec`.

No reds: `green` moves to `da18c2ec37cf`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | FAIL | submit_cpu_ms | 23.078 | 50.124 | 2.172 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 33.152 | 62.255 | 1.878 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_cpu_ms | 5.883 | 13.674 | 2.324 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 26.512 | 55.201 | 2.082 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 767.688 | 894.571 | 1.165 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 971.073 | 1060.018 | 1.092 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-da18c2ec/flatness.log | - | - | - | - | host-execution, store-retained |
