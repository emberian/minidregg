# Reds (owned by the builder, rewritten whole each round)

Tip: `93d8a0a0f144` (perf(submit): complete proof obligations for retiresCellFast, ofCellsFast, and narrowPacke). Round finished 2026-11-01T09:23Z.
green: `dbb0dc30de44`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-93d8a0a0`.

No reds: `green` moves to `93d8a0a0f144`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | FAIL | broken: propose_cpu_ms: early window below measurement resolution; increase --lo | - | - | - | - | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 45.000 | 48.500 | 1.078 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 124.701 | 144.542 | 1.159 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-93d8a0a0/flatness.log | - | - | - | - | host-execution, store-retained |
