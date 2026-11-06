# Reds (owned by the builder, rewritten whole each round)

Tip: `8f2d63fab93f` (grain-runtime: the lost resident prompt is recorded before the startup-recovery early retu). Round finished 2026-11-06T06:38Z.
green: `5bcbbfe94934`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-8f2d63fa`.

No reds: `green` moves to `8f2d63fab93f`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.159 | 0.209 | 1.314 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 31.720 | 93.565 | 2.950 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.132 | 0.207 | 1.568 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 27.317 | 99.360 | 3.637 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.345 | 0.338 | 0.978 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 135.662 | 128.205 | 0.945 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-8f2d63fa/flatness.log | - | - | - | - | host-execution, store-retained |
