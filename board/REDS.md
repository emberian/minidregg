# Reds (owned by the builder, rewritten whole each round)

Tip: `f1835938bf6e` (candidate: the role paths keep the manifest's own form). Round finished 2026-11-05T21:43Z.
green: `eefe274475cd`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-f1835938`.

No reds: `green` moves to `f1835938bf6e`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.160 | 0.191 | 1.199 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 30.097 | 60.474 | 2.009 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.127 | 0.169 | 1.331 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 22.766 | 73.993 | 3.250 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.306 | 0.296 | 0.965 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 137.127 | 128.419 | 0.937 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-f1835938/flatness.log | - | - | - | - | host-execution, store-retained |
