# Reds (owned by the builder, rewritten whole each round)

Tip: `0d7e1a2ce82f` (builder: a tip that changes only board/ is recorded as built, not rounded). Round finished 2026-11-06T02:42Z.
green: `9ac65ce9f744`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-0d7e1a2c`.

No reds: `green` moves to `0d7e1a2ce82f`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.145 | 0.203 | 1.399 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 31.684 | 75.333 | 2.378 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.115 | 0.172 | 1.494 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 23.561 | 87.288 | 3.705 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.284 | 0.360 | 1.266 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 151.171 | 130.229 | 0.861 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-0d7e1a2c/flatness.log | - | - | - | - | host-execution, store-retained |
