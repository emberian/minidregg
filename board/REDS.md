# Reds (owned by the builder, rewritten whole each round)

Tip: `9ac65ce9f744` (builder: REDS.md for 8bd7da7c5565 (0 red)). Round finished 2026-11-06T01:46Z.
green: `8bd7da7c5565`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-9ac65ce9`.

No reds: `green` moves to `9ac65ce9f744`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.164 | 0.203 | 1.237 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 33.148 | 68.913 | 2.079 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.142 | 0.163 | 1.148 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 23.386 | 98.784 | 4.224 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.594 | 0.394 | 0.663 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 198.193 | 142.007 | 0.717 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-9ac65ce9/flatness.log | - | - | - | - | host-execution, store-retained |
