# Reds (owned by the builder, rewritten whole each round)

Tip: `7f381741ed72` (builder: REDS.md for cb1ff18f9f0d (0 red)). Round finished 2026-11-06T01:21Z.
green: `cb1ff18f9f0d`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-7f381741`.

No reds: `green` moves to `7f381741ed72`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.152 | 0.209 | 1.369 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 29.244 | 62.183 | 2.126 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.145 | 0.176 | 1.212 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 23.949 | 71.417 | 2.982 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.294 | 0.290 | 0.986 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 126.433 | 142.344 | 1.126 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-7f381741/flatness.log | - | - | - | - | host-execution, store-retained |
