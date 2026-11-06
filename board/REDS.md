# Reds (owned by the builder, rewritten whole each round)

Tip: `5bcbbfe94934` (builder: REDS.md for 87b6c82dc0a6 (2 red)). Round finished 2026-11-06T06:12Z.
green: `f5d5df8145a6`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-5bcbbfe9`.

No reds: `green` moves to `5bcbbfe94934`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.170 | 0.207 | 1.221 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 29.656 | 76.830 | 2.591 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.140 | 0.175 | 1.253 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 23.278 | 74.377 | 3.195 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.314 | 0.294 | 0.938 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 203.510 | 193.140 | 0.949 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-5bcbbfe9/flatness.log | - | - | - | - | host-execution, store-retained |
