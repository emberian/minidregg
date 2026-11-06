# Reds (owned by the builder, rewritten whole each round)

Tip: `e7145c9c170e` (builder: REDS.md for 5e9aa1778312 (0 red)). Round finished 2026-11-06T03:14Z.
green: `5e9aa1778312`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-e7145c9c`.

No reds: `green` moves to `e7145c9c170e`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.169 | 0.186 | 1.096 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 30.239 | 60.889 | 2.014 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.157 | 0.160 | 1.014 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 26.631 | 71.109 | 2.670 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.317 | 0.394 | 1.241 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 128.690 | 155.897 | 1.211 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-e7145c9c/flatness.log | - | - | - | - | host-execution, store-retained |
