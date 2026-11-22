# Reds (owned by the builder, rewritten whole each round)

Tip: `8cd1f660afc7` (feat(selvage): Wave-10 GoldilocksDregg180Bridge UD-100 zero-wrap BabyBear-in-Goldilocks & ). Round finished 2026-11-22T21:03Z.
green: `053906870674`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-8cd1f660`.

No reds: `green` moves to `8cd1f660afc7`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.201 | 0.219 | 1.090 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 36.948 | 92.964 | 2.516 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.164 | 0.212 | 1.292 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 21.228 | 76.458 | 3.602 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.484 | 0.396 | 0.819 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 286.263 | 277.472 | 0.969 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-8cd1f660/flatness.log | - | - | - | - | host-execution, store-retained |
