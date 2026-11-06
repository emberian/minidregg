# Reds (owned by the builder, rewritten whole each round)

Tip: `8bd7da7c5565` (builder: REDS.md for 0c628486faed (0 red)). Round finished 2026-11-06T01:37Z.
green: `0c628486faed`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-8bd7da7c`.

No reds: `green` moves to `8bd7da7c5565`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.211 | 0.217 | 1.031 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 35.115 | 76.460 | 2.177 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.179 | 0.188 | 1.054 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 29.560 | 97.628 | 3.303 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.352 | 0.350 | 0.995 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 127.000 | 137.418 | 1.082 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-8bd7da7c/flatness.log | - | - | - | - | host-execution, store-retained |
