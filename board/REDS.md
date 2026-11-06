# Reds (owned by the builder, rewritten whole each round)

Tip: `0c628486faed` (builder: REDS.md for 7f381741ed72 (0 red)). Round finished 2026-11-06T01:29Z.
green: `7f381741ed72`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-0c628486`.

No reds: `green` moves to `0c628486faed`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.186 | 0.210 | 1.131 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 34.097 | 62.697 | 1.839 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.132 | 0.173 | 1.309 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 26.515 | 78.622 | 2.965 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.292 | 0.277 | 0.948 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 325.507 | 123.099 | 0.378 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-0c628486/flatness.log | - | - | - | - | host-execution, store-retained |
