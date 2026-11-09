# Reds (owned by the builder, rewritten whole each round)

Tip: `c049a8f1498c` (builder: REDS.md for 905e181b2c97 (0 red)). Round finished 2026-11-09T01:31Z.
green: `905e181b2c97`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-c049a8f1`.

No reds: `green` moves to `c049a8f1498c`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.242 | 0.225 | 0.932 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 48.170 | 78.169 | 1.623 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.219 | 0.222 | 1.014 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 23.512 | 77.571 | 3.299 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.562 | 0.639 | 1.138 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 572.864 | 226.173 | 0.395 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-c049a8f1/flatness.log | - | - | - | - | host-execution, store-retained |
