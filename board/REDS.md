# Reds (owned by the builder, rewritten whole each round)

Tip: `980d80c5dba8` (demo walk reds: provision replans a consent-refused Plan, the door re-authors a prepare-re). Round finished 2026-11-09T01:54Z.
green: `c049a8f1498c`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-980d80c5`.

No reds: `green` moves to `980d80c5dba8`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.232 | 0.225 | 0.973 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 46.352 | 85.575 | 1.846 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.178 | 0.256 | 1.444 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 19.726 | 76.742 | 3.890 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.445 | 0.359 | 0.806 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 176.669 | 161.115 | 0.912 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-980d80c5/flatness.log | - | - | - | - | host-execution, store-retained |
