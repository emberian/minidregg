# Reds (owned by the builder, rewritten whole each round)

Tip: `6594960dd02a` (builder: REDS.md says when j14-apps was not run and which verdict it carries). Round finished 2026-11-14T21:08Z.
green: `788dfb51fb5a`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-6594960d`.

No reds: `green` moves to `6594960dd02a`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.215 | 0.202 | 0.940 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 47.426 | 80.493 | 1.697 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.224 | 0.218 | 0.973 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 42.381 | 81.479 | 1.923 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.659 | 0.410 | 0.622 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 277.575 | 243.636 | 0.878 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-6594960d/flatness.log | - | - | - | - | host-execution, store-retained |
