# Reds (owned by the builder, rewritten whole each round)

Tip: `788dfb51fb5a` (simplex: the commit floor is the fold (`lastCommitted_spec`); harness probe sends above th). Round finished 2026-11-14T03:50Z.
green: `980d80c5dba8`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-788dfb51`.

No reds: `green` moves to `788dfb51fb5a`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | FAIL | submit_cpu_ms | 0.166 | 0.275 | 1.652 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 42.111 | 123.385 | 2.930 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_cpu_ms | 0.146 | 0.301 | 2.062 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 20.856 | 113.833 | 5.458 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.591 | 0.310 | 0.524 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 302.617 | 333.104 | 1.101 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-788dfb51/flatness.log | - | - | - | - | host-execution, store-retained |
