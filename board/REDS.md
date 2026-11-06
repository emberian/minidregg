# Reds (owned by the builder, rewritten whole each round)

Tip: `6f682cdf2a92` (shared-resident-useful-work: the room-write binding is written under the journal lock). Round finished 2026-11-06T00:29Z.
green: `f1835938bf6e`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-6f682cdf`.

No reds: `green` moves to `6f682cdf2a92`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.170 | 0.197 | 1.158 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 31.033 | 60.304 | 1.943 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_cpu_ms | 0.105 | 0.174 | 1.654 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 23.608 | 78.143 | 3.310 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.339 | 0.245 | 0.724 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 226.856 | 124.339 | 0.548 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-6f682cdf/flatness.log | - | - | - | - | host-execution, store-retained |
