# Reds (owned by the builder, rewritten whole each round)

Tip: `cb1ff18f9f0d` (install-hermes: the candidate through current; a spec differing only by candidate director). Round finished 2026-11-06T01:13Z.
green: `6f682cdf2a92`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-cb1ff18f`.

No reds: `green` moves to `cb1ff18f9f0d`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.166 | 0.215 | 1.295 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 35.433 | 58.825 | 1.660 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.120 | 0.183 | 1.529 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 23.514 | 75.473 | 3.210 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.270 | 0.339 | 1.256 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 127.120 | 128.753 | 1.013 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-cb1ff18f/flatness.log | - | - | - | - | host-execution, store-retained |
