# Reds (owned by the builder, rewritten whole each round)

Tip: `477bf8e9eb81` (builder: REDS.md for 8bbfc0798d57 (2 red)). Round finished 2026-11-06T18:50Z.
green: `8f2d63fab93f`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-477bf8e9`.

No reds: `green` moves to `477bf8e9eb81`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.154 | 0.202 | 1.313 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 33.506 | 73.171 | 2.184 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.138 | 0.194 | 1.404 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 27.049 | 87.631 | 3.240 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.294 | 0.275 | 0.934 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 129.292 | 136.579 | 1.056 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-477bf8e9/flatness.log | - | - | - | - | host-execution, store-retained |
