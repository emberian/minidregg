# Reds (owned by the builder, rewritten whole each round)

Tip: `d2989eb6e253` (world migration: the inventory, a rehearsed replay, and verify with 0 carried differences). Round finished 2026-11-07T04:03Z.
green: `eb932b7c6547`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-d2989eb6`.

No reds: `green` moves to `d2989eb6e253`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.148 | 0.210 | 1.416 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 33.175 | 59.417 | 1.791 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.125 | 0.185 | 1.482 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 23.880 | 69.394 | 2.906 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.285 | 0.365 | 1.280 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 244.831 | 257.309 | 1.051 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-d2989eb6/flatness.log | - | - | - | - | host-execution, store-retained |
