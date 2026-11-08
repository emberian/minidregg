# Reds (owned by the builder, rewritten whole each round)

Tip: `7f80be31654a` (grain controller: a typed close for a prompt witness its allowance outlived (`reconcile pr). Round finished 2026-11-08T20:13Z.
green: `d2989eb6e253`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-7f80be31`.

No reds: `green` moves to `7f80be31654a`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.191 | 0.209 | 1.092 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 54.890 | 106.788 | 1.945 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.152 | 0.225 | 1.479 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 44.369 | 119.398 | 2.691 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.542 | 0.386 | 0.713 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 293.253 | 194.201 | 0.662 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-7f80be31/flatness.log | - | - | - | - | host-execution, store-retained |
