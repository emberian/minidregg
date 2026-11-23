# Reds (owned by the builder, rewritten whole each round)

Tip: `1db75a1dba5d` (feat(wave11): land credible SVCS compiler + 2026/587 sumcheck, Frigo-shelat 2026/2770 Towe). Round finished 2026-11-23T03:24Z.
green: `8cd1f660afc7`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-1db75a1d`.

No reds: `green` moves to `1db75a1dba5d`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.160 | 0.195 | 1.216 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 24.060 | 55.708 | 2.315 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.128 | 0.170 | 1.333 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 14.983 | 48.877 | 3.262 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.294 | 0.276 | 0.940 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 240.206 | 140.729 | 0.586 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-1db75a1d/flatness.log | - | - | - | - | host-execution, store-retained |
