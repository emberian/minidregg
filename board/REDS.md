# Reds (owned by the builder, rewritten whole each round)

Tip: `0264f390ecf7` (j14-apps, resident fixture: a blank document line renders as its bare number). Round finished 2026-11-05T19:50Z.
green: `6ba8fe37fa18`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-0264f390`.

No reds: `green` moves to `0264f390ecf7`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.223 | 0.199 | 0.890 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | submit_wall_ms | 61.878 | 63.887 | 1.032 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.144 | 0.167 | 1.160 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 37.195 | 82.766 | 2.225 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.542 | 0.525 | 0.970 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 146.937 | 158.714 | 1.080 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-0264f390/flatness.log | - | - | - | - | host-execution, store-retained |
