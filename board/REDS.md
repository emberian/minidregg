# Reds (owned by the builder, rewritten whole each round)

Tip: `eefe274475cd` (candidate: a role may be named through a link that resolves to its output). Round finished 2026-11-05T21:08Z.
green: `0264f390ecf7`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-eefe2744`.

No reds: `green` moves to `eefe274475cd`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.171 | 0.215 | 1.251 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 31.135 | 57.937 | 1.861 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.119 | 0.178 | 1.496 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 23.787 | 86.120 | 3.620 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.362 | 0.331 | 0.913 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 140.578 | 134.911 | 0.960 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-eefe2744/flatness.log | - | - | - | - | host-execution, store-retained |
