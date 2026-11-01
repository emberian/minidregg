# Reds (owned by the builder, rewritten whole each round)

Tip: `dbb0dc30de44` (perf(host): pass verified.opened.durable in objectAudienceLoaded/RosterLoaded). Round finished 2026-11-01T07:16Z.
green: `6c0612f2f3e9`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-dbb0dc30`.

No reds: `green` moves to `dbb0dc30de44`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | FAIL | submit_cpu_ms | 16.000 | 49.500 | 3.094 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 29.251 | 61.123 | 2.090 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_cpu_ms | 7.000 | 13.500 | 1.929 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 24.569 | 80.130 | 3.261 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 45.000 | 58.500 | 1.300 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 213.715 | 249.877 | 1.169 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-dbb0dc30/flatness.log | - | - | - | - | host-execution, store-retained |
