# Reds (owned by the builder, rewritten whole each round)

Tip: `6c0612f2f3e9` (gate,Kernel,Host,resource-client: isolate composed units, allow non-authority suffix in re). Round finished 2026-11-01T06:35Z.
green: `83e926874e38`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-6c0612f2`.

No reds: `green` moves to `6c0612f2f3e9`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | FAIL | submit_cpu_ms | 31.000 | 56.500 | 1.823 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | submit_wall_ms | 55.189 | 72.245 | 1.309 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_cpu_ms | 7.000 | 16.500 | 2.357 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 30.783 | 90.122 | 2.928 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 55.000 | 53.500 | 0.973 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 146.949 | 156.918 | 1.068 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-6c0612f2/flatness.log | - | - | - | - | host-execution, store-retained |
