# Reds (owned by the builder, rewritten whole each round)

Tip: `e8e3bb8c83cc` (bytes-repr: a ratchet on List UInt8 in the deployed executables). Round finished 2026-11-08T20:46Z.
green: `7f80be31654a`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-e8e3bb8c`.

No reds: `green` moves to `e8e3bb8c83cc`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.210 | 0.204 | 0.971 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 42.286 | 70.041 | 1.656 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.152 | 0.187 | 1.230 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 31.890 | 78.959 | 2.476 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.350 | 0.363 | 1.035 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 372.896 | 148.789 | 0.399 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-e8e3bb8c/flatness.log | - | - | - | - | host-execution, store-retained |
