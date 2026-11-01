# Reds (owned by the builder, rewritten whole each round)

Tip: `6ba8fe37fa18` (fix(demo-seed,apps,spk-host,hermes,door): rehearsal seed, SPK grain route/install, and doo). Round finished 2026-11-01T17:05Z.
green: `d6f873639367`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-6ba8fe37`.

No reds: `green` moves to `6ba8fe37fa18`.

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.253 | 0.242 | 0.956 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | submit_wall_ms | 64.778 | 69.044 | 1.066 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.147 | 0.185 | 1.262 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 35.526 | 80.369 | 2.262 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.534 | 0.534 | 1.000 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 156.069 | 252.017 | 1.615 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-6ba8fe37/flatness.log | - | - | - | - | host-execution, store-retained |
