# Reds (owned by the builder, rewritten whole each round)

Tip: `7d0b33b067ba` (Preserve the Host operation checker boundary on byte-array frames). Round finished 2026-11-23T07:25Z.
green: `1db75a1dba5d`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-7d0b33b0`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | no | build-loop | the umbrellas have not finished; this file is rewritten when they do |
| gate:j14-apps | j14-apps FAIL | not rerun | no | apps-hermes | rc=1; /ci/j-7d0b33/journey.log |

Suspect commits since green (`git log 1db75a1dba5d..7d0b33b067ba`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `7d0b33b0` Preserve the Host operation checker boundary on byte-array frames
- `1648138a` builder: REDS.md for e3d290ee4bde (5 red) (owner: build-loop)
- `e3d290ee` Resolve dispatch and grant history against the refreshed light session (owner: apps-hermes)
- `8d8a6eca` Prove checkpoint authority agreement and trap prefix reads on cold sessions
- `720e33e8` builder: REDS.md for 9a7bbe40ccd1 (6 red) (owner: build-loop)
- `9a7bbe40` builder: REDS.md for 8b019bd95d5b (1 red) (owner: build-loop)
- `f5d8754d` Carry World admission through exact append, readback and receipt
- `8b019bd9` Use the QSAG Keccak permutation across the native cSHAKE root seam
- `3c04b71d` builder: REDS.md for 1db75a1dba5d (0 red) (owner: build-loop)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.282 | 0.279 | 0.989 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 54.973 | 127.423 | 2.318 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.290 | 0.322 | 1.110 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 33.930 | 129.121 | 3.806 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.772 | 0.704 | 0.911 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 1255.692 | 1109.692 | 0.884 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-7d0b33b0/flatness.log | - | - | - | - | host-execution, store-retained |
