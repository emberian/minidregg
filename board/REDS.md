# Reds (owned by the builder, rewritten whole each round)

Tip: `b7ce48271b8b` (apps: pin WBO replay baseline in rectangle.write and match Hummingbird hits stream). Round finished 2026-11-01T10:59Z.
green: `93d8a0a0f144`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-b7ce4827`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | rc=1 see /home/hbox/lanes/integ/logs/umbrella-tree-b7ce48271b8b.log | - | no | build-loop | /home/hbox/lanes/integ/logs/umbrella-tree-b7ce48271b8b.log |
| umbrella | RED Kernel.ContentCommutingAppendProofs | - | no | build-loop | /home/hbox/lanes/integ/logs/umbrella-tree-b7ce48271b8b.log |
| umbrella | RED Kernel.EffectsRevival.ContentProofs | - | no | build-loop | /home/hbox/lanes/integ/logs/umbrella-tree-b7ce48271b8b.log |

Suspect commits since green (`git log 93d8a0a0f144..b7ce48271b8b`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `b7ce4827` apps: pin WBO replay baseline in rectangle.write and match Hummingbird hits stream (owner: apps-hermes)
- `6acedf22` host, perf: O(1) StoreCodec salted root aux, relativeTo directory decode, and schedstat flatness CPU (owner: read-path)
- `4903669a` builder: REDS.md for 93d8a0a0f144 (0 red) (owner: build-loop)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.184 | 0.204 | 1.109 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 33.701 | 71.607 | 2.125 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.156 | 0.217 | 1.387 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 26.352 | 124.073 | 4.708 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.279 | 0.298 | 1.068 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 237.028 | 263.505 | 1.112 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-b7ce4827/flatness.log | - | - | - | - | host-execution, store-retained |
