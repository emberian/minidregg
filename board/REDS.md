# Reds (owned by the builder, rewritten whole each round)

Tip: `a08f00d6e4fb` (builder: REDS.md for b7ce48271b8b (3 red)). Round finished 2026-11-01T11:15Z.
green: `93d8a0a0f144`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-a08f00d6`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | rc=1 see /home/hbox/lanes/integ/logs/umbrella-tree-a08f00d6e4fb.log | - | no | build-loop | /home/hbox/lanes/integ/logs/umbrella-tree-a08f00d6e4fb.log |
| umbrella | RED Kernel.ContentCommutingAppendProofs | - | yes | build-loop | /home/hbox/lanes/integ/logs/umbrella-tree-a08f00d6e4fb.log |
| umbrella | RED Kernel.EffectsRevival.ContentProofs | - | yes | build-loop | /home/hbox/lanes/integ/logs/umbrella-tree-a08f00d6e4fb.log |

Suspect commits since green (`git log 93d8a0a0f144..a08f00d6e4fb`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `a08f00d6` builder: REDS.md for b7ce48271b8b (3 red) (owner: build-loop)
- `9db861ab` mini-sdk: support exists check in qualification scenario_assertions
- `aceec575` spk-host, grain-runtime: drain empty socket.io ticks and verify imageFreePlanHex in payer v3 (owner: apps-hermes)
- `b7ce4827` apps: pin WBO replay baseline in rectangle.write and match Hummingbird hits stream (owner: apps-hermes)
- `6acedf22` host, perf: O(1) StoreCodec salted root aux, relativeTo directory decode, and schedstat flatness CPU (owner: read-path)
- `4903669a` builder: REDS.md for 93d8a0a0f144 (0 red) (owner: build-loop)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | FAIL | submit_cpu_ms | 0.143 | 0.267 | 1.864 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 33.994 | 69.645 | 2.049 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_cpu_ms | 0.101 | 0.221 | 2.179 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 26.257 | 76.865 | 2.927 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.368 | 0.444 | 1.208 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 271.131 | 337.041 | 1.243 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-a08f00d6/flatness.log | - | - | - | - | host-execution, store-retained |
