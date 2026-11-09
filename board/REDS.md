# Reds (owned by the builder, rewritten whole each round)

Tip: `2e48af863c8e` (builder: REDS.md for 55d0721c587e (1 red)). Round finished 2026-11-09T02:44Z.
green: `980d80c5dba8`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-2e48af86`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| rust-check | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| host | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| consent | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| rust | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| pack | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| umbrella-tree | did not run | - | no | build-loop | an earlier stage stopped the build |

Suspect commits since green (`git log 980d80c5dba8..2e48af863c8e`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `2e48af86` builder: REDS.md for 55d0721c587e (1 red) (owner: build-loop)
- `78307b6d` WORLD-MIGRATION: app grains and their data are a carry gap, written as a row
- `df78d18e` spk-host STOP: a committed claim arms its fence from Running; a dead drifted unit is fenceable (owner: apps-hermes)
- `55d0721c` builder: REDS.md for fd1f1b33a35f (1 red) (owner: build-loop)
- `5f6cc3ef` seal encodes its body once; the light open holds the whole index trie (PERF-CLIENT rows 37, 38) (owner: read-path)
- `fd1f1b33` builder: REDS.md for 980d80c5dba8 (0 red) (owner: build-loop)
- `760fdf33` held directory, held index rows, seal off the member's path (PERF-CLIENT rows 36, 37, 38) (owner: bytes-repr)
- `23f7df18` world-migrate verify: a seed account whose balance only grew lost nothing
- `4e7a094f` seed: house-rules' link and note go on its last line, whatever the text's length
