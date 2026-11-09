# Reds (owned by the builder, rewritten whole each round)

Tip: `a8fb1630ec91` (shell: `apps install APP --carry GRAIN` forwards --carry to the client). Round finished 2026-11-09T03:31Z.
green: `980d80c5dba8`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-a8fb1630`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| rust-check | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| host | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| consent | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| rust | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| pack | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| umbrella-tree | did not run | - | yes | build-loop | an earlier stage stopped the build |

Suspect commits since green (`git log 980d80c5dba8..a8fb1630ec91`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `a8fb1630` shell: `apps install APP --carry GRAIN` forwards --carry to the client (owner: apps-hermes)
- `2db20e66` builder: REDS.md for 3503d5d2e1a0 (6 red) (owner: build-loop)
- `3503d5d2` retained seal: checkpoint body held encoded, sealed by concatenation off the serving thread (PERF-CL (owner: read-path)
- `088e03cc` builder: REDS.md for 892f8f95f101 (6 red) (owner: build-loop)
- `892f8f95` world-migrate carries app grains: export at capture, install --carry, re-share, digest verify (owner: apps-hermes)
- `3574f404` builder: REDS.md for 2e48af863c8e (6 red) (owner: build-loop)
- `2e48af86` builder: REDS.md for 55d0721c587e (1 red) (owner: build-loop)
- `78307b6d` WORLD-MIGRATION: app grains and their data are a carry gap, written as a row
- `df78d18e` spk-host STOP: a committed claim arms its fence from Running; a dead drifted unit is fenceable (owner: apps-hermes)
- `55d0721c` builder: REDS.md for fd1f1b33a35f (1 red) (owner: build-loop)
- `5f6cc3ef` seal encodes its body once; the light open holds the whole index trie (PERF-CLIENT rows 37, 38) (owner: read-path)
- `fd1f1b33` builder: REDS.md for 980d80c5dba8 (0 red) (owner: build-loop)
- `760fdf33` held directory, held index rows, seal off the member's path (PERF-CLIENT rows 36, 37, 38) (owner: bytes-repr)
- `23f7df18` world-migrate verify: a seed account whose balance only grew lost nothing
- `4e7a094f` seed: house-rules' link and note go on its last line, whatever the text's length
