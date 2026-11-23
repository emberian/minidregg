# Reds (owned by the builder, rewritten whole each round)

Tip: `cb2a3279f878` (Serve Fn frontier and provider continuity from native admission checkpoints). Round finished 2026-11-23T09:17Z.
green: `453aba535878`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-cb2a3279`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| ratchets | rc=1 see /home/hbox/lanes/integ/logs/ratchets.log | - | no | suspects' owners | /home/hbox/lanes/integ/logs/ratchets.log |
| consent | rc=1 lane-build: host roles built at cb2a3279f878; compiled inputs identical at cb2a3279f878 | - | no | suspects' owners | /home/hbox/lanes/integ/logs/consent.log |
| rust | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| pack | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| umbrella-tree | did not run | - | no | build-loop | an earlier stage stopped the build |

Suspect commits since green (`git log 453aba535878..cb2a3279f878`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `cb2a3279` Serve Fn frontier and provider continuity from native admission checkpoints (owner: apps-hermes, bytes-repr)
- `7bc4d1a0` builder: REDS.md for 453aba535878 (0 red) (owner: build-loop)
