# Reds (owned by the builder, rewritten whole each round)

Tip: `e3d290ee4bde` (Resolve dispatch and grant history against the refreshed light session). Round finished 2026-11-23T06:44Z.
green: `1db75a1dba5d`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-e3d290ee`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| host | rc=1 see /home/hbox/lanes/integ/logs/host.log | - | no | suspects' owners | /home/hbox/lanes/integ/logs/host.log |
| consent | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| rust | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| pack | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| umbrella-tree | did not run | - | yes | build-loop | an earlier stage stopped the build |

Suspect commits since green (`git log 1db75a1dba5d..e3d290ee4bde`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `e3d290ee` Resolve dispatch and grant history against the refreshed light session (owner: apps-hermes)
- `8d8a6eca` Prove checkpoint authority agreement and trap prefix reads on cold sessions
- `720e33e8` builder: REDS.md for 9a7bbe40ccd1 (6 red) (owner: build-loop)
- `9a7bbe40` builder: REDS.md for 8b019bd95d5b (1 red) (owner: build-loop)
- `f5d8754d` Carry World admission through exact append, readback and receipt
- `8b019bd9` Use the QSAG Keccak permutation across the native cSHAKE root seam
- `3c04b71d` builder: REDS.md for 1db75a1dba5d (0 red) (owner: build-loop)
