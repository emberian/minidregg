# Reds (owned by the builder, rewritten whole each round)

Tip: `9a7bbe40ccd1` (builder: REDS.md for 8b019bd95d5b (1 red)). Round finished 2026-11-23T06:12Z.
green: `1db75a1dba5d`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-9a7bbe40`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| ratchets | rc=1 see /home/hbox/lanes/integ/logs/ratchets.log | - | no | suspects' owners | /home/hbox/lanes/integ/logs/ratchets.log |
| host | rc=1 ✖ [2278/2570] Building Kernel.NativeHostContext (28s) | - | no | suspects' owners | /home/hbox/lanes/integ/logs/host.log |
| consent | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| rust | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| pack | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| umbrella-tree | did not run | - | no | build-loop | an earlier stage stopped the build |

Suspect commits since green (`git log 1db75a1dba5d..9a7bbe40ccd1`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `9a7bbe40` builder: REDS.md for 8b019bd95d5b (1 red) (owner: build-loop)
- `f5d8754d` Carry World admission through exact append, readback and receipt
- `8b019bd9` Use the QSAG Keccak permutation across the native cSHAKE root seam
- `3c04b71d` builder: REDS.md for 1db75a1dba5d (0 red) (owner: build-loop)
