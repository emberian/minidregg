# Reds (owned by the builder, rewritten whole each round)

Tip: `265f12f047b8` (builder: REDS.md for 7d0b33b067ba (2 red)). Round finished 2026-11-23T07:25Z.
green: `1db75a1dba5d`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-265f12f0`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| ratchets | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| rust-check | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| host | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| consent | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| rust | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| pack | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| umbrella-tree | did not run | - | no | build-loop | an earlier stage stopped the build |

Suspect commits since green (`git log 1db75a1dba5d..265f12f047b8`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `265f12f0` builder: REDS.md for 7d0b33b067ba (2 red) (owner: build-loop)
- `28068bd5` Add 134-byte Lean fast-path vectors without reseeding prior cases
- `150d16ce` Compare consent signing plans and stale-root refusals with prefix reads trapped
- `b0cc177f` Verify full NIST cSHAKE samples and both padding mutations across squeeze blocks
- `3a10bd28` Pin the Fn checkpoint fold to replay and require exact reserve write heights
- `ed810106` Inhabit the submit theorem with a verifying trailer and a forged-root counterexample
- `7d0b33b0` Preserve the Host operation checker boundary on byte-array frames
- `1648138a` builder: REDS.md for e3d290ee4bde (5 red) (owner: build-loop)
- `e3d290ee` Resolve dispatch and grant history against the refreshed light session (owner: apps-hermes)
- `8d8a6eca` Prove checkpoint authority agreement and trap prefix reads on cold sessions
- `720e33e8` builder: REDS.md for 9a7bbe40ccd1 (6 red) (owner: build-loop)
- `9a7bbe40` builder: REDS.md for 8b019bd95d5b (1 red) (owner: build-loop)
- `f5d8754d` Carry World admission through exact append, readback and receipt
- `8b019bd9` Use the QSAG Keccak permutation across the native cSHAKE root seam
- `3c04b71d` builder: REDS.md for 1db75a1dba5d (0 red) (owner: build-loop)
