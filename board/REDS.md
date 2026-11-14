# Reds (owned by the builder, rewritten whole each round)

Tip: `31d01a02e22a` (FLEET-SURFACE: `maxCost` caps a fleet turn only). Round finished 2026-11-14T02:35Z.
green: `980d80c5dba8`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-31d01a02`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | no | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log 980d80c5dba8..31d01a02e22a`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `31d01a02` FLEET-SURFACE: `maxCost` caps a fleet turn only
- `bd7b6a01` fleet surface: operator duties, what confines a seat to publishing, and two stale cost notes
- `c492c4dd` builder: REDS.md for 3a98e24518a1 (6 red) (owner: build-loop)
- `3a98e245` grain-runtime: `quiescence preflight`, the checkpoint's first question answered from durable state (owner: apps-hermes, bytes-repr)
- `d15b824f` builder: REDS.md for 3ab616e02c8d (6 red) (owner: build-loop)
- `3ab616e0` grain-runtime: an entered resident prompt whose work reserve was closed as never sent receives its p (owner: apps-hermes, bytes-repr)
- `8f32e2ac` builder: REDS.md for a49760895ada (6 red) (owner: build-loop)
- `a4976089` grain-runtime unsent close: an earlier run's attempt is decided by this process's start proof (owner: apps-hermes, bytes-repr)
- `6b2d08f8` builder: REDS.md for 5caf465e9c0c (6 red) (owner: build-loop)
- `5caf465e` install-hermes: the consent render removes the box drop-in that carried --resident-dir (owner: apps-hermes)
- `9f02df8f` builder: REDS.md for 0a73bd93734b (6 red) (owner: build-loop)
- `0a73bd93` consent residents: a unit-held directory is never launched into; door sponsor and lobby relay use th (owner: apps-hermes)
- `0a4255b5` builder: REDS.md for 1e6a8e907ae2 (6 red) (owner: build-loop)
- `1e6a8e90` render test: the seed's house-rules link and note resolve `$HR_LAST` from the text, as seed.sh does (owner: apps-hermes)
- `649ffd18` grain-runtime: a reserve whose custody attempt never wrote its call closes as never sent (`reconcile (owner: apps-hermes, bytes-repr)
- `15db4406` builder: REDS.md for 3ce5cfe6716f (6 red) (owner: build-loop)
- `3ce5cfe6` spk-host STOP: a held absent-replan probe's active marker moves aside, so the next probe is not refu (owner: apps-hermes)
- `86686d86` builder: REDS.md for eb3aa769c844 (6 red) (owner: build-loop)
- `eb3aa769` apps: `apps unshare GRAIN MEMBER` withdraws a member's route; an undecided delete is never raced by  (owner: apps-hermes)
- `8b54c006` spk-host STOP: a sent completion Mini holds no receipt for is replaced once its signatures' window h (owner: apps-hermes)
- `bc2b3bd2` builder: REDS.md for a0ca6d00234a (6 red) (owner: build-loop)
- `a0ca6d00` WORLD-MIGRATION: the grain carry with a share made again, walked on demo-dry
- `92131ca3` builder: REDS.md for 0fd9d0d920c5 (6 red) (owner: build-loop)
- `0fd9d0d9` world-migrate grains: a share that bound its route but could not yet enroll is settled by its exact 
- `8af1c7f7` builder: REDS.md for b39706c4bc64 (6 red) (owner: build-loop)
- `b39706c4` world-migrate verify: a green verify releases each carried grain's staging copies
- `4a32bc17` builder: REDS.md for 842fa347267b (6 red) (owner: build-loop)
- `842fa347` world-migrate grains: a carry counts once it runs, a re-run resumes the claimed request, and an unca
- `e0c00047` builder: REDS.md for 4c305fbd9e31 (6 red) (owner: build-loop)
- `4c305fbd` spk-host install --import: the staged image is removed once the volume is made from it (owner: apps-hermes)
- `22973155` builder: REDS.md for 2ecb9ee18fbc (6 red) (owner: build-loop)
- `2ecb9ee1` op 2's 10 ms steps: the Store helper's anchor lock waits by doubling sleeps; held index rows in a pe
- `a2d8dbc0` builder: REDS.md for 78f9119ef1af (6 red) (owner: build-loop)
- `78f9119e` WORLD-MIGRATION: the grain row is walked (one grain on demo-dry, 2026-11-09)
- `599fa9db` builder: REDS.md for fb9577f5e099 (6 red) (owner: build-loop)
- `fb9577f5` spk-host broker: a carried grain's mounts take the import digest its create named (owner: apps-hermes)
- `47e648fa` builder: REDS.md for 09d3fb734ec7 (6 red) (owner: build-loop)
- `09d3fb73` consent admission: presence index as maps, the loaded directory held and stepped, refresh off the wh (owner: apps-hermes, bytes-repr)
- `8f9f3883` builder: REDS.md for cf73141aca4b (6 red) (owner: build-loop)
- `cf73141a` apps worker: an install that meets an instance its member already holds refuses the request, never t (owner: apps-hermes)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.153 | 0.223 | 1.457 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 30.002 | 69.572 | 2.319 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.110 | 0.174 | 1.573 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 13.770 | 61.464 | 4.464 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.436 | 0.450 | 1.032 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 166.282 | 179.538 | 1.080 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-31d01a02/flatness.log | - | - | - | - | host-execution, store-retained |
