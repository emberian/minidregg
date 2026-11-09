# Reds (owned by the builder, rewritten whole each round)

Tip: `0a73bd93734b` (consent residents: a unit-held directory is never launched into; door sponsor and lobby re). Round finished 2026-11-09T09:00Z.
green: `980d80c5dba8`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-0a73bd93`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| rust-check | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| host | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| consent | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| rust | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| pack | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| umbrella-tree | did not run | - | yes | build-loop | an earlier stage stopped the build |

Suspect commits since green (`git log 980d80c5dba8..0a73bd93734b`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

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
- `2cf2942c` builder: REDS.md for 3649e4e58574 (6 red) (owner: build-loop)
- `3649e4e5` apps worker: an export answers only for the STOP that fenced it; a carry into an owner who holds the (owner: apps-hermes)
- `242b5823` builder: REDS.md for a8fb1630ec91 (6 red) (owner: build-loop)
- `a8fb1630` shell: `apps install APP --carry GRAIN` forwards --carry to the client (owner: apps-hermes)
- `2db20e66` builder: REDS.md for 3503d5d2e1a0 (6 red) (owner: build-loop)
- `3503d5d2` retained seal: checkpoint body held encoded, sealed by concatenation off the serving thread (PERF-CL (owner: read-path)
- `088e03cc` builder: REDS.md for 892f8f95f101 (6 red) (owner: build-loop)
- `892f8f95` world-migrate carries app grains: export at capture, install --carry, re-share, digest verify (owner: apps-hermes)
- `3574f404` builder: REDS.md for 2e48af863c8e (6 red) (owner: build-loop)
- `2e48af86` builder: REDS.md for 55d0721c587e (1 red) (owner: build-loop)
- `78307b6d` WORLD-MIGRATION: app grains and their data are a carry gap, written as a row
