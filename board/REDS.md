# Reds (owned by the builder, rewritten whole each round)

Tip: `a30cb1fdfb9b` (summon: the program document is appended one line per action). Round finished 2026-11-05T18:48Z.
green: `6ba8fe37fa18`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-a30cb1fd`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| gate:j14-apps | j14-apps FAIL | yes, red again | yes | apps-hermes | rc=1; /ci/j-a30cb1/journey.log |

Suspect commits since green (`git log 6ba8fe37fa18..a30cb1fdfb9b`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `a30cb1fd` summon: the program document is appended one line per action (owner: apps-hermes)
- `aebb9867` builder: REDS.md for ebabcc294d24 (1 red) (owner: build-loop)
- `ebabcc29` j14-apps: the app-assistant program goes in as doc push and is verified line by line (owner: apps-hermes)
- `1a9a9bc0` builder: REDS.md for 38ac5b7f678f (1 red) (owner: build-loop)
- `38ac5b7f` run.sh upgrade: POSIX sh, no arrays (dash runs this file; the previous commit broke every world init
- `75ec22c9` builder: REDS.md for 54ae5b6b05a4 (2 red) (owner: build-loop)
- `54ae5b6b` run.sh upgrade: an empty retained-config list under set -u
- `f11c9722` run.sh upgrade: the operator's retained service config follows the pinned config too
- `dad657c2` builder: REDS.md for 240295848cbf (1 red) (owner: build-loop)
- `24029584` builder: take the world reaper at round start, not only after READY (owner: build-loop)
- `f774ce7b` builder: REDS.md for 158ffd6fb027 (6 red) (owner: build-loop)
- `aa1ba047` builder: REDS.md for 158ffd6fb027 (2 red) (owner: build-loop)
- `888cc9a3` builder: REDS.md for 158ffd6fb027 (2 red) (owner: build-loop)
- `158ffd6f` builder: --once resolves the id it is given to the full commit (owner: build-loop)
- `3b554e43` builder: REDS.md for fa361191b (6 red) (owner: build-loop)
- `75d53e42` fixtures: native runs re-recorded from candidate fa361191bfa9 (accepted stale, doc-write current)
- `fa361191` board: build-loop row: the hbox builder root rebuilt and warmed on 2026-11-05
- `cda6ea02` builder: REDS.md for 0852014c3222 (5 red) (owner: build-loop)
- `0852014c` mini-web-spawn: warm every live public body, and again every two minutes
- `86b7a942` builder: REDS.md for 1c2da07121c0 (6 red) (owner: build-loop)
- `1c2da071` gate: the system's flock comes first on PATH
- `2099fc9b` builder: REDS.md for e4796e5f773d (6 red) (owner: build-loop)
- `e4796e5f` main: merge the perf-client lane's original commits so the live candidate's source stays reachable
- `01bfa1db` gate harness: the resident fixture reads a multi-line append line by line; HARNESS overlays testing/
- `e794a3f7` door: fixes from the first strangers' attempts on demo-dry
- `329c0310` door: paid v2 flow fixes from the live mainnet signup (owner: apps-hermes)
- `cbfcebb9` wave3-converge: wire apps snapshot grammar/web alias, seat ballot-commit CLI, and seed.sh Section 9 (owner: apps-hermes)
- `073b8c1f` Strengthen op 151 receipt-opening and certifying-solver assurance
- `5d8dbb37` assurance,verify: add op 151 receipt-opening and certifying-solver bridges
- `4a276d9b` host/kernel: port lookupLight, FnEvidence, FnArchivePublisher to DurableServed (-5 ratchet callers) (owner: read-path)
- `08455edf` Port 7 full-loaded callers and 13 Host.Main sites to DurableServed
- `3aed8f74` wave3-hermes-apps-tick: fix bend_answer @file staging, law_check witness & compound clauses, bend vi (owner: apps-hermes)
- `6e7038b5` wave3(lane2): add Hermes objective-world tools, bend tick-all clock automation, and app grain WorldR (owner: apps-hermes)
- `1c09d26c` resource-client: fix SeatJson/ObjectiveBendDataWire wire compliance, Cert-F self-verification, and c (owner: apps-hermes)
- `fdb94167` wave3-surface-solvers: wire seat/objective dispatch, Cert-F clearing solver, Pred.hashEq ballot cust (owner: apps-hermes)
- `b331bb34` world-overhaul: infer DrexBatch clear market, wire POST /act/surface, and enforce cSHAKE256 hasheq_c (owner: apps-hermes)
- `702cd5ee` world,kernel,compiler,web: execute 3-phase preview museum overhaul (owner: apps-hermes, read-path)
- `bc7070cf` Fix Presburger writeOnce/pruning/cert parity and receipt witness retention (owner: apps-hermes)
- `1c4acd0f` resource-client: deterministic cSHAKE256 world-root receipt inclusion (op 151) & interactive Presbur (owner: apps-hermes)
- `01a60d40` grain-runtime/demo-seed: preserve compaction quiescence, operator audit boundary, split-tenancy cont (owner: apps-hermes)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.259 | 0.195 | 0.752 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | submit_wall_ms | 67.111 | 67.247 | 1.002 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.166 | 0.189 | 1.142 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 37.519 | 88.007 | 2.346 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.487 | 0.497 | 1.021 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 150.117 | 160.410 | 1.069 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-a30cb1fd/flatness.log | - | - | - | - | host-execution, store-retained |
