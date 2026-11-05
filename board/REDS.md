# Reds (owned by the builder, rewritten whole each round)

Tip: `54ae5b6b05a4` (run.sh upgrade: an empty retained-config list under set -u). Round finished 2026-11-05T17:45Z.
green: `6ba8fe37fa18`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-54ae5b6b`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| gate:j14-apps | j14-apps FAIL | yes, red again | yes | apps-hermes | rc=1; /ci/j-54ae5b/journey.log |
| gate:composed:composed | composed composed fail | yes, red again | no | infra, member-side | scratch world: jworld FAIL init /ci-composed/c-54ae5b/w/root/var/lib/mini/candidate/current/run.sh: 153: Syntax error: "(" unexpected (expecting "}") |

Suspect commits since green (`git log 6ba8fe37fa18..54ae5b6b05a4`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

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
- `76d0996a` fix(grain-runtime): prefer confirmed settlement rows in prompt_outcome::audit_chain and auto-run ret (owner: apps-hermes)
- `98363a39` fix(demo-seed): check exact ref files in has_ref and fast-path have() via outcome.json
- `0a398a61` fix(hermes): raise demo provider maxInputTokens to 131072 matching j14 (owner: apps-hermes)
- `548bd808` fix(grain-runtime): clear hermes_session.pending_prompt and refresh fingerprint on reconcile_prompt_ (owner: apps-hermes)
- `64ba07cc` fix(grain-runtime): clear prompt_witness on parent hold reconcile and allow hermes_pending_prompt in (owner: apps-hermes)
- `8568da8b` fix(grain-runtime): class-settle malformed 200 provider responses at hold during audited reconciliat (owner: apps-hermes)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.396 | 0.291 | 0.733 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | submit_wall_ms | 69.993 | 70.881 | 1.013 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.205 | 0.233 | 1.133 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 42.071 | 88.975 | 2.115 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.497 | 0.382 | 0.769 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 152.740 | 159.991 | 1.047 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-54ae5b6b/flatness.log | - | - | - | - | host-execution, store-retained |
