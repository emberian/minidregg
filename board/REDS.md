# Reds (owned by the builder, rewritten whole each round)

Tip: `0852014c3222` (mini-web-spawn: warm every live public body, and again every two minutes). Round finished 2026-11-05T02:08Z.
green: `6ba8fe37fa18`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-0852014c`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| host | rc=1 see /home/hbox/lanes/integ/logs/host.log | - | no | suspects' owners | /home/hbox/lanes/integ/logs/host.log |
| consent | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| rust | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| pack | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| umbrella-tree | did not run | - | no | build-loop | an earlier stage stopped the build |

Suspect commits since green (`git log 6ba8fe37fa18..0852014c3222`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

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
- `5330c7d0` feat(wave1): integrate Host light opening, Assurance/Verify detwin, world/seed overhaul, and grain/c (owner: apps-hermes, read-path)
- `3f44281e` gate harness: the resident fixture reads a multi-line append line by line; HARNESS overlays testing/
- `8d11fca5` door: fixes from the first strangers' attempts on demo-dry
- `7896466b` door: paid v2 flow fixes from the live mainnet signup (owner: apps-hermes)
- `4db48b13` wave3-converge: wire apps snapshot grammar/web alias, seat ballot-commit CLI, and seed.sh Section 9 (owner: apps-hermes)
- `981556b5` Strengthen op 151 receipt-opening and certifying-solver assurance
- `75ccd797` assurance,verify: add op 151 receipt-opening and certifying-solver bridges
- `f6b7aff3` host/kernel: port lookupLight, FnEvidence, FnArchivePublisher to DurableServed (-5 ratchet callers) (owner: read-path)
- `03e7d5a5` Port 7 full-loaded callers and 13 Host.Main sites to DurableServed
- `532bb29c` wave3-hermes-apps-tick: fix bend_answer @file staging, law_check witness & compound clauses, bend vi (owner: apps-hermes)
- `faae71ba` wave3(lane2): add Hermes objective-world tools, bend tick-all clock automation, and app grain WorldR (owner: apps-hermes)
- `90224826` resource-client: fix SeatJson/ObjectiveBendDataWire wire compliance, Cert-F self-verification, and c (owner: apps-hermes)
