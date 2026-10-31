# Integrator state

Present-state record of the integration lane, rewritten whole when its shape changes. A successor reads this, then
`hbox:/home/hbox/lanes/integ/COMMANDS.log` (every build stage, gate verdict, sweep, world teardown and process stop, one
line each). History is in this file's git history.

The integrator is agent **aba0beaa578594e92**, distilled 10-31 06:00 from aeb671706eb3f70d7 (retired; the cv
retired-agent hook names the live integrator to anyone who messages the old id). Lanes send shas, READY, reds and handoffs to the
integrator; the integrator merges onto `integration/staging`, cuts batch candidates on hbox, gates them, moves main to
gated candidates and names candidates to infra and the explorer.

## Re-orienting (root, 10-31 10:50)

After any context clear, the ONLY sources of what is pending are this file and COMMANDS.log. Never send a report because
a scratchpad or task-output file exists. Send only what "Reports owed" below lists, and move it to "Reports sent" in the
same step. Closed items are never re-reported.

## Now (2026-10-31 10:52 EDT)

- **ember (10-31 09:10, via root): no rehearsal cut until she says.** Keep batching, gate once per batch, keep the newest
  green candidate as the fallback. Priorities: repair Hermes, efficiency everywhere, every red fixed, never worked around.
- **main = 83e926874** = gated batch 4 b9450147f + main 7978ddfdd. **Batch 4 is the green fallback.**
- Batch 5 1c151fce4 and batch 6 74e1cfa10: gate15 FAIL on j14 (Hermes final-say refused; app-reds narrowing, c88b88755 in
  batch 7 surfaces the write error). Forge composed on batch 5 passed every phase.
- **Batch 7 acc7cfa03: READY 10:29** (host 1,666 s beside batch 6's umbrella; seat-weights fix worked). gate15 (PID file
  $I/gate-acc7.pid): enrol PASS, tour 73/73. j14-apps FAIL: mini cannot create owner-workspace/attempt-index/by-intent/
  (ENOENT; perf-client aa24acaf8). Composed rerun -c2 ($I/gate-acc7-c2.pid): rooms/churn/documents/restart pass, the rest
  blocked by "metered workroom not ready" (hot-path: management subject 8 lacks the sponsor-born task's grant;
  suspected downstream of the ENOENT; if -hp1 still refuses, route to the apps-worker/workroom owner). Fix b940b3f50 (perf-client) merged on staging; mini rebuilt and
  overlaid as **candidates/acc7cfa03-attidx** (both copies of mini replaced; hotpatch-candidate.sh fixed to replace every
  copy by digest). Queued: gate15 PHASES="j14 composed" SUF=-hp1 on it, launching when both acc7 gates exit
  ($I/hp-attidx.pid waits; then $I/gate-acc7-attidx.pid). Forge composed of batch 7 queued by infra.
- **Staging dc0b7c935 (batch 8 so far)**: iter-speed 7800d3199 + 697db7664 (native-loop: a lane's Lean change reaches a
  native candidate in ~8 min), tower split 0eab28db7, exorcist 47b7cb2e1 + c763e3ead, perf-client 783b460cb + b6 +
  b940b3f50, retained-mode 675a80745 (Theory/Retained.lean, statement + witnesses; audit round owed) + 1d4ff4efb (docs).
  Batch 8 is the whole-tree build these owe.
- **Next shared-interface change: retained-mode L0** (Theory.Store's Store becomes a persistent extensional tree map,
  ~66 files, WorldCompact deleted): its own cut with one whole-tree build; FORMAT (private cells (a), hot-path row 11,
  Book entries) rebases onto it.
- **CLOSED: GET read-path contract.** Astra reviewed, ember ruled; hot-path a6c4a1532687a4fdb owns it statement-first. Never
  re-run or re-report.
- hbox: / 59 GB free (10:42).

## Reports owed

- Batch 7 gate verdict and the -hp1 hotpatch result (to root, infra, explorer, perf-apps), when they land.

## Reports sent (do not resend)

- 10-31: GET-contract astra review (many times, by mistake; CLOSED). Batch 7 READY named to infra, explorer, perf-apps.

## Lanes (route only to the newest id; distilled lanes' old ids are retired)

| lane | agent | owns now |
|---|---|---|
| hot-path | a6c4a1532687a4fdb (ac53c05fe796e4294 retired) | law-17 perf queue: flatness, `story new`, row 11, Book entries migration (FORMAT) |
| app-reds | ad85d40779880420c | apps installs on forge/hbox, op66-plan, Hummingbird/WBO/Scrumblr live qualification, Davros control run, E3/E4, G2 decider-side type, controller boot ordering, Hermes worker root interpreter |
| private cells | a8da2b953507b402b | FORMAT (a); then the compiler-emitted ZK selective opening; decode pin to CanonicalCellRegistry.custodyDecode with (b) |
| iteration speed | a6c58cb72b0764dbb | seam 1 (codec tags / Store epoch, lands before or with FORMAT), lane pool /home/hbox/pool, lane-tree, hot-swap overlay tool |
| explorer | a3e5d6dbcd68e616c | multi-member exploration of each READY candidate; docs/EXPLORER-FINDINGS.md on lane/explorer |
| infra | aa72653a8ce442178 | forge demo container, forge composed (judges residents/restart), dregg-infra (ship.sh, world-down finding) |
| exorcist | a76808829fc8e4836 (a6ad40ce192354deb, a31f4ba5028d24a92 retired) | no fsync anywhere (lane/exorcism); filtered set `nextest -E 'test(durable) \| test(anchor) \| test(signing_wire) \| test(attempt_state) \| test(receipt_continuity)'` |
| perf-apps | a25df305cfd551d8b | apps install, grain HTTP path, typed-tool path (perf) |
| perf-client | a778bbda6509944a5 (a8d456c6e773efbb8 retired) | client, consent provider per-record cost, web page loads, idle cold start (perf) |
| retained-mode | a13f0c9ab4513b2d7 | incremental-computation architecture: a Lean incremental node with one generic "maintained = recomputed" theorem, the Host's derived structures as maintained nodes persisted in checkpoints, emission from Effects/, a lint for whole-state functions on per-request paths, one hot path migrated end to end |
| demo-reds (sub-Opus of the integrator) | a64c387f3e638aa63 | bend/web/door/Hermes product reds as routed |
| statement auditor (sub-Opus of the integrator) | a4d9a6f4cba4855ca | read-only adversarial audit of each lane's top-level statements, one round per merged sha |

Every Lean-statement sha gets an audit round from a4d9a6f4cba4855ca before it rides a cut; verdicts go back to the lane.

## Rulings in force

- **/tank** (root, 10-31 08:30, correcting the earlier reading): ember's "don't use /tank" means don't MOVE data there to
  free disk. Existing small /tank files stay: /tank/lanes/world-up.lock (the ONE world-up lock every lane, gate and
  scripts/spk-platform flocks; never a second path), /tank/lanes/vars-backing.img, /tank/mini-ingest. Gates lock
  /tank/lanes/world-up.lock again (reverted 08:30); playwright runs from $I/pw (local copy, fine). Free disk only by
  removing old trash (retired trees after their checkpoint, finished /ci scratch, superseded candidates and gate roots).
- **Minimal checks** (ember, 10-31, after the gates went green): per iteration only the narrowest check that shows the
  change worked (lane-check of changed files plus one targeted measurement or row); full gates (gate13/15, forge composed,
  umbrellas) once per batch cut; cuts spaced out to accumulate perf work; hotpatched measurement worlds are the inner loop;
  freed hbox time goes to perf builds and measurements. Batch 4 stays the green fallback and rehearsal candidate.
- **Retained mode** (root, 10-31): every lane brief that touches state carries the line "a derived value is maintained,
  never recomputed; writing f(state) on a hot path means you owe its update rule." retained-mode a13f0c9ab4513b2d7 owns the
  architecture.
- **Import boundary**: Effects is the generator Kernel and Compiler consume; Effects sits below Kernel/Compiler, may import
  Theory and Lean core, never Kernel/Compiler/Host. Landed (b7bf3a8b2; table green, no cycle).
- **Consent**: no validity proofs; we trust the storage device; providers resume from a sealed snapshot; anchors survive
  ships (landed: CONSENT-STORE 54bd71d53).
- **Private cells FORMAT scope**: (a) now, (b) with the ZK opening; never trade hiding for speed.
- **Hotpatch, don't cut**: script/deploy fixes go onto a gated candidate via HARNESS and keep its verdicts; Rust/Lean
  needs the next cut, but Rust fixes may be overlaid onto a candidate copy to test between cuts. No single-fix cuts.
- **Stale leftovers**: our own fleet's leftover processes may be stopped by exact PID after reading each command line
  (root, relaying ember, 10-30); everything else needs a PID file or ember's word.
- Flatness (law 17) is reported, never gating. No rehearsal ships until ember says; then only a fully green gate with no
  demo-path product red.
- Split tenancy: one shared consent resident and one shared codec Host per box are approved. Egress gateway and Oracle7: held.
- No new build box (ember): hbox and forge only.

## Build, gate and sweep (hbox, as user hbox, /home/hbox/lanes/integ = $I)

- `integ-build6.sh SHA`: build5 + waits for the previous umbrella-tree's lock. Stages: rust-check, host, consent, rust,
  pack -> `READY $I/candidates/<sha>`; then releases build.lock, runs `src/scripts/pipeline/umbrella-tree SHA` in
  $I/umbrella-src (SEATS 4, MEM 32G) and the rerecord stage from umbrella-src (re-records stale Native fixtures by
  elaboration; pushes fixture-regen/<sha12>, which the integrator merges). Launch:
  `nohup setsid ./integ-build6.sh SHA > build.out 2>&1 & echo $! > build.pid` (SEATS=12 MEM=56G). Never launch while
  build.pid is alive.
- `gate13.sh SHA`: tour + composed + enrol + j14-apps + flatness, then sweep. `gate14.sh NAME` (overlay/hotpatch reruns):
  HARNESS=<staging sha> overlays scripts/ and deploy/spk-host, SUF=-hpN, PHASES subset of "tour composed enrol j14",
  KEEP_WORLD=1 optional. Env: EDGE_REV=69c17a3. hbox composed cannot judge residents/restart: forge composed does.
- Overlays: iter-speed's `deploy/candidate/lane-build.sh rust --crate X` then
  `lane-build.sh overlay $I/candidates/<BASE> $I/candidates/<NAME> ROLE...` (overlay a crate's whole bin set; dir named by
  a 12-hex `.overlay.id`). hotpatch-candidate.sh is the superseded stopgap.
- `sweep.sh [--dry]`: removes gate roots and /ci worlds for candidates two or more behind, candidates beyond the newest 3
  READY; skips $I/keep (be4ef7510, cdb399b47, eca98bde7, 35737eac4, a4cb65af3, overlays), non-40-hex names, anything with
  provenance `.overlay`, anything a live process or /ci world names. Runs at the end of every gate13.
- Hard-link hazard: never `cp -al` a .lake another tree builds in (lake writes .trace/setup.json in place). Lanes build in
  the lane pool (/home/hbox/pool, lane-tree; LANE_POOL_NO_WARM=1 while integ builds; pool.env sets LAKE_ARTIFACT_CACHE=false).
- Mac landing worktree /Users/ember/dev/minidregg-lanes/integration-r2 (branch integ/batch-435; staging is pushed from it).

## Candidates

| candidate | state |
|---|---|
| be4ef7510 | GATE GREEN (rehearsal 3 original ship) |
| a4cb65af3 | GATE GREEN (batch 3); main's base; fallback ship |
| eca98bde7-resvar2(-zai) | overlays of batch 2 with the resident /var fix (and Z.AI); forge demo build |
| b9450147f | GATE GREEN (batch 4, with deploy hotpatch 9fdef19bd): rehearsal-3 candidate; main's base |
| 1c151fce4 | READY (batch 5); gate15 FAIL: j14 `refused` ask, residents for forge |
| 74e1cfa10 | READY (batch 6); gate15 FAIL: j14 Hermes final-say refusal, residents for forge |
| acc7cfa03 | READY (batch 7); gate15: tour 73/73, enrol PASS; j14 FAIL (attempt-index ENOENT) |
| acc7cfa03-attidx | overlay: batch 7 + mini from b940b3f50; gate15 -hp1 j14+composed queued |
| 1c151fce4-resid | overlay: batch 5 + spk-host crate from 40efdcff9 (resource id any non-zero u64); gate15 -hp1: j14 same `refused` red |

## Open reds and owners

- TokenCensus ConsentAnchor L1 witness: fixed b70a547c8 (batch 4), confirm in batch 4's umbrella.
- Flatness submit/get (law 17): hot-path; content-cell flatness stays a published red until private-cells (b).
- Etherpad install on forge: 0aa00c3e0 (batch 4); recheck on a fresh world. op66-plan: app-reds.
- Hermes ask on forge: fenced controller fixed cb3bc4f85 (batch 4); Z.AI path 5f32da72d (batch 4).
- world-down.sh leaves the world dir and client residents behind: infra (dregg-infra).
- Every tour JWF-dry `mini web --body` orphan: fixed by demo-reds' lifeline 4928d9a77 (in batch 3); confirm after gates.
- Deregistration's lease freshness ranges over every lease (index leases by account if frequent): hot-path.

## Rules

Every lane brief that touches state carries this line (root, 10-31): "a derived value is maintained, never recomputed; writing f(state) on a hot path means you owe its update rule."

Named-file commits with `git commit -F <file>`; never `git add -A` or `git stash`; filtered tests only; every detached
job has a PID file and is stopped only by it; lake/git on hbox as hbox, never root; swarm-build caps summing under
~100 GB; one sequential job per build tree; never search from / or ~; disk pressure = stop and tell ember.
