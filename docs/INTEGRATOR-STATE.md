# Integrator state

Present-state record of the integration lane, rewritten whole when its shape changes. A successor reads this, then
`hbox:/home/hbox/lanes/integ/COMMANDS.log` (every build stage, gate verdict, sweep, world teardown and process stop, one
line each). History is in this file's git history.

The integrator is agent **aba0beaa578594e92**, distilled 10-31 06:00 from aeb671706eb3f70d7 (retired; the cv
retired-agent hook names the live integrator to anyone who messages the old id). Lanes send shas, READY, reds and handoffs to the
integrator; the integrator merges onto `integration/staging`, cuts batch candidates on hbox, gates them, moves main to
gated candidates and names candidates to infra and the explorer.

## Now (2026-10-31 10:30 EDT)

- **ember (10-31 09:10, via root): no rehearsal cut until she says.** Make the system as good as it can be: keep batching,
  gate once per batch, keep the newest green candidate as the fallback. Priorities: repair Hermes (batch 5's j14
  "Hermes sent no reply to the ask: refused" is app-reds' top item), efficiency everywhere, every red fixed, never worked
  around. Shared consent resident under split tenancy APPROVED (perf-client). Egress gateway and Oracle7 integration HELD.
  No new build box: hbox and forge only.
- **main = 83e926874** = gated batch 4 b9450147f + main 7978ddfdd. **Batch 4 is the green fallback** (hbox tour 73/73,
  enrol, composed; forge composed c-b945-d1 all phases; j14 with deploy hotpatch 9fdef19bd; umbrellas green).
- **Batch 5 1c151fce4: gate15 FAIL** on j14-apps: "Hermes sent no reply to the ask: refused" (also on overlay
  1c151fce4-resid -hp1). Cause narrowed by app-reds: the controller's final-delivery mini_say is paid (op g98) but never
  submitted (lookup `not-submitted`), and the write error was dropped; c88b88755 (batch 7) now surfaces it as writeError.
  Forge composed c-1c15-d1 PASSES every phase (residents, restart included). Umbrella-tree on batch 5: rc=0, 0 reds
  (TokenCensus fixed); its fixture re-record eb5cf8f8a is merged (staging 72ad281c5).
- **Batch 6 74e1cfa10: READY 09:31** (host 2,165 s, of which 1,471 s idle behind batch 5's umbrella seats: fixed by
  iter-speed 0f67c94b7, batch 7). gate15 (PID file $I/gate-74e1.pid) so far: enrol PASS, tour 73/73, hbox composed rooms/
  churn/documents/apps/connector PASS, residents UNKNOWN on hbox (forge decides), j14-apps FAIL with the same Hermes
  final-say refusal as batch 5. Umbrella-tree running in umbrella-src. Exorcist measured it against batch 5: signed read
  wall 42 -> 32 ms, operator CPU 27.8 -> 15.0 ms. perf-apps: EtherCalc create-to-first-page 53 s (256 s on 10-29), warm GET
  340 ms, of which ~170 ms is the SUBMIT Host turn (hot-path's).
- **CLOSED: GET read-path contract: astra reviewed, ember ruled (c)+(d), hot-path owns.** Never re-run astra on it or
  report it again. (Ruling: prepaid reserved credit per liable payer; declared per-route eligibility. Hot-path
  a6c4a1532687a4fdb, statement-first, after group commit; not a batch item until keystones and witnesses exist.)
- **Batch 6 gate15 verdict FAIL (10:00)**: enrol, tour 73/73, hbox composed rooms/churn/documents/apps/connector PASS;
  residents UNKNOWN (forge decides); j14-apps FAIL with batch 5's Hermes final-say refusal; flatness-submit FAIL,
  flatness-get PASS. Its umbrella-tree is running in umbrella-src (PID file $I/umbrella-src.pid).
- **Batch 7 acc7cfa03: host stage rc=0 at 10:25 (1,666 s, beside batch 6's umbrella: the seat-weights fix worked;
  batch 6 took 2,165 s)**; consent/rust/pack running, PID file $I/build-b7.pid. Also carries perf-client a1c70ef29 (consent provider reads the Store once per command; birth
  authority leg at the held authState; attempt index; audit sound, frame 233 now means "re-check owed"). Earlier contents: resident final writeError c88b88755, demo-reds 58c17b1de, perf-client f95edc7bf +
  b34173dad (candidate ssh wrapper) + 394039fb1 (one shared codec Host per box under split tenancy), apps-e2e 78a20cb56,
  perf-apps b2 05c2b208b, hot-path a55855f18, perf-client 5415aecf7, iter-speed Mathlib import trim ee7a25ca7 (Host.Main 3,930 -> 2,895 modules; Pratt certificate for mersenne127P_prime; audit sound, pins only shrank), app-reds c0a49c8d7 (an argument object keyed `path` is an argument: Davros qualify's declaration-invalid), iter-speed seat weights 0f67c94b7, perf-apps docs a7511c500; app-reds ecf4b917d merged as superseded by staging's 6cae27559 (staging ddc2e8863).
- **Staging 6b64e533e (batch 8 so far)**: iter-speed tower split 0eab28db7 (audit sound: 12 decls moved verbatim, pins only shrank), exorcist 47b7cb2e1 + c763e3ead (policy loads one encode per record; signed read loads the law graph once; audit sound; whole-tree build owed = batch 8), perf-client 783b460cb (MINI_TRACE consent/codec frames), perf-client b6 (frame 233 = re-check owed in the protocol registry; per-deployment ID index, settings and workspace read once per file identity; `doc new` statx 1,063 -> 505).
- **FORMAT batch (later, one genesis, after iter-speed's seam 1)**: hot-path row 11 + Book entries migration +
  private-cells FORMAT (a) (eventHistory, authority to the trie root, mask []) + KeptCell Aux cache + fixture re-record.
- Explorer on batch 5 vs 4: fsyncs 0; 128-ref credit 6.9 s -> 0.35 s; idle catch-up 61 s -> 0.36 s; first read after
  restart 19 s -> 0.24 s; say 0.55 s warm; doc-append grows with history (1.8 s at 13 entries, 6.2 s at 303: hot-path).
- Forge demo (infra): grain world green through the host custodian; infra holds its rebuild until batch-5's forge composed
  ends and waits for host load < 2 before starting the Hermes controller. Wedged lobby state saved at
  dregg-forge:/root/wedges/lobby-wedge-b4.tar for demo-reds.
- hbox: / 69 GB free (09:18, after the explorer removed 16 GB of its own /ci scratch).

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
