# Integrator state

Present-state record of the integration lane, rewritten whole when its shape changes. A successor reads this, then
`hbox:/home/hbox/lanes/integ/COMMANDS.log` (every build stage, gate verdict, sweep, world teardown and process stop, one
line each). History is in this file's git history.

The integrator is agent **aba0beaa578594e92**, distilled 10-31 06:00 from aeb671706eb3f70d7 (retired; the cv
retired-agent hook names the live integrator to anyone who messages the old id). Lanes send shas, READY, reds and handoffs to the
integrator; the integrator merges onto `integration/staging`, cuts batch candidates on hbox, gates them, moves main to
gated candidates and names candidates to infra and the explorer.

## Now (2026-10-31 08:35 EDT)

- **main = 83e926874** = gated batch 4 b9450147f merged with main 7978ddfdd.
- **Batch 4 b9450147f: GATE GREEN, the rehearsal-3 candidate.** hbox tour 73/73, enrol, composed; forge composed c-b945-d1
  all phases; j14-apps PASS with the deploy-script hotpatch HARNESS=9fdef19bd (bwrap ACL 11a4f4ac6: the controller uid gets
  its own execute entry on /usr/local/libexec/mini-grain-bwrap, app-range entries claimed per world; grant_acl stops at the
  world root c76dbe0c7; gate15 = gate14 + j14 socket parent 711; /ci is 711). Umbrellas all green; fixtures 5c00cc4f3
  merged. Flatness: submit_cpu 106 -> 380 (3.6x), propose_cpu 4.05x; walls and get PASS.
- **Batch 5 1c151fce4: READY 07:52** (host stage 1,005 s, the lake-threads fix's first measured cut; consent 150 s, rust
  191 s). Contents: exorcism 4f7972a62 (no fsync anywhere), module-cost, hot-path authority snapshot 4fb1a0e17, app-reds
  route/teardown/ACL, batch 4 fixtures. **gate15 running** (PID 2738976 in gate-1c15.pid; started 07:53 under the home
  lock path, so its remaining world-ups are not serialised against lanes): enrol PASS, tour 73/73 PASS; hbox composed
  residents UNKNOWN (forge composed decides); j14-apps FAIL: the room-refusal ask got no Hermes reply ("Hermes sent no
  reply to the ask: refused", /ci/j-1c151f/journey.log). Suspected cause: perf-apps' START crash loop ("attestation
  resource outside supported profile", 20-digit member-namespace resource ids), fixed 40efdcff9.
  **Next, armed** (hbox `$I/hp-resid.sh`, Mac waiter bji00dcor): when gate15 exits, gate15 runs on overlay
  **1c151fce4-resid** (batch 5 + the spk-host crate from 40efdcff9) with PHASES="j14 composed", HARNESS=staging tip,
  SUF=-hp1 (PID in gate-1c15-resid-hp1.pid, log logs/gate-1c15-resid-hp1.log). If j14 is still red there, the
  journey's step dir names the cause; route it to app-reds. Then ask infra for forge composed on the green one.
- **Batch 6 (staging 1e339d769+)**: the resource-id fix, exorcism 16f2d046f (reverts the commitment-seen cache) and whatever lands. Cut it when batch 5's gate and umbrella are
  in and enough has accumulated (minimal-checks ruling: cuts spaced out to accumulate perf work).
- **FORMAT batch (later, one genesis, after iter-speed's seam 1)**: hot-path row 11 (checkpoint carries session indexes;
  Store epoch) + Book entries migration (~50 consumers) + private-cells FORMAT (a): eventHistory and authority to the trie
  root with mask [] (root ruling: blinded content and declared kinds keep the salted ratchet until the compiler-emitted ZK
  selective opening exists; that is epoch (b), a second genesis) + KeptCell Aux cache + fixture re-record. Label FORMAT.
- **Batch 3 a4cb65af3: GATE GREEN** (forge composed c-a4cb-d2 every phase; hbox tour, enrol, j14). Fallback ship.
- **Forge demo** (infra): grain world GREEN through the host custodian; EtherCalc + reveal.js accepted. Keys: ember
  approved the OpenRouter pool key and Z.AI GLM (glm-5.3-flash default), relayed by root. Infra keeps a wait-for-Store
  drop-in until cb3bc4f85 ships. Infra unblocked quotactl/quotactl_fd in forge's composed nspawn seccomp (not yet in any
  repo script: infra records it).
- Flatness (reported, never gating): batch 3 submit_cpu 202 -> 1180 ms; batch 4 106 -> 380. CONSENT-STORE (batch 2+)
  measured by the explorer: first signed read 20.7 s -> 0.5-0.8 s flat in height; restart+read 26 s -> 5.6 s; certify
  ~6 s per 256 tail.
- hbox: / 47 GB free (08:30). Host state app-reds added: /var/lib/mini-vars-backing (loop of /tank/lanes/vars-backing.img,
  prjquota ext4, NOT in fstab), /etc/mini-spk-volumes/{vars-backing,ingest-scratch} (ingest scratch /tank/mini-ingest).

## Lanes (route only to the newest id; distilled lanes' old ids are retired)

| lane | agent | owns now |
|---|---|---|
| hot-path | a6c4a1532687a4fdb (ac53c05fe796e4294 retired) | law-17 perf queue: flatness, `story new`, row 11, Book entries migration (FORMAT) |
| app-reds | ad85d40779880420c | apps installs on forge/hbox, op66-plan, Hummingbird/WBO/Scrumblr live qualification, Davros control run, E3/E4, G2 decider-side type, controller boot ordering, Hermes worker root interpreter |
| private cells | a8da2b953507b402b | FORMAT (a); then the compiler-emitted ZK selective opening; decode pin to CanonicalCellRegistry.custodyDecode with (b) |
| iteration speed | a6c58cb72b0764dbb | seam 1 (codec tags / Store epoch, lands before or with FORMAT), lane pool /home/hbox/pool, lane-tree, hot-swap overlay tool |
| explorer | a3e5d6dbcd68e616c | multi-member exploration of each READY candidate; docs/EXPLORER-FINDINGS.md on lane/explorer |
| infra | aa72653a8ce442178 | forge demo container, forge composed (judges residents/restart), dregg-infra (ship.sh, world-down finding) |
| exorcist | a6ad40ce192354deb (a31f4ba5028d24a92 retired) | no fsync anywhere (lane/exorcism); filtered set `nextest -E 'test(durable) \| test(anchor) \| test(signing_wire) \| test(attempt_state) \| test(receipt_continuity)'` |
| perf-apps | a25df305cfd551d8b | apps install, grain HTTP path, typed-tool path (perf) |
| perf-client | a8d456c6e773efbb8 | client, consent provider per-record cost, web page loads, idle cold start (perf) |
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
- Flatness (law 17) is reported, never gating. Rehearse only a fully green gate with no demo-path product red.

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
| 1c151fce4 | READY (batch 5); gate15 running, j14 red |
| 1c151fce4-resid | overlay: batch 5 + spk-host crate from 40efdcff9 (resource id any non-zero u64); gate15 -hp1 queued after batch 5's gate |

## Open reds and owners

- TokenCensus ConsentAnchor L1 witness: fixed b70a547c8 (batch 4), confirm in batch 4's umbrella.
- Flatness submit/get (law 17): hot-path; content-cell flatness stays a published red until private-cells (b).
- Etherpad install on forge: 0aa00c3e0 (batch 4); recheck on a fresh world. op66-plan: app-reds.
- Hermes ask on forge: fenced controller fixed cb3bc4f85 (batch 4); Z.AI path 5f32da72d (batch 4).
- world-down.sh leaves the world dir and client residents behind: infra (dregg-infra).
- Every tour JWF-dry `mini web --body` orphan: fixed by demo-reds' lifeline 4928d9a77 (in batch 3); confirm after gates.
- Deregistration's lease freshness ranges over every lease (index leases by account if frequent): hot-path.

## Rules

Named-file commits with `git commit -F <file>`; never `git add -A` or `git stash`; filtered tests only; every detached
job has a PID file and is stopped only by it; lake/git on hbox as hbox, never root; swarm-build caps summing under
~100 GB; one sequential job per build tree; never search from / or ~; disk pressure = stop and tell ember.
