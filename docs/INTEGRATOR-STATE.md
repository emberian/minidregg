# Integrator state

Present-state record of the integration lane, rewritten whole when its shape changes. A successor reads this, then
`hbox:/home/hbox/lanes/integ/COMMANDS.log` (every build stage, gate verdict, sweep, world teardown and process stop, one
line each). History is in this file's git history.

The integrator is agent **aba0beaa578594e92**, distilled 10-31 06:00 from aeb671706eb3f70d7 (retired; the cv
retired-agent hook names the live integrator to anyone who messages the old id). Lanes send shas, READY, reds and handoffs to the
integrator; the integrator merges onto `integration/staging`, cuts batch candidates on hbox, gates them, moves main to
gated candidates and names candidates to infra and the explorer.

## Now (2026-10-31 07:40 EDT)

- **main = 83e926874** = gated batch 4 b9450147f merged with main 7978ddfdd.
- **Batch 4 b9450147f: GATE GREEN, the rehearsal-3 candidate.** hbox tour 73/73, enrol, composed; forge composed c-b945-d1 all
  phases; j14-apps PASS with the deploy-script hotpatch HARNESS=9fdef19bd (bwrap ACL 11a4f4ac6: controller uid gets its own
  execute entry on /usr/local/libexec/mini-grain-bwrap, app-range entries claimed per world; grant_acl stops at the world
  root c76dbe0c7; gate15 = gate14 + j14 socket parent 711; /ci is 711). Umbrellas all green; fixtures 5c00cc4f3 merged.
  Flatness: submit_cpu 106 -> 380 (3.6x), propose_cpu 4.05x; walls and get PASS.
- **Batch 5 1c151fce4 BUILDING** (07:29, integ-build6): exorcism, module-cost, hot-path authority, app-reds route/teardown/ACL.
- Known leak: residents started by j14-oracle application hooks' query step outlive the run (settings under
  step/oracle/application/hooks/*/002-query); app-reds owns the fix; the integrator stops them by exact PID after each j14.
- **Batch 3 a4cb65af3: GATE GREEN.** Forge distinct composed c-a4cb-d2 PASSES every phase (rooms, churn, documents,
  apps, connector, residents, restart, store-restart); hbox gate13 tour 73/73, enrol, j14-apps PASS (5 rows); umbrellas
  green except TokenCensus (ConsentAnchor L1 witness, fixed in batch 4). Fixtures re-recorded d546395a9 (merged). It is
  the fallback ship: it lacks the Z.AI endpoint fix 5f32da72d, the fenced-controller fix cb3bc4f85 and the Etherpad
  birth naming 0aa00c3e0 (all in batch 4).
- **Batch 4 b9450147f BUILDING** (launched 05:35 with integ-build6; host stage started after batch 3's umbrella-tree
  released its lock, ~05:39). First build with iter-speed's lake-threads fix e9d1c6fc8: report its host stage time beside
  batch 3's 2,476 s. Waiter: READY line is `READY /home/hbox/lanes/integ/candidates/<sha>`. If green on gate13 AND
  forge composed: it is the rehearsal-3 candidate (rehearse only green). Contents: hot-path demanded projection + content
  law over cached support + TokenCensus fix + StoryHistory fix + `story new` fold (17 -> 4 submits) + Book entries
  statement and proofs; private-cells Thunk, CustodyCodec, kindCtx, round-18 fixes; app-reds route before START,
  qualification args, gogs fixture, custodian installer dd80d1e2a + floor fd8de031a, Etherpad birth naming 0aa00c3e0,
  named-conjunct error d2377d3c5; demo-reds Z.AI endpoint 5f32da72d, fenced controller cb3bc4f85; iter-speed hot-swap
  overlay + overlay ids; explorer batches 10-11.
- **Batch 5 (staging a52de3604+)**: exorcism 4f7972a62 (no fsync anywhere, ember; rebased onto the no-loop volume design),
  hot-path 4fb1a0e17 (authority snapshot projection over cached support), plus whatever lands. Cut it after batch 4's
  READY and its umbrella-tree/rerecord (integ-build6 waits for the umbrella lock itself, so launching after READY is safe).
- **FORMAT batch (later, one genesis, after iter-speed's seam 1)**: hot-path row 11 (checkpoint carries session indexes;
  Store epoch) + Book entries migration (~50 consumers) + private-cells FORMAT (a): eventHistory and authority to the trie
  root with mask [] (root ruling: blinded content and declared kinds keep the salted ratchet until the compiler-emitted ZK
  selective opening exists; that is epoch (b), a second genesis) + KeptCell Aux cache + fixture re-record. Label FORMAT.
- **Forge demo** (infra): grain world GREEN through the host custodian; EtherCalc + reveal.js accepted; ships
  eca98bde7-resvar2-zai or a4cb65af3 with OpenRouter (Z.AI needs batch 4). Keys: ember approved OpenRouter pool key and Z.AI
  GLM (glm-5.3-flash default), relayed by root. Infra keeps a wait-for-Store drop-in until cb3bc4f85 ships. Infra
  unblocked quotactl/quotactl_fd in forge's composed nspawn seccomp (not yet in any repo script: infra records it).
- Flatness (reported, never gating): batch 3 submit_cpu 202 -> 1180 ms, get 2.19x. Hot-path's profile (/ci/hpc/fbz):
  28% content-law dedup (fixed f7da550af), 18% signed-read challenge path, 13.6% DTreeMap getD in payloadStream; private-
  cells' eager carried index only 3.8%. Batch 4 measures the fixes. CONSENT-STORE (batch 2+) measured by the explorer:
  first signed read 20.7 s -> 0.5-0.8 s flat in height; restart+read 26 s -> 5.6 s; certify ~6 s per 256 tail.
- hbox: / 43 GB free (05:59). Host state app-reds added: /var/lib/mini-vars-backing (loop prjquota ext4 from
  /tank/lanes/vars-backing.img, NOT in fstab: after reboot `sudo mount -o loop,prjquota /tank/lanes/vars-backing.img
  /var/lib/mini-vars-backing`), /etc/mini-spk-volumes/{vars-backing,ingest-scratch}, /tank/mini-ingest.

## Lanes (route only to the newest id; distilled lanes' old ids are retired)

| lane | agent | owns now |
|---|---|---|
| hot-path | a6c4a1532687a4fdb (ac53c05fe796e4294 retired) | law-17 perf queue: flatness, `story new`, row 11, Book entries migration (FORMAT) |
| app-reds | ad85d40779880420c | apps installs on forge/hbox, op66-plan, Hummingbird/WBO/Scrumblr live qualification, Davros control run, E3/E4, G2 decider-side type, controller boot ordering, Hermes worker root interpreter |
| private cells | a8da2b953507b402b | FORMAT (a); then the compiler-emitted ZK selective opening; decode pin to CanonicalCellRegistry.custodyDecode with (b) |
| iteration speed | a6c58cb72b0764dbb | seam 1 (codec tags / Store epoch, lands before or with FORMAT), lane pool /home/hbox/pool, lane-tree, hot-swap overlay tool |
| explorer | a3e5d6dbcd68e616c | multi-member exploration of each READY candidate; docs/EXPLORER-FINDINGS.md on lane/explorer |
| infra | aa72653a8ce442178 | forge demo container, forge composed (judges residents/restart), dregg-infra (ship.sh, world-down finding) |
| exorcist | a31f4ba5028d24a92 | no fsync anywhere (lane/exorcism); filtered set `nextest -E 'test(durable) \| test(anchor) \| test(signing_wire) \| test(attempt_state) \| test(receipt_continuity)'` |
| demo-reds (sub-Opus of the integrator) | a64c387f3e638aa63 | bend/web/door/Hermes product reds as routed |
| statement auditor (sub-Opus of the integrator) | a4d9a6f4cba4855ca | read-only adversarial audit of each lane's top-level statements, one round per merged sha |

Every Lean-statement sha gets an audit round from a4d9a6f4cba4855ca before it rides a cut; verdicts go back to the lane.

## Rulings in force

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
| 1c151fce4 | BUILDING (batch 5) |

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
