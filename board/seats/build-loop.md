# Seat: build-loop

Agent: none live (the 2026-11-05 rebuild was done by the demo-dry takeover session; handoff 2026-11-01 02:40Z before it). Last: a4141abe7297fdc4b (`cv show agent-a4141abe7297fdc4b`), before it
a6c58cb72b0764dbb. A new agent needs only the repo, `cv` and ~/swarm (MACHINES.md, RULES.md); this file is the whole
continuation.
Owns: the builder (`scripts/pipeline/{builder,integ-build,gate,sweep,world-reap}`) and `board/REDS.md`, the `green`
ref; build scripts (`scripts/build-native-host.sh`, `deploy/candidate/{lane-build.sh,package.py,lib.sh}`); the pool
(`scripts/pipeline/{lane-tree,warm-link,lane-check,umbrella-tree,native-loop}`); `scripts/pipeline/{hot-swap,
candidate-transfer}`; import seams; the boxes hbox (builds) and persvati (measurement pool); outside PRs (akapug).
Quest: an unattended builder on `main` that nobody waits on; inner loops of seconds to minutes; never slower.

## The builder (hbox, running, unattended: leave it running)
- What it does: loops on origin/main. Each new tip is a round:
  1. `integ-build` (from that tip) runs prime-cargo, rust-check, host, consent, rust and pack into
     `candidates/<sha>/READY`. It then syncs the umbrella tree and frees `src`, so the next round can start. The
     umbrellas (Fixtures, ObjectiveProofs, CensusChecks, Minidregg) and the fixture rerecord finish beside it.
  2. `gate`: the tour (J0-J8 and JWF dry), composed (keep-going, dregg-infra edge 3ddd90f), enrol-resume, j14-apps,
     and the flatness run last. A red phase is rerun once, alone (`-r1`).
  3. It rewrites board/REDS.md whole and commits it by path straight onto main. It moves `green` when nothing is
     red. Flatness is a published table and never gates (9317f32fc).
  4. `world-reap` tears down the processes of every builder gate world except those behind this round's reds.
- Where: hbox, BUILDER_ROOT=/home/hbox/lanes/integ (src = warm integration tree, umbrella-src, candidates/,
  logs/, builder/ = state: last-built, signatures, REDS-*.md, reap-*.log). Every action is a line in
  /home/hbox/lanes/integ/COMMANDS.log. Gate worlds are /ci/{t,c,e,f,j}-<sha6>[-r1]; gate roots integ/gate-<sha8>.
- Pushes: only board/REDS.md, `green`, `fixture-regen/<sha>` branches and the fixture rerecord commit (two
  Fixtures/*Data.lean files, fast-forward, never forced, RULINGS). Never force-pushes main.
- Deploy key: integ/src and umbrella-src push with hbox:~/.ssh/minidregg-deploy (read-write for emberian/minidregg),
  set as `core.sshCommand = ssh -i /home/hbox/.ssh/minidregg-deploy -o IdentitiesOnly=yes`. dregg-build2 (obend's
  box now) keeps its own key ~/.ssh/minidregg_deploy for user build until ember says otherwise. Never copy a key.
- **Stop it**: `ssh hbox-remote`, then
  `p=$(cat /home/hbox/lanes/integ/builder.pid); tr '\0' ' ' </proc/$p/cmdline` (it must read
  `bash /home/hbox/lanes/integ/builder-main.sh`), then `kill $p`. Stop it right after a `BUILDER round ... done` line
  in COMMANDS.log, or while it sleeps. Its detached children (an integ-build, the umbrellas) finish on their own. A
  stopped mid-gate round leaves no REDS.md for that tip; the next builder rebuilds the tip.
- **Start it**: `cd /home/hbox/lanes/integ && setsid nohup bash builder-run.sh >> builder.out 2>&1 < /dev/null &`.
  builder-run.sh sources ~/.minidregg-env, sets BUILDER_ROOT, GATE_RUNS=/ci, WORLD_UP_LOCK=/tank/lanes/world-up.lock,
  SEATS=12 and MEM=64G, fetches main's scripts/pipeline/builder into builder-main.sh, writes builder.pid and execs it.
  A new builder script on main takes effect only on restart. integ-build, gate, sweep and world-reap are taken
  from the tip each round. A second builder refuses (builder/builder.lock). A build lock held by another build
  defers the round (`deferred: build.lock held`, retried every 120 s) and publishes nothing.
- Live now (2026-11-05 02:30Z): rebuilt from scratch after ember's 2026-11-04 cleanup removed the whole
  /home/hbox/lanes/integ and /home/hbox/pool/lanes (the old builder had been dead since 11-01 on a GitHub key
  denial; the deploy key itself still works). The new root: `src` (fresh blob:none clone, deploy key as
  core.sshCommand), `builder-run.sh` as above plus `EDGE_REV=cf0b94f`, `PLAYWRIGHT_DIR=$I/pw/node_modules`,
  `PLAYWRIGHT_BROWSERS_PATH=$I/pw/browsers`; `j14-hroot`, `j14-data`, `spk-cache`, `pw` copied from
  dregg-build2:/srv/integ (where they were staged 10-31); `j14-secrets/openrouter.key` from the Mac's
  ~/.openrouter-key; `dregg-infra-cf0b94f/edge`. `src` was warmed the pool's way: `.lake/packages` linked to
  the pool's packages-3a3779933df4 then `lane-tree native src` (its own hard-linked copy), build outputs
  warm-linked from pool tree t1 (e53e4515) and t1's `.lake/native` copied. Its first round (0852014c3, cold
  tree) was red at `host` on a missing .lake/packages and wrote REDS.md so; the next tip rebuilds warm.
  Then: the Oct 31 builder (pid 1235827, its tree deleted under it) woke on the new src and raced the new
  loop until ember had it killed; `--once` now rev-parses its id (158ffd6fb); the reaper is taken at round
  start (240295848); the copied runtime root needed its venv interpreter link and umask-022 modes; j14 then
  found wave1's one-line `doc edit` rule against summon's one-action program (fixed on main: 2ef06fb15,
  0264f390e). Round 0264f390e: 0 reds, j14 PASS, composed PASS, tour 73 PASS, flatness published;
  `green` -> 0264f390ecf7 (2026-11-05 19:53Z), the first move since 6ba8fe37fa18 (11-01). The loop is
  `builder-run.sh` (builder.pid); two unnamed processes of the 11-05 00:xx collided tour world
  (`mini serve` 2392553, `mini-web-spawn --dev` 2392988, root /ci/t-158ffd) have no PID file and are left
  for ember or the sweep (ember killed them 11-05).
  Cycle (2026-11-06): a round is 468 s (build warm ~190 s, the gate's parallel phases ~250 s; flatness runs
  beside them and is published, the red-row rerun is BUILDER_RERUN=1, the reap is detached, poll 30 s). A green
  reaches the demo box by the plain walk (dregg-infra edge/demo/demo-dry-walk, WALK_REGENESIS=0): preship-check,
  stream (~5 min through the Mac), ship (17 s on the box: link flip + Store restart, world kept). Commit to
  serving is about 14 minutes; the stream is the next cut (hbox -> box direct, or the box pulling). A tip
  that changes only board/ (the builder's own REDS.md commits) is recorded as built, not rounded (0d7e1a2ce).
  2026-11-06: four plain ships landed on demo-dry; what they taught is on main (install-hermes through
  current and resumable, apps-worker publishes front tables, broker keeps a generation's runtime pin, the
  resident context brief bounds row provenance, the operator's refuse-unadmitted verb) and in dregg-infra
  (grain-world refresh in the plain walk, the entrance restarted after the Store, the ship refuses over an
  active checkpoint plan, mini-checkpoint --abandon). Open product item: a resident prompt whose reply was
  lost at a controller restart has no typed close (see the demo-dry ops memory).
- Knobs: `scripts/pipeline/builder --once`, `--reds SHA` (rewrite REDS.md from existing logs), BUILDER_DRY=1 (print,
  never push). $I/keep lists candidate prefixes that sweep and reap never touch. integ-build stops below 25 GB free.

## Open reds (REDS.md at d5e858b2222b; green is still 83e926874, batch 4, 15+ hours)
- gate:composed:residents (member-side, infra): `REFUSED timeout: managed fixture provider`. Every round since
  9dc9c138 has it (once `prepoll-filler-068 refused with status 3`). It blocks composed restart (host-execution).
  This is the red that holds green now that flatness does not gate.
- Flatness, published only: submit_cpu ratio 5.25, submit_wall 3.63, propose_cpu 3.33 and propose_wall 5.73
  (bound 2.0, host-execution and store-retained). get passes (0.6-1.9).
- Umbrellas: Fixtures.NativeAcceptedFixture and NativeDocWriteFixture go red whenever a Host change moves event ids.
  The rerecord lands their data itself now (land_regen, fd1686db7). fixture-regen/d5e858b2222b was recorded in a
  moving tree and stays unlanded; the next round records it again.
- Known gaps (unfixed): composed starts testing/journeys/shared-resident-fixture-provider.py with no PID file, so
  world-reap reports it UNNAMED (one left in /ci/c-4b750e, pid 2608947). scripts/spk-platform/stop-residents.sh
  stops RUN/a anchors only, not sessions' .call-slots line-residents. The umbrella stage runs the umbrella tree's
  HEAD, which can differ from the round's sha when rounds overlap. Read the rerecord's `recorded fixture-regen/<sha>`
  line, not the stage's sha.

## The pool and the inner loop (hbox /home/hbox/pool; Lean caps in ~/.minidregg-env)
- ~/.minidregg-env (sourced by .profile and .bashrc) sets PATH with /home/hbox/pool/bin (lane-tree, warm-link),
  MINIDREGG_LEAN_SEAT_ROOT=/home/hbox/seats, MINIDREGG_LEAN_SEATS=12, LEAN_NUM_THREADS 4, SWARM_MEM_MAX 48G,
  CARGO_BUILD_JOBS 12 and LANE_POOL_ENV=/home/hbox/pool/pool.env. Every build is `swarm-build <cmd>`.
- Trees t1..t11, worktrees of /home/hbox/pool/repo.git. All share the read-only packages-3a3779933df4 and are warm by
  hard links from integ/src (warm-link; a new tree costs about 2 GB). LAKE_ARTIFACT_CACHE=false.
- Lean: `t=$(lane-tree acquire SEAT origin/BRANCH); cd $t; scripts/pipeline/lane-check FILE...`; then
  `lane-tree release SEAT`. `lane-tree status` shows the holder, lease age, idle minutes and dirty count.
- Native host: `lane-tree native SEAT` (own linked packages copy), then `scripts/pipeline/native-loop SEAT BASE LABEL`.
  That is a Lean change to a native candidate in about 7 minutes (was about 48).
- Leases: a lease expires after 12 h (LANE_POOL_TTL_H). It is idle when nothing has touched it for 30 min
  (LANE_POOL_IDLE_M; touched = acquire, renew or an uncommitted file written) and no process has its cwd, an open
  file or its command line in the tree. The next acquire takes an idle or expired tree (a free one first), and
  `lane-tree gc` frees both. The holder's diff goes to /home/hbox/pool/saved/<tree>-<lane>-<time>.patch.
  The box copy bin/lane-tree is main's cbe54d87f; update it by `git show <sha>:scripts/pipeline/lane-tree` into
  bin/lane-tree.new, then mv.
- Leases at handoff: t1 private-cells 8 h, t2 apps-hermes, t3 he-enrol, t4 retained (store-retained), t5 he-births,
  t7 hot-path 8 h (no seat; the idle rule frees it), t8 host-execution. Free: t6, t9, t10, t11. build-loop released
  t6 (iter-hotswap) and t9 (seam1) at handoff; t6's saved patch lists only two untracked files already on main.

## Hot-swap and candidate transfer (on main)
- `deploy/candidate/lane-build.sh overlay BASE PARENT LABEL ROLE...` (`package.py --overlay`) builds an overlay
  candidate: whole build families only, a 12-hex id, every pin re-emitted.
- `LANE_DIR=LANE scripts/pipeline/hot-swap --state STATE [--hermes-root ROOT] LABEL ROLE...` does, in order:
  1. the overlay on the base the world STATE runs;
  2. `run.sh stop`, `run.sh upgrade`, and the Hermes root `--rebind` when grainRuntime or grainProviderBridge move;
  3. `run.sh start`, and one line in STATE/hot-swaps.jsonl.
  It refuses a unit-supervised Store. Measured 10-31: stop to serving in 8 s; overlay own disk 141 MB.
- `scripts/pipeline/candidate-transfer SRC_HOST:DIR DST_HOST:DIR NAME` (run from the Mac; `-` = local) streams to
  DST/.incoming-NAME, verifies SHA256SUMS (and READY), then renames in one step. Never copy into candidates/NAME
  directly.

## World hygiene
- `scripts/pipeline/world-reap [--dry] ROOT...` stops processes by PID file only. Sources: the world's *.pid
  files, jweb `.bodyPid` in state/sessions/*.json, and ~/.mini/consent-anchors/*.pid. Journeys run with the box
  HOME put their residents' files there. A process belongs to ROOT when its cwd, or an argument that is not a binary
  path, names ROOT. Everything else is reported UNNAMED and left. One /proc pass; about 25 s for 15 roots.
- `scripts/pipeline/sweep` (runs after each gate) removes the gate roots and worlds of candidates two or more behind,
  and candidates beyond the newest 3. It skips $I/keep and anything a live process names.
- Fleet at handoff (10-31 22:30 EDT), minidregg-host processes: hbox 43 before the builder's reap, 36 after (7 finished
  builder worlds, 31 processes stopped). Still up on hbox:
  - store-retained pool/t4: 12 (told);
  - /ci/hpc: 6 (hot-path, no seat; it also runs residents on /ci/c-acc7cf-c2's binaries);
  - the 10-29 demo-path jwf worlds: 10 (unowned);
  - read-path /ci/exo/w8: 3 (no live seat);
  - 10-03 codex workbox and 09-27 gitweb fixtures: 2;
  - /var/lib/mini-bigstep-hbox-r1, r2: 2 (root-owned).
  The unowned ones are root's to decide. persvati has 21: read-path rp/w 9, and member-side's rpw/tb and rpw/tr,
  store-retained's live before/after pair (member-side stops them when store-retained is done); rpw/sa is down.

## Boxes and disk
- hbox: / 455 GB, 40 GB free at handoff (91%; usually 85-93%). The gate and qualify worlds in /ci are the usual
  writers (about 0.5-0.9 GB each). sweep logs `DISK WARN` below 40 GB, and integ-build refuses below 25. No new data
  on /tank. `free` lies on ZFS (check arcstats).
- persvati (`ssh persvati-remote`): measurement only, pool /home/ember/mdpool (4 trees at 43995c7f), budget about 80 GB.
- dregg-build2: obend's; minidregg does not build or run worlds there (setup left in place, unused).

## Done and on main (for reference)
- Build speed: lake-threads (e9d1c6fc8), module-cost (b833dd9c9, cb49daa63), Mathlib trim (ee7a25ca7, 0eab28db7),
  unrecorded-module seating (0f67c94b7) and native-loop (7800d3199, 697db7664). The host stage went from 2,476 s
  to 1,005 s. Next levers: the per-compile import tax, the Application* path depth, the consent companion's ~116 s.
- Seam 1, codec tags (f2002e589): a census-tag edit rebuilds 4 modules in 95 s (was 365 modules in 447 s). Seams 2
  and 3 only if a measured edit rate pays for them.
- Builder fixes:
  - umbrellas do not hold the next round (eb4b7e7b2);
  - lock inheritance closed (3ef7de9ac fd 9, f1d2d3bbb fd 8);
  - fixture rerecord lands itself (15f9987f5, fd1686db7);
  - flatness published (9317f32fc), world reaping (9317f32fc);
  - idle pool leases (cbe54d87f).

## Outside PRs (akapug)
- Landed 10-31 and closed: #5 (d9f333dbf), #4 (ae98da48b, ported). Superseded and closed: #16, #14, #7.
- #18 (simplex prepared jump): open. Its item 1 (does the catch-up jump enter the deployed agreement step now?) is
  with ember via root. If yes, it needs items 2-5 (logMagic 5, drop the Fabric-bound script, drop the ResearchWip
  hunk, rebase onto Lean 4.35) before merge. If no, say so on the PR.

## Seams needed
- infra (a5bc08dce78e7405e): the kept-world rebind tool; ship.sh accepting `.overlay.id`.
- member-side / infra: a PID file for composed's shared-resident-fixture-provider.py; call-slot residents in
  stop-residents.sh.
