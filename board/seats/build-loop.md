# Seat: build-loop

Agent: none live. The 2026-11-14 restore after ember's second cleanup of hbox was done by a one-task agent of the
coordinator's session; the 2026-11-05 one by the demo-dry takeover session. Last seat: a4141abe7297fdc4b
(`cv show agent-a4141abe7297fdc4b`), before it a6c58cb72b0764dbb. A new agent needs only the repo, `cv` and ~/swarm
(MACHINES.md, RULES.md); this file is the whole continuation.
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
  2. `gate`: the tour (J0-J8 and JWF dry), composed (keep-going), enrol-resume and j14-apps in parallel, with the
     flatness run beside them. The edge is dregg-infra 97fc590 on hbox (builder-run.sh's EDGE_REV; the script's
     own default is 3ddd90f): cf0b94f plus one file, jworld-scratch.sh reading the client's usage whole before it
     searches it (branch `gate/cf0b94f-help-grep`; dregg-infra main carries the same fix as 697b8ff). Under
     pipefail `mini --help | grep -q` lost a race, dropped the Host pin and reported a serving world as `the relay
     did not answer a pinned enrollment-view within 30 s` (composed red for five rounds, 11-14 12:58-15:16 EST). A red phase is rerun once, alone (`-r1`), only with BUILDER_RERUN=1.
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
  stopped mid-gate round leaves no REDS.md for that tip; the next builder rebuilds the tip. A `sleep` child of the
  stopped builder keeps builder/builder.lock for up to the poll interval (30 s): a start inside that window is
  refused (`another builder holds ... builder.lock` in builder.out); wait it out and start again. If builder.pid is
  missing the builder may still be alive: see step 1 of the rebuild below.
- **Start it**: `cd /home/hbox/lanes/integ && setsid nohup bash builder-run.sh >> builder.out 2>&1 < /dev/null &`.
  builder-run.sh sources ~/.minidregg-env, sets BUILDER_ROOT, GATE_RUNS=/ci, WORLD_UP_LOCK=/tank/lanes/world-up.lock,
  SEATS=12, MEM=64G, BUILDER_POLL_S=30, EDGE_REV=97fc590, PLAYWRIGHT_DIR=$I/pw/node_modules and
  PLAYWRIGHT_BROWSERS_PATH=$I/pw/browsers, fetches main's scripts/pipeline/builder into builder-main.sh, writes
  builder.pid and execs it.
  A new builder script on main takes effect only on restart. integ-build, gate, sweep and world-reap are taken
  from the tip each round. A second builder refuses (builder/builder.lock). A build lock held by another build
  defers the round (`deferred: build.lock held`, retried every 120 s) and publishes nothing.
- Live now (2026-11-14 10:10Z): running, pid in builder.pid, started 2026-11-14 04:29 EST after ember's 03:37 EST
  cleanup of hbox's home removed the whole root (the second time; 11-04 was the first). EDGE_REV=97fc590 since 11-14 15:52 EST.
  Rounds since: a4472f3f65b2 (1,371 s, cold Rust and native; REDS.md published as 120e113e9) and 120e113e9c73
  (919 s). Both: build stages green, tour 73 PASS, composed PASS on all eight phases, enrol-resume PASS, flatness
  published. Reds: `ratchets` (bytes-repr: 5,001 `List UInt8` over the ceiling 4,931), the umbrella's
  Fixtures.NativeAcceptedFixture and NativeDocWriteFixture (the rerecord landed their data, 54dee83bc), and
  gate:j14-apps. j14 in the first round was the restore's own fault (below). In the second it ran to the probe
  with live model replies and stopped at `resident prompt 121 ended "review-needed" over an admitted outcome
  record` (/ci/j-120e11/step/oracle/commands/0109-controller-run.stderr): apps-hermes's to read; j14 passed at
  7db8a63a8 the same night before the cleanup. `green` is 788dfb51.
- **Rebuilding the root from nothing** (done 11-05 and 11-14; about 40 minutes plus one cold round), I=$BUILDER_ROOT:
  1. The old builder outlives its directory. A cleanup removes builder.pid and leaves the process (cwd $I, command
     line `bash builder-main.sh` or the full path, fd 8 on a deleted builder/builder.lock). It is inert while
     $I/builder is missing and wakes fully the moment a new builder creates it, then races every round (11-05).
     Find it before anything else: `pgrep -fl builder-main`, then `readlink /proc/PID/cwd` and `ls -l /proc/PID/fd`.
     It has no PID file, so stopping it needs ember's word; then `kill PID`, that one PID. Its knobs can be read
     from /proc/PID/environ (that is where EDGE_REV and BUILDER_POLL_S came from on 11-14).
  2. `src`: `git clone --filter=blob:none git@github.com:emberian/minidregg.git` with the deploy key, then
     core.sshCommand as above. Warm it the pool's way: `.lake/packages` linked to the pool's
     packages-3a3779933df4, `lane-tree native $I/src` (its own hard-linked copy, about 200 s), `warm-link
     SEED/.lake/build src/.lake/build` from the pool's seed tree, and the seed's `.lake/native` copied.
  3. `pw` (Playwright 1.62.1, chromium-1234), `j14-hroot`, `j14-data` (davros.spk, inventory.json) and `spk-cache`:
     still staged on dregg-build2:/srv/integ (10-31); stream them with tar through the Mac (hbox does not resolve
     bb2). The runtime root then needs `ln -s /usr/bin/python3 j14-hroot/venv/bin/python` (the source has an
     unreadable placeholder there) and `chmod -R u+rwX,go+rX,go-w`. Never import from that venv to test it: the
     `__pycache__` directories it writes under the login umask 002 fail the controller's custody check (`worker
     runtime directory custody refused`, round a4472f3f). If bb2's copy is gone, `deploy/hermes/build-runtime-root`
     builds a root from a hermes-agent checkout at 6d8a8beb with uv.
  4. `j14-secrets/openrouter.key` (0600 in a 0700 directory): scp of the Mac's ~/.openrouter-key.
  5. `dregg-infra-97fc590/edge`: `git archive 97fc590 edge` from the Mac's ~/dev/dregg-infra (branch
     `gate/cf0b94f-help-grep`, on both of its remotes).
  6. `builder-run.sh` as under Start. Everything else (builder/, logs/, candidates/, umbrella-src, the Rust target
     directories) the first round makes itself. The moved-aside `src.stub-20261114` is the 11-06 builder's debris.
- Cycle: warm, a round is about 470 s alone on the box (build ~190 s, the gate's parallel phases ~250 s) and
  470-630 s when it shares the box with lane builds; flatness runs beside the phases and is published, the red-row
  rerun is BUILDER_RERUN=1, the reap is detached, the poll is 30 s. A tip that changes only board/ (the builder's
  own REDS.md commits) is recorded as built, not rounded (0d7e1a2ce). A green reaches the demo box by the plain
  walk (dregg-infra edge/demo/demo-dry-walk, WALK_REGENESIS=0): preship-check, stream (~5 min through the Mac),
  ship (17 s on the box); commit to serving is about 14 minutes.
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

## Open: the census tail is longer than the rest of the umbrella (iteration lane, 2026-11-06)
- Measured on bb2 in a cold umbrella build of f54c4205e, LEAN_NUM_THREADS=4, under load 40-90.
  Everything else finished by 2,550 s. The census then runs serially at the end:
  AxiomCensusResearch took 412 s and 8.0 GB, TokenCensus.Fixtures 453 s, and TokenCensus was
  still elaborating after 75+ minutes when the run was stopped. The 10-31 Mac measurement in
  docs/ITER-SPEED-STATE.md has TokenCensus at 1,859 s.
- Ruled out: TokenCensus's scans over dependency constants. A filter skipping Mathlib/core
  constants is exact, because none of them can name a minidregg constant, but TokenCensus still
  ran past 24 minutes with it. TokenCensus.Fixtures, whose scans are already scoped, took 643 s.
  The time is elsewhere: the L1-witness checks (`l1WitnessFaults`, `trivialConclusion`'s
  `whnfR`/`isDefEq`) or `#assert_axioms_tree`.
- Next step for the census owner: time each check of `runTokenCensus` with `IO.monoMsNow` in a
  scratch copy (one lean, bb2, the whole tree loaded), then fix the dominant one.
- Notes: redregg-notes landscape/ITERATION-SPEED-2026-11-06.md.

## The pool and the inner loop (hbox /home/hbox/pool; Lean caps in ~/.minidregg-env)
- ~/.minidregg-env (sourced by .profile and .bashrc) sets PATH with /home/hbox/pool/bin (lane-tree, warm-link),
  MINIDREGG_LEAN_SEAT_ROOT=/home/hbox/seats, MINIDREGG_LEAN_SEATS=12, LEAN_NUM_THREADS 4, SWARM_MEM_MAX 48G,
  CARGO_BUILD_JOBS 12 and LANE_POOL_ENV=/home/hbox/pool/pool.env. Every build is `swarm-build <cmd>`.
- Trees t1..t3 (rebuilt 2026-11-14 after the cleanup; `lane-tree init SEED N` grows the pool), worktrees of
  /home/hbox/pool/repo.git. All share the read-only packages-3a3779933df4 and are warm by hard links from the pool's
  own seed tree /home/hbox/pool/seed (pool.env LANE_POOL_WARM; before 11-14 the warm source was integ/src; warm-link;
  a new tree costs about 2 GB). LAKE_ARTIFACT_CACHE=false.
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
- Leases: read them with `lane-tree status` (2026-11-14 05:00 EST: t1 free, t2 history-index-2, t3
  registry-effects-2).

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
- hbox: / 455 GB, 133 GB free on 2026-11-14 after ember's cleanup (70%; before it, usually 85-93%). The gate and
  qualify worlds in /ci are the usual writers (about 0.5-0.9 GB each). sweep logs `DISK WARN` below 40 GB, and
  integ-build refuses below 25. No new data on /tank. `free` lies on ZFS (check arcstats).
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
- #18 (simplex prepared jump): open, changes requested. Ember's review of 10-31 23:03Z asked for a progress theorem
  with the jump, what the jump trusts, logMagic 5 with a v4-refusal theorem, the O(V²) `preparedAbove` fixed with
  old views retired, and the Fabric-bound script fitted to main; nothing has been pushed since. The PR edits the one
  `step`; no shipped process runs it (the Host imports the engine for codec types only). Taken over 11-13.

## Seams needed
- infra (a5bc08dce78e7405e): the kept-world rebind tool; ship.sh accepting `.overlay.id`.
- member-side / infra: a PID file for composed's shared-resident-fixture-provider.py; call-slot residents in
  stop-residents.sh.
