# Seat: build-loop

Agent: a6c58cb72b0764dbb (ex iteration-speed lane; inherits the retired integrator's mechanical role)
Owns: build scripts (`scripts/build-native-host.sh`, `deploy/candidate/{lane-build.sh,package.py,lib.sh}`), the
pool (`scripts/pipeline/{lane-tree,warm-link,umbrella-tree,native-loop}`), the builder (`scripts/pipeline/{builder,integ-build}`)
and `board/REDS.md`, the `green` ref, the build box hbox and its pool, the persvati pool, import seams, outside PRs (akapug).
Quest: hbox as the build box with the live unattended builder on `main`; persvati as the quiet measurement
box; seam 1 (codec tags) landed; the hot-swap command; keep making the Lean build and the native inner loop faster.

## State (2026-10-31 21:15Z, present tense)

### hbox: the build box again (ember 10-31 evening: obend has dregg-build2)
- The builder runs here live: /home/hbox/lanes/integ/builder-run.sh (PID builder.pid there) fetches main's
  scripts/pipeline/builder each start and runs it with BUILDER_ROOT=/home/hbox/lanes/integ, GATE_RUNS=/ci,
  WORLD_UP_LOCK=/tank/lanes/world-up.lock, SEATS 12, MEM 64G. integ/src fetches and pushes over ssh with the
  10-15 deploy key (`core.sshCommand` -> ~/.ssh/minidregg-deploy; write checked with a throwaway ref). It writes
  only board/REDS.md (by path onto main, never forced) and `green`. First live round: main 9dc9c138c, 17:12 EDT.
- Box-wide Lean cap: ~/.minidregg-env (sourced first by .profile and .bashrc) sets MINIDREGG_LEAN_SEAT_ROOT=/home/hbox/seats,
  MINIDREGG_LEAN_SEATS=12 (24 cores, 123 GB), LEAN_NUM_THREADS 4, SWARM_MEM_MAX 48G default, CARGO_BUILD_JOBS 12,
  LANE_POOL_ENV=/home/hbox/pool/pool.env. Every build is `swarm-build`.
- Pool /home/hbox/pool (t1..t9, packages-3a3779933df4 read-only, LAKE_ARTIFACT_CACHE=false). Lane recipe:
  `t=$(lane-tree acquire SEAT origin/BRANCH); cd $t; scripts/pipeline/lane-check FILE...`; native: `lane-tree native
  SEAT`, then `scripts/pipeline/native-loop SEAT BASE LABEL`; `lane-tree release SEAT` when done.
- Disk: / is 455 GB with 78 GB free (10-31 17:55). Removed at the root's word (log integ/ci-rm.log): 52 old builder
  and integrator gate worlds in /ci (22.4 GB; kept the current round 9dc9c1, every dir a running process names, and
  apps-hermes' qualify worlds j-ar*/sb*/wb*/hbA), and the retired clones perf-apps (8.1 GB) and iter-speed (7.7 GB;
  its pushed branch kept, the old toolchain diff in integ/saved-iter-speed-src.diff). app-reds-cont stays (apps-hermes
  runs ar-cycle.sh from it). Still unowned in /ci: dp-*1029 (10-29, demo-path worlds, some still running). integ-build
  stops below 25 GB; no new data on /tank.

### dregg-build2: obend's now; minidregg does not use it
- Stopped 10-31 evening: the dry builder's round 997eba977 (pgid from builder.pid, mid-gate), its gate worlds (19, by
  PID, log /srv/integ/orphans-stop.log), the GitHub relay, the hotswap-test world (`run.sh stop`); build-loop's pool
  tree released. Setup stays for obend: user build, /srv/pool, /srv/integ, swarm-build, earlyoom, fail2ban, the deploy
  key ~/.ssh/minidregg_deploy (kept until ember says otherwise). Seats were told to release their bb2 trees.

### The builder
- `scripts/pipeline/builder`: per new main tip, `scripts/pipeline/integ-build` (now in the repo: rust-check, host,
  consent, rust, pack, umbrella-tree, rerecord), then scripts/pipeline/gate, REDS.md, green. BUILDER_ROOT
  is set by the box's builder-run.sh (hbox: /home/hbox/lanes/integ).
- eb4b7e7b2: a round no longer waits for its umbrellas. integ-build frees src once the umbrella tree has synced, the
  next round starts, and REDS.md carries `umbrella-tree running` (a red) until the umbrellas end and it is rewritten.
- 3ef7de9ac: umbrella-tree starts with `9>&-`. It had inherited build.lock, so round 960da1d8 stopped and published six
  "did not run" reds. A held lock (integ-build rc 75) now defers the round, with nothing published. REDS.md has an owner
  column, and a composed red is one row per failed phase. The gate's edge is dregg-infra 3ddd90f (the per-world
  certifier for composed residents; integ/dregg-infra-3ddd90f).
- f1d2d3bbb: the builder starts every child with `8>&-`. The round subshell, the gate and its rerun had inherited
  builder.lock, so integ-build, the umbrella tree and a kept gate world's `mini line-resident` (/ci/c-9dc9c1) held it
  after the builder stopped. Builder 1557758 (pre-3ef7de9ac) stopped 18:03 EDT at the root's word; last-built reset to
  9dc9c138 (960da1d8 and 60f43c43 only deferred), so the tip gets a real round. integ/relaunch-builder.sh (pid file
  relaunch-builder.pid) waits for the 9dc9c138 umbrellas (1685491), stops c-9dc9c1's residents with its own
  stop-residents.sh, then starts builder-run.sh (which writes builder.pid itself); each step is in COMMANDS.log.
- green is 83e926874 (batch 4) until a live round passes. The first live hbox round rewrites REDS.md whole.

### Seam 1 (codec tags): on main (f2002e589)
- The 12 named tags are in Compiler/PersistedCodecTags/Core.lean; the 645-tag census (Compiler/PersistedCodecTags.lean)
  is imported privately by DurableCheckpointCodec alone, and persistedCodecCorpus is @[no_expose]. The manifest is
  byte-identical and StoreEpoch.current is unchanged.
- Measured on dregg-build2 (pool tree, one census-tag edit, `lake build Host.Main`, 16 threads): main 365 modules,
  447 s; with the seam 4 modules, 95 s. The epoch corpus still moves on a census edit (28,604 -> 28,610 bytes).
- FORMAT batch (privacy a3f7fce75cd3e4e49, host-execution a24974e84d3c540d1) told to rebase onto it.
- Seams 2 and 3 (StoreCodec, Theory.Store, WorldRoot) only if a measured edit rate makes them pay.

### Build speed: done and on main
| change | effect (measured) |
|---|---|
| e9d1c6fc8 lake-threads: Lake's own LEAN_NUM_THREADS = 2 x seats | batch 3 ran exactly 2 compilers; now up to 12 |
| b833dd9c9 + cb49daa63 module-cost (closed cSHAKE256 digests not kernel-evaluated) | Evaluator 197->19 s, DurableIndex 237->12, PayEnrolReceiver 178->10 |
| host stage | batch 3 2,476 s -> batch 5 1,005 s (critical path 1,417 -> 569 s, 61 modules deep) |
| ee7a25ca7 + 0eab28db7 Mathlib import trim, tower split | Host.Main Mathlib modules 2,847 -> 1,423 |
| 0f67c94b7 unrecorded module = 1/3 of seats | batch 6 sat idle 1,471 s behind an all-seats waiter |
| 7800d3199 + 697db7664 native-loop | Lean change -> native host candidate 408 s (was ~48 min) |
- Next levers: per-compile import tax; path depth (the Application* chain); the consent companion's fixed ~116 s.

### Hot-swap
- `lane-build.sh overlay BASE PARENT LABEL ROLE...` / `package.py --overlay` (on main): an overlay candidate, whole
  build families only, named by a 12-hex id, every pin re-emitted.
- `LANE_DIR=LANE scripts/pipeline/hot-swap --state STATE [--hermes-root ROOT] LABEL ROLE...` (on main): overlay on
  BASE's filesystem (the candidate STATE runs), `run.sh stop`, `run.sh upgrade` to the overlay manifest, the Hermes
  root `--rebind` when grainRuntime/grainProviderBridge move, `run.sh start`, one line in STATE/hot-swaps.jsonl. A
  unit-supervised Store is refused (stop and start it by its unit: infra's kept-world tooling).
- Run on dregg-build2 2026-10-31 19:40: world /srv/worlds/hotswap-test on 76511e768bbc, grain-runtime rebuilt in
  /srv/lanes/hotswap (`lane-build.sh rust --crate grain-runtime`, 55 s), swapped as overlay 5ae41015cd71
  (grainRuntime + grainProviderBridge; SHA256SUMS clean; provenance .overlay names base, roles and source tar; Hermes
  root /srv/hermes/root-76511e768bbc rebound). Stop to serving again: 8 s. Overlay own disk 141 MB, the rest links.

### persvati (`ssh persvati-remote`, ember's machine): quiet measurement box
- /home/ember/mdpool: a 4-tree pool at 43995c7f (793 warm modules). Measurement only; no lane builds.


## Seams needed
- infra (aa72653a8ce442178): the kept-world rebind tool; ship.sh accepting `.overlay.id`; the gate's forge half from dregg-build2.
