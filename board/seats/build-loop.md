# Seat: build-loop

Agent: a6c58cb72b0764dbb (ex iteration-speed lane; inherits the retired integrator's mechanical role)
Owns: build scripts (`scripts/build-native-host.sh`, `deploy/candidate/{lane-build.sh,package.py,lib.sh}`), the
pool (`scripts/pipeline/{lane-tree,warm-link,umbrella-tree,native-loop}`), the builder (`scripts/pipeline/{builder,integ-build}`)
and `board/REDS.md`, the `green` ref, the build box dregg-build2 and its pool, the persvati pool, import seams, outside PRs (akapug).
Quest: dregg-build2 as the primary build box with the unattended builder on `main`; persvati as the quiet measurement
box; seam 1 (codec tags) landed; the hot-swap command; keep making the Lean build and the native inner loop faster.

## State (2026-10-31 19:00, present tense)

### dregg-build2: the build box (hbox is down, may not come back)
- Hetzner ccx53, fsn1, 2.31.77.40: 32 dedicated cores, 122 GB RAM, 564 GB NVMe root (27 GB used), Debian 13. About
  EUR 1/hour, approved by ember. Root: `ssh dregg-build2` (key ~/.ssh/id_portable). Lanes: `ssh bb2` (user `build`,
  same key, no sudo).
- Hardening: sshd key-only (PasswordAuthentication/KbdInteractive off, PermitRootLogin prohibit-password, MaxAuthTries 3),
  fail2ban sshd jail (systemd backend), earlyoom (prefers lean/lake/cargo/rustc/cc/ld, avoids sshd/systemd/fail2ban).
- Containment: `swarm-build` (scripts/burst/swarm-build, named scopes) under the user swarm.slice, MemoryMax 100G and no
  swap. The per-build cap is SWARM_MEM_MAX (default 48G). MINIDREGG_LEAN_SEATS=20 at /srv/seats is the box-wide cap on
  real Lean compilers. CARGO_BUILD_JOBS=12. All of this is in /home/build/.minidregg-env, sourced by .profile and .bashrc.
- Set up by `scripts/burst/remote/root.sh --role lane --user build --no-data-disk --slice-pct 82`, minus its sudoers
  line, plus the hardening above. Then elan with v4.35.0, Rust nightly-2026-06-21, a bare blob:none clone
  /srv/git/minidregg.git, and the seed /srv/lanes/main/src: Mathlib from cache; mini-kernels 13 s; Host.Main from cold in
  448 s (2,510 jobs).
- Pool /srv/pool: 8 trees t1..t8 at ffa7a77f, warm (1.6 GB own each), packages-3a3779933df4 read-only (7.3 GB).
  pool.env: LANE_POOL_WARM=/srv/lanes/main/src, LAKE_ARTIFACT_CACHE=false. Verified: acquire, then `lane-check
  Kernel/RoomBirthGate.lean`, takes 15 s.
- Lane recipe: `ssh bb2; t=$(lane-tree acquire SEAT origin/BRANCH); cd $t; scripts/pipeline/lane-check FILE...`; for a
  native host, `lane-tree native SEAT` then `scripts/pipeline/native-loop SEAT BASE LABEL`; finish with `lane-tree release SEAT`.
- The box holds no GitHub write key: lanes push from the Mac (or `git fetch ssh://bb2/srv/pool/tN HEAD`). The builder
  needs one to publish REDS.md and move `green`; until then it runs with BUILDER_DRY=1.
- Disk: everything under /srv. integ-build keeps one generation of old outputs and 6 candidates (plus green's).
- The gate runs here: scripts/pipeline/gate (408962f1d) with BUILDER_ROOT=/srv/integ, GATE_RUNS=/srv/integ/ci,
  WORLD_UP_LOCK=/srv/worlds/world-up.lock (inputs staged in /srv/integ: dregg-infra-e29997d, pw, j14-hroot, j14-data,
  j14-secrets, spk-cache). First run at 76511e768: all phases ran; every red is the consent-provider exit 86c9dbddb fixes.
  The builder runs as /srv/integ/builder-run.sh (those knobs, BUILDER_DRY=1, main's builder). Not yet: SPK/grain-world
  root setup (after the pool, per root).
- The shared packages are read-only; lake replays write missing .hash files, so the pool once refused six Mathlib
  replays (EACCES). Fixed 19:57 by one writable `lake build Mathlib ...` over the shared copy, then re-locked
  (~/mlhash.sh): run it again after any package re-seed.
- Candidate transfers: only by `scripts/pipeline/candidate-transfer SRC_HOST:DIR DST_HOST:DIR NAME` (a97b13c4a). It copies
  into DST/.incoming-NAME, verifies SHA256SUMS (and fixtures/, and READY) on the destination, then renames into place, so
  no reader of candidates/ ever sees a partial candidate. Never copy into candidates/NAME directly.
- hbox b9450147f candidate: transferring that way (from the Mac, PID file in the build-loop scratchpad cand-copy.pid; hbox
  uplink ~100 KB/s). It exists in /srv/integ/candidates only once complete and verified.

### The builder
- `scripts/pipeline/builder`: per new main tip, `scripts/pipeline/integ-build` (now in the repo: rust-check, host,
  consent, rust, pack, umbrella-tree, rerecord), then gate15.sh when the box has it, REDS.md, green. BUILDER_ROOT
  defaults to /srv/integ.
- green is 83e926874 (batch 4). The last REDS.md (hbox, main 997905c0) has 6 reds.

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

### hbox: back (a network outage, not a crash); secondary build box
- Its builder, integ tree, pool t1..t8 and the box-local gate15.sh are unreachable.

## Seams needed
- infra (aa72653a8ce442178): the kept-world rebind tool; ship.sh accepting `.overlay.id`; the gate's forge half from dregg-build2.
- root or ember: a GitHub write key for build@dregg-build2 (the builder's REDS.md and green pushes).
