# Seat: build-loop

Agent: a6c58cb72b0764dbb (ex iteration-speed lane; inherits the retired integrator's mechanical role)
Owns: build scripts (`scripts/build-native-host.sh`, `deploy/candidate/{lane-build.sh,package.py,lib.sh}`), the
pool (`scripts/pipeline/{lane-tree,warm-link,umbrella-tree,native-loop}`), the builder and `board/REDS.md`, the
`green` ref, hbox `/home/hbox/lanes/integ` (the dead integrator's tree), the hbox and persvati pools, import seams,
outside PRs (akapug).
Quest: the unattended builder on `main`; persvati as the quiet measurement box; land or answer akapug's PRs
(#18, #16, #14, #7); keep making the Lean build and the native inner loop faster.

## State (2026-10-31 13:20, present tense)

### The builder: NOT written yet (next step 1)
- Ingredients on hbox `/home/hbox/lanes/integ`: `integ-build6.sh SHA` (host stage via lane-build, then
  `src/scripts/pipeline/umbrella-tree`, then `rerecord.sh` in umbrella-src), `gate15.sh`/`gate14.sh NAME`
  (PHASES subsets of tour composed enrol j14; HARNESS=sha overlays scripts/ and deploy/spk-host), `sweep.sh`
  (leaves any candidate whose provenance has `.overlay`), `COMMANDS.log` (event log), `candidates/<sha>/READY`.
- Batch 9 (997905c0b, the integrator's last): READY 13:00; gate verdict FAIL 13:15 on the flatness rows
  (flatness-submit/get/run rc=1, logs /ci/f-997905/*.log); integ-build6.sh (pid 3311469, build-b9.pid) still
  running its umbrella-tree (pid 3686555, umbrella-src.pid). Let it finish; its reds go in REDS.md.
- Plan: one script `scripts/pipeline/builder` (in repo), run detached on hbox with a PID file: loop on
  `origin/main` tip; if new, integ-build6 equivalent (host stage, umbrella-tree, rerecord) then gate15 rows (tour,
  enrol, j14-apps, composed; forge composed via infra); write `board/REDS.md` (per red: stage, error text, first
  divergence, reruns?, same place?, suspect commits = `git log green..tip -- <files of the red>`, owner from
  board/seats/*.md "Owns:"); `git push origin SHA:refs/heads/green` when all green. Commit REDS.md by plumbing.
- After it runs: delete docs/INTEGRATOR-STATE.md, branch integration/staging, fixture-regen/acc7cfa03fac (land its
  rerecord on main first if still wanted: diff it against main's Fixtures/).

### Build speed: done and on main
| change | effect (measured) |
|---|---|
| e9d1c6fc8 lake-threads: Lake's own LEAN_NUM_THREADS = 2 x seats | batch 3 ran exactly 2 compilers; now up to 12 |
| b833dd9c9 + cb49daa63 module-cost (closed cSHAKE256 digests not kernel-evaluated) | Evaluator 197->19 s, PayEnrolReceiver 178->10, PayEnrolV2 154->11, PayCellDomain 119->9, CADR 108->6, PayObservation 106->4, ResourceTransaction 130->37, DurableIndex 237->12 |
| host stage | batch 3 2,476 s -> batch 5 1,005 s (critical path 1,417 -> 569 s, 61 modules deep) |
| ee7a25ca7 Mathlib import trim (+ Mersenne127 Pratt certificate) | Host.Main Mathlib modules 2,847 -> 1,816 |
| 0eab28db7 tower split (+ Air import) | 1,816 -> 1,423 Mathlib modules, FieldTheory 30 -> 0 |
| 0f67c94b7 unrecorded module = 1/3 of seats | batch 6 sat idle 1,471 s behind an all-seats waiter while an umbrella held seats |
| 7800d3199 + 697db7664 native-loop | Lean change -> native host candidate 408 s (was ~48 min) |
- Not split, by decision: Host.Json (natural seam saves only 10-15 s; needs 25-51 private helpers public).
- Next levers: per-compile import tax (~1-2.5 s x 61 path modules); path depth (the Application* chain);
  consent companion's fixed ~116 s (verification + link) in native-loop; off-path heavies LegacyContentCarry 53-93 s,
  ProviderRoute 47-64, AgentGrain 42-51, ObjectiveActivity 49.
- Waterfall (samth): ported to 4.35 (one line), at hbox:/home/hbox/lanes/module-cost-scratch/waterfall; verdict:
  adopt only for small structural lemmas over inductives; 10-100x slower than hand proofs; not in the manifest.

### Seam 1 (codec tags): unfinished
- origin/lane/seam1-epoch 1f71e625b (stale base 0e59f8891): 12 named tags to Compiler/PersistedCodecTags/Core.lean,
  the census imported privately by DurableCheckpointCodec, persistedCodecCorpus @[no_expose]; no statement change.
  Baseline: a census-tag edit rebuilds 478 Host modules (Mac 975 s; hbox 1,837 s pre-module-cost). After-probe and
  the staleness teeth (epoch must move after a tag edit; three ways) never reported: agent aef0f730d422d6aa7
  (Mac tree /Users/ember/dev/minidregg-lanes/iter-speed-land, on that branch). Next: rebase onto main, measure
  on a pool tree, land on main.

### Pool and native-loop
- hbox pool `/home/hbox/pool`: 8 trees t1..t8, packages a read-only real copy (packages-3a3779933df4), repo.git a
  blob:none clone of GitHub, pool.env (LANE_POOL_WARM=integ/src, LEAN_NUM_THREADS=4, LAKE_ARTIFACT_CACHE=false),
  object cache `/home/hbox/pool/object-cache` (177 MB), lanes dir `/home/hbox/pool/lanes/<lane>`.
  `lane-tree acquire` waits (LANE_POOL_WAIT_S 3600), lease TTL 12 h, `native` gives a tree its own package copy,
  `tripwire`, `gc`; trees() lists only t<N> worktrees. Tools deployed in /home/hbox/pool/bin.
- native-loop: `scripts/pipeline/native-loop LANE BASE_CANDIDATE LABEL` from the lane's pooled tree (commit
  first, hold the lease). Measured t6: host 310 s (130 modules, 800/801 objects cached), consent 88 s, overlay 10 s.
- Hot-swap: `lane-build.sh overlay BASE PARENT LABEL ROLE...` / `package.py --overlay`: whole build families only,
  dir named by 12-hex id = sha256 of provenance (minus id and stamps), `.overlay.name` the label. Swap into a running
  kept world (forge) waits on a rebind tool with infra (stop residents, controllers, broker, store; re-derive
  Hermes root, lobby runtime root, broker config, controller registrations; `run.sh upgrade`).
- My scratch on hbox: /home/hbox/iter-hs (0.5 GB cargo target + logs), /home/hbox/pool/lanes/native-loop (960 MB).

### persvati (`ssh persvati-remote`, ember's machine, 24 cores, 83 GB, swarm.slice cap 41 G)
- Everything under `/home/ember/mdpool` (budget ~80 GB; 8.1 GB now; disk 738 GB free). No system-wide change made.
  repo.git (blob:none GitHub), seed worktree at integration/staging 30db01d6 (re-point to main), elan v4.35.0,
  Mathlib cache fetched. Seed build attempt 1 failed: .lake/native/libmini_kernels_lean.so missing; setup2.sh
  (pid file setup2.pid) builds mini-kernels (CARGO_TARGET_DIR=/home/ember/mdpool/cargo-target, the shared Rust
  target) then `lake build Host.Main`.
- hbox reachable from persvati: `ssh -i ~/.ssh/id_boxlocal -o UserKnownHostsFile=/home/ember/mdpool/known_hosts
  hbox@100.64.0.2` (tailscale). Candidate copy + `/home/ember/mdpool/candidate-relocate DIR` (rewrites manifest
  paths, verifies pins): dc61016cb-codec copied (an overlay; copy a 40-hex cut too).
- Scratch worlds: Store-only worlds via a candidate's run.sh need no root. SPK/grain worlds need root setup
  (deploy/spk-host/install-user-world: /usr/local/libexec helper, /etc/mini-spk-volumes, ACLs on
  /usr/local/libexec/mini-grain-bwrap, subuid ranges, /var/lib/mini-spk-worlds): ask ember before doing any of it.
- Still to do: lane-tree init there (2-3 trees, pool.env), native-loop there, announce to seats, then candidates.

### akapug PRs #18, #16, #14, #7: not looked at yet.

## Seams needed
- infra (board/seats/infra.md): the kept-world rebind tool; ship.sh accepting `.overlay.id` as a candidate id.
- explorer: per-action cost rows feed which build-speed lever is next.
