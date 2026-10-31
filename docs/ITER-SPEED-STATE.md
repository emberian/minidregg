# Iteration-speed lane: state (present-state; rewrite whole, never append)

Agent: the iter-speed lane (2026-10-31). Order of work, from ember: step 0 the Lean bump, then the umbrella
second tree (integrator's ask), then (1) interface seams, (2) lane-tree warm pool, (3) hot-swap. Integrator:
aeb671706eb3f70d7 (send shas there). Hot path: a86738fc1dfae6429. Private cells: a74ad8d84ada5627a.

## Step 0: Lean v4.30.0 -> v4.35.0: LANDED

- main = `cdb399b47` (bump READY on hbox 23:54 10-30; the integrator moved main and lifted HOLD LEAN). The
  integrator's batch `integ/batch-435` (bump + staging + import-boundary + hot-path) follows.
- ResearchWip (outside the bump's closure check) under 4.35: `edad15301` on `origin/lane/iter-speed-hosted`
  (16 files fixed, statements unchanged). Still red there and NOT from the bump (API rot, for their owners):
  Kernel/RoomReleaseCurrent, Kernel/JointReservationFunding, Compiler/PortableJointCustodyIO (pre-date the DRC
  verified-ground refactor 2b9956c53/efbac239d) and Compiler/PrivateCircuitAllocationFast.stream_ext (false
  as stated since StreamCodec gained data fields in 58b3ae509).
- The Mac tree `/Users/ember/dev/minidregg-lanes/iter-speed-land` is back with this lane; the seam-1 sub-agent
  works there on `lane/seam1-epoch`. Commit other work by plumbing (a temporary GIT_INDEX_FILE).

## Umbrella stage in a second tree: done, wired in

- `scripts/pipeline/umbrella-tree SHA` on `origin/lane/iter-speed-tools` (2535ea2e1, then 7143777f0); the
  integrator merged both into the batch (staging 5bad63e84) and calls it from hbox
  `/home/hbox/lanes/integ/integ-build5.sh` after READY (SEATS 4, MEM 32G), then runs rerecord.sh in TREE.
  TREE = `/home/hbox/lanes/integ/umbrella-src` (created by the first run, a git worktree of integ/src).
- Mechanism: `scripts/pipeline/warm-link SRC/.lake/build DST/.lake/build`, per module newest trace wins;
  outputs hard-linked, .trace/.hash copied, .setup.json never shared. Safe because Lean 4.35 and leanc write
  .olean/.olean.private/.olean.server/.ilean/.ir/.ir.sig/.c/.o by rename(2) (measured: a rebuilt module's
  outputs split, untouched ones stay shared); Lake writes .trace and .setup.json in place. Tripwire: a
  multiply-linked file written after the sync is reported `RED shared-inode-written-in-place`.
- Mac test at cdb399b47: only the two main-red fixtures red, no tripwire, 3,568 s (TokenCensus 1,859 s; 327
  modules rebuilt because the source tree held outputs of 7 staged files, caught by Lake). Disk, own inodes:
  packages 37 MB, build 1.57 GB, mini-kernels target 59 MB. hbox steady state: 1-2 GB, never a second 12 GB.

## Lane pool (lane-tree): LIVE on hbox

- `scripts/pipeline/lane-tree` + `warm-link` on `origin/lane/iter-speed-tools` (latest 2261c5faa): empty-lookup
  acquire bug fixed, init writes pool.env, every tree warmed by warm-link, LANE_POOL_WARM, `warm`, `tripwire`
  (also run by release), macOS support, partial-clone seeds get a partial pool repo.
- hbox pool `/home/hbox/pool` (created 2026-10-31 00:0x): pool.env, bin/{lane-tree,warm-link}, repo.git
  (blob:none clone of GitHub; integ/src is itself a partial clone), packages-3a3779933df4 (7.4 GB real copy,
  read-only; verified by `lake build --no-build` Mathlib Batteries Aesop Qq Host.Main before copying),
  lake-cache, t1..t3 (each warmed from integ/src at cdb399b47: 1,375 modules, 175 MB own inodes),
  LANE_POOL_WARM=/home/hbox/lanes/integ/src. Init took 29 s after the 24 s packages copy. hbox / 34 GB free after.
- Use: `. /home/hbox/pool/pool.env; t=$(/home/hbox/pool/bin/lane-tree acquire LANE REF)`; `lane-tree release
  LANE`. Never acquire while a build runs in integ/src (acquire reads it). Hot path takes the first tree.
- Mac pool: not yet (the only built Mac tree is in use by the seam-1 sub-agent).

## Seam 1 (next): the codec registry and the Store epoch

Measured on main 929eac696 (static import graph, `scratchpad/graph.py`; Lake rebuilds on the transitive
closure, BUILD-INVERSION-2026-10-28.md):
- `Compiler/PersistedCodecTags` is the most-edited high module (19 edits in 10 days); one edit rebuilds 671
  modules (478 in the Host closure). It holds 657 tags; only 14 are referenced by name anywhere else: the 9
  the epoch/checkpoint code uses (DurableCheckpointCodec), clockWireVersion and
  registry_loaded_and_final_store_cells_v17 (CanonicalCellRegistry), clock_v4 (ClockCell), world_root_v2
  (WorldRoot), the front-end manifest header (ObjectiveBendFrontEndIdentity). The other 643 are a census of
  literals their consumers spell themselves; they matter only to the epoch's manifest.
- The epoch: `StoreEpoch.current`/`persistedCodecCorpus` live in DurableCheckpointCodec (609 dependents). The
  current-epoch definitions are used by: DurableReceiverCore (SeedEpoch.ofBytes, .refusal; 604 dependents),
  DurableServed (seedFrame, SeedEpoch.ofBytes; 577), ConsentAnchor (19), Host.Main (12),
  DurableFastForwardProofs (7), the two Fixtures and scripts.
- Design: (a) the 14 named tags move to an owner leaf (still `@[persisted_codec_tag]` in the same namespace);
  the 643-tag registry becomes the aggregate imported only by the epoch assembly; (b) DurableReceiverCore and
  DurableServed take the epoch as data (a `StoreEpoch` in their config, using the existing `...For epoch`
  forms), and one assembly module above them defines `StoreEpoch.current` and the current-epoch instances,
  imported by Host.Main, ConsentAnchor, DurableFastForwardProofs and the Fixtures. Statements generalise
  (ember 10-28: statements may change); the current-epoch theorems stay by name as instances.
- Prediction: a census tag edit rebuilds ~27 modules (1 in the Host closure) instead of 671; an edit to one
  of the 14 owner-leaf tags still rebuilds that tag's importers' closure. Measure before/after with a real
  build in a pool tree (an edit to PersistedCodecTags, `lake build Host.Main`, count `Built` lines) before
  starting, and continue only if the measured number moves as predicted.
- Seams 2 and 3 (StoreCodec 763 dependents, Theory.Store 1,038, WorldRoot 618) wait for seam 1's number;
  their edit rates are far lower (StoreCodec 8 edits in 10 days, Theory.Store and WorldRoot rare).

## Hot-swap (after the seams)

Rebuild one crate or the Host, swap it into a kept world, rerun one phase. Integrator requirement (rehearsal-3
world): the swap replaces the binary and re-pins it in the candidate's manifest.json, SHA256SUMS and the
Hermes runtime root (`deploy/hermes/build-runtime-root --rebind`) together, atomically, and records the
overlay in provenance; otherwise the Store restart crash-loops on the sha256 check. Ember: hotpatched worlds
between batch candidates.
