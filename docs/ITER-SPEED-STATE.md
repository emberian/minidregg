# Iteration-speed lane: state (present-state; rewrite whole, never append)

Agent: the iter-speed lane (2026-10-31). Order of work, from ember: step 0 the Lean bump, then the umbrella
second tree (integrator's ask), then (1) interface seams, (2) lane-tree warm pool, (3) hot-swap. Integrator:
aeb671706eb3f70d7 (send shas there). Hot path: a86738fc1dfae6429. Private cells: a74ad8d84ada5627a.

## Step 0: Lean v4.30.0 -> v4.35.0: final, building on hbox

- `cdb399b47` on `origin/lane/iter-speed` (FROZEN: one commit on main 929eac696; the commit message lists the
  324 pin changes, the 187 scoped respectTransparency options, the decide replacements, the native_decide
  self-test, the `alias` rename). Kimi review clean. Mac: whole closure green except the two Native fixtures
  that are red on main itself (private-cells codec change; the proofs lane re-records them).
- HOLD LEAN in force. The integrator builds cdb399b47 ALONE in hbox integ/src (started 22:03 10-30; Mathlib
  rebuilds on 4.35 there, so the host stage is long), moves main to it on a green host stage, lifts HOLD LEAN,
  then cuts the batch `integ/batch-435` (bump + staging + import-boundary refactor + hot-path snapshot batch).
- The Mac tree `/Users/ember/dev/minidregg-lanes/iter-speed-land` is LENT to the integrator's import-boundary
  sub-agent (branch lane/import-boundary there, a build running). Do not switch branches or build there until
  the integrator releases it. Commit this lane's work by plumbing (a temporary GIT_INDEX_FILE), never through
  that tree's index.
- What 4.35 broke and the fixes: in the bump's commit message (and the previous version of this file on
  lane/iter-speed).

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

## Lane pool (lane-tree): fixed; hbox pool next

- `scripts/pipeline/lane-tree` (7143777f0): the empty-lookup acquire bug fixed (held_by returned its last
  test's status under set -e); an empty pool says so; init writes pool.env, resolves the --reference repo
  absolutely, warms every tree by warm-link; `LANE_POOL_WARM` (acquire links a main-current tree's newer
  outputs into the tree it hands out) and `lane-tree warm`; macOS (python flock, shasum, clonefile copies,
  symlinked packages by target, `$HOME/pool/pool.env`). Tested on the Mac against a scratch pool.
- hbox NVMe pool: tools staged in `/home/hbox/pool-tools/` (lane-tree, warm-link, init-pool.sh). Run
  `/home/hbox/pool-tools/init-pool.sh` (as hbox; PID file /home/hbox/pool-init.pid) once COMMANDS.log shows
  `MINIDREGG umbrella cdb399b477ea rc=`: pool `/home/hbox/pool` (t1..t3, repo.git, packages-<key> real copy
  7.8 GB read-only, lake-cache, LANE_POOL_WARM=/home/hbox/lanes/integ/src). This is the ONE read of integ/src
  in that window: tell the integrator "clear" when it ends (it holds its batch build until then), and tell hot
  path (it will `lane-tree acquire hot-path origin/lane/hot-path-cold`).
- Mac pool: after the integrator releases iter-speed-land (it is the only built 4.35 Mac tree).

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
