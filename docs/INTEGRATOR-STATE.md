# Integrator state

Present-state record of the integration lane, rewritten whole when its shape changes. A successor reads this, then
`hbox:/home/hbox/lanes/integ/COMMANDS.log` (every build stage, gate verdict, sweep, world teardown and process stop, one
line each). History (the 10-30 rehearsal-3 smoke, the hbox disk pause, the Hermes and apps diagnoses) is in this file's
git history (e5dfc3ddb and earlier).

## Now (2026-10-31 03:40 EDT)

- main = cdb399b47 (Lean v4.35.0 bump). Candidates kept ($I/keep): be4ef7510 (forge ship), cdb399b47, 35737eac4,
  eca98bde7 (batch 2), eca98bde7-resvar1/-resvar2 (hotpatch copies, hotpatch-candidate.sh).
- **Batch 3 a4cb65af3 BUILDING** (integ-build5, 03:38): eca98bde7 + resident /var fix 486f0196f + astra follow-up
  19b7ab1de (dev pin, same-device, exact-size recheck at START; quota-change serialisation stated as open in VOLUMES.md
  G4) + ingest scratch 45091c14e + signed-identity c730fd3ea + bend responseType 32a7f0fc0 + web lifeline 4928d9a77 +
  bend show + H3/H4 + hot-path rows 4/9/13, consent option A, Pred.Frame + private-cells hiding goals and Materialized
  Aux (c75e4ac7a) + lane-tree fixes + fixture re-record 2a995c2e6. Waiter armed on READY.
- **Batch 2 eca98bde7**: gate13 tour 73/73, enrol PASS; apps red was the resident /var check. Hotpatch 2
  (eca98bde7-resvar2 = all spk-host crate bins from 19b7ab1de, gate14 HARNESS=19b7ab1de): j14-apps PASS 5 rows; composed
  rooms/churn/documents/apps/connector/store-restart PASS, residents UNKNOWN (hbox can't judge; forge decides);
  flatness-get PASS, flatness-submit FAIL. Umbrellas: Native fixtures (re-recorded 2a995c2e6) + NEW TokenCensus red
  (ConsentAnchor.Anchored.mk L1 witness; hot-path fix b70a547c8, not yet on staging).
- Hotpatching between cuts (ember): Rust fixes are overlaid as a hotpatch candidate copy
  (`hotpatch-candidate.sh BASE NAME bin=path...`, re-pins SHA256SUMS, manifest, provenance), then gate14 with
  HARNESS=<staging sha> (overlays scripts/ and deploy/spk-host) and SUF/PHASES. Build the crate's whole bin set (spk-host
  crate = spk-host, spk-browser-proxy, mini-spk-broker, mini-spk-volume-helper) or the world mixes binaries.
- Sweep bug fixed 03:40: the 03:36 sweep matched by prefix and removed hot-path's hotpatch copy and batch 2's gate roots;
  sweep.sh now skips non-sha candidates and shields shared prefixes.
- hot-path a8e4317c9e1574ca5: slot projection fix measured (submit CPU 116/874 -> 54/280, propose 28/231 -> 14/50) plus
  contentLawDecidable over cached support (f7da550af) in flight; one sha after re-bench.
- FORMAT batch (later, one genesis): hot-path row 11 (checkpoint carries session indexes; Store epoch) + private-cells
  KeptCell option (b) (Aux cache in Materialized; Theory/CellStateAux.lean statement 18e049691 audited sound, conditions
  sent) + the fixture re-record.
- hbox disk 72 GB free (02:24) after the root-approved sweep (hpc, hot-path, scout, hp-codex, hb-dav-1..3, old source
  tars, gate worlds; all logged). Host-level state app-reds added on hbox: /var/lib/mini-vars-backing (loop prjquota ext4
  from /tank/lanes/vars-backing.img, NOT in fstab: after reboot `sudo mount -o loop,prjquota /tank/lanes/vars-backing.img
  /var/lib/mini-vars-backing`), /etc/mini-spk-volumes/{vars-backing,ingest-scratch}, /tank/mini-ingest.
- Hard-link hazard (twice tonight): never `cp -al` a .lake that another tree builds in (lake writes .trace and
  setup.json in place). Lanes build in the lane pool (/home/hbox/pool, lane-tree; LANE_POOL_NO_WARM=1 while integ builds;
  pool.env sets LAKE_ARTIFACT_CACHE=false) or their own unshared trees.
- integ-build5 overlap: build5 releases build.lock at READY, so a second build can start while the first's umbrella-tree
  runs; the second's umbrella-tree then finds TREE.lock held. Launch the next build only after "stage rerecord" of the
  previous one, or run its umbrella-tree by hand after.
- Rehearsal 3 stays on be4ef7510 on forge. Hermes ask needs the OpenRouter pool key (ember's decision).

## Lanes (send shas; name every new candidate to infra and the explorer)

The session was pruned 10-30 evening; the root re-adopted the veteran lanes with `cv adopt` (their old ids work).

| lane | agent | owns |
|---|---|---|
| hot-path | aa2905fee8ef847d1 / a8e4317c9e1574ca5 (distilled; owns flatness reds; rows 4/9/13 at the shared seam; row 11 FORMAT with private cells: one batch, one genesis) | consent snapshot resume (provider starts from the Store checkpoint, admits the suffix; anchors survive ships; deletes CONSENT-OWN own-base, superseding staging batches 2-3) + JDV fix 1a4f3a623 (was 2dfa8372e), ONE sha on cdb399b47; the law-17 perf queue |
| infra (fresh) | aa72653a8ce442178 | Firecracker (or similar) lite VM inside the forge demo host, then the fresh ship; forge composed container |
| app-reds | ad85d40779880420c (volume/custodian/apps; a17f4172949caca14 on resident /var checks, Hermes items) | the no-loop volume helper (bind-mounted directory + project quotas, the real fix), then op66-plan and the rest |
| private cells | a30875aaf31364697 (distilled; KeptCell option (b) Aux cache in Materialized, statement first with astra, pool tree, FORMAT batch with hot-path row 11, one genesis) | O(log n) blinded-cell hiding (docs/RATCHET-LOG-DESIGN.md) |
| iteration speed | ab2786fe1172f5683 | the bump cdb399b47, umbrella-tree.sh (second warm tree for integ-build5) |
| explorer | a3e5d6dbcd68e616c | perf and behaviour probes on candidates; docs/EXPLORER-FINDINGS.md |
| demo-reds (sub-Opus of this integrator, done) | a64c387f3e638aa63 | G3-G6 (lane/demo-reds 8982fa265); left: no bend top-up verb, `bend show` prints "phase ?" after an activity ends |

No proofs or scout lane: the integrator owns umbrella reds and the fixture re-record.

## Rulings in force

- **Import boundary** (root, 10-31, under the law that kernel effects come from the Effects/ derivation engine): Effects is
  the generator whose outputs Kernel and Compiler consume, so Effects sits BELOW Kernel and Compiler. Effects may import
  Theory and Lean core; Kernel/Compiler may import Effects (the derived Effects.Revival.Hosted* descriptors); Effects never
  imports Kernel, Compiler or Host. On main the script is red: 16 edges (Effects -> Theory/Lean, Kernel/Compiler -> Effects)
  plus the real cycle Effects -> Kernel/Compiler (EffectSpec, Revival.Engine via Tower256ConcreteBackend's StreamCodec,
  Statements, ActivityStatements, CommutingProofs). Design in flight: generic algebra (Compiler.Signature, NatDigits255Fast,
  the StreamCodec nucleus) moves down into Theory; the keystones over the deployed kernel (Revival Statements/Content/
  Prepare/HostTeeth/Commuting/Activity, EffectSpec's moveEffect instance) move up into Kernel; names unchanged.
- **Consent** (root, 10-31; relayed to hot-path separately): no validity proofs. We trust the storage device (that is the
  threat model, not "operator trust"). Consent providers resume from a sealed snapshot; anchors must survive ships.
- **Demo**: a lite VM inside the forge demo host (infra); the volume helper's no-loop design is the real fix (app-reds).
  Land both as they come. This settles the 10-30 grain-volume design blocker (loop mounts refused in the userns container).
- Candidate cadence: cut only for meaningful batches or deep Lean changes; Rust fixes overlay onto kept worlds between cuts
  (re-pin manifest + SHA256SUMS + Hermes root together on a hot-swap: overlaying a pinned role binary alone breaks
  store-entry's manifest-digest check on the next Store restart).
- Deploy-script fixes keep a candidate's verdicts (no composed rerun); a Rust fix means a new cut.
- Flatness (law 17) is reported, never blocking.

## Lean 4.35 bump (what lands, and how)

cdb399b477ea76e8f8f50e956623f58b5b3412ec: one commit on main 929eac696; Mac closure green (only the two Native fixtures red,
as on main); 324 pin sets changed only within propext/Classical.choice/Quot.sound; 187 scoped
`backward.isDefEq.respectTransparency false`; decide -> `decide +kernel`/`rfl` (Theory/ExceptDecidableEq.lean); Kimi: no
statement changes beyond two meaning-preserving ones, no sorry/axiom, only native_decide added is the self-test
(TokenCensus/NativePinSelfTest.lean, refused by #assert_axioms by name). On a green host stage: push main = cdb399b47, merge
main into staging (integ/batch-435 already is that merge), lift HOLD LEAN, tell the lanes to rebase Lean work.
Fixtures: the Native fixtures re-record from the batch candidate (integ-build4's rerecord stage; `authority-differs` needs a
person's Authority-Change commit).

## Build, gate and sweep (hbox, as user hbox, /home/hbox/lanes/integ)

- `integ-build4.sh SHA` (SEATS MEM JOBS env): rust-check, host, consent, umbrellas (non-fatal; --unshipped targets
  Fixtures ObjectiveProofs CensusChecks, beside rust), rust, pack into candidates/<sha> -> READY, then the rerecord stage.
  Holds build.lock for the whole run. Launch as one sequential job with its PID in build.pid:
  `nohup setsid bash -c "./integ-build4.sh SHA; ./umbrella-minidregg.sh SHA" > build.out 2>&1 & echo $! > build.pid`.
  Never launch while build.pid is alive; never use queue-build.sh (stale queues rebuilt old shas).
- `umbrella-minidregg.sh SHA`: the whole `Minidregg` umbrella in the same tree after the build.
- `gate13.sh SHA` (current; gate12 + TEST_PROVIDER from $C/fixtures/ + the sweep after the verdict): tour + composed +
  enrol + j14-apps + flatness. Env: EDGE_REV=69c17a3 JWORLD_MANAGEMENT=distinct|sponsor KEEP_WORLD=1 PORT=..
  JWORLD_ROUTE_FRONT_PORT=.. (unique), PHASES subset, HARNESS=<sha>. j14 inputs staged once (j14-hroot, j14-data,
  j14-secrets); runs under /ci. Never edit a gate script in place; number the next one. hbox composed cannot judge
  residents/restart (no root): infra's forge composed container does.
- `sweep.sh [--dry]` (lane trash, ember 10-31): for every candidate two or more behind the newest READY one, removes
  $I/gate-<sha8>* and /ci/{t,c,e,f,j}-<sha6>*; removes candidates/<sha> beyond the newest KEEP_CANDIDATES (3) READY; and
  old/ build outputs except the newest two sets. Skips shas in $I/keep (be4ef7510 the forge ship, cdb399b47 the bump,
  35737eac4 the batch) and anything a live process names (cmdline, cwd, exe, fds) or a /ci world's inputs name (logs SWEEP
  IN-USE; read the holders' command lines and stop by exact PID only if they are our own stale leftovers). Logs sizes.
  Runs at the end of every gate13. 10-31 00:00: 27 candidates + old/packages-430 = 22.8 GB; f34b0309 left (demo-path
  leftovers still run its binaries).
- Kept world teardown: the candidate's scripts/spk-platform/world-down.sh RUN/inputs, then
  dregg-infra-69c17a3/edge/mini/journey/jworld-scratch.sh down RUN/w (XDG_RUNTIME_DIR and DBUS set); log DOWN.
- Mac landing worktree /Users/ember/dev/minidregg-lanes/integration-r2 (branch integ/batch-435; staging is pushed from
  it). CARGO_TARGET_DIR=/Users/ember/dev/minidregg-lanes/target-integ for filtered Mac tests (apps_front connector test
  fails only inside the apps:: group; SUN_LEN socket fixtures fail on macOS temp-path length: both known).
- Market adopt set: dregg-forge:/var/lib/spk-fresh/qualified-2026-10-29/out (22 packages); procedure in git history.

## Trash swept 10-30 22:05-22:08

Stopped by exact PID (command lines read: orphaned `mini web --body` JWF-dry trees with their codec/consent/store children,
configs under /ci/t-<sha6>): t-0feb2b, t-41590f, t-4e5faa, t-5f18b9, t-8fd079, t-91a307, t-994e36, t-a9d4ec; those dirs and
their /run/user/1000/jwf-m-* removed. First sweep: 119 dirs, 13.0 GB. Left alone, not ours: demo-path lane leftovers
(`/tank/lanes/demo-path/run-1029/.../mini web` trees for /ci/dp-*1029, and integ-candidate f34b0309 PID 696641 under
/ci/dp-t1029), b39563f1 `mini-web` PID 3004317 (a 10-29 journey's front, our candidate: stop on ember's word), /ci/x*
(explorer), /ci/scout, /ci/hpc, /ci/ar-*, /ci/hb-dav-*. Candidates/ holds 16 GB (30 x ~524 MB) of superseded candidates:
not swept (ember's word names gate roots and lane worlds only).

## Candidates

| candidate | state |
|---|---|
| be4ef7510 | GATE GREEN: rehearsal 3 ship (kept, $I/keep) |
| 06665f052 | READY; bin/ identical to be4ef7510 (scripts only) |
| 7d90da717 | READY host stages; private-cells receipt-leak (codec epoch); Fixtures umbrella red; = main minus two scripts |
| cdb399b47 | BUILDING (the bump, alone) |

## Open reds and owners

- Native fixtures stale against 7d90da717's event ids (rerecord.sh said `unchanged`: it keys on front-end identity only).
  Integrator: re-record from the batch candidate and make rerecord.sh detect stale data (replay or codec/event-id digest).
- Demo apps install: op66-plan "launch BEGIN authorization, descriptor or action shape refused" for EtherCalc and Etherpad
  (not Davros; differences: date-style app version, one `modify` permission with no roles, the interface schema): app-reds.
- Hermes ask with no reply ("controller service is unavailable", now named by 4bee4b608): infra re-checks on the VM world.
- JDV row 140 (Host's EOF clean end reopens the Store): fix 2dfa8372e on lane/hot-path-cold, unchecked; hot-path to confirm.
- flatness-submit (law 17): reported; hot-path, blinded-cell part to private cells.
- scripts/check-proof-hygiene.sh fails on scripts/oracle-cold-replay-budget.lean:55 (bare `#print axioms`); PredCompile.lean:832
  comment cites the wrong theorem name: integrator (proofs lane gone), in a batch.
- fleetsign 1/100 under full parallel load (attempt plan.frame missing): unconfirmed; no scout now.
- Open question for app-reds: a market refusal recorded under a since-changed host config should be re-sweepable by a named
  operator verb (`apps sweep`) rather than records moved by hand.

## Rules

Named-file commits with `git commit -F <file>`; never `git add -A` or `git stash`; filtered tests only; every detached
job has a PID file and is stopped only by it (our own stale leftovers may be stopped by exact PID after reading the command
line); lake/git on hbox as hbox, never root; swarm-build caps summing under ~100 GB; one sequential job per build tree;
never search from / or ~; disk pressure = stop and tell ember.
