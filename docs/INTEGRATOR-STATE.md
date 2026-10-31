# Integrator state

Present-state record of the integration lane, rewritten whole when its shape changes. A successor reads this, then
`hbox:/home/hbox/lanes/integ/COMMANDS.log` (every build stage, gate verdict, world teardown and process stop, one line
each). Older history is in this file's git history.

## Goal and the one blocker

Rehearsal 3 ships through infra (`demo-mini.sh ship` into the forge `demo` container) when the gate is fully green:
tour + j14-apps on hbox gate12, composed (all phases, distinct mode) on infra's forge composed container. Flatness
(law 17) is reported, never blocking (root ruling 2026-10-30: the submit ratchet preimage is ember's decision).
**Gate GREEN on be4ef7510 (2026-10-30 14:46).** Infra's distinct composed c-be4e-d1: rooms, churn, documents, apps,
connector, residents, restart, store-restart all PASS. hbox gate12: tour 73/73, j14-apps PASS (5 rows), enrol-resume PASS,
flatness-get PASS; flatness-submit FAIL (reported, not blocking). Confirmed to infra a104b94c2643e9c5d, which ships
rehearsal 3 from be4ef7510 (demo-mini.sh ship on forge, market adopt set 22 packages) and reports smoke + URL.
Ship status (be4ef7510 on forge, world kept, ssh demo-dry): GREEN ship, pins, health, members, apps bootstrap, reenroll,
grain-world, hermes preflight/route/subjects, seed (rooms, docs, grants, story/GM/narrate, bend, welcome, public reader),
door stranger/invite/lobby, public cold/first/warm; https://demo.dregg.online/ = 200 in 2.3 s. Smoke (a) door, (b) story,
(e) public green; (c) apps install and (d) Hermes lobby red:
- hermes.room: HOME fix 1447b883f got past consent anchors; the next refusal was infra's: /var/lib/mini/lobby held the
  10-29 world's install state (steps marked done, old founder subject). dregg-infra walk prep now sets it aside; infra
  reran hermes from preflight, then seed, door, public. Result pending.
- apps install: demo-world config (app-reds diagnosis), both fixes in dregg-infra demo-grain-world (infra): grain-host.json
  needs importProfile market-large-v1 (Etherpad > standard-v1's 768 MiB); grain-host.json must pin the resolved candidate
  path, not /var/lib/mini/candidate/current (a symlink; spk-host's O_NOFOLLOW parent walk is deliberate custody -> ENOTDIR),
  rewritten on each candidate switch. No candidate cut needed.
- Fresh be4ef7510 world (true regenesis, infra f8f7bc1): hermes.create red: install-hermes:447 sets the grain-create
  spec namespaceRoot=$NODE/namespace (operator-owned); the resident-run `grain-runtime create` propose refuses it (mini-sdk
  private.rs:44). Fixed by app-reds 5f22e6324 (resident phase uses its own private namespace;
  disjointness from the Host's collision refusal of random 63-bit reservations). Hotpatch: grain-runtime built from
  be4ef7510 + 5f22e6324 at hbox:/home/hbox/lanes/integ/tests-target/release/grain-runtime (sha256 99917187...), overlaid by
  infra on the live world. Apps installs hotpatched in the live grain-host.json (real candidate dir, market-large-v1); the market's
  recorded per-package refusals (/var/lib/mini-apps/verdicts, mini-market/refused) replayed the old failure until infra
  set them aside. Open question for app-reds: should a refusal recorded under a since-changed host config be re-sweepable
  by the operator (a named `apps sweep`), rather than needing records moved by hand?
- private-cells: 55a00e330 (fix: 0 < queryBound, teeth public_signature_refutes) merged as 4db04df8e; READY as its own
  candidate 7d90da717 (17:40; main moved to it). Minidregg umbrella GREEN; Fixtures umbrella RED: NativeAcceptedFixture and
  NativeDocWriteFixture stale against the new event ids; rerecord.sh said `unchanged` (keys on front-end identity only).
  Proofs re-records both from 7d90da717 and makes rerecord.sh detect stale data (replay or codec/event-id digests). Was HELD on 0e43b648c: Kimi found DeclaredReceiptHiding vacuous at queryBound = 0 (ReceiptEventHiding.lean:222-238);
  lane fixing (require 0 < queryBound). Codec epoch change; lands as its own candidate; fresh genesis after.
- Interim smoke 21:22 (fresh be4ef7510 world): (a) door GREEN, (b) story GREEN, (e) public GREEN (200, cold 0.3 s);
  (c) apps in flight (EtherCalc, Etherpad accepted after config hotpatch + refusals cleared + frame's missing
  dbus-user-session; Etherpad earlier hit op66-plan "launch BEGIN authorization, descriptor or action shape refused";
  Hacker Slides not in quarantine: seed may still use the old appId instead of reveal.js); (d) Hermes RED: with the
  namespace hotfix, hermes.create hit "op 91: resource birth target already present": world state (the 20:54 birth had
  completed, then lobby/g/create was removed); recover by restoring that dir or a fresh BASE; 659301aa4 (staging) names
  the NO_RECORD refusal and stops at once. Both product reds to app-reds a17f4172949caca14.
- 22:17 clean pass (fresh be4ef7510 world, fixes up front): Hermes create, handoff, summon GREEN (with the grain-runtime
  hotfix, then reverted: overlaying a pinned role binary breaks store-entry's manifest-digest check on the next Store
  restart; hot-swap must re-pin manifest + SHA256SUMS + Hermes root together; told iteration speed). Many infra fixes in
  dregg-infra main (registry umask, controller root, PATH, dbus-user-session, broker NoNewPrivileges). Red: hermes.controller
  "operator control peer UID mismatch": dregg-infra controller-entry runs controller-launch as mini-h-lobby without
  MINI_OPERATOR_PEER_UID (as_res pins 0); infra fixing. Seed must install reveal.js not Hacker Slides f0277a5d (infra).
- ~19:00: Hermes lobby create..resident GREEN on the clean world (infra fixes in dregg-infra main, CHECKLIST ea60c81).
  Apps: ingest passes; EtherCalc op66-plan "launch BEGIN authorization, descriptor or action shape refused", Etherpad
  "operator reply opcode mismatch" (maybe half-born births from earlier refused attempts). Infra rebuilds a one-shot
  fresh world with one install per app to separate world state from product. Landed on main: install-hermes 460ad0fd7 (infra:
  resident state dir, units enabled) and seed reveal.js deck step 929eac696 (integrator, from revealjs.json). Main =
  929eac696 (7d90da717 + those two scripts). Explorer F2 (member lacks a `welcome`
  ref), F5 (first action after idle 30-38 s, re-plan; likely consent catch-up, hot-path).
- Clean one-shot world (~20:30): smoke (a) door GREEN, (b) story GREEN, (d) Hermes lobby chain GREEN to resident (ask/reply
  untested), (e) public / 200; (c) apps install RED: EtherCalc and Etherpad each hit op66-plan "launch BEGIN authorization,
  descriptor or action shape refused" on one clean install (product red; app-reds has verdicts + worker journal; Davros
  installs through launch on hbox j14-apps, so compare the demo worker's draft). Etherpad's opcode mismatch was world state.
  /doc/welcome 404 publicly because the seed stops at the installs. Infra fixed: frame apt-get update before
  dbus-user-session.
- DESIGN BLOCKER (needs ember): grain installs cannot complete in the forge demo container. The spk volume helper makes
  each grain's /var a loop-mounted ext4 image under /var/lib/mini-spk-worlds and attests the backing fs UUID; the demo
  container (nspawn, user-namespaced) has no loop-control, refuses loop mounts in a userns, and its root ext4 has no UUID.
  Davros passed launch BEGIN and died at "volume-helper verb=Create ... volume create refused". Options (infra): (1) a
  non-userns demo container like the composed one (accepted by ember only for a gate-only container), (2) a small
  dedicated VM (SPEND RULE: ember's yes), (3) a volume-helper change in minidregg (bind-mounted directory on a UUID'd
  host ext4 + project quotas instead of loop images). Helper interface (infra): /usr/local/libexec/
  mini-spk-volume-helper-<STORE> (install-user-world, from $C/bin/mini-spk-volume-helper) via one sudoers rule for
  mini-core; execs `spk-var-volume --root GRAINS_ROOT create|create-from|verify|attest ...`; images in
  GRAINS_ROOT/vars/<STORE>-<resource>; loop-mounts ext4 nosuid,nodev; attests the backing fs UUID (collect_witness).
  A no-loop variant needs quota-bounded directories on a UUID'd fs and a changed attest/witness. op66-plan (EtherCalc, Etherpad; not Davros) is package-specific
  and stays with app-reds.
- Hermes (d) judged on the final world: controller, dispatch, resident GREEN; `ask lobby` admitted (5.7 s, one re-plan)
  and lands, but no reply: mini-grain-resident@9872001 joins the lobby then exits 1 with "resident source preparation
  refused before dispatch: controller service is unavailable" (4 repros). Routed to app-reds a17f4172949caca14.
Ruling: deploy-script fixes keep be4ef7510's verdicts (no composed rerun); a Rust fix means a new cut.
The restart `continuous` red was the resident's own output document moving its maintenance revision; be4ef7510's
maintenance_fingerprint leaves out documents the resident writes.

## DISK PRESSURE (2026-10-30 ~18:45): hbox / at 95%, 25G free

Writing to hbox paused (ember's rule: stop, tell, wait; delete nothing without ember's word). The batch build 9b3417120
was stopped (pgid). Not started: proofs' fixture re-record (deep build), any new build or gate. Ranked, integ lane:
candidates/ 16G (30 x ~524M; 2b8f75dc, 7001c0a9, b39563f1, c7a632f7, 86f8d3e7, d9661be9, f34b0309 from the predecessor,
the rest this session; keep be4ef7510 = rehearsal 3, 7d90da717 = main, 06665f052), src 12G (the warm tree; keep),
old/ 11G (set-aside build outputs, artifacts.* ~400M each, made by integ-build this session), /ci gate worlds 21G (63 c-/j-/t-/
f-/e- dirs from gates; none kept up), tests-target 1.0G, rust-target 0.9G, gate-* ~2.4G. Other lanes: hot-path 16G (predecessor's, unused), hpc
13G (hot-path's warm tree; artifacts-1/-b3 ~330M each), /ci/hpc few hundred MB, proofs 11G (msrc 12G unused), iter-speed 7.4G, infra 4.0G, private-cells 3.9G, hp-seed 2.5G; /ci/ar-ot 3.2G,
/ci/scout 2.7G, /ci/hp-codex 2.1G, /ci/ar-ec 1.4G, /ci/hb-dav-1/2 2G. Waiting for ember's choice.

## Candidate cadence (ember, 2026-10-30)

Cut candidates only for meaningful batches or deep Lean changes; never make anyone wait 40 minutes for one tiny fix.
Between cuts, test on hotpatched worlds: script and config fixes applied directly, Rust fixes overlaid onto a kept world
(the overlay/hot-swap path; iteration speed is building the one-crate hot-swap). Let a running build finish; do not queue
another until a real batch has accumulated. Rehearsal 3 ships be4ef7510 with the install-hermes HOME fix hotpatched
(infra), not 06665f052.

## Lanes (send shas; name every new candidate to infra and the scout)

| lane | agent | owns |
|---|---|---|
| infra (successor; predecessor add189844d158e3a7 handed off at dregg-infra edge/demo/CHECKLIST.md 712d404) | a104b94c2643e9c5d | forge composed container (composed-sync + composed-gate; residents/restart need root), the ship |
| scout (Sonnet) | a3d575cdd7a822f6b | every journey row + stress on the newest candidate; routes faults; docs/SCOUT-FINDINGS.md on lane/scout |
| proofs (Opus) | af4b3ea612564dea5 | umbrella reds, statement fixes, accepted-fixture re-records |
| app-reds (Sonnet) | a17f4172949caca14 | app packages and declarations, Hummingbird, grain-runtime app tests |
| iteration speed (Opus) | ab2786fe1172f5683 (predecessor a141a9c535501bbd7 hit its context limit; WIP origin/lane/iter-speed, self-test 000a36610) | Lean v4.30.0 -> v4.35.0 bump, then codec/store/world-root seams, lane-tree warm pool, hot-swap; will provide a second-tree umbrella stage |
| private cells (Opus) | a74ad8d84ada5627a | receipt-fingerprint leak first, then the O(log n) blinded-cell hiding (docs/RATCHET-LOG-DESIGN.md; Prop-only draft Kernel/BlindedCellHiding.lean, merged 20d3cd965, not imported by any lake target: lean_lib roots are the umbrella modules only) |
| hot path successor (Opus) | a86738fc1dfae6429 | the perf queue's law-17 reds: restart growth, certify, story new, flatness rows except the blinded-cell part (private cells); batched shas |
| explorer | a3e5d6dbcd68e616c | perf and behaviour probes on candidates; docs/EXPLORER-FINDINGS.md |
| SPK freshening | a58fcf100f4438710 | queue complete (all FEATURED repacks landed) |

## Lean 4.35 bump protocol (what is held)

**HOLD LEAN declared ~21:00 2026-10-30** by ab2786fe1172f5683: bump green on the Mac for the whole closure (only the two
Native fixtures red, as on main); 324 pin sets changed within propext/Classical.choice/Quot.sound; 187 scoped
`backward.isDefEq.respectTransparency false`; final sha off main 929eac696 after Kimi's review. Held: proofs (re-record from
the bump candidate instead), private cells, hot-path 2dfa8372e. Staging's unbuilt hot-path batches 1-3 merge after the bump.
The bump's hbox build waits for the disk to be cleared; build it alone, first.
FINAL bump sha cdb399b477ea76e8f8f50e956623f58b5b3412ec (one commit on main 929eac696; Kimi: no statement changes beyond
two meaning-preserving ones, no sorry/axiom, only native_decide added is the self-test). When writes resume: run
`bash -c './integ-build4.sh cdb399b47; ./umbrella-minidregg.sh cdb399b47'` alone (toolchain change: whole-tree rebuild,
raise MEM if hbox is quiet), move main to it on a green host stage, then merge main into staging (hot-path 1-3 recompile
under 4.35; iteration speed is checking those seven files together on the Mac), lift HOLD LEAN.

The bump comes as one sha off main. On its "HOLD LEAN" message, hold every other Lean landing (proofs batches) until
the bump's candidate is READY; then they rebase. Rust-only and harness landings keep flowing. Build the bump alone.
Required in its commit message: every #assert_axioms pin whose set changed (Classical.choice joining is fine; sorryAx,
ofReduceBool, trustCompiler or new axioms are not), what replaced native_decide sites, any moved #assert_compiled output
(lean-intents.json "lean" field expected). Kimi reviews its pin and statement diff before landing. Not yet declared.
Status 10-30 evening: WIP origin/lane/iter-speed 4cf4181ce (not landable; rebase to one sha), ~330 files, 139 pins gained
only Classical.choice; decide -> `decide +kernel`/`rfl` (root cause fixed by Theory/ExceptDecidableEq.lean); the two open reds (SnapRepresents:146,
OracleLogLinkedTwoPhaseGame:209-210) fixed by the successor ab2786fe1172f5683; full Mac umbrella round 13 running. Order:
the private-cells receipt-leak batch (codec epoch) lands first, then the bump rebases onto it. Confirmed (000a36610): TokenCensus/NativePinSelfTest.lean plants a native_decide twin of a decide theorem; #assert_axioms
refuses it, naming `..._native.native_decide.ax_1_1`; native_decide pins list their `_native` axiom by name and stay
unchanged; AssertAxioms recognises compiler trust only through the `_native` component.

## Build and gate (hbox, as user hbox, /home/hbox/lanes/integ)

- `integ-build3.sh SHA` (SEATS=4 MEM=40G): rust-check, host, consent, umbrellas (non-fatal, --unshipped targets: Fixtures
  ObjectiveProofs CensusChecks), rust, pack straight into candidates/<sha> (manifest.json names final paths) -> READY.
  Holds build.lock for the whole run including the umbrella subshell (two builds once collided in one tree).
  PID in build.pid. Never launch while build.pid is alive.
- `integ-build4.sh SHA` (current; queue-build uses it): integ-build3 + after the umbrellas, under the lock,
  `swarm-build scripts/native-accepted-fixture/rerecord.sh candidates/<sha> integ/rerecord/<sha12>-<t>` when the script
  exists (proofs ff9cf7df6): `unchanged` (0) | `recorded fixture-regen/<sha12> <commit>` (0; pushed for review) |
  `authority-differs <diff>` (4; a person writes the Authority-Change commit) | 1 (step failed; logs in that dir).
- `queue-build.sh SHA` (queue.pid): waits for the running build, then starts integ-build4.sh SHA. Prefer one sequential
  job (`bash -c "./integ-build4.sh SHA; ./umbrella-minidregg.sh SHA"`, PID in build.pid): stale queues have rebuilt old shas.
- `umbrella-minidregg.sh SHA` (minidregg.pid): after SHA's build, elaborates the whole `Minidregg` umbrella in the same
  tree (the pipeline otherwise never does). Logs "MINIDREGG umbrella" lines.
- Umbrellas take 20-30 min and hold the lock: candidate cadence is about one per 30 min until iteration speed's
  second-tree umbrella stage exists (they will send the command; switch in integ-build4.sh).
- `gate12.sh SHA`: tour + composed + enrol + j14-apps + flatness. Env: EDGE_REV=69c17a3 JWORLD_MANAGEMENT=distinct|sponsor
  KEEP_WORLD=1 PORT=.. JWORLD_ROUTE_FRONT_PORT=.. (unique), PHASES subset, HARNESS=<sha>. j14 inputs staged once:
  integ/j14-hroot (rebound per candidate), j14-data, j14-secrets; runs under /ci (broker-world-up refuses a group-writable
  ancestor and integ/ is 775). Never edit a gate script in place; number the next one. hbox composed cannot judge
  residents/restart (no root).
- Kept world teardown: the candidate's scripts/spk-platform/world-down.sh RUN/inputs, then
  dregg-infra-69c17a3/edge/mini/journey/jworld-scratch.sh down RUN/w (XDG_RUNTIME_DIR and DBUS set); log DOWN.
  No world is kept up now.
- Mac landing worktree /Users/ember/dev/minidregg-lanes/integration-r2 (branch integ/main = origin/integration/staging);
  main moves to staging once a build's host stage is green. CARGO_TARGET_DIR=/Users/ember/dev/minidregg-lanes/target-integ
  for filtered Mac tests (apps_front connector test fails only inside the apps:: group; SUN_LEN socket fixtures fail on
  macOS temp-path length: both known).
- Market adopt set: dregg-forge:/var/lib/spk-fresh/qualified-2026-10-29/out (local.json, adopt.tsv; 22 packages). Add a
  package as apps/<app>/out/<app>.spk (+ verify.txt or build-date-utc.txt), move out aside, run
  `python3 -I repo/deploy/market/fresh-index.py --apps $Q/apps --recipes $Q/repo/apps/packages --spk-tool
  /var/lib/spk-fresh/tools/spk --out $Q/out`, copy local.json to native/resource-client/tests/fixtures/
  fresh-local-index-2026-10-29.json, run `cargo test --bin mini -- apps::tests`.

## Candidates

| candidate | state |
|---|---|
| 41590f420 | gate12 distinct: tour 73/73, j14-apps PASS, composed all but residents/restart PASS; forge: residents PASS, restart red at `continuous` (on later harness) |
| 719d7b7aa | READY, first clean manifest; umbrellas: Native fixtures (fixed later), TokenCensus (fixed later) red |
| 06831831c | READY (named to scout and infra): app declarations, re-recorded Native fixtures; scout full pass running on it |
| 4e5faa8d8 | READY 13:20; main contains it. hbox gate12: tour 73/73, j14-apps PASS, enrol PASS, flatness-submit FAIL (reported). CONFIRMED on hbox; infra c-4e5f-d1 distinct composed running: if fully green this is the rehearsal-3 ship. Umbrellas then Minidregg umbrella running |
| 06665f052 | READY 16:17; every bin/ checksum identical to be4ef7510 (only provenance and source differ: install-hermes HOME fix, scout docs/stress, docs). Not shipped (root: ship be4ef7510 with the hotpatch). Umbrellas then Minidregg umbrella running in the same job |
| 2e3d16ef7 | READY 14:18 (umbrellas stopped: superseded) |
| be4ef7510 | READY 14:23 = 2e3d16ef7 + continuous fix. GATE GREEN (composed fully green on forge, tour 73/73, j14-apps PASS): REHEARSAL 3 SHIP. Umbrellas rc=0 (every umbrella green, TokenCensus included); rerecord `unchanged`. |

## Open reds and owners

- composed restart `continuous` (above): infra diff, then integrator.
- flatness-submit (law 17): reported, not blocking; hot-path successor owns it, the blinded-cell ratchet part goes to private cells.
- Hot-path batch 3 24a14656f merged (40750bc0e): OwnBase.state is a Thunk (16% of consent CPU per write); measurement pending.
- Hot-path batch 1 fb0899ff8 merged on staging a75b373bf (bytesBEq: withPtrEq before whole-cell byte compares; per-record
  post-validation flat 4.4-4.9 ms at every height vs 5 -> 17.5 ms; genesis audit at head 769 38.3 -> 32.6 s). Next batch.
  Batch 2 b57ceceab merged (c019b8756): ConsentAnchor.headState reads Loaded.cells (cached) instead of flattening every
  write per admission (68% of consent CPU per write); sponsor shell write 2.6 -> 1.65 s flat near head 1,000.
  For the root: a retained consent anchor is bound to the exact consent executable, so every client walks from genesis
  after each ship (48 s vs 9.2 s resuming at head ~1,000).
  Hot-path asks the root: may CONSENT-OWN change (for the consent provider's cold start from its own snapshot)?
- Perf queue (explorer, be4ef7510; owner: hot-path successor, blinded-cell flatness to private cells): E10 `story new --from tale`
  19.9 s (one submit per template line; batch into one proposal), `chat new` 3.0 s, `chat invite` 2.4 s, first credit
  2.0 s vs 0.5 s warm write; E11 restart 9.6 s and first signed read after it 8.0-8.6 s at height 160-190 (cold-start
  snapshots); certify 16.9 s at a 256 tail with writes halted meanwhile, about 2.7 writes/s from three members.
  Hot-path diagnosis (a86738fc1dfae6429): both restart and certify costs are the client consent provider's catch-up
  re-admission (~47 ms per record since it last admitted; a fresh provider folds from genesis: 6.5 s with anchor, 38.7 s
  without at head 849); Host restart + first read is 2.4 s, certify itself 0.21 s. Fix in progress: provider resumes from
  its own sealed snapshot; cut the per-record constant; no codec change so far.
  Follow-up: restart's first signed read is O(height), a law-17 red: 8.0-8.6 s at head 160-190, 23.4 s at head 769
  (restart.sh 26.0 s); cold-start snapshots fix it. Certify at a fixed 256 tail: 16.9 / 32.2 / 12.2 s at heads 257/512/768,
  not monotone (box load); at least ~12 s of halted writes per tail. Driver hbox:/ci/xp-log/f1.sh.
- Hummingbird live receiving path: app-reds building a j14apps()-style run.
- Scout full pass on be4ef7510: PASS 162, FAIL 2, UNCONFIGURED 7, UNJUDGED 3 (jpay 6/6, KC, JWF now pass). Reds:
  demo/J14 36/211 RETRACTED by the scout: its copied hbox pipeline box.env exports MINI_TEST_PROVIDER_BIN and
  MINI_LAUNCH_GATE_BIN pinned to stale 7ffd6524 fixtures (a hazard for any runner that sources it), overriding the
  candidate's own; JDV row 140 cause found by hot-path: on SIGTERM `mini serve` dies and the Host's EOF clean end ran
  DurableReceiverIO.sealHead, a second full cold load of the Store (3.6 s idle at head 769, longer under load; the journey
  allows 10 s). Fix 2dfa8372e (lane/hot-path-cold, Host/Main.lean: sealSession seals the held opening, no second open)
  is UNCHECKED; do not merge until hot-path reports its lane-check (blocked on hbox disk). Was: a stale mini-hermes-test-provider in the scout's run (app-reds traced "attach brief is not JSON";
  the candidate's own fixtures/mini-hermes-test-provider is current), rerun owed; demo/JDV row 140 "Host child outlived
  its server" on stop -> hot-path a86738fc1dfae6429 (13 later demo steps are shadows behind it). Evidence
  hbox:/ci/scout/rbe/be4ef751*/rows/demo/journey.err.
- fleetsign 1/100 under full parallel load (attempt plan.frame missing): scout reproducing; core client if confirmed.
- Scout's twelve demo steps never ran on c7aa7e8c4 (journey budget spent); rerunning on 06831831c with a 12000 s timeout.
- Owed (integrator, next gate script): gate12's j14apps sets TEST_PROVIDER=$J/bin/mini-hermes-test-provider, which the
  candidate keeps under fixtures/; point it at $C/fixtures/ (harmless today: Davros uses the real pool provider).
- Import boundary (scripts/check-import-boundary.sh) RED on main, 16 edges: Effects -> Theory/Lean (AssertAxioms, Store,
  CellState, TypedAuthorization, AxiomPin, Lean.Data.Json) and Kernel/Compiler -> Effects.Revival.HostedDav/
  HostedConversation (apps-agents 445a691f6, 0b4b39de7, 289e0088b). The tier table makes Effects a sink below nothing it
  now imports; needs a ruling (root): either Effects may import Theory/Lean and the derived Hosted* descriptors move
  below Kernel (or Effects leaves the sink row), or the edges are undone.
- Ruled 2026-10-30 (root), implemented by proofs in fa4193808 (merged; building as 103c6002a): (1) genesis refuses a factory predicate
  containing `witnessed`, loudly and by name (not fail-closed at every birth); (2) objective-native-acceptance.py
  publish-variant harness bug fixed (lean --run without the kernel dynlib); (3) the integrator's build regenerates the
  accepted fixture automatically whenever the Objective front-end identity changes, the Authority-Change commit staying
  reviewed (proofs implements it with the integrator: a build stage or a pre-candidate step that re-records from the
  candidate just built and proposes the Authority-Change commit for review).
- scripts/check-proof-hygiene.sh fails on scripts/oracle-cold-replay-budget.lean:55 (bare `#print axioms`); owner: proofs.
- PredCompile.lean:832 comment cites the wrong theorem name (proofs, next batch).

## Rules

Named-file commits with `git commit -F <file>`; never `git add -A` or `git stash`; filtered tests only; every detached
job has a PID file and is stopped only by it (stale leftovers of our own runs may be stopped by exact PID after reading
the command line: root ruling 2026-10-30); lake/git on hbox as hbox; never search from / or ~; disk pressure = stop and
tell ember (hbox / had about 84 GB free on 10-30).
