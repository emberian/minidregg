# Integrator state

Present-state record of the integration lane, rewritten whole when its shape changes. A successor reads this, then
`hbox:/home/hbox/lanes/integ/COMMANDS.log` (every build stage, gate verdict, world teardown and process stop, one line
each). Older history is in this file's git history.

## Goal and the one blocker

Rehearsal 3 ships through infra (`demo-mini.sh ship` into the forge `demo` container) when the gate is fully green:
tour + j14-apps on hbox gate12, composed (all phases, distinct mode) on infra's forge composed container. Flatness
(law 17) is reported, never blocking (root ruling 2026-10-30: the submit ratchet preimage is ember's decision).
**Only red before the ship: composed restart, step `continuous`.** The resident opens a maintenance turn after its last
delivered request because its maintenance fingerprint moved (room_resident.rs `assignment_fingerprint` over
prepare_resident minus sourceRequests/sourceRoom/roomStatus). Ruling: diagnose, never teach the fixture to answer it.
Staging carries a diagnostic: when maintenance is due, grain-runtime writes `maintenance-input.json` (and the one it
replaced as `maintenance-input.prev.json`) beside the resident's requests.json. Infra runs the first candidate with it
(4e5faa8d8 or later) with KEEP_WORLD in distinct mode, diffs the two, sends the moving field; the integrator fixes the
fingerprint (likely the resident's own say in contextProjection, or recentMemberChanges).

## Lanes (send shas; name every new candidate to infra and the scout)

| lane | agent | owns |
|---|---|---|
| infra (successor; predecessor add189844d158e3a7 handed off at dregg-infra edge/demo/CHECKLIST.md 712d404) | a104b94c2643e9c5d | forge composed container (composed-sync + composed-gate; residents/restart need root), the ship |
| scout (Sonnet) | a3d575cdd7a822f6b | every journey row + stress on the newest candidate; routes faults; docs/SCOUT-FINDINGS.md on lane/scout |
| proofs (Opus) | af4b3ea612564dea5 | umbrella reds, statement fixes, accepted-fixture re-records |
| app-reds (Sonnet) | a17f4172949caca14 | app packages and declarations, Hummingbird, grain-runtime app tests |
| iteration speed (Opus) | a141a9c535501bbd7 | Lean v4.30.0 -> v4.35.0 bump, then codec/store/world-root seams, lane-tree warm pool, hot-swap; will provide a second-tree umbrella stage |
| SPK freshening | a58fcf100f4438710 | queue complete (all FEATURED repacks landed) |

## Lean 4.35 bump protocol (what is held)

The bump comes as one sha off main. On its "HOLD LEAN" message, hold every other Lean landing (proofs batches) until
the bump's candidate is READY; then they rebase. Rust-only and harness landings keep flowing. Build the bump alone.
Required in its commit message: every #assert_axioms pin whose set changed (Classical.choice joining is fine; sorryAx,
ofReduceBool, trustCompiler or new axioms are not), what replaced native_decide sites, any moved #assert_compiled output
(lean-intents.json "lean" field expected). Kimi reviews its pin and statement diff before landing. Not yet declared.

## Build and gate (hbox, as user hbox, /home/hbox/lanes/integ)

- `integ-build3.sh SHA` (SEATS=4 MEM=40G): rust-check, host, consent, umbrellas (non-fatal, --unshipped targets: Fixtures
  ObjectiveProofs CensusChecks), rust, pack straight into candidates/<sha> (manifest.json names final paths) -> READY.
  Holds build.lock for the whole run including the umbrella subshell (two builds once collided in one tree).
  PID in build.pid. Never launch while build.pid is alive.
- `integ-build4.sh SHA` (current; queue-build uses it): integ-build3 + after the umbrellas, under the lock,
  `swarm-build scripts/native-accepted-fixture/rerecord.sh candidates/<sha> integ/rerecord/<sha12>-<t>` when the script
  exists (proofs ff9cf7df6): `unchanged` (0) | `recorded fixture-regen/<sha12> <commit>` (0; pushed for review) |
  `authority-differs <diff>` (4; a person writes the Authority-Change commit) | 1 (step failed; logs in that dir).
- `queue-build.sh SHA` (queue.pid): waits for the running build, then starts integ-build4.sh SHA.
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
| 4e5faa8d8 | READY 13:20 (host stage 33 min, deep); main contains it. Named to infra successor (distinct composed + continuous diff) and scout. hbox gate12 PHASES="tour enrol j14" running (gate-4e5faa8d, pid gate-4e5f.pid); Minidregg umbrella queued after its umbrellas (minidregg.pid) |
| staging tip c32e35e9a+ | + birth_refusal fixture fix c5905db60 (tests only), state docs: queue after 4e5faa8d8 and its Minidregg check |

## Open reds and owners

- composed restart `continuous` (above): infra diff, then integrator.
- flatness-submit (law 17): reported, not blocking; ember's design decision.
- Hummingbird live receiving path: app-reds building a j14apps()-style run.
- fleetsign 1/100 under full parallel load (attempt plan.frame missing): scout reproducing; core client if confirmed.
- Scout's twelve demo steps never ran on c7aa7e8c4 (journey budget spent); rerunning on 06831831c with a 12000 s timeout.
- Ruled 2026-10-30 (root), owned by proofs af4b3ea612564dea5, land as shas: (1) genesis refuses a factory predicate
  containing `witnessed`, loudly and by name (not fail-closed at every birth); (2) objective-native-acceptance.py
  publish-variant harness bug fixed (lean --run without the kernel dynlib); (3) the integrator's build regenerates the
  accepted fixture automatically whenever the Objective front-end identity changes, the Authority-Change commit staying
  reviewed (proofs implements it with the integrator: a build stage or a pre-candidate step that re-records from the
  candidate just built and proposes the Authority-Change commit for review).
- PredCompile.lean:832 comment cites the wrong theorem name (proofs, next batch).

## Rules

Named-file commits with `git commit -F <file>`; never `git add -A` or `git stash`; filtered tests only; every detached
job has a PID file and is stopped only by it (stale leftovers of our own runs may be stopped by exact PID after reading
the command line: root ruling 2026-10-30); lake/git on hbox as hbox; never search from / or ~; disk pressure = stop and
tell ember (hbox / had about 84 GB free on 10-30).
