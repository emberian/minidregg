# Integrator state

Present-state record of the integration lane, rewritten whole when its shape changes. A successor reads this, then
`hbox:/home/hbox/lanes/integ/COMMANDS.log` (every build stage, gate verdict, sweep, world teardown and process stop, one
line each). History is in this file's git history.

The integrator is agent **aec6914709d96f496** (fresh 10-31 10:55, replacing aba0beaa578594e92, retired by `cv retire`;
the hook names the live integrator to anyone who messages an old id). Lanes send shas, READY, reds and handoffs to the
integrator; the integrator merges onto `integration/staging`, cuts batch candidates on hbox, gates them once per batch,
moves main to gated candidates and names candidates to infra and the explorer.

## Re-orienting (root, 10-31 10:50)

After any context clear, the ONLY sources of what is pending are this file and COMMANDS.log. Never send a report because
a scratchpad or task-output file exists. Send only what "Reports owed" lists, and move it to "Reports sent" in the same
step. Closed items are never re-reported. Report to root on events only (READY, gate verdicts, reds, decisions needed).

## Now (2026-10-31 11:05 EDT)

- **ember (10-31): no rehearsal cut until she says.** Make the system excellent: Hermes repaired, efficiency everywhere,
  every red fixed (never worked around). ~1 ms warm per action is the direction, not a gate. Law 17 holds.
- **main = 83e926874** = gated batch 4 b9450147f + main 7978ddfdd. **Batch 4 is the green fallback.**
- **Batch 7 acc7cfa03: gate15 verdict FAIL (10:55).** enrol PASS, tour 73/73; j14 FAIL at worker/finish_worker:
  `controller-run grain-runtime create` rc=1, mini cannot create owner-workspace/attempt-index/by-intent/ (ENOENT;
  perf-client aa24acaf8, fixed b940b3f50); composed (-c2 after my predecessor's harness-extract launch error) blocked by
  "the metered workroom is not ready"; flatness submit FAIL / get PASS (published, never gating).
- **acc7cfa03-attidx -hp1** (batch 7 + mini from b940b3f50, HARNESS=49a717ef2, PHASES "j14 composed"; PID file
  $I/gate-acc7-attidx.pid; integrator waiter armed): composed FAIL again 10:57 with the SAME "metered workroom is not
  ready" refusal, so that refusal is NOT downstream of the attempt-index ENOENT: it is its own fault (W1). j14 FAIL
  11:02: H1 (op 47; journal: op 98 mini_say paid, write lookup not-submitted mapped to refused). Gate verdict FAIL
  in substance; flatness phase still finishing (waiter armed).
- Batch 6 74e1cfa10 umbrella-tree rc=0 reds=0 (10:57); fixture-regen/74e1cfa10719 merged on staging (790eb04a3).
- **Staging 790eb04a3 (batch 8 material)**: iter-speed 7800d3199 + 697db7664, tower split 0eab28db7, exorcist 47b7cb2e1
  + c763e3ead + **b37f26cf6** (A: ssh lines run in a per-member `mini line-resident` via new bin `mini-line`, role
  miniLine, which every mini overlay must also carry; B: signed reads keep one journal line, no attempt tree; doc show
  wall min 17.4 -> 13.7 ms), perf-client 783b460cb + b6 + b940b3f50 (+ fb6f024a8 via exorcism), retained-mode 62aa5fcf8
  over 675a80745 + 1d4ff4efb, + 05bffae27/7f42f6445 (round-2 answers: SparseMap transport lemmas, Zero, 37 pins;
  round-3 audit SOUND: injective over the full type, 37/37 pinned, none vacuous), app-reds H1 ccdaf98b3 + faeb1ff0b (not-submitted is its own resolution at every site; 23 filtered tests
  pass), hot-path 6d744e25f (5cb39c5fe + 05a38ff4e: law check on its own witness decides Pred.eval, csimp; audit SOUND:
  admitOwn hard-wires law.witness, no external caller of admit with another witness), perf-apps 546a551fd (docs: batch 7 vs 6, Host CPU samples 8,704 vs 13,647), boundary 48cea3caf (Theory may import Std), batch 6 fixtures. Batch 8 cut owes the
  whole-tree build of these.
- **Next shared-interface change: retained-mode L0** (Store as a persistent extensional tree map, ~66 files,
  WorldCompact deleted): its own cut with one whole-tree build; FORMAT rebases onto it. lane/retained-l0 is WIP
  (94cd7ceca, Theory wave 8/42): NEVER merge until retained-mode sends a sha labelled SHARED-INTERFACE.
  Audit items owed before L0 (sent to the lane by the auditor): toDFinsupp 0 = 0 as an equation, an ofDFinsupp
  inverse, one optionZero instance (two global remain), a toList code-order lemma for encode, one key DecidableEq.
- **CLOSED: GET read-path contract** (ember ruled (c) prepaid per-payer reservations, (d) per-route declared eligibility;
  hot-path owns it statement-first). Never re-run or re-report.
- hbox: / 57 GB free (11:00).

## Failure signatures (every red: stage, refusal/error text, first divergence; reruns? same place?)

- **H1, Hermes ungranted-ask final say `refused`** (batch 5 1c151fce4 and its overlay 1c151fce4-resid -hp1): stage j14
  probe, first `task_turn('refused', ...)` (the UNGRANTED Davros put; the label is the probe's name, not the outcome).
  Error: `ValueError: Hermes sent no reply to the ask: refused`. First divergence: the resident run completes (op 47,
  provider attempts 49/69/89, model text correctly names `typed-apps-not-granted`, `resident-completed`), then the final
  delivery outcome is `{"status":"refused","type":"mini-resident-request-outcome-v1"}` (3/3: batch 5, 5-resid, 7-hp1) with receipt
  `controller/home/grain/state/resident-final-refused-0000000000000047.json`; no say reaches the transcript. Service logs
  carry no error text (the receipt's body was in the torn-down world). Reruns: yes (2/2). Same place: yes, identical
  op id and outcome across a spk-host overlay. One fault. Cause class (app-reds run 24): the final `mini_say` got
  ECONNRESET from the operator-v2 socket and was recorded as `refused`. c88b88755 (batch 7) surfaces the write error.
  Run 24 confirmed: "Connection reset by peer (os error 104)", then the exact lookup said not-submitted, which
  `lookup_operation` (resource_tools.rs ~1213) maps to `refused` together with a real Host refusal. app-reds' 40cb4aa59
  (lane/app-reds-3-tf) is DROPPED (superseded by ccdaf98b3 on lane/app-reds-h1, itself sent back 11:45: resolution must
  carry not-submitted too, since publish_notices skips and resident_compute fails on resolution "refused"). 40cb4aa59 was: it matches error prose by substring and makes a real Host refusal found by
  exact lookup non-terminal after a reset (a retry loop). Asked for the fix at the lookup (not-submitted distinct, Host
  refusal stays terminal, two tests). The reset's own cause (ServeBounds 10 s deadline?) stays open; run 25 times it.
- Batch 6 74e1cfa10 j14: `FAIL rc=1`; its world /ci/j-74e1cf was swept, so its signature is unrecorded: not counted as H1.
- **H2, attempt-index ENOENT** (batch 7 base): stage j14 worker, `controller-run grain-runtime create` rc=1, ENOENT on
  owner-workspace/attempt-index/by-intent/. Never reached the probe. Distinct from H1. Fix b940b3f50; -hp1 decides.
- **W1, metered workroom not ready** (batch 7 base -c2 and -hp1): stage composed-inputs, `composed-inputs: the metered
  workroom is not ready`. Reruns: yes; same place: yes, with and without the ENOENT fix. One fault, independent of H2.
  CAUSE (hot-path): a gate pin, not the candidate. gate15.sh defaults EDGE_REV=4ea511d; batches 4-6 composed ran on
  dregg-infra 69c17a3. 4ea511d's jworld-scratch.sh apps-bootstrap dropped the JWORLD_MANAGEMENT=distinct branch (tasks
  born as subject 7), while workroom-ready.sh signs as subject 8 -> no-grant. Routed to infra aa72653a8ce442178
  Infra: 4ea511d is an ANCESTOR of 69c17a3 (stale pin; main kept the branch; forge syncs main so never saw W1).
  FIXED: gate15.sh default EDGE_REV=69c17a3 (12:15). Gates pin a sha; infra sends a newer one when wanted.
- **R1, residents room-summon UNKNOWN** on hbox composed (every batch since 2): hbox cannot judge residents; forge
  composed does (batch 5 forge PASS). Standing, not a candidate red.

## Reports owed

- To root: batch 7 verdict, H1 fix merged, W1 = infra pin (in the integrator's next return).
- When -hp2 lands ($I/hp-h1.pid waits for -hp1, builds grain-runtime from staging in hp-wt, overlays
  acc7cfa03-attidx -> acc7cfa03-h1, launches gate15 PHASES="j14 composed" EDGE_REV=69c17a3 KEEP_WORLD=1 SUF=-hp2,
  PID file $I/gate-acc7-h1.pid): verdict to root, infra, explorer, perf-apps; signature + kept world /ci/j-acc7cf-hp2 to
  app-reds (reset cause, ServeBounds 10 s deadline).
- Awaited (not owed): infra's forge composed of batch 7.

## Reports sent (do not resend)

- 10-31 12:10: W1 cause to infra; hot-path 6d744e25f merged + audit requested (auditor); ack to hot-path
  a0fee5643746e520c; app-reds faeb1ff0b merged, -hp2 queued.
- 10-31 11:50: batch 7 verdict FAIL (H2, H1, W1) to infra, explorer, perf-apps; -hp1 j14 = H1 signature to app-reds;
  W1 routed to hot-path a6c4a1532687a4fdb.
- 10-31 11:45: app-reds: ccdaf98b3 sent back (not-submitted as its own resolution at every resolution match; tests).
- 10-31 11:30: retained-mode: 05bffae27/7f42f6445 merged (573303614); auditor a4d9a6f4cba4855ca: round-3 request.
- 10-31 11:20: app-reds: 40cb4aa59 held with review (fix at lookup_operation; typed transport cause; two tests).
- 10-31 11:08: app-reds: H1 one fault (2/2 same place), batch 6 unrecorded, batch 7 base is H2, W1 separate; asked for
  KEEP_WORLD/receipt copy on a probe red. Exorcist: b37f26cf6 merged (c9cfa459e), rides batch 8.
- 10-31: retained-mode audit rounds 1 and 2 (to a13f0c9ab4513b2d7).
- 10-31: GET-contract astra review (CLOSED). Batch 7 READY named to infra, explorer, perf-apps.

## Lanes (route only to the newest id; distilled lanes' old ids are retired)

| lane | agent | owns now |
|---|---|---|
| hot-path | a0fee5643746e520c (a6c4a1532687a4fdb, ac53c05fe796e4294 retired) | law-17 perf queue: flatness, `story new`, row 11, Book entries migration (FORMAT) |
| app-reds | ad85d40779880420c | apps installs on forge/hbox, op66-plan, Hummingbird/WBO/Scrumblr live qualification, Davros control run, E3/E4, G2 decider-side type, controller boot ordering, Hermes worker root interpreter |
| private cells | a8da2b953507b402b | FORMAT (a); then the compiler-emitted ZK selective opening; decode pin to CanonicalCellRegistry.custodyDecode with (b) |
| iteration speed | a6c58cb72b0764dbb | seam 1 (codec tags / Store epoch, lands before or with FORMAT), lane pool /home/hbox/pool, lane-tree, hot-swap overlay tool |
| explorer | a3e5d6dbcd68e616c | multi-member exploration of each READY candidate; docs/EXPLORER-FINDINGS.md on lane/explorer |
| infra | aa72653a8ce442178 | forge demo container, forge composed (judges residents/restart), dregg-infra (ship.sh, world-down finding) |
| exorcist | a76808829fc8e4836 (a6ad40ce192354deb, a31f4ba5028d24a92 retired) | no fsync anywhere (lane/exorcism); filtered set `nextest -E 'test(durable) \| test(anchor) \| test(signing_wire) \| test(attempt_state) \| test(receipt_continuity)'` |
| perf-apps | a25df305cfd551d8b | apps install, grain HTTP path, typed-tool path (perf) |
| perf-client | a778bbda6509944a5 (a8d456c6e773efbb8 retired) | client, consent provider per-record cost, web page loads, idle cold start (perf) |
| retained-mode | a9b54e85e4a194b91 (a13f0c9ab4513b2d7 retired) | incremental-computation architecture: a Lean incremental node with one generic "maintained = recomputed" theorem, the Host's derived structures as maintained nodes persisted in checkpoints, emission from Effects/, a lint for whole-state functions on per-request paths, one hot path migrated end to end |
| demo-reds (sub-Opus of the integrator) | a64c387f3e638aa63 | bend/web/door/Hermes product reds as routed |
| statement auditor (sub-Opus of the integrator) | a4d9a6f4cba4855ca | read-only adversarial audit of each lane's top-level statements, one round per merged sha |

Every Lean-statement sha gets an audit round from a4d9a6f4cba4855ca before it rides a cut; verdicts go back to the lane.

## Rulings in force

- **/tank** (root, 10-31 08:30, correcting the earlier reading): ember's "don't use /tank" means don't MOVE data there to
  free disk. Existing small /tank files stay: /tank/lanes/world-up.lock (the ONE world-up lock every lane, gate and
  scripts/spk-platform flocks; never a second path), /tank/lanes/vars-backing.img, /tank/mini-ingest. Gates lock
  /tank/lanes/world-up.lock again (reverted 08:30); playwright runs from $I/pw (local copy, fine). Free disk only by
  removing old trash (retired trees after their checkpoint, finished /ci scratch, superseded candidates and gate roots).
- **Minimal checks** (ember, 10-31, after the gates went green): per iteration only the narrowest check that shows the
  change worked (lane-check of changed files plus one targeted measurement or row); full gates (gate13/15, forge composed,
  umbrellas) once per batch cut; cuts spaced out to accumulate perf work; hotpatched measurement worlds are the inner loop;
  freed hbox time goes to perf builds and measurements. Batch 4 stays the green fallback and rehearsal candidate.
- **Retained mode** (root, 10-31): every lane brief that touches state carries the line "a derived value is maintained,
  never recomputed; writing f(state) on a hot path means you owe its update rule." retained-mode a13f0c9ab4513b2d7 owns the
  architecture.
- **Import boundary**: Effects is the generator Kernel and Compiler consume; Effects sits below Kernel/Compiler, may import
  Theory and Lean core, never Kernel/Compiler/Host. Landed (b7bf3a8b2; table green, no cycle).
- **Consent**: no validity proofs; we trust the storage device; providers resume from a sealed snapshot; anchors survive
  ships (landed: CONSENT-STORE 54bd71d53).
- **Private cells FORMAT scope**: (a) now, (b) with the ZK opening; never trade hiding for speed.
- **Hotpatch, don't cut**: script/deploy fixes go onto a gated candidate via HARNESS and keep its verdicts; Rust/Lean
  needs the next cut, but Rust fixes may be overlaid onto a candidate copy to test between cuts. No single-fix cuts.
- **Stale leftovers**: our own fleet's leftover processes may be stopped by exact PID after reading each command line
  (root, relaying ember, 10-30); everything else needs a PID file or ember's word.
- Flatness (law 17) is reported, never gating. No rehearsal ships until ember says; then only a fully green gate with no
  demo-path product red.
- Split tenancy: one shared consent resident and one shared codec Host per box are approved. Egress gateway and Oracle7: held.
- No new build box (ember): hbox and forge only.

## Build, gate and sweep (hbox, as user hbox, /home/hbox/lanes/integ = $I)

- `integ-build6.sh SHA`: build5 + waits for the previous umbrella-tree's lock. Stages: rust-check, host, consent, rust,
  pack -> `READY $I/candidates/<sha>`; then releases build.lock, runs `src/scripts/pipeline/umbrella-tree SHA` in
  $I/umbrella-src (SEATS 4, MEM 32G) and the rerecord stage from umbrella-src (re-records stale Native fixtures by
  elaboration; pushes fixture-regen/<sha12>, which the integrator merges). Launch:
  `nohup setsid ./integ-build6.sh SHA > build.out 2>&1 & echo $! > build.pid` (SEATS=12 MEM=56G). Never launch while
  build.pid is alive.
- `gate13.sh SHA`: tour + composed + enrol + j14-apps + flatness, then sweep. `gate14.sh NAME` (overlay/hotpatch reruns):
  HARNESS=<staging sha> overlays scripts/ and deploy/spk-host, SUF=-hpN, PHASES subset of "tour composed enrol j14",
  KEEP_WORLD=1 optional. Env: EDGE_REV=69c17a3. hbox composed cannot judge residents/restart: forge composed does.
- Overlays: iter-speed's `deploy/candidate/lane-build.sh rust --crate X` then
  `lane-build.sh overlay $I/candidates/<BASE> $I/candidates/<NAME> ROLE...` (overlay a crate's whole bin set; dir named by
  a 12-hex `.overlay.id`). hotpatch-candidate.sh is the superseded stopgap.
- `sweep.sh [--dry]`: removes gate roots and /ci worlds for candidates two or more behind, candidates beyond the newest 3
  READY; skips $I/keep (be4ef7510, cdb399b47, eca98bde7, 35737eac4, a4cb65af3, overlays), non-40-hex names, anything with
  provenance `.overlay`, anything a live process or /ci world names. Runs at the end of every gate13.
- Hard-link hazard: never `cp -al` a .lake another tree builds in (lake writes .trace/setup.json in place). Lanes build in
  the lane pool (/home/hbox/pool, lane-tree; LANE_POOL_NO_WARM=1 while integ builds; pool.env sets LAKE_ARTIFACT_CACHE=false).
- Mac landing worktree /Users/ember/dev/minidregg-lanes/integration-r2 (branch integ/batch-435; staging is pushed from it).

## Candidates

| candidate | state |
|---|---|
| be4ef7510 | GATE GREEN (rehearsal 3 original ship) |
| a4cb65af3 | GATE GREEN (batch 3); main's base; fallback ship |
| eca98bde7-resvar2(-zai) | overlays of batch 2 with the resident /var fix (and Z.AI); forge demo build |
| b9450147f | GATE GREEN (batch 4, with deploy hotpatch 9fdef19bd): rehearsal-3 candidate; main's base |
| 1c151fce4 | READY (batch 5); gate15 FAIL: j14 H1; forge composed PASS |
| 74e1cfa10 | READY (batch 6); gate15 FAIL: j14 rc=1 (signature unrecorded, world swept); umbrella-tree reds=0 |
| acc7cfa03 | READY (batch 7); gate15 FAIL: tour 73/73, enrol PASS; j14 H2; composed W1 |
| acc7cfa03-attidx | overlay: batch 7 + mini from b940b3f50; gate15 -hp1: composed W1 again; j14 running |
| 1c151fce4-resid | overlay: batch 5 + spk-host crate from 40efdcff9; gate15 -hp1: j14 H1 again (same op, same outcome) |

## Open reds and owners

- TokenCensus ConsentAnchor L1 witness: fixed b70a547c8 (batch 4), confirm in batch 4's umbrella.
- Flatness submit/get (law 17): hot-path; content-cell flatness stays a published red until private-cells (b).
- Etherpad install on forge: 0aa00c3e0 (batch 4); recheck on a fresh world. op66-plan: app-reds.
- Hermes ask on forge: fenced controller fixed cb3bc4f85 (batch 4); Z.AI path 5f32da72d (batch 4).
- world-down.sh leaves the world dir and client residents behind: infra (dregg-infra).
- Every tour JWF-dry `mini web --body` orphan: fixed by demo-reds' lifeline 4928d9a77 (in batch 3); confirm after gates.
- Deregistration's lease freshness ranges over every lease (index leases by account if frequent): hot-path.

## Rules

Every lane brief that touches state carries this line (root, 10-31): "a derived value is maintained, never recomputed; writing f(state) on a hot path means you owe its update rule."

Named-file commits with `git commit -F <file>`; never `git add -A` or `git stash`; filtered tests only; every detached
job has a PID file and is stopped only by it; lake/git on hbox as hbox, never root; swarm-build caps summing under
~100 GB; one sequential job per build tree; never search from / or ~; disk pressure = stop and tell ember.
