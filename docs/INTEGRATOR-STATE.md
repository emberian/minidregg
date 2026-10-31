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

## Now (2026-10-31 11:30 EDT)

- **ember (10-31): no rehearsal cut until she says.** Make the system excellent: Hermes repaired, efficiency everywhere,
  every red fixed (never worked around). ~1 ms warm per action is the direction, not a gate. Law 17 holds.
- **main = 83e926874** = gated batch 4 b9450147f + main 7978ddfdd. **Batch 4 is the green fallback.**
- **Batch 8 dc61016cb: BUILD running** (launched 11:26, PID 2286225 in $I/build.pid and build-b8.pid; integrator waiter
  armed on READY). Carries: exorcist b37f26cf6 (resident shell `mini-line`, role miniLine; read scratch), retained
  05bffae27/7f42f6445 (SparseMap, audit sound), hot-path 5cb39c5fe/05a38ff4e + a5e757016 (cherry-picked as dc61016cb:
  fixes the staging Lean red, authorizeWith on admitOwn; Pred.eval law check, audit sound), app-reds H1a
  ccdaf98b3/faeb1ff0b, iter-speed 7800d3199/697db7664, tower split 0eab28db7, exorcist 47b7cb2e1/c763e3ead, perf-client
  783b460cb/b6/b940b3f50, retained 62aa5fcf8/675a80745/1d4ff4efb, boundary 48cea3caf, batch 6 fixtures, perf-apps
  546a551fd (docs). At READY: gate15 full (EDGE_REV default now 69c17a3); name to infra, explorer, perf-apps.
- **Batch 7 acc7cfa03: FAIL** (H2, H1, W1). Overlay **acc7cfa03-h1** (batch 7 + mini b940b3f50 + grain-runtime from
  a371cf4a5) -hp2 11:23: hbox composed rooms/churn/documents/apps/connector PASS (W1 gone), residents = R1 standing;
  j14 FAIL on H1b (below). KEPT worlds for app-reds: /ci/c-acc7cf-hp2/w (composed; down: world-down.sh
  /ci/c-acc7cf-hp2/inputs then jworld-scratch.sh down) and /ci/j-acc7cf-hp2 (j14). Take down when app-reds says.
- Batch 6 74e1cfa10 umbrella-tree reds=0; batch 7 umbrella-tree running in umbrella-src.
- **Next shared-interface change: retained-mode L0**: its own cut. lane/retained-l0 is WIP: NEVER merge until
  retained-mode a9b54e85e4a194b91 sends a sha labelled SHARED-INTERFACE. Auditor's items owed before L0: toDFinsupp 0 = 0
  as an equation, an ofDFinsupp inverse, one optionZero instance, a toList code-order lemma for encode, one key
  DecidableEq.
- **Staging 507155c77 (batch 9 so far)**: exorcist 975491262 (bc17cef1b + 7e6850892 `inspect view-resource-document`: a
  doc page in one codec frame, client and codec from one candidate; 253d0bc26 read-scratch pruning; its own copy of the
  admitOwn fix, identical to dc61016cb). Measured (overlay acf55bf9d552 vs batch 7, 100 doc show x2, load 22-25):
  Host+Store CPU -9..14%, codec CPU -17..24%, wall 35.5/30.0 -> 28.5/24.0 ms. Exorcist keeps /ci/exo/w7, w8 (~560 MB each).
  + perf-client 36612f028/6a088183f (Store open's represents decision linear via hash sets, @[csimp]
  representsCheck_eq_fast; first read after idle 20.8 s -> 3.9 s at height ~920; audit SOUND: unconditional funext csimp, hash sets over Nat).
  + hot-path 92828ff96/d7c55dfa0 (birth preparation takes Held directory/authority: callers with an Opened decode no
  directory row; ordinary birth plan prepared once instead of ~4 decodes; Held.eq_load, Loaded.load_eq; audit
  SOUND: stale directory is a type error; four RoomBirthGateAdmission theorems gained an implicit `held`, each
  equivalent to the old via Held.load + eq_load). Before: `doc new` Host CPU 621 ms -> 1000 ms after 500 says (law 17); after-numbers awaited.
- Awaited: infra's forge composed of batch 7 (after its batch 4 rebuild).
- **CLOSED: GET read-path contract** (ember ruled (c)+(d); hot-path owns it statement-first). Never re-run or re-report.
- hbox: / 57 GB free (11:25).

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
- **H1b, operator connection reset on the final say** (acc7cfa03-h1 -hp2, 4/4 counting H1's runs): stage j14 probe,
  `0099-controller-run` exit 1: `room resident: error: final write was never submitted: no terminal outcome; retain the
  exact source operation for an exact retry; the room write failed first: error: Connection reset by peer (os error 104)`.
  H1a (false `refused`) FIXED by faeb1ff0b. Path: resident -> public proxy participant.sock -> private/operator-v2.sock;
  no server-side log line. Owed by app-reds ad85d40779880420c: (a) the reset's cause (proxy, ServeBounds 10 s read
  deadline, operator drop); (b) who performs the exact retry of a never-submitted final.
- **D1, forge demo rebuild (batch 4) `members` step**: `sage` provision failed `local native codec: local process
  request failed: Broken pipe`; downstream apps-bootstrap/reenroll/grain world/seed/door red as consequences. Reruns:
  pending (infra repair after the batch 7 forge composed). Same class as H1b (a local transport drop): app-reds told.
- **H2, attempt-index ENOENT** (batch 7 base): stage j14 worker, `controller-run grain-runtime create` rc=1, ENOENT on
  owner-workspace/attempt-index/by-intent/. Never reached the probe. Distinct from H1. Fix b940b3f50; -hp1 decides.
- **W1, metered workroom not ready** (batch 7 base -c2 and -hp1): stage composed-inputs, `composed-inputs: the metered
  workroom is not ready`. Reruns: yes; same place: yes, with and without the ENOENT fix. One fault, independent of H2.
  CAUSE (hot-path): a gate pin, not the candidate. gate15.sh defaults EDGE_REV=4ea511d; batches 4-6 composed ran on
  dregg-infra 69c17a3. 4ea511d's jworld-scratch.sh apps-bootstrap dropped the JWORLD_MANAGEMENT=distinct branch (tasks
  born as subject 7), while workroom-ready.sh signs as subject 8 -> no-grant. Routed to infra aa72653a8ce442178
  Infra: 4ea511d is an ANCESTOR of 69c17a3 (stale pin; main kept the branch; forge syncs main so never saw W1).
  FIXED: gate15.sh default EDGE_REV=69c17a3 (11:09); -hp2 confirmed (apps, connector PASS). Gates pin a sha; infra sends a newer one when wanted.
- **R1, residents room-summon UNKNOWN** on hbox composed (every batch since 2): hbox cannot judge residents; forge
  composed does (batch 5 forge PASS). Standing, not a candidate red.

## Reports owed

- To root: -hp2 result (H1a fixed, H1b open, W1 gone) and batch 8 launch, in the integrator's next return.
- Batch 8 READY: name to infra, explorer, perf-apps (perf-apps' EtherCalc capture is the after-measurement); launch gate15.

## Reports sent (do not resend)

- 10-31 12:05: hot-path d7c55dfa0 merged (6640356b5); audit requested.
- 10-31 11:55: perf-client 6a088183f merged (45f0ed263), audit requested from a4d9a6f4cba4855ca.
- 10-31 11:50: app-reds: D1 (codec Broken pipe on forge batch 4) as a second transport-drop sighting.
- 10-31 11:35: exorcist: 975491262 merged (507155c77), batch 9; fix already in batch 8. hot-path: a5e757016 in batch 8.
- 10-31 11:28: -hp2 result to app-reds (H1b signature, kept worlds), infra, explorer, perf-apps.
- 10-31 12:30: staging Lean red routed to hot-path a0fee5643746e520c; ack to perf-client.
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

- FIXED a5e757016 (dc61016cb), confirm in batch 8's build: staging Lean red: Kernel/ResourceObservationAdmission.lean:515:33 `simp` made no progress
  (Authorized type mismatch, implicit transparency); `authorizeChecked_eq_fast` (:532) on sorryAx. From hot-path 05a38ff4e
  (merged 7dd554d78); found by perf-client (pool t8). Owner: hot-path a0fee5643746e520c, fix forward.
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
