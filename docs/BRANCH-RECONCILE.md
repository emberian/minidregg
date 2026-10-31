# Branch reconcile (2026-10-31)

Present state, rewritten whole. Measured against `origin/integration/staging` at 54e4e4cd5 by `git cherry` plus a read of
every unmerged diff. Verdicts: **a** on staging in another form, **b** wanted and missing (rebased, checked, sent to the
integrator), **c** obsolete or not worth landing (reason given). No branch was deleted.

Since the request, staging absorbed `lane/cx-oracle` (now an ancestor), `lane/statement-fixes` (its checkpoint
72722e54f has a patch-equivalent on staging) and `origin/checkpoint/hot-path-1029-wip` (66de8e6db, a patch-equivalent
on staging; it was itself marked "UNCHECKED, superseded in part by hot-path-cold row 6"): all three are verdict **a**
with nothing left to land.

## Landed on `lane/reconcile` (for the integrator)

| sha | what | check |
| --- | --- | --- |
| `797238235` | share-issue window statement, elaborated (cherry-pick of d08d8c1b0) | `lane-check scratch/ShareIssueWindowStatement.lean` rc 0 in pool tree t6 |
| `3d62a99a9` | AUDIT.md thirty-first pass on that statement (cherry-pick of 602f68f66) | docs only |
| `a8e8a44b1` | ROUTE-LATENCY-STATE.md: the branch's whole-file rewrite adopted | docs only |
| `f8d46dc39` | `Kernel/FnConsumerFrontierProofs.lean` and `FnConsumerFrontierScenario.lean` rescued as module files (scenario `Key` brought to six fields), imported by `Kernel.lean` | `lane-check` of both files rc 0 in t6 |

Branch tip is whatever `lane/reconcile` points at; the four commits above are in order.

## Per commit

| branch | sha | title | verdict | evidence |
| --- | --- | --- | --- | --- |
| `lane/un-deputy` | `a68f336ea` | Deputy state: composed issuer settled on main; apps:sheet overlay asked of the integrator | c | Time-bound entry of the deputy diary (docs/UNTOUCHED-DEPUTY-STATE.md) for the 2026-10-28 freeze / stand-down: it records "nothing is running", world-up.lock queues and an overlay japps1 wait, all long past; the code it tracked is on staging (strict-verify, composed fixture 5c3e7360e, tariff 3a29f1e1b). The lanes it stood down resumed. One loose end kept below: the japps r6/r7 world state. |
| `lane/un-deputy` | `b045653a5` | Deputy state: strict-verify extended to tokens and memos; apps:sheet rides the build after | c | Time-bound entry of the deputy diary (docs/UNTOUCHED-DEPUTY-STATE.md) for the 2026-10-28 freeze / stand-down: it records "nothing is running", world-up.lock queues and an overlay japps1 wait, all long past; the code it tracked is on staging (strict-verify, composed fixture 5c3e7360e, tariff 3a29f1e1b). The lanes it stood down resumed. One loose end kept below: the japps r6/r7 world state. |
| `lane/un-deputy` | `47ec3316e` | Deputy state: the deputy reads the overlay japps1 verdict | c | Time-bound entry of the deputy diary (docs/UNTOUCHED-DEPUTY-STATE.md) for the 2026-10-28 freeze / stand-down: it records "nothing is running", world-up.lock queues and an overlay japps1 wait, all long past; the code it tracked is on staging (strict-verify, composed fixture 5c3e7360e, tariff 3a29f1e1b). The lanes it stood down resumed. One loose end kept below: the japps r6/r7 world state. |
| `lane/un-deputy` | `62374c059` | Deputy state: world-up lock held by cx-store-sweep; bend rows run without the lock | c | Time-bound entry of the deputy diary (docs/UNTOUCHED-DEPUTY-STATE.md) for the 2026-10-28 freeze / stand-down: it records "nothing is running", world-up.lock queues and an overlay japps1 wait, all long past; the code it tracked is on staging (strict-verify, composed fixture 5c3e7360e, tariff 3a29f1e1b). The lanes it stood down resumed. One loose end kept below: the japps r6/r7 world state. |
| `lane/un-deputy` | `b37191a20` | Deputy state: world-up.lock queue after root stopped the sweep diagnostics | c | Time-bound entry of the deputy diary (docs/UNTOUCHED-DEPUTY-STATE.md) for the 2026-10-28 freeze / stand-down: it records "nothing is running", world-up.lock queues and an overlay japps1 wait, all long past; the code it tracked is on staging (strict-verify, composed fixture 5c3e7360e, tariff 3a29f1e1b). The lanes it stood down resumed. One loose end kept below: the japps r6/r7 world state. |
| `lane/un-deputy` | `08d293467` | Deputy state: demo ship freeze; one standby faerie | c | Time-bound entry of the deputy diary (docs/UNTOUCHED-DEPUTY-STATE.md) for the 2026-10-28 freeze / stand-down: it records "nothing is running", world-up.lock queues and an overlay japps1 wait, all long past; the code it tracked is on staging (strict-verify, composed fixture 5c3e7360e, tariff 3a29f1e1b). The lanes it stood down resumed. One loose end kept below: the japps r6/r7 world state. |
| `lane/un-deputy` | `cbf97496a` | Deputy state: stand-down, no candidate and no ship; every faerie stopped | c | Time-bound entry of the deputy diary (docs/UNTOUCHED-DEPUTY-STATE.md) for the 2026-10-28 freeze / stand-down: it records "nothing is running", world-up.lock queues and an overlay japps1 wait, all long past; the code it tracked is on staging (strict-verify, composed fixture 5c3e7360e, tariff 3a29f1e1b). The lanes it stood down resumed. One loose end kept below: the japps r6/r7 world state. |
| `lane/un-deputy` | `4f99aa551` | Deputy state: resume note after stand-down (stale re-wake corrected; all faeries confirmed | c | Time-bound entry of the deputy diary (docs/UNTOUCHED-DEPUTY-STATE.md) for the 2026-10-28 freeze / stand-down: it records "nothing is running", world-up.lock queues and an overlay japps1 wait, all long past; the code it tracked is on staging (strict-verify, composed fixture 5c3e7360e, tariff 3a29f1e1b). The lanes it stood down resumed. One loose end kept below: the japps r6/r7 world state. |
| `lane/un-route-latency` | `6216374ab` | ROUTE-LATENCY-STATE: rewritten whole as present state; the owed measurement and cuts. | b | ROUTE-LATENCY-STATE.md rewritten whole on the branch; staging still has the older diary form of the same file. Cherry-pick conflicted, so the branch final file is adopted as one commit (a8e8a44b1). |
| `lane/un-route-latency` | `3438a1db8` | ROUTE-LATENCY-STATE: record the rephrasing ruling. | b | ROUTE-LATENCY-STATE.md rewritten whole on the branch; staging still has the older diary form of the same file. Cherry-pick conflicted, so the branch final file is adopted as one commit (a8e8a44b1). |
| `lane/un-route-latency` | `682b94c35` | ROUTE-LATENCY-STATE: the landed cuts and what is left. | b | ROUTE-LATENCY-STATE.md rewritten whole on the branch; staging still has the older diary form of the same file. Cherry-pick conflicted, so the branch final file is adopted as one commit (a8e8a44b1). |
| `lane/qualify-doc-contention` | `25c84470c` | WIP (unelaborated): CommutingAppend proofs drafted, not yet checked by Lean | a | Unchecked drafts of the commuting-append proofs; 04840919d on staging says it proves them "from the drafts of 25c84470c checked and finished" (Kernel/ContentCommutingAppendProofs.lean, Kernel/EffectsRevival/CommutingProofs.lean). |
| `lane/qualify-doc-contention` | `162e36a15` | docs: COMMUTING-APPEND-STATE.md: the commuting-append lane's state and next step | c | COMMUTING-APPEND-STATE.md is the handoff of a lane that finished (04840919d: commutingPrepare, movedRootAccepted, twoAppendersOneObservation all proved); its owed list is closed. |
| `lane/qualify-doc-contention` | `a0b45fe8e` | docs: COMMUTING-APPEND-STATE.md: the statements elaborate on dregg-ref | c | Same state file (statements elaborate on dregg-ref); overtaken by the proofs landing. |
| `lane/app-market-b5` | `e4dad8b6b` | app-market b4/b6: WordPress, OwnTracks and Hummingbird write diagnostics and fallbacks | c | The WordPress, OwnTracks and Hummingbird write recipes it patched were replaced: write_WordPress and write_Hummingbird are now typed_app_row (knowledge-interface.sh, data-interface.sh), write_OwnTracks was rewritten in b6.sh; b6-hb.py is gone. The diagnostics were for the 349e59ef1 candidate. |
| `lane/app-market-b5` | `33ee01407` | checkpoint: save uncommitted work (root, 2026-10-30, before travel pauses) | c | Checkpoint adding scratch batch b5x.tsv; all five of its apps (OwnTracks, ExpenseOwl, WordPress, HackerCMS, Hummingbird) already have rows in b2/b4/b6/knowledge.tsv on staging. |
| `codex/controller-anchor-fix` | `e67034979` | Use a short private consent anchor directory for isolated controllers | a | On staging as the same change in deploy/spk-host/controller-world.py (unit line 716 and controller_child env), its test (tests/test_controller_world.py:120-126), and the install-user-world pin, now fa485c05... for the current file. |
| `codex/controller-anchor-fix` | `56f433bc6` | Keep bounded controller CLI helpers from spawning detached residents | a | Same: MINI_CODEC_RESIDENT=0 / MINI_CONSENT_RESIDENT=0 in controller_child are at controller-world.py:2105-2106 on staging, tested at test_controller_world.py:126. |
| `lane/untracked-2026-10-27` | `ab2d805a4` | Safety copy of untracked files from the shared minidregg worktree | b/c | Safety copy of 15 untracked files; docs/review/2026-10-27-untracked/TRIAGE.md on staging already judged each. Per file: Host/ClientConsentSettingsScenario.lean identical on staging (a). Kernel/FnConsumerFrontierProofs.lean and FnConsumerFrontierScenario.lean (b): rescued as module files, Key updated to six fields, added to Kernel.lean, sha in the Sent section. The rest (c): Uwueave trio (needs ember to declare the uwueave Lake package, otherwise unbuildable: unknown module prefix), ApplicationDispatchAgentPurse/Reserve (red: DeclaredEffectPageMaterializer.pageAt exists nowhere; the paid-dispatch route went to ApplicationDispatchAgentPaidInspection and the Lifetime dispatch modules), build-native-host-bounded.py (ember decides; written against pre-module Lake traces, so stale for Lean 4.35 and swarm-build now bounds builds), bootstrap-agent-platform.py, probe-authority-domain.lean, probe-fn-accepted-origin-outbox.lean, probe-fn-selective-fn-receiving.lean, ProbeCompletionAdmission.lean (hash-pinned evidence, already tracked under docs/evidence/2026-09-27-r3-completion-diagnostic/), and the stray "\|member-socket\|unknown" shell-redirect scar. |
| `lane/app-market-b3` | `d29428fa7` | B3-STATE.md: the share-window statement is parked by the demo freeze | c | Says the share-window statement failed to elaborate (InitialFunding, descriptorPlannedAt unknown); d08d8c1b0 fixed exactly that, so the note is false once the statement lands. |
| `lane/audit-platform` | `602f68f66` | Thirty-first pass: share-issue plan window | b | AUDIT.md thirty-first pass on the share-window statement (its blocking item: prepareSourceBirth's height). Not on staging; pairs with d08d8c1b0. Cherry-picked clean. |
| `lane/cx-regen` | `5f0f5cb1d` | checkpoint: save uncommitted work (root, 2026-10-30, before travel pauses) | c | Checkpoint extending scripts/codec-shapes-regen.py and its test; both files were deliberately deleted on staging by 977dce2e3 "Remove the persisted-codec definition fingerprint census" (no codec pins, per ember). |
| `lane/hot-path-v4` | `7b2e8fecd` | checkpoint: save uncommitted work (root, 2026-10-30, before travel pauses) | c | Checkpoint adding Opened.below to Compiler/DurableFastForwardSpec.lean, the "amendment next" in HOT-PATH-STATE; no consumer, unelaborated (no Lean has run on it), and it changes Impl.ff and the Opened structure every open proof depends on. Left to the hot-path lane to redo with its consumer. |
| `lane/hp-effects` | `567d79eb8` | checkpoint: save uncommitted work (root, 2026-10-30, before travel pauses) | a | Checkpoint re-cutting ContentProofs/EngineProofs/PrepareProofs for the freshness gate; staging has it in the moved files Kernel/EffectsRevival/{ContentProofs,PrepareProofs}.lean (fresh : root = pre.root ∨ commutes, Handler.admits) and Effects/Revival/EngineProofs.lean (Handler.admits, CellState.Materialized.ext), via 0ca243107 and 04840919d. |
| `lane/pd-grain-class` | `4ef18de80` | checkpoint: save uncommitted work (root, 2026-10-30, before travel pauses) | c | Checkpoint: one doc line moving the slice drop-in path from ~/.config/systemd/user to /etc/systemd/user in deploy/spk-host/README.md. Unreviewed and unverified (the broker renders units under /run/user/<uid>/systemd/user; either path is read by the user manager), no code depends on it. |
| `lane/perf-rust-ops` | `4142e1902` | perf-rust: handoff state for the in-session tool operations | c | Handoff note for Option B; the work itself (40392d4dc: operations 195-197, runToolSession in Host/Main.lean:7248, tool_in_session in dispatch_native.rs:606) is an ancestor of staging, which also resolves the note's "Lean not checked". |
| `lane/proofs-rerecord2` | `fd8e091d3` | rerecord.sh: a red fixture is stale data; cover the doc-write run too | a | Same change landed as fb8a638f8 "rerecord: a fixture is stale when it no longer elaborates; the doc-write fixture re-records too" (scripts/native-accepted-fixture/rerecord.sh covers Fixtures.NativeDocWriteFixture, exits 4 and 5). |
| `lane/qualify-sharefix` | `1ed5a180f` | checkpoint: save uncommitted work (root, 2026-10-30, before travel pauses) | a | Checkpoint of same-store-app.py delegate_share/owner_reference_names and the ws-continuity-fixture.py shareDelegation issue path; staging has the same change in other form from 5c3e7360e (merged 1956d1a63): same-store-app.py:134-151 writes f[shareDelegation], ws-continuity-fixture.py:419 reads it as the appDelegateCapability. |
| `lane/un-bend-seed` | `e65e5dfbd` | Tariff 6/2 re-run note: what passed and what the demo freeze stopped | c | Evidence note for a tariff re-run on candidate 76758dba that the freeze stopped; stale candidate, no row needed a price changed. |
| `lane/un-ifaddrs-shim` | `f2495cad8` | docs: state of the getifaddrs shim lane (the IPython write row is owed after the demo free | c | The shim is on staging (native/spk-host/shim/libifaddrs-lo.c, build.rs); the IPython write row it owes is now typed_app_row ipython-notebook (data-interface.sh:4) and write_IPythonNotebook in b8.sh is gone. |
| `lane/un-public-read` | `630e50c21` | docs: public-read lane state (403 fix, cold-start 504 findings, post-demo warm-at-spawn) | c | Cold-start 504 finding; the post-demo warm-at-spawn fix is on staging (native/mini-web-spawn/src/spawn.rs and main.rs, Helper::warm_public). |
| `lane/un-share-window-statement-2` | `d08d8c1b0` | share-issue window statement: elaborated on dregg-ref, Accepted change as real Props | b | Staging holds only the unelaborated statement (3baaa9d73); this is the elaborated one (Accepted change as real Props). Share-issue admission still rebuilds the descriptor at submit height (ApplicationShareIssueSource.lean unchanged since 349e59ef1), so the statement is still the only record of the window fix. Cherry-picked clean. |
| `lane/un-story-install` | `cf5602792` | Park note for lane/un-story-install: runs owed and the unexplained signed-message mismatch | c | Park note. Its landed list is on main (a8376ce8f ... 53e71b418). The open "signed message mismatch" is already recorded in docs/UNTOUCHED-DEPUTY-STATE.md on staging (line 59), and REHEARSAL-3-BOARD.md; the JSGM rows it owes are run by the journeys. |

## Held, not touched (Oracle7)

- `lane/cx-oracle`: 0 unmerged now, it is an ancestor of staging.
- `codex/oracle-v7-qualification` (= `lane/oracle-v7-qualification`, tip b32f15604), 4 commits, acceptance-harness
  work under `deploy/oracle/acceptance/`: 126675f46 resume a stopped Oracle activation through the native successor
  lifecycle (`recover_activation.py`, its test); 93db9b06e recover an unreserved API call through native audit before
  resuming (`recover_application_api.py`, its test); d1bbe302a match the rendered question card before checking the
  browser answer (`browser_probe.mjs`); 16e2cf912 match lifetime route payer pins to native target and authority slots
  (`agent.py`, `prepare-lifetime-route.sh`).
- `lane/oracle-codex-recovery`, 2 commits: 0903ae21f recovers the five Oracle files' edits lost to the 13:00 UTC reset
  (`agent_api_native.rs`, `agent_api_server.rs`, `resident_service.rs`, `oracle-shared-data-journey.sh`,
  `oracle-stop-inspection-probe.py`); 21c326003 acceptance world and report, `install-user-world`,
  `namespace_identity.rs`, `resident_privilege.rs`, `docs/oracle-replay-2026-10-27.md`.
- `lane/oracle-codex-2`: 21c326003 only (the same commit).

## Needs ember

- Uwueave trio (`Compiler/UwueavePreoProjectionV2.lean`, `prover/generated/` and `prover/tests/` copies): lands only if
  the `uwueave` package is declared as a Lake dependency; otherwise delete all three together.
- `scripts/build-native-host-bounded.py`: a real bounded builder, but written against pre-module Lake traces; rescue
  means porting to Lean 4.35 and wiring into the host build, delete means `swarm-build` is enough.
- The untracked files themselves are still untracked in the main worktree (see its `git status`); the safety copy
  `ab2d805a4` holds them, so they can be removed there once the verdicts above are accepted.
- japps r6/r7 world state left under `/var/lib/mini-spk-worlds/9120f40565eb72ce` and `fac66d0c8d5fecfc` (from the
  deputy diary's resume note) needs root or ember to clear; unknown whether it still exists.

## Branches safe to delete

Every unmerged commit is verdict a or c, or its b was cherry-picked/rewritten onto `lane/reconcile` once that reaches
staging. Deleting a branch makes its commits unreachable, so the c-verdicts keep their record only in this table.

- Verdict a only: `codex/controller-anchor-fix`, `lane/qualify-sharefix`, `lane/proofs-rerecord2`, `lane/hp-effects`,
  `lane/statement-fixes`, `origin/checkpoint/hot-path-1029-wip`, `lane/cx-oracle`.
- a plus doc-only c (nothing wanted): `lane/qualify-doc-contention`, `lane/app-market-b5`, `lane/cx-regen`,
  `lane/un-public-read`, `lane/un-ifaddrs-shim`, `lane/un-bend-seed`, `lane/un-story-install`, `lane/perf-rust-ops`,
  `lane/app-market-b3`, `lane/pd-grain-class`, `lane/un-deputy`.
- After `lane/reconcile` reaches staging: `lane/un-route-latency`, `lane/un-share-window-statement-2`,
  `lane/audit-platform`.
- Keep for now: `lane/hot-path-v4` (its c is the unfinished `Opened.below` amendment, which the hot-path lane may want
  to read), `lane/untracked-2026-10-27` (only copy of the untracked files until ember rules on the list above), and the
  four Oracle holds.
