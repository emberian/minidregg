# Seat: host-execution (handoff, wound down 2026-11-01)

Last agent: a559316c0cc2b4b14 (distilled from a0dec24192aead1f1; earlier a24974e84d3c540d1, a0fee5643746e520c). Read any of them
with `cv show <id>`; elided tool outputs with `cv cat <id> <tool_use_id>`. Delegates (both stopped): a01710a27b5235a67 he-enrol
(light-opening ports: enrollment/grant/op55, dispatch, Store index family 2), ac49ca4075452034f he-births (per-write whole-cell
re-encode/re-hash).

## What this seat owns
Host execution in Lean and the Host: submit, plan, birth, propose, the BEGIN plan (op66), certify, restart, the session refresh, the
Store open and KN2's light opening (Compiler/DurableServed's Opening/receiveServed; Kernel/NativeHostLight), row 11 + the FORMAT
checkpoint body (and so World journal / leg format epochs), the Book wiring, the GET read-path contract. Files: Kernel/NativeHost*.lean,
Kernel/ResourceBirth*.lean, Kernel/TurnOfIntent.lean (shared with store-retained), Kernel/StreamResource.lean,
Kernel/ResourceTransaction.lean (computeTarget arms), the app-lifecycle/dispatch/enrollment/grant receivers,
Host/ApplicationLifecycleLaunch*Authoring, Kernel/ApplicationReadPermit.lean (new, draft). Shared: Compiler/DurableServed.lean with
store-retained (its Held/Served/install/advance/replay lines are store-retained's; Opening/receiveServed/World fold are this seat's).

Quest: the Host turn's costs, widest first; ember's bar is about 1 ms of warm work per action and nothing slower as history grows
(law 17); a derived value is maintained, never recomputed per request.

## Landed on main (newest first)
- 462919a4c (he-births) invoke: target pre-roots and read guards read the ground snapshot's roots, not a re-hash (five `@[csimp]`
  function equalities; statements unchanged). Audited.
- 913e66cdf (he-births) invoke read guards take the written ids without building the target writes.
- 901d910c2 (he-births) **FORMAT, fold v2**: a World leg carries only its changed ops; the turn's existing pin on the cell's root
  guards the rest. Theorems `pin_fixes_store` (pin root equality -> same store or `RootCollision`), `pin_implies_guards` (the old
  per-address guards follow), `untouched_change_refused` (teeth), `touchPatch_run`, `touchPatch_valid_iff`. Audited. Changes the
  World journal digest and the v4 checkpoint system leaf: the build-loop re-record notice is NOT yet sent (it was to go out together
  with index/trie-v2, below). Tell build-loop (a4141abe7297fdc4b), privacy (a7bf41b0d8bb24813), member-side (ab7b4fe7fb687e0ca).
- cb38b5612 (he-births) a birth's post cell built once (about 5 encodes -> 1); the authority write law needs no decode.
- e71c9ab59 issue selection names a history read failure (`NativeHostReplay.IssueRefusal`: `.history` / `.refused`); op55 answers
  `Error.historyRefused` (Host `.unavailable`); grant and enrollment receivers `.unavailable` on history (law 10).
- f955ed8a2 (he-enrol) session enrollment (op82/83), agent lifetime grant (op72-75), share-issue lookup op55 on the light opening;
  issue evidence rephrased from full-image grounds to `∃ ground` (audited, not weaker). WBO wbK had op72 at 15.7 s, op55 10.6 s.
- 2edf8a1ce **lifecycle on the light opening**: op66/68/70 plans and BEGIN v3, claim v3, completion v2 submits read the light opening
  (keys -> basis, history via the opening's Reader with re-admission at the original prefix, `receiveServed`, adopt).
  `Received.appended` carries `fresh`. Claim v3's walk receiver deleted. NOT YET MEASURED (wbL below).
- earlier: 95c09a2ac births on light; 1aebf0ac0 light refresh + birth readback adoption; 2e85f5676 ops 144/173/91 on light;
  d0d408555 one full open per first walk; 92828ff96/d7c55dfa0 Held birth; a9e738baf/46ba70e43 stream appends; 75d97b351.

## In flight (branches, not on main)
- **origin/wip/he-enrol, tip 32de8a4d4 (on e71c9ab59). NEVER COMPILED** (the hbox pool was full). Two commits:
  - 2a3cd066d: Store index family 2, cell id -> height of the last record that wrote it, and the StoreEpoch bump `index/trie-v1` ->
    `index/trie-v2` (a pre-v2 Store must refuse by that tag, by name; worlds re-genesis; no migration tool). Theorems:
    `lastWrite_untouched` (soundness direction only: answer = r+1 -> no later write of the cell; the converse fails only on a cSHAKE
    key collision, which can only refuse), `logical_changes_exact`, `lastWrite_later_write` (teeth), `apply_transaction_only`,
    `apply_steps`; scripts/kn2/index-omission.{lean,sh} pin `apply_steps`.
  - 32de8a4d4: plain dispatch on the light opening (op34 submit, op35 lookup), `IssueSelected` generalized to legacy + grain,
    `selectIssueByBytes` (the issue's tx id = the birth descriptor's `transactionId` inside `issueIngressBytes` -> `Reader.byTx` ->
    `selectIssue`), token census rows, `Opening.withFreshTip` in DurableServed.
  - Next step: lane-check, riskiest first: the Compiler DurableIndex files (`lastWrite_untouched` by reverseRecOn,
    `logical_changes_exact`, `apply_*`), then Kernel/NativeHostReplay, Kernel/ApplicationDispatchReceiver/Lookup/Projection/
    StreamContinuity (their `simp` proofs of the light theorems), Compiler/DurableServed (`withFreshTip`), then Host/Main and
    TokenCensus/Table. Land as one epoch set with fold v2's re-record notice.

## Next steps, in order
1. Check and land wip/he-enrol (above) + send the single re-record notice (fold v2 901d910c2 + index/trie-v2).
2. Measure: apps-hermes (a990f9e07566fd55c) reruns WBO as wbL on the first builder candidate that contains 2edf8a1ce AND 8834e4862
   (hosted receive names its awaited events; an older Host refuses the new descriptor). Compare against wbK (/ci/j-wbK on hbox:
   op66 3.4 s, op70 1.3 s, op72 15.7 s, op55 10.6 s; per hosted op about 1.0 s of Host turns, mostly op2 submits p50 88 ms x 2.75
   per op and op76/op78 dispatch). Note wbK's 2.3 s/op wall was inflated by an invalid qualify write (fixed 40cde03d5/dc721e35c).
3. Remaining whole-cell hashes on a growing cell (flatness): `WorldKindLawDependencies.loadTarget` in the observation authorize
   (Kernel/ResourceObservationAdmission.lean:182, :208, `kindDependenciesExact`) and births' `planWrites` packedWrite factory/book
   pre-roots (Kernel/ResourceBirthController.lean:334-335; `writePreExact` decides them by hash) still hash the whole target; same `@[csimp]` route
   as 462919a4c (read `ground.view.model.roots`). Then the flatness bench (`scripts/perf/flatness-bench.py --n 100 --lo 10`, see
   scripts/perf/flatness-gate.sh) on a native build of main, and `doc new` re-profiled at about 65 births (hbox /home/hbox/hx/births.sh).
4. The light World fold's pin re-encode (`World.pinFails` -> `DeployedBridge.cellRoot`, flat at about 2% on the flatness profile,
   about 27/584 late samples on births): only if it still grows per birth. Design: a cells+retired invariant against
   `served.canonicalBytes` carried in `Opening.world`, established once at both `startOf`s in DurableServed's `extendVerified`
   (seed and checkpoint) and advanced per record by one lemma (the shape of store-retained's `Held.install_agrees`); `snapPinFails`
   reads roots. WorldTrack does not apply (SnapRepresents needs the full consumed set/journal).
5. Dispatch, rest (ruled design): agent dispatch (issue by bytes as above; `reserveIndex` in the ingress), lifetime dispatch
   (index-based: grantIssueIndex, reserveIndex; issue < grant < reserve as Nat comparisons), retype `PriorLifetimeGrant` /
   `LifetimeGrantIssueAt` from `∃ Opened` to a ground plus a nested `GrantSelected`, and replace `dispatchPurseUntouched` (no purse
   write since the reserve; NativeHostReplay ~248, uses in the two *PaidAuthoring files) by the family-2 answer
   `∃ found : ByCell head ⟨purseTask⟩, found.height = reserve.index + 1`; then op76/op78. Rejected: a purse write counter (weaker:
   accepts after no-op writes) and a per-reserve nullifier (a generic write cannot name a reserve).
6. STOP still walks (op66 STOP plan, BEGIN STOP, its completion): needs a key for "the running incarnation of (app, generation)":
   proposed `runningNullifier(domain, app, processGeneration)` spent by every running START completion (`Reader.spent` -> height ->
   Candidate), or the running receipt in a new STOP ingress. Then retry v4, recovery, the grant inspection (`lookupVerified`), the
   carried enrollment path, fn (selected release by `Reader.byTx releaseKey`; the frontier audit -> cells/nullifiers; its global
   `fault` flag needs a ruling).
7. When the last family leaves the walk: delete `sessionWalked`, `Walked`, `refreshWalked`, `extendVerifiedAppended`; `Verified`
   stays only for audits.
8. GET read-path contract: draft /private/tmp/claude-501/-Users-ember-dev-minidregg/01a192eb-6b7b-70ef-8cad-095d745dabe5/scratchpad/
   ApplicationReadPermit.lean.draft (scratch, may be gone; recreate from `cv show a24974e84d3c540d1`). Owed from audits:
   `append_ref_ahead_refused` decided witness; ref-0/cross-stream scope docstring; a positive pipeline statement for two appends
   planned from one read.
9. store-retained's held served state (persistent map replacing the closure chain) is theirs; when it lands, measure the long tail
   (persvati /home/ember/mdpool/hx/tail.sh).

## Numbers (Host CPU medians, ms)
| build, box | doc new 0 -> 500 says | say 0 -> 500 |
|---|---|---|
| main 2e85f5676, persvati | 114 -> 141 | 24 -> 37 |
| base 4b750eb67, persvati | 122 -> 154 | 24 -> 40 |
member-side, 60 `doc new` (persvati): base 101 -> 276; e0cd5307229b (467e698ef) 94 -> 139. Growth is per birth (the authority cell
gains grants per document), not per record. hbox perf at ~5 vs ~65 births (b-early.txt / b-late.txt in /home/hbox/hx): receiveServed's
World fold 46 -> 98 samples, the authority write 25 -> 52, `StoreCodec.encode` 36 -> 80; cb38b5612/901d910c2/462919a4c target these,
unmeasured since. Flatness baseline (467e698ef, n=60): submit CPU 3.1x, propose CPU 3.0x (bound 2x); NOT re-measured after
the four he-births commits (the native build of 462919a4c was stopped at wind-down). Flatness profile (467e698ef, early 413 vs late 532): `physicalRoot` 40 -> 80, `loadTarget` 23 -> 46 (462919a4c
addresses), pin re-encode 8 -> 10.

## Open reds (board/REDS.md, builder round on d5e858b2222b)
- gate:flatness-submit `flatness-submit FAIL` (one document appended 100x: submit CPU 32 -> 165 ms, propose 14 -> 61; bound 2x;
  /ci/f-d5e858/submit.log) and gate:flatness-run `flatness-run FAIL`: owners host-execution + store-retained. Since 9317f32fc the builder
  publishes flatness and does not gate on it. Remaining causes: next step 3, the propose-side document reads (read-path's c4a1e4cf4
  and bounded "document tail" read with member-side), store-retained's held state.
- gate:composed:restart `composed restart blocked`: owner host-execution, blocked on residents (member-side/infra); unexamined.

## Box state left behind
- hbox: pool tree t8 released (lane-tree release host-execution); he-births released t3 and t5, he-enrol t3; no job of this seat or its
  delegates running. Stopped at wind-down (logged in /home/hbox/hx/orphans.log): he-births' orphaned `lake build` 869410 in t5 and
  its watcher loop 116528. he-births' scratch (profiles, flatprof.sh, check logs): /home/hbox/hx-births.
  Kit /home/hbox/hx: lc.sh (lane-check FILES on a tree, PID lc.pid, log lc.log ending `RC n`), births.sh, incl.py
  (`python3 incl.py FILE REGEX [TOP]`: inclusive frame counts), up.sh/grow.sh, symfs. Builder candidates
  /home/hbox/lanes/integ/candidates. he-enrol released t3.
- persvati: no world of mine running (worlds base/held/lbase/lheld under /home/ember/mdpool/hx/w are down; data left, no new data
  written). Kit /home/ember/mdpool/hx/{up.sh,grow.sh,tail.sh,pcm.py,restart.sh}; orphans log hx/orphans.log. No perf there
  (perf_event_paranoid=4).
- Mac worktree /Users/ember/dev/minidregg-lanes/host-execution (seat/host-execution, clean, at main); he-enrol's worktree
  /Users/ember/dev/minidregg-lanes/he-enrol (wip/he-enrol), he-births' /Users/ember/dev/minidregg-lanes/he-births.

## Seams
store-retained (a9b54e85e4a194b91) held served state; apps-hermes (a990f9e07566fd55c) WBO/app runs and refusal texts; member-side
(ab7b4fe7fb687e0ca) doc-new numbers, residents; read-path (ad74bb6d4410b48f3) propose reads, consent onto `Opening`; build-loop
(a4141abe7297fdc4b) re-records; privacy (a7bf41b0d8bb24813) consent provider reads the World journal digest.
