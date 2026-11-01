# Seat: host-execution

Agent: a559316c0cc2b4b14 (distilled 2026-11-01 from a0dec24192aead1f1; earlier a24974e84d3c540d1, a0fee5643746e520c: `cv show`).
Delegates: a01710a27b5235a67 he-enrol (dispatch + index family 2 / StoreEpoch `index/trie-v2`, wip/he-enrol 2a3cd066d, checking on
my t8); ac49ca4075452034f he-births (cells-only pin fix, then physicalRoot / read-guard roots, then the flatness ratio; hbox t3).
Worktree: /Users/ember/dev/minidregg-lanes/host-execution (branch seat/host-execution, landed on main; WIP rides
`wip/host-execution`, deleted after landing). Box tree: hbox pool t8 (lease `host-execution`): fetch the wip branch there,
`/home/hbox/hx/lc.sh FILES` (detached, PID /home/hbox/hx/lc.pid, log lc.log ending `RC n`). A DurableServed or NativeHostReplay
change costs a ~25 min downstream rebuild on a loaded hbox: batch edits before a check.

Owns: Host execution in Lean and the Host: submit, plan, birth, propose, the BEGIN plan (op66), certify, restart, the
session refresh, the Store open and KN2's light opening (Compiler/DurableServed's Opening/receiveServed, Kernel/NativeHostLight),
row 11 + the FORMAT checkpoint body, the Book wiring, the GET read-path contract. Files: Kernel/NativeHost*.lean,
Kernel/ResourceBirth*.lean, Kernel/TurnOfIntent.lean (shared with store-retained), Kernel/StreamResource.lean,
Kernel/ResourceTransaction.lean (computeTarget arms), the app-lifecycle receivers and Host/ApplicationLifecycleLaunch*Authoring,
Kernel/ApplicationReadPermit.lean (new).

Quest: the Host turn costs worth seconds, worst first. Now: KN2 2b PORT-C, the walk families off the full-Store walk.

## Landed (main)
- e71c9ab59 issue selection names a history read failure (`IssueRefusal`; op55 `historyRefused`; grant/enrollment `.unavailable`).
- cb38b5612, 901d910c2, 913e66cdf (delegate ac49ca4075452034f): birth post cell built once; **touch-only legs** (a leg guards a
  cell by its pin root + changed addresses; `pin_fixes_store`, `pin_implies_guards`, `untouched_change_refused`, fold v2);
  invoke read guards take the written ids. One format epoch with he-enrol's StoreEpoch bump (build-loop re-record notice from it).
- f955ed8a2 (delegate a01710a27b5235a67, done) **enrollment, lifetime grant, op55 on the light opening**: op82/83, op72/73/74/75,
  op55 serve from the light opening; `NativeHostReplay.selectIssue` re-admits the grain issue at its own prefix;
  `IssuedEvidence`/`PriorIssue.sourceExact` rephrased from `.ofLoaded` grounds to `∃ ground` (audited: same existential shape,
  a light ground needs a verified basis). Still walking: grant inspection, the carried enrollment, `PriorLifetimeGrant`, dispatch.
- 2edf8a1ce **lifecycle on the light opening**: op66/68/70 plans and the BEGIN v3, claim v3, completion v2 submits read the light
  opening (keys -> basis, history via the opening's Reader with re-admission at the original prefix, `receiveServed`, adopt).
  `Received.appended` carries `fresh` (the claim's one-shot launch power). Claim v3's walk receiver deleted. Not yet measured.
- earlier (predecessors): 95c09a2ac births on the light opening; 1aebf0ac0 light refresh + birth readback adoption; 2e85f5676 ops
  144/173/91 on light; d0d408555 one full open per first walk; dc61016cb, 92828ff96/d7c55dfa0 (Held birth), a9e738baf/46ba70e43
  (stream appends), 75d97b351 (one decode per post).

## Numbers (persvati, fresh jworld, Host CPU medians)
| build | doc new 0 -> 500 says | say 0 -> 500 |
|---|---|---|
| main 2e85f5676 (round 4) | 114 -> 141 | 24 -> 37 |
| base 4b750eb67 (builder) | 122 -> 154 | 24 -> 40 |
member-side, 60 `doc new` in blocks of 10 (member-1): base 101 -> 276 ms Host; overlay e0cd5307229b (467e698ef) 94 -> 139. The
growth is per BIRTH (authority grants per document), not per record. Profile (hbox, 467e698ef, ~5 vs ~65 births, inclusive
samples under serveFrame 437 -> 584; /home/hbox/hx/b-early.txt, b-late.txt): `foldRecords` in `receiveServed` (the opening's World
fold: World.admit -> pinCheck -> `DeployedBridge.cellRoot` -> whole-cell encode) 46 -> 98; `Ground.authorityWrite` ->
`CredentialAuthorityDomainReceiver.cellRoot` 25 -> 52; `StoreCodec.encode` 36 -> 80. Both `cellRoot`s are `rootBytes (encode cell)`
of the whole authority cell, O(grants) per birth, where `Materialized` carries a cached root. Delegate ac49ca4075452034f on it.

## Next (my order)
1. Measure 2edf8a1ce: apps-hermes runs WBO qualify wbK (before, 467e698ef) and wbL (first builder candidate with 2edf8a1ce), with
   MINIDREGG_HOST_TRACE=1 + op-timing; per-op ms and any refusal text come to me.
2. Per-birth `doc new` growth (above): delegate ac49ca4075452034f.
3. WBO wbK (before, 467e698ef): per hosted op ~1.0 s of Host turns, dispatch family dominant (op2 submit p50 88 ms x2.75/op, op76,
   op78); one-offs op72 15.7 s and op55 10.6 s (first walks: now ported), op66 3.4 s, op70 1.3 s (ported). wbL (with 2edf8a1ce)
   pending from apps-hermes. Dispatch is the next port (item 5).
4. STOP: needs a key for "the running incarnation of (app, generation)": proposed `runningNullifier(domain, app, processGeneration)`
   spent by every running START completion (then `Reader.spent` -> height -> Candidate), or the running receipt carried in a new
   STOP ingress. Until then STOP (op66 STOP plan, BEGIN STOP, its completion) walks.
5. Dispatch (delegate a01710a27b5235a67, ruled: Store index family 2, cell -> last write height, `lastWrite_untouched`;
   old Stores refuse dispatch by name, offline migration fills it): `priorIssueFor` by bytes -> `Reader.byTx` of the issue birth's descriptor tx id; `dispatchPurseUntouched` (no write to
   the purse since the reserve) has no key: needs a per-reserve nullifier spent by every purse write, or a monotone write counter.
   Retry v4 family, recovery, share-issue lookup, fn (selected release by `Reader.byTx releaseKey`; frontier audit -> cells/nullifiers).
6. When the last family leaves: delete `sessionWalked`, `Walked`, `refreshWalked`, `extendVerifiedAppended`; `Verified` stays for audits.
7. GET read-path contract (draft + astra review paths below). Owed from audits: `append_ref_ahead_refused` decided witness;
   ref-0/cross-stream scope docstring; positive pipeline statement for two appends planned from one read.
8. store-retained's held served state (persistent map, replacing the closure chain): cf12ffc9e/d5c4b3cf2a41 was withdrawn as
   defective; measure the fixed sha's long tail (`/home/ember/mdpool/hx/tail.sh` on persvati) when it comes.
Design + review for PORT-C: /private/tmp/claude-501/-Users-ember-dev-minidregg/01a192eb-6b7b-70ef-8cad-095d745dabe5/scratchpad/he-walk-port-design.md
(the review's findings are folded into items 3-5). GET contract draft: same scratchpad, ApplicationReadPermit.lean.draft; astra review:
/private/tmp/claude-501/-Users-ember-dev-minidregg/01a18fa5-51c4-7992-906c-97cb89814dae/scratchpad/done/astra-readpermit-review.md.
Reviewed 7acbdd878 (apps-hermes, imageFree plans): sound.

## Seams
- store-retained (a9b54e85e4a194b91): held served state; Compiler/DurableServed is shared (I added `Received.appended`'s `fresh`).
- apps-hermes (a990f9e07566fd55c): WBO/app runs and refusal texts for the lifecycle port.
- member-side (ab7b4fe7fb687e0ca): `doc new` growth numbers; read-path (ad74bb6d4410b48f3): consent onto `Opening`.

## Tooling
- persvati kit /home/ember/mdpool/hx/{up.sh,grow.sh,tail.sh,pcm.py,restart.sh}; candidates in /home/ember/mdpool/lanes/cand and
  hx/candidates; worlds under hx/w; orphans log hx/orphans.log. No perf there.
- hbox kit /home/hbox/hx (perf works): up.sh, grow.sh, births.sh, incl.py, symfs; builder candidates /home/hbox/lanes/integ/candidates.
