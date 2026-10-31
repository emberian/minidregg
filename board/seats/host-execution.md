# Seat: host-execution

Agent: a0fee5643746e520c (about 420K tokens at 2026-10-31 evening; distill at ~500K)
Worktree: /Users/ember/dev/minidregg-lanes/host-execution (branch seat/host-execution, rebased onto main and pushed to main;
no side branch). Box tree: hbox pool t7 (`. /home/hbox/pool/pool.env; lane-tree renew hot-path`), native Host builds via
`scripts/pipeline/native-loop hot-path <base candidate> <label>` from t7 (~3-15 min; candidates land in
/home/hbox/pool/lanes/hot-path/candidates/<id>).

Owns: Host execution in Lean and the Host: submit, plan, birth, propose, the BEGIN plan (op66), certify, restart, the
session refresh, row 11 + the FORMAT checkpoint body (six indexes, receipt-root log, the sealed World with its
`.held` SnapRepresents), the Book wiring, the GET read-path contract. Files: Kernel/NativeHost*.lean,
Kernel/ResourceBirth*.lean, Kernel/TurnOfIntent.lean (shared with retained-mode's mechanical L0 repairs),
Kernel/StreamResource.lean, Kernel/ResourceTransaction.lean (the computeTarget arms), Kernel/ApplicationReadPermit.lean
(new), docs/HOT-PATH-STATE.md (older detail; this row is the continuation).

Quest: the Host turn costs worth seconds, worst first.

## Landed (all on main)
- dc61016cb `authorizeWith` admits with `admitOwn` (staging red; kept the Pred.eval law check on signed reads).
- 92828ff96 + d7c55dfa0 `ResourceBirthController.Concrete.Held`: every birth preparation, plan and admission reads the
  `Opened` directory and authority (no O(cells) decode); an ordinary birth's authorized plan is prepared once. Audited.
- a9e738baf + 46ba70e43 stream appends computed at the head they meet (`append_planned_root_irrelevant`),
  `Reject.streamRef` (`append_ref_ahead_refused`), PLACE.md client contract. Audited sound.
- 75d97b351 `@[csimp] TurnOfIntent.ofCells_eq_fast`: each written post decoded once per derivation (was 6x).

## Numbers (hbox, fresh jworld worlds, `doc new` median Host CPU via /ci/hpc/bp/grow.sh + pcm.py; hbox is noisy)
| world | 0 says | 500 says |
|---|---|---|
| acc7cfa03 (batch 7) stock | 621 ms | 1000 ms |
| dc61016cb (batch 8) stock | 651 ms | 841 ms |
| staging 5e5ee95f7 + Held | 186 ms | 557 ms |
Profile at 500 (hbox:/ci/hpc/bp/held500.perf.data, symfs /ci/hpc/bp/symfs, callee tally /ci/hpc/bp/under.py): 455/1316
samples are the per-request session refresh (`NativeHostSession.refresh`: Light.refresh 241 via foldRecords/World.admit/
ofCells; full Loaded.extend -> WorldTrack.advance -> ofCells 121; validateLoadedFrom 46; encode 116); the birth plan is
9.6%. Candidate 8d4f5935b6ef (batch 8 + 75d97b351 + C1) is built, not yet measured. Next measurements move to persvati
(the quiet box) per board/README.md.

## Next (my order)
1. Measure 8d4f5935b6ef against dc61016cb on persvati's standing world (`doc new` at 0/500 says).
2. The refresh term (the growing one): (i) a write carries its decoded post beside its bytes (carried value with
   `decode bytes = some post`), so `deltaOf` never decodes on the Host's own path; (ii) one derived turn per record
   shared by the receive, the light view and the full view (a memo keyed by record, with its exactness equation).
   Retained-mode ruled both are ours and node instances; send it the shas.
3. op66 (BEGIN plan, 3-6 s), then route (4.5 s), enrolment (4.1 s), START (2.3 s): read and trace each plan path
   (perf-apps' timelines hbox:/home/hbox/lanes/perf-apps/ctpH, ctpI; driver ctp.sh).
4. GET read-path contract: draft (not elaborated) at
   /private/tmp/claude-501/-Users-ember-dev-minidregg/01a192eb-6b7b-70ef-8cad-095d745dabe5/scratchpad/ApplicationReadPermit.lean.draft;
   astra's NEEDS-CHANGE review at
   /private/tmp/claude-501/-Users-ember-dev-minidregg/01a18fa5-51c4-7992-906c-97cb89814dae/scratchpad/done/astra-readpermit-review.md
   (route selector must be `app.interfaceId`; v3 manifest read clause in the model now, with an accepting witness;
   replay keyed by `ApplicationDispatchIngress.keyDigest` with a signed read-domain attempt and validity window;
   R5 handoff-at-most-once; R8 bounds `journaled ≤ actual ≤ journaled + slack`; reservation custody invariant;
   payer = an authorized funding scope, issuer as the default sponsor).
5. Owed from audits: a decided witness for `append_ref_ahead_refused` (head count 1: ref (id,2) refused, (id,1) not),
   docstring scope for ref 0 and cross-stream refs; the positive pipeline statement (two appends planned from one read
   both admit, either order).
6. Row 11 + FORMAT checkpoint body, after retained-mode's L0 lands and private cells' FORMAT sha.

## Seams
- retained-mode (a9b54e85e4a194b91): L0 on lane/retained-l0 (SparseMap Store/World; its files listed in its 10-31
  message); after L0 the encode side is mine (StoreKey code order = wire `addressKey` order, so `sortedSupport` needs
  no sort).
- perf-client (a778bbda6509944a5): walk side only; row 11 is mine.
- perf-apps (a70a7655df79c4335): reruns ctp.sh on any candidate I name.
- explorer (a3e5d6dbcd68e616c): reruns the 16-parallel-say rows.
