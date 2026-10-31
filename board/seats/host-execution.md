# Seat: host-execution

Agent: a24974e84d3c540d1 (distilled from a0fee5643746e520c, 2026-10-31 17:27)
Worktree: /Users/ember/dev/minidregg-lanes/host-execution (branch seat/host-execution, rebased onto main and pushed to main;
no side branch). Box tree: hbox pool t3 (`ssh hbox`, `. ~/.minidregg-env`, `lane-tree acquire host-execution origin/main`), native Host builds via
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

## Numbers (hbox, fresh jworld worlds, `doc new` median Host CPU via /ci/hpc/bp/grow.sh + pcm.py; hbox at load ~8, noisy)
| world | 0 says | 500 says |
|---|---|---|
| acc7cfa03 (batch 7) stock | 621 ms | 1000 ms |
| dc61016cb (batch 8) stock | 651 ms | 841 ms |
| 8d4f5935b6ef (batch 8 base + everything above, overlay of the lane head) | 308 ms | 242 ms |
The growth over 500 says is gone on 8d4f5935b6ef (flat within noise); a later run under perf at 500 gave 581 ms, so
quote "~250-580 ms, flat". Profile at 500 (hbox:/ci/hpc/bp/fuse500.perf.data, script fuse500.script.txt, symfs
/ci/hpc/bp/symfs, `python3 /ci/hpc/bp/under.py <script> <frame regex>` tallies callees): of 1,167 samples under
serveFrame, submit 1,002; the session refresh 465 (Light.refresh 270, full Loaded.extend 235, both deriving the same
record's turn); the birth receive 405 (admitDecodedNative 183, receiveCandidateWithFresh 151); encode 401. The world
/ci/hpc/bp/w is UP (stop: `/home/hbox/lanes/integ/dregg-infra-69c17a3/edge/mini/journey/jworld-scratch.sh down
/ci/hpc/bp/w`). persvati has no standing world yet (build-loop's).

## Next (my order)
Numbers (persvati, fresh jworld, Host CPU median, 0 -> 500 member says): slice-1-only 76511e768+fix: doc new
214 -> 248 ms, say 27 -> 46; main 2e85f5676 (slices 2-4 + others' R6(i) etc.): doc new 114 -> 141, say 24 -> 37.
Profile at 500 (hbox, world /home/hbox/hx/w/p4 on 430c4f577a31; scripts /home/hbox/hx/{say,doc}.script.txt,
`python3 /home/hbox/hx/incl.py FILE REGEX`): say 32% and doc new ~25% are `DataSnapshot.install`'s canonicalBytes
closure chain (Served.advance nests one closure per append since the session opened; base reads are list scans,
`State.snapshot`): O(cells + appends) per read, the law-17 growth. doc new: encode (`encodeViaWriter`) ~20%, trie
build ~12% (store-retained/privacy), checkpoint seal 5%.
1. The served state as a persistent map (bytes/roots/available), advanced per write, `DataSnapshot` built from it
   with an exactness equation (asked store-retained a9b54e85e4a194b91 whether it is theirs: DataSnapshot,
   State.snapshot, DurableServed.Served/advance/viewAt).
2. KN2 2b remainder: the walk families (`sessionWalked`, NativeHostReplay `Verified` over the light opening; the 81
   `accepted[i]?` premises become Reader reads; one-shot `startWalked` loads the Store in full twice); fn/carried
   ops; op 130 dry run; the per-family receivers that still take `opened` (share-issue, selected release, fn).
3. App-create turns (op66 BEGIN, route, enrolment, START): mostly the walk families (2).
4. GET read-path contract (draft + astra review paths below).
5. Owed from audits: `append_ref_ahead_refused` decided witness; ref-0/cross-stream scope docstring; positive
   pipeline statement for two appends planned from one read.
6. Ruled for apps-hermes (afb920b22b17049cd): a lifetime paid plan's re-check compares the signed parts, not the
   image coordinates (paid.rs:350); theirs to implement.
GET contract draft: /private/tmp/claude-501/-Users-ember-dev-minidregg/01a192eb-6b7b-70ef-8cad-095d745dabe5/scratchpad/ApplicationReadPermit.lean.draft;
astra review: /private/tmp/claude-501/-Users-ember-dev-minidregg/01a18fa5-51c4-7992-906c-97cb89814dae/scratchpad/done/astra-readpermit-review.md.

## Seams
- store-retained (a9b54e85e4a194b91): L0 on lane/retained-l0 (SparseMap Store/World); after L0 the encode side is mine
  (StoreKey code order = wire `addressKey` order, so `sortedSupport` needs no sort).
- read-path (ad74bb6d4410b48f3): consent onto `Opening`; op 5; cold first read.
- perf-client (a778bbda6509944a5): walk side.
- perf-apps (a70a7655df79c4335): reruns ctp.sh on any candidate I name.
- explorer (a3e5d6dbcd68e616c): reruns the 16-parallel-say rows.
