# Seat: host-execution

Agent: a24974e84d3c540d1 (distilled from a0fee5643746e520c, 2026-10-31 17:27)
Worktree: /Users/ember/dev/minidregg-lanes/host-execution (branch seat/host-execution, rebased onto main and pushed to main;
no side branch). Box tree: dregg-build2 (`ssh bb2`) pool t3 (was hbox pool t7) (`. /home/hbox/pool/pool.env; lane-tree renew hot-path`), native Host builds via
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
1. KN2 stage 2b (root ruling 10-31): `NativeHostSession.start`/`refresh` and NativeHostReplay's admission (`Verified`,
   `DispatchAt`, `SuffixVerified`, every receiver typed over `Opened`/full `Loaded`) retyped over the light
   `Opening`/`OpenedServed` (Kernel/NativeHostLight.lean, Compiler/DurableServed.lean). It removes the O(height) full
   open (read-path measured ~4.3 ms per record: 1,100 ms full vs 125 ms light at head 256) from restart and the
   cold first read, AND the doubled per-request refresh (one view instead of two), so the planned
   "one derived turn shared by both views" memo is NOT built (2b deletes the second view). Scope: ~135
   `opened.durable` uses in Kernel/NativeHost.lean, ~259 in NativeHostReplay.lean, 25 in Host/Main.lean. Order:
   Inventory done (10-31): NativeHostReplay reads the full image 89x, 81 of them the provenance premise
   `present : opened.durable.image.accepted[i]? = some record` (issue, reserve, grant, lifecycle evidence at an
   index); the rest are height/base/baseHeight/logStart/snapshot/extend/prepare. NativeHost: `durable.snapshot` 11x
   (cell bytes, roots: `OpenedServed.served` has them), `image.accepted` 4x, links/index 2x each. Host/Main: 6.
   So 2b's statement change is one premise shape: `accepted[i]? = some record` becomes the Opening's authenticated
   reader's record at i (`DurableHistoryReader`, MAC-verified tag, trusted storage), as `Light.basisVia` already
   reads keys; everything else maps onto `OpenedServed` fields.
   Slice 1 LANDED 4fb012263 (lane-check dregg-build2 RC 0; not yet measured): the session opens the light
   opening only and the full image on first need (`Session.full`, `materialize`, Host `sessionFull`); ops 0, 1,
   2 (all but births) and the receipt readback on light; own appends adopted (`sessionAdopt`); anchor identity
   cached per config. Still full: births (slice 2, delegated to aa75280bd04c5d700 on seat/birth-ground), ops 4/5
   (asked read-path who takes them), the walk families (`sessionWalked`), fn/carried ops.
   (a) inventory what each `Opened` consumer reads (directory, authority, pins, seed/logStart exactness, the image's
   accepted records for historical receipts and walks); (b) give `OpenedServed` the missing fields as maintained
   values; (c) retype receivers family by family (birth first: `Held.of` already isolates it to directory +
   authority); (d) delete the full `Loaded` from the session. Seam with read-path (ad74bb6d4410b48f3): it ports
   ClientConsentCore/ConsentAnchor onto `Opening`; I don't move `Opening`'s signatures without telling it. Rides
   store-retained's L0 (a9b54e85e4a194b91).
2. (i) a write carries its decoded post beside its bytes (`decode bytes = some post`), so the receive and the light
   adopt never decode the Host's own post (ruled ours by retained-mode).
3. App-create turns: op66 BEGIN plan (3-6 s), route (4.5 s), enrolment (4.1 s), START (2.3 s): read and trace each
   (perf-apps' timelines hbox:/home/hbox/lanes/perf-apps/ctpH, ctpI; driver ctp.sh; a70a7655df79c4335 reruns it).
4. GET read-path contract: draft (not elaborated) at
   /private/tmp/claude-501/-Users-ember-dev-minidregg/01a192eb-6b7b-70ef-8cad-095d745dabe5/scratchpad/ApplicationReadPermit.lean.draft;
   astra's NEEDS-CHANGE review at
   /private/tmp/claude-501/-Users-ember-dev-minidregg/01a18fa5-51c4-7992-906c-97cb89814dae/scratchpad/done/astra-readpermit-review.md
   (route selector `app.interfaceId`; v3 manifest read clause in the model now, with an accepting witness; replay
   keyed by `ApplicationDispatchIngress.keyDigest` with a signed read-domain attempt and validity window; R5
   handoff at most once; R8 `journaled ≤ actual ≤ journaled + slack`; reservation custody invariant; payer an
   authorized funding scope, issuer as the default sponsor).
5. Owed from audits: a decided witness for `append_ref_ahead_refused` (head count 1: ref (id,2) refused, (id,1) not),
   docstring scope for ref 0 and cross-stream refs; the positive pipeline statement (two appends planned from one
   read both admit, either order).
6. Row 11: likely unnecessary for the Host after 2b (the light opening already starts at the checkpoint); decide
   after 2b's inventory. The FORMAT trie roots stay with private cells.

## Seams
- store-retained (a9b54e85e4a194b91): L0 on lane/retained-l0 (SparseMap Store/World); after L0 the encode side is mine
  (StoreKey code order = wire `addressKey` order, so `sortedSupport` needs no sort).
- read-path (ad74bb6d4410b48f3): consent onto `Opening`; op 5; cold first read.
- perf-client (a778bbda6509944a5): walk side.
- perf-apps (a70a7655df79c4335): reruns ctp.sh on any candidate I name.
- explorer (a3e5d6dbcd68e616c): reruns the 16-parallel-say rows.
