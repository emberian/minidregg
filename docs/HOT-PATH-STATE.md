# HOT-PATH state — 2026-10-31, hot-path successor (Opus, agent a86738fc)

Law 17: a fixed-size operation may cost at most O(log n) in accumulated history
and state, or O(changed · log n) for a multi-entry change. Full exports must be
charged for their output; audits (`audit`, `store-audit`, `pay-claim-audit`) are
genesis replays by design. K-HIDE-ROTATE stays.

**Threat model (ember, 2026-10-31):** "We trust the storage device. That isn't
'operator trust', that's just the threat model we're working within. … we DO NOT
need validity proofs." So every open, provider start and walk resumes from the
Store's MAC-verified checkpoint plus the suffix; what is checked is every record
after the snapshot. CONSENT-OWN is retired, replaced by CONSENT-STORE
(Kernel/ConsentAnchor.lean). Anchors bind to the consent statement epoch and the
settings, not the executable, so they survive ships.

Branch `lane/hot-path-cold`, on the Lean 4.35 bump cdb399b47 (Mac worktree
`/Users/ember/dev/minidregg-lanes/hot-path-cold`). hbox: `/home/hbox/lanes/hpc/src`
is a 4.30 tree (the old-base measurement variant `measure/hpc-oldbase`, which opens
x1's be4ef7510-epoch Store); a 4.35 tree is seeded from the integrator's after its bump
build. hbox scratch `/ci/hpc` (`x1s/` = a copy of x1's Store at head 769).
Integrator: aeb671706eb3f70d7.

## The genesis / full-history sweep (law 17), in rank order

From the sweep of 2026-10-31 (agent abda12fb71c02d194, read-only; file:line on the
tree at that date). H = log height, k = entries returned. Status: **fixed** (on the
lane, check status in the next section), *open*, or audit (by design).

| # | Path | Cost | Reached by | Fix | Status |
|---|---|---|---|---|---|
| 1 | `objective-quote` → `startWalked` → `verifyLoaded` (Host/Main) | O(H) open + O(H) re-admission | every Objective invocation | the checkpoint+suffix opening (`openExisting`); the quote reads only `.opened` | **fixed** |
| 2 | `since` view: `sinceFrom` over all of `accepted` (NativeObservationController) | O(H) decodes per query | every signed `since` | `sinceView` starts at the first record above `after` (`sinceFrom_skip`, `sinceView_eq`); a `drop` pointer walk remains | **fixed** (decode cost); the walk needs an indexed record store |
| 3 | `tail` view: `streamPayload` `accepted.find?` per entry | O(k·H) compares | every stream tail (chat, scenes) | TxIndex + indexed records | *open* (needs an indexed record store) |
| 4 | `sessionWalked` / `startWalked` → `verifyLoaded` (NativeHostSession) | O(H) re-admission | first walk-provenance request per Host process; every per-verb Host | walk from the Store checkpoint (CONSENT-STORE's anchored basis for the walk families) | *open*: the walk's certificate lists (Prior*) are minted only by genesis admission; restate them over trusted storage |
| 5 | `refreshWalked` → `extendVerified` prefix encode+compare | O(H) per growth | every walk-provenance request after an append | extend the retained walk from its own target with `extendFrom`'s append proof (`extendVerifiedAppended`) | **fixed** |
| 6 | `*Lookup` `findIdx?` + `receipts[index]?` (receipts = `toList`) | O(H) | every `*-lookup`, readback confirm | `Loaded.firstIndex` (TxIndex, `firstIndex_eq`) + `Verified.receiptAt` (`receiptAt_eq`) | **fixed** (the `accepted[index]?` list walk remains) |
| 7 | receiver idempotency `findIdx? … != none` | O(H) per submit | these families' submits | `Loaded.firstIndex` | **fixed** |
| 8 | Fn scans (FnSelectedPollReleaseLink, FnOriginOutbox, FnConsumerProgress, FnCatalogOwnRProgress, FnReplyConsumption) | O(H) | Fn poll/ACK/consume | index at admission | *open* |
| 9 | `inspect-stop-claim`, `selected-release-fn-ack`, `fn-empty-page-ack`: `load` + `verifyLoaded` | O(H) | per command | as #4 | *open* |
| 10 | `pay-claim-status` (startWalked) | O(H) | per command | `openExisting` | **fixed**; `pay-claim-audit` and `diagnose-completion` stay audits |
| 11 | every one-shot Host verb: `start` → `loadChained` reads every entry, MACs every tag, decodes every record, rebuilds six indexes | O(H) per process | every Host process (the CLI spawns one per verb unless `--socket`) | checkpoint carries the indexes; read checkpoint + suffix only | *open* (the biggest constant left) |
| 12 | `story new`: ~22 separate submissions | 22 × per-write | each `story new` | batch the template's invokes; per-write cost (rows 11, 13) | *open* |
| 13 | consent fallbacks: `verifyInitial` / `refresh` suffix failure and `upgrade` (`Basis.full?`) → genesis `verifyLoaded` | O(H) | rare suffix failures; ops 236/224 once per provider | as #4 | *open* |
| 14 | `atPrefixFrom` from the seed when no kept checkpoint ≤ height | O(height) | `at` reads below the open base | nearest retained checkpoint ≤ height | *open* |
| 15 | `audit`, `store-audit`, `pay-claim-audit` | O(H) | operator / `mini pay --action audit` | audits by design; keep them out of routine flows | audit |
| 16 | FnEvidence `verifyBytes` → `loadImage` (whole package prefix) | O(H) | `verify-evidence`, grain-origin, portable-verify-fn | checkpoint + suffix packages | *open* |
| 17 | JointSourcePrefixValidation (`loadImage` + `verifyLoaded` per proposal) | O(H)/block, O(H²) total | consensus proposals | validate the block suffix over the retained tip | *open* |
| 18 | GenericSimplexParticipant `reloadSource`: `load` + `extendVerified` | O(H) | after a lost reply / CAS conflict | `extendFrom` + `extendVerifiedAppended` | *open* |
| 19 | CarriedSegment `buildTarget` → `loadImage` | O(H) | carry receive/plan | resume from the source checkpoint | *open* |
| 20 | `retainedDispatchReceipt` `accepted.any`; RetainedSegmentInspection `findIdx?` by event bytes | O(H_src) | carried-registry dispatch | index by event-bytes digest | *open* |

Consent (CONSENT-STORE, sweep rows 13 partly): a provider start is the Store's
checkpoint + the suffix (no genesis fold); catch-up is O(records since the client last
looked), each natively admitted (~30 ms at head ~1,000).

## Flatness submit red: where the Host's per-append CPU goes (35737eac4, 2026-10-31)

flatness-submit on 35737eac4 (gate13): submit CPU went from 100 to 847 ms over heights
3..103 (8.5x), propose from 24 to 229 ms. The workload is appends to one document, so the
document's size grows with history. I profiled the Host child during ops 85-100 with dwarf
call graphs (hbox `/ci/hpc/fby`; the Host runs from a memfd, so `perf report
--symfs=/ci/hpc/fby/symfs` maps it back to the candidate binary). Inclusive shares of the
Host's CPU:
- **ContentResource.project, 17.7%**: the policy projection computes all ~30 `content/*`
  slots eagerly, and each is a pass over the whole content store (bytes, payload bytes,
  `support.card`, names unique, body/annotation writes), before and after. The law reads
  two of them. On top of that, the slot table (`PredCompile.slotTable`: String-keyed
  HashMap inserts of every slot, both sides) is 22.8%, and `inputsInRangeFast` is 14%.
- **DFinsupp.support → Multiset.dedup, 4% and quadratic** (`List.pwFilter`), via
  `ContentResource.elementCount` and `support.card`.
- **StoreCodec.encode, 10.5%** (StreamCodec writer 19%): the whole document cell is
  re-encoded per append. That is O(cell), not O(change).
- **The observation authorize, 15%** (`NativeObservationController.checkGrants` →
  `ResourceObservationAdmission.projectWith`, with `PreparedLaw.witness` at 8.5%): a
  second full projection and law witness, inside `NativeObservationOpeningCache.queryLoaded`.
- `prepareAuthorizedLoaded` 31%, `submitInvokeLight` 24%.

**Root cause of the slot volume:** `DeclaredResourceController.participantSlots` puts
`bytesSlots "resource/bytes" 0 (encode cell)` into the policy state: one String-named slot
per byte of the target cell's encoding, and three times over (local, `joint/target/…`,
`joint/index/…`), on both sides, for every projection (the invoke admission and the
observation check). A 5 KB document is about 30,000 formatted names and HashMap inserts
per projection. This dominates `slotTable` and the String hashing.

Fix order: (1) project only the slots the law reads" (needs a `Pred` read-set frame lemma;
`witnessed` and `hashEq` read named slots too); (2) `support.card` and `elementCount` from
StoreCodec's cached sorted support, not a dedup; (3) the observation path's second
projection; (4) chunked document cells (O(change) encode, a design item and a format
change). Blinded-cell re-salting is private cells' and did not show in this profile.

## Design question for ember: every member's provider re-admits every record

**What happens.** Each client runs its own consent provider (`minidregg-client-consent`,
a resident per client with a 10-minute idle timeout). Before it signs anything it
`refresh`es (Host/ClientConsentCore.lean): it natively admits every record the Store
appended since it last looked (re-execution, full-record comparison, tail law,
post-image validation). With M members and R records written per period:

| | cost |
|---|---|
| one record, one provider (head ~1,000, hbox, after batches 1-3) | ~30 ms CPU |
| one member's next command after R foreign records | R × 30 ms of latency (60 records: 1.8 s; 500: 15 s) |
| the fleet | M × R × 30 ms of CPU: every record is re-executed once per member |
| a resident that idled out | the Store's checkpoint (at most 64 below the head) + the suffix (CONSENT-STORE) |

The latency is not O(history), but it is O(activity since this member last looked), and
a quiet member coming back to a busy room pays all of it. This is the explorer's 23.4 s
read and the sponsor's 12-32 s certify. On the demo every member's provider runs on the
same box (the workhorse), so the M × R term is all one machine's CPU.

**Options.**
- **A. Re-base on a lag (recommended).** A resident whose unseen suffix crosses the
  Store's newest checkpoint rebases there, as a fresh start already does, and admits only
  the records above it. Worst case: one checkpoint interval (64) × 30 ms ≈ 1.9 s; average
  about half that. This is the 10-31 ruling ("providers resume from a sealed snapshot")
  applied to a resident as well as a start, so no new trust premise. The interval can be
  lowered (sealing costs ~90 ms at 769 cells) to trade Store writes for latency. The
  records between the old and new base are decoded, not executed. It needs one
  ClientConsentCore change: `refresh` compares the Store's base with the held height.
- **B. One provider per box.** Members whose providers share a box (all of them on the
  demo) share one admitted state. Their custody differs only in signing keys, so the
  provider keeps one session and signs per member. That divides the fleet term by M. It
  needs a multi-member frame protocol and a key-per-member custody layout in mini-sdk.
- **C. No admission.** The provider signs over the Host's opened state (checkpoint + suffix)
  without re-executing anything. Per-command cost O(1), but the client no longer checks
  that each record is a lawful transition of the one before. That retires the provider's
  independent check, a larger change of meaning than A.
- **D. Status quo.** Correct, but law 17 red for quiet members.

**Recommendation:** A now (it is within the existing ruling; I will land it unless you
object), then B when the fleet has more than a handful of members on one box.

## Rows 4, 9, 13 (walks from the checkpoint): the statement (root: go, 10-31)

The walk (`NativeHostReplay.verifyLoaded`) re-admits every record from genesis because
the walk families' certificate lists (`PriorBegin*`, `PriorClaim*`, `PriorCreatedV3`,
`PriorRunningV3`, `RetryHistory`, `PriorIssue`, `PriorDispatchReserve`,
`PriorLifetimeGrant`, `PriorSelectedRelease`, the Fn frontier audit) are minted only by
native admission. Under the threat model ("we trust the storage device"), the honest
statement is: **a certificate's record was admitted by this walk, or it is a record of
the trusted Store below the walk's start.** It is restated once, at the seam, so that the
consumers follow one definition:

```lean
/-- A walk certificate's provenance. `admitted`: this walk natively admitted the
record at its prefix. `stored`: the record lies below the walk's start (the trusted
Store's sealed checkpoint) and its event carries exactly this certificate's ingress;
it was decoded and classified, never executed. Consumers bind either one to the
current image by their own presence check (`…_record_at`). -/
inductive Provenance (admitted carried : Prop) : Prop
  | admitted (h : admitted)
  | stored (h : carried)
```

Each certificate's `admitted : ∃ original accepted, record = ofIntent …` becomes
`admitted : Provenance (∃ original accepted, …) (codec.decode (historicalSourceEvent
record.event).canonicalBytes = some ingress)`. The one theorem that destructures it,
`PriorLifetimeGrant.finalRoot_in_record`, keeps its statement: the stored grant's carried
fact includes the write whose `exactPost` is `finalRoot`.

`Verified` gains its start:

```lean
  start : Nat
  startTrusted : start = 0 ∨ start = target.baseHeight     -- genesis, or the Store's sealed base
  originExact : origin.durable.image.accepted = target.image.accepted.take start
  admitted : AdmittedReplay config origin (target.image.accepted.drop start) opened
    (receiptHistory.toList.drop start)
  storedReceipts : ∀ i < start, receipts[i]? = the tag-carried receipt at height i + 1
```

and `Verified.accepted_history` is restated over `drop start`
(`FnSelectedHistoricalStep` selects only at or above the start; a selection below it
walks from the nearest checkpoint at or below the index).

- **Satisfiable:** every genesis walk (`start = 0`, no stored certificate); every walk
  from a Store checkpoint whose prefix classifies.
- **Teeth:** a `Verified` cannot start anywhere but genesis or the Store's own sealed base
  (`startTrusted`); every record at or above the start is natively admitted; a stored
  certificate cannot name an ingress its record does not carry.

**Families, by what classifying them needs:**
- *decode-only* (stored provenance): lifecycle begin v1/v2/v3, claim v2/v3, completion
  v2/v4 (created/running), failed-start recovery, retry begin/claim v4, and the Fn frontier
  (`frontierAfter` already reads only the record and receipt).
- *state-dependent*: `PriorIssue` (the descriptor reads the authority snapshot at that
  height), `PriorDispatchReserve` (the purse cell's state before the record),
  `PriorSelectedRelease` (the post state), `PriorLifetimeGrant` (its ticket and final
  root). Slice 1: if the prefix holds a record of these families, the walk starts at
  genesis, as today. Slice 2: these certificates resolve lazily, by one native admission at
  the trusted `Reader.stateAt index`, when a consumer selects them. That costs O(checkpoint
  interval) per use, never per walk.

Rows 9 and 13 then take the same start: `inspect-stop-claim`, `selected-release-fn-ack` and
`fn-empty-page-ack`, and consent's genesis fallbacks (`verifyInitial`/`refresh` suffix
failure, `upgrade`).

## Diagnosis that started this (2026-10-30, be4ef7510, x1 world on hbox)


Measured on hbox against the explorer's x1 world (be4ef7510, heads 769 to 1,000).

- **The Host restart is not the cost.** It seals a checkpoint every 64 heights and at a
  clean stop and opens checkpoint + suffix: restart + first signed read 2.4 s at head
  769, the read 0.13 s.
- **The client's local consent provider is.** `minidregg-client-consent` (a resident per
  client, 10-minute idle) re-admits natively every record written since it last looked:
  ~47 ms per record at head ~800 on be4ef7510. 20 foreign writes then a sponsor read
  0.95 s; 60 then a read 2.8 s; the next read 0.17 s. The explorer's 23.4 s was ~500
  records of catch-up after member-1's 512 says.
- **Certify is 0.21 s.** Certify after 60 foreign writes 2.9 s; read first (2.9 s of
  catch-up) then certify 0.22 s. "12-32 s per 256 tail" is 256 × 47 ms of the sponsor
  consent's catch-up plus, when the resident had idled out, its cold start.
- **A fresh provider is O(height)** (law 17): head 849, retained anchor: 6.5 s (the
  `Loaded.prefixOwn` genesis fold to the anchor, CONSENT-OWN); no anchor: 38.7 s (the
  genesis re-admission walk). The Host's own genesis audit at 769: 38 s.
- **`story new --from tale`** = 22 submissions (19 template lines, then table + map),
  each ~0.9 s unloaded (~1.7 s with the box busy); the first line also pays the
  member's consent catch-up (12 s in a traced run after ~250 foreign writes). Per line,
  Host ops are ~1 s of ~1.7 s; the rest is client-side (consent frames, codec resident).
  Trace: `/ci/hpc/r6.trace` (MINI_TRACE through `mini-shell-ssh` as the sponsor).

Per admitted record, the genesis audit's own timing (`MINI_AUDIT_TIMING=1`, x1s, head 769):
admission (event-v3) ~17 ms flat, advance ~6-9 ms flat, post-validation **grew 5 → 17.5 ms
with height** on be4ef7510.


## Landed / on the lane

Batch 54bd71d53 (CONSENT-STORE, JDV clean end, sweep rows 1 2 5 6 7 10 12 18) is on staging.
The next batch, on staging f7eb65272:

| sha | what | checked |
|---|---|---|
| aa6370007, e72f385b5 | rows 4/9/13: `Provenance` for the lifecycle certificates; `Verified.start` (genesis or the Store's base; `start_trusted`); `verifyFrom`/`verifyStart`; current-Store walks switched (Host session, STOP claim, selected-release/empty-page ACKs, consent fallbacks and upgrade, grant/dispatch lookups, current member key); audits stay genesis | lane-check of 15 files, 134 importers rebuilt, RC 0 |
| 62beac442 | consent option A: a resident lagging a checkpoint interval rebases at the Store's checkpoint | same lane-check |
| docs | rows 4/9/13 statement, the many-members question, the flatness submit profile | |

Measurements owed (next candidate, which carries 54bd71d53 and this batch): a fresh
member's first read (explorer H1: 20.7 s on be4ef7510), a fresh provider at two heights,
restart, `story new`, the first walk-family request after a restart.

## Next (successor: start here)

State (2026-10-31): lane `lane/hot-path-cold` at 545f80874, which is the slot fix, unmeasured and not yet
sent. The integrator is aeb671706eb3f70d7 and routes hot-path to this agent; private cells is
a30875aaf31364697. On hbox, build only in pool trees (`. /home/hbox/pool/pool.env;
LANE_POOL_NO_WARM=1 lane-tree acquire hot-path origin/lane/hot-path-cold`, release when done). Logs go
to `/ci/hpc`. Profiles: `/ci/hpc/fby` (run.sh, `--symfs`). The native Host build driver is
`/ci/hpc/nb/build.sh` (deploy/candidate/lane-build.sh host, LANE_DIR=/ci/hpc/nb).

1. **Flatness submit: the demanded projection. Written (545f80874); measurement owed.**
   - **Shared seam.** `PolicyStepContext.restrict` and `PhysicalLawResolution.predicateOf?` /
     `targetPredicate?`, with `predicateOf?_law`, which reads the law's predicate off the same graph
     load as the resolution.
   - **Declared resources (DRC).** `legKeys` and `step`, which is the full step restricted to the law's
     reads (`step_prepared_exact`). `legKeys_exact` plus `step_eval_exact` (via `Pred.eval_restrict`) is
     the tie the audit asked for.
   - **Read path.** `fullStep`, `keys` and `step_eval_exact`; the clock theorems are stated of `fullStep`.
   - **What runs, via `@[csimp]`.** `projectWithCommonDemand` and `projectWithDemand`. A byte block is
     encoded only if a demanded name contains its stem (`demandsStem`); content summaries are thunks
     (`ContentResource.projectLazy`, `targetProjectionDemand`, `resourceSlotsDemand`). Content support
     uses the cached key sort (`supportFast`, with csimps for `elementCount`, `contentPayloadBytes` and
     `changedIn`).
   - **Not done.** `StoreCodec.encode` of the whole cell per append (10.5%) still runs where a law reads
     `content/bytes/*` or the per-byte block, and in the write itself; that needs chunked document cells
     (a design item and a format change).
   - **Before (gate13).** 35737eac4: submit CPU 100 → 847 ms. eca98bde7: 116 → 874 ms, propose CPU
     28 → 231 ms, over heights 3 → 103.
   - **How to measure.** `scripts/perf/flatness-bench.py --bin <candidate bin with the new
     minidregg-host>`, built with `/home/hbox/lanes/integ/hotpatch-candidate.sh eca98bde… <name>
     minidregg-host=/ci/hpc/nb/artifacts/minidregg-host`.
2. **Row 4 slice 2 and row 11, one format change** (one epoch bump with private cells,
   now a30875aaf31364697: they send their FORMAT sha (AuxCache in Materialized, masked-trie
   roots, new PersistedCodecTags), we rebase row 11 onto it, and the integrator lands the pair with one
   genesis. Row 11 persists no cell root or Materialized field (answered 10-31); together with their private-cell root; agreed, and theirs is not
   imminent): the checkpoint carries the session indexes and the certificates that read the
   state at their height (issues, reserves, releases, grants). A Store with dispatch history
   then also starts at its checkpoint, and the open stops reading the whole log.
3. Rows 3, 8, 16, 17, 19, 20. Measurements on the batch-2 candidate: a fresh member's first
   read, a fresh provider at two heights, restart, `story new`, and the first walk-family
   request after a restart. flatness-get waits on app-reds' resident `/var` fix.

## Remaining accumulated-size costs (source inventory)

Here `H` = history length, `E` = entries in a changed cell, `B` = its encoded bytes,
`C` = cell count, `K` = retained certificates, and `Δ` = changed entries. These
are outstanding work, not benchmark verdicts or a proof that no other path grows.

| Term and source | Present cost | Required change |
|---|---|---|
| `DataWrite.canonicalPostBytes`, record encoding/hash/fsync/replay | O(B) each append, O(n²) bytes for n fixed document appends | Canonical patch + resulting root; same executor and exact-readback semantics |
| `Materialized` replacement encode, StoreCodec decode/root, DeployedBridge pin, storage charge | At least Ω(E+B); canonical sorting adds work | Persistent keyed entries, changed-path encoding/commitment, maintained charge; caches alone do not change the bound |
| K-HIDE-ROTATE and current root | O(E) even when Δ=1 | Exact constraint below; do not substitute root-only privacy |
| ContentLaw/EventHistoryLaw | At least Ω(E), now one pass | Incremental checker equal to the full law under the held pre-law witness |
| `ResourceObservationAdmission.projectWith`, resourceSlots, bytesSlots, balances | Whole resource/byte projection | Demand-driven lookup proved equal to list `State.get`, per predicate atom |
| `Pred.indexState` | O(projected slots) per law check | Share persistent state index; do not rebuild from the projection per request |
| Full signed views + document append preparation in workspace.rs | O(E+B) transfers/scans, multiple observations | Authorized bounded append-context query from Lean; full exports explicitly output-sensitive |
| `Verified` certificate lists: `find?`, `present`, retry and Fn/frontier histories | O(K), sometimes plus list indexing into H | Keyed indexes with exact first-match semantics, including duplicate/ambiguity refusal |
| Receipt append/selection | **Fixed here:** O(log H) push/get | Keep operational users on receiptAt; full list export is still O(H) |
| `Image.accepted` reverses acceptedRev; list take/drop/map/index in refresh/history consumers | O(H) when materialized | Persistent history index/cursor with list specification, authenticate a suffix against a held head |
| `Loaded.rootLog` / chainLog flat Array pushes | Potential O(H) COW when old openings share arrays | Persistent tree sequence; prove/select original-prefix roots, not current recomputations |
| `SessionIndex.TxIndex`, KeyIndex and cell-id HashMaps/HashSets | Shared flat hash-array updates can copy accumulated state; hash collisions also lack a strict logarithmic bound | Persistent ordered indexes with the same first-index/membership specifications |
| Direct transaction `findIdx?` in dispatch/lifecycle receiving and lookups | O(H) even though Loaded.firstIndex already exists | Use the exact cached lookup; also fix its persistent representation as above |
| `extendVerified` prefix/seed comparisons, Fn selected-poll historical zip | O(H) / seed size | Retained authenticated prefix identity and keyed selected evidence |
| `storeCheckpoint` -> State.ofSnapshot -> image.cellIds/map, full body codec/MAC | O(C + total cell bytes) every 64 records | Immutable addressed pages and O(Δ log n) manifest updates, not periodic full traversal |
| Full opening `loadChained` -> openLoaded | At least all journal bytes + state, even with checkpoint | Checkpoint+suffix open with persistent index roots, no prefix read/decode/rebuild |
| Cold walk and consent prefixOwn / verifyLoaded | O(H) admissions plus state work | Bound sealed certificate context to the same checkpoint; resume both clients |
| Directory/authority row enumeration and whole-cell account/member/index payloads | O(C), members or ledger entries on affected paths | Persistent typed indexes, touched-key validation and projection; distinguish fixed queries from full enumeration |

### What the kept privacy ratchet actually forces

The deployed commitment is **not a Merkle tree**. `StoreCodec.rootPreimage_length`
proves that its preimage has exactly `44 + 32 * (entries W store).length` bytes.
`rootBytesFast` removes allocations but still feeds those bytes to the flat hash.
A cached root of an unchanged cell helps reads; every new cell version still pays
this amount. A Merkle tree over the present leaves alone does not solve blinding.

`StoreHiding.view` sends one Item per entry: opened salt+entry or hidden 32-byte
leaf. `change_detection_only_via_root` says no hidden leaf survives an in-place
hidden write, except by a KMAC cross-key coincidence or cSHAKE leaf collision.
Fresh blinding changes every salt preimage, including unchanged entries. Thus,
for **this KMAC/cSHAKE leaf scheme and flat authenticated-view format**, producing
the new root/view performs Ω(E) leaf/preimage work and a full view has Ω(E) output.
Lazily computing leaves can defer work, but the flat root immediately demands all
of them. Per-entry epochs or a fresh wrapper around a stable Merkle root expose
stable hidden sibling commitments across views and do not preserve that theorem.

This is not a universal lower bound for every hiding commitment. A rerandomizable
commitment with updateable authenticated selective openings would require a new
construction and corresponding binding/hiding/cross-view statements. No such
construction is implemented or proved here. Keep the current ratchet and expose
its remaining linear cost; no further privacy choice is being deferred to Ember.

## Flatness gate and measurements

`scripts/perf/flatness-gate.sh CANDIDATE NEW_ROOT [N=1000] [LO=10]` runs submit/propose
and GET, then writes `flatness-submit` and `flatness-get` rows. Both run even when
submit fails. It records the candidate SHA256SUMS hash. A fresh root is mandatory;
missing results, missing metrics, failed operations and interrupted runs fail.

Each sample records actual accepted history size. Compare mean costs at operations
6–10 with the final 10 by default, bounding the ratio by
`max(1.5, mean(log2 late_history) / mean(log2 early_history))`. CPU is the explicitly
selected service process tree, including waited-for child CPU; wall is end-to-end.
Do not interpret a passing finite comparison as an asymptotic proof. Submit can
fail at a completed 100/200/400/800-operation prefix; it cannot pass before N.
GET runs the full N. Certification is normal admitted work every 96 appends or
32 GETs, outside measured requests, to preserve the deployed 256-record tail law.
Certification cost is therefore not certified flat by these two metrics.
The fixture explicitly allocates 10¹² units in each physical meter lane at
GENESIS, through NEWPARTICIPANT_METER_ALLOWANCE / WORKROOM_METER_ALLOWANCE.
Defaults for other workloads are unchanged; the participant template digest
includes the selected allocation. Account funds and physical meter allowance
are separate. This does not remove a bound, top up a running world or relax admission.

On hbox, use a private NVMe root under `/ci/<lane>` for the route world: the standard
resident custody inventory cannot execute its copied runtime under `/home`.
All services use their own PID files and world-down/stop-residents cleanup.

The integrator's new `/home/hbox/lanes/integ/gate10.sh` extends gate9: after tour,
composed and enrol finish, it runs this candidate's flatness harness serially and
feeds its TSV to `gate-from-runs.py --tour`. Missing harness or failed fresh-root
creation yields FAIL, never an old green result. gate9 is unchanged. The reviewed
copy is `target/hp-scratch/gate10.sh`; the integrator must select gate10 for the next
cut. A production candidate has not run this combined gate yet. The real
`gate-from-runs.py` was exercised with synthetic verdict inputs: all-pass PASS;
failed-flatness and incomplete-flatness FAIL despite otherwise passing inputs
(`/home/hbox/lanes/hp-codex/scratch/gate-aggregation`).

Runs on the existing batch-1 candidate `cand-b2c` (not the new receipt binary):

| Run | Samples | CPU early → late | Wall early → late | Verdict |
|---|---:|---|---|---|
| `scratch/fs2`, submit | 100 | 104 → 863 ms (8.30×) | 241 → 1577 ms (6.53×) | FAIL, bound 2.00× |
| same, propose | 100 | 26 → 242 ms (9.31×) | 582 → 4113 ms (7.07×) | FAIL, bound 2.00× |
| `/ci/hp-codex/fg5`, GET | 40 | 144 → 158 ms (1.10×) | 260 → 349 ms (1.34×) | PASS smoke, bound 1.50× |

`fs2` certified successfully at operation 96 (installed at acceptedCount 98).
`fg5` reached head 68 and world-down recorded removal_assertions=0.
`fg6` stopped at GET 894 with HTTP 403, head 947; it has no passing flatness result.
The fixture exhausted its 10⁷-unit storage allocation: Lean decoded the final
checkpoint and previous record (`meter-diagnosis2.log`): available.storageBytes
= 10,674, previous GET exactCharge.storageBytes = 10,895, fundedCheck = false.
The receiver hid the precise durable reason behind “durable dispatch refused”;
this is the metering diagnosis, not an observed detailed refusal code. The
new explicit genesis allocation above fixes the instrument's capacity. Some
fg6 timing overlaps builds; none of its partial samples are a passing result.

`/ci/hp-codex/receipt-smoke2` ran the combined gate on the development assembly
`hp-codex/dev-receipts` (the two native binaries above plus cand-b2c Rust roles).
All 40 appends installed. Submit CPU 150→361 ms, wall 341→568 ms; propose CPU
34→89 ms, wall 620→981 ms: all FAIL (bound 1.580). GET CPU 154→219 ms and wall
734→964 ms: PASS (bound 1.5). Overall gate FAIL, as required; GET ran after the
submit failure. Both worlds stopped; route removal_assertions=0. The first
smoke assembly lacked candidate params.sh and failed setup; smoke2 supplied
that fixture helper. Neither is a packaged candidate or a tour result.

`fs3` requested 1,000 appends with the new genesis allocation and stopped on a
completed failing prefix at 100: result.json records n=100, requested_n=1000,
stopped_early=true, FAIL. Submit CPU 106→1016 ms (9.585×), wall 299→1388 ms
(4.647×), propose CPU 30→282 ms (9.400×), all above the 2.000× bound.
Propose wall 1110→1766 ms (1.591×) passed in this run. It overlapped fg7 in
its middle, so keep the per-run verdicts instead of combining wall observations.
Both fixture genesis files were checked to contain the requested 10¹² allowance.

`/ci/hp-codex/fg7` completed all 1,000 GETs, head 1,058, with the larger meter
allocation and these receipt binaries: CPU 174→268 ms (1.540×), wall
491→607 ms (1.238×), bound 1.958×: PASS for both metrics. It certified through
operation 992 and then measured the final window. World-down recorded
removal_assertions=0; its runner stopped. The mid-run submit workload finished
before its final window. The complete result, earlier small results and the
smoke gate TSV are copied to local `target/hp-evidence/`.

All processes started for the completed fixtures have been stopped through
their own PID files/normal teardown. The lane's Lean REPL was stopped as well.
No other lane's processes, files or caches were removed.

