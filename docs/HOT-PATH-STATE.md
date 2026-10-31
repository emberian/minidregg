# HOT-PATH state — 2026-10-30, hot-path successor (Opus, agent a86738fc)

Law 17: a fixed-size operation may cost at most O(log n) in accumulated history
and state, or O(changed · log n) for a multi-entry change. Full exports must be
charged for their output. K-HIDE-ROTATE stays. Ember approved trusting sealed
snapshots on our own filesystem (the Host already opens from its MAC'd checkpoint).

Branch `lane/hot-path-cold` (Mac worktree `/Users/ember/dev/minidregg-lanes/hot-path-cold`;
hbox warm tree `/home/hbox/lanes/hpc/src`, packages hard-linked from the integrator's,
native outputs `/home/hbox/lanes/hpc/{native-out,consent-out,artifacts}`; hbox scratch
`/ci/hpc`, where `x1s/` is a copy of the explorer's x1 Store at head 769).

## The restart / certify / story reds: what they are

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

## Landed on lane/hot-path-cold

| sha | what | measured |
|---|---|---|
| dbe692893 | `bytesBEq`: whole-cell byte comparisons (cellsLawfulFrom, decodeRowFrom, loadDeploymentFromAt, the served twins) by object identity first. `==` on `List UInt8` is `List.beq`, which `listDecEq`'s csimp never reached, so every advance walked every cell's bytes. `bytesBEq_eq` keeps every `_eq` statement. | genesis audit at 769: 38.3 → 32.6 s; post-validation flat 4.4-4.9 ms per record at every height (was 5 → 17.5) |

| d78ee272b | a consent provider's own bases (`retainOwn` -> `ownOfGenesis`, after every admission) read cells off the cached enumeration (`ConsentAnchor.headState`, `headState_eq` is `rfl`) instead of `State.ofSnapshot`, whose `Image.cellIds` flattens and dedups every write of the log: 68% of the provider's CPU per write (dwarf call graphs of the sponsor's resident). | sponsor shell write (doc append + submit) through a copied workspace, x1 near head 1,000: 2.6 s → 1.65 s each, flat over 6 writes |

Checked: lane-check of every changed file and its direct importers on hbox; native Host and
consent built at d78ee272b (`lane-build.sh host`, `consent`, EXIT 0).

After both, a shell write's CPU splits about evenly between the codec resident (JSON hex
rendering, ByteArray/List marshalling; flat profile) and the consent provider (cell-table
lookups with big-Nat keys; flat); the serving Host is ~3%. A retained anchor is bound to the
exact consent executable and settings, so **every candidate upgrade makes every client's next
provider walk from genesis** (48 s at head ~1,000 with the new binary vs 9.2 s resuming): one
more reason for option 1 below to carry across binaries of the same Store epoch.

## Open, in order

1. **Consent cold start** (ruling requested from root, 10-30): option 1 = the provider seals
   its own state under a client key in its anchor directory and resumes from it (keeps
   CONSENT-OWN; draft statement in the session scratchpad `hpc-consent-sealed-statement.md`;
   statement to the auditor first; Rust frames in mini-sdk consent.rs); option 2 = resume
   from the Store's MAC'd checkpoint (retires CONSENT-OWN: a weakening, needs explicit approval).
1b. **Anchors across a ship** (for the root, with item 1). `mini_sdk::local::binding` hashes the
   provider's path, inode, size and mtimes with the settings bytes, so even a byte-identical
   re-install voids every client's anchor, and every ship makes each client's next provider
   walk from genesis. Choices: (a) bind to the bytes' sha256 plus settings: as sound as today,
   but it hashes a ~170 MB provider on every command and saves only same-path re-installs
   (each candidate installs under its own path): not worth it; (b) bind to the Store epoch, the factory template and the
   settings (not to `receiverSemanticsFrom`, which hashes the compiled manifest and moves every
   ship): an anchor admitted by any provider of the same epoch and template is then trusted.
   That is a new trust premise (an older provider's admission stands until the next epoch), and
   it needs an explicit rule. `mini consent-full-ready` remains the full re-verification.
2. **Per-record admission** (~17 ms event-v3, ~140 ms each event-v2): profile with call graphs
   (frame pointers are absent; dwarf perf of the whole audit captured only start-up).
3. **Consent catch-up is O(records since the client last looked)** for every client: N
   members' residents each re-admit every record. Design question for ember/council.
4. **story new**: fewer submissions (the index edits, binds and links are 8 of 22) and the
   per-line client overhead.
5. The whole-cell write path (inventory below); blinded-cell re-salting is private cells'.

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

