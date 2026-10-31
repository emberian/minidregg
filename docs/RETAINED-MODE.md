# Retained mode

A present-state document, rewritten whole. Lane `lane/retained` (worktree
`/Users/ember/dev/minidregg-lanes/retained`). Ember, 2026-10-31: "it seems fundamentally this current
generation of code generation models keeps writing re-execution. If you imagine the global computation graph
required to keep a mini system going, the whole thing would be incremental and efficient and held
'retained-mode'." The bar: about 1 ms of warm Host work per user action on NVMe; law 17 (ATLAS §6): no
operation does work that grows with history, document size, cell count or member count.

## 1. The diagnosis

Almost every pathology the perf lanes found this week is immediate-mode code in a system that should be
retained-mode: a value derived from the state is recomputed from the whole state at the moment it is needed,
instead of being kept beside the state and advanced by each change. Models write it by default because
`x = f(state)` is trivially correct, while the retained version owes "the kept `x` is still `f(state)`"
after every write, which nobody pays by hand at hundreds of call sites. The result is cost proportional to
what exists rather than to what changed.

The deepest instance is the leaf. `Theory.Store`'s `Store L` is a `DFinsupp`: `Store.set` wraps the old
lookup function in one more closure and conses the address onto the support multiset. Lookups walk every
write since the store was last rebuilt; `support` dedups the whole multiset. `Finset` and `List` are used
the same way as runtime sets and indexes (`AuthState.revoked`, `Parentage.support`, `image.accepted`).
These are specification types used as runtime data, so every node built on them inherits O(n). The
measurement (hot-path's 8-story run, `hbox:/ci/hpc/sn/g2.s{2,8}.all.txt`, Host CPU per story 1.50 → 2.51 s):

| inclusive share of Host CPU | story 2 | story 8 |
|---|---|---|
| `DFinsupp.update` under `Store.set` (two closures) | 3.9 % | 24 % + 9 % |
| `StoreCodec.encode` (whole cell per write) | 3.3 % | 13 % |
| `NativeHostSession.refresh` (per-request served-state advance) | 23 % | 10 % |
| `supportCached` / `sortedSupport` | ~4 % | ~4 % each |
| `authStateOfFast` (authority projection) | 1.7 % | 2.9 % |

`Compiler/WorldCompact.lean` exists only to flatten the closure chains every 32 heights (its own header: a
483-record open spent 99 % of 175 s inside `Function.update`).

## 2. The abstraction (`Theory/Retained.lean`, statement-first, astra-reviewed)

* **`DeltaSystem`**: states, deltas, a partial `step` (refusal), a genesis. **`View`**: queries `Q`, answers
  `A q`, and `spec : State → (q : Q) → A q`, the recomputation, which is a specification and never runs on a
  request path.
* **`Maintained D V`** (closed): a representation `Rep`, a relation `Holds r s` (a relation, not equality
  with a bulk build: a kept trie need not be the one a rebuild makes; ACL2's abstract stobjs and
  `Theory.CellStateAux` are the precedent), `fetch` (answer plus the representation to keep, so a read can
  fill a memo), `advance` per delta, `init` at genesis.
* **`Node D In Out`** (open over an input view): a read declares the input queries it needs given its
  representation (`readProbes`, none on a memo hit) and sees only their answers; an update declares probes
  from the delta alone (pre- or post-delta) and sees only theirs. `ReadFootprintBounded` /
  `ProbeFootprintBounded` bound the declared input footprint `c + k · size`, not cost: a shadow-state node
  (`Rep := Store`, recomputing per read) has a zero footprint. Cost is gated by the flatness bench (law 17);
  a per-node cost statement over an instrumented interpreter (as `PrivateCellTrie.EraseCost`) is owed.
* **The keystone**: `Maintained.maintained_eq_recompute`: after any admitted run, from any representation
  holding at its start, the maintained answer is the recomputation's answer at the final state.
  `checkpoint_restore_from`: restore any held representation from its checkpoint and advance over the
  suffix, and the answers are the recomputation's at the head (trusted storage, ember 2026-10-31).
* **The chain rule**: `Node.stack N M` makes a node over a maintained input maintained; the input's answers
  are fetched once, materialized, and its memo fills kept. Nested `View.sum` layers express any finite DAG in
  topological order; `Node.weakenLeft` reads a wider input.
* **`RedGreen.node`**: the generic memo node for any `Derivation` (a query computed from exactly its
  declared dependencies, plus a delta's syntactic touched set with its frame law). A write stamps what it
  touched (O(touched)); a green read reads nothing; a miss reads its dependencies and remembers. Salsa's
  red-green without early cutoff; Adapton's demanded computation.
* **Witnesses** (law 2): a two-layer graph over the example store (a total maintained from the guarded ops'
  own before/after values, no probes; a threshold flag reading one post answer), a red-green memo of the
  same total. `flag_reachable`, `memo_hit_reads_nothing` (satisfiable, operational: a miss reads both
  dependencies, the remembered read reads none, a write turns it red); `stale_refuted`, `constant_refuted`,
  `ignoring_update_refuted`, `empty_deps_refuted` (teeth); `holds_inhabited`.
* **Deferred until an instance needs them** (astra round 1): typed output deltas per layer (DBSP's chain
  rule, the ILC derivative contract), early cutoff and durability (Salsa).

Prior art read: Acar's self-adjusting computation (from-scratch consistency is our keystone's shape), Salsa
(red-green, durability, early cutoff), Adapton (demanded computation, `fetch`), Gupta-Mumick IVM and DBSP
(Budiu et al., Lean-formalized: `Q^Δ = D ∘ Q ∘ I`, linear operators are their own increment), Cai et al.'s
ILC (change structures, static differentiation), McSherry's differential dataflow (arrangements: one
maintained index shared by many readers), ACL2 abstract stobjs (correspondence plus preservation). Papers in
`~/paperbin` (`acar2005-*`, `hammer2014-adapton`, `budiu2023-dbsp-*`, `gupta1993-*`, `mcsherry2013-*`,
`swords2018-acl2-*`).

## 3. The Host as one graph: node inventory

The Store holds leaves; everything derived is a node, persisted in the checkpoint and advanced by deltas.
"Today" names how the value is obtained now; "kind" is the node shape that replaces it. Owners are the lanes
holding the code today (hot-path a6c4a1532687a4fdb, private cells a8da2b953507b402b, perf-client
a778bbda6509944a5, exorcist a76808829fc8e4836, perf-apps a25df305cfd551d8b, retained-mode this lane).

### 3.1 Leaves

| # | value | today | kind | owner |
|---|---|---|---|---|
| L0 | a cell's logical store (`Store L`) | `DFinsupp`: a closure per `set`, a multiset support; `WorldCompact` re-trees every 32 heights | the leaf representation: a persistent extensional tree map, O(log n) get/insert/erase, statements unchanged (§5) | **retained-mode, first migration** |
| L1 | a cell's root | flat hash over all entries (`rootPreimage_length`); KeptCell trie root for eventHistory/authority (FORMAT a) | `AuxCache` carried beside the store (already the shape of a `Maintained` with `root?` as its one query) | private cells |
| L2 | a cell's canonical bytes | `StoreCodec.encode` of the whole cell per write (13 % at story 8) | per-entry persistence: entries are the stored unit, the cell blob is an export | hot-path (FORMAT batch) |
| L3 | the record log | `image.accepted : List`, `acceptedRev` reversed per use | persistent sequence with O(log H) index and suffix cursor | hot-path (row 11) |

### 3.2 Indexes over the log (the session indexes; row 11)

| # | value | today | kind | owner |
|---|---|---|---|---|
| I1 | presence, links, ids, tx, spentAt, writesAt (`Loaded.indexExact` … `writesAtExact`, `Compiler/DurableReceiverCore.lean:1102`) | six hand-maintained fields with hand `*Exact` lemmas; rebuilt from every record at each process open (`loadChained`) | six instances of one linear-fold node over the log (`Holds := *Exact`), carried in the checkpoint body (`Persist`) and advanced over the suffix | hot-path (row 11), restated here |
| I2 | receipt roots, `receiptAt`, `firstIndex` | O(log H) push/get (fixed), `TxIndex` | maintained indexes (done; restate as instances) | hot-path |
| I3 | walk certificates (`Prior*`, `RetryHistory`, Fn frontier) | minted by genesis re-admission; `Provenance.stored` from the checkpoint | keyed index node over the log, persisted in the checkpoint | hot-path (rows 4/9/13) |
| I4 | Fn scans (`FnSelectedPollReleaseLink`, `FnOriginOutbox`, `FnConsumerProgress`, …), `retainedDispatchReceipt` `accepted.any`, RetainedSegmentInspection `findIdx?` | O(H) scans per poll/ACK/dispatch (sweep rows 8, 20) | keyed index nodes at admission | **unowned → retained-mode** (coordinator, 10-31) |
| I5 | carry prefix verification (`CarriedSegment.buildTarget → loadImage`), FnEvidence `verifyBytes`, `JointSourcePrefixValidation` (O(H) per proposal, O(H²) total), `GenericSimplexParticipant.reloadSource` | whole-prefix reload per use (rows 16-19) | resume from the source checkpoint: the source's own maintained tip plus its suffix | **unowned → retained-mode** |

### 3.3 Derived state per cell and per policy

| # | value | today | kind | owner |
|---|---|---|---|---|
| D1 | authority projection (`AuthState`: revoked set, parentage, epochs) | `ServedAuthority.authState`, built once per served state, i.e. O(authority) per authority write; `revoked : Finset` membership is a list scan | a query view over the authority store (revoked = a lookup; parentage = lookups), no materialized Finset; on L0 every query is O(log n) | retained-mode after L0 (hot-path's pick for the authority growth) |
| D2 | served directory and authority cell (`validateServedFrom`, `loadServedDirectoryFrom`, `loadServedAuthorityFrom`, `cellsLawfulServedFrom`) | early cutoff by byte comparison of every row per refresh: O(total bytes) | delta-driven: the suffix records name the cells they wrote (`writesAt`), only those are decoded and re-checked | retained-mode with hot-path |
| D3 | policy projection (`ContentResource.project`, `projectWithDemand`, `slotTable`, `Pred.indexState`) | demanded projection (hot-path, csimp): only slots the law reads; slot table rebuilt per request | a `Derivation` per law read set (`law.predicate.reads`, `Pred.eval_restrict` is the frame law) → red-green memo keyed by (target, policy roots) | hot-path / retained-mode |
| D4 | law resolution (`PhysicalLawResolution.predicateOf?`, `resolve?`, `loadTarget`, `loadPolicy`, `fetchPolicySource`) | loaded twice per grant, policy records re-encoded per load | red-green memo keyed by (target, policy cell roots); deps = the policy cells | exorcist (in flight), then a node |
| D5 | content summaries (`ContentResource.elementCount`, `support.card`, `contentPayloadBytes`, `changedIn`) | csimps over the cached key sort, O(cell) | linear-fold nodes over the content store (count/sum are linear: their increment is the patch's before/after) | private cells / hot-path |
| D6 | the per-write post decode (`TurnOfIntent.deltaOf` decodes the bytes the Host just encoded) | encode then decode per write | the write carries its decoded post (a non-persisted field) | hot-path |
| D7 | `World.admit` pin roots (`DeployedBridge.cellRoot` per pinned cell per record) | re-encode per record; `snapPinFails` judges from the snapshot's bytes (perf-client 5415aecf7) | carried roots (L1) | perf-client, private cells |

### 3.4 Per-request derived values (Host session)

| # | value | today | kind | owner |
|---|---|---|---|---|
| R1 | op 4 → op 5 challenge (`NativeObservationController.challengeAt`/`headerAt`, 13 % + 3 % of op 5) | recomputed in op 5 to check the answer; `headerAt` twice per grant | session node keyed by (state root, request digest), deps = the opened head | exorcist → retained-mode (handed over 10-31) |
| R2 | `checkGrants` verdict | recomputed per signed read | red-green memo keyed by (authority root, policy roots, resource cell root, clock, grant bytes) | exorcist |
| R3 | consent: the planner's prepared write vs the deriver's re-execution of the admitted record (perf-client 10-31: 347-372 ms of a 1.66 s `doc new`) | prepared twice from the same pre-state | node keyed by (pre-state height and head tag, intent bytes); consumed by the deriver when the admitted record matches, with "derived suffix = deriver's result at that pre-state" | retained-mode (handed over by perf-client) |
| R4 | consent catch-up (`refresh` → `walkSuffix`), every member re-executes every record | O(records since last look) per member; option A rebases at the Store checkpoint | per box, one admitted state (option B); then R3 | perf-client / hot-path |
| R5 | `PackedCell.decode` builds with `materialize`, dropping the Store's bytes | re-encode for `resourceViewUsing` | `materializeCanonical` (proved equal): the bytes are carried | exorcist |
| R6 | session refresh: each new record's turn derived once per view (light, full) and again on receive, each decoding posts the Host just encoded (hot-path 10-31: 455 of 1,316 samples at 500 says) | derived 2-3 times per request | (i) the write carries its decoded post (a carried value with `decode bytes = some post`); (ii) one derived turn per record shared by both views (red-green memo keyed by record) | hot-path (a0fee5643746e520c) |
| R7 | the open's World: represents re-decided at open | O(H) at open | the checkpoint seals the World beside the snapshot; `WorldTrack.advance` is its update rule | hot-path + perf-client |

### 3.5 Client and app side (already retained by hand; restate, do not regress)

| value | today |
|---|---|
| Host image digest, workspace, settings, attempt index, namespace ID index (perf-client 60b0dbf20, aa24acaf8, c4ef61d37, c9f64c275) | kept by file identity: a memo keyed by (dev, inode, size, mtime) |
| SPK verification of an installed image (perf-apps batch 1: 2.7-4.3 s → 0.02 s) | kept by file identity |
| SQLite handle per root (exorcist b3b132f19), `RefIndex` in the web body | resident handle, kept index |
| client reference names over WORKSPACE/refs (`workspace::reference_names`, `reference_for_target`, `sealed_room`) | built lazily once per read (exorcist 478f170ab: 13-15 → 3 ms per `doc show` at 500 refs); still O(references) when a page names a target. Owed: a maintained index keyed per file by (ino, size, mtime_ns, ctime_ns) from one getdents plus statx (a directory stamp misses in-place overwrites), never trusting a stamp younger than two clock ticks at fill time; other writers (journeys, grain-runtime, tests) need no cooperation |
| resident clients, consent and codec residents (no idle exit) | resident processes are where retained state lives |

These are the right shape and are all red-green memos whose dependency is a file identity. They become
instances of one Rust helper with the same contract (deps = file identity tuples; a stat is the stamp), so
the next one is not hand-written.

### 3.6 Operator paths assigned here (coordinator, 10-31)

| value | today | kind |
|---|---|---|
| `export world`, `doc app-export`, backup, `mini-restore-check` | O(world): 1,034 ms first / 176 ms second at height 142 (b6); 6.9 s at h195 (early, other box) | output-sensitive exports charged for their output; backup = the checkpoint pages written since the last backup (incremental, by L0's persistent pages) |
| carry, FN consumer, consensus and source-agreement readers | zero measurements; carry authenticates a receipt-to-cut prefix (likely O(H)); the source-agreement reader reopens the configured Store per stateful operation | resident reader holding the source's maintained tip (I5) |
| snapshot save / restore, cold start | restart 11.7 s wall at h491 (b5), first read 0.24 s | the checkpoint carries every node's representation (`Persist`); open = checkpoint + suffix, no prefix decode |

## 4. Migration order

1. **L0, the leaf** (this lane, now; hot-path and private cells agreed 10-31): §5.
2. **D1 and D2** on L0: the authority projection as a lookup view; the served-state advance driven by the
   suffix's write sets instead of byte comparison of every row.
3. **I1 restated** as instances of one linear-fold node with `Persist` (row 11 then carries them in the
   checkpoint body: hot-path's FORMAT epoch).
4. **R1, R3** (handed over): the challenge node; the prepared-write node shared by planner and deriver.
5. **D3/D4** as red-green derivations from law read sets, after the exorcist's loader work lands.
6. **I4, I5** and the §3.6 operator paths.
Each migration deletes the recomputation it replaces in the same commit (law: the derived path is the only
path).

## 5. L0: the leaf representation

`Store L` becomes a structure over `Std.ExtDTreeMap (Address L) (fun a => L.Value a.1) cmp` (extensional:
`ext_get?`; persistent: path copying, so pre and post stores share structure; O(log n) `get?`, `insert`,
`erase`). Surface kept: `s a` (CoeFun, `get?`), `Store.set` (insert or erase), `set_eq`, `set_ne`, `zero_apply`,
`ext`, `support` (a `Finset` view for statements; runtime enumeration is `toList` in key order), `Op`,
`Patch`, `run`, `ValidFrom`, `run_frame` unchanged. A `toDFinsupp` spec view and its `toDFinsupp_apply`
keep the files that reason through DFinsupp lemmas provable. The address order: `Layout` gains an
instance-implicit field `[keyOrder : ∀ space, StoreKey (Key space)]` and `[namespaceOrder : StoreKey
Namespace]`, where `StoreKey α` is an injective code `α → List Nat` (List Nat has a lawful order in Std);
instance-implicit fields are filled by instance search exactly as the layout's `DecidableEq` fields are
today, so most layouts change not at all; key types without an instance get one (an injective code).
The tree keys carry the code once (`FiniteDependentMapCachedOrdering`'s `CachedKey` idea), so a lookup
encodes the probe once.

What it deletes: `Compiler/WorldCompact.lean` and `compactEvery`, the post-store `Store.set` chains,
`fromEntriesCached`'s re-keying, `supportCached`'s dedup (the tree's keys are already unique and sorted, so
`sortedSupport` is `keys`).

Repairs: about 66 files use DFinsupp on stores directly (largest: `Theory/CanonicalResourceKernel` 27,
`Kernel/Seat` 21, `Compiler/StoreCodecBook` 19, `Kernel/PrivateCellView` 18, `Kernel/NativeThinConsent` 13,
`Compiler/FiniteDependentMapCodec` 13); 18 `simp [Store.set …]` unfolds; private cells named
`Compiler/PrivateCellRoot.lean` (two unfolds), the narrowed view's `DFinsupp.filter`
(`ResourceObservationAdmission.narrowStore`, `Kernel/PrivateCellView`, `Kernel/PrivateCellReceiver`
1274-1330) and `Compiler/PrivateCellIndex`. `Store.filter` with `filter_apply` replaces `DFinsupp.filter`.
One whole-tree build through the integrator at the cut (a shared interface: per-file green hides umbrella
reds).

Measurement: hot-path's `hbox:/ci/hpc/sn/grow2.sh` (one world, 8 sequential `story new`, Host CPU per story
and perf of stories 2 and 8) before and after, and `scripts/perf/flatness-bench.py` submit late/early ratio.
The after is a flat story 2 → 8 slope with `Store.set` gone from the profile.

## 6. Generation: nodes come out of Effects/, never by hand

Ember's rule is that kernel effects come from the `Effects/` derivation engine. A node is the same kind of
artifact:

* **The delta system is derived.** `Effects/Revival/Engine.lean`'s `Substrate` already has `step`, `writes`
  (the syntactic footprint) and the frame law `Framed`. A `DeltaSystem` is `Substrate.run` over descriptors,
  and a delta's `touched` set is the descriptor's `footprint` with `touched_frame` from `Framed`, proved once
  for every declaration.
* **Query views are derived from read sets.** A view declared as a query over substrate locations with a
  syntactic read set (a `Pred`'s `reads`, `Pred.eval_restrict` as the frame law: hot-path's demanded
  projection already proves exactly this) is a `Derivation`, hence a `RedGreen.node`, with no update rule
  written.
* **Aggregates and indexes are linear folds.** A count, sum, membership index or first-index over entries is
  a linear map of the store's entries (DBSP: linear operators are their own increment). The declaration names
  the per-entry map and the monoid; the update `r ⊕ f(after) ⊖ f(before)` per op and its `update_holds` are
  one generic theorem (the `Example.totalNode` proof, generalized). Indexes into the log (I1) are folds over
  appended records, append-only, so `⊖` is not needed.
* **What an author writes**: the view (query or fold) and nothing else. The engine emits the node, its
  `Holds`, its `Persist` codec (from the representation's `StreamCodec`), and the instance of the keystone.
  A hand-written update rule is the same smell as a hand-written executor arm.

The `[EFFECT-registry]` residual in `Effects/EffectSpec.lean` gains a `views` field; the first two
generated nodes are D1 (query view) and I1 (linear fold).

## 7. Guard rails

* **The lint** (`Theory/RetainedLint.lean`, design): an attribute `@[whole_state]` on functions whose cost
  is the size of what exists (`DFinsupp.support`, `Finset` builders over stores, `sortedSupport`,
  `StoreCodec.encode` of a whole cell, `List.find?`/`findIdx?` over `accepted`, `verifyLoaded`,
  `loadChained`, `authStateOf`, `PresenceIndex.ofRecords`, …) and `@[request_path]` on the Host's operation
  entry points; a command walks the transitive constant closure from every request path (the same walk
  `#assert_axioms_tree` does) and fails naming each whole-state constant reached, unless the path is an
  audit (`@[audit_path]`: `audit`, `store-audit`, `pay-claim-audit`, genesis replay). It runs once per
  batch cut on the build box, beside the axiom census; it is red-proofed by a planted request path that
  calls `sortedSupport`.
* **The paragraph for every lane brief:**

  > A derived value is maintained, never recomputed. If your code computes `f(state)` (a projection, an
  > index, a set, a count, a decode of a whole cell, a scan of the log) on a request or write path, you owe
  > its update rule: make it a node in `Theory/Retained.lean`'s sense (a `Derivation` with declared reads, a
  > linear fold, or a `Node` with its local `update_holds`) and keep it beside the state, advanced by the
  > delta. `Finset`, `List` and `DFinsupp` are specification types; a runtime set or index is a persistent
  > map. The lint names any whole-state function reachable from a request path; "it's only O(n)" is the
  > defect law 17 names.

## 8. Continuation (start here)

**Landed (staging, batch 8):** `675a80745` `Theory/Retained.lean`; `1d4ff4efb` this document; `62aa5fcf8`
footprint renames, 35 pins, `Theory/SparseMap.lean`; `05bffae27` SparseMap transport lemmas
(`toDFinsupp_set/support/zero/injective`), `Zero` instance, 37 pins. Integrator audits round 1 and 2
closed. Integrator is now aec6914709d96f496 (aba0beaa578594e92 retired).

**L0 in progress: branch `lane/retained-l0`** (staging merged at `f566153b1`, then the WIP commit
"Theory.Store over SparseMap"). `Theory/Store.lean` is switched (`Store L := SparseMap (Address L) …`,
`Layout` gains instance-implicit `namespaceCode`/`keyCode : StoreKey …`, `Store.ext`, `coe_set`; the
example layout gets a `StoreKey Namespace` from `ctorIdx`); it, `Theory/CellStateAux`, `Theory/CellState`
and `Theory/Retained` elaborate unchanged over the tree (Retained's `decide` witnesses included).
Astra round 2 (`scratch/l0/astra-review-2.txt`) approved the type replacement with these terms: keep
`toDFinsupp` as the spec view; keep `StoreCodec.sortedSupport`'s wire order (tree order is not wire order);
injective `List Nat` codes accept countability as a real restriction (World's `TxId`/`D`).

**Method (the Mac, no lake):** `scratch/l0/lc.sh FILE` elaborates one file with lake's options
(`-R . -Dcompiler.relaxedMetaCheck=true -Dbackward.proofsInPublic=true -Dbackward.privateInPublic=true`) and
writes its olean into a symlink mirror of `/Users/ember/dev/minidregg-lanes/iter-speed-land/.lake/build/lib/lean`
(read only) at `<scratchpad>/retained/olean`, LEAN_PATH in `<scratchpad>/leanpath2`. `scratch/l0/topo.py
Theory.Store` lists the 1,090 dependents in topological order (`scratch/l0/l0-order.txt`, 44 in Theory);
`scratch/l0/runwave.sh LIST LOG` compiles a list in order and logs RED/OK per file. Theory-wave 1
(`scratch/l0/w-theory.log`): 8 of 42 green; the reds have four root causes, every other red is a cascade:
1. **StoreKey instances for key types**: `Theory/EffectDeclaration` (`StateKey`), `Theory/CredentialAuthorityState`
   (`AuthorityPlane` and its keys `CapabilityId`, `IssuerId`, `PolicyId`, `PolicyRevision`, `SubjectId`,
   `Epoch`, `RevocationKey`), `Theory/CanonicalResourceKernel` (`Field`), and in Kernel/Compiler about
   twenty more (`Namespace.Key` families of ClockCell, PayCell, PayCellLegacyV4, PlatformCellLayout,
   SystemCell; StoreCodecBook `Space`; HyperdocumentCell `IndexSpace`; World `SysKey TxId D`;
   `VersionEventId`; `Hyperdocument.Key`; `Digest`). **Decision: do not hand-write ~30 instances; grow
   the vocabulary** (law 11): a `deriving StoreKey` handler (`Theory/DeriveStoreKey.lean`) emitting
   `code a := ctorIdx :: frame(code field₁) ++ …` together with a prefix decoder, and injectivity from
   `decode_code` by `cases a <;> simp [decode_code]`, so each key type adds `StoreKey` to its `deriving`
   clause. Dependent `Namespace.Key space` families take a one-line `match` instance like their `keyDecEq`.
2. **`DFinsupp.ext` on stores** (`Theory/CellStateWitness` :56 :190, `Theory/PlanBinding` :464): use `Store.ext`.
3. **`DFinsupp.update` / `Π₀` on stores** (`Theory/StoreNormalize` :68 states `update_update` over
   `DFinsupp.update s …`): restate over `Store.set` (`SparseMap.set_set`, `set_comm`, `set_self` exist).
4. **`DFinsupp.mem_support_iff` / `0` vs `none`** (`Theory/StoreFootprint` :32-33, `Theory/PlanBinding`
   :292 :332): `SparseMap.mem_support_iff` (reads `≠ none`), `toDFinsupp_support` to transport.
Then the Compiler/Kernel/Assurance/Host waves (1,046 files) on hbox in a pool tree
(`. /home/hbox/pool/pool.env; lane-tree acquire retained origin/lane/retained-l0`, `swarm-build lake build`,
LEAN_NUM_THREADS per pool.env), reading every red of one run together (COORDINATION §4: design the whole
fix set, one build per batch). Known Compiler-side work: `Compiler/FiniteDependentMapCodec` and
`FiniteDependentMapCachedOrdering` build stores as `Π₀` (they become `SparseMap` builders; `supportCached`
becomes `keys` sorted by the wire key); `Compiler/WorldCompact.lean` and `compactEvery` are deleted;
World's `Cells R := Π₀ _ : CellId, Option (Cell R)` becomes `SparseMap CellId (fun _ => Cell R)`;
private cells' `Compiler/PrivateCellRoot` (two `simp [Store.set]` unfolds), the narrowed view's
`DFinsupp.filter` (`ResourceObservationAdmission.narrowStore`, `Kernel/PrivateCellView`,
`Kernel/PrivateCellReceiver` 1274-1330 → `SparseMap.filter`/`filter_apply`), `Compiler/PrivateCellIndex`;
perf-client's `Kernel/DeployedRepresentsCheck` iterates `w.system.support` (switch to `keys`; perf-client
told). Send the sha to the integrator labelled SHARED-INTERFACE (its own cut, one whole-tree build), with
`scripts/check-import-boundary.sh` green and a `grow2.sh` before number.

**Measurement owed:** `hbox:/ci/hpc/sn/grow2.sh` (8 sequential `story new`, Host CPU per story, perf of
stories 2 and 8) on the candidate before L0 and on the L0 candidate; the after is `Store.set`/`DFinsupp.update`
gone from the profile and a flat 2 → 8 slope. Then `scripts/perf/flatness-bench.py` submit ratio, and certify
at two heights (hot-path owns certify; same table).

**Handed to this lane, after L0 (§3 rows):** R1 the op 4 → op 5 challenge (exorcist), R3 the
planner/deriver prepared-write node (perf-client), I4/I5 and §3.6 (coordinator). The lint (§7) is designed,
not built.
