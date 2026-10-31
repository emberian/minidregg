# Private cells lane: state

Lane `lane/private-cells`, Mac worktree `~/dev/minidregg-lanes/private-cells`,
hbox tree `/home/hbox/lanes/private-cells/src`. Design: `docs/RATCHET-LOG-DESIGN.md`
(approved). This file is rewritten in place; it is the lane's present state.

## Job 1: the receipt-fingerprint leak (K-RECEIPT-HIDE)

**The leak, traced.** A receipt is `(transactionId, eventId, acceptedCount, worldRoot)`
(`NativeHostCodec.Receipt`). Op 102 serves it to anyone naming a transaction id, and
`since` gives every reader the transaction ids of the writers of its visible cells. A
declared invocation (the write path of the blinded Hyperdocument and DeclaredEffect
cells) recorded `eventId = ResourceTransaction.effectsDigest command`: unkeyed cSHAKE of
the unsigned command bytes, so a reader holding two candidate commands could hash both
and link the receipt. Four other families did the same: capability delegation and
revocation, realm well, participant key enrollment.

**The statement** (`Kernel/ReceiptEventHiding.lean`, two astra rounds): `DeclaredReceiptHiding`, the
receipts of a legal challenge (one transaction identity, two different commands) are
unlinkable at `num/den < 1` given the reader's common view (no world argument: the
same-leakage rule), with the budget required to admit the reader's own point and
membership hash tests up to a query bound (`BudgetAdmitsPublicHash`, both hashes). Proved:
`legacy_receipt_links` (teeth: the retired id gives gap 1), `unlinkable_of_idealReplacement`
(the hybrid reduction), `declaredReceiptHiding_of_idealReplacement`, and the ideal-model
satisfiable and premise-inhabitation witnesses (`pad_idealReplacement`,
`pad_unlinkable_with_hidden_choice`, `fingerprint_in_pad_model_links`). Open and named:
`IdealReplacement` for the cSHAKE instance (ROM plus credential-signature EUF-CMA, under
the custody premise that a signed ingress never reaches a non-party).

**The fix.** `invocationEvent`'s id is `eventIdOfSigned (signedBytes …)`, a digest of the
exact signed ingress the event already retained (it carries the authority signature that
`withAcceptedOn` authenticates first). The four families use `StableEvent.retained` over
their signed ingress bytes. `invocationEvent_eq_iff`: exact-retry recognition and replay
conflicts are the same relation on new records. **History-breaking**: old records carry
`effectsDigest` ids and the historical re-admission compares whole records, so a world
moves by fresh genesis.
Transaction ids, nullifiers and authorization declarations are unchanged. New persisted
tags registered (`PersistedCodecTags`): this is a codec batch; the accepted fixture's
event ids change. Old histories carry the old ids; a fresh genesis moves over.

**Landed** on main as 7d90da717 (Kimi's review found that bound 0 admitted only
the constant reader; fixed by `0 < queryBound` and `public_signature_refutes`).
The Fixtures umbrella went red because the accepted fixtures carried the old event ids,
and the proofs lane re-recorded them. **Rule for the next codec or event-id batch:**
the fixture re-record goes in this lane's own sha, recorded from a candidate built
from this tree.

**Planted test**: `tests/lean/ReceiptEventLinking.lean` (run with
`--load-dynlib=.lake/native/libmini_kernels_lean.so`).

**Findings to route** (not fixed here):
* The fn archive (`Kernel/FnArchive.lean`) posts exact durable record bytes: every signed
  ingress and every blinded cell's plaintext and blinding. A deployment archiving to a
  public fn group has no hiding at all, receipts or roots.
* The world root on a receipt is the design's separate wrapper obligation (§2); not
  discharged.
* Event ids of the ~35 families already hashing their signed ingress inline are the same
  construction; folding them onto `StableEvent.retained` is pending consolidation.

## Job 2: blinded cells on a private authenticated map

**Statements** (`Kernel/BlindedCellHiding.lean`, wired into the Kernel umbrella, sharing
`Theory/FiniteTapeGap.lean` with job 1). The draft had never elaborated (it used the
keyword `prefix`). Two astra rounds; state now:
* `hybridReduction_holds` (proved): the hybrid composition holds for every instantiation;
  the open obligations are its antecedents.
* `RatchetHidingGoal`, `StandardModelHidingGoal`: now require the final bound below one
  (astra: a bound of 2 accepted perfect disclosure) and `BudgetMeaningful` with the
  hidden-choice witness a distinguisher. Open: `distinguisher` must be the game
  interpreter's concrete attack strategies (stable-token equality, d-decoy membership,
  receipt public-hash tests); a label on a constant strategy still trivializes.
* `MaskedTrieBinding` (proved, `maskedTrieBinding_holds`, from `AuthTrie.Cache.root_lastVal_eq`):
  one commitment under one context means the compared outer inputs differ, or every key
  has the same last value unless two nodes AMONG that key's comparison nodes collide
  (astra: the first version's global collision disjunct was trivially true).
* `CompleteOpeningRelation`, `PerOperationLogCost`: specification shapes, trivially
  inhabited by `False`/`work := 0` until tied to the real projection, authorization,
  execution and counters. They are instantiation targets, not claims.

**Representation: reuse `Theory.AuthTrie`, not a new balanced tree.** Canonical compressed
trie (root a function of the logical map), already the world root's map; an insert
touches one walk, bounded by the public key-bit length `L` (constant in n at fixed `L`;
about log2 n expected for hashed keys, not a worst-case log2 n). Canonicity removes the
tree-shape invariant from binding. Owed before it can carry cells (astra round 2):
* **delete** with branch collapse preserving `Inv`/`Holds` (the trie has insert only);
* **hierarchical keys** matching admission's coverage (`body/atoms/low/…`,
  `annotations/…`; `ResourceObservationAdmission` field mapping), the original address
  authenticated in the leaf, and complete class openings from `AuthTrieRange.reveal_sound`
  (its `reveal_complete` is absent and `revealFor` rebuilds from lists);
* **padding** of private paths to `L` inside ZK, including stopped absence walks that
  would expose a leaf of another class;
* **index collisions**: admission preserves `PathsInjective` or counts them.

**Increment 1, proved** (on the Lean 4.35 bump `cdb399b47`; on staging): trie erase,
scoped reveal soundness (`revealNodes`, a finite comparison scope, not the vacuous global
`Collision`), `reveal_complete`, `classRevealComplete`, the receipt wire shape.

**Increment 2, proved** (the integrator's audit of increment 1, items (a) to (d); astra rounds 5
to 7):
* **Store adapter** (`Compiler/PrivateCellIndex.lean`): a `Store` is a finite map, so first- vs
  last-wins is a property of entry lists only; the adapter reads canonical entries (distinct
  addresses). `indexExact` (last value at every address = the value bytes; none at the
  blinding address), `indexBindsData`, `indexIgnoresBlinding`. Scope: canonical-list binding at
  one fixed wire; that the wire's exclusion is `isBlinding` is the Kernel instantiation's.
* **Erase cost the operation cannot fake** (`Theory/AuthTrieErase.lean`, `EraseCost` in
  `Theory/PrivateCellTrie.lean`): the erase is a heap program (`Prog`: hash, load, store as
  constructors; handles are heap indices) interpreted by `run`, one per operation and a clash
  load charged its size. `EraseCost` fixes its constants before the key, value and digest
  types, the digest function and `L`, and quantifies over every heap representing the cache's
  trie: the result handle represents the erase, and the interpreter's count is at most
  `perBit * L + fixed` on injective live paths. `eraseM_sim`, `erase_cost` at `7L + 3`. Scope:
  abstract operations on a constant-access heap; pure computation between operations is not
  metered. Astra rounds 6 and 7 refuted two weaker forms (a monad-polymorphic erase can type-case
  on the monad; constants after the key type absorb a finite key space).
* **`Cache.reveal_eq`** (`Theory/AuthTrieReveal.lean`): the kept trie's reveal has the honest
  siblings and its members up to order; `revealVerify_perm`; `Cache.reveal_verifies`.
* **Two-class teeth** (`PrivateCellTrie.Witness`): 3-bit keys in two classes over a free
  (injective) digest, so `ClassRevealComplete`'s premises hold and its collision escape is
  impossible (`class_opening_exact`); honest opening verifies, cross-class, withheld and
  other-class reveals refused.
* **Receipt joint witness** (`Kernel/ReceiptEventHiding.lean`): `DeployedRandomized`, the
  signer's randomness on four tapes, constant view, budget exactly the query-bounded public-hash
  tests (`AnyPublicHash`): `IdealReplacement` by `idealReplacement_of_injective` and
  `deployed_receiptHiding` at gap 1/2, inhabitation at `q < T` only (a four-query reader
separates the worlds; cite it with this caveat); `leaked_tape_refuted` (teeth). The reduction
and the ideal-replacement lemmas carry `#assert_axioms` (standard three), so no soundness or
hiding proof can cite the native facts. The public signer is
  refuted unconditionally (`public_signer_refuted_always`). Distinctness of concrete cSHAKE ids
  is a compiled-evaluation fact (`native_decide` over the pure-Lean fast path, the kernel cannot
  evaluate Keccak), pinned with `#guard_msgs` on `#print axioms` (precedent:
  `Kernel/NativeHostStoreIdentity.lean`, `Theory/Sp800185Cshake256Conformance.lean`).
* **Scope selection** (`Kernel/PrivateCellScope.lean`, item 2): `ClassCode` (a fixed-width class
  prefix code; `body` opens its family prefix, covering every `atomsOf`), `scopeSelectsVisible`
  and `scopeSelectsPath` (a reader's `Visible` set is exactly the addresses under one of at most
  `card fields` prefixes, one for a full scope), and the concrete `bitCode` of width `4 + W`
  (satisfiable), with teeth.

**Increment 3** (the integrator's re-audit of increment 2, staging 35737eac4: nothing vacuous;
items 1 to 4 below done; astra round 8):
* **One erase walk** (`Theory/AuthTrieErase.lean`): the oracle walk (`Layer`, `Ops`, `joinM`,
  `clashM`, `finishM`, `eraseM`) comes first; `Trie.join`, `Trie.clashOf` and `Trie.erase` are
  `joinM`, `clashM` and `eraseM` at the identity handler (`trieOps`, monad `Id`), their cases are
  lemmas (`join_eq`, `clashOf_eq`, `erase_branch`, `erase_stop`, `erase_empty`, `erase_leaf`,
  `erase_clash`). The cache's erase and the metered heap program are one walk at two handlers.
  `Trie.reveal` / `walkReveal` are still two implementations; no cost is claimed for either.
* **Width** (`Kernel/PrivateCellScope.lean`): `keyFits` / `addressFits`, the private index's
  admission check (a declared key's digests below `2^256`; content atoms and streams always fit at
  `W >= 64`, `fits_of_addressFits`); `fitScope` cuts a reader's scope to fitting fields without
  changing a fitting address's visibility (`visible_fitScope`); `scopeSelectsVisible_checked` at
  `bitCode 256`. Teeth: `Witness.slot_overflow_shares_tag`, `Witness.overflow_refused`.
* **The seam** (`Kernel/PrivateCellView.lean`): `isBlinding_iff` (the wire's exclusion is
  `isBlinding`); `viewOpeningExact`: verifying reveals at a reader's cut prefixes answer exactly
  `DFinsupp.filter (Visible fields kind) store` (narrowPacked's store) as value bytes, or two
  distinct live addresses on one key path, or a collision in a reveal's `revealNodes`;
  `viewOpeningExact_hashed`: at the receiver's address path (`hashedAddrBits`, a truncated hash of
  the canonical address bytes) the index collision is a collision of that hash on distinct bytes
  among this store's live addresses (`addressCollision_is_hash`, by the address codec's
  injectivity). `honest_accepted` inhabits the premise.
* **Reveal locality** (`Theory/AuthTrieRange.lean`): `climb_digest_sound` concludes with the
  walk's `PathNode`s (one per walked bit plus one), and `revealNodes`' store side is those path
  nodes plus the selected subtree (`revealNodes_store_treeNode`: inside the canonical tree). A
  collision outside the walked path and the selected subtree no longer discharges a reveal; the
  bound is the reveal's stop depth (at depth 0 the selected subtree is the whole store).

**Increment 4** (the integrator's third-round audit of e2f6da711..b027ed235):
* `viewOpeningExact_deployed` (`Kernel/PrivateCellView.lean`): at the receiver's real parameters
  (`addressHash`, 256 bits of cSHAKE256 under `DREGG/PRIVATE-CELL/ADDRESS/v1`; `deployedDig`,
  cSHAKE256 under `DREGG/PRIVATE-CELL/NODE/v1` over injective node bytes `nodeBytesWith`) each
  collision alternative is a real cSHAKE256 collision on distinct inputs among this store's live
  addresses or one reveal's scope. The address alternative ranges over every live address of the
  store, not only the reader's classes (conservative, not local).
* `Witness` there: a declared cell with two data fields, another class and the blinding, a free
  injective node digest and an injective address path; both collision branches refuted
  (`Witness.exact`), honest reveals verify, answers and refusals for a slot-1 reader, the full
  scope, and an overflowing slot whose tag aliases slot 1 (answered nothing; such a store is
  refused at the gate).
* The gate: `storeFits`, `FitStore`, `admit` (refuses; `admit_refuses`), and
  `admitted_of_storeFits` discharging `admitted`.
* Locality wording: bounded by the reveal's stop depth.

**Increment 5, the receiving state machine** (`Kernel/PrivateCellReceiver.lean`, astra round 9
applied):
* `KeptCell`: params (protocol, cell, layout, size bound, the wire's `Blinding`), accepted
  version, gated store (`FitStore`), kept index with `holds`, mask bytes held directly (`mask_eq`).
  Every constructor passes the gate: `birth` runs `admit` on the whole store (`birth_refuses`),
  `write` checks the one address (`write_refuses`), so no receiving path exists without it.
* `write`: refuses the blinding address (`write_refuses_blinding`: the mask moves only by
  `accept`); a value is one `Cache.insert`, a removal one `Cache.erase` (`write_none_index`).
* `accept`: one accepted version: the next version and its mask `Params.prf (version + 1)`, then
  the patch in order, for a no-op too; no caller supplies a mask (fourth-round audit).
  `accept_spec` gives the resulting store exactly; `accept_isSome_iff`: accepted exactly when every
  write fits and avoids the blinding. `History.custodyInputs_distinct`: across a cell's history the
  custody function is evaluated at pairwise distinct versions (inputs only: a constant function
  passes it). Freshness is the named premise `Custody.CustodyPrf` (round 6): the ideal fixed as the
  uniform function on the version window (`idealFn`, tapes enumerate all functions by
  `finFunctionFinEquiv`), the budget admitting every two-query evaluation test
  (`BudgetAdmitsQueries`); honest pole `enumeration_satisfies`, teeth `constant_refuted`.
  Round 7: queries are restricted to the window (`QueryTest` over `vs ⊆ window`), so a real PRF can
  meet the game. `receiver_prf_hop`: one birth store and one patch list, the custody function alone
  varying with the key (`run`, `run_twin`: the runs are twins cell by cell, same public parameters,
  versions and kept index); the published transcript (the run's roots) factors through the masks
  over a shared skeleton (`roots_factor`); the gap between the transcript under the keyed function
  and under the ideal is `num/den`; the versions are distinct and the ideal's masks at them are the
  tape's own tuple (`idealFn_window`). `AtMostOneSuccessor` is not a premise of the hop: a run is one
  chain (`History.atMostOneSuccessor`), and that the host publishes exactly its run stays the
  host's obligation. Forks: `AtMostOneSuccessor` is the host's
  obligation (a persisted version counter, a retry returning the stored successor); a history meets
  it, and `fork_shares_mask` shows two accepts from one cell share a mask.
* `birth` refuses a store already holding a mask (`birth_refuses_masked`: imports are never
  silently re-masked) and accepts any other gated store (`birth_accepts`); `blinding_fits` proves
  the registry's blinding address passes the gate, so no caller supplies that either.
* `privateRoot` is `BlindedCellHidingDraft.maskedTrieCommitment` itself: one commitment definition.
* `root` / `root_eq`: the outer commitment (cSHAKE256 under `DREGG/PRIVATE-CELL/OUTER/v1` over the
  state-derived context, the held mask, the kept digest) equals `privateRoot`, with no rebuild and
  no store lookup.

**Owed, in order:**
0. **The hiding goals out of the Draft namespace** (`Kernel/BlindedCellHiding.lean`), statement
   first, with `CustodyPrf` as the PRF premise of `StandardModelHidingGoal` / `HybridReduction`'s
   first hop and `AtMostOneSuccessor` as the fork premise.
1. **The cell representation carries `KeptCell`**: `Materialized.rootCache := KeptCell.root`,
   `rootExact` by `root_eq` and a materializer whose `rootOf` is `privateRoot` (context made
   explicit in the specification: `rootOf : Store → Root` cannot see the accepted version), patch
   application through `accept` with no rematerialization, export bytes lazy.
2. **The registry and native-host switch** for content and the declared kinds: a root-format change
   (fresh genesis, fixture re-record in the same sha), codec epoch ordered with the hot-path lane
   (a86738fc1dfae6429 answered 10-31: no overlap with Materialized, CellState, PersistedCodecTags or snapshots; private cells go first; it reports before touching a format). The receiver's acceptance theorems cite `admit`; **no receiver
   path ships without it** (the agreed ordering: not on today's `Action.admissionCheck`, the source
   of `DeclaredActionAir` and the native binding's acceptance theorems).
3. **Insert metered**: `Trie.insert` backs the world root's hot path (`Kernel/WorldRootCache`), so
   the oracle walk enters as a proved `@[csimp]` equality, not a rewrite of the compiled walk.
4. Retention of accepted versions for retries and historical reads; path collisions are refused or
   counted (the `7 L + 3` erase bound needs injective live paths).
5. The opening relation in the compiler's vocabulary (compiler-emitted AIR; grow the compiler
   where it lacks a trie-path or cSHAKE gadget), not a hand-written circuit.
6. Flatness: gate10/gate12 flatness-submit.

**Linear paths seen** (each blocks flatness independently): flat `rootPreimage`
(44 + 32E bytes per write, `StoreCodec`), whole-view `items` in `StoreHiding.view` and
`ResourceView`, `NativeThinConsent.checkOpened` recomputing the flat root, whole-cell
serialization in `canonicalPostBytes` of every durable write, `streamPayload` and `since`
scanning the accepted log, `historicalReceipt`'s `findIdx?` (cached variant exists).

## Continuation (for a successor)

* **Trees.** Mac worktree `~/dev/minidregg-lanes/private-cells` (branch `lane/private-cells`,
  pushed). hbox warm tree `/home/hbox/lanes/private-cells/src` on Lean 4.35: sync edited files with
  rsync, iterate with `swarm-build lake env lean <file>` (seconds to minutes), batch with
  `../b6.sh` (full `Theory Kernel Compiler Minidregg Host` plus the planted receipt test, about
  10-40 min warm; log under `../logs/`, PID file beside it). Before READY, verify each committed
  `.lean` file equals the hbox copy (`git show HEAD:f | ssh hbox cmp - …`).
* **Landing.** Integrator aeb671706eb3f70d7: a sha stacked on the lane's last merged commit
  (staging, never main), with the full build result. Merged so far: through bf2bfe84a; b076a4806
  sent READY. Codec or root-format batches carry their own fixture re-record.
* **Next increment** (owed item 1 then 2): a cell representation carrying `KeptCell` (read
  `Theory/CellState.lean` `Materialized`/`materialize`/patch application near line 263, and the
  hot-path note: checkpoints persist the State and roots are recomputed on open by
  `openSealedWith`/`RootCache`), then the registry switch (`Compiler/CanonicalCellRegistry.lean`
  `materializer`/`wire?`; layering: `fieldOf` is Kernel, the registry is Compiler, so the private
  materializer is selected in Kernel or `fieldOf` moves down). Tell hot-path a86738fc1dfae6429
  before that sha lands.
* **Review practice.** Statement first; codex astra (`codex exec -m gpt-6-astra -s read-only -C
  <worktree> "<prompt>"`) as peer on each statement and proof claim; Kimi via the integrator for
  non-vacuity. Every round so far found real defects: apply them, never weaken.
* **Lessons.** Scoped collisions, never a global `Collision` disjunct; collision disjuncts must be
  stated at deployed parameters (an abstract hash or width makes them free); a cost Prop over a
  polymorphic operation is fakeable, so make the operation a program an interpreter charges;
  quantify constants before the size parameters and the types; budgets need a positive query
  bound; a witness at the wire shape is not an admitted invocation; `Action.admissionCheck` feeds
  a derived AIR and the native binding, so admission bounds go on new receivers, not there.
