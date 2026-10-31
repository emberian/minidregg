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

**Increment 1, proved** (on the Lean 4.35 bump `cdb399b47`; two astra rounds on the proofs):
* `Theory/AuthTrieErase.lean`: `Trie.eraseCounted` walks once, re-joins each level (a lone
  leaf rises without rehashing), and counts the work: visits, every digest evaluation
  (`joinCost`, the empty-child digests a fresh branch reads included) and clash entries.
  `erase_correct`, and `erase_cost` at `4 * L + 1` on injective live paths, constants chosen
  before `L` (astra: constants after `L` could hide a rebuild). `EraseCost` constrains the
  returned count only, so the claim is about this operation's own instrumented count;
  allocations are O(1) per visit and not separately counted.
* `Theory/AuthTrieRange.lean`: `tree_injective`, `climb_digest_sound` and `reveal_sound` now
  conclude with a collision AMONG `revealNodes` (a finite comparison scope, over-approximating
  the nodes hashed), not the vacuous global `Collision`; `Compiler/DurableIndex.reveal_sound`
  follows.
* `Theory/AuthTrieReveal.lean`: `reveal_complete` (the honest reveal verifies); `Trie.reveal`
  reads it off the kept trie in walked depth plus answer (its equality `Cache.reveal_eq` owed).
* `Theory/PrivateCellTrie.lean`: `classRevealComplete`, `erase_correct`, `erase_cost`.
* `Kernel/ReceiptEventHiding.lean`: the challenge carries the native envelope shape
  (`Challenge.envelope_decodes`); `DeployedShape.premises_inhabited` inhabits every keystone
  premise but `IdealReplacement` at that shape (a syntactic challenge, not an admitted
  invocation: version, target envelopes and header binding are admission's); the refutations
  take ingress reconstructible from the reader's view.

**Owed** (astra round 3): the Store adapter (namespace-qualified address, canonical value
bytes, layout binding; `StoreCodec.fromEntries` is first-wins, the trie last-wins); the
projection target is `Visible`/`narrowPacked`, NOT `narrowStore` (which keeps blinding under
full scope), and the private index omits the blinding entry (mask custody separate); scope
coverage equals a bounded prefix union (`body` covers every `atomsOf low`); multi-class,
overwrite and deletion witnesses; store-side collision locality (authentication path plus
selected subtree); `Cache.reveal_eq`.

**Next increments** (in order):
1. The Store adapter and the class-prefix = `Visible` theorem; `maskedTrieCommitment` over the
   kept cache (the bulk root is the spec only).
2. The opening relation in the compiler's vocabulary (compiler-emitted AIR; grow the
   compiler where it lacks a trie-path or cSHAKE gadget), not a hand-written circuit.
3. The receiver: new materializer version beside the old one until a fresh genesis, with its
   fixture re-record in the same sha; coordinate the codec epoch with the hot-path successor.
4. Flatness: gate10/gate12 flatness-submit.

**Linear paths seen** (each blocks flatness independently): flat `rootPreimage`
(44 + 32E bytes per write, `StoreCodec`), whole-view `items` in `StoreHiding.view` and
`ResourceView`, `NativeThinConsent.checkOpened` recomputing the flat root, whole-cell
serialization in `canonicalPostBytes` of every durable write, `streamPayload` and `since`
scanning the accepted log, `historicalReceipt`'s `findIdx?` (cached variant exists).
