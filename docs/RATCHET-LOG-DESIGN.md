# Blinded-cell updates without a whole-cell privacy ratchet

Research draft, 2026-10-30, codex (gpt-6-astra). Source tree:
`d3c8c57af7309af0ba5df2e1ebe44a9774c4ee65`, `lane/ratchet-research`.
No receiver, codec or security implementation changes in this deliverable.

## Decision

**Replace the flat opening protocol, not just its hash.** Recommend a private,
persistent authenticated map; one freshly blinded commitment to its root per
accepted cell version; and **zero-knowledge, complete selective-opening proofs**
instead of publishing hidden leaves or Merkle siblings. An ordinary bounded
write changes O(log n) map nodes and one outer commitment. A bounded selective
read proves O(log n) work; full exports pay for their output. This is a new,
versioned commitment/view construction, not a claim that a root wrapper preserves
`StoreHiding.items` unchanged.

This fits the actual trust boundary: the Host already knows the store and blinding;
the adversary is another reader, not the Host. ORAM is the appropriate extension
if an observer must also see physical storage snapshots or access traces. It is
unnecessary for the narrower, currently implemented disclosure boundary. The
security reduction below is for **every polynomially bounded sequence** of
published commitments and authorized query answers, with explicit leakage. Its
primitive assumptions and unimplemented receiving obligations are separated.

Do **not** switch production to per-entry epochs on the strength of this draft.
They are a viable simpler implementation only with the explicit change-pattern
leak in §7. There is a better asymptotic design under the present observer model;
its principal price is the new zero-knowledge opening protocol and its constants,
not an ORAM position map. This research does not claim that the new design would
pass today's flatness bench before the other linear paths are replaced.

## 1. What the code actually exposes

The following references are source evidence, not observations of the deployed
binary or a network capture. The Lean check could not start: SSH to the designated
`dregg-build` box refused authentication (`publickey,password`). The draft is
unelaborated; no Lean build was run on the Mac.

| Path | Actual representation / disclosure |
|---|---|
| `Compiler/HyperdocumentCell.lean:437–461` | `contentWire` identifies the content layout and its `.blinding` entry; `contentMaterializer` uses `StoreCodec.materializer`. |
| `Compiler/DeclaredEffectCell.lean:141–162` | Declared cells use the same machinery, with an integer blinding entry. |
| `Compiler/LegacyContentCarry.lean:614–628` | A migration from Store2/content-v3 copies the old birth blinding and takes one **current** ratchet step at carry height. This is not a third ongoing write protocol; pre-carry history is not retroactively ratcheted. |
| `Kernel/ResourceTransaction.lean:781–808,1120–1169` | Source operations execute on the loaded pre-state, then the kernel appends the blinding patch. Scalar/content receiving theorems establish the post key. |
| `Compiler/StoreCodec.lean:645–713,1044–1138` | The Host holds the key. Entry salt is KMAC256(key, canonical entry bytes); a leaf is cSHAKE256(salt, entry). A height-keyed KMAC chain advances the key on writes. |
| `Compiler/StoreCodec.lean:818–868` | Root is a flat hash of the frame and all 32-byte leaves. `rootPreimage_length` proves **44 + 32E bytes**, E including the blinding entry. It is not a Merkle tree. |
| `Compiler/StoreHiding.lean:110–146` | `view = (saltedRoot, items)`. Canonical address order, one item per entry: either salt + entry, or the hidden leaf. Readers recompute the flat root. |
| `Kernel/NativeObservationController.lean:726–767,1260–1283,1292–1315,1639–1656` | `ResourceView` carries root, narrowed packed bytes, narrowed balances, opening frame + **all items**, and optional compute quote. Resource/scope queries encode it. At-height views carry the corresponding historical narrowed image and opening. These are query responses, not evidence of an automatic full-view broadcast on each write. An observer can nevertheless query after every write. |
| `Kernel/ResourceObservationAdmission.lean:677–749,849–879` | Visibility comes from admitted scope fields; blinding is erased even for full-scope readers. Content includes body, annotations and `atomsOf low64`; declared cells include slot, balance and code fields. Colluding grants must be treated as their combined observations. |
| `Kernel/NativeThinConsent.lean:341–386` | Consent decodes this opening, recomputes `rootOfItems`, checks opened bytes against the narrowed cell, and applies the member patch. A new root with the old checker is not an implementation. |
| `Kernel/NativeObservationOpeningCache.lean:55,240–244` | Cached openings are proved equal to the same flat rendering. Caching does not change disclosure or new-version cost. |
| `Kernel/DurableDataIntent.lean:92–96,119–134`; `Compiler/DurableReceiverCodec.lean:75–81` | Durable writes carry full `canonicalPostBytes`, pre-root and exact post-root. The journal/store custodian sees plaintext and the blinding. No snapshot-hiding claim applies to those bytes. |
| `Compiler/NativeHostCodec.lean:316–330`; `Kernel/NativeHost.lean:1625–1628` | A receipt carries transaction id, event id, accepted height and world root. A receipt is not a flat cell opening. |
| `Kernel/NativeObservationController.lean:1040–1056,1677–1684` | `since` reveals height, signer, transaction id and the visible cells written. Cell-level activity is already disclosed. |

**An additional boundary matters:** `ResourceTransaction.effectsDigest`
(`Kernel/ResourceTransaction.lean:428–453`) hashes the command framing without a
secret mask. `DeclaredResourceController.invocationEvent`
(`Kernel/DeclaredResourceController.lean:1718–1722`) uses it
as the receipt's event id. A receipt-holder who knows two candidate command
encodings, including nonce/context, can hash both and distinguish them. A hiding
cell root cannot fix this. Transaction identity is separately derived from
(domain, semantics, subject, nonce), not the command body
(`Kernel/ResourceTransaction.lean:464–470`).

Consequently, “any published snapshot” must mean the authorized **resource
projection**, not every internal `DataSnapshot` or the entire journal. For a
receipt-inclusive guarantee, either include these command fingerprints in allowed
leakage (which rules out the corresponding challenge pairs), or replace public
event fingerprints with blinded commitments/proofs and retain exact event bytes
inside custody. Do not silently call the fingerprint pseudorandom. The useful
non-vacuous claim here is hiding changes to never-disclosed entries from resource
readers with identical other public observations; it is not general transaction
privacy.

`StoreHiding.change_detection_only_via_root` proves collision/coincidence
alternatives and leaf non-survival, not a probability bound against all algorithms.
`SaltedLeafHiding` and `RatchetedViewHiding` remain named indistinguishability
premises, not discharged computational games (`Compiler/StoreHiding.lean:225–249,
278–309,427–455`). Making every leaf different removes one distinguisher; it does
not itself establish indistinguishability. We replace that missing argument below.

`docs/HOT-PATH-STATE.md` also identifies whole-cell serialization, law checking,
projection, client preparation and checkpoints. Its recorded runs include 8.30×
and 9.585× submit CPU growth against a 2× bound; the brief's 7.8× is not the number
in this checkout. No new benchmark was run. Law 17 is `ATLAS.md` §6, law 17.

## 2. Security experiment and scope

Let λ be the security parameter, n the maximum live entries, T the number of
**distinct published cell versions** (including initialization), M the number
of proof responses, Q the number of outer-hash oracle queries, and τ the
adversary's computational budget. Include all cells in T for a combined claim.
These quantities are polynomially bounded in the security experiment. An
unbounded observer over an infinite lifetime is not promised a fixed epsilon.

An adversary A has auxiliary information, keeps every response, colludes across
reader identities, and adaptively requests current or retained historical views.
At each turn it submits two candidate logical operations, or two queries, for
worlds 0 and 1. A fixed secret bit b chooses which world answers. Both worlds
start from explicitly related, valid stores. Both branches advance throughout
the game. Invalid challenge pairs are rejected identically, without consulting b.

The **same-leakage rule** requires, at every common transcript prefix:

* the same cell ids, schema/layout identities, version schedule, publication and
  query schedule, success/refusal outcomes, and public bounds for padded messages;
* the same authorized answer bytes, including existence/absence, field coverage,
  balances, quotes, and any links or other ancillary answers the game exposes;
* the same released cardinalities/support information. For conservatism the game
  may give the old view's open/sealed pattern and insertion/deletion positions
  as leakage too; the recommended wire need not send them;
* the same remaining public metadata, including any receipt/event fingerprint
  or action details given to A. The roots and ZK proof bytes being challenged are
  **not** placed in this leakage. Public world-root/signature wrappers must be
  computable from the challenged transcript plus this leakage and independent
  public coins; otherwise they need a separate reduction.

Call this leakage L. The protected fact is the hidden target/content and its
cross-write equality pattern **beyond L**. At least two hidden entries and an
in-place update provide a useful challenge with identical authorized outputs.
Reading either differing value later is an inadmissible challenge unless the
states have converged before that disclosure. This is necessary, not a
selective-opening security shortcut: a legitimate plaintext answer distinguishes
those worlds. In contrast, an old opening of an equal value followed by revocation
must not identify subsequent hidden updates; §4's simulator covers that case.

Define the distinguishing gap

```
Adv_hide(A) = | Pr[A(View_0) = 1] - Pr[A(View_1) = 1] |.
```

Probabilities include key generation, masking/proof coins, oracle randomness and
A's coins. This convention has maximum 1. Success in guessing a uniform b is at
most `(1 + Adv_hide(A))/2`. Honest custody and publication are assumed for hiding;
a malicious publisher can always signal secrets in timing or proof coins.
Binding/soundness against a malicious publisher is a separate requirement.

Excluded: custody-key compromise, raw journal access, physical page addresses,
cache/fault traces and latency dependent on hidden data. Timing/request frequency
is explicitly released, as in standard ORAM [P]. Padding proof shape must depend
only on public bounds/L, not on secret tree shape or the changed key. If physical
snapshots are published, use the stronger ORAM observer in §6 instead.

## 3. Recommended representation and receiving contract

### 3.1 Private persistent index and fresh outer mask

Maintain an authenticated persistent balanced search tree, keyed by
`(visibilityClass(kind,address), canonicalAddressBytes)`; leaves contain canonical
entry bytes and branches commit to their child hashes, size, ordering bounds and
balance metadata. Domain-separate leaves, branches, empty trees and outer roots.
Each node has bounded metadata; value and key bytes are charged explicitly.
The class function is emitted from the Lean visibility definition, not independently
implemented in Rust. Body/atomsOf/annotations and declared field classes admit
prefix/range selections; arbitrary future predicates require an index or an
explicitly output-sensitive scan, not a claimed cheap generic filter.

The tree shape is part of the **versioned materialized representation**. A logical
store can have more than one balanced representation. The required binding is
“one accepted root cannot open to two different logical projections,” not “all
construction histories of a logical map produce one tree shape.” Do not rebuild
a sorted-median canonical tree on each append: that can change linearly many
nodes. Preserve the tree and check local rotations. A canonical sparse hash trie
is an alternative with O(λ) path work, but its address-hash collisions and full
field enumeration must be specified; it is not needed for this bound.

Let R_t be the **private** inner root. Publish

```
ctx_t = encode(protocolVersion, cellId, layoutDigest, acceptedVersion, publicSizeBound)
r_t   <- {0,1}^λ
C_t   = H_outer(encode(ctx_t, r_t, R_t)).
```

The salt and R_t are never disclosed to a narrowed reader, including as auxiliary
Merkle proofs, update certificates, content-addressed node URLs, or diagnostics.
Freshly mask every accepted version, including a no-op if that version is
published. Re-serve the same C_t for repeated reads and exact retries of that
version; do not invent a second commitment after an uncertain reply.

Either obtain independent randomness at the custody boundary or derive masks
from an independent PRF key with unique `(cell, acceptedVersion, schemeEpoch)`
labels. The mask-generation key must not be a public seed or an entry disclosed
by a full-scope query. Keeping the present self-keyed KMAC chain would require a
separate related-key/chain argument; an ordinary PRF assumption does not by itself
prove that chain. The reference security argument uses independent uniform r_t.
An independent mask-PRF adds the explicit term in §4.

Retain `(r_t, R_t, manifest)` under custody for historical queries and exact
recovery. Persist the accepted choice atomically with the transaction identity,
pre-root and resulting C_t. Garbage collection follows retained-history policy.
No fresh random choice on retry, no rollback of a PRF label, no full snapshot
serialization as the durability mechanism. A versioned patch/manifest commits
the exact changed nodes, salt and resulting root; full logical export remains
available separately. A root-format change is not byte-compatible Store3.

### 3.2 Selective openings replace the flat list

A response is `(ctx_t, C_t, scope/query, authorized projection, π)`. The ZK
relation checks knowledge of r_t and a private tree witness such that:

1. the outer hash equals C_t and the tree root equals R_t;
2. returned entries and absence answers are authenticated at that tree root;
3. the answer is the **complete** projection for the requested, currently
   authorized scope/window, not an arbitrary subset of valid leaves;
4. all context, range endpoints, query arguments and result bytes are bound.

For a range, use membership plus authenticated boundary/adjacency checks, or a
multiproof whose omitted subtrees provably lie outside the requested ranges.
All sibling hashes, hidden ordering bounds, directions, blinding metadata and
private node contents stay inside the ZK witness. Merely wrapping an ordinary
Merkle proof in a signature is insufficient. No per-entry public update tokens.

A valid-index invariant must be established at birth and preserved by every
accepted patch/rotation; it covers ordering, uniqueness, authenticated subtree
bounds/counts and agreement with the logical `Store`. Otherwise a dishonest
subtree count or range bound can hide an omitted entry. This is an **admitted
history obligation**, not something a point membership proof establishes.
Receivers must check the invariant incrementally against the held pre-invariant;
requiring a fresh proof of validity of the entire tree on every read would lose
the cost bound. The verifier's trusted history/certificate must bind this exact
index validity, just as it binds the root, without synthesizing original admission
from a cached flag.

For bounded queries, a circuit verifies O(1) paths of O(log n) nodes. A linear-size
Boolean-circuit ZK construction gives linear work in that circuit at fixed
security parameters; succinctness is not necessary. ZKBoo's circuit-size formula
and ROM transformation provide a concrete feasibility reference [Z], **not** a
claim of an installed or fully instantiated Mini backend. The chosen backend
must provide adaptive multi-theorem ZK, not just honest-verifier ZK; its simulation
and soundness budgets must be recorded. Existing STARK/Selvage names do not
supply this obligation automatically. Compile the relation from Lean; Rust owns
physical crypto execution/custody, not authorization or tree semantics.

### 3.3 The actual cost bound

Let h ≤ a + b log2(n+1) be the maintained balance bound, Δ the entries changed,
B the input/new-value byte length, k the entries returned, and s the number of
normalized query ranges (query length is charged). For constants independent of
n and accumulated history H:

```
node work per write ≤ c0 + c1 (Δ+1) (h+1)
write bytes/work    ≤ c2 B + c3 (Δ+1) (h+1) + c4 log2(H+2)
read circuit gates  ≤ c5 B_answer + c6 (k+s+1) (h+1).
```

Balance maintenance, hashes, copy-on-write allocation and private manifest
updates are included, on successful and refused operations from valid states.
The model counts RAM/I/O work with bounded key/hash widths and word-sized
pointers/counters; key comparisons are not allowed to scan unbounded hidden
values. A bit-complexity accounting of unbounded integers adds its corresponding
logarithmic factors and must be reported separately. The final history term is
the persistent history/manifest index, not a rescan. PRF/mask and outer-hash work are constant for bounded ctx.
Persistent current storage is O(n); retaining T versions adds O(Σ(Δ_t+1) log(n_t+1))
nodes plus payload bytes and O(T) masks. Public roots cost O(Tλ), plus requested
proofs/answers. Construction/migration of n existing entries is a charged bulk
operation; no periodic O(n) rebuild is hidden in these bounds.

For a fixed-size write and bounded accompanying query, with a prover/verifier
linear in gate count and security parameters fixed, total work is O(log(n+H+2)).
If a chosen backend instead costs G log G for G gates, report
O(log n log log n), **not** strict law-17 compliance. Full views/exports with
k=Θ(n) cost at least Ω(n) just to transmit; no cryptography removes this. In
particular, never run the old full-view client preparation on every append and
charge it to “read time.” Query-specific append context and incremental admission
are part of the same receiving change. See `docs/HOT-PATH-STATE.md` for consumers.

## 4. Sequence-wide hiding argument

This is a reduction for the construction in §3, not a proof that cSHAKE256 is a
random oracle or that the present implementation realizes it.

Assume:

* H_outer is a λ-output random oracle, separated from tree hashes, proof
  commitments and Fiat–Shamir challenges by unambiguous domains. Encodings are
  injective. Contexts distinguish every published version. The adversary and
  simulator together make at most Q queries to H_outer, with Q < 2^λ.
* For at most M adaptively selected responses, the proof system's real transcript
  can be replaced by its simulator on public statements with distinguishing gap
  at most ε_ZK(λ,M,τ',Q'). The simulator receives **no** r_t, R_t, private siblings
  or operation targets. Its programmed oracles are separate from H_outer. It is
  a total algorithm on well-formed statements; the ZK guarantee is needed on
  true statements. M counts historical re-proofs as well as current ones.
* Honest proof coins are fresh; padding and every other output follow L. If
  masks are PRF-derived, the entire mask-generation transcript can first be
  replaced by independent uniform masks at gap ε_F(λ,T,τ',Q'). With genuine
  independent masks, ε_F = 0. This term includes custody RNG/derivation assumptions,
  not a silently asserted 256-bit entropy for arbitrary integers.

For either branch b, perform these hybrids:

1. Replace mask derivation by independent masks: cost at most ε_F.
2. Replace all opening proofs by the adaptive ZK simulator: cost at most ε_ZK.
   The public statements/answers remain the same. This removes openings and
   witness-dependent proof information from the observer's view.
3. Lazy-sample an independent uniform λ-bit string U_t for each new version and
   use it instead of C_t; re-use it for queries to that version. Couple the outer
   oracle by assigning U_t at the hidden input `encode(ctx_t,r_t,R_t)`.

The coupling fails only when an observable oracle query guesses a hidden mask
input. Conditional on no prior hit, a uniform mask has at least `2^λ-Q` possible
values. A union bound over at most Q queries and T versions gives

```
p_bad ≤ min(1, T Q / (2^λ - Q)).
```

This deliberately loose bound also covers oracle queries made before a version
is published and correlations among private inner roots. Unique contexts prevent
two version inputs from being the same even if masks or states repeat. Colliding
**outputs** are already present in the uniform experiment; no birthday term is
needed for hiding. Tree hash collisions belong to binding, not this hybrid.

After replacement the simulator needs only L, an independent U_t per published
version, and the public query/answer. The two worlds' ideal distributions are
identical by the online same-leakage rule. Adaptivity is covered by induction on
the common simulated transcript: the next pair of operations is chosen from the
same distribution in both worlds. Taking the triangle inequality across both
worlds yields the promised bound:

```
Adv_hide(A) ≤ ε := min(1, 2 ε_F + 2 ε_ZK + 2 T Q / (2^λ - Q)).       (H)
Pr[guess b correctly] ≤ 1/2 + ε/2.
```

If a backend only supplies a per-response ZK bound δ with auxiliary-input
adaptive composition, use ε_ZK ≤ Mδ with the reduction's resource overhead
charged in τ', Q'. A single-instance/HVZK theorem alone is not that premise.
The ZK proof must verify the **same** commitment computation that the hiding
analysis models.
A generic SHA/cSHAKE circuit benchmark is not a proof of a ROM-aware composition:
instantiate an appropriate joint model, or use the standard-model formulation
`Adv_hide ≤ 2ε_commit + 2ε_ZK`, where ε_commit is multi-version hiding of the
concrete outer commitment. The ROM calculation above explains its proposed
ε_commit bound; it does not prove that idealizing a circuit's fixed hash is sound.
A direct standard-model assumption for the same byte construction is that
`F_r(ctx,R)=H_outer(encode(ctx,r,R))`, keyed by uniform r, is a PRF. There is
only one distinct message under each version key; repeated reads reuse its
output. A T-key adaptive hybrid replaces these outputs by independent uniform
words at cost at most `T·ε_PRF(λ,τ'')`, where the single-key reduction simulates
all other keys and knows the selected world's R. An earlier mask-derivation
replacement costs ε_F as before. Thus an alternative explicit bound is

```
Adv_hide ≤ min(1, 2ε_F + 2T·ε_PRF + 2ε_ZK).                      (H-SM)
```

This is a substantive keyed-hash assumption, not a consequence of collision
resistance, and its reduction budget includes simulated keys/circuits. It is
compatible with proving the actual fixed hash circuit; [Z, §5.2] makes the
analogous PRF-in-the-randomness assumption for hash commitments. Cross-input
binding remains a separate collision/extraction obligation. Use this explicit
assumption, or a concrete analyzed commitment such as Pedersen (§5), when the
joint ROM/circuit model is unavailable; do not treat (H) as an implementation
certificate. Pedersen avoids the masking idealization and PRF hiding assumption.
For λ=256 and T,Q ≤ 2^40 the **outer masking contribution alone** is less than
2^-174. This is not a 174-bit claim for the full system: ε_F and ε_ZK are still
uninstantiated. No concrete deployed epsilon is claimed.

The simulator argument is why this is stronger than saying that every leaf
changes: A may compare any function of arbitrarily many responses, including old
openings of entries subsequently hidden, subject to L. Conversely, giving even
one stable hidden sibling hash to A invalidates hybrid 2 and the theorem.

### Binding and exact preimages are independent

A binding reduction needs an explicitly knowledge-sound/extractable backend:
ordinary statement soundness alone does not give the collision witnesses to a
reduction. Two extracted inconsistent openings must yield an outer-hash or
inner-tree collision, or a failure of the admitted index/logical-store invariant
or context binding. With those invariants proved and the extraction budget
charged, the reduction has the form
`ε_bind ≤ ε_extract + ε_CR,outer + ε_CR,tree`; do not assume hash injectivity.
A constant-root scheme satisfies hiding and fails this obligation. Correct
complete queries, nonmembership, wrong scope/version refusals, and exact retry
identity therefore accompany the hiding statement. Neither privacy nor a valid
membership proof authorizes a write.

## 5. Candidates compared

Costs below exclude changed payload bytes and explicitly requested full output.
Security parameter factors are stated separately from n. They are construction
costs, not measured Mini timings. “Private” means private from the specified
observer, not inaccessible to the Host.

| Candidate | Write / other work | Storage | Leak and assumptions / verdict |
|---|---|---|---|
| Current K-HIDE-ROTATE + flat root | Ω(n) salt/leaf work and hash input; full view Ω(n) | O(n), plus full history copies today | Count/order and public metadata; computational transcript hiding assumed, not proved. Keep until replaced. [code §1] |
| Per-entry epoch + persistent Merkle map | O(Δ log n); proof paths O(log n), flat exports still Ω(n) | O(n); O(Δ log n) retained nodes/write | Exact unchanged/changed slot pattern across aligned snapshots, with return-to-old-value equality suppressed if epochs never repeat. §7. |
| Fresh root wrapper + ordinary Merkle openings | O(Δ log n) | O(n) | Root-only hiding is possible; stable siblings/path identities leak under repeated selective openings. Rejected for the existing reader. |
| **Private Merkle map + fresh outer commitment + ZK complete openings** | **O(Δ log n)**; proof cost O((k+s+1)log n) times fixed crypto factor for linear-circuit ZK | O(n), persistent history as §3 | Hides hidden change pattern beyond L; ROM + multi-theorem ZK + optional mask PRF. Recommended; new wire/receiver required. |
| Path ORAM, host-private position map | O(log n) encrypted blocks transferred; client work also pays stash/eviction processing, not automatically O(log n) | O(n) encrypted tree + O(n log n) private map bits + stash | Full access traces hidden up to length/timing/failure; IND-CPA encryption and stash bound. Good stronger-observer reference; selective disclosures need composition. [P] |
| Recursive Path ORAM | Common uniform-block accounting O(log² n / log χ) bandwidth for B=χ log n; parameters matter | Linear server tree; reduced client storage | Avoids a large private map at extra cost. No reason here to pretend the Host has only tiny private storage. [P, §4] |
| Circuit ORAM | Optimizes circuit work; table 1 gives O((D+log² n)log n)·ω(1) gates at negligible-in-n failure, D block bits | Linear encrypted tree + stash; recursive map as configured | Useful for MPC/oblivious client computation, not a zero-cost wrapper around plaintext leaves. Do not quote bandwidth as proving CPU flatness. [C] |
| Ring ORAM | O(log n) amortized total bandwidth; XOR-assisted **online** bandwidth can be O(1) | Linear encrypted storage, map/stash and dummy slots | Includes scheduled eviction/reshuffling; “constant online” excludes maintenance. Does not supply selective-opening proofs. [R] |
| DetWoORAM | Under its B=Ω(log² n) uniform-block assumptions: 2 block writes, O(log n) physical reads per logical write | Linear backing store, O(B) unsynchronized client memory, no stash | Hides write snapshots, **not observed reads**; useful for encrypted published storage. Logical-address openings still need separate handling. [W, table 1] |
| Pedersen / homomorphic vector commitment | C′=C·g_i^Δ·h^ρ can update a fixed vector commitment in constant group operations | O(n) messages/generators; witnesses/preprocessing extra | Fresh ρ hides a standalone commitment; public Δ/i or reused openings may leak. Computing/updating arbitrary selective proofs is an additional cost. Discrete log/pairing or other chosen assumptions; not a drop-in Store codec. [T, §§12.3,14.3] |
| Accumulator | Some support constant group-operation insert/update; deletions and witnesses are scheme-specific | Linear data; compact accumulator, witness state may be linear | Membership ≠ authenticated map position/value/absence/completeness; public update elements leak. Add hiding and ZK and re-evaluate **all** witness maintenance. No blanket O(log n) claim. [V; U, related work] |
| Vector commitments / updatable ZK databases | Scheme-dependent setup, update and witness costs; compact proofs alone do not bound prover work | Public parameters/witnesses may scale with n | Genuine candidates, not ruled out by the flat-format lower bound. Evaluate the update transcript and selective-opening game, not just position binding. [V] |
| Liskov transparently updatable ZK database | Security-depth k path work; appendix F gives O(k²) per individual update/proof update; initialization depends on n | Private database/tree and proof/update state | **Pattern pseudonyms leak equality of update targets.** Opaque refresh-style queries are closer to our goal. VRF + mercurial commitments + ROM; not our full change-pattern property. [L, §§3.2,5–6, app. F] |
| Epoch sweep / log-sized refresh frontier | O(log n) refreshing each turn, or Θ(n)/epoch with amortization | O(n) + queued generations | Intermediate snapshots identify unswept changed entries. Batch boundaries reveal net changes unless all exposed tokens are refreshed. A batch of n/log n turns buys amortized work only with that latency and no intermediate views. §7. |

Pedersen algebra is useful for the outer commitment too: `C=g^m h^r` with uniform
r is perfectly hiding; rerandomization is cheap [T]. It would remove the masking
oracle-guess term from (H), but introduces a group commitment relation, scalar
encoding/binding obligations, and non-post-quantum binding for the usual discrete
log instantiation. The hash wrapper keeps the existing hash-oriented boundary;
this is an engineering choice, not a claim that homomorphic hiding is impossible.

Liskov's result is particularly instructive: its simulator explicitly receives
the pattern pseudonym N_P(x) on each update; the definition preserves target
repetition. That is weaker than hiding `[write i, write i]` versus
`[write i, write j]` for never-opened i,j. The 2020 UC updatable-database paper
uses **non-hiding** vector commitments for a different updater/reader task [U].
Neither title alone discharges Mini's game. A later search hit, *Concise UC
Zero-Knowledge Proofs for Oblivious Updatable Databases* (2021,
DOI `10.1109/CSF51468.2021.00008`), merits a future implementation comparison;
its full text was not available through the attempted endpoints, so no complexity
or security claim here relies on it.

## 6. What an ORAM alternative would actually prove

For Path ORAM, an access reads and rewrites the **old assigned path**, reassigns
the logical block a fresh secret leaf label, and encrypts every real/dummy block
written back. It does not publish the real target and add random cover paths.
A private position map, padded buckets and stash are essential. With semantic
security, encrypted paths can be replaced by encryptions of zero; revealed path
labels are then independent uniform samples. Full encrypted snapshots are
post-processing of initialization and this transcript, so the same reduction
covers them. It does not cover plaintext logical labels attached to ciphertexts
or keys handed to a reader [P, §§2–3.6].

At bucket size 5 the journal version's Theorem 5.1 bounds overflow after any
fixed access sequence by `14·0.6^R`, R stash blocks. Across T accesses, union bound
`δ_over ≤ 14T·0.6^R`. Thus a conservative two-world bound is

```
Adv_ORAM ≤ 2 ε_enc^multi(q_enc,τ') + 28 T·0.6^R,
```

with a further map-PRF term if labels are pseudorandom rather than uniform.
The path simulator/overflow bound must apply to the permitted adaptive workload;
[P, §2] discusses this adaptation. For T≤2^40 and desired overflow contribution
≤2^-128, choose R≥235 by this conservative inequality. This is **not** a claim of
235-block constant-time stash handling or a full 128-bit encryption bound.
Recursion adds its own accesses/failure terms. Integrity uses authenticated
storage and current-root checks; encryption alone does not provide it.

A host with private RAM can index the map directly; a proof circuit or adversary
observing that RAM cannot. A narrowed reader who learns an accessed block's
physical location/current assigned leaf can distinguish a future access to it.
Therefore selective openings must hide these locators, for example through ZK
logical membership proofs. Giving ordinary ORAM ciphertexts one-for-one as
`StoreHiding.Item`s is not a safe composition. If the operator/storage observer
becomes part of scope, the private Merkle design must be replaced or its storage
accesses protected; it cannot silently inherit the ORAM guarantee.

## 7. Precisely what cheaper refresh schemes leak

**Per-entry epochs.** Keep a private master salt key K and monotone generation e_i
per logical key; on *every write to i* set a fresh generation, including writes
that restore an old value. Commit
`H(domain, F_K(cellId,i,e_i), encode(i,value))` in a persistent tree. Re-creation
after deletion must not reset the generation; otherwise equality can reappear.
Publishing epoch numbers would additionally reveal exact write counts, so keep
them private. Fresh randomness per entry version can replace counters.

In aligned full snapshots, the unchanged hidden tokens are equal and changed
ones differ except for collisions. The observer learns the exact change set at
its snapshot sampling resolution, stable-slot lifetimes/frequencies and overlap
between writes; previous openings can label those slots. Insertions/deletions,
order and count also leak. Fresh epochs hide return-to-old-value equality and
content dictionary tests absent a salt/key compromise. They do **not** hide that
the same entry was written twice. With only sparse Merkle paths exposed, the
leak is coarser subtree/path change information, not necessarily the full key set.
A correct theorem is hiding **conditioned on this enlarged leakage**; it cannot
claim a small epsilon for arbitrary hidden target choices.

A one-step counterexample: initially hidden i and j have known distinct tokens.
World 0 changes i; world 1 changes j. Test whether i's old token survives. The
distinguishing gap is 1 minus the collision/coincidence probability. This is not
an epsilon that falls as λ grows; it approaches 1.

**Random decoys/frontiers.** Suppose every update visibly rewrites the true slot
and d uniform distinct decoys among n−1 other slots. For worlds “write i” and
“write j,” the test `i is in the rewritten set` has probabilities 1 and d/(n−1).
The gap is `1−d/(n−1)`. O(log n) decoys are almost maximally distinguishable in
this model. A deterministic refresh frontier has the same problem outside that
frontier. This is our direct calculation, not an ORAM lower bound.

An epoch of B writes followed by a full re-salt costs Θ(n/B) refresh work per
write on average, but answers during the epoch leak the change sets. Suppressing
intermediate publications changes latency/semantics; B=Ω(n/log n) is needed to
amortize this sweep to O(log n), so delay grows with accumulated state. Hierarchical
mixing and encrypted relocation can fix access leakage, but then the design is
an oblivious storage construction with its own proof, not a free frontier trick.
For the old independent-salt flat format, emitting n fresh leaves already costs
Ω(n); that is a format-specific lower bound, not a universal impossibility.

## 8. What transfers from breadstuffs

Read against breadstuffs `22fad151e9f118e3aa001a823e075918ffa139e8`:

* `.docs-history-noclaude/private-information-retrieval.md` §4 correctly separates
  private position-map state and ORAM-in-proof cost. Its narrative says
  O(log N)-sized buckets then counts five-block buckets, and says a path is written
  to a new random path. Use [P]'s constant buckets and old-path writeback instead.
  Its full-map O(N) permutation check is a proposed proof encoding, not an ORAM
  lower bound; authenticate only changed map paths when the invariant permits it.
* `.docs-history-noclaude/federation-privacy.md` §“What the Bloom Filter Leaks” and
  `old-docs/design-encrypted-intents.md` §1 / phase 1 identify linkage/frequency
  from stable tokens. Epoch rotation limits the interval, not the leakage inside
  it. That is the same issue as a stable hidden Store leaf.
* `.docs-history-noclaude/fast-path-design.md` §§6.4–6.5 separates validator privacy
  and conflict-set disclosure. Same lesson here: hiding a root cannot hide an
  independently published command fingerprint or touched-cell list.
* `.docs-history-noclaude/garbled-circuits.md` §8.1 concerns reuse of garblings;
  fresh proof randomness matters, but its approximate “100×” RAM overhead is not
  a cost theorem and is not reused here.
* `.docs-history-noclaude/rebuild/dregg2-design/DREGG4-CRYPTO-MENU.md` §1.12 locates
  ORAM below the ISA as the access-pattern complement to content encryption.
  That separation fits a stronger physical observer, not a semantic Rust wrapper.

The two latter requested paths were found in the historical directories above,
not at `breadstuffs/rebuild/...` or the top historical directory respectively.

## 9. Review and integration work

`Kernel/BlindedCellHiding.lean` is a **statement-only draft**, intentionally not
imported by an umbrella or target. It defines a finite-tape probability gap,
whole-transcript/adaptive-strategy obligations, the hybrid budget, complete
opening and receiving-realization obligations, and per-operation cost statements.
Its comments give satisfiable, teeth and premise-inhabitation sketches. Static
module-format and whitespace checks passed, and exact rational arithmetic checks
confirmed (H), the masking example, the decoy gap and R=235 stash calculation. No
cryptographic premise is an axiom/instance; no theorem pretends the live wire
satisfies the new protocol. Toy witnesses are explicitly separate from a binding
implementation.

Implementation obligations, recorded here as the tracker for this research:

1. Introduce the persistent authenticated representation with a proved logical
   projection, maintained balance/index invariants and local update relation.
   Version the materializer/root semantics, migration and patch journal together.
2. Implement the mask custody/atomic retry choice and retained historical roots;
   replace **all** flat-view producers, at-height views, cache rendering and
   `NativeThinConsent.checkOpened` with the new complete-proof protocol. Remove
   the old-format path for this version; do not leave two privacy claims selected
   by a client flag.
3. Compile the projection relation and choose/instantiate the ZK backend with
   explicit multi-theorem ZK and knowledge-soundness/extraction reductions and
   measured constants.
   Test omission, wrong range/scope/root/version, reused mask label, old opening
   after revocation, A→B→A hidden writes, and lost-reply exact retry.
4. Join the persistent-state work: incremental laws/projection/certificates,
   bounded append queries, changed-page journal/checkpoints and suffix recovery.
   Prove cost for the actual receiving path, including proofs, not just root math.
5. Parent integration on `dregg-build`: compile the statement draft separately
   if desired; later build the implemented receiver and run tour/composed plus
   submit/propose/GET flatness on the same candidate. This research did not run
   them and does not claim a performance fix.

## Sources and retrieval

Source-code references above are pinned to this note's Mini tip; code takes
precedence over status prose. The new construction, hybrid calculation and
counterexamples are this note's derivations. External sources used:

* **[P]** Stefanov et al., *Path ORAM: An Extremely Simple Oblivious RAM Protocol*,
  JACM 65(4), 2018, §§2–6, Theorem 5.1.
  [Author PDF](https://elaineshi.com/docs/pathoram.pdf),
  [DOI](https://doi.org/10.1145/3177872). Read the PDF text; use the theorem's
  `0.6^R`, not the introductory extraction's erroneous negative exponent.
* **[C]** Wang, Chan, Shi, *Circuit ORAM: On Tightness of the Goldreich–Ostrovsky
  Lower Bound*, CCS 2015, table 1 and construction.
  [DOI](https://doi.org/10.1145/2810103.2813634),
  [ePrint](https://eprint.iacr.org/2014/672). Full text via Scry
  `academic.papers`, paper_key `10.1145/2810103.2813634`, quality `good`.
* **[R]** Ren et al., *Constants Count: Practical Improvements to Oblivious RAM*,
  USENIX Security 2015, table 1 and §§3–5.
  [Paper](https://www.usenix.org/system/files/conference/usenixsecurity15/sec15-paper-ren-ling.pdf).
* **[W]** Roche, Aviv, Choi, Mayberry, *Deterministic, Stash-Free Write-Only ORAM*,
  CCS 2017, §§1–3 and table 1.
  [DOI](https://doi.org/10.1145/3133956.3134051). Full text via Scry
  `academic.papers`, paper_key `10.1145/3133956.3134051`, quality `good`.
* **[Z]** Giacomelli, Madsen, Orlandi, *ZKBoo: Faster Zero-Knowledge for Boolean
  Circuits*, USENIX Security 2016, §§2,4.1–4.2,5.2 (Propositions 4.1–4.2).
  [Paper](https://www.usenix.org/system/files/conference/usenixsecurity16/sec16_paper_giacomelli.pdf).
  Used for linear circuit cost and the need for an explicit ROM/FS transformation,
  not a measured Mini prover or a concrete multi-theorem budget.
* **[T]** Justin Thaler, *Proofs, Arguments, and Zero-Knowledge*, §§12.3,13.1,14.3.
  Local `/Users/ember/paperbin/book.txt` (Pedersen and linear commit-and-prove
  sections read); [author's book](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.html).
* **[V]** Catalano, Fiore, *Vector Commitments and Their Applications*, PKC 2013.
  [Author abstract / ePrint](https://eprint.iacr.org/2011/495),
  [DOI](https://doi.org/10.1007/978-3-642-36362-7_5).
  Abstract checked; full-text endpoints failed. Used only for the primitive's
  position-binding definition and named applications, not a cost/security bound.
* **[L]** Moses Liskov, *Updatable Zero-Knowledge Databases*, ASIACRYPT 2005,
  §§3.1–3.2,5–6, appendices C,F.
  [DOI](https://doi.org/10.1007/11593447_10). Full text via Scry
  `academic.papers`, paper_key `10.1007/11593447_10`, quality `good`;
  in particular the **pattern pseudonym** is explicit permitted leakage.
* **[U]** Damodaran, Rial, *UC Updatable Databases and Applications*, AFRICACRYPT
  2020, construction and related work.
  [Full text](https://pmc.ncbi.nlm.nih.gov/articles/PMC7334996/).
  Its non-hiding VC/reader-proof setting is distinguished from this note's task.

Discovery used five successful bounded Kagi queries and read-only Scry
schema/title/full-text queries on 2026-10-30; returned Scry reads were complete, untruncated, free under
slack. Zero full-text rows for other requested keys are retrieval gaps, not
nonexistence claims. Exact responses and extracted working texts remain in
`target/ratchet-research/scratch/` (uncommitted); no credentials are copied there.
The paperbin `.txt` search also located Viaduct and FHE/PIR references; no claim
above relies on their incidental ORAM mentions. No copied personal profile or
recipient-specific correspondence belongs in the commit.
