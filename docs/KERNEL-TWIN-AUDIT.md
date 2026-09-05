# KERNEL-TWIN-AUDIT — twins and sprawl in the kernel layer

*Read-only audit, 2026-09-04. Method: full read of `ATLAS.md`; full read of the (A) files
(`Kernel/State.lean`, `Verbs.lean`, `Gate.lean`, `Receipt.lean`, `Turn.lean`) and of
`Kernel/MultiCellHyperedge.lean`, `Kernel/DeclaredHyperedge.lean`,
`Theory/CanonicalTransition.lean`, `Theory/DeclaredTurn.lean`, the three anti-vacuity witness
files, and targeted regions of every other file quoted below; the import graph was built with
`grep -rn "^import Kernel\.\|^import Theory\." --include='*.lean'` (387 edges). Headers of all
47 `Kernel/*.lean` were read for classification. No file under the tree was modified; no
`lake build` was run. Every theorem statement below is quoted verbatim with an absolute path and
line numbers; where I did not read the Lean, the claim is marked UNVERIFIED.*

Counts at the audit snapshot: `Kernel/` 47 files / 23,802 lines · `Theory/` 61 files in the
umbrella / 26,075 lines · `Assurance/` 120 files / 54,689 lines · `Effects/` 436 · `Pred/` 450.
**Tonight's live wave landed files while this audit ran** (`Kernel/` is 49 files / 24,342 and
`Theory/` 65 files / 27,567 at the time of writing); see §10 — two of the new files change the
picture and are covered there. All other sections describe the snapshot.

---

## 0. Verdict

1. **(A) and (B) are twins, not layers.** (B) imports exactly one (A) file, `Kernel/Turn.lean`
   (the abstract `Hyperedge` structure). Nothing in (B) references `KernelState`, `UKey`,
   `umap`, `Act`, `TurnReq`, `gateOK`, `admit`, `totalAsset`, `move`, `create`, `gwrite`, or
   `uproj` (grep over every (B) file: zero hits except the sentence at
   `/Users/ember/dev/minidregg/Theory/CanonicalResourceKernel.lean:4`, which names (A) as "the
   original `KernelState`" and re-proves its conservation law over a new `Book`). Fail-closed,
   no-TOCTOU, conservation, frame, and receipt binding are each stated a second time over
   (B)'s carriers (§2 table).
2. **`Kernel/Gate.lean` (638 lines) has zero importers** besides the `Kernel.lean` umbrella, its
   `@[export minidregg_gate_ok]` has no caller in `prover/` or `native/`, and the
   `[ADMISSION-kernel-bridge]` that was to identify it with `Compiler/AdmissionAir` was never
   started (AdmissionAir imports only `Compiler.NoteSpend`). `Kernel/Camera.lean` (637 lines) is
   imported by `State.lean` but no identifier from it is used anywhere (only two doc-comments).
3. **None of Gate.lean's residuals were closed by (B).** `[GATE-hyperedge]` is re-expressed
   (three joint gates over `CellState`), not connected; `[N-TURN-a]`/`[N-TURN-b]` have no
   `StepComplete`/`sound_needs_binding` anywhere in Lean. `toHyperedge` exists three times;
   the only consumer stores it as a structure field (`Assurance/GrainForkSettlement.lean:333-335,
   445-459`); no theorem from `Turn.lean` (`legs_agree`, `binary_balanced`, N2a/N2b) is ever
   applied to a (B) hyperedge. The bridge is decorative.
4. **(B) contains its own internal twin pair**: `Kernel/DeclaredHyperedge.lean` is self-labelled
   "the legacy integer-field, empty-resource schema" / "a migration surface, not the canonical
   runtime" (`TypedCellHyperedge.lean:5-6`, `DeclaredHyperedgeWitness.lean:3-4`), yet it is the
   ONLY hyperedge carrier `Compiler/` consumes (`Compiler/DeclaredHyperedgeArtifact.lean:15`).
   `TypedCellHyperedge`/`MultiCellHyperedge` — the D-0002 "semantic kernel" — are consumed by
   no `Compiler/` or `Effects/` file.
5. **10,393 of Kernel's 23,802 lines are application code** by ATLAS's own carve (escrow market,
   provider lease, quota GC, hyperdocument editing/merging, policy registry, credential
   envelope, resource charge); a further 5,856 are durable-device and distributed-finality
   models that ATLAS put in `Distributed/`. The ATLAS kernel-primitive + necessity content is
   2,823 lines on the (A) side and 4,730 on the (B) side.
6. **`Assurance/` is hand-written Lean, not generated.** All eight sampled files are
   hand-authored (one is a 1,430-line hand-maintained re-export manifest, two are application
   modules). No script in `scripts/` writes into `Assurance/`; `scripts/CarrierCensus.lean` is a
   read-only query. `Assurance/Placeholder.lean` still says "No hand-maintained ledger anywhere."
7. **Vacuity spot-check (6 headlines):** 2 have both poles built at closed data
   (CanonicalTransition delta laws; Hyperdocument merge), 3 have the satisfiable pole only
   (MultiCell `no_commit_of_nonzero_balance`; DurableCommitProtocol on its stale-root/nullifier
   legs; ReplicatedSettlementFinality), and 1 has neither pole at data
   (`DeclaredTurn.execute_committed_sound` — no `DeclaredTurn.Declaration` is ever constructed).
8. **Layering inversion:** three `Kernel/` files import `Compiler.*`
   (`CanonicalPolicyRegistry`, `CredentialSignedEnvelopeController`, `DeclaredActionExecution`)
   while nine `Compiler/` files import `Kernel.*`. `scripts/check-import-boundary.sh` checks only
   `Theory`/`Selvage`, so nothing catches this.
9. **Proposed collapse (§8):** (B) survives as the semantic kernel (D-0002 already says so; the
   tree's mass and the Compiler welds agree); (A) is folded in, not deleted wholesale — Gate and
   Camera can go now (−1,275 lines, zero consumers), State/Verbs/Receipt/PrivateTurn only after
   `Effects/EffectSpec.moveEffect` and `Assurance/ReceiptClaim` are re-pointed (a real (B)-side
   faithfulness theorem is missing). Kernel/ lands at ≈3.6K lines after apps and durable/
   distributed models move out — inside the ATLAS 5-10K budget.
10. **The ATLAS `Theory/` carve was mostly never built.** At the snapshot, of its listed
    contents only the verify/find seam existed (`Theory/Knowledge.lean`, 100 lines);
    `GovernedDynamics`, `AmpClosed`, `nuF` appear nowhere in Lean, and `Frame/Knows/DistKnows`
    arrived only at 23:51 tonight as `Theory/EpistemicConsensus.lean` (§10). The other 26K
    lines of `Theory/` are the (B) kernel model (13.2K), the Hyperdocument application (4.9K),
    proof-system algebra (6.0K), and zkML/EVM domain work (1.9K).
11. **The twin is growing in both directions tonight.** `Kernel/HyperedgeTier.lean` (23:50)
    imports `Kernel.State` and `Kernel.Turn` and proves new theorems over `KernelState`
    (`conservedAtTier`, `mint_breaks_at_every_tier`) — new (A)-side mass, landed 26 days after
    D-0002 declared (B) the semantic kernel. Whoever adjudicates the collapse should do so
    before wave 2 (§10).

---

## 1. The import graph

### 1.1 (A) files: what imports them

| (A) file | lines | importers (all libs; umbrella `Kernel.lean` excluded) |
|---|---|---|
| `Kernel/Camera.lean` | 637 | `Kernel/State.lean` (import only — no identifier used; see §5) |
| `Kernel/State.lean` | 258 | `Effects/EffectSpec.lean`, `Kernel/Receipt.lean` |
| `Kernel/Receipt.lean` | 130 | `Assurance/ReceiptClaim.lean`, `Kernel/Verbs.lean` |
| `Kernel/Verbs.lean` | 304 | `Assurance/SelvageV0Manifest.lean`, `Kernel/Gate.lean` |
| `Kernel/Gate.lean` | 638 | **none** |
| `Kernel/Turn.lean` | 120 | `Kernel/DeclaredHyperedge.lean`, `Kernel/MultiCellHyperedge.lean`, `Kernel/PrivateTurn.lean`, `Kernel/TurnLimit.lean` |
| `Kernel/TurnLimit.lean` | 172 | `Kernel/TurnBalancedLimit.lean` |
| `Kernel/TurnBalancedLimit.lean` | 277 | `Assurance/SelvageV0Manifest.lean` |
| `Kernel/PrivateTurn.lean` | 287 | `Assurance/SelvageV0Manifest.lean` (`Assurance/PrivateTurn.lean` does NOT import it; it imports only `Assurance.PrivateReceipt`) |

### 1.2 (B) core files: what imports them

| (B) file | lines | importers outside `Kernel/` | importers inside `Kernel/` |
|---|---|---|---|
| `Theory/CellState.lean` | 474 | — | `SparseAuthenticatedState` (plus 20+ Theory files) |
| `Theory/TypedAuthorization.lean` | 585 | `Assurance/SemanticTurnReceipt`, `Compiler/CanonicalPolicyAdmission`, `Compiler/TypedAuthorizationRequestCodec` | `SparseAuthenticatedState` |
| `Theory/EffectDeclaration.lean` | 416 | `Compiler/DeclaredEffectArtifact` | — |
| `Theory/AcceptedCellEffect.lean` | 792 | 5 Assurance files | `MultiCellHyperedge`, `TypedCellHyperedge` |
| `Theory/CanonicalTransition.lean` | 424 | — | `DeclaredHyperedge` |
| `Theory/DeclaredTurn.lean` | 411 | `Assurance/DeclaredTurnReceipt` | — (via Theory) |
| `Theory/TurnTransition.lean` | 404 | **none** (only `Theory.lean`) | — |
| `Kernel/DeclaredHyperedge.lean` | 760 | `Assurance/DeclaredHyperedgeReceipt`, `Compiler/DeclaredHyperedgeArtifact` | `DeclaredHyperedgeCost`, `TypedCellHyperedge` |
| `Kernel/TypedCellHyperedge.lean` | 561 | `Assurance/GrainForkSettlement`, `Assurance/ReactiveLifecycleHistory` | `CanonicalResourceEffect`, `DeclaredHyperedgeWitness`, `DurableCommitProtocol`, `TypedCellHyperedgeWitness` |
| `Kernel/MultiCellHyperedge.lean` | 447 | **none** | `CanonicalResourceEffect`, `DurableCommitProtocol`, `HyperdocumentMergePublication`, `HyperdocumentPublication`, `MultiCellHyperedgeWitness` |
| `Kernel/DeclaredActionExecution.lean` | 468 | **none** | **none** |

### 1.3 What (B) imports from (A)

Exactly `Kernel.Turn` — from `Kernel/DeclaredHyperedge.lean:17` and
`Kernel/MultiCellHyperedge.lean:20` (and `TypedCellHyperedge` transitively). No (B) file imports
`Kernel.State`, `Kernel.Verbs`, `Kernel.Gate`, `Kernel.Receipt`, or `Kernel.Camera`.
`docs/decisions/D-0002-canonical-hyperedge-kernel.md` lists `Kernel/Turn.lean` and
`Kernel/TurnBalancedLimit.lean` as "source anchors" and omits State/Verbs/Gate/Receipt/Camera.

### 1.4 Layering inversion

`Kernel/` → `Compiler/`: `Kernel/CanonicalPolicyRegistry.lean:26` (`import
Compiler.CanonicalPolicyAdmission`), `Kernel/CredentialSignedEnvelopeController.lean:20`
(`import Compiler.Tower256ConcreteBackend`), `Kernel/DeclaredActionExecution.lean:15` (`import
Compiler.DeclaredActionBytes`). `Compiler/` → `Kernel/`: nine files
(`CredentialAuthorityPolicyRegistry`, `DeclaredEffectPageMaterializer`,
`DeclaredHyperedgeArtifact`, `DeployedCellRegistry`, `FiniteSparseMaterializerAudit`,
`FramedWalRecoveryController`, `HyperdocumentIndexPageMaterializer`,
`HyperdocumentEventPageMaterializer`, `SparseAuthenticatedStateLogupBridge`). Module-level the
graph is acyclic (it builds), but the ATLAS carve has Kernel upstream of Compiler.
`scripts/check-import-boundary.sh` guards only `Theory` and `Selvage`.

---

## 2. Q1 — twins, layers, or refinement?

**Answer: twins with one shared abstract object.** (B) reuses `Kernel/Turn.lean`'s `Hyperedge`
structure and nothing else; every gate/conservation/frame/receipt property of (A) is
re-stated over (B)'s state (`CellState.Materialized` / `EffectDeclaration.Store` /
`CanonicalResourceKernel.Book`) rather than derived from, refined from, or instantiated at
`KernelState`. (B) is not a refinement of (A): there is no simulation relation, adapter, or
theorem in the tree relating `KernelState` to any (B) carrier (grep for `KernelState` outside
the five (A) files finds only `Effects/EffectSpec.lean`, `Assurance/{SelvageV0Manifest,
ReceiptClaim,SelvageV0,PrivateReceipt}.lean`, `Compiler/AdmissionAir.lean:693` (a doc-comment),
`Compiler/Signature.lean:300` and `Pred/Core.lean:17` (both doc-comments about breadstuffs'
`RecordKernelState`), and `Theory/CanonicalResourceKernel.lean:4` (doc-comment)).

The shared object, verbatim (`/Users/ember/dev/minidregg/Kernel/Turn.lean:38-55`):

```lean
structure Hyperedge
    (ι : Type v) [Fintype ι]
    (Carrier : Type uCarrier) (Turn : Type uTurn)
    (TurnId : Type uTurnId) (Bal : Type uBal)
    [AddCommMonoid Bal] [DecidableEq TurnId]
    (step : Carrier → Turn → Carrier)
    (turnId : ι → Carrier → TurnId)
    (halfEdge : ι → Carrier → Turn → Bal) where
  x : ι → Carrier
  t : Turn
  tid : TurnId
  agree : ∀ i, turnId i (step (x i) t) = tid
  balanced : (Finset.univ.sum fun i => halfEdge i (x i) t) = 0
```

### 2.1 Counterpart theorems — same property, different state type

**Fail-closed.**

(A) `/Users/ember/dev/minidregg/Kernel/Gate.lean:341-343`
```lean
theorem admit_fail_closed [Theory.Verifiable CellId W] {k : KernelState} {t : TurnReq W}
    (fp : Footprint) (h : gateOK k t = false) : admit k (gatedVerb fp) t = none :=
```
with `Kernel/Gate.lean:233-234`
```lean
def gateOK [Theory.Verifiable CellId W] (k : KernelState) (t : TurnReq W) : Bool :=
  credOK t && capOK k t && cavOK t && revOK k t
```
and `Kernel/Gate.lean:313-316`
```lean
def admit (k : KernelState) (v : Verb W) (t : TurnReq W) : Option KernelState :=
  if v.admission k t && t.act.wf k && t.act.touched.within v.footprint
  then some (t.act.apply k)
  else none
```

(B) `/Users/ember/dev/minidregg/Kernel/DeclaredHyperedge.lean:499-514` (the joint gate)
```lean
def execute
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence) :
    Outcome declaration :=
  if declaration.shapeCheck then
    if declaration.authorizationCheck projection then
      if declaration.balanceCheck then
        if declaration.guardsCheck then
          let postStore := applyPatch declaration.patch declaration.preStore
          let post := materialize materializer (declaration.logicalOfStore postStore)
          if post.root = declaration.apex then .committed postStore
          else .rejected .apex
        else .rejected .guard
      else .rejected .aggregateBalance
    else .rejected .authorization
  else .rejected .shape
```
`/Users/ember/dev/minidregg/Kernel/DeclaredHyperedge.lean:529-536`
```lean
theorem execute_rejected_unchanged
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    (reason : RejectReason)
    (rejected : execute projection declaration = .rejected reason) :
    (execute projection declaration).materialized = declaration.pre := by
```
`/Users/ember/dev/minidregg/Kernel/MultiCellHyperedge.lean:343-355` and `369-375`
```lean
def admit
    {boundary : HandlerBoundary.{u, v, w, x, y, z, h} declaration}
    {Reject : Type h}
    (validateLegs : Except Reject declaration.AcceptedLegs)
    (validateJoint : (accepted : declaration.AcceptedLegs) ->
      Except Reject (Commit law accepted boundary)) :
    Admission law boundary Reject :=
  match validateLegs with
  | .error reason => .rejected reason
  | .ok accepted =>
      match validateJoint accepted with
      | .error reason => .rejected reason
      | .ok commit => .committed accepted commit
```
```lean
@[simp] theorem Admission.rejected_atomic
    {boundary : HandlerBoundary.{u, v, w, x, y, z, h} declaration}
    {Reject : Type h} (reason : Reject) (incidence : Incidence) :
    Admission.logicalPost (law := law)
      (Admission.rejected (law := law) (boundary := boundary) reason)
      incidence = declaration.pre incidence :=
```
Shape note: (A) states "gate predicate false ⇒ deny" (plus four per-leg denials at
`Gate.lean:346-365`). (B) states "rejected ⇒ post = pre" (rejection atomicity). The only (B)
theorem of the (A) shape *check false ⇒ execute rejects* is the balance leg,
`DeclaredHyperedge.lean:738-750` (quoted under Conservation). Per-leg denials in (B) exist at
built data only (`Kernel/DeclaredHyperedgeWitness.lean:290-291, 304-305`). I did not find, and
do not claim the absence of, a general per-leg denial theorem for the authorization/shape/guard
legs in (B).

**No-TOCTOU (check-equals-use).**

(A) `/Users/ember/dev/minidregg/Kernel/Gate.lean:382-384`
```lean
theorem admit_check_eq_use [Theory.Verifiable CellId W] {k k' : KernelState}
    {fp : Footprint} {t : TurnReq W} (h : admit k (gatedVerb fp) t = some k') :
    gateOK k t = true ∧ k' = t.act.apply k :=
```

(B) `/Users/ember/dev/minidregg/Kernel/DeclaredHyperedge.lean:690-695`
```lean
theorem execute_committed_hyperedge_sound
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    (postStore : Store)
    (committed : execute projection declaration = .committed postStore) :
    Nonempty (CommittedHyperedge projection declaration postStore) := by
```
where `CommittedHyperedge` (`Kernel/DeclaredHyperedge.lean:568-581`) carries
`authorizations : forall incidence, Nonempty (Authorized portal (declaration.authState projection) (declaration.legs incidence).request)`
and `evaluated : applyPatch declaration.patch declaration.preStore = postStore`, and the
same-pre-state binding is `Kernel/DeclaredHyperedge.lean:166-169`
```lean
@[simp] theorem Declaration.authState_same_pre
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence) :
    declaration.authState projection = projection.project declaration.pre.logical := rfl
```
Single-cell form: `/Users/ember/dev/minidregg/Theory/DeclaredTurn.lean:251-257`
```lean
theorem execute_committed_sound {portal : Portal} (state : AuthState)
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Declaration portal materializer kind)
    (postStore : EffectDeclaration.Store)
    (committed : execute state declaration = .committed postStore) :
    Nonempty (Commit (state := state) declaration postStore) := by
```

**Conservation.**

(A) `/Users/ember/dev/minidregg/Kernel/State.lean:176-178` and `197-199`
```lean
theorem move_conserves (k : KernelState) (src dst : CellId) (a : AssetId) (δ : ℤ)
    (hsrc : src ∈ k.accounts) (hdst : dst ∈ k.accounts) :
    totalAsset (move k src dst a δ) a = totalAsset k a := by
```
```lean
theorem mint_breaks_conservation (k : KernelState) (dst : CellId) (a : AssetId) (δ : ℤ)
    (hdst : dst ∈ k.accounts) (hδ : δ ≠ 0) :
    totalAsset (mint k dst a δ) a ≠ totalAsset k a := by
```
and at the gate, `/Users/ember/dev/minidregg/Kernel/Gate.lean:406-409`
```lean
theorem admit_conserves {k k' : KernelState} {v : Verb W} {t : TurnReq W}
    (a : AssetId) (h : admit k v t = some k')
    (hcreate : ∀ c, t.act = Act.create c → k.bal c a = 0) :
    totalAsset k' a = totalAsset k a := by
```

(B) `/Users/ember/dev/minidregg/Theory/CanonicalResourceKernel.lean:185-190` and `434-438`
```lean
theorem Operation.apply_conserves
    (operation : Operation) (book : Book)
    (sourcePresent : operation.posting.source ∈ book.accounts)
    (destinationPresent : operation.posting.destination ∈ book.accounts)
    (asset : AssetId) :
    (operation.apply book).totalAsset asset = book.totalAsset asset := by
```
```lean
theorem Book.creditOnly_breaks_conservation
    (book : Book) (destination : AccountId) (asset : AssetId) (amount : Nat)
    (destinationPresent : destination ∈ book.accounts) (positive : 0 < amount) :
    (book.creditOnly destination asset amount).totalAsset asset ≠
      book.totalAsset asset := by
```
The file's own header, `Theory/CanonicalResourceKernel.lean:4-5`: "The original `KernelState`
proves the right conservation equation, but its ledger is a fixed field of an early monolithic
state." — (B) knew (A) existed and landed beside it.
At the joint level, `/Users/ember/dev/minidregg/Kernel/MultiCellHyperedge.lean:415-420`
```lean
theorem no_commit_of_nonzero_balance
    {boundary : HandlerBoundary.{u, v, w, x, y, z, h} declaration}
    (coordinate : Coordinate)
    (nonzero : forall accepted : declaration.AcceptedLegs,
      aggregateDelta law accepted coordinate ≠ 0) :
    IsEmpty (AdmittedCommit law boundary) :=
```
and `/Users/ember/dev/minidregg/Kernel/DeclaredHyperedge.lean:738-750`
```lean
theorem execute_rejects_agreeing_nonzero_balance
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    (shapeAccepted : declaration.shapeCheck = true)
    (authorizationAccepted : declaration.authorizationCheck projection = true)
    (resource : Digest) (present : resource ∈ declaration.resources)
    (nonzero : declaration.aggregateDelta resource ≠ 0)
    (_agreement :
      (materialize materializer
        (declaration.logicalOfStore
          (applyPatch declaration.patch declaration.preStore))).root =
        declaration.apex) :
    execute projection declaration = .rejected .aggregateBalance := by
```

**Frame.**

(A) `/Users/ember/dev/minidregg/Kernel/Gate.lean:426-431`
```lean
theorem admit_footprint {k k' : KernelState} {v : Verb W} {t : TurnReq W}
    (h : admit k v t = some k') :
    (∀ c : CellId, c ∉ v.footprint.cells →
        (∀ a : AssetId, k'.bal c a = k.bal c a) ∧ (c ∈ k'.accounts ↔ c ∈ k.accounts))
    ∧ (∀ u : UKey, u ∉ v.footprint.keys → k'.umap u = k.umap u)
    ∧ k'.caps = k.caps := by
```
plus `Kernel/Verbs.lean:142-145` (`gwrite_umap_frame`) and `Kernel/Receipt.lean:83-87`
(`uproj_move_frame`).

(B) `/Users/ember/dev/minidregg/Theory/CellState.lean:372-377` and `398-403`
```lean
theorem ValidatedPatch.field_frame
    {S : Schema.{u, v, w, x}} {Root : Type y} [DecidableEq S.Field]
    [DecidableEq S.Resource] {M : Materializer S Root} {pre : Materialized M}
    {patch : Patch S Root} (validated : ValidatedPatch M pre patch)
    (field : S.Field) (outside : field ∉ patch.fieldFootprint) :
    validated.apply.logical.fields field = pre.logical.fields field := by
```
```lean
theorem ValidatedPatch.field_changed_only_declared
    {S : Schema.{u, v, w, x}} {Root : Type y} [DecidableEq S.Field]
    [DecidableEq S.Resource] {M : Materializer S Root} {pre : Materialized M}
    {patch : Patch S Root} (validated : ValidatedPatch M pre patch)
    (field : S.Field)
    (changed : validated.apply.logical.fields field ≠ pre.logical.fields field) :
    field ∈ patch.fieldFootprint := by
```
`/Users/ember/dev/minidregg/Theory/CanonicalTransition.lean:55-62`
```lean
theorem CellDelta.field_changed_only_declared
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root}
    {pre post : CellState.Materialized M} (delta : CellDelta pre post)
    (field : S.Field)
    (changed : post.logical.fields field ≠ pre.logical.fields field) :
    field ∈ delta.fieldFootprint := by
```
`/Users/ember/dev/minidregg/Theory/DeclaredTurn.lean:353-360`
```lean
theorem Commit.frame {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : EffectDeclaration.Store}
    (commit : Commit (state := state) declaration postStore)
    (key : EffectDeclaration.StateKey)
    (outside : key ∉ commit.footprint) :
    commit.post.logical.fields key = declaration.pre.logical.fields key := by
```
(Also `Theory/AcceptedCellEffect.lean:157-164` `field_frame`, `Theory/EffectDeclaration.lean:378`
`AuthorizedEffect.frame` — index only, statements not quoted here.)

**Receipt binding.**

(A) `/Users/ember/dev/minidregg/Kernel/Receipt.lean:59-62`
```lean
theorem uproj_faithful (w : Window) (k k' : KernelState) :
    uproj w k = uproj w k' ↔
      (∀ c ∈ w.cells, k.bal c.1 c.2 = k'.bal c.1 c.2)
      ∧ (∀ u ∈ w.keys, k.umap u = k'.umap u) := by
```
(consumed by `Assurance/ReceiptClaim.lean:81-86` `flatten_faithful`, the OB-3 kill-checkpoint.)

(B) has no theorem of the "word equality ↔ observed-state agreement" shape. Its binding is
"the root is a projection of the canonical post":
`/Users/ember/dev/minidregg/Theory/CanonicalTransition.lean:149-155`
```lean
@[simp] theorem PreparedTurn.postRoot_derived
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root} {pre : CellState.Materialized M}
    {Nullifier : Type z} (turn : PreparedTurn M pre Nullifier) :
    turn.postRoot = M.rootBytes (M.codec.encode turn.post.logical) :=
  rfl
```
`/Users/ember/dev/minidregg/Theory/CellState.lean:183-187`
```lean
theorem Materialized.root_encoding_coherent
    {S : Schema.{u, v, w, x}} {Root : Type y} {M : Materializer S Root}
    (cell : Materialized M) :
    cell.root = M.rootBytes cell.bytes :=
  rfl
```
and the receipt object `Theory/AcceptedCellEffect.lean:206-229` (`structure ReceiptEvent`, with
fields `preRoot postRoot : Digest`, `requestPreRootBound : request.preStateRoot = preRoot`),
projected by `AcceptedCellEffect.toReceiptEvent` (`232-256`, `postRoot := accepted.prepared.postRoot`);
`Kernel/DeclaredHyperedge.lean:591-602` `CommittedHyperedge.receipt : ReactiveReceipt.ReceiptDelta declaration.preStore postStore`.
Whether `M.rootBytes` is injective is nowhere assumed in (B) (D-0002: "Digest equality reflects
arguments only under an explicit binding/CR premise"). So receipt binding is split: (A) proves
faithfulness of an observation word; (B) proves root-derivation and carries CR as a premise.
`Assurance/ReceiptClaim` (928 lines) rides (A); `Assurance/GrainForkSettlement` builds receipt
claims on (B)'s `TypedCellHyperedge`.

### 2.2 The (B)-internal twin: three hyperedge carriers

| carrier | lines | self-description | consumed by |
|---|---|---|---|
| `Kernel/DeclaredHyperedge.lean` (+Cost 291, +Witness 604) | 760 | "the legacy integer-field, empty-resource schema" (`TypedCellHyperedge.lean:5-6`); "a migration surface, not the canonical runtime" (`DeclaredHyperedgeWitness.lean:3-4`) | `Compiler/DeclaredHyperedgeArtifact.lean:15`; `Compiler/DeclaredEffectPageMaterializer`, `Compiler/FiniteSparseMaterializerAudit` (via Witness); `Assurance/DeclaredHyperedgeReceipt` |
| `Kernel/TypedCellHyperedge.lean` (+Witness 126) | 561 | "the generic flat joint-transition nucleus" (line 4) | `Assurance/GrainForkSettlement`, `Assurance/ReactiveLifecycleHistory`; Kernel-internal |
| `Kernel/MultiCellHyperedge.lean` (+Witness 160) | 447 | "genuinely heterogeneous incidence-indexed cells" | Kernel-internal only |

`TypedCellHyperedge.lean:419-530` carries a `LegacyAdapter.Certificate` (11 proof fields) and
`committed_post_matches_legacy` / `committed_balance_matches_legacy` (`496-530`) — a migration
certificate whose target is the file `Compiler/` still consumes. This is the breadstuffs
pattern ("a `rfl` against a hand-written twin is evidence only while the twin exists; cashing it
means deleting the twin") reproduced inside (B).

Additionally `Kernel/SparseAuthenticatedState.lean:4-5` opens with "The old universal map
demonstrates that many side tables fit in one address space, but it fixes keys and payloads to
a handful of constructors and `Int`" — i.e. it is the (B) replacement of (A)'s
`umap : UKey → Option ℤ` (`Kernel/State.lean:129`), again landed beside it. And
`Theory/TurnTransition.lean` (404 lines, a `Mode := ordinary | resumed` sum over
`DeclaredTurn`/`ReactiveCellTransition`) is imported by nothing but `Theory.lean`; D-0002
"Alternatives rejected" names it ("Add private/reactive branches to `TurnTransition.Mode`").
Neither `DurableDataIntent.execute` (`Kernel/DurableDataIntent.lean:342-357`) calls
`DurableCommitProtocol.execute` (`Kernel/DurableCommitProtocol.lean:330-352`); it re-implements
the same `match` over `DataSnapshot` with a `.durable` reason wrapper.

---

## 3. Q2 — which of Gate.lean's residuals did (B) close?

`/Users/ember/dev/minidregg/Kernel/Gate.lean:57-60`, verbatim and unchanged since its single
commit (2026-08-08):
```
  [GATE-hyperedge] `admit` takes a single-incidence request — the `ι = 1`
     slice of `Kernel/Turn.lean`'s hyperedge. The N-party joint gate
     (per-incidence legs over the wide pullback, connecting to
     `[N-TURN-a]`'s `Admissible`) is the connection residual.
```

| residual | status | evidence |
|---|---|---|
| `[GATE-hyperedge]` | **re-expressed, not closed** | Three N-incidence joint gates exist in (B) (`DeclaredHyperedge.execute` 499-514, `MultiCellHyperedge.admit` 343-355, `TypedCellHyperedge.Commit`), none over `KernelState`, none mentioning `gateOK`/`admit`/`TurnReq`/`Act`. The "connection" the residual names (Gate's `admit` as the `ι = 1` slice of a joint gate) does not exist in either direction. |
| `[N-TURN-a]` `sound_needs_binding` / `[N-TURN-b]` `sound_bisim_ill_posed` (`Kernel/Turn.lean:110-117`) | **open** | `StepComplete`, `sound_needs_binding`, `sound_bisim_ill_posed` occur in no `.lean` file (only `ATLAS.md:124`, `docs/HYPEREDGE-DESIGN.md:87,91`, `docs/N2-HYPEREDGE-LIMIT.md:81,86`). `TypedAuthorization.Admissible` (`Theory/TypedAuthorization.lean:204`) is capability admissibility, not the joint-admissibility notion N-TURN-a needs. |
| `[ADMISSION-kernel-bridge]` (`Compiler/AdmissionAir.lean:92, 691`) | **open, never started** | `AdmissionAir.lean` imports only `Compiler.NoteSpend` (line 104); `Kernel.Gate` has zero importers; `GOAL.md:1132` (2026-08-08) promised the bridge "Assurance-side" and no Assurance file imports `Kernel.Gate`. The "AIR refines the kernel model" claim therefore has no Lean artifact on either side. |
| `[GATE-fpu]` (footprint as camera `Fpu`) | **open** | `Camera.Fpu` is referenced by no file outside `Camera.lean` (grep `Fpu\b`, `conservation_is_fpu`: only doc-comments in `State.lean:27,170` and `Gate.lean:27,61-62,296`). |
| `[GATE-grant]` (authority-producing verbs) | **realized on the (B) side only** | `Theory/CredentialAuthorityEffects.lean` (issuance, strict attenuation, revocation, epoch rotation as `AcceptedCellEffect` families — per `Theory.lean:47`; UNVERIFIED by reading that file). Nothing connects it to Gate's `caps`. |

**Is `toHyperedge` a genuine bridge?** There are three (`Kernel/DeclaredHyperedge.lean:649-654`,
`Kernel/TypedCellHyperedge.lean:383-384`, `Kernel/MultiCellHyperedge.lean:302-303`), each a
well-typed `Hyperedge` instance whose `agree`/`balanced` proofs are real (e.g.
`MultiCellHyperedge.lean:310-320` derives `balanced` from `commit.aggregateBalanced`). Consumers
tree-wide (grep `toHyperedge|SemanticHyperedge`): only
`/Users/ember/dev/minidregg/Assurance/GrainForkSettlement.lean:333-335`
```lean
def hyperedge (settlement : AcceptedSettlement (law := law) cut) :
    Minidregg.Kernel.TypedCellHyperedge.Commit.SemanticHyperedge
      settlement.commit :=
  settlement.commit.toHyperedge
```
which is then stored as a field `semanticHyperedge` with `semanticHyperedgeExact :
semanticHyperedge = settlement.hyperedge` (`GrainForkSettlement.lean:445-459`,
`GrainForkScopedSettlement.lean:294-308`). No file applies `Hyperedge.legs_agree`,
`Hyperedge.binary_balanced`, `.agree`, or `.balanced` to any (B) hyperedge (grep across
`Assurance/`, `Compiler/`, and the (B) Kernel files: zero hits; `legs_agree` is used only by
`Kernel/PrivateTurn.lean:216`, on the (A) side). N2a/N2b (`TurnLimit`, `TurnBalancedLimit`) are
proved about the abstract `Hyperedge` and are never instantiated at a (B) carrier; their only
consumer is the hand manifest. **Verdict: decorative** — a type-level "this is an instance"
certificate across which no theorem flows.

---

## 4. Q3 — what in `Kernel/` is app-shaped?

Classes: **P(A)** kernel-primitive, ATLAS model · **N** kernel-necessity · **P(B)**
kernel-primitive, D-0002 model · **D** durable/device/settlement model · **F**
distributed/finality/async delivery · **App** application. Classification is from each file's
own header (read for all 47) and its imports.

| file | lines | class | basis |
|---|---:|---|---|
| Camera | 637 | P(A) | resource algebra port (breadstuffs `Resource.lean`) |
| State | 258 | P(A) | `KernelState`, `move`/`mint`, conservation |
| Verbs | 304 | P(A) | `create`/`gwrite` |
| Receipt | 130 | P(A) | `uproj`, faithfulness |
| Gate | 638 | P(A) | 4-leg `gateOK`, `admit` |
| Turn | 120 | P(A) | `Hyperedge` |
| PrivateTurn | 287 | P(A) | `Hyperedge` at `Pub × Priv` |
| TurnLimit | 172 | N | N2a |
| TurnBalancedLimit | 277 | N | N2b |
| DeclaredHyperedge | 760 | P(B) | legacy joint carrier |
| DeclaredHyperedgeCost | 291 | P(B) | metering of the legacy carrier |
| DeclaredHyperedgeWitness | 604 | P(B) | witness + migration certificate |
| TypedCellHyperedge | 561 | P(B) | same-cell joint carrier |
| TypedCellHyperedgeWitness | 126 | P(B) | witness |
| MultiCellHyperedge | 447 | P(B) | heterogeneous joint carrier |
| MultiCellHyperedgeWitness | 160 | P(B) | witness |
| CanonicalResourceEffect | 590 | P(B) | resource book on the accepted-effect path |
| SparseAuthenticatedState | 723 | P(B) | typed sparse ROM/RAM substrate (replaces `umap`) |
| DeclaredActionExecution | 468 | P(B) | action-batch lowering (imports Compiler) |
| DurableCommitProtocol | 919 | D | CAS/nullifier/budget/history settlement model |
| DurableDataIntent | 588 | D | payload-bearing adapter |
| DurableWalHandler | 435 | D | WAL device model |
| FramedWalRefinement | 545 | D | framed/checksummed WAL |
| AdmissionPrologue | 644 | D | fee+nonce before body |
| IrreversibleEffectSettlement | 645 | D | external-action settlement |
| ReplicatedSettlementFinality | 513 | F | quorum safety |
| AuthenticatedSettlementFinality | 615 | F | signed votes/key epochs |
| ReactiveTerminalCell | 572 | F | promise terminal + outbox |
| OutboxDelivery | 380 | F | delivery/ack |
| HyperdocumentEventLog | 242 | App | hyperdocument |
| HyperdocumentIndexSync | 405 | App | hyperdocument |
| DeployedMaterializerWitness | 116 | App | hyperdocument event-log schema |
| HyperdocumentVersionEffects | 404 | App | hyperdocument |
| EventLogMaterializerLimit | 71 | App | hyperdocument regression tooth |
| HyperdocumentPublication | 351 | App | hyperdocument |
| HyperdocumentMerge | 949 | App | hyperdocument |
| HyperdocumentMergePublication | 652 | App | hyperdocument |
| HyperdocumentMergeAncestry | 327 | App | hyperdocument |
| HyperdocumentTwoParentWitness | 908 | App | hyperdocument |
| GuardedDurableCommit | 345 | App | hyperdocument-specialised durable commit (imports `HyperdocumentPublication`) |
| CanonicalPolicyRegistry | 425 | App | policy registry (imports Compiler) |
| CredentialSignedEnvelopeController | 425 | App | credential envelope (imports Compiler) |
| AuthorizedResourceCharge | 729 | App | ten-lane tariff charge |
| ProviderExecutionLease | 1211 | App | provider lease |
| CanonicalEscrowMarket | 1373 | App | escrow market |
| PrivateEscrowSettlement | 614 | App | private market order |
| QuotaGcSettlement | 846 | App | quota / GC |

**Sums:** P(A) 2,374 · N 449 · P(B) 4,730 · D 3,776 · F 2,080 · App 10,393 · **total 23,802**.
ATLAS budgeted Kernel/ at 5-10K and put App/D/F content in `Apps/`, `Deos/`, `Distributed/`
(none of which exist). Kernel-shaped content today is 7,553 lines across two models.

---

## 5. Q4 — load-bearing vs parallel tower

Importers outside `Kernel/` for every Kernel file (full raw list in Appendix A):

**Consumed by the derived path (`Compiler/` or `Effects/`) — 11 files:** State (Effects/EffectSpec),
DeclaredHyperedge, DeclaredHyperedgeWitness, DeployedMaterializerWitness, DurableDataIntent,
FramedWalRefinement, HyperdocumentEventLog, HyperdocumentIndexSync, HyperdocumentTwoParentWitness,
SparseAuthenticatedState, CanonicalPolicyRegistry. Note the (A) entry: `Effects/EffectSpec.lean:288-290`
```lean
def moveEffect : EffectSpec where
  Op := MoveArgs
  State := KernelState
  sem := fun m k => move k m.src m.dst m.asset m.δ
```
is the ONE effect in the ATLAS "open handler registry", and it is welded to (A). All ten (B)
entries are welded to the legacy carrier, the durable/WAL model, or the Hyperdocument app; none
to `TypedCellHyperedge`/`MultiCellHyperedge`.

**Consumed only by `Assurance/` — 19 files:** AdmissionPrologue, AuthenticatedSettlementFinality,
CanonicalEscrowMarket, CredentialSignedEnvelopeController, DurableCommitProtocol,
DurableWalHandler, GuardedDurableCommit, HyperdocumentPublication, OutboxDelivery,
PrivateEscrowSettlement, PrivateTurn, ProviderExecutionLease, QuotaGcSettlement,
ReactiveTerminalCell, Receipt, ReplicatedSettlementFinality, TurnBalancedLimit,
TypedCellHyperedge, Verbs. (Receipt/Verbs/TurnBalancedLimit/PrivateTurn are consumed by
`Assurance/ReceiptClaim` and the hand manifest `Assurance/SelvageV0Manifest` only.)

**Consumed only inside `Kernel/` — 11 files:** AuthorizedResourceCharge, Camera,
CanonicalResourceEffect, HyperdocumentMerge, HyperdocumentMergeAncestry,
HyperdocumentMergePublication, HyperdocumentVersionEffects, IrreversibleEffectSettlement,
MultiCellHyperedge, Turn, TurnLimit.

**Umbrella-only (zero importers anywhere) — 6 files, 1,754 lines:** `Gate` (638),
`DeclaredActionExecution` (468), `DeclaredHyperedgeCost` (291), `MultiCellHyperedgeWitness` (160),
`TypedCellHyperedgeWitness` (126), `EventLogMaterializerLimit` (71). The three witness/tooth files
are legitimately consumer-less. The other three are parallel-tower candidates under ATLAS law 5.

**Parallel-tower list (my reading):**
- `Kernel/Gate.lean` — 638 lines, zero importers, export `minidregg_gate_ok` (`Gate.lean:615-617`)
  has no caller in `prover/` or `native/` (grep `gate_ok` over `*.rs *.c *.h *.toml`: none).
- `Kernel/Camera.lean` — 637 lines; imported by `State.lean:40` but no identifier used
  (`ResourceAlgebra`, `Fpu`, `Auth`, `Excl`, `conservation_is_fpu`, `Substances` appear outside
  `Camera.lean` only in doc-comments). Boundary-clean (imports only Mathlib) — it is Theory-shaped.
- `Kernel/TurnLimit.lean` + `TurnBalancedLimit.lean` — 449 lines; proved about the abstract
  `Hyperedge`, instantiated at `Fin 2 / ℤ` toys, never at any (B) carrier; sole external consumer
  is the manifest.
- `Kernel/PrivateTurn.lean` — 287 lines; sole external consumer is the manifest; the (B) private
  story is sealed `AcceptedCellEffect` families (D-0002).
- `Kernel/DeclaredActionExecution.lean` — 468 lines; zero importers; imports `Compiler`.
- `Kernel/DeclaredHyperedgeCost.lean` — 291 lines; zero importers; meters the legacy carrier.
- `Theory/TurnTransition.lean` — 404 lines; imported by nothing but `Theory.lean`.

---

## 6. Q5 — `Assurance/` as a hand-written ledger

Sampled: the four largest plus `ErrorBudget`, `ReceiptClaim`, `NoteSpendCoreAcceptedCellEffect`,
`Tower256MerkleBindingCardinality`.

| file | lines | theorems / defs / structures | what it is |
|---|---:|---|---|
| `SelvageV0Manifest.lean` | 1,430 | 75 / 1 / 0 | **hand-maintained re-export manifest**: 75 `theorem manifest_<name> : <copied type> := <original>` (its header, lines 4-8: "a verbatim RE-EXPORT ... The type is copied from the real declaration"). This is the artifact ATLAS §5 names as leave-behind ("`AssuranceCase.lean` as theorem-bearing code — the honest version is a generated index") and law 7 ("Namespace pins beat curated lists"). Its §11 Kernel entries (lines 1147-1195) re-export only (A)-side theorems (`balanced_turn_universal`, `gwrite_umap_frame`, `create_unbacked_breaks`, `privateTurn_*`, `leaky_step_leaks`); none from (B). |
| `DeployedCredentialLifecycle.lean` | 1,099 | 26 / 55 / 2 | hand-written closed lifecycle witness/weld over Compiler+Kernel+Theory |
| `HyperdocumentFinalizedDomainCrawler.lean` | 1,045 | 38 / 36 / 10 | **an application module** (a finite-domain crawler with its own state machine); imports `Kernel.HyperdocumentIndexSync` |
| `DreggNetProviderConsumer.lean` | 952 | 12 / 57 / 5 | self-described "application-level weld for a DreggNet/cloud-provider job" (line 3) |
| `ErrorBudget.lean` | 656 | 14 / 9 / 1 | hand-written composed soundness bound (legitimate assurance content; one bare `#print axioms` candidate at line 649, UNVERIFIED whether prose) |
| `ReceiptClaim.lean` | 928 | 37 / 25 / 1 | hand-written OB-3 bridge from (A)'s `uproj` to Selvage; the only lawful home given the import boundary |
| `NoteSpendCoreAcceptedCellEffect.lean` | 324 | 4 / 13 / 8 | hand-written weld of `Compiler.NoteSpend` into (B)'s `AcceptedCellEffect` |
| `Tower256MerkleBindingCardinality.lean` | 92 | 1 / 0 / 0 | hand-written refutation consequence |

**Generator:** none. `grep -rn "Assurance/" scripts/` finds no script that writes Lean into
`Assurance/`. `scripts/CarrierCensus.lean` is a read-only census (`lake env lean
scripts/CarrierCensus.lean`) over unwitnessed carriers — the law-1 "query, never a hand-count"
shape, but it produces a report, not the ledger. `scripts/local-check.sh` builds
`Theory Kernel Compiler Assurance`. The five files matching "generated" are prose mentions.
`/Users/ember/dev/minidregg/Assurance/Placeholder.lean:4-6` still reads "Generated: namespace
pins, keystone audit (satisfiable + teeth + premise), the carrier registry with realizer slots,
Bound/Forced types, and the floor doc with both soundness numbers. No hand-maintained ledger
anywhere." — contradicted by the directory around it.

**Pins vs theorems (tree-wide, `#print axioms` lines with a `#guard_msgs` on the same or
preceding line counted as guarded):**

| lib | guarded pins | unguarded `#print axioms` candidates | theorem+lemma decl lines |
|---|---:|---:|---:|
| Theory | 266 | 0 | 726 |
| Kernel | 199 | 0 (the 1 hit at `Verbs.lean:282` is prose) | 465 |
| Pred | 0 | 0 | 17 |
| Effects | 6 | 0 | 9 |
| Compiler | 328 | 0 | 985 |
| Selvage | 499 | 27 (UNVERIFIED prose vs command; `GOAL.md` claims zero bare prints after `e6abd03`) | 2,312 |
| Assurance | 572 | 2 (`ErrorBudget.lean:649`, `SelvageV0Manifest.lean:567`; UNVERIFIED) | 1,389 |
| **total** | **1,870** | 29 | **7,685** |

Two Assurance files have zero theorems (`Placeholder`, `SemanticHistoryFamilyInstances`). Two
Assurance files are not in `Assurance.lean` (`Tower256RawHistoryFsController`,
`ZkmlMatmulChecker`) and so are outside `lake build Minidregg` unless imported elsewhere
(UNVERIFIED). App-shaped Assurance by filename: `Hyperdocument*` 21 files / 11,897 lines;
`DreggNet*`+`Grain*`+`TransclusionBacklinkHistory` 3,046; `Zkml*` 2,781 (classification by name
only, UNVERIFIED beyond the two read above).

---

## 7. Q6 — vacuity spot-check

"Built" means a closed term at concrete data in-tree; "generic" means a theorem quantified over
the carrier with no instance.

| # | headline theorem | satisfiable pole | teeth pole | verdict |
|---|---|---|---|---|
| 1 | `MultiCellHyperedge.no_commit_of_nonzero_balance` (`Kernel/MultiCellHyperedge.lean:415-420`, quoted §2) | **BUILT**: `Kernel/MultiCellHyperedgeWitness.lean:111` `def commit : Commit law acceptedLegs boundary where`; `:131` `theorem commit_nonempty : Nonempty (Commit law acceptedLegs boundary) := ⟨commit⟩`; the law cancels `+1/−1` (`:101-102`), two schemas (`schemas_heterogeneous`, `:127-129`) | **NOT built for this theorem**: `no_commit_of_nonzero_balance` and `AdmittedCommit` have zero uses outside the defining file; no built law with a nonzero coordinate. The witness file's tooth is the *apex* equation: `:140-142` `theorem no_commit_with_wrong_apex (other : Commit law acceptedLegs boundary) (wrong : other.jointInput.jointCommit = ⟨99⟩) : False` | one pole (+ a different tooth). Note `Kernel.lean:21` still says "Cross-SCHEMA heterogeneity is still untested"; the witness proves two schemas — stale comment. |
| 2 | `DeclaredTurn.execute_committed_sound` (`Theory/DeclaredTurn.lean:251-257`, quoted §2) | **NOT built**: no `DeclaredTurn.Declaration` is constructed at data anywhere (grep for `DeclaredTurn.Declaration` constructions: none; the only `Declaration ... where` at data is `DeclaredHyperedge.Declaration` in `DeclaredHyperedgeWitness.lean:178`). Consumers are generic (`Assurance/DeclaredTurnReceipt.lean:201,323`, `Theory/TurnTransition.lean:312`) | **NOT built**: `execute_rejected_unchanged` (`:314-322`) is generic; no `.rejected` at data | **neither pole at data**. (The sibling `DeclaredHyperedge.execute` has both: `DeclaredHyperedgeWitness.lean:232-233` `theorem executes_committed : execute projection declaration = .committed postStore`, `:290-291` `theorem rejects_wrong_apex : execute projection wrongApexDeclaration = .rejected .apex`, `:304-305` `theorem rejects_stale_authority : execute staleProjection declaration = .rejected .authorization`.) |
| 3 | CanonicalTransition delta laws (`CellDelta.field_changed_only_declared` `:55-62`; `PreparedTurn.postRoot_derived` `:149-155`, quoted §2) | **BUILT**: `Theory/CanonicalTransitionWitness.lean:38-39` `noncomputable def preparedTurn : PreparedTurn materializer cell Unit := PreparedTurn.ofValidatedPatch (Nullifier := Unit) validated`; `:55` `theorem preparedTurn_moves : preparedTurn.preRoot ≠ preparedTurn.postRoot` | **BUILT at the validator**: `Theory/CellStateWitness.lean:292-294` `theorem stalePatch_rejected : validate materializer cell stalePatch = ValidationOutcome.rejected RejectReason.stalePreRoot := rfl`; `:300-302` `overDeclaredPatch_rejected ... = ValidationOutcome.rejected RejectReason.fieldFootprintMismatch`; `:314-316` `underDeclaredPatch_rejected` (same) | both poles (the delta law is the one-line contrapositive of `fieldFrame`; its teeth live at `validate`, which is where they belong) |
| 4 | `DurableCommitProtocol.execute_no_partial_commit` (`Kernel/DurableCommitProtocol.lean:354-362`) `(execute schedule before intent).storeAfter before = before \/ (execute schedule before intent).storeAfter before = Snapshot.install before intent`; `physical_step_no_partial_commit` (`:880-903`) | **BUILT** at closed data: `Kernel/DurableWalHandler.lean:313-330` `ClosedInstance.device`/`intent` (Nat ids, cell 0 digest 0→1, nullifier 7); `:338-339` `theorem preflighted : intent.preflight device.recovered = .ok () := by decide`; `:343-347` `def committedStep : WalStep ...`; `:366-368` `theorem retry_replays : execute .complete afterCommit.recovered intent = Outcome.replayed intent`. `ImplementationRefinement` (`:861-874`) is inhabited by the WAL handler (`DurableWalHandler.lean:229`). A built `.accepted` exists one adapter up: `Kernel/DurableDataIntent.lean:505-507` `theorem positive_install : execute .complete before intent = .accepted (DataSnapshot.install before intent)` — but that is `DurableDataIntent.execute`, a separate definition (§2.2). | **PARTIAL**: no built `.rejected .stalePreRoot`, `.alreadyConsumed`, `.duplicateCell`, or `.insufficientBudget` anywhere (grep: none) — the fail-closed preflight legs (`:282-297`) have no data-level refutation. Built negatives are the journal branch only: `DurableDataIntent.lean:570-572` `theorem byte_tamper_rejected_after_install : execute .complete (DataSnapshot.install before intent) tamperedIntent = .rejected (.durable .transactionConflict) := by rfl`, and the guard branch `Assurance/HyperdocumentGuardedDurable.lean:249-262` `stale_authority_execute_rejected` (quantified over `current` with a stale hypothesis — not closed data). | satisfiable built; teeth built for 1 of 7 reject reasons |
| 5 | `ReplicatedSettlementFinality.no_conflicting_finalized_transactions` (`Kernel/ReplicatedSettlementFinality.lean:193-201`) `(discipline : PrefixDiscipline book) ... (leftFinal : Finalized quorums book left) (rightFinal : Finalized quorums book right) : ¬ ConflictsAtSlot left right` | **BUILT**: `:401-404` `def certificate : Finalized quorums book candidate where voters := core ...`; `:393-399` `discipline`; `:407-411` `theorem closed_no_conflicting_finalization {other : Candidate Nat Nat Nat Nat} (otherFinal : Finalized quorums book other) : ¬ ConflictsAtSlot candidate other`; failover/retry at `:437-447` | **NOT built**: `:348-356` `theorem no_finality_without_any_quorum ... (none : forall voters, ¬ quorums.isQuorum voters) : ¬ Nonempty (Finalized quorums book candidate)` has zero instances/consumers; there is no built vote book violating `PrefixDiscipline` that exhibits a fork (i.e. nothing shows the `discipline` premise is load-bearing at data) | one pole |
| 6 | Hyperdocument merge: `HyperdocumentMerge.FieldPlan.two_sources_not_conflict_free` (`Kernel/HyperdocumentMerge.lean:744-748`) `(sourcesExact : plan.sources = first :: second :: rest) : ¬ ConflictFree (plan.packedWrites config operation)`; `concurrent_sibling_conflict_positive` (`:780-795`, proof `rfl`) | **BUILT**: `Kernel/HyperdocumentTwoParentWitness.lean:669` `mergeAccepted`; `:681-685` `theorem conflict_is_materialized : lookup mergeAccepted.accepted.prepared.post.logical .conflicts (plan.conflictId ...) = some (plan.conflictRecord ...)`; `:822-823` `commit := HyperdocumentMergePublication.commit ...`; `:825-831` `atomic_content_conflict`; `:841-842` `theorem atomic_conflict_cannot_disappear : ¬ HyperdocumentMergePublication.ConflictFreeState (commit.post .content).logical` | **BUILT**: `:893-894` `theorem swapped_parents_not_canonical : ¬ HyperdocumentMerge.Parent.CanonicalOrder [rightParent, leftParent]`; `:885-887` `base_is_not_current`; `:889-892` `siblings_are_distinct`; `:873-875` `stale_authority_rejects (snapshot : ...) (moved : snapshot.model.roots ⟨905⟩ ≠ authorityPre.root) : durableIntent.preflight snapshot = .error .staleReadGuard` (hypothesis-carrying) | both poles |

---

## 8. Q7 — a proposed collapse, costed

### 8.1 Which side survives

**(B) survives as the semantic kernel; (A) is folded in.** Against the ATLAS criteria:

- *Derived path / feeds Compiler & Effects:* (B) feeds ten Compiler welds (§5); (A) feeds one
  Effects declaration (`moveEffect`) and the OB-3 receipt bridge. Neither side's gate is
  consumed by the AIR (`[ADMISSION-kernel-bridge]` open on both).
- *Field-faithful:* neither. (A) is `ℤ`/`Nat` (`Kernel/State.lean:51,59,124`); (B)'s `Digest` is
  `structure Digest where value : Nat` (`Theory/TypedAuthorization.lean:53-54`). Law 3 is unmet
  by both; not a discriminator.
- *Honest keystones:* (A) has both poles built for every theorem in its five files (read in
  full: `State.lean:210-244`, `Verbs.lean:182-277`, `Receipt.lean:105-129`, `Gate.lean:495-604`).
  (B) is uneven (§7). This favours (A) on discipline but (A) is 2.8K lines proving a model nobody
  downstream runs.
- *Decision record:* D-0002 (2026-08-09, "accepted") declares (B) the semantic kernel and lists
  (A)'s `Turn.lean` as an anchor; it never mentions State/Verbs/Gate/Receipt/Camera, so it never
  said "delete the twin". That omission is the ATLAS §1 failure mode exactly.

### 8.2 What to delete, move, or re-point — and what is NOT safe

**Phase 1 — safe now (zero importers):**
- Delete `Kernel/Gate.lean` (−638). Re-home its still-open labels: `[GATE-fpu]` to `Camera`,
  `[ADMISSION-kernel-bridge]` re-targeted in `Compiler/AdmissionAir.lean:92,691` at
  `DeclaredHyperedge.authorizationCheck` (or whichever (B) gate the owner designates) — this
  bridge is the real remaining work and deleting Gate makes its current target text false.
  Content unique to Gate not present in (B): the closed caveat AST (`Caveat`, `Gate.lean:161-172`)
  — (B) routes policy through `Pred` via `Compiler.CanonicalPolicyAdmission` (UNVERIFIED by
  reading that file), which is where ATLAS wanted it.
- Move `Kernel/Camera.lean` → `Theory/Camera.lean` (0 lines; boundary-clean; it is the ATLAS §7
  "product camera" that was supposed to live in Theory) and drop `Kernel/State.lean:40`'s
  import. Or delete (−637) if `[GATE-fpu]` is abandoned.
- Owner decision, not safe by default: `Kernel/DeclaredActionExecution.lean` (468, zero
  importers, Kernel→Compiler edge) and `Kernel/DeclaredHyperedgeCost.lean` (291, zero
  importers, meters the legacy carrier).

**Phase 2 — re-point the two live (A) consumers, then delete:**
- `Effects/EffectSpec.lean:288-290` `moveEffect` → `CanonicalResourceKernel.Operation.transfer`
  over `Book` (`Theory/CanonicalResourceKernel.lean:123-133, 165`). Mechanical; `move_conserves`
  is replaced by `Operation.apply_conserves` (§2).
- `Assurance/ReceiptClaim.lean` (928 lines) rides `uproj_faithful`. (B) has no theorem of that
  shape (§2, Receipt binding). A (B)-side observation word with a faithfulness theorem over
  `CellState.Materialized` must be written first (estimate: one new Theory file, ~150-250 lines;
  UNVERIFIED — I have not designed it). Until then `State`/`Receipt` are NOT safe to delete.
- After both: delete `Kernel/State.lean`, `Verbs.lean`, `Receipt.lean` (−692) and the five
  manifest entries `SelvageV0Manifest.lean:1160-1177`. `Kernel/PrivateTurn.lean` (−287) can go
  with its two manifest entries (`:1179-1207`) — its only consumer.

**Phase 3 — cash the (B)-internal twin:**
- Re-point `Compiler/DeclaredHyperedgeArtifact.lean` (155), `Compiler/DeclaredEffectPageMaterializer.lean`
  (770), `Compiler/FiniteSparseMaterializerAudit.lean` (238), `Assurance/DeclaredHyperedgeReceipt.lean`
  (293), `Assurance/DeclaredHyperedgeHistoryBinding.lean` (147) at `TypedCellHyperedge` /
  `MultiCellHyperedge`, then delete `DeclaredHyperedge` + `Cost` + `Witness` (−1,655) and the
  `LegacyAdapter` section of `TypedCellHyperedge.lean:419-530` (≈−110). Cost: ~1,600 lines of
  consumers to rewrite (sizes verified; effort UNVERIFIED). This is the single largest honest
  deletion available and it is exactly the move D-0002's own text ("Supersedes: Mina-derived
  call-forest execution") implies.
- Delete `Theory/TurnTransition.lean` (−404; zero importers; the D-0002-rejected alternative).

**Moves (no line delta, but they make the carve true):**
- `Apps/` (new lib): Kernel App class (10,393) + `Assurance/HyperdocumentFinalizedDomainCrawler`,
  `Assurance/DreggNetProviderConsumer` (1,997) + by-name candidates (§6; UNVERIFIED).
- `Deos/` or `Apps/`: `Theory/{Hyperdocument,StableRanges,HyperdocumentOperationIntent,
  HyperdocumentOperations,HyperdocumentInterface,CausalVersionDag,HyperdocumentCausalFamily,
  CausalVersionAncestry}.lean` (4,865). Blocker: three non-Hyperdocument Theory files import
  this group (`Theory/AcceptedCellEffectRequestBinding.lean`, `Theory/CellSlot.lean`,
  `Theory/DeployedMaterializerWitness.lean`) and would have to be split first.
- `Distributed/` (new lib): D + F classes (5,856).

**Line-count arithmetic for `Kernel/`:** 23,802 − 638 (Gate) − 637 (Camera→Theory) − 979
(State+Verbs+Receipt+PrivateTurn) − 1,655 (legacy carrier) − 10,393 (→Apps) − 5,856
(→Distributed) = **3,644 lines** (Turn, TurnLimit, TurnBalancedLimit, TypedCellHyperedge,
MultiCellHyperedge, both witnesses, CanonicalResourceEffect, SparseAuthenticatedState,
DeclaredActionExecution, minus the LegacyAdapter). ATLAS budget: 5-10K. `Theory/` after the
Hyperdocument move and Camera arrival: 26,075 − 4,865 + 637 = 21,847 — still 4-7× the 3-5K
budget, because 13.2K of it is the (B) kernel model wearing Theory's badge (the boundary script
checks imports, not content). Whether those 13.2K lines belong in `Kernel/` (making Kernel ≈16.8K,
Theory ≈8.6K) is an owner decision; the numbers are the same either way.

**Not safe to delete (imported by Compiler/Effects/Assurance/Selvage):** every file in §5's
first two lists. In particular `Kernel/State.lean` (Effects), `Kernel/Receipt.lean`
(Assurance/ReceiptClaim), `Kernel/DeclaredHyperedge*.lean` (Compiler), all `Hyperdocument*`
(Compiler page materializers), `DurableDataIntent`/`FramedWalRefinement`
(`Compiler/FramedWalRecoveryController`), `SparseAuthenticatedState`
(`Compiler/SparseAuthenticatedStateLogupBridge`).

---

## 9. Not determined / UNVERIFIED register

- `Theory/CredentialAuthorityEffects.lean`, `Compiler/CanonicalPolicyAdmission.lean`,
  `Compiler/AdmissionAir.lean` (beyond lines 1-30, 86-100, 681-705), and the bodies of the
  Durable/Finality/App files beyond the regions cited: not read; classification of those files
  rests on headers (lines 1-28) and `Kernel.lean`'s one-line summaries.
- The 27 Selvage + 2 Assurance unguarded `#print axioms` candidates: not checked line-by-line
  for prose vs command.
- Whether `Compiler/Ext6GateProofVersionedDeployment`, `Sp800185Cshake256Core`,
  `TwistMultisetInvariant`, `Selvage/SpongeIndiffPrefixFresh`, `Selvage/ZkmlPoseidon2Data`,
  `Assurance/Tower256RawHistoryFsController`, `Assurance/ZkmlMatmulChecker` are reachable from
  `Minidregg.lean` (they are absent from their lib umbrellas).
- Effort estimates in §8 (rewriting ~1,600 lines of legacy-carrier consumers; the missing
  (B)-side faithfulness theorem).
- App-shaped Assurance beyond the two files read (`Hyperdocument*` 11,897 by name).
- `git` history: file-level dates verified (`Gate.lean` one commit 2026-08-08; `MultiCellHyperedge`
  2026-08-09/10; `TypedCellHyperedge` 8 commits to 2026-08-11); no `Kernel/` file has ever been
  deleted (`git log --diff-filter=D`: only `Kernel/Placeholder.lean`).

---

## 10. Snapshot drift — files that landed during the audit (2026-09-04, 23:45-23:51)

Not mine; from the wave `GOAL.md`'s standing-goal block describes. Headers and imports read;
bodies not audited. Only `Kernel/HyperedgeTier.lean` imports any of them.

| file | lines | imports | what it says it is | bearing on this audit |
|---|---:|---|---|---|
| `Kernel/HyperedgeTier.lean` | 211 | `Theory.Finality`, `Kernel.Turn`, **`Kernel.State`** | "Law 2 (ordering) connected to the ONE turn model (`Kernel/Turn.lean`) and to the conservation spine (`Kernel/State.lean`)"; defines `conservedAtTier (_t : Tier) (k k' : KernelState) (a : AssetId) : Prop` (line 101), `conservedAtTier_move` (106), `conservation_tier_independent` (114), `mint_breaks_at_every_tier` (121); instantiates `Hyperedge (Fin 2) ℕ ℕ ℕ ℤ ...` at toy data (172) | **New (A)-side mass.** It treats `Kernel/State.lean` as "the conservation spine" — the (A) reading — with no reference to `CanonicalResourceKernel`, `MultiCellHyperedge`, or any (B) carrier. Every theorem in it is a fourth restatement of conservation (after State, Gate, CanonicalResourceKernel). If (B) survives (§8), this file's `KernelState` half must be re-pointed at `Book` before it acquires consumers; its `Hyperedge` half is fine (Turn.lean survives). |
| `Kernel/FinalityGate.lean` | 329 | `Kernel.ReplicatedSettlementFinality` | ATLAS §3 item 11 — the fail-closed `@[export]` finality decider; `check` is a `Bool` with `check_eq_true_iff` "in the `gateOK_eq_true_iff` role"; `certificate` turns a `true` verdict into the existing `Finalized` | Built on the (B)-side finality model (class F). Lands in `Kernel/`, though ATLAS §7 places the finality gate in `Distributed/`. Reuses rather than re-proves — the right shape. Whether its export has a caller: UNVERIFIED. |
| `Theory/Finality.lean` | 293 | Mathlib only | four-tier finality lattice, `FinalityRule`, commit-at-join, no-downgrade; port of breadstuffs `Dregg2/Finality.lean` | Boundary-clean. Its header (lines 18-19) promises `tier1_requires_iconfluent` "over `Theory.Confluence.IConfluent`"; no `Theory/Confluence*.lean` exists, and `tier1_requires_iconfluent`/`IConfluent` occur in the file only in doc-comments (lines 19, 74) — the third ordering law named in the header is not in the file. Whether the file builds: UNVERIFIED. |
| `Theory/EpistemicConsensus.lean` | 371 | `Theory.Knowledge` | ATLAS §3 item 5 — `Frame`, `Knows`, `DistKnows`, `verified`, `knows_verified_iff_discharged`, `no_dist_knowledge_of_unrealizable` | Corrects §0 item 10: `Frame/Knows/DistKnows` now exist. Boundary-clean. |

Also landed, not kernel-relevant: `Theory/CyclotomicExceptionalSet.lean`,
`Theory/ExceptionalSetLocalRing.lean`, `Selvage/BaseFoldBcsCapacityEvent.lean`,
`Assurance/ZkmlMatmulSuiteRegistry.lean`, `docs/DISTRIBUTED-DESIGN.md`; modified:
`GOAL.md`, `Assurance/ZkmlMatmulAuditTurn.lean`, `Selvage/HeteroComposition.lean`,
`Selvage/ZkRbrGame.lean`. None of these is in any umbrella yet (`Kernel.lean`/`Theory.lean`
unchanged), so none is in the `lake build Minidregg` closure until wired.

The practical point for the morning: the collapse decision in §8 is not a cleanup of history;
it is the difference between wave 2 adding to one kernel or to two.

---

## Appendix A — raw importer list (umbrella `Kernel.lean` excluded)

```
Kernel.AdmissionPrologue <- Assurance/ReactiveDurableSettlement.lean Kernel/AuthorizedResourceCharge.lean
Kernel.AuthenticatedSettlementFinality <- Assurance/AuthenticatedSettlementFinalityWitness.lean
Kernel.AuthorizedResourceCharge <- Kernel/CanonicalEscrowMarket.lean Kernel/ProviderExecutionLease.lean Kernel/QuotaGcSettlement.lean
Kernel.Camera <- Kernel/State.lean
Kernel.CanonicalEscrowMarket <- Assurance/DreggNetProviderConsumer.lean Kernel/PrivateEscrowSettlement.lean
Kernel.CanonicalPolicyRegistry <- Assurance/DeployedCredentialLifecycle.lean Compiler/CredentialAuthorityPolicyRegistry.lean Kernel/CredentialSignedEnvelopeController.lean
Kernel.CanonicalResourceEffect <- Kernel/AuthorizedResourceCharge.lean
Kernel.CredentialSignedEnvelopeController <- Assurance/CredentialSignedEnvelopeEndpoint.lean
Kernel.DeclaredActionExecution <-
Kernel.DeclaredHyperedge <- Assurance/DeclaredHyperedgeReceipt.lean Compiler/DeclaredHyperedgeArtifact.lean Kernel/DeclaredHyperedgeCost.lean Kernel/TypedCellHyperedge.lean
Kernel.DeclaredHyperedgeCost <-
Kernel.DeclaredHyperedgeWitness <- Compiler/DeclaredEffectPageMaterializer.lean Compiler/FiniteSparseMaterializerAudit.lean Kernel/DeclaredActionExecution.lean
Kernel.DeployedMaterializerWitness <- Assurance/HyperdocumentLinkPublicationWitness.lean Compiler/DeployedCellRegistry.lean Kernel/HyperdocumentTwoParentWitness.lean
Kernel.DurableCommitProtocol <- Assurance/HyperdocumentAgentOperation.lean Kernel/DeclaredActionExecution.lean Kernel/DurableDataIntent.lean Kernel/DurableWalHandler.lean
Kernel.DurableDataIntent <- Assurance/HyperdocumentLinkPageDurableWeld.lean Assurance/ZkmlMatmulAuditTurn.lean Compiler/FramedWalRecoveryController.lean Kernel/AdmissionPrologue.lean Kernel/CanonicalPolicyRegistry.lean Kernel/GuardedDurableCommit.lean Kernel/HyperdocumentTwoParentWitness.lean Kernel/ReactiveTerminalCell.lean Kernel/ReplicatedSettlementFinality.lean
Kernel.DurableWalHandler <- Assurance/HyperdocumentDurableInstallation.lean Kernel/FramedWalRefinement.lean
Kernel.EventLogMaterializerLimit <-
Kernel.FramedWalRefinement <- Assurance/HyperdocumentLinkFramedRecovery.lean Assurance/HyperdocumentMergeDurableFinalityWitness.lean Assurance/ZkmlMatmulFramedWal.lean Compiler/FramedWalRecoveryController.lean Kernel/ReplicatedSettlementFinality.lean
Kernel.Gate <-
Kernel.GuardedDurableCommit <- Assurance/HyperdocumentGuardedDurable.lean Assurance/HyperdocumentMergeDurableFinalityWitness.lean
Kernel.HyperdocumentEventLog <- Compiler/HyperdocumentEventPageMaterializer.lean Kernel/DeployedMaterializerWitness.lean Kernel/EventLogMaterializerLimit.lean Kernel/HyperdocumentVersionEffects.lean
Kernel.HyperdocumentIndexSync <- Assurance/HyperdocumentFinalizedDomainCrawler.lean Compiler/HyperdocumentIndexPageMaterializer.lean
Kernel.HyperdocumentMerge <- Kernel/HyperdocumentMergePublication.lean
Kernel.HyperdocumentMergeAncestry <- Kernel/HyperdocumentTwoParentWitness.lean
Kernel.HyperdocumentMergePublication <- Kernel/HyperdocumentMergeAncestry.lean
Kernel.HyperdocumentPublication <- Assurance/HyperdocumentAgentOperation.lean Assurance/HyperdocumentLinkPublicationWitness.lean Kernel/GuardedDurableCommit.lean
Kernel.HyperdocumentTwoParentWitness <- Assurance/HyperdocumentTwoParentHistoryWitness.lean Compiler/FiniteSparseMaterializerAudit.lean
Kernel.HyperdocumentVersionEffects <- Kernel/HyperdocumentMerge.lean Kernel/HyperdocumentPublication.lean
Kernel.IrreversibleEffectSettlement <- Kernel/ProviderExecutionLease.lean
Kernel.MultiCellHyperedge <- Kernel/CanonicalResourceEffect.lean Kernel/DurableCommitProtocol.lean Kernel/HyperdocumentMergePublication.lean Kernel/HyperdocumentPublication.lean Kernel/MultiCellHyperedgeWitness.lean
Kernel.MultiCellHyperedgeWitness <-
Kernel.OutboxDelivery <- Assurance/ReactiveOutboxDelivery.lean
Kernel.PrivateEscrowSettlement <- Assurance/PrivateEscrowSettlementJoin.lean
Kernel.PrivateTurn <- Assurance/SelvageV0Manifest.lean
Kernel.ProviderExecutionLease <- Assurance/DreggNetProviderConsumer.lean Assurance/HyperdocumentAgentRuntimeScheduler.lean
Kernel.QuotaGcSettlement <- Assurance/QuotaGcSettlementWitness.lean
Kernel.ReactiveTerminalCell <- Assurance/ReactiveDurableSettlement.lean Kernel/OutboxDelivery.lean Kernel/ProviderExecutionLease.lean
Kernel.Receipt <- Assurance/ReceiptClaim.lean Kernel/Verbs.lean
Kernel.ReplicatedSettlementFinality <- Assurance/BoundedPageSchemaUpgradeCutover.lean Assurance/DreggNetProviderConsumer.lean Assurance/HyperdocumentMergeDurableFinalityWitness.lean Kernel/AuthenticatedSettlementFinality.lean
Kernel.SparseAuthenticatedState <- Assurance/GrainForkSettlement.lean Compiler/SparseAuthenticatedStateLogupBridge.lean Kernel/HyperdocumentEventLog.lean
Kernel.State <- Effects/EffectSpec.lean Kernel/Receipt.lean
Kernel.Turn <- Kernel/DeclaredHyperedge.lean Kernel/MultiCellHyperedge.lean Kernel/PrivateTurn.lean Kernel/TurnLimit.lean
Kernel.TurnBalancedLimit <- Assurance/SelvageV0Manifest.lean
Kernel.TurnLimit <- Kernel/TurnBalancedLimit.lean
Kernel.TypedCellHyperedge <- Assurance/GrainForkSettlement.lean Assurance/ReactiveLifecycleHistory.lean Kernel/CanonicalResourceEffect.lean Kernel/DeclaredHyperedgeWitness.lean Kernel/DurableCommitProtocol.lean Kernel/TypedCellHyperedgeWitness.lean
Kernel.TypedCellHyperedgeWitness <-
Kernel.Verbs <- Assurance/SelvageV0Manifest.lean Kernel/Gate.lean
```

---

## Orchestrator's note for the morning (2026-09-05, not the auditor's voice)

The decision above is ember's, not an overnight lane's; nothing was deleted tonight. Two
things the audit's §8 criterion under-weights, for the decision:

1. **"Feeds Compiler/Effects" counts hand-welds as consumers.** (B)'s ten Compiler consumers
   are page materializers and artifact welds authored by the same swarm that authored (B);
   (A)'s one consumer is `Effects/EffectSpec.moveEffect` — the tree's only executor DERIVED by
   the initiality engine. By ATLAS §1 ("the derived path is the ONLY path"), a side wins by
   being derived, not by having more hand-instantiated dependents; volume is how breadstuffs'
   hand-written corpus beat its generic mechanisms.
2. **The two sides are not the same kind of object.** (A) is the compressed concrete state
   (four fields + `UKey`); (B) is schema-polymorphic cells with canonical materialization,
   validated patches, and heterogeneous multi-cell commit — the deployment-shaped vocabulary
   (A) lacks. The synthesis ATLAS §4 already names ("factory cell-programs") is: (A)'s
   `KernelState` becomes ONE `CellState.Schema` instance (the `UKey` plane as a schema), the
   4-leg `gateOK` becomes (B)'s authorization+admission at that schema, and `EffectSpec.derive`
   is re-targeted at (B)'s `sem` so the derived engine covers both. Then §8's Phase 1–2
   deletions are cashed — with the re-pointing done through the derivation engine, not new
   welds. That keeps (A)'s discipline (both poles built, everywhere) and (B)'s vocabulary.

Safe regardless of the decision, for a later wave: the Apps/ move (10.4K), the three
Kernel→Compiler layering inversions, `Theory/TurnTransition.lean` (zero importers), and
extending `scripts/check-import-boundary.sh` to refuse Kernel→Compiler edges.

Tonight's wave was kept model-neutral after this audit landed: `Kernel/HyperedgeTier.lean`
was re-pointed from `KernelState` to `Hyperedge.balanced` (the shared conservation aggregate
both towers bridge into); `Kernel/HyperedgeKnowledge.lean` and the N2 files sit on
`Kernel/Turn.lean` only; everything else is in `Theory/`.
