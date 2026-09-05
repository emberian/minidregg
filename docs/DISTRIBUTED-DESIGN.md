# DISTRIBUTED-DESIGN — the two missing step-logics, stated before they are built

*Design pass 2026-09-04/05, overnight. Inputs: the constitution (`~/dev/breadstuffs/paper2/`,
§1.3 the frame rule read four ways, §2.4 the three logics over a step, §3.3 the coordination
dial, §5 floor 8 PostGSTProgress, §8 "liveness is exactly as strong as its carrier"); a
full survey of breadstuffs' distributed layer (`metatheory/Dregg2/Distributed/`, 36 files /
20,201 lines, plus `Authority/Blocklace`, `Consensus/*`, `Proof/CordialMiners*`,
`Metatheory/EpistemicConsensus`); a full survey of what minidregg holds today; ATLAS §3
items 5, 9, 10, 11 and §7's never-created `Distributed/` carve; KERNEL-NECESSITY §N6. Method
is N2's: fix the statement and the category before the Lean, keystone fields at the
declaration, then author.*

## 0. The diagnosis in one paragraph

The constitution judges every turn by **three orthogonal logics** (paper2 §2.4):
**conservation** (linear: Σδ = 0, the camera), **ordering** (temporal/modal: a finality
lattice over one causal DAG; a turn commits at the join of its written cells' tiers and
never downgrades), and **independence** (the join-semilattice of invariant-preserving
merges — the coordination-free fragment, priced by the confluence classifier). Minidregg
today has the first logic end to end (`Kernel/Camera`, `Kernel/State`, `Kernel/Gate`,
`Kernel/Turn`, N2a/N2b) and **none of the other two**: no `IConfluent`, no `Tier`, no
join, no `Knows`, no colimit anywhere in 217K lines. What landed under the megaswarm is a
replicated-settlement tower (`Kernel/ReplicatedSettlementFinality` — safety over
intersecting quorums as a theorem, liveness as bare `Prop` premises, no decider, no
export, consumed only by closed `Fin 3` Assurance witnesses), a causal DAG with a poset
and an LCA but no join (`Theory/CausalVersionDag`, `CausalVersionAncestry`), and a
document merge that is deliberately anti-commutative (`Kernel/HyperdocumentMerge`,
`raw_pair_order_observable`). That is "the distributed semantics of the OS never got
completed", made exact: two of the three step-logics are absent.

## 1. Where breadstuffs stopped, and why each stop is an implementation-modeling artifact

Breadstuffs built the whole tower — blocklace, τ-ordering, super-ratification, quorum
gates with `@[export]`, LaceMerge, catch-up, prune, strands, epistemic consensus — and its
formal core never closed. The six named defects, each quoted from the source:

| # | Defect | Where | Why it is a modeling artifact |
|---|---|---|---|
| G1 | `hOrder` — permutation-invariance of `tauOrder` NOT established; carried as a binder on every "same blocks ⇒ same state" theorem | `Distributed/LaceMerge.lean:326-353` | `computeRounds` is an `Array.qsort` fold on `(seq, creator)` with TIES (a tie IS an equivocating pair). A finalizer that is a **fold over a `Finset`** is permutation-invariant by construction. |
| G2 | `CrossCanonical` — equal keysets are not equal laces; content-address collision at the replica boundary; "carried ANONYMOUSLY at every convergence site until it was named" | `LaceMerge.lean:24-31, 244-246`; `Consensus/Safety.lean:48-61` | The premise was never a typed carrier. Minidregg's `Theory/CausalVersionDag.BindingPremise.reflectsEquality` IS this premise as a realizer slot; the lace must consume it, not re-hypothesize it. |
| G3 | `ChainExtends` (Cordial Miners Prop. 3) imported from the paper; `finalLeaderAt` can **retract** an anchored wave — "the deeper defect" | `Consensus/TauPrefixMonotone.lean:52-80`; `docs/reference/READING-DAG-BFT-2026-08-08.md:751` | There was no append-only floor. Finality as a **prefix-monotone chain by type** (the finalized prefix is a field with an `IsPrefix` proof, never recomputed) makes retraction unrepresentable. |
| G4 | `OPEN-CM-LOCAL-EQUIVOCATION` — the node's observer-local same-round guard vs the algebra's global incomparability guard; a class of live runs outside the safety theorem's domain | `Consensus/SuperRatifyBridge.lean:229-258` | Two definitions of "equivocator" (executor twin vs proof twin). One definition, exported, ends the seam. |
| G5 | The BFT model over the UNION of two nodes' ratifier pools is assumed (post-GST dissemination residual) | `Consensus/Safety.lean:117-123`; `Proof/CordialMiners.lean:87-89` | Legitimately a floor (reliable broadcast). Must be ONE named carrier with a realizer slot, not a structure field per file. |
| G6 | "no Lean THEOREM in this tree can evaluate the deployed finalizer on a concrete lace" — every FinalityGate pin is `native_decide` | `SuperRatifyBridge.lean:239-248`; `FinalityGate.lean:62-65` | `qsort`'s worker is `private` to `Init` and irreducible. A finalizer written as a structural fold over a `Finset`/`List` with mathlib's `mergeSort` lemmas (or no sort at all) is kernel-evaluable; keystones become `decide`, not tests. |

Plus the honest floors that stay floors: G7 liveness (`World.rand` measure bridge,
PostGSTProgress), G15 UC composition, G19 the orphaned federation crypto. ATLAS law 5
("one executable tower") and law 9 ("`#guard` is silent `native_decide`") were both paid
for here before they were written down.

**The design law this fixes for `Distributed/`:** the finalizer is DERIVED — a fold over
syntactic structure (N3), kernel-evaluable, permutation-invariant by construction — and
finality is prefix-monotone by type. Every distributed premise (collision resistance at
the replica boundary, reliable dissemination, post-GST progress) is one typed carrier with
a realizer slot and a refutation at a broken sibling (law 1). No twin of a Rust `tau`.

## 2. The slate landing tonight — statement-first, keystone-fielded

Files are placed by the import boundary: candidate-independent shapes in `Theory/`
(Mathlib + Theory only, CI-enforced), instantiations on the hyperedge and the kernel state
in `Kernel/`. A `Distributed` lean_lib opens when the first lace file lands (§3.1); tonight
nothing needs it.

### 2.1 Independence logic — `Theory/Confluence.lean`

- `IConfluent [SemilatticeSup S] (I : S → Prop) : Prop := ∀ x y, I x → I y → I (x ⊔ y)`.
  ONE name (breadstuffs had `IConfluent = Tier1Eligible = guardKeepsConfluence =
  CoordinationFree` with `Iff.rfl` "theorems" between them — naming is faking).
- **The categorical reading (new; N6's heart at the poset shadow).** I-confluence is exactly
  mathlib's `Subtype.semilatticeSup` hypothesis: under it the invariant-satisfying views
  form a sub-semilattice and the merge of two lawful views IS their binary coproduct in the
  lawful subcategory (`merge_is_coproduct`, via `Preorder.isColimitBinaryCofan`).
  **Sharp edge, built as teeth:** the converse is FALSE — a 5-point lattice `⊥ < a,b < c < ⊤`
  with `I := (· ≠ c)` has `I a`, `I b`, `¬ I (a ⊔ b)` yet its lawful part is the 4-point
  Boolean lattice, so `HasBinaryCoproducts Five.Lawful ∧ ¬ IConfluent` is a theorem
  (`subtype_lub_does_not_imply_iconfluent`) and the displacement is computed
  (`lawful_join_is_not_the_merge`: the lawful coproduct of `a`,`b` is `⊤`, their merge is
  `c`). This stops anyone stating the wrong iff. Landed as `Theory/Confluence.lean` (416
  lines).
- Guard classifier: `Guard S := monotone proj c | bounded proj c | relational I`,
  `CoordinationFree g := IConfluent g.inv`; `monotone_free` (a grow-only floor runs
  coordination-free), `bounded_breaks`/`bounded_forces_ordering` (a resource ceiling with a
  clashing pair forces consensus, with the pair exhibited).
- Keystones: grow-only `Finset ℕ` (`⊤` confluent; `card ≤ 1` not, at `{0}`,`{1}`); **the
  constitution's own example as a real CRDT** — a two-replica PN-counter
  `Fin 2 → ℕ × ℕ` under pointwise max; `x = ![(5,4),(0,0)]`, `y = ![(5,0),(0,4)]` both have
  value 1 ≥ 0, `x ⊔ y = ![(5,4),(0,4)]` has value −3: two concurrent withdrawals merge to
  overdraft, so `balance ≥ 0` is linear but NOT I-confluent.
- Residuals: `[CONFLUENCE-pred-dial]` classification of the ONE `Pred` AST under a declared
  per-cell merge (the coordination dial as a computed price — the Pred lane's follow-on);
  `[CONFLUENCE-finality]` consumption by the tier ladder (§2.3).

### 2.2 N6 at the poset shadow — `Theory/ViewMerge.lean`

- Partial views of a replicated log are a `SemilatticeSup`; federation merge is the join.
  `binary_merge_is_colimit` (mathlib, named), `finite_merge_is_colimit` (a finite family of
  views: the whole-history object is the colimit of the discrete diagram, via
  `Preorder.isColimitOfIsLUB`), teeth `strict_upper_bound_not_colimit` (`{0,1,2,3}` is an
  upper bound of `{0,1}`,`{1,2}` but not the colimit; `{0,1,2}` is).
- LaceMerge's four laws (`merge_comm/assoc/idem/monotone`, `LaceMerge.lean:148-182`) are
  `sup_comm/sup_assoc/sup_idem/le_sup_left` of the instance — subsumed, not restated.
- Landed as `Theory/ViewMerge.lean` (296 lines) with the finite-prefix chain
  (`chain_merge_is_colimit`, any `Preorder`, no completeness assumed) and the PN-counter
  teeth in federation vocabulary: the two lawful overdraft views have NO least upper bound
  among lawful views, hence `overdraft_pair_has_no_colimit : ¬ HasColimit (pair xL yL)` —
  "forces ordering" as the literal absence of a colimit.
- Residuals: `[N6-receipt-colimit]` the receipt-chain colimit (Selvage's accumulator) is the
  real N6 and is NOT here; `[N6-blocklace]` equivocation exclusion / per-author strands;
  `[N6-cross-canonical]` see §3.1.

### 2.3 Ordering logic — `Theory/Finality.lean` + `Kernel/HyperedgeTier.lean`

- The four-tier ladder `Tier := causal | ackThreshold | bft | constitutional` (breadstuffs
  `Dregg2/Finality.lean` §2.2, docstrings kept: tier 1 never blocks under partition and is
  eligible ONLY for I-confluent state; tier 2 degrades to 1; tier 3 stalls and resumes after
  GST; tier 4 stalls with a deadline), `LinearOrder`, `OrderBot` (`⊥ = causal`), the
  cross-tier rule is the lattice join (no `crossTierJoin` synonym).
- `FinalityRule H` (tier, committed, canonical, commit_canonical),
  `commit_at_join_of_tiers` (the join dominates every written cell's tier AND canonicity is
  granted only by the join-tier rule's commit), `reachable_no_downgrade` with its tooth
  `downgrade_unreachable : ¬ ReflTransGen TierStep .bft .causal`.
- `tier1_requires_iconfluent` in the parametric form (a classifier that assigns tier 1 must be
  sound for `IConfluent`) with both corollaries: monotone-floor guards may be tier 1;
  a bounded guard with a clashing pair may NOT.
- `Kernel/HyperedgeTier`: `commitTier tierOf := Finset.univ.sup tierOf` over a hyperedge's
  incidences; `leg_le_commitTier`; `commitTier_eq_causal_iff` (a turn runs coordination-free
  iff EVERY written cell is tier 1); `hyperedge_commit_at_join`; and the orthogonality of
  Law 1 and Law 2 on the kernel's own spine: `conservedAtTier t k … := totalAsset (move …) =
  totalAsset k`, `conservation_tier_independent … := rfl`, `mint_breaks_at_every_tier`.
- Residuals: `[FINALITY-blocklace]` τ-BFT waves/leaders/ratification; `[TIER-of-cell]` the
  kernel state carries no per-cell tier field yet; `[TIER-gate]` `admit` does not consult
  tiers; `[FINALITY-liveness]` §3.2.

### 2.4 The finality gate as a decider — `Kernel/FinalityGate.lean`

ATLAS §3 item 11's pattern, over the tower that already exists. `Cert Node := {voters}` is
the only wire data; `check quorums book candidate cert : Bool` is a bare `&&` of positive
checks (`decide (isQuorum voters) && ∀ voter, candidate ∈ book voter`); `check_eq_true_iff`
is the unfolding lemma; `certificate : check = true → Finalized quorums book candidate`
CONSTRUCTS the certificate the existing theorems consume, so `checked_logs_comparable` and
`checked_no_conflict` are inherited through the checker, never re-proved. Fail-closed teeth
per refusal reason, attributable (the other condition still holds). `@[export
minidregg_finality_check]` on the closed `Fin 3` instance — the symbol exists (Gate.lean §10
pattern). Residuals: `[FINALITY-GATE-authenticated]` (the same checker over signed votes,
erasing to this one), `[FINALITY-GATE-liveness]`, `[FINALITY-GATE-rust]` (the unverified
fallback behind an explicit labeled env var is Rust-side), `[FINALITY-GATE-receipt-seam]`.

### 2.5 The epistemic seam — `Theory/EpistemicConsensus.lean` + `Kernel/HyperedgeKnowledge.lean`

ATLAS §3 item 5, unrealized until tonight. `Frame Ω ι` (actual world, per-agent
indistinguishability, faulty set), `Knows`, `DistKnows`, and **the trick**: `verified X w₀`
is a constant proposition over worlds, so a discharged claim is known by every agent in
every frame regardless of `Indist` and regardless of who is faulty
(`all_know_discharged`, `honest_distributed_knows_discharged`,
`knows_verified_iff_discharged`); an unrealizable claim is distributed knowledge of nobody
(`no_dist_knowledge_of_unrealizable`). Keystones on a two-world, two-agent frame where a
world-dependent fact is known by the discriminating agent only. Then the hyperedge bridge:
the cone condition `H.agree` makes the apex id **distributed knowledge among the honest
legs** (`agreement_is_distributed_knowledge` — the epistemic reading of `legs_agree`), and a
fork (two honest legs reading different ids) is precisely the absence of any distributed
apex (`fork_has_no_distributed_apex`); the characterization `distKnows_apex_iff_honest_agree`
is an iff. Landed as `Theory/EpistemicConsensus.lean` (369 lines; the ancestor's misnamed
`honest_dist_knowledge_iff_holds` is `holds_of_honest_distKnows_verified`, its `hrefl`
premise absorbed by the frame's `indist_refl`; the keystone verifier is `p = 2·w` so wrong
witnesses and unrealizable claims both exist) and `Kernel/HyperedgeKnowledge.lean` (222
lines, on `Kernel/Turn.lean` only). Residuals: `[EPISTEMIC-common]` common knowledge and
the finality floor `C_G` (breadstuffs `Authority/Epistemic.FinalityFloor`, the weld to the
light client); `[EPISTEMIC-threshold]`; `[EPISTEMIC-uc]`; `[HYPEREDGE-operational]`.

## 3. The next slate — designed, not yet authored

### 3.1 The lace, with the CrossCanonical gap closed by a realizer slot

`Theory/CausalVersionDag.lean` already carries the content-addressed multi-parent DAG
(`EventPreimage`, `ContentAddressing`, `BindingPremise.reflectsEquality`, `ValidAppend`,
`frontier`, `Builds`, `Replay`, `checkpoint_suffix_equivalence`) and is load-bearing through
`Theory/Hyperdocument`. The lace is its keyset view: `View := Finset Address`, merge = `∪`
(§2.2's instance), and the two theorems breadstuffs could only hypothesize become:
`sameView_of_binding (h : BindingPremise scheme) : laceIds B₁ = laceIds B₂ → Canonical B₁ →
Canonical B₂ → SameView B₁ B₂` — G2's `CrossCanonical` DERIVED from the named premise — with
the port of `crossCanonical_is_the_gap` as teeth at a NON-binding addressing (two canonical
views, equal keysets, different lookups). That is law 1 executed on the highest-exposure
unrefuted floor of the predecessor. Lives in `Theory/LaceMerge.lean` (it imports only
`Theory.CausalVersionDag`, so the boundary puts it in `Theory/`); the `Distributed`
lean_lib opens with the first file that needs both `Theory` and `Kernel` and is not
itself kernel vocabulary — the derived finalizer of §3.3.

### 3.2 Liveness as one carrier

`PostGSTProgress` as ONE typed structure bundling `ReplicatedSettlementFinality`'s three
premises (`AvailableQuorum`, `FairDelivery`, `Responsive`) with a realizer slot; the pair the
constitution states — `no_forge_without_quorum` (safety needs no liveness premise; already
`no_finality_without_any_quorum`) and `progress_of_postGST` (already
`finalized_of_available_fair_responsive`, a `def`) — named as the two poles; plus the port of
`Liveness.revocation_needs_consensus` with its satisfiable/teeth pair and, if
`Nat.Partrec` elaborates cleanly at this pin, `dead_undecidable`. "A partitioned network
stalls finality; it cannot forge it" becomes two theorems, not a sentence.

### 3.3 The DERIVED finalizer (the statement, for when the lace exists)

Not a port of `tauOrder`. Statement-first: an ordering rule is a function `order : View → List
Address` that is (i) a fold over the view (so `order_perm : ∀ B₁ B₂, laceIds B₁ = laceIds B₂ →
order B₁ = order B₂` is a THEOREM — G1 dissolved), (ii) prefix-monotone along admitted
extension (`order B <+: order (B ⊔ Δ)` under a typed extension relation — G3's floor as a
type, retraction unrepresentable), (iii) kernel-evaluable (keystones by `decide` — G6
dissolved). Equivocation exclusion enters as ONE predicate on the view (G4), and the union
BFT premise as one carrier (G5). Whether a Cordial-Miners-shaped τ can be written as such a
fold is the research question; if it cannot, the failure names the exact sense in which
leaderless DAG finality is not a fold, which is the honest signature.

### 3.4 The coordination dial on the ONE `Pred` AST

`[CONFLUENCE-pred-dial]`: `Pred.State` is a name-keyed `Int` record; a cell's program
declares its merge (per-slot rule: max / PN-counter / write-once), the classifier reads the
syntactic guard (`monotone slot` under max-merge ⇒ tier 1; `le slot c` under a PN-merge ⇒
forces ordering) and its verdict is proved sound against `eval`'s denotation. This is where
"a guard doesn't have a price, it is priced by where it lives" lands.

### 3.5 N4

No Lean tonight on purpose; the statement-first pass is `docs/N4-DISTRIBUTIVE-LAW.md`.
Its verdict: Σ is `Compiler/Signature` (mathlib `PFunctor`), and `EffectSpec.sig` is the
unary `1 + Op × X` whose closed terms are lists — over it Turi–Plotkin says nothing, so N4's
content lives at the ι-ary JOINT node (the hyperedge as a shape). There is no behavior
functor B in the tree; the honest one is the Moore functor `Req → Obs × X` with refusal an
OBSERVATION (both state models already refuse by "post = pre"), whose final coalgebra is
`PFunctor.M` at that shape — ATLAS item 15's `nuF = List Req → Obs` for free, do not port
it. Format-fit, checked by hand: the fail-closed law is the strict `Option` traversal and
satisfies every axiom — but so does a fail-open sibling, so fail-closedness is a CHOICE of
λ, to be a separate keystone `FailClosed` with teeth (the open law commits a hyperedge with a
refused leg). Adequacy (`fold = corec`, the unique bialgebra morphism) and congruence
(a hyperedge over `nuF`-equal cells is `nuF`-equal) are what it buys; conservation,
authority, frame, crypto are not. The single most likely failure: `Hyperedge.halfEdge`
reads the CARRIER, and GSOS rules may only read behaviours — `Bal` must be observable in
`Obs` or conservation-gating falls outside the format. Sequencing: decide B's `Obs` and
Σ's joint shape first (the same decision the twin audit's Phase 2 needs); the collapse
gates only the instance file.

## 4. What is NOT claimed

Nothing tonight is a consensus protocol, a network model, a liveness proof, a Byzantine
tolerance result, a collision-resistance theorem, or a deployment. `Finalized` certificates
are built from a TRUSTED vote book (authenticated votes remain
`AuthenticatedSettlementFinality`'s). The N6 statements are the poset shadow; the
receipt-chain colimit is the real N6 and is named, not built. Every premise stays a premise
with a name and a slot.

## 5. Relation to what exists

`Kernel/ReplicatedSettlementFinality` is consumed, not replaced: the decider constructs its
certificate. `Theory/CausalVersionDag` is consumed by §3.1. `Kernel/HyperdocumentMerge`'s
conservative conflict-retaining join is NOT a semilattice and is not made one — it is the
`relational` guard whose confluence is decided by its merge, and D-0005's reservation of
the words *pushout/I-confluence* for their exact proved definitions is exactly what §2.1
supplies the definitions for. `Kernel/HyperedgeTier` and `Kernel/HyperedgeKnowledge` sit on
`Kernel/Turn`'s `Hyperedge`, the ONE turn model; the twin audit decides whether the typed-cell
`MultiCellHyperedge` tower is a refinement of it or a second model.
