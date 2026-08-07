# ATLAS — what breadstuffs taught us, and what minidregg must be

*Compiled 2026-08-06 from a six-lane deep exploration of `~/dev/breadstuffs` (primarily
`metatheory/`). This is the founding map: the diagnosis, the inventory of what survives,
the design laws, and the architecture carve. File references point into breadstuffs.*

---

## 0. The numbers

| | lines of code |
|---|---|
| breadstuffs total | **~2.89M** (1.82M Rust · 913K Lean · ~160K TS/JS) |
| minidregg budget (≤10%) | **~290K** — and the analysis below says we need far less |
| `metatheory/Dregg2` | 715K Lean / 2,242 files |
| — of which `Circuit/` | 416K (58%) — `Circuit/Emit/` alone is **271K** |
| — of which `Games/` | 98.6K |
| — semantic core (Substrate+Spec+Authority+Calculus+Proof+Logic) | **~25K** |
| `Metatheory/` (abstract theory) | 5.1K — genuinely candidate-independent: **~2.4K** |
| Rust prover/executor machinery (circuit+circuit-prove+turn+node) | ~416K |
| `Apps/` | 28K, of which ~75% is five mechanical moves repeated per app |
| 29 Argus effect welds | ~11K lines, of which ~1.5K is content |
| irreducible kernel (per the kernel-lane audit) | **800–1,200 lines** |

The system's *meaning* is a few tens of thousands of lines. Everything else is
hand-instantiated derivation output, welds between parallel abstractions, and twins.

## 1. The central diagnosis

**Breadstuffs built and proved every piece of the derivation machine, demonstrated each
at n=1, and wired almost none of them into the load path.** The distance to "write once,
derive executor + proofs + circuits" was never mathematical — every lowering is sound.
The mass exists because each generic mechanism landed *beside* the hand-written corpus
it should have replaced:

- `dregg_program` eDSL → VCG → whole-run safety: complete vertical slice, used **once**
  (its own demo). 63 apps / ~962 theorems hand-written beside it.
- `Apps/VerificationToolkit.lean` proves the five shared app moves parametrically:
  **3 of 63** files adopt it; 14 hand-roll; 8 gated/ungated historical twins persist.
- Logic→IR compiler real and sound; **11 of 76** deployed descriptors compiler-*authored*
  (later 26/91). "Reachability is not authorship."
- `EffectCommit.EffectSpec` proves soundness/completeness + all four anti-ghost teeth
  **once, generically** (~100 lines per effect to instantiate) — the Argus welds are a
  parallel hand-written universe bridging *to* it instead of being generated from it.
- `Substrate/VerbCompression.lean` **proves the kernel is 3 verbs** (`create·gwrite·move`)
  over a proved-sharp 4-level guard lattice (`compressed_kernel_three`,
  `verb_minimality_is_ontology_relative`). Never executed.
- `UniversalBridge.UKey` shows the 19-field kernel record is 3 fields + one keyed map.
  Landed beside the record.
- `GatedForestCfg.GatedForestCarriers` bundles the 11-type-parameter signature disease.
  Never propagated back.
- `Metatheory/Dynamics/Initiality.lean` proves `interp` is a fold and the current
  `compile` provably is not (`compile_not_a_seq_hom`) — naming exactly the one design
  change that makes executor⟺circuit agreement free forever.

**The corpus contains its own refactor plan, proved as theorems, and did not execute it.**
Root causes, documented in its own words: the additive-extension culture ("the additive
extension, exactly as nullifiers/commitments were added" — verbatim ~10× inside one
structure), no delete-the-twin discipline ("a `rfl` against a hand-written twin is
evidence only while the twin exists; cashing it means deleting the twin"), and ~19
concurrent goal lanes sharing one tree with no isolation.

**Minidregg's founding move is the inversion: the derived path is the *only* path, so
n=1 and n=all coincide by construction. Nothing lands beside; everything replaces.**

## 2. The distilled thesis (from paper2/, 747 lines — keep as the constitution)

> A **turn** is the exercise of an attenuable, proof-carrying token over owned state,
> leaving a verifiable receipt.

- **Four substances**, each a discipline: value **linear** (Σδ=0 exactly, issuer wells,
  mint=move), authority **generative under non-forgeability** ("only connectivity begets
  connectivity" — NOT lattice descent; introduction/amplification/mint are authorized
  production), evidence **monotone**, state **guarded-mutable** (the frame rule).
- **One `Pred` algebra at four polarities**: caveat (delegated power) / program (owned
  state) / precondition (turn) / intent demand (world). Two **computed dials**:
  coordination (confluence-stable ⇒ coordination-free, priced not forbidden) and
  disclosure (cleartext → committed → range-proved → garbled; "what the proof does not
  need, it does not see").
- **Authority = constructive knowledge** (BHK operational): proof-checking cheap+trusted,
  proof-search undecidable+untrusted. To hold a capability is to be able to exhibit a
  witness that verifies.
- **Receipts Q**: one committed object — the witness proves it, the dial projects it,
  aggregation folds it, the light client verifies only Q-chains.
- **The Lean kernel IS the executor** (FFI export); apps are factory-minted cells whose
  contracts are *inherited* kernel theorems.
- The spine in five words: **determination is eager; witness is lazy.** Every hole is a
  lazy witness over an eager shape; the thing to never build is a hole that defers its
  δ or its guard.

## 3. Inventory — take verbatim

1. **The verify/find seam** (`Dregg2/Laws.lean:35-56` + `ConstructiveKnowledge.lean:63-93`):
   `Verifiable.Verify : P → W → Bool`, `Discharged`, `Searchable.find` with deliberately
   NO soundness field, `Holds X = ∃ w, Verify X.stmt w = true`, `Knower = (trusted
   decidable verify, untrusted opaque search)`. Four declarations under 12,700 lines.
2. **`GovernedDynamics` / `governed_holds`** (`Metatheory/Adversary/Schema.lean:58-84`):
   `∀ c, accept (run c) → invariant (run c)` with `holds` as a field, plus the
   not-a-tautology proof and the per-instance accept-satisfiability obligation. The
   top-level shape of every security statement, from day one.
3. **The four-substance product camera + `Verb = admission × footprint-Fpu`**
   (`Metatheory/Dynamics/Substance.lean`, `VerbSignature.lean`): all four disciplines are
   one Fpu in a product resource algebra; `authority_evidence_share_camera` (same `Auth M`
   camera); the preserved negative `camera_blind_to_caveats` (the pair is irreducible).
4. **Authority closure with amplification** (`Open/AuthorityClosure.lean`):
   `AmpProduces`/`AmpClosed` — a reachable right is ≤ a ⊗-combination of held rights
   (sealer/unsealer done right); `Produces` recovered at `b := 𝟙`.
5. **`Frame`/`Knows`/`DistKnows`/`verified`** (`EpistemicConsensus.lean:68-122`) — the
   world-independence of a discharged claim is the Byzantine-proofing trick. Carries
   CommonSecret (threshold cliff/jump), Disputation, OptimisticAdjudication
   (¬¬ core; `Classical.choice` as regime *diagnostic*), ResharingChain.
6. **Games**: `SafetyGame` viability kernel + `kernelShield` (shield the gfp, not the
   floor), `ReachGame.reachWithin_sound` (honest bounded monitor), `EnergyGame` world-
   expansion trick. 106 lines doing real work.
7. **The gate + executor core** (`Exec/FullForestAuth.lean:433-585`): four-leg `gateOK`
   (credential-portal ∧ cap-authority-in-Lean ∧ caveats ∧ revocation-from-committed-state),
   fail-closed `execFullAGated`, `gatedNode_check_eq_use` no-TOCTOU. ~30 lines.
8. **The conservation spine**: `bal : CellId → AssetId → ℤ` over `Finset accounts`,
   issuer wells carrying −supply, Σ=0 as identity; `reachable_total_zero`;
   `oldMint_breaks_conservation` as the tooth.
9. **`Hyperedge`** (`Dregg2/Hyperedge.lean`) — turn = wide pullback (participant tuple,
   one turn, one shared id, N cone legs, Σ half-edges = 0); pairwise agreement a theorem
   not C(N,2) data — **with its three negative theorems** (`hyper_binding_is_proper`,
   `hyperedge_sound_needs_binding`, `hyperedge_sound_bisim_ill_posed`).
10. **LaceMerge join semilattice** (`Distributed/LaceMerge.lean`) — four one-line Finset
    proofs that ARE the replication story; `crossCanonical_is_the_gap` (naming the
    anonymously-carried assumption + executable refutation).
11. **The `@[export]` gate pattern** (`Distributed/FinalityGate.lean`) — Lean is the live
    decider; fail-closed; unverified fallback requires an explicit labeled env var.
12. **`decideVm` + `decideVm_iff_satisfiedVm` + golden corpus + proved-injective
    serializer** (`Circuit/Argus/InterpCore.lean`, `EmitRoundtrip.lean`) — the TCB-to-30-
    lines move: decidable reference ↔ Prop denotation, injective bytes, embedded verdicts.
13. **`graduateV1`-style proved descriptor→descriptor passes** with `autoParam`
    admissibility (inadmissible descriptor fails to *elaborate*).
14. **The deos crown**: surface-as-cap, membrane non-amplification,
    `replayedDeterministic_iff_confined` (confinement IS the deterministic-replay
    fragment), affordance-soundness; DocMerge as LUB / pushout products; fog-of-war
    non-interference. Identity: *affordance = cap-gated effect-template; firing = turn;
    turn = receipt* — one machinery, three faces (human/authored/agentic).
15. **`nuF = List Adm → Obs`** final coalgebra (100 constructive lines, no Adámek).
16. **`InterchainAdapter`** fail-closed pattern (`emptyAdapter_never_credits` — the
    inverse of the Nomad bug).

## 4. Inventory — take the pattern, redesign the body

- **Factory cell-programs** (7 kernel verb families deleted; ONE new atom
  `RelCaveat.fieldLteOther` covered all; side tables + conservation exemptions *stopped
  existing*; found live bug R7 — stored caps must re-check grantor epoch on retrieval).
- **VerificationToolkit** widened to multi-slot + effect families + credential legs —
  then it IS the app layer. Author supplies spec + RED witnesses; proofs generated.
  (Generate the proofs; **demand** the non-vacuity witnesses — those are app data.)
- **Registry-driven executor** (HARVEST-KEEPERS design): open `Registry := List
  PackedHandler`; each handler carries step/delta/auth/admission/trace with ALL floor
  obligations as **proof fields** (ill-typed until discharged). Not 3 of 9 typed and 6
  as side-hypotheses — that is "the exact shape of a silent gate."
- **RED/GREEN witnesses in the tree**: pre-fix rules kept live so `#guard`s execute the
  wound (RED) next to the fix (GREEN) on the same instance. A reverted edit is
  forgettable; a build-breaking witness is not.
- **MPST choreography surface** (`DSLChoreo` — inherited deadlock-freedom + privacy-by-
  projection) once recursion projection is closed.
- **The honest-floor documentation style** (`docs/STARK-FLOOR.md`): exact deployed
  parameters, BOTH soundness numbers (conjectured 130-bit / proven 73-bit), audit status
  stated without euphemism, floors as typeclass hypotheses never axioms.

## 5. Inventory — leave behind (with the reason on the label)

- The gated/ungated executor twins + `eraseG` (137KB for "add a boolean gate"); 38 of 40
  `exec*` entry points; `Core.lean`'s ornamental category packaging (keep
  `noClone_of_invariant_tor` = 4 lines); `Spec/`'s 3-constructor toy `Effect` and
  `Spec/Coherence.lean` (do the factoring, don't prove the non-factoring harmless).
- Three parallel `compile`s + `RecStmt`/`RecStmtE` split (fixed by syntactic leaves).
- Three parallel predicate algebras + opaque `Ctx → Bool` caveats (fixed by ONE algebra,
  AST-only policy path).
- The GENTIAN descriptor plumbing colonizing `Deos/` (~7K lines), aggregator-shim
  modules, ungated app twins, `EpistemicDial`'s 607→80 lines, misfiled domain apps in
  `Metatheory/` (orbital screening…), `attestationUCDynamics` (self-labeled relabel).
- `AssuranceCase.lean` as theorem-bearing code — the honest version is a generated index.
- Hand-rolled JSON emission + 98KB of per-format round-trip proof (derive the codec
  generically, prove round-trip once).
- Prose counts (27 vs 36 effects, 17 vs 19 fields, 51 vs 31 actions — same tree, same
  objects). Prose never carries state; generated docs with `--check`, or nothing.

## 6. The design laws (each purchased with a documented wound)

1. **Naming is faking.** A `class`/`def : Prop` hypothesis is an assumption
   `#assert_axioms` cannot see (the 07-09 retraction; StarkSound "instance" laundered
   from a 0-instance hypothesis; accept-everything `FriExtract` realization). → Carriers
   are typed obligations with a realizer-or-FLOOR-tag slot; the unrealized census is a
   query, never a hand-count; every carrier must be refuted at a broken sibling oracle.
2. **A keystone that can't exhibit both poles doesn't compile.** Kernel-clean + true +
   vacuous happened repeatedly (empty accepting sets; `leaves := []` tautology no
   deployment can repair; hash-injectivity premises false by counting *at deployed
   parameters* — and the assurance file ships an apex in the shape its own preamble
   names as its past mistake). → declaration-level `satisfiable` + `teeth` + premise-
   inhabitation (`∃ s : PremiseType`), CI-gated beside the axiom pin.
3. **Model the deployed field from line one.** ℤ-for-BabyBear hid four verdict-A
   soundness gaps (balance-1 cell debits ~10⁹; a cap granting nothing authorizes a
   transfer). Retrofit cost ~220 files. → the field is a parameter instantiated once at
   the deployed value; toys are type-distinct from the soundness path.
4. **Bound ≠ forced, as types.** "Commitment binds X" is scaffolding; "the gate FORCES
   X" is where soundness lives (heap-root advance not matching heap content). → two
   types, no coercion, apexes only over the second.
5. **One executable tower.** Abstract towers quantifying over their own vocabulary are
   parallel proofs no live code runs (JointTurn/Coordination/Polis: 0 sorry, kernel-
   clean, disconnected). → abstraction = generalization of the live types; instance in
   the CI closure or it doesn't exist.
6. **Wire-first.** ~38 orphaned built-and-tested capabilities; a fee-DoS because
   `verify_stark()` was never called; dead wire vocabularies. → CI reachability gate;
   land the capability and its wire in the same commit.
7. **The claims ledger is generated and unparkable.** Namespace pins beat curated lists
   (batch pinned 108 where the hand list had 75 — "verbosity was hiding incomplete
   coverage"); parked pins were a tooling race leaking into the credibility artifact.
8. **Gate the gates.** CI dead five days = green; `| tail` eats exit codes; the guard
   ratchet's own baseline was launderable via a module split. → every gate red-proofs
   itself, distinguishes ran-from-passed, and its ledger self-verifies without git
   history. Loud escape hatches, never silent ones.
9. **`#guard` is silent `native_decide`.** Case-tests in Lean are still case-tests
   (848 of them = zero theorems about the subject). Prove the general fact; use guards
   as non-vacuity *witnesses*, graded and confessed (`#assert_compiled`).
10. **Refusal must be loud.** A leg the compiler can't lower becomes an unsatisfiable
    boundary pair, never silence — dropping is fail-open and no byte-golden sees it.
11. **Widen the source, not the emitter.** The compiler was fine; the source language
    couldn't SAY lookups/tables/ranges. One added word moved reach 25/76 → 76/76.
    "A `propBit` is a claim; the borrow chain is a proof."
12. **Bind the policy term, not the decision bit.** Today's circuit proves "the executor
    said admit," not "the policy held" — the seam where derived proofs stop being about
    the app.
13. **Emit, never imitate.** The hand-written descriptor corpus was internally
    inconsistent (37/58/25 rendering splits) — byte-agreement with it is ill-posed.
    One canonical normal form, true by construction. And **delete the twin** — the only
    move that changes the authorship count.
14. **Quote the pessimistic number of a pair.** (2^92.7 collision quoted as ~2^185
    second-preimage.) State covered scope in the same sentence as the claim
    ("KERNEL STARK-SOUNDNESS = 1/27" is the honest sentence).
15. **Cost estimate → constraint is the substitution to watch.** Invented constituencies
    ("existing signed witnesses") defer real fixes. If you ship a containment while
    naming the real fix as a later phase, the phases are backwards.
16. **One lane can hold it.** The 19-concurrent-lanes-one-tree process produced the
    parked pins, the baseline laundering, the committed merge conflicts. Minidregg's
    size target is also a *process* target.

## 7. The architecture carve

```
minidregg/
  Theory/        — candidate-independent core (~3-5K): verify/find seam, Holds,
                   GovernedDynamics, product camera, Verb=admission×Fpu, AmpClosed,
                   Frame/Knows/DistKnows, games, nuF. Import boundary MECHANICALLY
                   enforced (no concrete imports; CI-checked).
  Kernel/        — 3 primitives (create · gwrite · move) over the camera; state =
                   accounts + bal + caps + ONE keyed map (UKey address space);
                   4-leg gate; guard lattice (local ⊂ literal ⊂ +absence ⊂ +order);
                   Hyperedge as THE turn shape (a delegation forest is a tree-shaped
                   hyperedge — one model, not two). ~5-10K.
  Pred/          — ONE predicate algebra, syntactic AST end-to-end (no opaque functions
                   anywhere in the policy path), decidable eval, relational + quantified
                   closures as views with proven-equal denotation, the two dials
                   (ConfluenceClassifier, disclosure ladder) as computed prices. ~5K.
  Effects/       — the open handler registry: each effect ONE declaration (EffectSpec-
                   shaped: view, touched, leaf exprs, guard AST, δ, authority demand)
                   with ALL floor obligations as proof fields. From it, DERIVED:
                   (a) the IR term, (b) executor-equality, (c) the descriptor,
                   (d) the weld, (e) frame/reject teeth, (f) the witness generator.
  Compiler/      — the arithmetization spine: first-order IR with SYNTACTIC leaves;
                   one signature algebra; fold_unique as the single induction; seqDescr
                   as the target monoid; closed first-order descriptor type (v2-style:
                   tables + lookups + mem/map ops as first-class vocabulary, censused
                   against what targets actually need); derived canonical codec with a
                   generic round-trip theorem; decideVm-style decidable reference;
                   graduated optimization passes proved sound/complete/faithful.
                   Field-faithful (deployed prime as the one instantiation). ~15-25K.
  Assurance/     — generated: namespace pins, keystone audit (satisfiable+teeth+premise),
                   carrier registry with realizer slots, Bound/Forced types, floor doc
                   with both soundness numbers. No hand-maintained ledger anywhere.
  Distributed/   — blocklace + strand + LaceMerge + the finality gate (@[export] from
                   day one, fail-closed); Stingray budget; CapTP; migration. ~10K.
  Apps/          — factories + the widened toolkit; apps are declarations + RED
                   witnesses; contracts inherited. ~10K.
  Deos/          — the crown four + hyperdreggmedia (transclusion, DocMerge, fog-of-war,
                   affordance algebra) over the real substrate — no descriptor plumbing
                   in this namespace. ~10K.
  rust/          — interpreter + node + FFI marshalling ONLY. Authors nothing.
                   Every decision point is a Lean export or a Lean-emitted artifact.
```

Rough total: **100–150K lines** — half the budget, for the whole re-expression.

## 8. Open decisions (ember's to make)

1. **`verifyBatch` opaque vs modeled** — breadstuffs' one explicitly ember-gated call:
   (A) define `verifyBatch := verifyBatchModel` + KAT correspondence, or (B) keep opaque
   and name `StarkSound` as the explicit floor. Minidregg gets to choose *before* the
   import-cycle ripple exists.
2. **Proof system**: inherit Plonky3/BabyBear/FRI (and its conjectured-vs-Johnson floor,
   unaudited), or re-decide the backend while the descriptor interface is still ours.
3. **Turn model unification**: hyperedge-as-primitive with forests as tree instances is
   the carve above — worth a design pass on whether delegation edges stay *executed*
   attenuations (they should).
4. **Which frontier items become day-one features**: refusal-reason export over FFI
   ("every cheat is refused, with a witnessed reason" — the thesis, currently trapped
   behind a bare Bool); trace-shaped/causal guards; per-issuer-global conservation as
   the deployed ledger discipline (breadstuffs specified, never deployed).
5. **The Games/ question**: 98.6K lines unaudited in this pass; likely home of the
   largest duplication. Harvest lane needed before anything is carried over.
