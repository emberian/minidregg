# Loom — the formalization, and what "complete" honestly means

*Written to be handed to the skeptic who asks "you formalized a whole proof system — is it
actually done?" The honest answer has three parts: what is PROVED end-to-end, the IRREDUCIBLE
cryptographic FLOOR it stands on (named and inhabited, the same floor every hash-based SNARK
carries), and the BEYOND-v0 RESEARCH that genuinely remains. Status 2026-08-08. Every theorem
cited is machine-checked in Lean on the ATLAS axiom triple `[propext, Classical.choice,
Quot.sound]`, hand-audited (statement read, not just "it compiled"), with a built non-vacuity
witness — and where a claim has a false neighbor, the false statement is kept compiling beside
the true one so the true one means exactly what it says.*

## 0. The one honest sentence

**Loom's v0 soundness formalization is complete: a machine-checked chain from a kernel turn to a
light client that learns the whole federation history — accumulation, unbounded-depth recursion,
a non-interactive zero-knowledge argument of knowledge, a full-gate arithmetization retired by a
proven sumcheck, and a sound shielded note-spend — all derived so drift is structurally
impossible, standing on exactly three named, inhabited cryptographic assumptions and no more.**

It is NOT a working prover, it has NO benchmarks, and its rate<1 soundness rides one standing
proximity-gap hypothesis. Those are stated plainly below, not buried.

## 1. What is PROVED, end-to-end

**Accumulation + full recursion (the product's core promise).**
- `Loom/Accumulator`: the WARP-shape accumulated claim + the γ-fold, closure `foldClaims_satisfies`
  (CRS × CRS → CRS) — the chain is one accumulated object.
- `Loom/AccExtractChain.lean/lightClientKnowledgeSound`: **knowledge-soundness over the whole
  chain at arbitrary depth** — the extractor recovers every link's actual witness. Full recursion.
- `Loom/Depth.lean/OB2_depth_composition_nonneg_proved`: the whole-stack straightline depth
  composition — the theorem whose absence was breadstuffs' laundered `EngineSound`; its false
  form still compiles beside it.
- `Loom/LightClient.lean/lightClient_attests` + `LightClientSound/lightClientSound` +
  `LightClientFS/lightClientFS_sound`: the light client learns the whole history from one
  aggregate, at one Fiat-Shamir schedule, sound at `≤ n·(err⋆(δ)+1/|F|)`.
- `Assurance/LoomV0.loomV0_holds`: the **capstone** — a committed receipt chain verified at one
  FS schedule is sound + knowledge-sound + commitment-bound + decided, the proof term being
  exactly the four citations.
- `Loom/LightClientGrinding.lightClientGrinding_sound`: soundness against a **grinding** adversary
  (one that reorders/chooses the chain after querying the oracle) at the try-count-scaled bound —
  the prefix-correlation kept honest, `phantomGrind_beats_fixed_bound` proving no fixed-chain bound
  survives grinding.

**The zero-knowledge argument of knowledge (OB-4, confirmed-absent-from-the-literature).**
- `Loom/ZkRbrGame.loom_zk_argument`: Loom has a **machine-checked straightline non-interactive
  zero-knowledge argument of knowledge** for the accumulated claim — completeness, knowledge-
  soundness (via the two-point / chain extractor), zero-knowledge (perfect, via masked openings),
  round error on the proven `accRbrError` scale, FS-composed.
- `Loom/AccRbrInstance.accFsSound_native`: the argument is **fully native at the IOR resolution**
  — FS fires on the accumulator's own Def-4.2 instance (all Def-4.1 clauses + `extract_sound`
  proved), not a placeholder.
- The novel content resolved along the way: `ZkExtraction` (the mask counterfactuals the
  extractor needs are provably not computable from what the ZK distinguisher sees — quantifier
  position confines them, `by rfl`); `ZkTriangular` (the deployed recommitment hiding, the
  backward induction through the ∀-witness quantifier closes); `ConstrainedMask` (a mask that
  respects the claim AND still hides).

**The arithmetization compiler (the "make it real" spine, DERIVED).**
- `Compiler/Air`: an arithmetization DSL whose circuit reading and executor reading are proved
  EQUAL by initiality (`eval_agrees_exec`, on `[propext, Quot.sound]` — no choice; drift is not
  avoided, it is impossible). This is N3 applied to arithmetization.
- `Compiler/AirFlatten`: nested expressions → a degree-≤2 gate system with aux wires, wire-forcing
  proved.
- `Assurance/AirSumcheck` + `AirSumcheckQuadratic/airGateSystem_sound`: the FULL gate system
  (linear ∧ quadratic) is retired by Loom's **proven** sumcheck — no unretired channel. The
  derived arithmetization inherits the proof system's soundness, completely.
- `Loom/MultilinearExtension`: the MLE (`[SC-reshape]` discharged), uniqueness and all.

**The sound shielded note-spend (the private-witness turn, SOUNDLY CONSTRAINING).**
- Gadgets, all derived + iff-correct: `AirRange` (value range), `AirHash` (Poseidon-style
  permutation, all rounds), `AirMembership` (Merkle, general depth).
- `Compiler/NoteSpend.noteSpend_correct` + `noteSpend_binds`: the composed system accepts iff a
  VALID shielded spend (value bounded ∧ nullifier = hash(note) ∧ note committed in the tree) — a
  satisfying assignment IS a valid spend. It even exhibits a toy-hash collision to make
  `[COMMIT-CR]`'s necessity visible.
- The private-witness arc, machine-checked end-to-end: **hides** (`Assurance/PrivateReceipt`,
  `PrivateTurn`, `Kernel/PrivateTurn`), **soundly constrains** (`NoteSpend`), **proved in ZK**
  (`loom_zk_argument`).

**The kernel (the semantic substrate).** `Camera` (resource algebra), `State`, `Turn` (the
hyperedge), `TurnLimit` (N2a — the turn's agreement half is a universal object), `TurnBalancedLimit`
(N2b — the conserving turn is universal), `Receipt` (OB-3, the receipt is the accumulator's word),
`Verbs` (create/gwrite/move conservation algebra), `PrivateTurn` (the hidden-witness turn).

## 2. The IRREDUCIBLE cryptographic FLOOR (named, inhabited, not eliminable)

These are assumptions, not gaps. Every hash-based SNARK stands on the same three. "Finishing"
means keeping them minimal, named, and *inhabited* — never an unproved `axiom`, never
`StarkSound`-with-zero-instances.

- **`[PROX-fold-distance]` — the proximity-gap hypothesis** (`IsProximityGenerator`, WHIR Thm 4.8
  / BCIKS). The rate<1 soundness rides it. Proven unconditionally at exact-membership (the trivial
  rate→1 corner); at deployed rates it is the standing hypothesis the whole tree carries. (Sobering
  context: the predecessor line had a *conjectured* 130-bit bound disproved to a proven 73 in Nov
  2025 — this is the least-reported, most load-bearing axis in the transparent-STARK field, and we
  quote it.)
- **`[FS-ROM]` — the sponge realizes the random oracle.** Inhabited by `Oracle.empty` (a lazy-
  sampling handler, no axiom).
- **`[COMMIT-CR]` — the hash is collision-resistant.** The `BindingCommitment` abstraction is
  inhabited **axiom-free** by `idealCommitment`; binding is proven load-bearing (an equivocating
  scheme breaks the extraction seam); `NoteSpend` exhibits a collision to make the assumption's
  necessity concrete.

## 3. BEYOND-v0 RESEARCH honestly remaining (Lean-authorable, not done)

- **`[ZK-RBR-extract]` lemma A** — the sub-unique-decoding seam: recovering the recommitment
  increment from `t < d` opened columns via mutual correlated agreement (the ZK argument's
  soundness at UD is complete; below UD is this lemma). Beyond-UD list-decoding math.
- **`[ACC-rbr-bcs]`** — the BCS/root-alphabet packaging of the native RBR instance (PMsg = root +
  opened columns rather than the full word). All the algebra is landed (ZkExtraction/Commitment);
  the packaging re-run at that alphabet remains.
- **`[ACC-sound-list]` / Johnson regime, `[OB-8-tower]` / binary tower** — everything is proved at
  *unique decoding* (the conservative ~2–4× regime); the better-rate Johnson regime and the
  Binius-style binary-tower arithmetic are named, not proved.

## 4. What "complete" does NOT include (the pessimistic column)

- **No prover, no verifier implementation, no benchmarks. Performance is UNMEASURED.** This is a
  soundness SPECIFICATION — theorems about what the protocol guarantees — not running code. The
  deployed compute (breadstuffs' WGPU BabyBear⁴ FRI fold) is exactly what these theorems cover, but
  the emit path (Lean → constraint artifact → prover) is not built.
- **Proven parameters only, unique-decoding regime.** No number on this label is a conjecture.
- The one-transcript soundness/knowledge fusion (`loomV0_holds` bundles four separate guarantees)
  and the FS-derived (vs uniform) schedule are proved at their stated resolutions; the deployment
  fusions are the named residuals above.

**The defensible one-breath claim:** *we did not build a faster SNARK; we built a proof system
whose soundness — accumulation, unbounded recursion, a zero-knowledge argument of knowledge, and a
sound shielded turn — is a machine-checked Lean term standing on three named cryptographic
assumptions, derived so the circuit can't drift from the semantics, honest enough to keep its own
false theorems compiling in the margin. What remains is a prover, benchmarks, and two named pieces
of beyond-unique-decoding mathematics — and we say so.*
