/-
# `Assurance/SelvageV0.lean` — the v0 CAPSTONE: the whole Selvage tower, one theorem.

The end-to-end composition (docs/SELVAGE-RECOMPOSITION.md, docs/HYPEREDGE-DESIGN.md):
a committed chain of KERNEL RECEIPTS, verified by the light client at ONE
Fiat–Shamir schedule, attests the whole history — soundly, knowledge-soundly,
bound to the commitment, and decided. Every clause of that sentence is a
LANDED theorem; this file's only job is to CITE them together, at ONE shared
final accumulator, so a skeptic can read one bundle instead of five files.

**No new math.** `SelvageV0Guarantee` is a `Prop`-valued structure whose four
fields are, verbatim, the conclusions of:

  * `Selvage.lightClientSound`      (`Selvage/LightClientSound.lean`) — SOUNDNESS,
  * `Selvage.lightClientKnowledgeSound_oneProver_committed`
    (`Selvage/LightClientKnowledge.lean`) — KNOWLEDGE, about the SAME prover,
  * `Selvage.committed_extract_bind` (`Selvage/Commitment.lean`) — BINDING,
  * `Selvage.decider_sound`         (`Selvage/Decider.lean`) — DECISION,

the first two at ONE prover (its committed words `ms`, genesis word `f₀`, and
the opened columns `cols` of its recommitted partial folds), the last two at
ONE final accumulator `aggregate foldRoot γs A₀ ch` — the object the light
client's one-time decider pass actually checks (`Selvage/Decider.lean`'s
D_ACC). `loomV0_holds` PROVES the bundle by forwarding every landed hypothesis
to its theorem; the proof term is literally `⟨lightClientSound …,
lightClientKnowledgeSound_oneProver_committed …, committed_extract_bind …,
decider_sound …⟩`.

**The receipt bridge** (§1): `Assurance/ReceiptClaim.lean` already proved that
one kernel receipt IS a native Selvage accumulated claim (`ReceiptClaim.acc`).
`receiptLink`/`receiptChain` here are the remaining bookkeeping — wrapping a
list of receipts with their pre/post state roots into a `Selvage.Chain` — so
"history of kernel receipts" and "the `Chain` the light client aggregates"
are the SAME object, not merely analogous ones.

**Honest scope, stated once here and not re-litigated per field below**: every
theorem cited is proved over the STRICT/word-level relation
(`AccClaim.Satisfies`, exact membership + exact channel equality) and the
IDEALIZED commitment layer (`BindingCommitment`, inhabited by the identity
scheme). What the capstone does NOT manufacture — the deployment realizers —
is named plainly in the residual block at the end of this file. This file
proves the PROVED tower composes; it does not shrink what remains.
-/
import Assurance.ReceiptClaim
import Selvage.LightClientSound
import Selvage.LightClientKnowledge
import Selvage.Decider
import Selvage.Commitment

namespace Minidregg.Assurance

open Minidregg.Kernel Minidregg.Selvage

/-! ## §1. The composition primitive — a receipt history IS a light-client chain

`ReceiptClaim.acc` (`Assurance/ReceiptClaim.lean`, OB-3) proved that ONE kernel
receipt, over a window `w`, is a native `AccClaim Root F (FlatIx w)
(ixList w).length`. Wrapping a SEQUENCE of receipts with the pre/post state
roots each committed turn claims turns that into a `Selvage.Chain` — exactly the
object `Selvage/LightClient.lean` aggregates. Bookkeeping only: no algebra here,
the fold/soundness/knowledge/binding content is entirely the four theorems
cited below. -/

variable {F : Type} [Field F] [DecidableEq F] {w : Window} {Root : Type}

/-- **One committed turn as a light-client link**: the receipt claim
(`ReceiptClaim.acc`) plus the pre/post roots the chain seam pins together.
The claim's OWN commitment root is `post` — the receipt commits to the state
IT PRODUCED, so a fold's recommitment and the next link's `pre` are the same
datum by convention (matching `Selvage/LightClient.lean`'s `LCExample`, where
`claim.rt = link.post` throughout). -/
noncomputable def receiptLink (pre post : Root) (rc : ReceiptClaim w F) :
    Selvage.Link Root F (FlatIx w) (ixList w).length :=
  ⟨pre, post, rc.acc post⟩

/-- **A receipt history, as a `Chain`**: a list of (pre-root, post-root,
receipt claim) turns, oldest first — `List ReceiptClaim` (with their roots)
mapped through `.acc` into `Selvage.Chain`, the object the whole tower below
consumes. -/
noncomputable def receiptChain (turns : List (Root × Root × ReceiptClaim w F)) :
    Selvage.Chain Root F (FlatIx w) (ixList w).length :=
  turns.map fun t => receiptLink t.1 t.2.1 t.2.2

@[simp] theorem receiptChain_nil :
    receiptChain (Root := Root) (w := w) (F := F) [] = [] := rfl

@[simp] theorem receiptChain_cons (pre post : Root) (rc : ReceiptClaim w F)
    (turns : List (Root × Root × ReceiptClaim w F)) :
    receiptChain ((pre, post, rc) :: turns)
      = receiptLink pre post rc :: receiptChain turns := rfl

theorem receiptChain_length (turns : List (Root × Root × ReceiptClaim w F)) :
    (receiptChain turns).length = turns.length := List.length_map ..

/-! ## §2. `SelvageV0Guarantee` — the end-to-end bundle, statement-first

Four fields, one per landed theorem. `sound` and `knowledge` are both events
over ONE uniformly sampled schedule about ONE prover — the words `ms` it
committed (one per link), its genesis word `f₀`, and the columns `cols γv` it
opens of its recommitted partial folds at the sampled schedule `γv`.
`binding` and `decision` are at the shared final accumulator
`A := aggregate foldRoot γs A₀ ch` — the object `Selvage/Decider.lean`'s D_ACC
actually checks. Every field's TYPE is a landed theorem's conclusion, verbatim
(compare each to the docstring citation). -/

/-- **The v0 Selvage guarantee.** A history `ch` (in practice: `receiptChain` —
a chain of kernel receipts) aggregated from genesis `A₀` under `foldRoot`,
checked by the light client at ONE Fiat–Shamir schedule:

* `sound` — `Selvage.lightClientSound`: a chain carrying a δ-far-false CLAIMED
  link (the prover's own committed words, anchored at
  `foldWords … f₀ (List.ofFn ms)`) survives verification at one uniformly
  sampled schedule with probability at most `n · (err⋆(δ) + 1/|F|)`.
* `knowledge` — `Selvage.lightClientKnowledgeSound_oneProver_committed`: for
  the SAME prover's data, the probability that its base transcript δ-verifies
  AND the one-execution extractor `lcExtract` (fed the base word and the
  columns `cols γv` the prover opened, bound to its recommitment roots) fails
  to deliver an attestation with linkwise δ-close witnesses is at most
  `n · (err⋆(δ) + 2/|F|)`. No separately-given transcript family: the `n + 1`
  counterfactual transcripts of `lightClientKnowledgeSound` are synthesized
  from this one execution's opened columns (`seamCounterfactual`).
* `binding` — `Selvage.committed_extract_bind` at the final accumulator `A`: a
  word `e` fully opened from `A`'s root against a `BindingCommitment` IS the
  word `w` the prover committed, and satisfaction transfers to it.
* `decision` — `Selvage.decider_sound` at `A`: the light client's one-time check
  (D_ACC) accepts exactly the claim, nothing more, nothing less.

`sound` and `knowledge` share `f₀`/`ms`/`cols`: the coupling the previous
revision of this file named as `[ACC-extract-bind]`'s job ("a single prover's
data feeding BOTH roles at once under one FS execution") is
`lightClientKnowledgeSound_oneProver_committed`, at the word level and unique
decoding; the FS transport of the sampled schedule stays `[FS-ROM]`. -/
structure SelvageV0Guarantee {Root : Type*} {F : Type} [Field F] {ι : Type*}
    {r : ℕ} {Op : Type*} [Fintype F] [Nonempty ι] [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (foldRoot : Root → F → Root → Root) (C : Submodule F (ι → F))
    (A₀ : AccClaim Root F ι r) (ch : Chain Root F ι r)
    (δ : ℝ) (errstar : ℝ → ℝ) (f₀ : ι → F) (ms : Fin ch.length → ι → F)
    (dom : ι ↪ F) (d : ℕ) {t : ℕ} (q : Fin t → ι)
    (cols : (Fin ch.length → F) → ℕ → Fin t → F) (γs : ℕ → F)
    (S : BindingCommitment Root F ι Op) (w e f : ι → F) : Prop where
  /-- **Soundness** (`lightClientSound`). -/
  sound : uniformProb (Fin ch.length → F) (fun γv =>
      ∃ u, relDist (foldWords (padSched γv) f₀ (List.ofFn ms)) u ≤ δ ∧
        AccClaim.Satisfies C (aggregate foldRoot (padSched γv) A₀ ch) u)
    ≤ (ch.length : ℝ) * (errstar δ + 1 / (Fintype.card F : ℝ))
  /-- **Knowledge soundness** (`lightClientKnowledgeSound_oneProver_committed`),
  about the same prover. -/
  knowledge : uniformProb (Fin ch.length → F) (fun γv =>
      (∃ u, relDist (foldWords (padSched γv) f₀ (List.ofFn ms)) u ≤ δ ∧
        AccClaim.Satisfies C (aggregate foldRoot (padSched γv) A₀ ch) u) ∧
      ¬ (attests C ch ∧
        List.Forall₂ (fun l u => ∃ v, relDist u v ≤ δ ∧ AccClaim.Satisfies C l.claim v)
          ch (lcExtract dom d q ch.length (padSched γv)
            (foldWords (padSched γv) f₀ (List.ofFn ms)) (cols γv))))
    ≤ (ch.length : ℝ) * (errstar δ + 2 / (Fintype.card F : ℝ))
  /-- **Binding to the commitment** (`committed_extract_bind`), at the final
  accumulator `aggregate foldRoot γs A₀ ch`. -/
  binding : e = w ∧
    AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch) w
  /-- **Decision** (`decider_sound`), at the same final accumulator: the
  decider's verdict IS the claim. -/
  decision : decider C (aggregate foldRoot γs A₀ ch) f
    ↔ AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch) f

/-! ## §3. `loomV0_holds` — the composition theorem

Every hypothesis of the four landed theorems, forwarded (no new math): the
proof term is exactly the four citations, one per field. The hypotheses are
grouped by which field they discharge, matching the docstring above;
soundness and knowledge share the prover's data and the mutual-CA regime. -/

/-- **`loomV0_holds`.** Given every hypothesis `lightClientSound`,
`lightClientKnowledgeSound_oneProver_committed`, `committed_extract_bind`, and
`decider_sound` ask for — forwarded, not re-derived — the bundle fires. This
IS the composition: no algebra beyond the four citations. -/
theorem loomV0_holds {Root : Type*} {F : Type} [Field F] {ι : Type*} {r : ℕ}
    {Op : Type*} [Fintype F] [Nonempty ι] [Fintype ι] [DecidableEq ι] [DecidableEq F]
    {foldRoot : Root → F → Root → Root} {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    {δ dC Bstar : ℝ} {errstar : ℝ → ℝ} {f₀ : ι → F} {ms : Fin ch.length → ι → F}
    -- the regime shared by soundness and knowledge
    (halign : Aligned A₀ ch)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2)
    (herr0 : 0 ≤ errstar δ)
    -- soundness (`lightClientSound`): a δ-far-false committed word
    (hfalse : ∃ p ∈ ch.zip (List.ofFn ms), ∀ v ∈ C, relDist p.2 v ≤ δ →
      ¬ AccClaim.Satisfies C p.1.claim v)
    -- knowledge (`lightClientKnowledgeSound_oneProver_committed`): the seam
    (hseam : SeamOk ch) {dom : ι ↪ F} {d t : ℕ} (hdt : d ≤ t) {q : Fin t → ι}
    (hq : Function.Injective (dom ∘ q))
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    {S : BindingCommitment Root F ι Op}
    {rts : (Fin ch.length → F) → ℕ → Root}
    {cols : (Fin ch.length → F) → ℕ → Fin t → F}
    {ops : (Fin ch.length → F) → ℕ → Fin t → Op}
    (hrts : ∀ (γv : Fin ch.length → F) (c : ℕ), c ≤ ch.length →
      rts γv c = S.commit (partialFold (padSched γv) f₀ ms c))
    (hver : ∀ (γv : Fin ch.length → F) (c : ℕ), c ≤ ch.length → ∀ j,
      S.verifyOpen (rts γv c) (q j) (cols γv c j) (ops γv c j))
    -- binding (`committed_extract_bind`), at the schedule-`γs` accumulator
    {γs : ℕ → F} {w e : ι → F} {oe : ι → Op}
    (hrt : (aggregate foldRoot γs A₀ ch).rt = S.commit w)
    (hopen : ∀ i, S.verifyOpen (aggregate foldRoot γs A₀ ch).rt i (e i) (oe i))
    (hsat : AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch) e)
    -- decision (`decider_sound`) is unconditional; `f` is free
    (f : ι → F) :
    SelvageV0Guarantee foldRoot C A₀ ch δ errstar f₀ ms dom d q cols γs S w e f where
  sound := lightClientSound foldRoot (f₀ := f₀) halign hdC hMCA hδ0 hδB hδC herr0
    (by simp) hfalse
  knowledge := lightClientKnowledgeSound_oneProver_committed foldRoot halign hseam
    hdC hMCA hδ0 hδB hδC herr0 S dom hdt hq hms hrts hver
  binding := committed_extract_bind S hrt hopen hsat
  decision := decider_sound C (aggregate foldRoot γs A₀ ch) f

/-! ## §4. `loomV0_light_client` — the defensibility one-liner -/

/-- **THE ONE-LINER.** Checking the aggregate accumulated claim of a receipt
history at ONE Fiat–Shamir schedule (plus the decidable seam) is SOUND: a
history carrying a δ-far-false receipt survives that one check with
probability at most `n · (err⋆(δ) + 1/|F|)`. This is `lightClientSound`,
re-exported at the capstone's name for legibility — a citation, not new math;
the contrapositive-probabilistic reading of `Selvage.lightClient_attests`'
∀-schedule apex (`Selvage/LightClient.lean`), discharged by one draw at this
price. -/
theorem loomV0_light_client {Root : Type*} {F : Type} [Field F] {ι : Type*}
    {r : ℕ} [Fintype F] [Nonempty ι] [Fintype ι] [DecidableEq ι] [DecidableEq F]
    {foldRoot : Root → F → Root → Root}
    {C : Submodule F (ι → F)} {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    {ws : List (ι → F)} {f₀ : ι → F} {δ dC Bstar : ℝ} {errstar : ℝ → ℝ}
    (halign : Aligned A₀ ch)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2)
    (herr0 : 0 ≤ errstar δ) (hlen : ws.length = ch.length)
    (hfalse : ∃ p ∈ ch.zip ws, ∀ v ∈ C, relDist p.2 v ≤ δ →
      ¬ AccClaim.Satisfies C p.1.claim v) :
    uniformProb (Fin ch.length → F) (fun γv =>
        ∃ u, relDist (foldWords (padSched γv) f₀ ws) u ≤ δ ∧
          AccClaim.Satisfies C (aggregate foldRoot (padSched γv) A₀ ch) u)
      ≤ (ch.length : ℝ) * (errstar δ + 1 / (Fintype.card F : ℝ)) :=
  lightClientSound foldRoot halign hdC hMCA hδ0 hδB hδC herr0 hlen hfalse

/-! ## §5. Keystones — the capstone FIRES on a built receipt history

ATLAS law 2 (satisfiable + teeth + premise-inhabitation), at the RECEIPT
instance the capstone was written for. `Assurance/ReceiptClaim.lean`'s own
F₅ keystone objects (`w₀`, `rcHonest`, `rcSpent`, …) are FILE-PRIVATE, so
this section rebuilds an equally small instance from the same PUBLIC
vocabulary (`Window`, `KernelState`, `ReceiptClaim`, `flatten`,
`ReceiptClaim.acc`, `receiptClaim_folds`) — same shape, same technique
(anti-ghost: nullifier unspent → spent), nothing reused by name that could
not be. -/

namespace SelvageV0Example

open Selvage.LCExample

/-- The keystone window: no cells, one key — `FlatIx` is exactly the
presence-bit/value pair, `Fintype.card = 2` (the same shape as
`Assurance/ReceiptClaim.lean`'s private keystone window). -/
def w₁ : Window := ⟨∅, {UKey.nullifier 11}⟩

theorem card_FlatIx_w₁ : Fintype.card (FlatIx w₁) = 2 := by decide

instance : Nonempty (FlatIx w₁) := ⟨Sum.inr (⟨UKey.nullifier 11, by decide⟩, 0)⟩

/-- Genesis kernel state: the nullifier unspent. -/
def k₁ : KernelState := ⟨∅, fun _ _ => 0, fun _ => [], fun _ => none⟩

/-- The next turn's kernel state: the nullifier now spent — `some 0`, the
anti-ghost target `Kernel/Receipt.lean`/`Assurance/ReceiptClaim.lean` guard
against conflating with `none`. -/
def k₁spent : KernelState :=
  { k₁ with umap := fun u => if u = UKey.nullifier 11 then some 0 else none }

/-- The genesis receipt: the word IS the flattening, by construction. -/
def rc₁ : ReceiptClaim w₁ (ZMod 5) := ⟨k₁, flatten w₁ k₁, rfl⟩

/-- The second turn's receipt. -/
def rc₂ : ReceiptClaim w₁ (ZMod 5) := ⟨k₁spent, flatten w₁ k₁spent, rfl⟩

/-- Roots live in the word space itself — `Selvage/Commitment.lean`'s
inhabitation witness, the identity commitment: a receipt's root IS its
flattened word. -/
def S₁ : BindingCommitment (FlatIx w₁ → ZMod 5) (ZMod 5) (FlatIx w₁) Unit :=
  idealCommitment (ZMod 5) (FlatIx w₁)

/-- The recommitment schedule: under the identity commitment, recommitting
a fold IS adding the words — `foldRoot a γ b := a + γ • b` — so a fold's
claimed root and the honestly-folded word coincide BY CONSTRUCTION (WARP's
"the prover recommits the folded word", made literal, not assumed). -/
def foldRoot₁ : (FlatIx w₁ → ZMod 5) → ZMod 5 → (FlatIx w₁ → ZMod 5)
    → (FlatIx w₁ → ZMod 5) :=
  fun a γ b => a + γ • b

def rt₁ : FlatIx w₁ → ZMod 5 := flatten w₁ k₁
def rt₂ : FlatIx w₁ → ZMod 5 := flatten w₁ k₁spent

/-- The genesis accumulated claim: the first receipt, rooted at its own
commitment. -/
noncomputable def A₀₁ :
    AccClaim (FlatIx w₁ → ZMod 5) (ZMod 5) (FlatIx w₁) (ixList w₁).length :=
  rc₁.acc rt₁

/-- The one-link receipt history `k₁ → k₁spent`, via `receiptChain` — a
genuine `List ReceiptClaim` (with roots) mapped through `.acc`. -/
noncomputable def ch₁ :
    Chain (FlatIx w₁ → ZMod 5) (ZMod 5) (FlatIx w₁) (ixList w₁).length :=
  receiptChain [(rt₁, rt₂, rc₂)]

theorem ch₁_length : ch₁.length = 1 := receiptChain_length _

/-- The full code `⊤`: every membership hypothesis of `receiptClaim_folds`
discharges for free, keeping this keystone's arithmetic small. (The rate<1
refinement — `Assurance/ReceiptClaim.lean`'s `[OB3-c-prox]`, checking
`ReceiptClaim.proxAccepts` against a PROPER code via the FRI/WHIR descent —
is CLOSED there at exact-membership; this capstone keystone simply doesn't
need it, since `receiptClaim_folds`/`lightClientSound`/
`lightClientKnowledgeSound` all take `C` as a free submodule.) -/
def C₁ : Submodule (ZMod 5) (FlatIx w₁ → ZMod 5) := ⊤

theorem ch₁_aligned : Aligned A₀₁ ch₁ := by
  intro l hl i
  have hl' : l = receiptLink rt₁ rt₂ rc₂ := by
    simpa [ch₁, receiptChain] using hl
  subst hl'
  exact ReceiptClaim.acc_weights_shared rc₁ rc₂ rt₁ rt₂ i

theorem ch₁_seamOk : SeamOk ch₁ := by
  show SeamOk [receiptLink rt₁ rt₂ rc₂]
  exact seamOk_singleton _

theorem A₀₁_verifies : Verifies C₁ A₀₁ :=
  ⟨_, rc₁.acc_self rt₁ Submodule.mem_top⟩

/-- Every schedule folds the two receipts to a satisfied claim — the
γ-fold's closure theorem (`receiptClaim_folds`) reused verbatim at `γ := γs
0`, code membership free at `C₁ = ⊤`. -/
theorem ch₁_verifies_forall (γs : ℕ → ZMod 5) :
    Verifies C₁ (aggregate foldRoot₁ γs A₀₁ ch₁) := by
  show Verifies C₁ (aggregate foldRoot₁ γs A₀₁ [receiptLink rt₁ rt₂ rc₂])
  exact ⟨_, receiptClaim_folds foldRoot₁ rc₁ rc₂ rt₁ rt₂ (γs 0)
    Submodule.mem_top Submodule.mem_top⟩

/-- **Premise inhabitation, the deterministic apex fires on a genuine receipt
chain**: `lightClient_attests` (the ∀-schedule apex of `Selvage/LightClient.lean`)
applied to receipt-derived data — every hypothesis discharged by the objects
above, nothing vacuous. The receipt history genuinely attests. -/
theorem ch₁_attests : attests C₁ ch₁ :=
  lightClient_attests foldRoot₁ ch₁_aligned A₀₁_verifies ch₁_seamOk
    ch₁_verifies_forall

/-! ### The one prover — ghost-replay data feeding `sound` AND `knowledge`

`sound` and `knowledge` anchor at ONE prover. The keystone prover CLAIMS link
0's word is still `rt₁` — the genesis word, i.e. the nullifier UNSPENT —
instead of the honest `rt₂` (spent): the anti-ghost attack
`Assurance/ReceiptClaim.lean`'s presence bit was built to catch, cast as the
light client's soundness event AND as the one-execution extractor's input. -/

/-- The ghost prover's committed word list: `rt₁` at the one link. -/
def ms₁ : Fin ch₁.length → FlatIx w₁ → ZMod 5 := fun _ => rt₁

/-- The base schedule: constant `1`. -/
def γbase₁ : ℕ → ZMod 5 := fun _ => 1

/-- The erasure-decoding domain for the seam: the two flat coordinates
embedded as `{0, 1} ⊂ F₅` (`w₁` has no cells; the `inl` branch is never
inhabited). Injectivity by `decide`. -/
def dom₁ : FlatIx w₁ ↪ ZMod 5 :=
  ⟨Sum.elim (fun _ => 4) (fun p => ((p.2 : ℕ) : ZMod 5)), by decide⟩

/-- The opened positions: both flat coordinates — `t = d = 2`, full rate, the
seam decodes every word from its two symbols. -/
def q₁ : Fin 2 → FlatIx w₁ := fun b => Sum.inr (⟨UKey.nullifier 11, by decide⟩, b)

theorem q₁_inj : Function.Injective (dom₁ ∘ q₁) := by decide

/-- At full rate the RS code over the two flat coordinates is everything
(`reedSolomonCode_card_eq_top`): every word — the ghost word included — is a
codeword for the seam. -/
theorem ms₁_mem : ∀ k, ms₁ k ∈ reedSolomonCode dom₁ 2 := by
  intro k
  have htop := reedSolomonCode_card_eq_top dom₁
  rw [card_FlatIx_w₁] at htop
  rw [htop]
  exact Submodule.mem_top

/-- The ghost prover's recommitment roots under the identity commitment: the
partial folds themselves. -/
noncomputable def rts₁ (γv : Fin ch₁.length → ZMod 5) : ℕ → FlatIx w₁ → ZMod 5 :=
  fun c => S₁.commit (partialFold (padSched γv) 0 ms₁ c)

/-- The ghost prover's opened columns: its partial folds' symbols at `q₁`. -/
noncomputable def cols₁ (γv : Fin ch₁.length → ZMod 5) : ℕ → Fin 2 → ZMod 5 :=
  fun c j => partialFold (padSched γv) 0 ms₁ c (q₁ j)

/-- The ghost claim `rt₁` and the honest post-word `rt₂` differ AT the
presence-bit coordinate — the exact anti-ghost tooth of
`Assurance/ReceiptClaim.lean`'s `flatten_tamper_changes`, recomputed for
`w₁`: `k₁`'s unspent `none` versus `k₁spent`'s spent `some 0`. -/
theorem rt₁_ne_rt₂_pt :
    rt₁ (Sum.inr (⟨UKey.nullifier 11, by decide⟩, 0))
      ≠ rt₂ (Sum.inr (⟨UKey.nullifier 11, by decide⟩, 0)) := by
  show flatten (F := ZMod 5) w₁ k₁ _ ≠ flatten (F := ZMod 5) w₁ k₁spent _
  decide

theorem rt₁_ne_rt₂ : rt₁ ≠ rt₂ := fun h => rt₁_ne_rt₂_pt (congrFun h _)

theorem hmax₁ :
    max (1 - 1 / (Fintype.card (FlatIx w₁) : ℝ) / 2) 0 = 3 / 4 := by
  rw [card_FlatIx_w₁]; norm_num

theorem hMCA₁ :
    HasMutualCorrelatedAgreement (affineGenerator (ZMod 5)) C₁ (3 / 4)
      (fun _ => 0) := by
  rw [← hmax₁]; exact hasMutualCorrelatedAgreement_top_affine

/-- The ghost word is δ-far-false at the one link: every δ-close word (there is
only `rt₁` itself, by quantization) violates the spent-receipt claim. -/
theorem ch₁_hfalse :
    ∃ p ∈ ch₁.zip (List.ofFn ms₁), ∀ v ∈ C₁,
      relDist p.2 v ≤ (1 / 8 : ℝ) → ¬ AccClaim.Satisfies C₁ p.1.claim v := by
  refine ⟨(ch₁.get ⟨0, by rw [ch₁_length]; omega⟩, rt₁),
    zip_ofFn_mem ch₁ ms₁ ⟨0, by rw [ch₁_length]; omega⟩, ?_⟩
  intro v _ hclose hsat
  have hsat' : AccClaim.Satisfies C₁ (rc₂.acc rt₂) v := hsat
  have hv : v = rt₂ :=
    ((ReceiptClaim.acc_satisfies_iff (C := C₁) rc₂ rt₂ (f := v)).mp hsat').2
  have hfar : (1 : ℝ) / 2 ≤ relDist rt₁ v :=
    hv ▸ one_div_card_le_relDist (F := ZMod 5) rt₁_ne_rt₂
  linarith

/-- **[SelvageV0-teeth] premise inhabitation, soundness fires**: `lightClientSound`
applied to the ghost prover's word — every hypothesis (alignment, the
δ-far falsity of the replayed claim, the MCA regime) discharged concretely,
bound `1 · (0 + 1/5) = 1/5`. The receipt chain's PROBABILISTIC guarantee is
non-vacuous: this is exactly the event `[ACC-sound]`/`[LC-sound]` bound, cast
at a real receipt history. -/
theorem ch₁_sound_fires :
    uniformProb (Fin ch₁.length → ZMod 5) (fun γv =>
        ∃ u, relDist (foldWords (padSched γv) (0 : FlatIx w₁ → ZMod 5) (List.ofFn ms₁)) u
            ≤ (1 / 8 : ℝ) ∧
          AccClaim.Satisfies C₁ (aggregate foldRoot₁ (padSched γv) A₀₁ ch₁) u)
      ≤ (ch₁.length : ℝ) * ((0 : ℝ) + 1 / (Fintype.card (ZMod 5) : ℝ)) :=
  lightClientSound foldRoot₁ ch₁_aligned (minDistLB_inhabited C₁) hMCA₁
    (by norm_num) (by norm_num) (by rw [card_FlatIx_w₁]; norm_num) (le_refl 0)
    (by simp) ch₁_hfalse

/-- **Premise inhabitation, knowledge**: the one-prover apex fires on the
receipt chain with the SAME ghost prover's data — seam, the seam's
preconditions (`dom₁`/`q₁`/full-rate membership), the identity commitment's
openings of its own partial folds — bound `1 · (0 + 2/5) = 2/5`. -/
theorem ch₁_knowledge_fires :
    uniformProb (Fin ch₁.length → ZMod 5) (fun γv =>
        (∃ u, relDist (foldWords (padSched γv) (0 : FlatIx w₁ → ZMod 5) (List.ofFn ms₁)) u
            ≤ (1 / 8 : ℝ) ∧
          AccClaim.Satisfies C₁ (aggregate foldRoot₁ (padSched γv) A₀₁ ch₁) u) ∧
        ¬ (attests C₁ ch₁ ∧
          List.Forall₂ (fun l u => ∃ v, relDist u v ≤ (1 / 8 : ℝ) ∧
              AccClaim.Satisfies C₁ l.claim v) ch₁
            (lcExtract dom₁ 2 q₁ ch₁.length (padSched γv)
              (foldWords (padSched γv) (0 : FlatIx w₁ → ZMod 5) (List.ofFn ms₁))
              (cols₁ γv))))
      ≤ (ch₁.length : ℝ) * ((0 : ℝ) + 2 / (Fintype.card (ZMod 5) : ℝ)) :=
  lightClientKnowledgeSound_oneProver_committed foldRoot₁ ch₁_aligned ch₁_seamOk
    (minDistLB_inhabited C₁) hMCA₁ (by norm_num) (by norm_num)
    (by rw [card_FlatIx_w₁]; norm_num) (le_refl 0) S₁ dom₁ le_rfl q₁_inj ms₁_mem
    (rts := rts₁) (ops := fun _ _ _ => ()) (fun _ _ _ => rfl)
    (fun γv c _ j => S₁.verifyOpen_commit (partialFold (padSched γv) 0 ms₁ c) (q₁ j))

/-! ### Binding and decision — the final accumulator's root IS the committed fold -/

/-- The honest γ=1 fold verifies the final accumulator: the word the
binding/decision slices open. -/
theorem ch₁_hbase :
    AccClaim.Satisfies C₁ (aggregate foldRoot₁ γbase₁ A₀₁ ch₁)
      (rt₁ + (1 : ZMod 5) • rt₂) := by
  show AccClaim.Satisfies C₁
    (aggregate foldRoot₁ γbase₁ A₀₁ [receiptLink rt₁ rt₂ rc₂])
    (rt₁ + (1 : ZMod 5) • rt₂)
  exact receiptClaim_folds foldRoot₁ rc₁ rc₂ rt₁ rt₂ 1
    Submodule.mem_top Submodule.mem_top

/-- The final accumulator's root, computed: under `foldRoot₁`'s literal
word-addition recommitment, the base-schedule fold's root IS the base
transcript's word — the prover's recommitment and the honest fold coincide
BY CONSTRUCTION. -/
theorem ch₁_final_rt :
    (aggregate foldRoot₁ γbase₁ A₀₁ ch₁).rt = rt₁ + (1 : ZMod 5) • rt₂ := by
  show (aggregate foldRoot₁ γbase₁ A₀₁ [receiptLink rt₁ rt₂ rc₂]).rt
    = rt₁ + (1 : ZMod 5) • rt₂
  rw [aggregate_cons, aggregate_nil, foldClaims_rt]
  rfl

/-- **Premise inhabitation, binding**: `committed_extract_bind` fires at the
receipt chain's FINAL accumulator, rooted at a genuine `BindingCommitment`
(the identity scheme) — the honestly-opened word is (trivially, `e = w`) the
committed one, and the aggregate's satisfaction transfers to it. -/
theorem ch₁_binding_fires :
    (rt₁ + (1 : ZMod 5) • rt₂) = (rt₁ + (1 : ZMod 5) • rt₂) ∧
    AccClaim.Satisfies C₁ (aggregate foldRoot₁ γbase₁ A₀₁ ch₁)
      (rt₁ + (1 : ZMod 5) • rt₂) :=
  committed_extract_bind S₁ (oe := fun _ => ()) ch₁_final_rt (fun _ => rfl)
    ch₁_hbase

/-- **Premise inhabitation, decision**: the decider's verdict at the final
accumulator IS the claim, unconditionally (`decider_sound`) — and, run on
the honest word, it ACCEPTS (via `ch₁_hbase`). -/
theorem ch₁_decision_fires :
    decider C₁ (aggregate foldRoot₁ γbase₁ A₀₁ ch₁) (rt₁ + (1 : ZMod 5) • rt₂) :=
  (decider_sound C₁ _ _).mpr ch₁_hbase

/-! ### The whole bundle FIRES, on the receipt chain, at once

Every hypothesis of ALL FOUR landed theorems, discharged on `ch₁` — the two
probabilistic slices at the SAME ghost prover (its word `rt₁`, its own
partial-fold openings), the binding/decision slices at the final accumulator
(the honest γ=1 fold). `SelvageV0Guarantee` is non-vacuous end to end. -/

/-- **THE CAPSTONE FIRES.** `loomV0_holds` applied to the receipt chain
`ch₁`: soundness (the ghost-replay teeth, bound `1/5`), knowledge (the same
ghost prover, its extractor's failure event bounded at `2/5`), binding (the
final accumulator's root is the honestly-folded word), and decision (the
decider accepts it) — all four, together, on one built history of kernel
receipts. -/
theorem ch₁_loomV0_holds :
    SelvageV0Guarantee foldRoot₁ C₁ A₀₁ ch₁ (1 / 8) (fun _ => (0 : ℝ))
      (0 : FlatIx w₁ → ZMod 5) ms₁ dom₁ 2 q₁ cols₁ γbase₁ S₁
      (rt₁ + (1 : ZMod 5) • rt₂) (rt₁ + (1 : ZMod 5) • rt₂)
      (rt₁ + (1 : ZMod 5) • rt₂) :=
  loomV0_holds (oe := fun _ => ()) ch₁_aligned (minDistLB_inhabited C₁) hMCA₁
    (by norm_num) (by norm_num) (by rw [card_FlatIx_w₁]; norm_num) (le_refl 0)
    ch₁_hfalse ch₁_seamOk le_rfl q₁_inj ms₁_mem (rts := rts₁)
    (ops := fun _ _ _ => ()) (fun _ _ _ => rfl)
    (fun γv c _ j => S₁.verifyOpen_commit (partialFold (padSched γv) 0 ms₁ c) (q₁ j))
    ch₁_final_rt (fun _ => rfl) ch₁_hbase (rt₁ + (1 : ZMod 5) • rt₂)

/-! ### Teeth — a broken seam is caught (general theorem, on receipt data)

`SeamOk` of a ONE-link chain is vacuously true (no consecutive pair to
check) — `ch₁` cannot exhibit the seam tooth. A genuine two-link receipt
chain, with the second link's `pre` set to the FIRST link's PRE (not its
POST — a spliced/reordered history), breaks it. -/

/-- Two copies of the one honest link, spliced so the second's `pre` does NOT
match the first's `post` (`rt₂ ≠ rt₁`, the anti-ghost distinction reused). -/
noncomputable def brokenCh₁ :
    Chain (FlatIx w₁ → ZMod 5) (ZMod 5) (FlatIx w₁) (ixList w₁).length :=
  receiptChain [(rt₁, rt₂, rc₂), (rt₁, rt₂, rc₂)]

/-- **Teeth, the seam**: `Selvage.not_seamOk_of_broken` — the general anti-tamper
tooth of `Selvage/LightClient.lean` — fires on genuine receipt-derived links: a
spliced receipt history is caught, deterministically, before any
probabilistic argument is needed. -/
theorem brokenCh₁_not_seamOk : ¬ SeamOk brokenCh₁ := by
  show ¬ SeamOk [receiptLink rt₁ rt₂ rc₂, receiptLink rt₁ rt₂ rc₂]
  exact not_seamOk_of_broken [] [] (a := receiptLink rt₁ rt₂ rc₂)
    (b := receiptLink rt₁ rt₂ rc₂) rt₁_ne_rt₂.symm

end SelvageV0Example

/-! ## §6. Residual obligations — prose, not stubs

Named residuals with their realizers; none is a `def : Prop := True` (the
vacuous-obligation sin, per `minidregg-audit-discipline`). This capstone
composes the PROVED tower — every field of `SelvageV0Guarantee` is a landed
theorem's conclusion, cited. It does NOT shrink what the tower already named
as open, and it manufactures none of the deployment realizers. Stated once
here rather than re-litigated per field:

* **`[ACC-extract-bind]`(b)`** (`Selvage/AccExtract.lean`, unchanged) — every
  theorem composed here (`lightClientSound`, `lightClientKnowledgeSound`,
  `committed_extract_bind`) consumes folded WORDS at named schedules as
  transcript data, and (for binding) a FULLY-OPENED word at every position.
  In deployment the prover opens `t` spot-checked Merkle columns and the
  full word is reconstructed by erasure correction inside the
  mutual-agreement set (WARP App. B; mutual correlated agreement PROVED at
  unique decoding — `Selvage/CorrelatedAgreement.lean`). That partial-opening
  lift is untouched by composition; it stays exactly where `AccExtract`/
  `AccExtractChain` left it.
* **`[COMMIT-CR]`** (`Selvage/Commitment.lean`, unchanged) — `binding` fires here
  against `S₁ := idealCommitment (ZMod 5) (FlatIx w₁)`, the INHABITED identity
  scheme (binding PROVED, no axiom). The deployed Merkle/sponge realizing
  `BindingCommitment` with a short root, whose `binding` field is a theorem
  ONLY relative to collision-resistance of the compression function, is
  priced there, not manufactured here — `loomV0_holds` is generic in `S`, so
  swapping in the deployed scheme composes for free once `[COMMIT-CR]` lands.
* **`[FS-ROM]`** (`Selvage/FiatShamir.lean`) — every `γs`/`padSched γv` above is
  a UNIFORMLY SAMPLED (or, for the deterministic apex, universally
  quantified) schedule. The deployed light client derives its ONE schedule
  by Fiat–Shamir from the transcript hash (σ-before-γ); the ROM idealization
  transporting "uniform" to "hash-derived, at the RBR price" is
  `Selvage/FiatShamir.lean`'s compilation (`Selvage/LightClientFS.lean` closes the
  fixed-chain form of this transport already — `lightClientSound` composed
  here is its PRE-transport ancestor, cited at that resolution).
* **`[LC-fs-adaptive]`** (`Selvage/LightClientFS.lean`) — the `t`-query grinding
  strengthening (an adaptive prover re-rolling the transcript hash `t` times
  to bias the FS-derived schedule) is named THERE, not closed by this file;
  composing `lightClientSound`/`lightClientKnowledgeSound` inherits it
  unchanged.
* **NO PROVER; performance UNMEASURED.** Every theorem here is a VERIFIER
  guarantee over WORDS and CLAIMS the tree already has in hand (satisfied
  claims, opened words, extracted witnesses). There is no prover
  implementation in this tree, no cost/latency measurement of the WHIR
  descent `Selvage/Decider.lean`'s `[DEC-proximity]` names (621 KiB / 4.8 ms /
  10k hashes at UD is the CITED LOOM §6 number, not a benchmark run here),
  and no wall-clock claim of any kind. "The capstone fires" means the Lean
  statements typecheck against built, non-vacuous witnesses — nothing about
  wall-clock cost.
* **The coupling this capstone previously SURFACED — closed at the word
  level.** `sound` and `knowledge` now anchor at ONE prover (`f₀`/`ms`/`cols`):
  `lightClientKnowledgeSound_oneProver_committed`
  (`Selvage/LightClientKnowledge.lean`) synthesizes the extractor's `n + 1`
  transcripts from that prover's opened columns (`seamCounterfactual`) and
  prices, over one sampled schedule, "verifies AND extraction fails" at
  `n · (err⋆ + 2/|F|)`. What remains of the old sentence is the FS transport
  of the sampled schedule (`[FS-ROM]`, above) and the deployed commitment
  (`[COMMIT-CR]`, above); the extractor's extra `1/|F|` per link (a zero
  challenge hides that link's word from every recommitted fold) is a priced
  limit of THIS extractor, on its label. `ch₁_loomV0_holds` above exhibits
  both probabilistic fields firing on the SAME ghost-replay prover —
  soundness because its word is δ-far-false, knowledge because the
  extractor's failure event is then contained in the verification event —
  while binding/decision fire at the honest final accumulator. -/

/-! ## §7. Axiom pins (house law) -/

/-- info: 'Minidregg.Assurance.loomV0_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loomV0_holds
/-- info: 'Minidregg.Assurance.SelvageV0Example.ch₁_loomV0_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SelvageV0Example.ch₁_loomV0_holds

end Minidregg.Assurance
