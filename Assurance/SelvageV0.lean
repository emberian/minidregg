/-
# `Assurance/SelvageV0.lean` — the v0 CAPSTONE: the Selvage tower, one theorem.

The end-to-end composition (docs/SELVAGE-RECOMPOSITION.md, docs/HYPEREDGE-DESIGN.md):
a committed chain of KERNEL RECEIPTS, verified by the light client at ONE
Fiat–Shamir schedule, attests the whole history — soundly, knowledge-soundly,
and bound to the commitment. Every clause of that sentence is a landed
theorem; this file cites them together, at ONE prover and ONE final
accumulator, so a skeptic can read one bundle instead of five files.

`SelvageV0Guarantee` has THREE fields:

  * `sound` — `Selvage.lightClientSound` (`Selvage/LightClientSound.lean`);
  * `knowledge` — `Selvage.lightClientKnowledgeSound_authMap`
    (`Selvage/AuthMapCommitment.lean`), about the SAME prover, whose columns
    are opened from `Theory.AuthMap` roots of its recommitted partial folds;
  * `binding` — `Selvage.authMap_extract_bind` at the final accumulator.

**The commitment is `Theory.AuthMap`, and binding is a reduction.**  The
previous revision took a `Selvage.BindingCommitment`, whose `binding` field is
unconditional position binding.  Every inhabitant has an injective `commit`
(`BindingCommitment.commit_injective`), so none exists at a root smaller than
its word space (`BindingCommitment.isEmpty_of_card_lt`): a deployed Merkle
root cannot be one under any hash assumption, and the capstone's binding leg
held only of the identity scheme.  Here the word is committed as an AuthMap
(a map holding the word, `HoldsWord`), and the two commitment-facing legs say:

  * `binding` — the word `e` fully opened from the final root IS the committed
    word `w` (and satisfaction transfers to it), OR the opening of some
    position where they differ EXHIBITS a collision of `H` among the pairs
    that check compared (`OpeningCollision`, the conclusion of
    `Scheme.forgery_exhibits_collision`).
  * `knowledge` — `Pr[verifies ∧ extraction fails] ≤ n·(err⋆(δ) + 2/|F|) +
    Pr[the prover's column openings exhibit a collision]`.

Neither disjunct nor summand is "`H` has a collision somewhere": that is true
of every compressing hash by pigeonhole, and would make the leg provable
outright.  The collision is the one the transcript's own checks compared.
Poles, at this file's receipt instance (§5):
  * satisfied, at the injective hash (`idScheme₁`, `H = id`): no opening
    exhibits a collision, so `binding` is exact (`idHash_binding_exact`) and the
    knowledge bound's collision term is `0` (`ch₁_knowledge_fires`);
  * refuted, at the 8-bit length hash (`lenScheme₁`): a forged full opening of
    a different word verifies (`lengthHash_forged_opens`), so the left
    disjunct fails, the per-check carrier `PathBinding` is false
    (`lengthHash_pathBinding_fails`) and the leg is forced to hand over a
    collision (`lengthHash_binding_collision`).
The conditional corollary `loomV0_binding_of_pathBinding` states the binding
leg under `Scheme.PathBinding` at every position — the per-check carrier that
is satisfiable at every hash (`Scheme.honest_binding`) and refutable at the
length hash.

**"Decided" is not a leg.**  The previous revision's fourth field was
`Selvage.decider_sound : decider C A f ↔ AccClaim.Satisfies C A f`, which is
`Iff.rfl`: `decider` is defined with `AccClaim.Satisfies`'s body.  It holds of
every accumulator and word, so it certified nothing, and it is removed.  What
the light client's final check does is decide `AccClaim.Satisfies` (the
`Decidable` instance in `Selvage/Decider.lean`); that is a fact about
computability, not a security leg.

**Honest scope**: every theorem cited is proved over the STRICT/word-level
relation (`AccClaim.Satisfies`) at a uniformly sampled schedule; the residuals
are named in §6.
-/
import Assurance.ReceiptClaim
import Selvage.LightClientSound
import Selvage.AuthMapCommitment

namespace Minidregg.Assurance

open Minidregg.Kernel Minidregg.Selvage Minidregg.Theory

/-! ## §1. The composition primitive — a receipt history IS a light-client chain

`ReceiptClaim.acc` (`Assurance/ReceiptClaim.lean`, OB-3) proved that ONE kernel
receipt, over a window `w`, is a native `AccClaim Root F (FlatIx w)
(ixList w).length`. Wrapping a SEQUENCE of receipts with the pre/post state
roots each committed turn claims turns that into a `Selvage.Chain` — exactly the
object `Selvage/LightClient.lean` aggregates. Bookkeeping only. -/

variable {F : Type} [Field F] [DecidableEq F] {w : Window} {Root : Type}

/-- **One committed turn as a light-client link**: the receipt claim
(`ReceiptClaim.acc`) plus the pre/post roots the chain seam pins together.
The claim's OWN commitment root is `post`. -/
noncomputable def receiptLink (pre post : Root) (rc : ReceiptClaim w F) :
    Selvage.Link Root F (FlatIx w) (ixList w).length :=
  ⟨pre, post, rc.acc post⟩

/-- **A receipt history, as a `Chain`**: a list of (pre-root, post-root,
receipt claim) turns, oldest first. -/
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

/-! ## §2. `SelvageV0Guarantee` — the end-to-end bundle, statement-first -/

/-- **The v0 Selvage guarantee.** A history `ch` (in practice `receiptChain`)
over AuthMap roots `D`, aggregated from genesis `A₀` under `foldRoot`,
checked by the light client at ONE Fiat–Shamir schedule:

* `sound` — `Selvage.lightClientSound`: a chain carrying a δ-far-false CLAIMED
  link (the prover's own committed words, anchored at
  `foldWords … f₀ (List.ofFn ms)`) survives verification at one uniformly
  sampled schedule with probability at most `n · (err⋆(δ) + 1/|F|)`.
* `knowledge` — `Selvage.lightClientKnowledgeSound_authMap`: for the SAME
  prover, whose partial fold `c` at schedule `γv` is committed as the map
  `maps γv c` and whose columns `cols γv c` are opened by `πs γv c`, the
  probability that its transcript δ-verifies AND the one-execution extractor
  fails is at most `n · (err⋆(δ) + 2/|F|)` plus the probability that those
  openings exhibit a collision of `S.H`.
* `binding` — `Selvage.authMap_extract_bind` at the final accumulator
  `A := aggregate foldRoot γs A₀ ch`, rooted at the map `m` holding `w`: the
  word `e` fully opened by `πe` is `w` and satisfaction transfers to it, or the
  opening of a position where `e i ≠ w i` exhibits a collision of `S.H`. -/
structure SelvageV0Guarantee {F : Type} [Field F] {ι D : Type} {r : ℕ}
    [Fintype F] [Nonempty ι] [Fintype ι] [DecidableEq ι] [DecidableEq F] [DecidableEq D]
    (S : AuthMap.Scheme ι F D)
    (foldRoot : D → F → D → D) (C : Submodule F (ι → F))
    (A₀ : AccClaim D F ι r) (ch : Chain D F ι r)
    (δ : ℝ) (errstar : ℝ → ℝ) (f₀ : ι → F) (ms : Fin ch.length → ι → F)
    (dom : ι ↪ F) (d : ℕ) {t : ℕ} (q : Fin t → ι)
    (maps : (Fin ch.length → F) → ℕ → AuthMap.Map ι F)
    (cols : (Fin ch.length → F) → ℕ → Fin t → F)
    (πs : (Fin ch.length → F) → ℕ → Fin t → AuthMap.Scheme.Opening ι F D)
    (γs : ℕ → F) (m : AuthMap.Map ι F) (πe : ι → AuthMap.Scheme.Opening ι F D)
    (w e : ι → F) : Prop where
  /-- **Soundness** (`lightClientSound`). -/
  sound : uniformProb (Fin ch.length → F) (fun γv =>
      ∃ u, relDist (foldWords (padSched γv) f₀ (List.ofFn ms)) u ≤ δ ∧
        AccClaim.Satisfies C (aggregate foldRoot (padSched γv) A₀ ch) u)
    ≤ (ch.length : ℝ) * (errstar δ + 1 / (Fintype.card F : ℝ))
  /-- **Knowledge soundness** (`lightClientKnowledgeSound_authMap`), about the
  same prover, priced with its openings' collision event. -/
  knowledge : uniformProb (Fin ch.length → F) (fun γv =>
      (∃ u, relDist (foldWords (padSched γv) f₀ (List.ofFn ms)) u ≤ δ ∧
        AccClaim.Satisfies C (aggregate foldRoot (padSched γv) A₀ ch) u) ∧
      ¬ (attests C ch ∧
        List.Forall₂ (fun l u => ∃ v, relDist u v ≤ δ ∧ AccClaim.Satisfies C l.claim v)
          ch (lcExtract dom d q ch.length (padSched γv)
            (foldWords (padSched γv) f₀ (List.ofFn ms)) (cols γv))))
    ≤ (ch.length : ℝ) * (errstar δ + 2 / (Fintype.card F : ℝ)) +
      uniformProb (Fin ch.length → F) (ColumnCollision S q maps cols πs)
  /-- **Binding to the commitment, as a reduction** (`authMap_extract_bind`),
  at the final accumulator. -/
  binding : (e = w ∧ AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch) w) ∨
    ∃ i, e i ≠ w i ∧ OpeningCollision S m i (some (e i)) (πe i)

/-! ## §3. `loomV0_holds` — the composition theorem -/

/-- **`loomV0_holds`.** Given every hypothesis `lightClientSound`,
`lightClientKnowledgeSound_authMap` and `authMap_extract_bind` ask for —
forwarded, not re-derived — the bundle fires. -/
theorem loomV0_holds {F : Type} [Field F] {ι D : Type} {r : ℕ}
    [Fintype F] [Nonempty ι] [Fintype ι] [DecidableEq ι] [DecidableEq F] [DecidableEq D]
    {S : AuthMap.Scheme ι F D}
    {foldRoot : D → F → D → D} {C : Submodule F (ι → F)}
    {A₀ : AccClaim D F ι r} {ch : Chain D F ι r}
    {δ dC Bstar : ℝ} {errstar : ℝ → ℝ} {f₀ : ι → F} {ms : Fin ch.length → ι → F}
    -- the regime shared by soundness and knowledge
    (halign : Aligned A₀ ch)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2)
    (herr0 : 0 ≤ errstar δ)
    -- soundness: a δ-far-false committed word
    (hfalse : ∃ p ∈ ch.zip (List.ofFn ms), ∀ v ∈ C, relDist p.2 v ≤ δ →
      ¬ AccClaim.Satisfies C p.1.claim v)
    -- knowledge: the seam, and the prover's AuthMap openings of its partial folds
    (hseam : SeamOk ch) {dom : ι ↪ F} {d t : ℕ} (hdt : d ≤ t) {q : Fin t → ι}
    (hq : Function.Injective (dom ∘ q))
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    {maps : (Fin ch.length → F) → ℕ → AuthMap.Map ι F}
    {cols : (Fin ch.length → F) → ℕ → Fin t → F}
    {πs : (Fin ch.length → F) → ℕ → Fin t → AuthMap.Scheme.Opening ι F D}
    (hmaps : ∀ (γv : Fin ch.length → F) (c : ℕ), c ≤ ch.length →
      HoldsWord S (maps γv c) (partialFold (padSched γv) f₀ ms c))
    (hver : ∀ (γv : Fin ch.length → F) (c : ℕ), c ≤ ch.length → ∀ j,
      S.verify (S.root (maps γv c)) (q j) (some (cols γv c j)) (πs γv c j) = true)
    -- binding, at the schedule-`γs` accumulator
    {γs : ℕ → F} {m : AuthMap.Map ι F} {w e : ι → F}
    {πe : ι → AuthMap.Scheme.Opening ι F D}
    (hrt : (aggregate foldRoot γs A₀ ch).rt = S.root m) (hm : HoldsWord S m w)
    (hopen : ∀ i, S.verify (aggregate foldRoot γs A₀ ch).rt i (some (e i)) (πe i) = true)
    (hsat : AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch) e) :
    SelvageV0Guarantee S foldRoot C A₀ ch δ errstar f₀ ms dom d q maps cols πs γs m πe
      w e where
  sound := lightClientSound foldRoot (f₀ := f₀) halign hdC hMCA hδ0 hδB hδC herr0
    (by simp) hfalse
  knowledge := lightClientKnowledgeSound_authMap foldRoot halign hseam hdC hMCA hδ0 hδB
    hδC herr0 S dom hdt hq hms hmaps hver
  binding := authMap_extract_bind S hrt hm hopen hsat

/-- **The binding leg under the per-check carrier.**  If `S.H` separates the
pairs each position's check compares (`Scheme.PathBinding`), the opened word
IS the committed word and satisfaction transfers to it.  The carrier is
satisfiable at every hash (`Scheme.honest_binding`) and refuted at the length
hash (`SelvageV0Example.lengthHash_pathBinding_fails`). -/
theorem loomV0_binding_of_pathBinding {F : Type} [Field F] {ι D : Type} {r : ℕ}
    [DecidableEq ι] [DecidableEq D] {S : AuthMap.Scheme ι F D}
    {foldRoot : D → F → D → D} {C : Submodule F (ι → F)}
    {A₀ : AccClaim D F ι r} {ch : Chain D F ι r}
    {γs : ℕ → F} {m : AuthMap.Map ι F} {w e : ι → F}
    {πe : ι → AuthMap.Scheme.Opening ι F D}
    (hrt : (aggregate foldRoot γs A₀ ch).rt = S.root m) (hm : HoldsWord S m w)
    (hb : ∀ i, S.PathBinding m i (some (e i)) (πe i))
    (hopen : ∀ i, S.verify (aggregate foldRoot γs A₀ ch).rt i (some (e i)) (πe i) = true)
    (hsat : AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch) e) :
    e = w ∧ AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch) w :=
  authMap_extract_bind_of_pathBinding S hrt hm hb hopen hsat

/-! ## §4. `loomV0_light_client` — the defensibility one-liner -/

/-- **THE ONE-LINER.** Checking the aggregate accumulated claim of a receipt
history at ONE Fiat–Shamir schedule (plus the decidable seam) is SOUND: a
history carrying a δ-far-false receipt survives that one check with
probability at most `n · (err⋆(δ) + 1/|F|)`. `lightClientSound`, re-exported
at the capstone's name. -/
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

A two-coordinate receipt window over F₅.  Its words are committed as AuthMaps
under two hashes that share every other parameter: `idScheme₁` (`H = id`,
the satisfied pole) and `lenScheme₁` (`H` = input length as a byte, the
refuted pole), mirroring `Theory.AuthMap`'s `IdToy` and `LengthToy`. -/

namespace SelvageV0Example

open Selvage.LCExample

/-- The keystone window: no cells, one key — `FlatIx` is the presence-bit/value
pair, `Fintype.card = 2`. -/
def w₁ : Window := ⟨∅, {UKey.nullifier 11}⟩

theorem card_FlatIx_w₁ : Fintype.card (FlatIx w₁) = 2 := by decide

/-- The two positions: presence bit and value of the one key. -/
def p₀ : FlatIx w₁ := Sum.inr (⟨UKey.nullifier 11, by decide⟩, 0)
def p₁ : FlatIx w₁ := Sum.inr (⟨UKey.nullifier 11, by decide⟩, 1)

instance : Nonempty (FlatIx w₁) := ⟨p₀⟩

def all₁ : List (FlatIx w₁) := [p₀, p₁]

theorem mem_all₁ : ∀ i, i ∈ all₁ := by decide

/-- Genesis kernel state: the nullifier unspent. -/
def k₁ : KernelState := ⟨∅, fun _ _ => 0, fun _ => [], fun _ => none⟩

/-- The next turn's kernel state: the nullifier spent (`some 0`, not `none`). -/
def k₁spent : KernelState :=
  { k₁ with umap := fun u => if u = UKey.nullifier 11 then some 0 else none }

def rc₁ : ReceiptClaim w₁ (ZMod 5) := ⟨k₁, flatten w₁ k₁, rfl⟩
def rc₂ : ReceiptClaim w₁ (ZMod 5) := ⟨k₁spent, flatten w₁ k₁spent, rfl⟩

/-- The two receipt words. -/
def u₁ : FlatIx w₁ → ZMod 5 := flatten w₁ k₁
def u₂ : FlatIx w₁ → ZMod 5 := flatten w₁ k₁spent

/-! ### The two AuthMap schemes over the receipt window -/

def ix₁ (i : FlatIx w₁) : List Bool := [decide (i = p₁)]

theorem ix₁_injective : Function.Injective ix₁ := by decide

def keyBytes₁ (i : FlatIx w₁) : List UInt8 := [if i = p₁ then 1 else 0]

theorem keyBytes₁_injective : Function.Injective keyBytes₁ := by decide

def valBytes₁ (x : ZMod 5) : List UInt8 := [x.val.toUInt8]

theorem valBytes₁_injective : Function.Injective valBytes₁ := by decide

/-- The satisfied pole's hash: `H = id`, digests framed by `unaryFrame`. -/
def idScheme₁ : AuthMap.Scheme (FlatIx w₁) (ZMod 5) (List UInt8) where
  H := id
  digestBytes := AuthMap.unaryFrame
  keyBytes := keyBytes₁
  valBytes := valBytes₁
  digestBytes_prefixFree := AuthMap.unaryFrame_prefixFree
  keyBytes_prefixFree :=
    AuthMap.prefixFree_of_fixedWidth _ 1 (fun _ => rfl) keyBytes₁_injective
  valBytes_injective := valBytes₁_injective
  depth := 1
  ix := ix₁
  ix_length _ := rfl

/-- The refuted pole's hash: the input's length, as one byte. -/
def lenScheme₁ : AuthMap.Scheme (FlatIx w₁) (ZMod 5) UInt8 where
  H bs := bs.length.toUInt8
  digestBytes d := [d]
  keyBytes := keyBytes₁
  valBytes := valBytes₁
  digestBytes_prefixFree := AuthMap.prefixFree_of_fixedWidth _ 1 (fun _ => rfl)
    AuthMap.LengthToy.single_injective
  keyBytes_prefixFree :=
    AuthMap.prefixFree_of_fixedWidth _ 1 (fun _ => rfl) keyBytes₁_injective
  valBytes_injective := valBytes₁_injective
  depth := 1
  ix := ix₁
  ix_length _ := rfl

/-- A word committed under `idScheme₁`. -/
def M (u : FlatIx w₁ → ZMod 5) : AuthMap.Map (FlatIx w₁) (ZMod 5) :=
  wordMap idScheme₁ all₁ u

theorem holds_M (u : FlatIx w₁ → ZMod 5) : HoldsWord idScheme₁ (M u) u :=
  holdsWord_wordMap idScheme₁ mem_all₁ ix₁_injective u

/-- The honest opening of every position of a committed word verifies. -/
theorem M_opens (u : FlatIx w₁ → ZMod 5) (i : FlatIx w₁) :
    idScheme₁.verify (idScheme₁.root (M u)) i (some (u i))
      (idScheme₁.opening (M u) i) = true := by
  have h := idScheme₁.verify_opening (M u) i
  rwa [holds_M u i] at h

/-! ### The receipt history over `idScheme₁` roots -/

def rt₁ : List UInt8 := idScheme₁.root (M u₁)
def rt₂ : List UInt8 := idScheme₁.root (M u₂)

/-- The genesis accumulated claim: the first receipt, rooted at its own
commitment. -/
noncomputable def A₀₁ :
    AccClaim (List UInt8) (ZMod 5) (FlatIx w₁) (ixList w₁).length :=
  rc₁.acc rt₁

/-- The one-link receipt history `k₁ → k₁spent`. -/
noncomputable def ch₁ :
    Chain (List UInt8) (ZMod 5) (FlatIx w₁) (ixList w₁).length :=
  receiptChain [(rt₁, rt₂, rc₂)]

theorem ch₁_length : ch₁.length = 1 := receiptChain_length _

/-- The prover's recommitment: it knows the words behind the roots it
committed (`u₁` at the accumulator, `u₂` at the link) and commits their fold.
A hash root cannot be folded homomorphically; the prover recommits the folded
word, which is what WARP's prover does. -/
def decA (a : List UInt8) : FlatIx w₁ → ZMod 5 := if a = rt₁ then u₁ else 0
def decB (b : List UInt8) : FlatIx w₁ → ZMod 5 := if b = rt₂ then u₂ else 0

def foldRoot₁ : List UInt8 → ZMod 5 → List UInt8 → List UInt8 :=
  fun a γ b => idScheme₁.root (M (decA a + γ • decB b))

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

theorem ch₁_verifies_forall (γs : ℕ → ZMod 5) :
    Verifies C₁ (aggregate foldRoot₁ γs A₀₁ ch₁) := by
  show Verifies C₁ (aggregate foldRoot₁ γs A₀₁ [receiptLink rt₁ rt₂ rc₂])
  exact ⟨_, receiptClaim_folds foldRoot₁ rc₁ rc₂ rt₁ rt₂ (γs 0)
    Submodule.mem_top Submodule.mem_top⟩

/-- The deterministic apex fires on the receipt chain. -/
theorem ch₁_attests : attests C₁ ch₁ :=
  lightClient_attests foldRoot₁ ch₁_aligned A₀₁_verifies ch₁_seamOk
    ch₁_verifies_forall

/-! ### The one prover — ghost-replay data feeding `sound` AND `knowledge`

The keystone prover CLAIMS link 0's word is still `u₁` (the nullifier
UNSPENT) instead of the honest `u₂` (spent). -/

def ms₁ : Fin ch₁.length → FlatIx w₁ → ZMod 5 := fun _ => u₁

def γbase₁ : ℕ → ZMod 5 := fun _ => 1

/-- The erasure-decoding domain: the two coordinates embedded as `{0, 1}`. -/
def dom₁ : FlatIx w₁ ↪ ZMod 5 :=
  ⟨Sum.elim (fun _ => 4) (fun p => ((p.2 : ℕ) : ZMod 5)), by decide⟩

def q₁ : Fin 2 → FlatIx w₁ := fun b => Sum.inr (⟨UKey.nullifier 11, by decide⟩, b)

theorem q₁_inj : Function.Injective (dom₁ ∘ q₁) := by decide

theorem ms₁_mem : ∀ k, ms₁ k ∈ reedSolomonCode dom₁ 2 := by
  intro k
  have htop := reedSolomonCode_card_eq_top dom₁
  rw [card_FlatIx_w₁] at htop
  rw [htop]
  exact Submodule.mem_top

/-- The ghost prover's recommitted partial folds, as AuthMaps. -/
noncomputable def maps₁ (γv : Fin ch₁.length → ZMod 5) (c : ℕ) : AuthMap.Map (FlatIx w₁) (ZMod 5) :=
  M (partialFold (padSched γv) 0 ms₁ c)

/-- Its opened columns: the partial folds' symbols at `q₁`. -/
noncomputable def cols₁ (γv : Fin ch₁.length → ZMod 5) : ℕ → Fin 2 → ZMod 5 :=
  fun c j => partialFold (padSched γv) 0 ms₁ c (q₁ j)

/-- Its openings: the honest AuthMap openings of those columns. -/
noncomputable def πs₁ (γv : Fin ch₁.length → ZMod 5) (c : ℕ) (j : Fin 2) :
    AuthMap.Scheme.Opening (FlatIx w₁) (ZMod 5) (List UInt8) :=
  idScheme₁.opening (maps₁ γv c) (q₁ j)

theorem u₁_ne_u₂_pt : u₁ p₀ ≠ u₂ p₀ := by
  show flatten (F := ZMod 5) w₁ k₁ _ ≠ flatten (F := ZMod 5) w₁ k₁spent _
  decide

theorem u₁_ne_u₂ : u₁ ≠ u₂ := fun h => u₁_ne_u₂_pt (congrFun h _)

theorem hmax₁ :
    max (1 - 1 / (Fintype.card (FlatIx w₁) : ℝ) / 2) 0 = 3 / 4 := by
  rw [card_FlatIx_w₁]; norm_num

theorem hMCA₁ :
    HasMutualCorrelatedAgreement (affineGenerator (ZMod 5)) C₁ (3 / 4)
      (fun _ => 0) := by
  rw [← hmax₁]; exact hasMutualCorrelatedAgreement_top_affine

/-- The ghost word is δ-far-false at the one link. -/
theorem ch₁_hfalse :
    ∃ p ∈ ch₁.zip (List.ofFn ms₁), ∀ v ∈ C₁,
      relDist p.2 v ≤ (1 / 8 : ℝ) → ¬ AccClaim.Satisfies C₁ p.1.claim v := by
  refine ⟨(ch₁.get ⟨0, by rw [ch₁_length]; omega⟩, u₁),
    zip_ofFn_mem ch₁ ms₁ ⟨0, by rw [ch₁_length]; omega⟩, ?_⟩
  intro v _ hclose hsat
  have hsat' : AccClaim.Satisfies C₁ (rc₂.acc rt₂) v := hsat
  have hv : v = u₂ :=
    ((ReceiptClaim.acc_satisfies_iff (C := C₁) rc₂ rt₂ (f := v)).mp hsat').2
  have hfar : (1 : ℝ) / 2 ≤ relDist u₁ v :=
    hv ▸ one_div_card_le_relDist (F := ZMod 5) u₁_ne_u₂
  linarith

/-- **Premise inhabitation, soundness fires**, bound `1 · (0 + 1/5)`. -/
theorem ch₁_sound_fires :
    uniformProb (Fin ch₁.length → ZMod 5) (fun γv =>
        ∃ u, relDist (foldWords (padSched γv) (0 : FlatIx w₁ → ZMod 5) (List.ofFn ms₁)) u
            ≤ (1 / 8 : ℝ) ∧
          AccClaim.Satisfies C₁ (aggregate foldRoot₁ (padSched γv) A₀₁ ch₁) u)
      ≤ (ch₁.length : ℝ) * ((0 : ℝ) + 1 / (Fintype.card (ZMod 5) : ℝ)) :=
  lightClientSound foldRoot₁ ch₁_aligned (minDistLB_inhabited C₁) hMCA₁
    (by norm_num) (by norm_num) (by rw [card_FlatIx_w₁]; norm_num) (le_refl 0)
    (by simp) ch₁_hfalse

theorem hmaps₁ (γv : Fin ch₁.length → ZMod 5) (c : ℕ) (_ : c ≤ ch₁.length) :
    HoldsWord idScheme₁ (maps₁ γv c) (partialFold (padSched γv) 0 ms₁ c) :=
  holds_M _

theorem hver₁ (γv : Fin ch₁.length → ZMod 5) (c : ℕ) (_ : c ≤ ch₁.length) (j : Fin 2) :
    idScheme₁.verify (idScheme₁.root (maps₁ γv c)) (q₁ j) (some (cols₁ γv c j))
      (πs₁ γv c j) = true :=
  M_opens _ (q₁ j)

/-- At the injective hash no opening exhibits a collision, so the knowledge
bound's collision term is `0`. -/
theorem ch₁_noColumnCollision :
    uniformProb (Fin ch₁.length → ZMod 5) (ColumnCollision idScheme₁ q₁ maps₁ cols₁ πs₁)
      = 0 :=
  uniformProb_false fun _ ⟨_, _, _, h⟩ =>
    not_openingCollision_of_injective idScheme₁ Function.injective_id _ _ _ _ h

/-- **Premise inhabitation, knowledge**, at the SAME ghost prover's data:
bound `1 · (0 + 2/5) + 0`. -/
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
      ≤ (ch₁.length : ℝ) * ((0 : ℝ) + 2 / (Fintype.card (ZMod 5) : ℝ)) := by
  have h := lightClientKnowledgeSound_authMap (δ := 1 / 8) (errstar := fun _ => 0)
    foldRoot₁ ch₁_aligned ch₁_seamOk
    (minDistLB_inhabited C₁) hMCA₁ (by norm_num) (by norm_num)
    (by rw [card_FlatIx_w₁]; norm_num) (le_refl 0) idScheme₁ dom₁ le_rfl q₁_inj ms₁_mem
    (maps := maps₁) (cols := cols₁) (πs := πs₁) hmaps₁ hver₁
  rwa [ch₁_noColumnCollision, add_zero] at h

/-! ### Binding — the final accumulator's root commits the folded word -/

/-- The honest γ=1 fold. -/
def ufin : FlatIx w₁ → ZMod 5 := u₁ + (1 : ZMod 5) • u₂

theorem ch₁_hbase :
    AccClaim.Satisfies C₁ (aggregate foldRoot₁ γbase₁ A₀₁ ch₁) ufin := by
  show AccClaim.Satisfies C₁
    (aggregate foldRoot₁ γbase₁ A₀₁ [receiptLink rt₁ rt₂ rc₂]) ufin
  exact receiptClaim_folds foldRoot₁ rc₁ rc₂ rt₁ rt₂ 1
    Submodule.mem_top Submodule.mem_top

/-- The final accumulator's root is the root of the map holding the fold. -/
theorem ch₁_final_rt :
    (aggregate foldRoot₁ γbase₁ A₀₁ ch₁).rt = idScheme₁.root (M ufin) := by
  show (aggregate foldRoot₁ γbase₁ A₀₁ [receiptLink rt₁ rt₂ rc₂]).rt
    = idScheme₁.root (M ufin)
  rw [aggregate_cons, aggregate_nil, foldClaims_rt]
  show idScheme₁.root (M (decA rt₁ + γbase₁ 0 • decB rt₂)) = idScheme₁.root (M ufin)
  simp only [decA, decB, if_true, γbase₁, ufin]

/-- The honest full opening of the fold against the final root. -/
def πe₁ (i : FlatIx w₁) : AuthMap.Scheme.Opening (FlatIx w₁) (ZMod 5) (List UInt8) :=
  idScheme₁.opening (M ufin) i

theorem ch₁_hopen (i : FlatIx w₁) :
    idScheme₁.verify (aggregate foldRoot₁ γbase₁ A₀₁ ch₁).rt i (some (ufin i)) (πe₁ i)
      = true := by
  rw [ch₁_final_rt]; exact M_opens ufin i

/-- **Satisfied pole of the binding leg.**  At the injective hash, EVERY word
fully opened from the final root is the committed fold, and satisfaction
transfers to it: the collision disjunct is impossible. -/
theorem idHash_binding_exact {e : FlatIx w₁ → ZMod 5}
    {πe : FlatIx w₁ → AuthMap.Scheme.Opening (FlatIx w₁) (ZMod 5) (List UInt8)}
    (hopen : ∀ i, idScheme₁.verify (aggregate foldRoot₁ γbase₁ A₀₁ ch₁).rt i
      (some (e i)) (πe i) = true)
    (hsat : AccClaim.Satisfies C₁ (aggregate foldRoot₁ γbase₁ A₀₁ ch₁) e) :
    e = ufin ∧ AccClaim.Satisfies C₁ (aggregate foldRoot₁ γbase₁ A₀₁ ch₁) ufin :=
  (authMap_extract_bind idScheme₁ ch₁_final_rt (holds_M ufin) hopen hsat).resolve_right
    fun ⟨_, _, h⟩ =>
      not_openingCollision_of_injective idScheme₁ Function.injective_id _ _ _ _ h

/-! ### The whole bundle FIRES, on the receipt chain, at once -/

/-- **THE CAPSTONE FIRES.** `loomV0_holds` on the receipt chain `ch₁` at the
satisfied pole: soundness (ghost replay, `1/5`), knowledge (the same ghost
prover's AuthMap openings), binding (the final root commits the honest
fold). -/
theorem ch₁_loomV0_holds :
    SelvageV0Guarantee idScheme₁ foldRoot₁ C₁ A₀₁ ch₁ (1 / 8) (fun _ => (0 : ℝ))
      (0 : FlatIx w₁ → ZMod 5) ms₁ dom₁ 2 q₁ maps₁ cols₁ πs₁ γbase₁ (M ufin) πe₁
      ufin ufin :=
  loomV0_holds ch₁_aligned (minDistLB_inhabited C₁) hMCA₁
    (by norm_num) (by norm_num) (by rw [card_FlatIx_w₁]; norm_num) (le_refl 0)
    ch₁_hfalse ch₁_seamOk le_rfl q₁_inj ms₁_mem hmaps₁ hver₁
    ch₁_final_rt (holds_M ufin) ch₁_hopen ch₁_hbase

/-! ### Refuted pole — the length hash

Under `lenScheme₁` the digest depends only on input lengths, and every value
renders as one byte, so the honest siblings of a committed word also verify a
DIFFERENT word.  The binding leg's left disjunct fails, the per-check carrier
is false, and the leg hands over a collision. -/

def w0 : FlatIx w₁ → ZMod 5 := fun _ => 0
def e1 : FlatIx w₁ → ZMod 5 := fun _ => 1

def mL : AuthMap.Map (FlatIx w₁) (ZMod 5) := wordMap lenScheme₁ all₁ w0

theorem holds_mL : HoldsWord lenScheme₁ mL w0 :=
  holdsWord_wordMap lenScheme₁ mem_all₁ ix₁_injective w0

def πL (i : FlatIx w₁) : AuthMap.Scheme.Opening (FlatIx w₁) (ZMod 5) UInt8 :=
  lenScheme₁.opening mL i

/-- The forged full opening of `e1` against the root of the map holding
`w0` verifies at every position. -/
theorem lengthHash_forged_opens :
    ∀ i, lenScheme₁.verify (lenScheme₁.root mL) i (some (e1 i)) (πL i) = true := by
  decide

theorem e1_ne_w0 : e1 ≠ w0 := fun h => absurd (congrFun h p₀) (by decide)

/-- **The leg is forced into its collision disjunct.** -/
theorem lengthHash_binding_collision :
    ∃ i, e1 i ≠ w0 i ∧ OpeningCollision lenScheme₁ mL i (some (e1 i)) (πL i) :=
  (opened_word_or_collision lenScheme₁ holds_mL lengthHash_forged_opens).resolve_left
    e1_ne_w0

/-- **Refuted pole of the carrier.**  `PathBinding` fails at this forgery:
were it true at every position, `loomV0_binding_of_pathBinding`'s reasoning
would prove `e1 = w0`. -/
theorem lengthHash_pathBinding_fails :
    ¬ ∀ i, lenScheme₁.PathBinding mL i (some (e1 i)) (πL i) := fun hb =>
  e1_ne_w0 (funext fun i =>
    column_of_pathBinding lenScheme₁ holds_mL (hb i) (lengthHash_forged_opens i))

/-- **Satisfied pole of the carrier, at the same 8-bit hash.**  The honest
openings meet it (`Scheme.honest_binding`). -/
theorem lengthHash_pathBinding_honest :
    ∀ i, lenScheme₁.PathBinding mL i (some (w0 i)) (lenScheme₁.opening mL i) := by
  intro i
  have h := lenScheme₁.honest_binding mL i
  rwa [holds_mL i] at h

/-! ### Teeth — a broken seam is caught -/

noncomputable def brokenCh₁ :
    Chain (List UInt8) (ZMod 5) (FlatIx w₁) (ixList w₁).length :=
  receiptChain [(rt₁, rt₂, rc₂), (rt₁, rt₂, rc₂)]

theorem rt₁_ne_rt₂ : rt₁ ≠ rt₂ := fun h => by
  have h1 := M_opens u₁ p₀
  rw [show idScheme₁.root (M u₁) = idScheme₁.root (M u₂) from h] at h1
  have := column_of_pathBinding idScheme₁ (holds_M u₂)
    (idScheme₁.binding_of_injective Function.injective_id _ _ _ _) h1
  exact u₁_ne_u₂_pt this

/-- **Teeth, the seam**: a spliced receipt history is caught. -/
theorem brokenCh₁_not_seamOk : ¬ SeamOk brokenCh₁ := by
  show ¬ SeamOk [receiptLink rt₁ rt₂ rc₂, receiptLink rt₁ rt₂ rc₂]
  exact not_seamOk_of_broken [] [] (a := receiptLink rt₁ rt₂ rc₂)
    (b := receiptLink rt₁ rt₂ rc₂) rt₁_ne_rt₂.symm

end SelvageV0Example

/-! ## §6. Residual obligations — prose, not stubs

* **`[ACC-extract-bind]`(b)** (`Selvage/AccExtract.lean`, unchanged) — `binding`
  consumes a FULLY-OPENED word at every position. In deployment the prover
  opens `t` spot-checked columns and the full word is reconstructed by erasure
  correction inside the mutual-agreement set; that lift stays where
  `AccExtract`/`AccExtractChain` left it.
* **`[COMMIT-CR]`, now a price, not a type.** `binding` and `knowledge` are
  reductions: a failure of either is an exhibited collision of `S.H` among
  the pairs a check compared. What remains is to bound the probability that
  an efficient prover produces such a collision for the deployed hash — the
  collision-resistance ASSUMPTION, which must be stated over efficient
  adversaries (a statement that `H` has no collisions is false at every
  compressing hash). This file does not state it; `knowledge` carries the
  collision probability as an explicit summand instead.
* **The deployed hash and framing.** `idScheme₁`/`lenScheme₁` are toys. The
  deployed scheme instantiates `Theory.AuthMap.Scheme` with the stage-F hash
  and a fixed-width 32-byte digest framing (`prefixFree_of_fixedWidth`);
  that instantiation belongs to the data-model waves.
* **`[FS-ROM]`** (`Selvage/FiatShamir.lean`) — every `γs`/`padSched γv` above
  is a UNIFORMLY SAMPLED schedule; the transport to the hash-derived schedule
  is `Selvage/LightClientFS.lean`'s.
* **`[LC-fs-adaptive]`** (`Selvage/LightClientFS.lean`) — the `t`-query
  grinding strengthening is named there, inherited unchanged.
* **NO PROVER; performance UNMEASURED.** Every theorem here is a VERIFIER
  guarantee over words and claims. "The capstone fires" means the statements
  typecheck against built witnesses — nothing about wall-clock cost. -/

/-! ## §7. Axiom pins (house law) -/

/-- info: 'Minidregg.Assurance.loomV0_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loomV0_holds
/-- info: 'Minidregg.Assurance.loomV0_binding_of_pathBinding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loomV0_binding_of_pathBinding
/-- info: 'Minidregg.Assurance.SelvageV0Example.ch₁_loomV0_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SelvageV0Example.ch₁_loomV0_holds
/-- info: 'Minidregg.Assurance.SelvageV0Example.idHash_binding_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SelvageV0Example.idHash_binding_exact
/-- info: 'Minidregg.Assurance.SelvageV0Example.ch₁_knowledge_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SelvageV0Example.ch₁_knowledge_fires
/-- info: 'Minidregg.Assurance.SelvageV0Example.lengthHash_forged_opens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SelvageV0Example.lengthHash_forged_opens
/-- info: 'Minidregg.Assurance.SelvageV0Example.lengthHash_binding_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SelvageV0Example.lengthHash_binding_collision
/-- info: 'Minidregg.Assurance.SelvageV0Example.lengthHash_pathBinding_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SelvageV0Example.lengthHash_pathBinding_fails
/-- info: 'Minidregg.Assurance.SelvageV0Example.lengthHash_pathBinding_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SelvageV0Example.lengthHash_pathBinding_honest

end Minidregg.Assurance
