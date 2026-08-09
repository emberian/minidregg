/-
# Assurance.ErrorBudget — the END-TO-END SOUNDNESS ERROR BUDGET: one number.

Every component bound in this tree is landed and quoted piecemeal; this file
states the WHOLE: one composed soundness-error expression, one theorem bounding
the joint failure event by it, one deployed instantiation with the bit-security
COMPUTED. The four component failure events, each priced by its landed theorem
(CITED, never re-derived):

* **Grinding/FS light client** — `Loom.lightClientGrinding_sound`
  (`Loom/LightClientGrinding.lean`): a `t`-query grinding adversary forges the
  FS light client with probability `≤ (t + k)·[k·(err⋆(δ) + 1/|F|)]`, `k` the
  chain-length bound. The per-fold factor `err⋆(δ) + 1/|F|` IS the landed RBR
  round error `accRbrError` (`Loom/AccSoundRbr.lean`) — `budget_accRbrError`
  below records the identification as `rfl`.
* **Sumcheck** — `Loom.sumcheck_soundness` (`Loom/Sumcheck.lean`): each link's
  `v`-round degree-`d` sumcheck accepts a false claim with probability
  `≤ v·d/|F|`; union over the `k` links: `k·(v·d/|F|)`.
* **CR in the ROM** — `Loom.commitCR_of_RO_pow`
  (`Loom/CollisionResistanceROM.lean`): a `q`-query commitment-break adversary
  against an `h`-bit hash range wins with probability `≤ q·(q−1)/2^(h+1)`
  (the birthday bound).
* **Proximity gap** — `Loom.hasMutualCorrelatedAgreement_UD`
  (`Loom/ProximityGapUD.lean`): one affine-generator draw (the decider's fold
  challenge) lands in the mutual-CA failure set with probability `≤ n/|F|`,
  `n` the code length — the PROVED unique-decoding error, which is also the
  `err⋆(δ)` substituted into the grinding term.

`soundnessError` is their SUM; `soundnessError_bound` proves the union of the
four events over a product coin space is `≤ soundnessError P`, by the union
bound + exact product marginals + the four citations. `deployedBudget`
instantiates at BabyBear⁴ and computes the number.

**THE HEADLINE (deployed parameters, proven terms, unique decoding):**
`soundnessError deployedBudget ≤ 2^{−55}` and `> 2^{−56}` — **55 bits**, at
challenge field BabyBear⁴ (`p = 2013265921 = 15·2²⁷+1`, `|F| = p⁴ ≈ 2^{123.6}`),
code length `n = 2^{20}`, rate `ρ = 1/2`, `δ = 1/8` (inside the UD radius
`(1−ρ)/3 = 1/6`), grinding/hash budgets `t = q = 2^{40}`, chain depth
`k = 2^8`, sumcheck `v = 20`, `d = 3`, hash range `2^{248}`. The DOMINANT term
is the grinding term `(t+k)·k·(n+1)/|F|` — everything else together is
`≤ 2^{−100}` (`deployedBudget_grinding_dominant`): the load-bearing knobs are
the challenge-field size and the `t·k·n` numerator, nothing else. General
reading: bits ≈ log₂|F| − log₂(t·k·n).

**Covered scope, in the same sentence as the claim**: the budget sums the
PROVEN terms at UNIQUE DECODING (`err⋆ = n/|F|` for `δ < (1−ρ)/3`, the landed
`rs_proximityGap_UD` regime — no Johnson/beyond-UD conjecture on the label),
and it RIDES the named floor: [FS-ROM] (the deployed hash realizes the
lazy-sampling handler — the one modeling idealization, shared by the grinding
and CR terms), [ACC-extract-bind] (the partial-opening/erasure lift),
[ACC-rbr-bcs] (the deployed root-and-columns alphabet), [COMMIT-CR](i)/(iii)
(the Merkle tree walk — the CR ENDPOINT is priced here by `crTerm`; the
tree-path reduction is not), [CR-ROM-adaptive] (the birthday bound covers
non-adaptive query schedules; the claimed pair is adaptive). The floor
contributes NO summand because its content is an idealization, not an event
with a proven probability — stated separately, never silently added to zero.
-/
import Loom.LightClientGrinding
import Loom.Sumcheck
import Loom.CollisionResistanceROM
import Loom.AccSoundRbr
import Loom.ProximityGapUD

namespace Minidregg.Assurance

open Minidregg.Loom

/-! ## §1 The deployment knobs and the composed error -/

/-- **The deployment knobs.** Everything the composed soundness error reads:
challenge-field size, code length + RS degree (rate `ρ = degree/codeLen`),
the proximity parameter, the grinding/oracle query budget, the chain depth,
the per-link sumcheck shape, the hash budget + range, and the TARGET security
level `secparam` (the λ the deployed instantiation is measured against — it
does not enter the error expression; it is what the error is compared to). -/
structure SoundnessParams where
  /-- `|F|` — the challenge-field size (deployed: BabyBear⁴). -/
  fieldCard : ℕ
  /-- `n` — the code length (evaluation-domain size). -/
  codeLen : ℕ
  /-- The RS degree bound; the rate is `ρ = degree / codeLen`. -/
  degree : ℕ
  /-- `δ` — the proximity parameter; admissible at UD when
  `δ < 1 − (2 + ρ)/3 = (1 − ρ)/3`. Only side conditions read it: the proved
  UD error `err⋆(δ) = n/|F|` is δ-independent. -/
  delta : ℝ
  /-- `t` — the grinding adversary's oracle-query budget. -/
  queries : ℕ
  /-- `k` — the chain depth (number of links / folds / FS rounds). -/
  depth : ℕ
  /-- `v` — sumcheck rounds per link. -/
  scRounds : ℕ
  /-- `d` — sumcheck round-polynomial degree bound. -/
  scDegree : ℕ
  /-- `q` — the commitment adversary's hash-query budget. -/
  hashQueries : ℕ
  /-- `h` — the hash range is `2^h`. -/
  hashBits : ℕ
  /-- λ — the target bit-security level (the label, not a term). -/
  secparam : ℕ

/-- The PROVED unique-decoding mutual-CA error `err⋆ = n/|F|`
(`hasMutualCorrelatedAgreement_UD`, `Loom/ProximityGapUD.lean`) — the one
error function every proximity citation below instantiates. -/
noncomputable def errStarUD (P : SoundnessParams) : ℝ :=
  (P.codeLen : ℝ) / (P.fieldCard : ℝ)

/-- **The grinding term** `(t + k) · [k · (err⋆ + 1/|F|)]` — the landed
`lightClientGrinding_sound` bound, verbatim: the `(t+k)` grinding factor of
WARP Thm B.4 / `fsKeystone_proved` scaling the fixed-chain bound
`k·(err⋆ + 1/|F|)`. Union-bound accounting pays per-try·per-chain; the
per-query·per-fold sharpening `(t+k)·(err⋆+1/|F|)` is `[LC-grinding-native]`
(would shave a factor `k` — log₂ k bits — off the dominant term). -/
noncomputable def grindingTerm (P : SoundnessParams) : ℝ :=
  ((P.queries : ℝ) + (P.depth : ℝ)) *
    ((P.depth : ℝ) * (errStarUD P + 1 / (P.fieldCard : ℝ)))

/-- **The sumcheck term** `k · (v·d/|F|)` — `sumcheck_soundness`'s `v·d/|F|`
per link, union over the `k` links. -/
noncomputable def sumcheckTerm (P : SoundnessParams) : ℝ :=
  (P.depth : ℝ) * ((P.scRounds : ℝ) * ((P.scDegree : ℝ) / (P.fieldCard : ℝ)))

/-- **The CR-in-ROM term** `q(q−1)/2^(h+1)` — `commitCR_of_RO_pow`'s birthday
bound, verbatim (`≤ q²/2^h`, quoted at the sharper proven form). -/
noncomputable def crTerm (P : SoundnessParams) : ℝ :=
  (P.hashQueries : ℝ) * ((P.hashQueries : ℝ) - 1) / (2 ^ (P.hashBits + 1) : ℝ)

/-- **The proximity-gap term** `n/|F|` — one more affine-generator draw of the
mutual-CA failure event (the decider's own fold challenge), priced by
`hasMutualCorrelatedAgreement_UD`. -/
noncomputable def proximityTerm (P : SoundnessParams) : ℝ := errStarUD P

/-- **THE COMPOSED SOUNDNESS ERROR** — the union bound over the four component
failure events:

  `(t+k)·[k·(err⋆+1/|F|)]  +  k·(v·d/|F|)  +  q(q−1)/2^(h+1)  +  n/|F|`.

Every summand is a landed theorem's right-hand side; `soundnessError_bound`
is the composition. -/
noncomputable def soundnessError (P : SoundnessParams) : ℝ :=
  grindingTerm P + sumcheckTerm P + crTerm P + proximityTerm P

/-- The grinding term's per-fold factor IS the landed RBR round error
`accRbrError` (`Loom/AccSoundRbr.lean`) at the UD-proved `err⋆` — the
identification is definitional, recorded so the budget's vocabulary and the
RBR tower's provably coincide. -/
theorem budget_accRbrError (F ι : Type) [Fintype F] [Fintype ι] (δ : ℝ) :
    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) + 1 / (Fintype.card F : ℝ)
      = accRbrError F
          (fun _ => (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) δ := rfl

/-! ## §2 Product-marginal plumbing

The four component events live on four coin blocks; the joint space is their
product. An event reading ONE block keeps exactly its marginal probability —
the same counting fact `Loom/LightClientGrinding.lean` proves (privately) for
its shared-oracle transfer, rebuilt here for a four-fold product. Private, per
the module-private discipline. -/

section Marginals

private def fstSubtypeEquiv {A B : Type} (p : A → Prop) :
    {y : A × B // p y.1} ≃ {a : A // p a} × B where
  toFun y := (⟨y.1.1, y.2⟩, y.1.2)
  invFun x := ⟨(x.1.1, x.2), x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- An event reading only the FIRST factor keeps its probability. (The
`Nonempty` guard is real: over an empty second factor the product probability
degenerates to `0`.) -/
private theorem uniformProb_fst_marg {A B : Type} [Fintype A] [Fintype B]
    [Nonempty B] (p : A → Prop) :
    uniformProb (A × B) (fun y => p y.1) = uniformProb A p := by
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold uniformProb
  rw [Nat.card_congr (fstSubtypeEquiv p), Nat.card_prod,
    Nat.card_eq_fintype_card (α := B), Fintype.card_prod]
  push_cast
  rw [← div_mul_div_comm, div_self hB, mul_one]

/-- An event reading only the SECOND factor keeps its probability. -/
private theorem uniformProb_snd_marg {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] (p : B → Prop) :
    uniformProb (A × B) (fun y => p y.2) = uniformProb B p :=
  (uniformProb_equiv (Equiv.prodComm A B) (fun y : B × A => p y.1)).trans
    (uniformProb_fst_marg p)

/-- **The four-block union bound**: over a product of four coin blocks, if
each block's event has marginal `≤ εᵢ`, the union has probability
`≤ ε₁ + ε₂ + ε₃ + ε₄`. Union bound (`uniformProb_or_le`, Depth's toolkit) +
exact product marginals; independence is never used — only the marginal
prices, which each landed component theorem supplies at its own coins. -/
private theorem uniformProb_four_prod_le
    {Ω₁ Ω₂ Ω₃ Ω₄ : Type} [Fintype Ω₁] [Fintype Ω₂] [Fintype Ω₃] [Fintype Ω₄]
    [Nonempty Ω₁] [Nonempty Ω₂] [Nonempty Ω₃] [Nonempty Ω₄]
    (p₁ : Ω₁ → Prop) (p₂ : Ω₂ → Prop) (p₃ : Ω₃ → Prop) (p₄ : Ω₄ → Prop)
    {ε₁ ε₂ ε₃ ε₄ : ℝ}
    (h₁ : uniformProb Ω₁ p₁ ≤ ε₁) (h₂ : uniformProb Ω₂ p₂ ≤ ε₂)
    (h₃ : uniformProb Ω₃ p₃ ≤ ε₃) (h₄ : uniformProb Ω₄ p₄ ≤ ε₄) :
    uniformProb (Ω₁ × Ω₂ × Ω₃ × Ω₄)
      (fun c => p₁ c.1 ∨ p₂ c.2.1 ∨ p₃ c.2.2.1 ∨ p₄ c.2.2.2)
      ≤ ε₁ + ε₂ + ε₃ + ε₄ := by
  have m₁ : uniformProb (Ω₁ × Ω₂ × Ω₃ × Ω₄) (fun c => p₁ c.1)
      = uniformProb Ω₁ p₁ := uniformProb_fst_marg p₁
  have m₂ : uniformProb (Ω₁ × Ω₂ × Ω₃ × Ω₄) (fun c => p₂ c.2.1)
      = uniformProb Ω₂ p₂ :=
    (uniformProb_snd_marg (fun y : Ω₂ × Ω₃ × Ω₄ => p₂ y.1)).trans
      (uniformProb_fst_marg p₂)
  have m₃ : uniformProb (Ω₁ × Ω₂ × Ω₃ × Ω₄) (fun c => p₃ c.2.2.1)
      = uniformProb Ω₃ p₃ :=
    ((uniformProb_snd_marg (fun y : Ω₂ × Ω₃ × Ω₄ => p₃ y.2.1)).trans
      (uniformProb_snd_marg (fun y : Ω₃ × Ω₄ => p₃ y.1))).trans
      (uniformProb_fst_marg p₃)
  have m₄ : uniformProb (Ω₁ × Ω₂ × Ω₃ × Ω₄) (fun c => p₄ c.2.2.2)
      = uniformProb Ω₄ p₄ :=
    ((uniformProb_snd_marg (fun y : Ω₂ × Ω₃ × Ω₄ => p₄ y.2.2)).trans
      (uniformProb_snd_marg (fun y : Ω₃ × Ω₄ => p₄ y.2))).trans
      (uniformProb_snd_marg p₄)
  have hu : uniformProb (Ω₁ × Ω₂ × Ω₃ × Ω₄)
      (fun c => p₁ c.1 ∨ p₂ c.2.1 ∨ p₃ c.2.2.1 ∨ p₄ c.2.2.2)
      ≤ uniformProb (Ω₁ × Ω₂ × Ω₃ × Ω₄) (fun c => p₁ c.1)
        + (uniformProb (Ω₁ × Ω₂ × Ω₃ × Ω₄) (fun c => p₂ c.2.1)
          + (uniformProb (Ω₁ × Ω₂ × Ω₃ × Ω₄) (fun c => p₃ c.2.2.1)
            + uniformProb (Ω₁ × Ω₂ × Ω₃ × Ω₄) (fun c => p₄ c.2.2.2))) := by
    have h34 : uniformProb (Ω₁ × Ω₂ × Ω₃ × Ω₄)
        (fun c => p₃ c.2.2.1 ∨ p₄ c.2.2.2)
        ≤ uniformProb (Ω₁ × Ω₂ × Ω₃ × Ω₄) (fun c => p₃ c.2.2.1)
          + uniformProb (Ω₁ × Ω₂ × Ω₃ × Ω₄) (fun c => p₄ c.2.2.2) :=
      uniformProb_or_le _ _
    have h234 : uniformProb (Ω₁ × Ω₂ × Ω₃ × Ω₄)
        (fun c => p₂ c.2.1 ∨ p₃ c.2.2.1 ∨ p₄ c.2.2.2)
        ≤ uniformProb (Ω₁ × Ω₂ × Ω₃ × Ω₄) (fun c => p₂ c.2.1)
          + (uniformProb (Ω₁ × Ω₂ × Ω₃ × Ω₄) (fun c => p₃ c.2.2.1)
            + uniformProb (Ω₁ × Ω₂ × Ω₃ × Ω₄) (fun c => p₄ c.2.2.2)) :=
      le_trans (uniformProb_or_le _ _) (by linarith)
    exact le_trans (uniformProb_or_le _ _) (by linarith)
  rw [m₁, m₂, m₃, m₄] at hu
  linarith

/-- The affine generator's `pr` IS `uniformProb` over the field — the seed is
`F` with constant weight `1/|F|`, so the weighted sum over the event's seeds
is exactly the counting probability. The bridge from
`hasMutualCorrelatedAgreement_UD`'s measure into the composition's. -/
private theorem affinePr_eq_uniformProb {F : Type} [Field F] [Fintype F]
    [DecidableEq F] (E : (Fin 2 → F) → Prop) :
    (affineGenerator F).pr E = uniformProb F (fun γ => E ![1, γ]) := by
  classical
  unfold ProximityGenerator.pr uniformProb
  have hfilter : (Finset.univ.filter fun ω : (affineGenerator F).Seed =>
      E ((affineGenerator F).gen ω))
      = (Finset.univ.filter fun γ : F => E ![1, γ]) :=
    Finset.filter_congr fun γ _ => Iff.rfl
  have hcard : Nat.card {γ : F // E ![1, γ]}
      = (Finset.univ.filter fun γ : F => E ![1, γ]).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype _
  rw [hfilter, hcard]
  calc ∑ ω ∈ Finset.univ.filter (fun γ : F => E ![1, γ]),
        (affineGenerator F).weight ω
      = ∑ _ω ∈ Finset.univ.filter (fun γ : F => E ![1, γ]),
          ((Fintype.card F : ℝ))⁻¹ := Finset.sum_congr rfl fun ω _ => rfl
    _ = ((Finset.univ.filter fun γ : F => E ![1, γ]).card : ℝ)
          * ((Fintype.card F : ℝ))⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((Finset.univ.filter fun γ : F => E ![1, γ]).card : ℝ)
          / (Fintype.card F : ℝ) := (div_eq_mul_inv _ _).symm

end Marginals

/-! ## §3 `soundnessError_bound` — the composition theorem

The joint failure event over the product coin space — grinding coins ×
per-link sumcheck challenges × hash coins × the decider's fold challenge — is
bounded by `soundnessError P`. Every hypothesis of the four landed theorems is
forwarded, none re-derived; the mutual-CA hypothesis is DISCHARGED by the
proved `hasMutualCorrelatedAgreement_UD` (no `hMCA` left free), which is what
pins `err⋆ = n/|F|` and makes the budget a closed-form number. -/

set_option maxHeartbeats 1600000 in
/-- **The end-to-end composition.** Over one product draw of all four coin
blocks, the probability that ANY component fails — the grinding adversary
forges the FS light client, some link's sumcheck accepts a false claim, the
hash adversary equivocates the commitment, or the decider's fold challenge
lands in the mutual-CA failure set — is at most `soundnessError P`.

By `uniformProb_four_prod_le` (union bound + exact marginals) with the four
landed citations: `lightClientGrinding_sound`, `sumcheck_soundness` (once per
link, `uniformProb_exists_le` over the chain), `commitCR_of_RO_pow`, and
`hasMutualCorrelatedAgreement_UD` (through `affinePr_eq_uniformProb`). The
product-measure honesty note is `[BUDGET-compose]`, §5. -/
theorem soundnessError_bound
    {Root ι F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι] [Nonempty ι] {r : ℕ} {D : Type}
    (P : SoundnessParams)
    (foldRoot : Root → F → Root → Root) (dom : ι ↪ F) {dd : ℕ}
    {A₀ : AccClaim Root F ι r} {T : ℕ} {chs : Fin T → Chain Root F ι r}
    {qs : List (LcQuery Root F ι r)}
    {wss : Fin T → List (ι → F)} {f0s : Fin T → ι → F} {δ dC : ℝ}
    {prover honest : Fin P.depth → ℕ → Polynomial F} {Hc Sc : Fin P.depth → F}
    (Adv : BreakAdversary D P.hashQueries (2 ^ P.hashBits))
    (pf : Fin 2 → ι → F)
    -- the code: RS at rate dd/n, `d ≤ n`
    (hdn : dd ≤ Fintype.card ι)
    -- grinding (`lightClientGrinding_sound`'s hypotheses, forwarded)
    (hnd : qs.Nodup)
    (hcov : ∀ (i : Fin T) (k : Fin (chs i).length),
      linkPrefix A₀ (chs i) (k : ℕ) ∈ qs)
    (hn : ∀ i, (chs i).length ≤ P.depth)
    (hne : ∀ i, chs i ≠ []) (hinj : Function.Injective chs)
    (halign : ∀ i, Aligned A₀ (chs i))
    (hdC : ∀ u ∈ reedSolomonCode dom dd, ∀ v ∈ reedSolomonCode dom dd,
      u ≠ v → dC ≤ relDist u v)
    (hδ0 : 0 < δ)
    (hδB : δ < 1 - (2 + (dd : ℝ) / (Fintype.card ι : ℝ)) / 3)
    (hδC : δ < dC / 2)
    (hlen : ∀ i, (wss i).length = (chs i).length)
    (hfalse : ∀ i, ∃ p ∈ (chs i).zip (wss i), ∀ v ∈ reedSolomonCode dom dd,
      relDist p.2 v ≤ δ →
        ¬ AccClaim.Satisfies (reedSolomonCode dom dd) p.1.claim v)
    (dflt : (i : Fin T) → Fin (chs i).length → F)
    -- sumcheck (`sumcheck_soundness`'s hypotheses, one run per link)
    (hProverDeg : ∀ (j : Fin P.depth) i, i < P.scRounds →
      (prover j i).degree < ((P.scDegree + 1 : ℕ) : WithBot ℕ))
    (hHonestDeg : ∀ (j : Fin P.depth) i, i < P.scRounds →
      (honest j i).degree < ((P.scDegree + 1 : ℕ) : WithBot ℕ))
    (hHonest : ∀ (j : Fin P.depth) (rv : Fin P.scRounds → F) i,
      i < P.scRounds → (honest j i).eval 0 + (honest j i).eval 1
        = scChain (Sc j) (honest j) (chalOf rv) i)
    -- the knobs match the objects
    (hPF : P.fieldCard = Fintype.card F) (hPn : P.codeLen = Fintype.card ι)
    (hPt : P.queries = qs.length) :
    uniformProb ((Fin qs.length → F) × ((Fin P.depth → (Fin P.scRounds → F)) ×
        ((Fin P.hashQueries → Fin (2 ^ P.hashBits)) × F)))
      (fun c =>
        -- (1) the grinding adversary forges the FS light client
        (∃ i, ∃ w, relDist (foldWords
            (padSched (fsSchedule (Oracle.ofList qs c.1) A₀ (chs i) (dflt i)))
            (f0s i) (wss i)) w ≤ δ ∧
          AccClaim.Satisfies (reedSolomonCode dom dd)
            (aggregate foldRoot
              (padSched (fsSchedule (Oracle.ofList qs c.1) A₀ (chs i)
                (dflt i)))
              A₀ (chs i)) w) ∨
        -- (2) some link's sumcheck accepts a false claim
        (∃ j, AcceptsFalse (prover j) (honest j) (Hc j) (Sc j) (c.2.1 j)) ∨
        -- (3) the hash adversary equivocates the commitment
        Adv.Wins c.2.2.1 ∨
        -- (4) the decider's fold challenge fails mutual agreement
        MutualCAFailure (reedSolomonCode dom dd) δ pf ![1, c.2.2.2])
      ≤ soundnessError P := by
  haveI : Nonempty F := ⟨0⟩
  haveI : Nonempty (Fin (2 ^ P.hashBits)) := ⟨⟨0, by positivity⟩⟩
  -- (1) grinding — `lightClientGrinding_sound` at the UD-proved mutual CA
  have b1 : uniformProb (Fin qs.length → F) (fun c₁ => ∃ i, ∃ w,
        relDist (foldWords
          (padSched (fsSchedule (Oracle.ofList qs c₁) A₀ (chs i) (dflt i)))
          (f0s i) (wss i)) w ≤ δ ∧
        AccClaim.Satisfies (reedSolomonCode dom dd)
          (aggregate foldRoot
            (padSched (fsSchedule (Oracle.ofList qs c₁) A₀ (chs i) (dflt i)))
            A₀ (chs i)) w)
      ≤ ((qs.length : ℝ) + (P.depth : ℝ)) * ((P.depth : ℝ) *
          ((Fintype.card ι : ℝ) / (Fintype.card F : ℝ)
            + 1 / (Fintype.card F : ℝ))) :=
    lightClientGrinding_sound foldRoot hnd hcov hn hne hinj halign hdC
      (hasMutualCorrelatedAgreement_UD dom hdn) hδ0 hδB hδC
      (by positivity) hlen hfalse dflt
  -- (2) sumcheck — one landed run per link, union over the chain
  have b2 : uniformProb (Fin P.depth → (Fin P.scRounds → F))
        (fun c₂ => ∃ j, AcceptsFalse (prover j) (honest j) (Hc j) (Sc j)
          (c₂ j))
      ≤ (P.depth : ℝ) * ((P.scRounds : ℝ) *
          ((P.scDegree : ℝ) / (Fintype.card F : ℝ))) := by
    have hun := uniformProb_exists_le (C := Fin P.depth → (Fin P.scRounds → F))
      (p := fun j c₂ => AcceptsFalse (prover j) (honest j) (Hc j) (Sc j)
        (c₂ j))
    have hj : ∀ j : Fin P.depth,
        uniformProb (Fin P.depth → (Fin P.scRounds → F))
          (fun c₂ => AcceptsFalse (prover j) (honest j) (Hc j) (Sc j) (c₂ j))
        ≤ (P.scRounds : ℝ) * ((P.scDegree : ℝ) / (Fintype.card F : ℝ)) := by
      intro j
      haveI : Nonempty ({i : Fin P.depth // i ≠ j} → (Fin P.scRounds → F)) :=
        ⟨fun _ => Classical.arbitrary _⟩
      have hx := uniformProb_equiv (splitCoord j)
        (p := fun x : ({i : Fin P.depth // i ≠ j} → (Fin P.scRounds → F))
            × (Fin P.scRounds → F) =>
          AcceptsFalse (prover j) (honest j) (Hc j) (Sc j) x.2)
      have hy := uniformProb_snd_marg
        (A := {i : Fin P.depth // i ≠ j} → (Fin P.scRounds → F))
        (B := Fin P.scRounds → F)
        (AcceptsFalse (prover j) (honest j) (Hc j) (Sc j))
      exact le_of_eq (hx.trans hy) |>.trans
        (sumcheck_soundness (hProverDeg j) (hHonestDeg j)
          (fun rv i hi => hHonest j rv i hi))
    refine le_trans hun (le_trans (Finset.sum_le_sum fun j _ => hj j)
      (le_of_eq ?_))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- (3) collision — the birthday bound at the `2^h` range
  have b3 : uniformProb (Fin P.hashQueries → Fin (2 ^ P.hashBits)) Adv.Wins
      ≤ (P.hashQueries : ℝ) * ((P.hashQueries : ℝ) - 1)
          / (2 ^ (P.hashBits + 1) : ℝ) :=
    commitCR_of_RO_pow P.hashQueries P.hashBits Adv
  -- (4) the decider's proximity-gap draw — the proved UD error
  have b4 : uniformProb F (fun γ =>
        MutualCAFailure (reedSolomonCode dom dd) δ pf ![1, γ])
      ≤ (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) :=
    (affinePr_eq_uniformProb _).symm.trans_le
      (hasMutualCorrelatedAgreement_UD dom hdn pf δ hδ0 hδB)
  -- the union-bound composition, then the numeric identification
  have htot := uniformProb_four_prod_le _ _ _ _ b1 b2 b3 b4
  refine le_trans htot (le_of_eq ?_)
  unfold soundnessError grindingTerm sumcheckTerm crTerm proximityTerm
    errStarUD
  rw [hPF, hPn, hPt]

/-! ## §4 Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

The deployed instantiation computes the NUMBER (satisfiable), the dominant
term is exhibited and the next bit refuted (teeth), and the composition
theorem FIRES on the landed F₅ witnesses end to end (premise inhabitation). -/

/-- **The deployed parameters** — BabyBear⁴ challenge field
(`p = 2013265921 = 15·2²⁷ + 1`, the PROVED prime of
`Compiler/EmitSerialize.lean`; `|F| = p⁴ ≈ 2^{123.63}`), code length `2^{20}`
(the benchmarked fold domain), rate `1/2`, `δ = 1/8` (inside the UD radius
`1/6`), grinding/hash budgets `2^{40}`, chain depth `2^8`, sumcheck `20`
rounds at degree `≤ 3`, ideal hash range `2^{248}`. The Rust commitment carrier
now uses nine BabyBear limbs (eight are slightly below 248 bits), but carrier
width alone does not instantiate this ideal collision-resistant range,
target λ = 55 — the level the budget PROVES (`deployedBudget_secure`) and
whose successor it refutes (`deployedBudget_ceiling`). -/
noncomputable def deployedBudget : SoundnessParams where
  fieldCard := 2013265921 ^ 4
  codeLen := 2 ^ 20
  degree := 2 ^ 19
  delta := 1 / 8
  queries := 2 ^ 40
  depth := 2 ^ 8
  scRounds := 20
  scDegree := 3
  hashQueries := 2 ^ 40
  hashBits := 248
  secparam := 55

/-- **Satisfiable — THE NUMBER: 55 bits.** The deployed composed soundness
error is at most `2^{−55}`. Exact integer arithmetic at the honest BabyBear
prime (not the round `2^{31}`): the margin is
`(t+k)·k·(n+1)·2^{55} ≈ 0.65·p⁴`. -/
theorem deployedBudget_secure : soundnessError deployedBudget ≤ 1 / 2 ^ 55 := by
  norm_num [soundnessError, grindingTerm, sumcheckTerm, crTerm, proximityTerm,
    errStarUD, deployedBudget]

/-- **Teeth — the 56th bit is REFUTED**: the composed error strictly exceeds
`2^{−56}`; the deployed budget sits in `(2^{−56}, 2^{−55}]`. 55 is the
pessimistic label and it is tight to the bit. -/
theorem deployedBudget_ceiling : 1 / 2 ^ 56 < soundnessError deployedBudget := by
  norm_num [soundnessError, grindingTerm, sumcheckTerm, crTerm, proximityTerm,
    errStarUD, deployedBudget]

/-- **Teeth — the dominant term identified**: the sumcheck + CR + proximity
terms TOGETHER are below `2^{−100}`, while the grinding term alone already
exceeds `2^{−56}`. The budget is the grinding term
`(t+k)·k·(n+1)/|F|` to within one part in `2^{44}`: the load-bearing knobs
are the challenge-field size and the `t·k·n` numerator — tightening anything
else buys nothing, and `[LC-grinding-native]`'s per-fold sharpening would buy
exactly `log₂ k = 8` bits. -/
theorem deployedBudget_grinding_dominant :
    sumcheckTerm deployedBudget + crTerm deployedBudget
        + proximityTerm deployedBudget ≤ 1 / 2 ^ 100
      ∧ 1 / 2 ^ 56 < grindingTerm deployedBudget := by
  constructor <;>
    norm_num [sumcheckTerm, crTerm, proximityTerm, grindingTerm, errStarUD,
      deployedBudget]

/-- The deployed `δ = 1/8` is ADMISSIBLE at unique decoding: strictly inside
`(0, 1 − (2+ρ)/3) = (0, 1/6)` at rate `ρ = 1/2` — the side condition every
proximity citation in `soundnessError_bound` demands, checked at the deployed
knobs. -/
theorem deployedBudget_delta_admissible :
    0 < deployedBudget.delta ∧ deployedBudget.delta
      < 1 - (2 + (deployedBudget.degree : ℝ) / (deployedBudget.codeLen : ℝ))
          / 3 := by
  constructor <;> norm_num [deployedBudget]

/-! ### Premise inhabitation — the composition FIRES on landed F₅ witnesses -/

section BudgetExample

open Minidregg.Loom.RSExample Minidregg.Loom.AccExample Minidregg.Loom.LCExample
  Minidregg.Loom.LCSoundExample Minidregg.Loom.LCGrindExample
  Minidregg.Loom.BirthdayExample

/-- The F₅ keystone knobs: `|F| = 5`, `n = 4`, RS degree `2` (rate `1/2`),
`δ = 1/16`, the landed 4-query grind over the phantom pair (`t = 4`, `k = 2`),
a degenerate zero-round sumcheck, and the landed two-query birthday adversary
(`q = 2`, `h = 1`). -/
noncomputable def budgetF₅ : SoundnessParams :=
  ⟨5, 4, 2, 1 / 16, 4, 2, 0, 0, 2, 1, 0⟩

private theorem chainsF₅_ne : phantomChain ≠ phantomSwapChain := fun h =>
  absurd (congrArg
    (fun ch : Chain (ZMod 5) (ZMod 5) (Fin 4) 1 =>
      (ch.map Link.pre).head?) h) (by decide)

/-- **Premise inhabitation — `soundnessError_bound` FIRES.** Every hypothesis
of the composition discharged by LANDED witnesses: the grinding pair
`grindChs` with its `Nodup` 4-query run and δ-far-false links
(`phantomClaim₀_unsatisfiable` — false against ALL codewords, a fortiori
against the δ-close ones), the zero-round sumcheck (its hypotheses vacuous,
its event impossible), the birthday adversary `A₂`, and a proximity draw on
the zero pair — all against the RS code `reedSolomonCode dom₅ 2` with the
PROVED UD mutual CA. (Numerically `soundnessError budgetF₅ = 133/10 > 1`,
vacuous as a probability bound — the deliberately tiny field prices the
deployment regime `|F| ≫ t·k·n`, exactly as
`Loom/LightClientGrinding.lean`'s headline notes; the deployed keystone above
carries the real number. What fires here is the PREMISES.) -/
theorem budget_fired :
    uniformProb ((Fin grindQs.length → ZMod 5) ×
        ((Fin budgetF₅.depth → (Fin budgetF₅.scRounds → ZMod 5)) ×
          ((Fin budgetF₅.hashQueries → Fin (2 ^ budgetF₅.hashBits))
            × ZMod 5)))
      (fun c =>
        (∃ i, ∃ w, relDist (foldWords
            (padSched (fsSchedule (Oracle.ofList grindQs c.1) phantomGenesis
              (grindChs i) (fun _ => 0)))
            0 [0, 0]) w ≤ 1 / 16 ∧
          AccClaim.Satisfies (reedSolomonCode dom₅ 2)
            (aggregate linRoot
              (padSched (fsSchedule (Oracle.ofList grindQs c.1)
                phantomGenesis (grindChs i) (fun _ => 0)))
              phantomGenesis (grindChs i)) w) ∨
        (∃ j, AcceptsFalse ((fun _ _ => 0) j) ((fun _ _ => 0) j)
          ((fun _ => 0) j) ((fun _ => 0) j) (c.2.1 j)) ∨
        A₂.Wins c.2.2.1 ∨
        MutualCAFailure (reedSolomonCode dom₅ 2) (1 / 16) ![0, 0]
          ![1, c.2.2.2])
      ≤ soundnessError budgetF₅ := by
  refine soundnessError_bound budgetF₅ linRoot dom₅ A₂ ![0, 0]
    (by norm_num)
    grindQs_nodup grindChs_cover
    (fun i => by
      fin_cases i <;> norm_num [grindChs, phantomChain, phantomSwapChain,
        budgetF₅])
    (fun i => by
      fin_cases i <;> simp [grindChs, phantomChain, phantomSwapChain])
    (fun i j hij => by
      fin_cases i <;> fin_cases j
      · rfl
      · exact absurd hij chainsF₅_ne
      · exact absurd hij.symm chainsF₅_ne
      · rfl)
    (fun i => by
      fin_cases i
      · exact phantomChain_aligned
      · exact phantomSwapChain_aligned)
    (minDistLB_inhabited _)
    (by norm_num)
    (by norm_num [Fintype.card_fin])
    (by norm_num [Fintype.card_fin])
    (fun i => by fin_cases i <;> rfl)
    (fun i => by
      fin_cases i
      · exact ⟨(⟨0, 1, phantomClaim₀⟩, 0), List.mem_cons_self ..,
          fun v _ _ hsat => phantomClaim₀_unsatisfiable ⟨v, hsat⟩⟩
      · exact ⟨(⟨0, 1, phantomClaim₀⟩, 0),
          List.mem_cons_of_mem _ (List.mem_cons_self ..),
          fun v _ _ hsat => phantomClaim₀_unsatisfiable ⟨v, hsat⟩⟩)
    (fun _ _ => 0)
    (fun j i hi => absurd hi (Nat.not_lt_zero i))
    (fun j i hi => absurd hi (Nat.not_lt_zero i))
    (fun j rv i hi => absurd hi (Nat.not_lt_zero i))
    (ZMod.card 5).symm (Fintype.card_fin 4).symm rfl

/-- The F₅ keystone budget, computed: `133/10` — grinding `12`, sumcheck `0`,
birthday `1/2`, proximity `4/5`. The expression genuinely computes on any
instance (satisfiable at the formula level); its vacuity as a probability on
F₅ is the honest small-field note in `budget_fired`'s docstring. -/
theorem budgetF₅_value : soundnessError budgetF₅ = 133 / 10 := by
  norm_num [soundnessError, grindingTerm, sumcheckTerm, crTerm, proximityTerm,
    errStarUD, budgetF₅]

end BudgetExample

/-! ## §5 Residual ledger — prose, not stubs

**What CLOSED here.** The composed soundness-error EXPRESSION
(`soundnessError`: four landed right-hand sides, summed), the union-bound
COMPOSITION (`soundnessError_bound`: a real theorem over one product coin
space — union bound + exact product marginals + the four citations, mutual CA
DISCHARGED by the proved UD realizer, no `hMCA` hypothesis left free), and
the deployed NUMBER (`deployedBudget_secure`/`_ceiling`: 55 bits, tight to
the bit, dominant term identified). No `sorry`, no `def : Prop := True`.

**[BUDGET-compose]** — the shared-oracle composition, owed. The composition
above is at the PRODUCT measure: four independent coin blocks, one per
component event. The deployed system runs ONE oracle — the FS schedule, the
per-link sumcheck challenges, and the commitment digests are all answers of
one hash, and the decider's fold challenge is FS-derived. The shared-oracle
rendering — all four events as reads of ONE lazy-sampling handler, with
domain separation making the four query families pairwise disjoint, whence
the product marginals above are EXACT by the same injection-marginal argument
as `uniformProb_comp_injective` (`Loom/LightClientGrinding.lean`) — is what
`[BUDGET-compose]` names; it rides `[FS-ROM]` for the handler itself. The SUM
and the union-bound structure are unaffected: the union bound never needed
independence (the grinding file's audit note), only the marginal prices,
which each landed theorem supplies at its own coins. Also under this name:
the four adversary objects are quantified separately here; identifying them
as ONE prover's single execution (its grind, its sumcheck messages, its
commitment queries, one transcript feeding all four events) is the same
one-run coupling `Assurance/LoomV0.lean`'s residual block names for the
capstone — inherited, not new.

**The floor, inherited unchanged** (no summand — an idealization is not an
event with a proven probability; it is named beside the number, never added
silently): `[FS-ROM]` (the deployed sponge realizes the handler; domain
separation), `[ACC-extract-bind]` (partial-opening/erasure lift),
`[ACC-rbr-bcs]` (the deployed root-and-columns alphabet),
`[COMMIT-CR]`(i)/(iii) (the Merkle tree walk — `crTerm` prices the CR
ENDPOINT; the tree-path reduction to it is owed there),
`[CR-ROM-adaptive]` (birthday at non-adaptive schedules; the claimed pair is
adaptive), and UNIQUE DECODING (`err⋆ = n/|F|` proved only for
`δ < (1−ρ)/3`; beyond-UD would shrink nothing here — `err⋆` is already the
smaller of the two `1/|F|`-scale terms — but would widen the admissible δ).

**Sharpening named, with its price computed**: `[LC-grinding-native]`
(`Loom/LightClientGrinding.lean`) would replace the grinding term's
per-try·per-chain `(t+k)·k·(err⋆+1/|F|)` by per-query·per-fold
`(t+k)·(err⋆+1/|F|)` — at the deployed knobs exactly `log₂ k = 8` more bits
(55 → 63). The engine is landed (`accFsSound_native`); the transport is owed
there, not here.

## Ledger

* `SoundnessParams` — the deployment knobs, λ carried as the label.
* `errStarUD` / `grindingTerm` / `sumcheckTerm` / `crTerm` /
  `proximityTerm` / `soundnessError` — the composed expression, each summand
  a landed RHS verbatim; `budget_accRbrError` ties the per-fold factor to
  `accRbrError` by `rfl`.
* `uniformProb_four_prod_le` + marginals + `affinePr_eq_uniformProb` —
  the union-bound skeleton (private plumbing).
* `soundnessError_bound` — THE COMPOSITION, four citations forwarded.
* `deployedBudget` / `deployedBudget_secure` / `deployedBudget_ceiling` /
  `deployedBudget_grinding_dominant` / `deployedBudget_delta_admissible` —
  the number: **55 bits, in `(2^{−56}, 2^{−55}]`, grinding-dominated**, at
  BabyBear⁴ / `n = 2^{20}` / `ρ = 1/2` / `t = q = 2^{40}` / `k = 2^8`.
* `budgetF₅` / `budget_fired` / `budgetF₅_value` — premise inhabitation on
  landed F₅ witnesses, with the small-field vacuity said out loud.
* `#print axioms` on every headline: `propext`, `Classical.choice`,
  `Quot.sound` only; no `sorry`. -/

#check @soundnessError_bound
#check @deployedBudget_secure
#check @deployedBudget_grinding_dominant

end Minidregg.Assurance
