/-
# Bfv.Smudging — the noise-flooding SECURITY theorem (what fhe.rs mbfv's smudging `TODO` lacks).

**The failure this module kills (class D of the silent-failure taxonomy):** in the n-of-n
threshold decrypt, each party publishes a partial decryption of the folded ciphertext. Without
smudging, that share is `(publicly predictable value) + e_ct` — and `e_ct`, the ciphertext noise,
is a function of the secret material (key + encryption randomness). Publishing it LEAKS. fhe.rs's
`mbfv` marks its smudging noise as an upstream `TODO`: the share is published with fresh-noise
smudging that has no proven relation to the thing it must hide. This module proves the actual
noise-flooding bound, both directions:

  * **hiding (the security side):** smudge uniformly from `[-2^b, 2^b]` with `2^b` a factor
    `2^secbits` above the ciphertext-noise magnitude, and the share's distribution moves by at
    most `2^-secbits` in statistical distance when the secret noise changes — i.e. the share is
    statistically near-independent of the key-share-dependent term, and simulatable from public
    data alone (`share_simulatable`).
  * **leaking (the failing side, REQUIRED):** smudge below the bound and the leak is REAL:
    `smudge_too_small_leaks` proves statistical distance **1** (perfect distinguishability) the
    moment the smudge interval is smaller than the noise gap, and
    `smudge_too_small_distinguishes` exhibits the pointwise distinguisher (every observable
    share value is consistent with exactly one of the two candidate secrets).

## The model, stated precisely (fidelity — what IS and is NOT proved)

  * **The distribution model is exact and finite:** a smudged share is `center + u` with `u`
    UNIFORM on the integer interval `[-S, S]` — mass function `shareMass`, proved to be an honest
    probability distribution (`sum_shareMass = 1`). The security statement is a **statistical
    (total-variation) distance bound**, computed EXACTLY (`sd_eq`), not an inequality chain with
    slack: `sd = min(|Δcenter|, 2S+1) / (2S+1)`. This is NOT perfect secrecy and is not claimed
    to be: the residual `≤ 2·B/(2S+1)` is the proven fidelity.
  * **The reduction of the mbfv share to `known + secret + u` is a MODEL step, not a theorem.**
    In mbfv, a coalition of the other parties knowing the plaintext can compute the honest
    party's share up to `e_ct + u` (the ciphertext noise plus that party's smudge). Modeling the
    adversary's residual view as `pub + e + u` with `|e| ≤ B` inherits the scalar-coefficient
    model gap NAMED in `Bfv.Noise` (no polynomial ring here), and additionally does not formalize
    the conditioning argument or the RLWE share shape `c₁·s_i`. Named, not hidden.
  * **The smudge distribution must be UNIFORM on `[-S, S]`.** The theorem is about exactly that
    distribution; a Gaussian (or fhe.rs's fresh-noise stand-in) needs its own bound. The Rust
    threshold lane must sample uniformly on the integer interval — the fail-closed sampler gate.
  * **Scalar-share theorem, conditional transcript ledger.** The distribution theorem is per
    coefficient of one honest share against the full coalition of the other n−1 parties (the
    worst case for n-of-n). Section 6 formalizes the deterministic hybrid/union accounting across
    coefficients, parties, and repeated decrypt sessions: `degree · parties · sessions` scalar
    steps each bounded by `2^-48` cost at most their sum. It deliberately does NOT derive the
    joint-view hybrid steps from the scalar theorem: that needs a product-distribution / adaptive-
    conditioning theorem for the real RLWE/RNS transcript. No independence is assumed here.
  * **Out of scope, named:** a full UC/simulation-security proof (this stone is the concrete
    noise-flooding bound that such a proof consumes); the ring lift; RLWE hardness (class B — an
    estimator artifact, never a Lean theorem); the `CommonRandomPoly` honesty assumption.

## The deployed export (what the threshold lane consumes)

  * **`smudgeBits = 80`**: each party samples its smudge uniformly from `[-2^80, 2^80]`.
  * **`deployed_smudge_hides`**: against the deployed fold envelope's ciphertext noise
    (`≤ 2^32 = 4096 orders × 2^20 fresh`, the `Bfv.Fold.deployed_margin_holds` envelope), a
    `2^80` smudge hides the secret term to statistical distance `≤ 2^-48`.
  * **`deployed_smudged_decrypt_exact`**: the OTHER jaw of the vise — 16 parties' worth of
    `2^80` smudge (`≤ 16·2^80 = 2^84`) plus the `2^32` fold noise still sits inside the decrypt
    margin (~`2^88`), so smudging at the hiding bound does NOT break correctness. Both jaws
    proved on the real fhe.rs degree-4096 parameters; the meter can also read empty
    (`deployed_smudge_floor_leaks`: a `2^15` smudge against the same envelope leaks TOTALLY).
  * **`deployed_transcript_hides_of_hybrid`**: once the real transcript supplies the named
    hybrid certificate, 4096 coefficients × at most 16 parties spends 16 bits of the scalar
    ledger per decrypt: `2^-32` per session, `2^-24` across 256 sessions, and `2^-16` across
    65,536 sessions. At `2^32` full sessions the union bound reaches 1 and is vacuous; the session
    count is a load-bearing security parameter, not free reuse of the scalar 48-bit headline.

Pure. No axioms beyond the kernel triple.

**Port provenance (Mini, 2026-10-04).** Copied from breadstuffs `metatheory/Bfv/Smudging.lean`
(sha256 `0bf31610ebbdbe8312c39d7e65772473f16b0424856e066f33efa16fe4dcebb7`), renamespaced `Bfv` → `Minidregg.Theory.Bfv`; statements and proofs
unchanged; Bread's `#assert_all_clean` lists became Mini's `#print axioms` pins, recorded
against Bread's own axiom sets in `docs/BREAD-PORTS.md`. Mathlib-only imports.
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Theory.BfvParams
import Theory.BfvNoise
import Theory.BfvFold

namespace Minidregg.Theory.Bfv.Smudging

/-! ## 1. The smudged-share distribution: uniform on `[center − S, center + S]`. -/

/-- The support of a smudged share centered at `c` with smudge radius `S`:
the integer interval `[c − S, c + S]`. -/
def supp (S : ℕ) (c : ℤ) : Finset ℤ := Finset.Icc (c - (S : ℤ)) (c + (S : ℤ))

/-- The mass function of the smudged share `c + u`, `u` uniform on `[-S, S]`: each of the
`2S + 1` support points carries mass `1/(2S+1)`. -/
def shareMass (S : ℕ) (c x : ℤ) : ℚ :=
  if x ∈ supp S c then (2 * (S : ℚ) + 1)⁻¹ else 0

/-- The support has exactly `2S + 1` points. -/
theorem card_supp (S : ℕ) (c : ℤ) : (supp S c).card = 2 * S + 1 := by
  unfold supp
  rw [Int.card_Icc]
  omega

/-- **`shareMass` is an honest probability distribution**: over any window containing the
support, the masses sum to exactly 1. (A "distribution" that did not normalize would make every
distance bound below vacuous — this is the sanity tooth.) -/
theorem sum_shareMass (S : ℕ) (c : ℤ) (W : Finset ℤ) (hW : supp S c ⊆ W) :
    ∑ x ∈ W, shareMass S c x = 1 := by
  unfold shareMass
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hW, Finset.sum_const, nsmul_eq_mul,
    card_supp]
  push_cast
  field_simp

/-! ## 2. Statistical (total-variation) distance between two smudged shares. -/

/-- The canonical window covering both supports of a pair of centers. -/
def window (S : ℕ) (c₁ c₂ : ℤ) : Finset ℤ :=
  Finset.Icc (min c₁ c₂ - (S : ℤ)) (max c₁ c₂ + (S : ℤ))

theorem supp_subset_window_left (S : ℕ) (c₁ c₂ : ℤ) : supp S c₁ ⊆ window S c₁ c₂ :=
  Finset.Icc_subset_Icc (by omega) (by omega)

theorem supp_subset_window_right (S : ℕ) (c₁ c₂ : ℤ) : supp S c₂ ⊆ window S c₁ c₂ :=
  Finset.Icc_subset_Icc (by omega) (by omega)

/-- **Statistical distance** between the two share distributions centered at `c₁` and `c₂`
(with the same smudge radius `S`): half the L¹ distance of the mass functions. The sum runs over
the canonical covering window; `l1_window_free` proves any covering window gives the same value,
so this IS the total-variation distance over all of ℤ, not a windowed undercount. -/
def sd (S : ℕ) (c₁ c₂ : ℤ) : ℚ :=
  (∑ x ∈ window S c₁ c₂, |shareMass S c₁ x - shareMass S c₂ x|) / 2

/-- The L¹ sum does not depend on the covering window (all mass differences vanish outside the
two supports) — `sd` is well-defined as a distance over all of ℤ. -/
theorem l1_window_free (S : ℕ) (c₁ c₂ : ℤ) (W : Finset ℤ)
    (hW : window S c₁ c₂ ⊆ W) :
    ∑ x ∈ W, |shareMass S c₁ x - shareMass S c₂ x|
      = ∑ x ∈ window S c₁ c₂, |shareMass S c₁ x - shareMass S c₂ x| := by
  refine (Finset.sum_subset hW ?_).symm
  intro x _ hx
  have h₁ : x ∉ supp S c₁ := fun h => hx (supp_subset_window_left S c₁ c₂ h)
  have h₂ : x ∉ supp S c₂ := fun h => hx (supp_subset_window_right S c₁ c₂ h)
  simp [shareMass, h₁, h₂]

/-- Pointwise: `|a − b| = a + b − 2·min a b` (used to turn the L¹ sum into mass sums). -/
theorem abs_sub_eq_add_sub_two_min (a b : ℚ) : |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (by linarith), min_eq_left h]; ring
  · rw [abs_of_nonneg (by linarith), min_eq_right h]; ring

/-- The min of the two mass functions is the (scaled) indicator of the support overlap. -/
theorem sum_min_shareMass (S : ℕ) (c₁ c₂ : ℤ) (W : Finset ℤ)
    (h₁ : supp S c₁ ⊆ W) :
    ∑ x ∈ W, min (shareMass S c₁ x) (shareMass S c₂ x)
      = ((supp S c₁ ∩ supp S c₂).card : ℚ) * (2 * (S : ℚ) + 1)⁻¹ := by
  have hpos : (0 : ℚ) ≤ (2 * (S : ℚ) + 1)⁻¹ := inv_nonneg.mpr (by positivity)
  have hpt : ∀ x ∈ W, min (shareMass S c₁ x) (shareMass S c₂ x)
      = if x ∈ supp S c₁ ∩ supp S c₂ then (2 * (S : ℚ) + 1)⁻¹ else 0 := by
    intro x _
    unfold shareMass
    by_cases hm₁ : x ∈ supp S c₁
    · by_cases hm₂ : x ∈ supp S c₂
      · simp [hm₁, hm₂]
      · simp [hm₁, hm₂, min_eq_right hpos]
    · by_cases hm₂ : x ∈ supp S c₂
      · simp [hm₁, hm₂, min_eq_left hpos]
      · simp [hm₁, hm₂]
  rw [Finset.sum_congr rfl hpt, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr (Finset.inter_subset_left.trans h₁),
    Finset.sum_const, nsmul_eq_mul]

/-- The support overlap is itself an interval. -/
theorem supp_inter (S : ℕ) (c₁ c₂ : ℤ) :
    supp S c₁ ∩ supp S c₂
      = Finset.Icc (max (c₁ - (S : ℤ)) (c₂ - (S : ℤ))) (min (c₁ + (S : ℤ)) (c₂ + (S : ℤ))) := by
  ext x
  simp only [Finset.mem_inter, supp, Finset.mem_Icc, le_min_iff, max_le_iff]
  tauto

/-- **The exact overlap count**: `max 0 (2S+1 − |c₁ − c₂|)` support points coincide. -/
theorem card_supp_inter (S : ℕ) (c₁ c₂ : ℤ) :
    (((supp S c₁ ∩ supp S c₂).card : ℤ)) = max 0 (2 * (S : ℤ) + 1 - |c₁ - c₂|) := by
  rw [supp_inter, Int.card_Icc, Int.toNat_eq_max]
  rcases le_total c₁ c₂ with h | h
  · rw [abs_of_nonpos (by linarith : c₁ - c₂ ≤ 0)]
    omega
  · rw [abs_of_nonneg (by linarith : 0 ≤ c₁ - c₂)]
    omega

/-- The L¹ distance, computed exactly: `2 − 2·overlap/(2S+1)`. -/
theorem l1_eq (S : ℕ) (c₁ c₂ : ℤ) (W : Finset ℤ)
    (h₁ : supp S c₁ ⊆ W) (h₂ : supp S c₂ ⊆ W) :
    ∑ x ∈ W, |shareMass S c₁ x - shareMass S c₂ x|
      = 2 - 2 * (((supp S c₁ ∩ supp S c₂).card : ℚ) * (2 * (S : ℚ) + 1)⁻¹) := by
  have hpt : ∀ x ∈ W, |shareMass S c₁ x - shareMass S c₂ x|
      = shareMass S c₁ x + shareMass S c₂ x
        - 2 * min (shareMass S c₁ x) (shareMass S c₂ x) :=
    fun x _ => abs_sub_eq_add_sub_two_min _ _
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, sum_shareMass S c₁ W h₁, sum_shareMass S c₂ W h₂,
    sum_min_shareMass S c₁ c₂ W h₁]
  ring

/-- **THE EXACT DISTANCE FORMULA**: `sd = 1 − max(0, 2S+1 − |c₁−c₂|)/(2S+1)`, i.e.
`min(|c₁−c₂|, 2S+1)/(2S+1)`. Everything below (both the hiding side AND the leaking side) is a
corollary of this one equation — the security bound and its failure are the SAME fact. -/
theorem sd_eq (S : ℕ) (c₁ c₂ : ℤ) :
    sd S c₁ c₂
      = 1 - ((max 0 (2 * (S : ℤ) + 1 - |c₁ - c₂|) : ℤ) : ℚ) / (2 * (S : ℚ) + 1) := by
  have hne : (2 * (S : ℚ) + 1) ≠ 0 := by positivity
  have hcard : (((supp S c₁ ∩ supp S c₂).card : ℚ))
      = ((max 0 (2 * (S : ℤ) + 1 - |c₁ - c₂|) : ℤ) : ℚ) := by
    exact_mod_cast card_supp_inter S c₁ c₂
  unfold sd
  rw [l1_eq S c₁ c₂ _ (supp_subset_window_left S c₁ c₂) (supp_subset_window_right S c₁ c₂),
    hcard]
  field_simp

/-- Sanity: `sd` is nonnegative (it is a distance, not a signed slack). -/
theorem sd_nonneg (S : ℕ) (c₁ c₂ : ℤ) : 0 ≤ sd S c₁ c₂ := by
  unfold sd
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg fun x _ => abs_nonneg _

/-- Sanity: `sd ≤ 1` — total variation is normalized, so `sd = 1` (the leak theorems below)
really is MAXIMAL distinguishability, not an artifact of an unnormalized metric. -/
theorem sd_le_one (S : ℕ) (c₁ c₂ : ℤ) : sd S c₁ c₂ ≤ 1 := by
  rw [sd_eq]
  have h0 : (0 : ℚ) ≤ ((max 0 (2 * (S : ℤ) + 1 - |c₁ - c₂|) : ℤ) : ℚ) := by
    exact_mod_cast le_max_left 0 (2 * (S : ℤ) + 1 - |c₁ - c₂|)
  have hn : (0 : ℚ) < 2 * (S : ℚ) + 1 := by positivity
  have := div_nonneg h0 hn.le
  linarith

/-! ## 3. The flooding bound (the security side). -/

/-- **The noise-flooding lemma, ratio form**: the statistical distance between two smudged
shares is at most `|Δcenter| / (2S+1)`. (For `|Δ| ≤ 2S+1` this is EXACT, by `sd_eq`.) -/
theorem sd_le_ratio (S : ℕ) (c₁ c₂ : ℤ) :
    sd S c₁ c₂ ≤ ((|c₁ - c₂| : ℤ) : ℚ) / (2 * (S : ℚ) + 1) := by
  have hn : (0 : ℚ) < 2 * (S : ℚ) + 1 := by positivity
  rw [sd_eq]
  rcases le_total (|c₁ - c₂|) (2 * (S : ℤ) + 1) with h | h
  · rw [max_eq_right (by linarith)]
    have hcast : ((2 * (S : ℤ) + 1 - |c₁ - c₂| : ℤ) : ℚ)
        = (2 * (S : ℚ) + 1) - ((|c₁ - c₂| : ℤ) : ℚ) := by
      push_cast
      ring
    rw [hcast, sub_div, div_self hn.ne']
    ring_nf
    exact le_refl _
  · rw [max_eq_left (by linarith)]
    have hd : (2 * (S : ℚ) + 1) ≤ ((|c₁ - c₂| : ℤ) : ℚ) := by exact_mod_cast h
    have h1 : (1 : ℚ) ≤ ((|c₁ - c₂| : ℤ) : ℚ) / (2 * (S : ℚ) + 1) := by
      rw [le_div_iff₀ hn]
      linarith
    simpa using h1

/-- **THE SECURITY THEOREM (hiding).** Model a published partial decryption as
`pub + e + u`: `pub` the coalition-predictable part, `e` the secret-dependent term (the
ciphertext noise, a function of the key share and encryption randomness), `u` the uniform smudge
on `[-S, S]`. Then for ANY two candidate secrets `e₁, e₂` inside the noise envelope `B`, the two
share distributions are within `2B/(2S+1)` total variation — the observed share is statistically
near-independent of which secret produced it. The public offset `pub` drops out exactly. -/
theorem partial_decrypt_hides (S : ℕ) (pub e₁ e₂ B : ℤ)
    (h₁ : |e₁| ≤ B) (h₂ : |e₂| ≤ B) :
    sd S (pub + e₁) (pub + e₂) ≤ 2 * (B : ℚ) / (2 * (S : ℚ) + 1) := by
  refine le_trans (sd_le_ratio S _ _) ?_
  have habs : |pub + e₁ - (pub + e₂)| = |e₁ - e₂| := by
    rw [show pub + e₁ - (pub + e₂) = e₁ - e₂ by ring]
  rw [habs]
  have hle : |e₁ - e₂| ≤ 2 * B := by
    rw [sub_eq_add_neg]
    calc |e₁ + -e₂| ≤ |e₁| + |-e₂| := abs_add_le _ _
      _ = |e₁| + |e₂| := by rw [abs_neg]
      _ ≤ 2 * B := by linarith
  gcongr
  exact_mod_cast hle

/-- **The exponential form the roadmap asks for**: smudge radius at least `2^secbits` times the
noise envelope (`2^secbits · 2B ≤ 2S+1`) drives the distinguishing advantage below
`2^-secbits`. This is "smudging noise exponential in the ciphertext noise magnitude", made
precise as a statistical-distance bound — NOT perfect secrecy, and not claimed as such. -/
theorem partial_decrypt_hides_exp (S secbits : ℕ) (pub e₁ e₂ B : ℤ)
    (h₁ : |e₁| ≤ B) (h₂ : |e₂| ≤ B)
    (hS : 2 ^ secbits * (2 * B) ≤ 2 * (S : ℤ) + 1) :
    sd S (pub + e₁) (pub + e₂) ≤ 1 / (2 : ℚ) ^ secbits := by
  refine le_trans (partial_decrypt_hides S pub e₁ e₂ B h₁ h₂) ?_
  have hn : (0 : ℚ) < 2 * (S : ℚ) + 1 := by positivity
  have hp : (0 : ℚ) < (2 : ℚ) ^ secbits := by positivity
  rw [div_le_div_iff₀ hn hp]
  have hSq : ((2 : ℚ)) ^ secbits * (2 * (B : ℚ)) ≤ 2 * (S : ℚ) + 1 := by exact_mod_cast hS
  nlinarith [hSq, hp.le]

/-- **Simulatability**: the honest share's distribution is within `B/(2S+1)` of the distribution
centered at the PUBLIC value alone (secret term zero) — a simulator holding no key material
produces a statistically indistinguishable share. This is the "no-viewer" property in its
operational form. -/
theorem share_simulatable (S : ℕ) (pub e B : ℤ) (h : |e| ≤ B) :
    sd S (pub + e) pub ≤ (B : ℚ) / (2 * (S : ℚ) + 1) := by
  refine le_trans (sd_le_ratio S _ _) ?_
  have habs : |pub + e - pub| = |e| := by
    rw [show pub + e - pub = e by ring]
  rw [habs]
  gcongr

/-! ## 4. THE FAILING SIDE (required): a sub-bound smudge PROVED to leak. -/

/-- **`smudge_too_small_leaks`** — when the smudge interval is smaller than the gap between two
candidate secrets (`2S+1 ≤ |c₁ − c₂|`), the statistical distance is EXACTLY 1: the supports are
disjoint and the adversary distinguishes with certainty. A hiding theorem whose bound could not
fail would prove nothing; this is the cliff, proved. -/
theorem smudge_too_small_leaks (S : ℕ) (c₁ c₂ : ℤ) (h : 2 * (S : ℤ) + 1 ≤ |c₁ - c₂|) :
    sd S c₁ c₂ = 1 := by
  rw [sd_eq, max_eq_left (by linarith)]
  simp

/-- The pointwise distinguisher behind the leak: under the same sub-bound condition, every share
value with positive probability under secret `c₁` has probability ZERO under secret `c₂` — one
observation determines the secret. -/
theorem smudge_too_small_distinguishes (S : ℕ) (c₁ c₂ x : ℤ)
    (h : 2 * (S : ℤ) + 1 ≤ |c₁ - c₂|)
    (hx : shareMass S c₁ x ≠ 0) : shareMass S c₂ x = 0 := by
  unfold shareMass at hx ⊢
  by_cases h₁ : x ∈ supp S c₁
  · by_cases h₂ : x ∈ supp S c₂
    · exfalso
      unfold supp at h₁ h₂
      rw [Finset.mem_Icc] at h₁ h₂
      rcases abs_cases (c₁ - c₂) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at h <;> omega
    · simp [h₂]
  · simp [h₁] at hx

/-! ## 5. The deployed export: `smudgeBits = 80` on the fhe.rs degree-4096 envelope.

The vise has two jaws and BOTH are proved on the real numbers:
jaw 1 (hiding): `2^80` floods the fold-envelope noise (`≤ 2^32`) to distance `≤ 2^-48`;
jaw 2 (correctness): 16 parties × `2^80` smudge + the fold noise still decrypts EXACTLY. -/

/-- **THE EXPORT**: the smudge bit-width the threshold lane samples to. Each party's smudge is
uniform on the integer interval `[-2^smudgeBits, +2^smudgeBits]` — uniform on EXACTLY that
interval; the theorems are about this distribution and no other. -/
def smudgeBits : ℕ := 80

/-- The smudge radius `S = 2^80`. -/
def smudgeBound : ℕ := 2 ^ smudgeBits

/-- The party-count envelope the correctness jaw is pinned at. -/
def maxPartiesPinned : ℕ := 16

/-- The deployed fold's ciphertext-noise envelope: 4096 orders × `2^20` fresh noise = `2^32`
(the `Bfv.Fold.deployed_margin_holds` envelope; `B_fresh ≈ 2^20` is the same NAMED assumption
it rests on). -/
def deployedCtNoise : ℤ := 2 ^ 32

/-- **Jaw 1 — deployed hiding pin**: on the deployed envelope (secret noise `≤ 2^32`), a
`2^80`-radius uniform smudge makes any two secrets' share distributions `≤ 2^-48`-close.
48 bits of statistical security, stated as the bound it is — not more. -/
theorem deployed_smudge_hides (pub e₁ e₂ : ℤ)
    (h₁ : |e₁| ≤ deployedCtNoise) (h₂ : |e₂| ≤ deployedCtNoise) :
    sd smudgeBound (pub + e₁) (pub + e₂) ≤ 1 / 2 ^ 48 := by
  refine partial_decrypt_hides_exp smudgeBound 48 pub e₁ e₂ deployedCtNoise h₁ h₂ ?_
  norm_num [smudgeBound, smudgeBits, deployedCtNoise]

/-- The margin check for jaw 2, kernel-evaluated on the real 109-bit `q`: fold noise `2^32`
plus 16 parties × `2^80` smudge is inside the decrypt budget. -/
theorem deployed_smudge_margin :
    marginHolds fheRs4096 1 (2 ^ 32 + maxPartiesPinned * smudgeBound) = true := by decide

/-- **Jaw 2 — smudging at the hiding bound does NOT break correctness**: a phase carrying the
deployed fold noise (`|e| ≤ 2^32`) plus the total smudge of 16 parties (`|u| ≤ 16·2^80`) still
decrypts EXACTLY. Hiding and correctness hold simultaneously at `smudgeBits = 80` — the export
is a proven WINDOW, not a one-sided knob. -/
theorem deployed_smudged_decrypt_exact (m : ℕ) (e u : ℤ)
    (hm : m < fheRs4096.t)
    (he : |e| ≤ deployedCtNoise)
    (hu : |u| ≤ (maxPartiesPinned : ℤ) * (smudgeBound : ℤ)) :
    decryptPhase fheRs4096 ((fheRs4096.Δ : ℤ) * m + (e + u)) = m := by
  have hs := marginHolds_safe fheRs4096 1 (2 ^ 32 + maxPartiesPinned * smudgeBound)
    deployed_smudge_margin
  apply decrypt_exact fheRs4096 m (e + u) hm
  apply SafeNoise.mono _ hs
  have h1 : |e + u| ≤ |e| + |u| := abs_add_le _ _
  have he' : |e| ≤ 2 ^ 32 := he
  push_cast
  linarith

/-- **The deployed failing side**: a `2^15` smudge against the SAME deployed envelope leaks
TOTALLY — two in-envelope secrets (`0` and `2^32`) give distance exactly 1. The bound in jaw 1
is load-bearing: shrink the smudge below the noise scale and the no-viewer property is not
degraded but GONE. -/
theorem deployed_smudge_floor_leaks (pub : ℤ) :
    sd (2 ^ 15) pub (pub + 2 ^ 32) = 1 := by
  apply smudge_too_small_leaks
  have habs : |pub - (pub + 2 ^ 32)| = 2 ^ 32 := by
    rw [show pub - (pub + 2 ^ 32) = -(2 ^ 32) by ring, abs_neg,
      abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 ^ 32)]
  rw [habs]
  push_cast

/-! ## 6. Honest transcript composition: a conditional hybrid ledger.

`deployed_smudge_hides` is a scalar theorem. A threshold-decrypt transcript exposes a polynomial
for every publishing party, and a long-lived federation publishes such transcripts repeatedly.
Calling the scalar `2^-48` bound "48-bit transcript security" would therefore be false.

The accounting below uses only the triangle/union shape of a hybrid proof: if a real-to-simulated
transcript path has one scalar replacement per `(session, party, coefficient)`, every replacement
costs at most `2^-48`, and the transcript distance is at most the sum of those step distances, then
the whole view costs at most

`degree · parties · sessions · 2^-48`.

This theorem assumes neither independence nor a product distribution. That honesty has a price:
`TranscriptHybridLedger` is an explicit correspondence obligation. `deployed_smudge_hides` alone
does NOT construct it. The missing bridge must show, for the real RLWE/RNS partial-decrypt view,
that each adaptively conditioned hybrid step is represented by the scalar `shareMass` experiment
(or prove a different conditional step bound), that fresh uniform smudges are used for every
coordinate/session, and that revealing the CRT limbs is just a faithful encoding of one ring
coefficient rather than extra observations. Until that bridge exists, the numbers below are a
sound budget consumed by a future transcript proof, not a claim that the deployed protocol has
already obtained joint-view simulation security.
-/

/-- The proved worst-case scalar distinguishing budget consumed by one hybrid replacement. -/
def deployedScalarEpsilon : ℚ := 1 / (2 : ℚ) ^ 48

/-- One scalar replacement for every coefficient of every published share in every decrypt
session. `sessions` may count batches, decrypt calls inside a batch, or any other transcript reuse;
the ledger intentionally makes the caller account for the chosen protocol boundary. -/
def transcriptCoordinateCount (degree parties sessions : ℕ) : ℕ :=
  degree * parties * sessions

/-- The deterministic union/hybrid budget. It is allowed to exceed one: that is the explicit
vacuity cliff, rather than a silently truncated number that still looks like a security claim. -/
def transcriptAdvBudget (degree parties sessions : ℕ) : ℚ :=
  (transcriptCoordinateCount degree parties sessions : ℚ) * deployedScalarEpsilon

/-- The exact missing bridge between scalar smudging and a joint transcript. A producer supplies
the real-to-simulated transcript distance, one conditional distance per hybrid replacement, the
triangle/union inequality for its hybrid path, and the scalar bound for every step.

No field asserts independence. Correlated/adaptive transcripts are admissible when their
*conditional* hybrid steps meet `step_le`; transcripts for which this cannot be proved do not get
a certificate. -/
structure TranscriptHybridLedger (degree parties sessions : ℕ) where
  /-- Statistical distance between the real and simulated full views. -/
  transcriptDistance : ℚ
  /-- Distance of each consecutive conditional hybrid replacement. -/
  stepDistance : Fin (transcriptCoordinateCount degree parties sessions) → ℚ
  /-- Distances are nonnegative (kept in the certificate so its fields retain metric meaning). -/
  transcript_nonneg : 0 ≤ transcriptDistance
  /-- Every step is a nonnegative distance. -/
  step_nonneg : ∀ i, 0 ≤ stepDistance i
  /-- The transcript hybrid telescopes by triangle inequality. -/
  hybrid_le : transcriptDistance ≤ ∑ i, stepDistance i
  /-- Every adaptively conditioned scalar replacement meets the deployed `2^-48` bound. -/
  step_le : ∀ i, stepDistance i ≤ deployedScalarEpsilon

namespace TranscriptHybridLedger

/-- **Generic composition theorem.** A certified transcript hybrid costs at most the number of
scalar observations times the deployed scalar epsilon. This is deterministic accounting; it does
not need or invent independence. -/
theorem sound {degree parties sessions : ℕ}
    (L : TranscriptHybridLedger degree parties sessions) :
    L.transcriptDistance ≤ transcriptAdvBudget degree parties sessions := by
  calc
    L.transcriptDistance ≤ ∑ i, L.stepDistance i := L.hybrid_le
    _ ≤ ∑ _i : Fin (transcriptCoordinateCount degree parties sessions),
          deployedScalarEpsilon := Finset.sum_le_sum fun i _ => L.step_le i
    _ = transcriptAdvBudget degree parties sessions := by
      simp [transcriptAdvBudget]

end TranscriptHybridLedger

/-- Monotonicity pins the admitted deployed shape: at most 4096 coefficients and 16 parties.
Sessions remain visible because every repeated decrypt spends the budget again. -/
theorem transcriptAdvBudget_deployed_le (degree parties sessions : ℕ)
    (hdegree : degree ≤ 4096) (hparties : parties ≤ maxPartiesPinned) :
    transcriptAdvBudget degree parties sessions
      ≤ transcriptAdvBudget 4096 maxPartiesPinned sessions := by
  unfold transcriptAdvBudget transcriptCoordinateCount deployedScalarEpsilon
  have hcount : degree * parties * sessions ≤ 4096 * maxPartiesPinned * sessions :=
    Nat.mul_le_mul (Nat.mul_le_mul hdegree hparties) (le_refl sessions)
  gcongr

/-- At the full degree-4096, 16-party envelope, each decrypt session costs exactly `2^-32` in
the deterministic ledger: the 4096 coefficients spend 12 bits and the 16 parties spend 4. -/
theorem deployed_max_transcript_budget_eq (sessions : ℕ) :
    transcriptAdvBudget 4096 maxPartiesPinned sessions = (sessions : ℚ) / 2 ^ 32 := by
  norm_num [transcriptAdvBudget, transcriptCoordinateCount, deployedScalarEpsilon,
    maxPartiesPinned]
  ring

/-- **Deployed conditional transcript theorem.** Given the explicit real-transcript hybrid
certificate, any degree-at-most-4096, at-most-16-party transcript over `sessions` decrypts is
within `sessions / 2^32` of its simulator. The hybrid certificate is load-bearing. -/
theorem deployed_transcript_hides_of_hybrid {degree parties sessions : ℕ}
    (L : TranscriptHybridLedger degree parties sessions)
    (hdegree : degree ≤ 4096) (hparties : parties ≤ maxPartiesPinned) :
    L.transcriptDistance ≤ (sessions : ℚ) / 2 ^ 32 := by
  calc
    L.transcriptDistance ≤ transcriptAdvBudget degree parties sessions := L.sound
    _ ≤ transcriptAdvBudget 4096 maxPartiesPinned sessions :=
      transcriptAdvBudget_deployed_le degree parties sessions hdegree hparties
    _ = (sessions : ℚ) / 2 ^ 32 := deployed_max_transcript_budget_eq sessions

/-! ### Numerical teeth: residual bits after repeated full-size decrypts. -/

/-- One full 4096-coefficient, 16-party decrypt has transcript budget exactly `2^-32`. -/
theorem deployed_one_session_residual :
    transcriptAdvBudget 4096 maxPartiesPinned 1 = 1 / (2 : ℚ) ^ 32 := by
  norm_num [deployed_max_transcript_budget_eq]

/-- 256 full decrypt sessions spend another 8 bits: the residual ledger is exactly `2^-24`. -/
theorem deployed_256_session_residual :
    transcriptAdvBudget 4096 maxPartiesPinned 256 = 1 / (2 : ℚ) ^ 24 := by
  norm_num [transcriptAdvBudget, transcriptCoordinateCount, deployedScalarEpsilon,
    maxPartiesPinned]

/-- 65,536 full decrypt sessions spend 16 bits: the residual ledger is exactly `2^-16`. -/
theorem deployed_65536_session_residual :
    transcriptAdvBudget 4096 maxPartiesPinned 65536 = 1 / (2 : ℚ) ^ 16 := by
  norm_num [transcriptAdvBudget, transcriptCoordinateCount, deployedScalarEpsilon,
    maxPartiesPinned]

/-- **The composition failing side.** At `2^32` full-size decrypt sessions the honest union/hybrid
budget is exactly 1, hence vacuous as a statistical-security claim. Repeating a scalar theorem
does not preserve its 48-bit headline. -/
theorem deployed_composition_vacuous_at_2pow32 :
    transcriptAdvBudget 4096 maxPartiesPinned (2 ^ 32) = 1 := by
  norm_num [transcriptAdvBudget, transcriptCoordinateCount, deployedScalarEpsilon,
    maxPartiesPinned]

/-- Past the cliff the untruncated accounting budget is strictly greater than 1. This tooth
prevents treating `transcriptAdvBudget` itself as a normalized statistical distance. -/
theorem deployed_composition_unsafe_past_cliff :
    1 < transcriptAdvBudget 4096 maxPartiesPinned (2 ^ 32 + 1) := by
  norm_num [transcriptAdvBudget, transcriptCoordinateCount, deployedScalarEpsilon,
    maxPartiesPinned]

/-- info: 'Minidregg.Theory.Bfv.Smudging.card_supp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_supp
/-- info: 'Minidregg.Theory.Bfv.Smudging.sum_shareMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sum_shareMass
/-- info: 'Minidregg.Theory.Bfv.Smudging.l1_window_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms l1_window_free
/-- info: 'Minidregg.Theory.Bfv.Smudging.card_supp_inter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_supp_inter
/-- info: 'Minidregg.Theory.Bfv.Smudging.l1_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms l1_eq
/-- info: 'Minidregg.Theory.Bfv.Smudging.sd_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sd_eq
/-- info: 'Minidregg.Theory.Bfv.Smudging.sd_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sd_nonneg
/-- info: 'Minidregg.Theory.Bfv.Smudging.sd_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sd_le_one
/-- info: 'Minidregg.Theory.Bfv.Smudging.sd_le_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sd_le_ratio
/-- info: 'Minidregg.Theory.Bfv.Smudging.partial_decrypt_hides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms partial_decrypt_hides
/-- info: 'Minidregg.Theory.Bfv.Smudging.partial_decrypt_hides_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms partial_decrypt_hides_exp
/-- info: 'Minidregg.Theory.Bfv.Smudging.share_simulatable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms share_simulatable
/-- info: 'Minidregg.Theory.Bfv.Smudging.smudge_too_small_leaks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms smudge_too_small_leaks
/-- info: 'Minidregg.Theory.Bfv.Smudging.smudge_too_small_distinguishes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms smudge_too_small_distinguishes
/-- info: 'Minidregg.Theory.Bfv.Smudging.deployed_smudge_hides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_smudge_hides
/-- info: 'Minidregg.Theory.Bfv.Smudging.deployed_smudge_margin' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_smudge_margin
/-- info: 'Minidregg.Theory.Bfv.Smudging.deployed_smudged_decrypt_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_smudged_decrypt_exact
/-- info: 'Minidregg.Theory.Bfv.Smudging.deployed_smudge_floor_leaks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_smudge_floor_leaks
/-- info: 'Minidregg.Theory.Bfv.Smudging.TranscriptHybridLedger.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms TranscriptHybridLedger.sound
/-- info: 'Minidregg.Theory.Bfv.Smudging.transcriptAdvBudget_deployed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transcriptAdvBudget_deployed_le
/-- info: 'Minidregg.Theory.Bfv.Smudging.deployed_max_transcript_budget_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_max_transcript_budget_eq
/-- info: 'Minidregg.Theory.Bfv.Smudging.deployed_transcript_hides_of_hybrid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_transcript_hides_of_hybrid
/-- info: 'Minidregg.Theory.Bfv.Smudging.deployed_one_session_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_one_session_residual
/-- info: 'Minidregg.Theory.Bfv.Smudging.deployed_256_session_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_256_session_residual
/-- info: 'Minidregg.Theory.Bfv.Smudging.deployed_65536_session_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_65536_session_residual
/-- info: 'Minidregg.Theory.Bfv.Smudging.deployed_composition_vacuous_at_2pow32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_composition_vacuous_at_2pow32
/-- info: 'Minidregg.Theory.Bfv.Smudging.deployed_composition_unsafe_past_cliff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_composition_unsafe_past_cliff

end Minidregg.Theory.Bfv.Smudging
