/-
# Bfv.Mul — the MULTIPLICATIVE stone: ct×ct multiply + relinearization, silent failures made RED.

**The failures this module kills.** Multiplication re-opens BOTH silent-failure classes, and
each is QUALITATIVELY worse than its additive twin:

  * **Class (C), product wrap:** the plaintext PRODUCT `m₁·m₂` wraps mod `t` far faster than a
    sum — with the deployed `t = 1032193`, full-range u16 operands ALREADY wrap
    (`65535² = 4,294,836,225` reads as `913,345`); the safe per-operand cap for one multiply is
    **1015** (`1015² = 1030225 < t < 1016² = 1032256`), against the ADDITIVE capacity of 15 whole
    full-range u16 orders. `product_no_wrap` is the guard theorem; `product_wraps` is the proved
    failing side (a 1016² book truly holds 1,032,256 and READS as **63**).
  * **Class (A), noise amplification:** one ct×ct multiply amplifies the operand noises by the
    MESSAGE SCALE — the proven decomposition has the exact cross-term `m₁e₂ + m₂e₁` (up to
    `(t−1)(B₁+B₂)` at full plaintext range: the `t·(e₁+e₂)` shape), plus a down-scaled quadratic
    `t·e₁e₂/q` and a rounding unit — where addition only ADDS noises. Relinearization then adds
    its key-switch noise ON TOP (modeled at its interface: a bounded additive phase perturbation
    `|e_ks| ≤ B_ks`; the bound is an INPUT, see the honesty ledger). `mul_relin_noise_le` is the
    sound upper bound; `mul_margin_fails_big_noise` + `mul_amplifies_where_add_accepts` prove
    the guard REJECTS — the same 2^80 operand noise the additive margin ACCEPTS is REFUSED by
    the multiplicative one, because M·B crosses the budget. A meter that cannot read empty is
    not a meter.

## The model (the gaps NAMED, not hidden — they are LARGER than the additive ones)

`mulPhase P p₁ p₂ = round(t·p₁·p₂/q)` (round-half-up, the same convention as `decryptPhase`) is
the scalar-model image of the BFV tensor step; `Ct.relin` models relinearization AT ITS NOISE
INTERFACE (an additive phase perturbation, bound supplied as a hypothesis). Three honest gaps:

  1. **The ring lift is MISSING and multiplication makes it load-bearing.** Real BFV multiply is
     a negacyclic polynomial convolution: coefficients MIX, and the true noise bound carries the
     ring expansion factor `δ_R ≤ n = 4096` on the cross-terms. The scalar model proves the
     SHAPE (`t·(e₁+e₂)`-scale growth) with NO `n` factor. Mitigation, pinned:
     `deployed_mul_margin_survives_ring_expansion` — even inflating the ENTIRE proven scalar
     bound by the full `n = 4096`, the deployed margin still holds (~2^36 spare under the ~2^89
     budget). The lift itself (`‖a·b‖_∞ ≤ n·‖a‖_∞·‖b‖_∞` over `R_q = Z_q[X]/(X^n+1)`) is Phase-2.
  2. **The mod-q correspondence does NOT carry over from the add path.** For addition,
     `decryptPhase_add_q` closes the ℤ-model/mod-q gap. Multiplication BREAKS that argument:
     phase products are not `+q`-shift-invariant (`(p₁+q)·p₂ ≠ p₁·p₂ + k·q·Δ`), so the real
     scheme's analysis needs CENTERED (balanced) representatives. This module's theorems are
     exact ℤ-phase arithmetic of the scaled product — the centered-lift correspondence is a
     NAMED, undischarged gap (bigger than the additive one, which is closed in-envelope).
  3. **`B_ks` (relin/key-switch noise) is an ASSUMPTION**, like `B_fresh`: deriving it needs the
     RNS gadget decomposition of fhe.rs's `RelinearizationKey`. The deployed pins budget
     `B_ks ≤ 2^40` — a deliberately generous allowance whose validation is EXACTLY the
     coordination point with the Rust lane's measured oracle (`fhegg-fhe/src/bfv_mul.rs`,
     test `noise_growth_measured`): if the measured post-relin noise exceeds the emitted
     `mulNoiseBound` (with the `n` inflation of gap 1), that is a REAL FINDING — report it,
     do not widen the allowance silently.

## Out of scope, named plainly

  * **Depth > 1 / the multiplicative-depth budget:** these theorems cover ONE multiply (+relin)
    of fresh-noise operands. Chaining (product-of-products, `Σ aᵢ·bᵢ` product-sum folds — the
    `bfv_mul.rs` `product_sum` shape) needs the bound iterated with the OUTPUT noise as the next
    INPUT noise — a depth-budget recursion deliberately not stated until the ring lift (gap 1)
    makes the per-level constant honest.
  * **Bootstrapping** — nothing here models it; the depth budget is what the 3-moduli q buys.
  * **Who holds the relin key** (sk²-material custody in a no-viewer deployment) — a design
    question, not a theorem; named in `bfv_mul.rs`'s ledger too.

Pure. No axioms beyond the kernel triple.

**Port provenance (Mini, 2026-10-04).** Copied from breadstuffs `metatheory/Bfv/Mul.lean`
(sha256 `2ecf22e70d671a1b8244d32df05c8b6fd4b8dac1aac9bd6b9f32cfacda166a02`), renamespaced `Bfv` → `Minidregg.Theory.Bfv`; statements and proofs
unchanged; Bread's `#assert_all_clean` lists became Mini's `#print axioms` pins, recorded
against Bread's own axiom sets in `docs/BREAD-PORTS.md`. Mathlib-only imports.
-/
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Abs
import Theory.BfvParams
import Theory.BfvNoWrap
import Theory.BfvNoise
import Theory.BfvFold

namespace Minidregg.Theory.Bfv

variable {P : Params}

/-! ## 1. The model: scaled phase product + relinearization at its noise interface. -/

/-- Model BFV ct×ct multiply on phases: `round(t·p₁·p₂/q)`, round-half-up, computed exactly in
integer arithmetic as `⌊(2t·p₁p₂ + q) / (2q)⌋` — the same rounding convention as `decryptPhase`.
This is the scalar-model image of the tensor + `t/q`-rescale step (fhe.rs `Multiplicator`). -/
def mulPhase (P : Params) (p₁ p₂ : ℤ) : ℤ :=
  (2 * (P.t : ℤ) * (p₁ * p₂) + P.q) / (2 * (P.q : ℤ))

/-- Homomorphic multiplication of model ciphertexts. -/
def Ct.mul (c₁ c₂ : Ct P) : Ct P := ⟨mulPhase P c₁.phase c₂.phase⟩

/-- Relinearization, modeled AT ITS NOISE INTERFACE: key-switching the 3-element tensor back to
2 elements perturbs the phase by an additive key-switch noise `e_ks`. The bound `|e_ks| ≤ B_ks`
is a hypothesis of every theorem that touches this — an INPUT, not a derived fact (deriving it
needs the RNS gadget decomposition: named Phase-2 work, see the module doc). -/
def Ct.relin (c : Ct P) (eks : ℤ) : Ct P := ⟨c.phase + eks⟩

/-- The exact sub-`q` remainder of the multiplicative phase decomposition (everything the
`t/q`-rescale shrinks by a factor of `q`): `t·e₁e₂ − r·Δ·m₁m₂ − r·(m₁e₂ + m₂e₁)`. -/
def mulRemainder (P : Params) (m₁ m₂ : ℕ) (e₁ e₂ : ℤ) : ℤ :=
  (P.t : ℤ) * (e₁ * e₂) - (P.r : ℤ) * (P.Δ : ℤ) * ((m₁ : ℤ) * m₂)
    - (P.r : ℤ) * ((m₁ : ℤ) * e₂ + (m₂ : ℤ) * e₁)

/-! ## 2. The exact decomposition (the multiplicative analogue of `foldEnc_phase`). -/

/-- **The multiplicative phase decomposition, EXACT:** multiplying honest encryptions of `m₁`
(noise `e₁`) and `m₂` (noise `e₂`) yields phase

  `Δ·(m₁m₂)  +  (m₁e₂ + m₂e₁)  +  ⌊(2·mulRemainder + q)/(2q)⌋`.

Read it: the product message lands at scale `Δ` (a valid encryption of `m₁·m₂`); the operand
noises come back AMPLIFIED BY THE MESSAGES (`m₁e₂ + m₂e₁` — the term that makes multiplication
expensive); and the entire quadratic-in-noise + `r`-cross structure survives only after division
by `q` (the rounding term, bounded by `abs_mulRound_le`). No inequality here — this is an
equation, the spine the sound bound hangs on. -/
theorem mulPhase_encrypt_eq (P : Params) (m₁ m₂ : ℕ) (e₁ e₂ : ℤ) :
    mulPhase P ((P.Δ : ℤ) * m₁ + e₁) ((P.Δ : ℤ) * m₂ + e₂)
      = (P.Δ : ℤ) * ((m₁ : ℤ) * m₂) + ((m₁ : ℤ) * e₂ + (m₂ : ℤ) * e₁)
        + (2 * mulRemainder P m₁ m₂ e₁ e₂ + P.q) / (2 * (P.q : ℤ)) := by
  have hq : (0 : ℤ) < (P.q : ℤ) := by exact_mod_cast P.q_pos
  have hq0 : (2 * (P.q : ℤ)) ≠ 0 := by linarith
  have hQeq : (P.q : ℤ) = (P.Δ : ℤ) * (P.t : ℤ) + (P.r : ℤ) := by exact_mod_cast P.q_eq
  unfold mulPhase mulRemainder
  have hnum : 2 * (P.t : ℤ) * (((P.Δ : ℤ) * m₁ + e₁) * ((P.Δ : ℤ) * m₂ + e₂)) + (P.q : ℤ)
      = (2 * ((P.t : ℤ) * (e₁ * e₂) - (P.r : ℤ) * (P.Δ : ℤ) * ((m₁ : ℤ) * m₂)
            - (P.r : ℤ) * ((m₁ : ℤ) * e₂ + (m₂ : ℤ) * e₁)) + (P.q : ℤ))
        + ((P.Δ : ℤ) * ((m₁ : ℤ) * m₂) + ((m₁ : ℤ) * e₂ + (m₂ : ℤ) * e₁)) * (2 * (P.q : ℤ)) := by
    rw [hQeq]; ring
  rw [hnum, Int.add_mul_ediv_right _ _ hq0]
  ring

/-- **The rounding term is small:** for any `E` and `q > 0`,
`|⌊(2E + q)/(2q)⌋| ≤ |E|/q + 1`. (The `+1` is the honest slack of round-half-up — deleting it
breaks `mul_relin_noise_le`, which is exactly the mutation discipline wants.) -/
theorem abs_mulRound_le (q E : ℤ) (hq : 0 < q) :
    |(2 * E + q) / (2 * q)| ≤ |E| / q + 1 := by
  have h2q : (0 : ℤ) < 2 * q := by linarith
  have hqk : q * (|E| / q) + |E| % q = |E| := Int.mul_ediv_add_emod _ _
  have hs0 : 0 ≤ |E| % q := Int.emod_nonneg _ (by linarith)
  have hsq : |E| % q < q := Int.emod_lt_of_pos _ hq
  have hk0 : 0 ≤ |E| / q := Int.ediv_nonneg (abs_nonneg E) hq.le
  have hEle : E ≤ |E| := le_abs_self E
  have hEge : -|E| ≤ E := neg_abs_le E
  -- upper: F < k + 2, hence F ≤ k + 1
  have hup : (2 * E + q) / (2 * q) < (|E| / q + 1) + 1 := by
    rw [Int.ediv_lt_iff_lt_mul h2q]
    have hexp : (|E| / q + 1 + 1) * (2 * q) = 2 * (q * (|E| / q)) + 4 * q := by ring
    linarith
  have hup' : (2 * E + q) / (2 * q) ≤ |E| / q + 1 := Int.lt_add_one_iff.mp hup
  -- lower: −(k + 1) ≤ F
  have hlo : -(|E| / q + 1) ≤ (2 * E + q) / (2 * q) := by
    rw [Int.le_ediv_iff_mul_le h2q]
    have hexp : -(|E| / q + 1) * (2 * q) = -(2 * (q * (|E| / q))) - 2 * q := by ring
    linarith
  rw [abs_le]
  exact ⟨by linarith, hup'⟩

/-! ## 3. The SOUND noise bound for one multiply + relinearization. -/

/-- **The proven sound upper bound** on the noise of ONE relinearized model multiply, for
operand messages `≤ M₁, M₂`, operand noises `≤ B₁, B₂`, key-switch noise `≤ B_ks`:

  `M₁B₂ + M₂B₁  +  (t·B₁B₂ + r·Δ·M₁M₂ + r·(M₁B₂ + M₂B₁))/q  +  1  +  B_ks`.

The first term is the DOMINANT message-scale amplification (`(t−1)(B₁+B₂)` at full plaintext
range — the `t·(e₁+e₂)` shape); the `/q` block is the rescaled quadratic + `r`-cross residue
(a few bits above zero on the deployed set); `+1` is the rounding unit; `B_ks` is relin. The
NAMED SLACK: this is a worst-case ℓ∞ triangle-inequality bound — sign cancellations and the
average-case (variance) story are not used and not claimed — and it carries NO ring-expansion
factor `n` (scalar model; see module doc gap 1 and the ×4096 survival pin). -/
def mulNoiseBound (P : Params) (M₁ M₂ B₁ B₂ Bks : ℤ) : ℤ :=
  M₁ * B₂ + M₂ * B₁
    + ((P.t : ℤ) * (B₁ * B₂) + (P.r : ℤ) * (P.Δ : ℤ) * (M₁ * M₂)
        + (P.r : ℤ) * (M₁ * B₂ + M₂ * B₁)) / (P.q : ℤ)
    + 1 + Bks

/-- **THE MULTIPLICATIVE NOISE KEYSTONE:** one ct×ct multiply + relinearization of honest
encryptions has noise (relative to the product message `m₁·m₂`) bounded by `mulNoiseBound`.
Compare `abs_noise_add_le`: addition ADDS noise bounds; multiplication multiplies them into the
message scale. This is the theorem that turns multiply's silent failure into a checkable margin
hypothesis. -/
theorem mul_relin_noise_le (P : Params) (m₁ m₂ : ℕ) (e₁ e₂ eks : ℤ)
    (M₁ M₂ B₁ B₂ Bks : ℤ)
    (hm₁ : (m₁ : ℤ) ≤ M₁) (hm₂ : (m₂ : ℤ) ≤ M₂)
    (he₁ : |e₁| ≤ B₁) (he₂ : |e₂| ≤ B₂) (hks : |eks| ≤ Bks) :
    |(((encrypt P m₁ e₁).mul (encrypt P m₂ e₂)).relin eks).noiseAt (m₁ * m₂)|
      ≤ mulNoiseBound P M₁ M₂ B₁ B₂ Bks := by
  have hq : (0 : ℤ) < (P.q : ℤ) := by exact_mod_cast P.q_pos
  have hm₁0 : (0 : ℤ) ≤ (m₁ : ℤ) := Int.natCast_nonneg _
  have hm₂0 : (0 : ℤ) ≤ (m₂ : ℤ) := Int.natCast_nonneg _
  have hM₁0 : 0 ≤ M₁ := le_trans hm₁0 hm₁
  have hM₂0 : 0 ≤ M₂ := le_trans hm₂0 hm₂
  have hB₁0 : 0 ≤ B₁ := le_trans (abs_nonneg _) he₁
  have ht0 : (0 : ℤ) ≤ (P.t : ℤ) := Int.natCast_nonneg _
  have hr0 : (0 : ℤ) ≤ (P.r : ℤ) := Int.natCast_nonneg _
  have hd0 : (0 : ℤ) ≤ (P.Δ : ℤ) := Int.natCast_nonneg _
  -- the noise, decomposed exactly
  have hnoise_eq :
      (((encrypt P m₁ e₁).mul (encrypt P m₂ e₂)).relin eks).noiseAt (m₁ * m₂)
        = ((m₁ : ℤ) * e₂ + (m₂ : ℤ) * e₁)
          + (2 * mulRemainder P m₁ m₂ e₁ e₂ + P.q) / (2 * (P.q : ℤ)) + eks := by
    simp only [encrypt, Ct.mul, Ct.relin, Ct.noiseAt]
    rw [Nat.cast_mul, mulPhase_encrypt_eq]
    ring
  -- the cross term
  have hcross : |(m₁ : ℤ) * e₂ + (m₂ : ℤ) * e₁| ≤ M₁ * B₂ + M₂ * B₁ := by
    have h1 : (m₁ : ℤ) * |e₂| ≤ M₁ * B₂ := mul_le_mul hm₁ he₂ (abs_nonneg _) hM₁0
    have h2 : (m₂ : ℤ) * |e₁| ≤ M₂ * B₁ := mul_le_mul hm₂ he₁ (abs_nonneg _) hM₂0
    calc |(m₁ : ℤ) * e₂ + (m₂ : ℤ) * e₁| ≤ |(m₁ : ℤ) * e₂| + |(m₂ : ℤ) * e₁| := abs_add_le _ _
      _ = (m₁ : ℤ) * |e₂| + (m₂ : ℤ) * |e₁| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hm₁0, abs_of_nonneg hm₂0]
      _ ≤ M₁ * B₂ + M₂ * B₁ := by linarith
  -- the remainder, bounded term by term
  have hE : |mulRemainder P m₁ m₂ e₁ e₂|
      ≤ (P.t : ℤ) * (B₁ * B₂) + (P.r : ℤ) * (P.Δ : ℤ) * (M₁ * M₂)
        + (P.r : ℤ) * (M₁ * B₂ + M₂ * B₁) := by
    have h1 : |(P.t : ℤ) * (e₁ * e₂)| ≤ (P.t : ℤ) * (B₁ * B₂) := by
      rw [abs_mul, abs_of_nonneg ht0, abs_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul he₁ he₂ (abs_nonneg _) hB₁0) ht0
    have h2 : |(P.r : ℤ) * (P.Δ : ℤ) * ((m₁ : ℤ) * m₂)|
        ≤ (P.r : ℤ) * (P.Δ : ℤ) * (M₁ * M₂) := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg hr0 hd0), abs_mul,
        abs_of_nonneg hm₁0, abs_of_nonneg hm₂0]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hm₁ hm₂ hm₂0 hM₁0) (mul_nonneg hr0 hd0)
    have h3 : |(P.r : ℤ) * ((m₁ : ℤ) * e₂ + (m₂ : ℤ) * e₁)|
        ≤ (P.r : ℤ) * (M₁ * B₂ + M₂ * B₁) := by
      rw [abs_mul, abs_of_nonneg hr0]
      exact mul_le_mul_of_nonneg_left hcross hr0
    have hsplit : mulRemainder P m₁ m₂ e₁ e₂
        = (P.t : ℤ) * (e₁ * e₂) + -((P.r : ℤ) * (P.Δ : ℤ) * ((m₁ : ℤ) * m₂))
          + -((P.r : ℤ) * ((m₁ : ℤ) * e₂ + (m₂ : ℤ) * e₁)) := by
      unfold mulRemainder; ring
    calc |mulRemainder P m₁ m₂ e₁ e₂|
        ≤ |(P.t : ℤ) * (e₁ * e₂) + -((P.r : ℤ) * (P.Δ : ℤ) * ((m₁ : ℤ) * m₂))|
          + |-((P.r : ℤ) * ((m₁ : ℤ) * e₂ + (m₂ : ℤ) * e₁))| := by
          rw [hsplit]; exact abs_add_le _ _
      _ ≤ |(P.t : ℤ) * (e₁ * e₂)| + |-((P.r : ℤ) * (P.Δ : ℤ) * ((m₁ : ℤ) * m₂))|
          + |-((P.r : ℤ) * ((m₁ : ℤ) * e₂ + (m₂ : ℤ) * e₁))| := by
          have := abs_add_le ((P.t : ℤ) * (e₁ * e₂))
            (-((P.r : ℤ) * (P.Δ : ℤ) * ((m₁ : ℤ) * m₂)))
          linarith
      _ ≤ (P.t : ℤ) * (B₁ * B₂) + (P.r : ℤ) * (P.Δ : ℤ) * (M₁ * M₂)
          + (P.r : ℤ) * (M₁ * B₂ + M₂ * B₁) := by
          rw [abs_neg, abs_neg]; linarith
  -- rounding term ≤ |E|/q + 1 ≤ Ebound/q + 1
  have hF := abs_mulRound_le (P.q : ℤ) (mulRemainder P m₁ m₂ e₁ e₂) hq
  have hdiv : |mulRemainder P m₁ m₂ e₁ e₂| / (P.q : ℤ)
      ≤ ((P.t : ℤ) * (B₁ * B₂) + (P.r : ℤ) * (P.Δ : ℤ) * (M₁ * M₂)
          + (P.r : ℤ) * (M₁ * B₂ + M₂ * B₁)) / (P.q : ℤ) :=
    Int.ediv_le_ediv hq hE
  -- assemble
  rw [hnoise_eq]
  unfold mulNoiseBound
  have htri : |((m₁ : ℤ) * e₂ + (m₂ : ℤ) * e₁)
      + (2 * mulRemainder P m₁ m₂ e₁ e₂ + P.q) / (2 * (P.q : ℤ)) + eks|
      ≤ |(m₁ : ℤ) * e₂ + (m₂ : ℤ) * e₁|
        + |(2 * mulRemainder P m₁ m₂ e₁ e₂ + P.q) / (2 * (P.q : ℤ))| + |eks| := by
    have h1 := abs_add_le (((m₁ : ℤ) * e₂ + (m₂ : ℤ) * e₁)
      + (2 * mulRemainder P m₁ m₂ e₁ e₂ + P.q) / (2 * (P.q : ℤ))) eks
    have h2 := abs_add_le ((m₁ : ℤ) * e₂ + (m₂ : ℤ) * e₁)
      ((2 * mulRemainder P m₁ m₂ e₁ e₂ + P.q) / (2 * (P.q : ℤ)))
    linarith
  linarith

/-! ## 4. Decrypt correctness: product no-wrap + margin ⇒ EXACT product out. -/

/-- **The PRODUCT no-wrap gate (class C, multiplicative):** operands under caps whose PRODUCT
stays under `t` cannot wrap. Distinct from the additive `fold_sum_no_wrap` (`N·qmax < t`): the
constraint is `qmax₁·qmax₂ < t` — per-OPERAND square-root-of-`t` scale, not per-COUNT. -/
theorem product_no_wrap (q₁ q₂ qmax₁ qmax₂ t : ℕ) (h₁ : q₁ ≤ qmax₁) (h₂ : q₂ ≤ qmax₂)
    (hcap : qmax₁ * qmax₂ < t) : q₁ * q₂ < t :=
  lt_of_le_of_lt (Nat.mul_le_mul h₁ h₂) hcap

/-- **The multiplicative keystone, end to end:** honest encryptions, product under `t`, noise
margin covering `mulNoiseBound` — then decrypting the relinearized product yields EXACTLY
`m₁·m₂`. Both multiplicative silent-failure classes closed in one statement (at scalar-model
scope; module-doc gaps 1–3 apply). -/
theorem mul_relin_decrypts_exact (P : Params) (m₁ m₂ : ℕ) (e₁ e₂ eks : ℤ)
    (M₁ M₂ B₁ B₂ Bks : ℤ)
    (hm₁ : (m₁ : ℤ) ≤ M₁) (hm₂ : (m₂ : ℤ) ≤ M₂)
    (he₁ : |e₁| ≤ B₁) (he₂ : |e₂| ≤ B₂) (hks : |eks| ≤ Bks)
    (hwrap : m₁ * m₂ < P.t)
    (hmargin : SafeNoise P (mulNoiseBound P M₁ M₂ B₁ B₂ Bks)) :
    (((encrypt P m₁ e₁).mul (encrypt P m₂ e₂)).relin eks).decrypt = ((m₁ * m₂ : ℕ) : ℤ) := by
  have hnoise := mul_relin_noise_le P m₁ m₂ e₁ e₂ eks M₁ M₂ B₁ B₂ Bks hm₁ hm₂ he₁ he₂ hks
  set c := ((encrypt P m₁ e₁).mul (encrypt P m₂ e₂)).relin eks with hc
  have hsafe : SafeNoise P |c.noiseAt (m₁ * m₂)| := SafeNoise.mono hnoise hmargin
  have hphase : c.phase = (P.Δ : ℤ) * ((m₁ * m₂ : ℕ) : ℤ) + c.noiseAt (m₁ * m₂) := by
    unfold Ct.noiseAt; ring
  show decryptPhase P c.phase = _
  rw [hphase]
  exact decrypt_exact P (m₁ * m₂) _ hwrap hsafe

/-! ## 5. The deployed numbers — caps, margins, and the FAILING sides, `decide`-pinned. -/

/-- **The deployed per-operand cap is 1015** (`1015² = 1030225 < t = 1032193`) — the Lean twin
of `bfv_mul.rs::square_safe_bound(1032193) = 1015`. Contrast the ADDITIVE world: there, 15
whole full-range u16 orders fit per bucket; here, one multiply already caps each OPERAND at
1015 — the product wraps ~65× sooner than u16 range. -/
theorem deployed_product_capacity (q₁ q₂ : ℕ) (h₁ : q₁ ≤ 1015) (h₂ : q₂ ≤ 1015) :
    q₁ * q₂ < fheRs4096.t :=
  product_no_wrap q₁ q₂ 1015 1015 _ h₁ h₂ (by decide)

/-- …and 1016 is too much: the cap is TIGHT (`1016² = 1032256 ≥ t`). -/
theorem product_capacity_tight : ¬ (1016 * 1016 < fheRs4096.t) := by decide

/-- **THE FAILING SIDE (class C, multiplicative):** the 1016² product truly holds `1,032,256`
and READS as **63** — a well-formed, error-free, catastrophically wrong number. This is the
guard's tooth: what it rejects really does mis-clear. -/
theorem product_wraps :
    1016 * 1016 = 1032256 ∧ 1032256 % fheRs4096.t = 63 ∧ (63 : ℕ) ≠ 1032256 := by decide

/-- **Why the additive intuition kills you here:** ADDING two full-range u16 values is nowhere
near wrap (`131,070 ≪ t`), but MULTIPLYING them wraps catastrophically — `65535² = 4,294,836,225`
reads as `913,345`. The product hazard is a different REGIME, not a bigger constant. -/
theorem u16_product_misclears :
    65535 + 65535 < fheRs4096.t ∧
    65535 * 65535 = 4294836225 ∧ 4294836225 % fheRs4096.t = 913345 := by decide

/-! ### The computable margin check (the thing to EMIT for the Rust gate). -/

/-- The ℕ-side computable multiplicative noise bound — term-for-term the cast of
`mulNoiseBound` (proved by `mulNoiseBoundN_cast`). This is the constant to EMIT for the
Rust-side multiply gate, exactly as `marginHolds` is for the fold. -/
def mulNoiseBoundN (P : Params) (M₁ M₂ B₁ B₂ Bks : ℕ) : ℕ :=
  M₁ * B₂ + M₂ * B₁
    + (P.t * (B₁ * B₂) + P.r * P.Δ * (M₁ * M₂) + P.r * (M₁ * B₂ + M₂ * B₁)) / P.q
    + 1 + Bks

/-- The ℕ bound casts to the ℤ bound on the nose (ℕ floor division IS ℤ euclidean division on
nonnegatives), so the computable check and the theorem hypothesis are the SAME number. -/
theorem mulNoiseBoundN_cast (P : Params) (M₁ M₂ B₁ B₂ Bks : ℕ) :
    ((mulNoiseBoundN P M₁ M₂ B₁ B₂ Bks : ℕ) : ℤ)
      = mulNoiseBound P (M₁ : ℤ) (M₂ : ℤ) (B₁ : ℤ) (B₂ : ℤ) (Bks : ℤ) := by
  unfold mulNoiseBoundN mulNoiseBound
  push_cast [Int.natCast_div]
  ring

/-- The computable multiplicative margin check: does the deployed parameter set absorb one
multiply's worth of noise? (`SafeNoise` at `mulNoiseBoundN`.) -/
def mulMarginHolds (P : Params) (M₁ M₂ B₁ B₂ Bks : ℕ) : Bool :=
  decide (2 * P.t * mulNoiseBoundN P M₁ M₂ B₁ B₂ Bks + 2 * (P.t - 1) * P.r < P.q)

/-- The check is SOUND: `mulMarginHolds = true` implies the keystone's `SafeNoise` hypothesis —
a Rust multiply gated on the emitted check enforces a theorem's hypothesis, not a vibe. -/
theorem mulMarginHolds_safe (P : Params) (M₁ M₂ B₁ B₂ Bks : ℕ)
    (h : mulMarginHolds P M₁ M₂ B₁ B₂ Bks = true) :
    SafeNoise P ((mulNoiseBoundN P M₁ M₂ B₁ B₂ Bks : ℕ) : ℤ) := by
  unfold mulMarginHolds at h
  have hnat := of_decide_eq_true h
  have h1 : (1 : ℕ) ≤ P.t := P.t_pos
  unfold SafeNoise
  zify [h1] at hnat
  linarith

/-! ### Deployed margin pins — the meter reads full where it should, EMPTY where it must. -/

/-- **The deployed one-multiply margin HOLDS:** operands capped at 1015 (the product no-wrap
cap), fresh noise `≤ 2^20`, relin allowance `B_ks ≤ 2^40` — the whole proven scalar bound
(~2^41) sits ~2^47 under the ~2^89 budget. Kernel-evaluated on the real 109-bit `q`. -/
theorem deployed_mul_margin_holds :
    mulMarginHolds fheRs4096 1015 1015 (2 ^ 20) (2 ^ 20) (2 ^ 40) = true := by decide

/-- **The meter reads EMPTY (class A, multiplicative):** operands carrying noise `2^80` — which
the ADDITIVE margin would happily accept for a single ciphertext — are REFUSED by the multiply
check: the message-scale amplification `M·B ≈ 2^90` crosses the ~2^89 budget. -/
theorem mul_margin_fails_big_noise :
    mulMarginHolds fheRs4096 1015 1015 (2 ^ 80) (2 ^ 80) 0 = false := by decide

/-- **The amplification is REAL, pinned as a contrast:** the SAME `2^80` noise — additive
margin ACCEPTS (one ciphertext, no amplification), multiplicative margin REFUSES (amplified by
the message scale past the budget). This is the theorem-shaped statement of "multiplication
grows noise multiplicatively"; a guard that treated multiply like add would silently
mis-decrypt here. -/
theorem mul_amplifies_where_add_accepts :
    marginHolds fheRs4096 1 (2 ^ 80) = true ∧
    mulMarginHolds fheRs4096 1015 1015 (2 ^ 80) (2 ^ 80) 0 = false := by decide

/-- **The scalar bound survives the FULL ring-expansion inflation:** even multiplying the
entire proven scalar-model bound by `n = 4096` (the worst-case ring expansion factor the
unformalized polynomial lift could contribute — module-doc gap 1), the deployed margin still
holds. Reuses `marginHolds` with `K = 4096` as the inflation. This pin is what makes the
scalar-scope theorem OPERATIONALLY honest for the deployed parameters while the lift is
Phase-2. -/
theorem deployed_mul_margin_survives_ring_expansion :
    marginHolds fheRs4096 4096 (mulNoiseBoundN fheRs4096 1015 1015 (2 ^ 20) (2 ^ 20) (2 ^ 40))
      = true := by decide

/-! ## 6. THE DEPLOYED MULTIPLICATIVE KEYSTONE. -/

/-- **One multiply + relin on the deployed fhe.rs degree-4096 parameters, both gates at their
honest tight values:** operands `≤ 1015` (the TIGHT product cap — not u16!), fresh noise
`≤ 2^20`, relin noise `≤ 2^40` (the named allowance) — the relinearized product decrypts to
EXACTLY `m₁·m₂`. The multiplicative twin of `deployed_fold_decrypts_exact`. -/
theorem deployed_mul_relin_decrypts_exact (m₁ m₂ : ℕ) (e₁ e₂ eks : ℤ)
    (hm₁ : m₁ ≤ 1015) (hm₂ : m₂ ≤ 1015)
    (he₁ : |e₁| ≤ 2 ^ 20) (he₂ : |e₂| ≤ 2 ^ 20) (hks : |eks| ≤ 2 ^ 40) :
    (((encrypt fheRs4096 m₁ e₁).mul (encrypt fheRs4096 m₂ e₂)).relin eks).decrypt
      = ((m₁ * m₂ : ℕ) : ℤ) := by
  apply mul_relin_decrypts_exact fheRs4096 m₁ m₂ e₁ e₂ eks
      ((1015 : ℕ) : ℤ) ((1015 : ℕ) : ℤ) ((2 ^ 20 : ℕ) : ℤ) ((2 ^ 20 : ℕ) : ℤ) ((2 ^ 40 : ℕ) : ℤ)
      (by exact_mod_cast hm₁) (by exact_mod_cast hm₂)
      (by exact_mod_cast he₁) (by exact_mod_cast he₂) (by exact_mod_cast hks)
      (deployed_product_capacity m₁ m₂ hm₁ hm₂)
  rw [← mulNoiseBoundN_cast]
  exact mulMarginHolds_safe _ _ _ _ _ _ deployed_mul_margin_holds

#print axioms mulPhase_encrypt_eq
#print axioms abs_mulRound_le
#print axioms mul_relin_noise_le
#print axioms product_no_wrap
#print axioms mul_relin_decrypts_exact
#print axioms deployed_product_capacity
#print axioms product_capacity_tight
#print axioms product_wraps
#print axioms u16_product_misclears
#print axioms mulNoiseBoundN_cast
#print axioms mulMarginHolds_safe
#print axioms deployed_mul_margin_holds
#print axioms mul_margin_fails_big_noise
#print axioms mul_amplifies_where_add_accepts
#print axioms deployed_mul_margin_survives_ring_expansion
#print axioms deployed_mul_relin_decrypts_exact

end Minidregg.Theory.Bfv
