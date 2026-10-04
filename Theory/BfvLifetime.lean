/-
# `Theory.BfvLifetime` — Mini's BFV noise margin, over Mini's actual modulus chain

The ported `Theory.Bfv*` modules (breadstuffs `metatheory/Bfv/`) prove the noise algebra for
BFV over the fhe.rs degree-4096 parameter set. Mini runs that same set: degree 4096,
`t = 1,032,193`, and the three RNS moduli `68719403009 · 68719230977 · 137438822401`
(`Compiler/BfvCompressedEquation.lean` `RnsModulus.value`).
This module joins the ported algebra to the native FHE profile Mini last ran. That profile
(`native/fhe-bend`) consumed only artifacts of the upstream-Bend path and was deleted with it on
2026-10-04 (Git history keeps it); the next native FHE consumer must re-bind these constants.

## What Mini's native code decided (read from the deleted `native/fhe-bend/src/{lib,natural}.rs`)

* Plaintexts are lifted as `⌊q·m/t⌋`, not as `Δ·m` (README: "actual floor(q*m/t) lifting adds
  at most one defect per … addition"). Bread's keystone `decrypt_exact` is for the `Δ·m` lift and
  needs the `2(t−1)·r` cross term; Mini's margin is `2t(B+1) < q` (`natural.rs`, "conditional
  linear noise exhausts strict rounding margin"). `decrypt_exact_lift` proves that margin is the
  exact sufficient condition for Mini's lift.
* The fresh coefficient-noise constant is `FRESH_NOISE = 3,276,820 = 2·4096·20·20 + 20`.
  `fresh_noise_from_ring` derives it from the proven ring expansion `‖a·b‖∞ ≤ N‖a‖∞‖b‖∞`
  for the public-key encryption noise `−e·u + e₁ + e₂·s` with every factor in `[-20, 20]`.
* The add recurrence `B = Bl + Br + 1` (`add_bound`) is `liftNoise_add_le`.
* The natural add-only profile admits at most 64 addition gates. `natural_profile_margin` proves the
  worst case (a 64-deep doubling chain) still clears the margin, so within that profile the margin
  refusal can never fire; the worst-case doubling chain first exhausts the margin at gate 67
  (`natural_doubling_exhausts_at_67`).
* The mux profiles count ciphertext×ciphertext depth and refuse depth 3 ("ciphertext lifetime depth
  exceeded", `max_depth`), i.e. a third unrefreshed use. In Rust that is a counter, not a noise
  computation. Section 5 makes it a theorem about a noise budget: with the worst-case per-level
  bound `muxLevelBound` (Bread's proven scalar multiply bound, inflated by the attained ring
  expansion factor `N = 4096`, plus one same-depth addition), Mini's margin check
  admits exactly the depths `d ≤ 2` and refuses depth 3 — for every relinearization-noise allowance
  up to `relinAllowance ≈ 2^52.39` (`mini_lifetime_iff`). Past that allowance depth 2 is refused too
  (`lifetime_two_refused_past_allowance`), and depth 3 is refused at every allowance
  (`lifetime_three_refused`).

## What is and is not claimed

* `muxLevel_sound` proves the per-level bound sound in the ported SCALAR ciphertext model (one
  coefficient, `Δ·m` lift, relinearization modeled at its additive noise interface). The factor
  `N` is the ring budget: `scalar_budget_admits_three` shows that without it the same check admits
  depth 3, so the depth-3 refusal is carried entirely by the ring expansion factor. The ring lift of
  the multiplication decomposition itself (including the mod-`q` wrap polynomial of a product) is
  NOT formalized; it is Bread's named gap 1–2 of `Theory.BfvMul`, unchanged.
* The relinearization noise bound `Bks` is a premise. `relinAllowance` is the exact largest value at
  which depth 2 still clears the margin; it is not a measurement of fhe.rs's key-switch noise.
* Section 6 states the threshold-decrypt release precondition (smudging window). Its refusal side
  shows that no smudge radius both hides a depth-1 mux output at 48 bits and keeps the margin:
  under this worst-case envelope, threshold release is only available for low-noise ciphertexts.
* Lattice security of the parameter set is not a Lean statement here or anywhere in `Theory.Bfv*`.
-/
import Theory.BfvMul
import Theory.BfvRing
import Theory.BfvSmudging

namespace Minidregg.Theory.Bfv

/-! ## 1. Mini's parameter identity -/

/-- Mini's first RNS modulus (`RnsModulus.q0`). -/
def miniQ0 : ℕ := 68719403009
/-- Mini's second RNS modulus (`RnsModulus.q1`). -/
def miniQ1 : ℕ := 68719230977
/-- Mini's third RNS modulus (`RnsModulus.q2`). -/
def miniQ2 : ℕ := 137438822401
/-- Mini's plaintext modulus (`T` of the deleted native profile). -/
def miniT : ℕ := 1032193

/-- Mini's modulus chain IS the ported parameter set: the product of Mini's three pinned RNS
moduli is `fheRs4096.q`, Mini's `t` is `fheRs4096.t`, and each modulus is the hex literal of
`Q` in the deleted native profile. -/
theorem mini_modulus_chain :
    miniQ0 * miniQ1 * miniQ2 = fheRs4096.q ∧ miniT = fheRs4096.t ∧
      miniQ0 = 0xffffee001 ∧ miniQ1 = 0xffffc4001 ∧ miniQ2 = 0x1ffffe0001 := by
  decide

/-! ## 2. Mini's lift `⌊q·m/t⌋` and its strict margin `2t(B+1) < q` -/

/-- The plaintext lift Mini's native profiles use: `⌊q·m/t⌋`. -/
def liftEncode (P : Params) (m : ℕ) : ℤ := ((P.q * m / P.t : ℕ) : ℤ)

/-- Noise of a phase relative to an intended message under Mini's lift. -/
def liftNoise (P : Params) (p : ℤ) (m : ℕ) : ℤ := p - liftEncode P m

/-- Mini's strict rounding margin for a coefficient-noise bound `B`. -/
def MiniMargin (P : Params) (B : ℕ) : Prop := 2 * P.t * (B + 1) < P.q

/-- The computable check (the `ensure(lhs < q)` of `natural.rs`). -/
def miniMarginHolds (P : Params) (B : ℕ) : Bool := decide (2 * P.t * (B + 1) < P.q)

theorem miniMarginHolds_iff (P : Params) (B : ℕ) :
    miniMarginHolds P B = true ↔ MiniMargin P B := by
  simp [miniMarginHolds, MiniMargin]

/-- The margin is antitone: a smaller bound passes whenever a larger one does. -/
theorem miniMargin_anti {P : Params} {B B' : ℕ} (h : B ≤ B') (h' : MiniMargin P B') :
    MiniMargin P B := by
  unfold MiniMargin at *
  have : 2 * P.t * (B + 1) ≤ 2 * P.t * (B' + 1) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- **Decryption is exact under Mini's lift inside Mini's margin.** A phase `⌊q·m/t⌋ + e` with
`|e| ≤ B` and `2t(B+1) < q` decrypts to exactly `m`. The `+1` absorbs the lift's fractional
defect `(q·m mod t)/t < 1`; no `r` cross term appears, unlike the `Δ·m` lift of
`decrypt_exact`. -/
theorem decrypt_exact_lift (P : Params) (m : ℕ) (e : ℤ) (B : ℕ)
    (he : |e| ≤ B) (hmargin : MiniMargin P B) :
    decryptPhase P (liftEncode P m + e) = m := by
  unfold decryptPhase liftEncode
  unfold MiniMargin at hmargin
  have hdiv := Nat.div_add_mod (P.q * m) P.t
  have hmod := Nat.mod_lt (P.q * m) P.t_pos
  set L : ℕ := P.q * m / P.t with hL
  set ρ : ℕ := P.q * m % P.t with hρ
  set T : ℤ := (P.t : ℤ) with hT
  set Q : ℤ := (P.q : ℤ) with hQ
  have hdivZ : T * (L : ℤ) + (ρ : ℤ) = Q * (m : ℤ) := by
    rw [hT, hQ]; exact_mod_cast hdiv
  have hρT : (ρ : ℤ) + 1 ≤ T := by rw [hT]; exact_mod_cast hmod
  have hρ0 : (0 : ℤ) ≤ (ρ : ℤ) := by positivity
  have hT0 : (0 : ℤ) < T := by rw [hT]; exact_mod_cast P.t_pos
  have hmZ : 2 * T * ((B : ℤ) + 1) < Q := by rw [hT, hQ]; exact_mod_cast hmargin
  have hle : T * e ≤ T * (B : ℤ) :=
    mul_le_mul_of_nonneg_left (le_trans (le_abs_self e) he) hT0.le
  have hge : -(T * (B : ℤ)) ≤ T * e := by
    have := mul_le_mul_of_nonneg_left (neg_le_of_abs_le he) hT0.le
    linarith
  have h2Q : (0 : ℤ) < 2 * Q := by nlinarith
  have hlow : (m : ℤ) * (2 * Q) ≤ 2 * T * ((L : ℤ) + e) + Q := by nlinarith
  have hup : 2 * T * ((L : ℤ) + e) + Q < ((m : ℤ) + 1) * (2 * Q) := by nlinarith
  have h1 : (m : ℤ) ≤ (2 * T * ((L : ℤ) + e) + Q) / (2 * Q) :=
    (Int.le_ediv_iff_mul_le h2Q).mpr hlow
  have h2 : (2 * T * ((L : ℤ) + e) + Q) / (2 * Q) < (m : ℤ) + 1 :=
    (Int.ediv_lt_iff_lt_mul h2Q).mpr hup
  exact le_antisymm (Int.lt_add_one_iff.mp h2) h1

/-- The margin is load-bearing on the deployed numbers: one unit of noise past the rounding radius
(`e = ⌈q/(2t)⌉` on `m = 0`) decrypts cleanly to `1`. -/
theorem lift_cliff :
    decryptPhase fheRs4096 (liftEncode fheRs4096 0 + (q4096 / (2 * t4096) + 1 : ℕ)) = 1 := by
  decide

/-- **The lift's addition defect is 0 or 1** — the `+1` of Rust's `add_bound`. -/
theorem liftEncode_add_defect (P : Params) (m₁ m₂ : ℕ) :
    ∃ δ : ℤ, (δ = 0 ∨ δ = 1) ∧
      liftEncode P (m₁ + m₂) = liftEncode P m₁ + liftEncode P m₂ + δ := by
  unfold liftEncode
  have hsplit := Nat.add_div (a := P.q * m₁) (b := P.q * m₂) P.t_pos
  rw [Nat.mul_add, hsplit]
  by_cases h : P.t ≤ P.q * m₁ % P.t + P.q * m₂ % P.t
  · exact ⟨1, Or.inr rfl, by rw [if_pos h]; push_cast; ring⟩
  · exact ⟨0, Or.inl rfl, by rw [if_neg h]; push_cast; ring⟩

/-- **Rust's `add_bound` recurrence, proved:** adding two ciphertexts adds their lift-noises and at
most one unit of lift defect: `|noise(p₁+p₂ | m₁+m₂)| ≤ |noise₁| + |noise₂| + 1`. -/
theorem liftNoise_add_le (P : Params) (p₁ p₂ : ℤ) (m₁ m₂ : ℕ) :
    |liftNoise P (p₁ + p₂) (m₁ + m₂)| ≤ |liftNoise P p₁ m₁| + |liftNoise P p₂ m₂| + 1 := by
  obtain ⟨δ, hδ, heq⟩ := liftEncode_add_defect P m₁ m₂
  unfold liftNoise
  rw [heq]
  have hδabs : |δ| ≤ 1 := by rcases hδ with h | h <;> simp [h]
  have hsplit : p₁ + p₂ - (liftEncode P m₁ + liftEncode P m₂ + δ)
      = (p₁ - liftEncode P m₁) + (p₂ - liftEncode P m₂) + -δ := by ring
  rw [hsplit]
  calc |(p₁ - liftEncode P m₁) + (p₂ - liftEncode P m₂) + -δ|
      ≤ |(p₁ - liftEncode P m₁) + (p₂ - liftEncode P m₂)| + |-δ| := abs_add_le _ _
    _ ≤ |p₁ - liftEncode P m₁| + |p₂ - liftEncode P m₂| + |-δ| := by
        gcongr; exact abs_add_le _ _
    _ ≤ |p₁ - liftEncode P m₁| + |p₂ - liftEncode P m₂| + 1 := by rw [abs_neg]; linarith

/-! ## 3. The fresh-noise constant, derived from the proven ring expansion -/

/-- Mini's fresh public-key encryption coefficient-noise constant (`natural.rs` `FRESH_NOISE`). -/
def freshNoise : ℕ := 3276820

theorem freshNoise_formula : freshNoise = 2 * 4096 * 20 * 20 + 20 := rfl

/-- **`FRESH_NOISE` is a theorem about the ring, not a comment.** BFV public-key encryption leaves
the phase noise `−e·u + e₁ + e₂·s` (key error `e`, encryption randomness `u`, `e₁`, `e₂`, secret
`s`). With every coefficient of every factor in `[-20, 20]` (the CBD variance-10 support), each
ring product costs at most `4096·20·20` by `negaMul_normInf_le`, so the noise's ∞-norm is at most
`3,276,820`. The support bound `20` is the premise; that fhe.rs samples inside it is not proved
here. -/
theorem fresh_noise_from_ring {e u e₁ e₂ s : Rn 4096}
    (he : NormInfLE e 20) (hu : NormInfLE u 20) (he₁ : NormInfLE e₁ 20)
    (he₂ : NormInfLE e₂ 20) (hs : NormInfLE s 20) :
    NormInfLE (fun k => -negaMul e u k + e₁ k + negaMul e₂ s k) (freshNoise : ℤ) := by
  intro k
  have h1 := negaMul_normInf_le he hu (by norm_num) k
  have h2 := negaMul_normInf_le he₂ hs (by norm_num) k
  have h3 := he₁ k
  calc |-negaMul e u k + e₁ k + negaMul e₂ s k|
      ≤ |-negaMul e u k + e₁ k| + |negaMul e₂ s k| := abs_add_le _ _
    _ ≤ |-negaMul e u k| + |e₁ k| + |negaMul e₂ s k| := by gcongr; exact abs_add_le _ _
    _ ≤ (4096 : ℕ) * 20 * 20 + 20 + (4096 : ℕ) * 20 * 20 := by
        rw [abs_neg]; push_cast at h1 h2 ⊢; linarith
    _ = (freshNoise : ℤ) := by norm_num [freshNoise]

/-- The premise is satisfiable and the bound is not vacuous: all-`20` factors meet it. -/
theorem fresh_noise_premise_inhabited :
    NormInfLE (fun _ : Fin 4096 => (20 : ℤ)) 20 := fun _ => by norm_num

/-! ## 4. The natural add-only profile: the margin cannot fire within 64 gates -/

/-- **Worst-case doubling.** Wire bounds `b` with the first `n₀` (inputs) at most `B`, and every
later wire `n₀ + k` bounded by Rust's `add_bound` of two operands, each an earlier wire or a
noiseless constant, satisfy `b i + 1 ≤ 2^k·(B+1)` for every wire `i < n₀ + k`. -/
theorem add_chain_bound (b : ℕ → ℕ) (n₀ B : ℕ) (hin : ∀ i < n₀, b i ≤ B)
    (hgate : ∀ k, ∃ x y : ℕ, (x = 0 ∨ ∃ i < n₀ + k, x = b i) ∧
      (y = 0 ∨ ∃ j < n₀ + k, y = b j) ∧ b (n₀ + k) ≤ x + y + 1) :
    ∀ k, ∀ i < n₀ + k, b i + 1 ≤ 2 ^ k * (B + 1) := by
  intro k
  induction k with
  | zero => intro i hi; simpa using Nat.succ_le_succ (hin i (by simpa using hi))
  | succ k ih =>
    intro i hi
    have hp : 2 ^ (k + 1) * (B + 1) = 2 ^ k * (B + 1) + 2 ^ k * (B + 1) := by ring
    have hpos : 1 ≤ 2 ^ k * (B + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rcases Nat.lt_succ_iff_lt_or_eq.mp (by omega : i < n₀ + k + 1) with hlt | heq
    · have := ih i hlt; rw [hp]; omega
    · obtain ⟨x, y, hx, hy, hb⟩ := hgate k
      have hx' : x + 1 ≤ 2 ^ k * (B + 1) := by
        rcases hx with h | ⟨j, hj, h⟩
        · omega
        · rw [h]; exact ih j hj
      have hy' : y + 1 ≤ 2 ^ k * (B + 1) := by
        rcases hy with h | ⟨j, hj, h⟩
        · omega
        · rw [h]; exact ih j hj
      rw [heq, hp]; omega

/-- The doubling chain `b ↦ 2b + 1` from `freshNoise` reaches exactly `2^k·(B+1) − 1`: the
`add_chain_bound` envelope is attained, not slack. -/
theorem doubling_chain_exact (B k : ℕ) :
    (fun b => b + b + 1)^[k] B + 1 = 2 ^ k * (B + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    have := ih
    linarith

/-- **The natural profile's margin never refuses within its 64-gate cap.** Any add-only plan of at
most 64 gates over fresh inputs (`≤ freshNoise`) keeps every wire inside Mini's margin. -/
theorem natural_profile_margin (b : ℕ → ℕ) (n₀ k : ℕ) (hk : k ≤ 64)
    (hin : ∀ i < n₀, b i ≤ freshNoise)
    (hgate : ∀ k, ∃ x y : ℕ, (x = 0 ∨ ∃ i < n₀ + k, x = b i) ∧
      (y = 0 ∨ ∃ j < n₀ + k, y = b j) ∧ b (n₀ + k) ≤ x + y + 1)
    (i : ℕ) (hi : i < n₀ + k) : MiniMargin fheRs4096 (b i) := by
  have hb := add_chain_bound b n₀ freshNoise hin hgate k i hi
  have hpow : 2 ^ k * (freshNoise + 1) ≤ 2 ^ 64 * (freshNoise + 1) :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hk)
  have hcap : 2 * fheRs4096.t * (2 ^ 64 * (freshNoise + 1)) < fheRs4096.q := by decide
  unfold MiniMargin
  have : 2 * fheRs4096.t * (b i + 1) ≤ 2 * fheRs4096.t * (2 ^ 64 * (freshNoise + 1)) :=
    Nat.mul_le_mul_left _ (le_trans hb hpow)
  exact lt_of_le_of_lt this hcap

/-- The true ceiling of the worst case: the doubling chain clears the margin through gate 66
and exhausts it at gate 67. The 64-gate cap, not the noise margin, is the binding refusal. -/
theorem natural_doubling_exhausts_at_67 :
    MiniMargin fheRs4096 ((fun b => b + b + 1)^[66] freshNoise) ∧
      ¬ MiniMargin fheRs4096 ((fun b => b + b + 1)^[67] freshNoise) := by
  unfold MiniMargin
  rw [doubling_chain_exact, doubling_chain_exact]
  decide

/-! ## 5. The mux lifetime: depth 2 admitted, depth 3 refused -/

/-- **One mux level, worst case:** one relinearized ciphertext×ciphertext product of operands with
messages `≤ t−1` and noise `≤ B` (Bread's proven scalar bound `mulNoiseBoundN`, inflated by the ring
expansion budget `N`), plus the relinearization allowance `Bks`, plus one same-depth addition
(`B + 1`). -/
def muxLevelBound (P : Params) (N Bks B : ℕ) : ℕ :=
  N * mulNoiseBoundN P (P.t - 1) (P.t - 1) B B 0 + Bks + B + 1

/-- The worst-case noise after `d` unrefreshed mux levels from fresh noise `B₀`. -/
def lifetimeNoise (P : Params) (N Bks B₀ : ℕ) : ℕ → ℕ
  | 0 => B₀
  | d + 1 => muxLevelBound P N Bks (lifetimeNoise P N Bks B₀ d)

/-- Mini's margin check at lifetime depth `d`. -/
def lifetimeMarginHolds (P : Params) (N Bks B₀ d : ℕ) : Bool :=
  miniMarginHolds P (lifetimeNoise P N Bks B₀ d)

theorem mulNoiseBoundN_mono (P : Params) (M : ℕ) {B B' : ℕ} (h : B ≤ B') :
    mulNoiseBoundN P M M B B 0 ≤ mulNoiseBoundN P M M B' B' 0 := by
  unfold mulNoiseBoundN
  have h1 : M * B ≤ M * B' := Nat.mul_le_mul_left _ h
  have h2 : P.t * (B * B) + P.r * P.Δ * (M * M) + P.r * (M * B + M * B)
      ≤ P.t * (B' * B') + P.r * P.Δ * (M * M) + P.r * (M * B' + M * B') := by
    have := Nat.mul_le_mul h h
    have h3 : P.t * (B * B) ≤ P.t * (B' * B') := Nat.mul_le_mul_left _ this
    have h4 : P.r * (M * B + M * B) ≤ P.r * (M * B' + M * B') :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have h5 := Nat.div_le_div_right (c := P.q) h2
  omega

theorem muxLevelBound_mono {P : Params} {N Bks Bks' B B' : ℕ} (hk : Bks ≤ Bks') (h : B ≤ B') :
    muxLevelBound P N Bks B ≤ muxLevelBound P N Bks' B' := by
  unfold muxLevelBound
  have := Nat.mul_le_mul_left N (mulNoiseBoundN_mono P (P.t - 1) h)
  omega

theorem lt_muxLevelBound (P : Params) (N Bks B : ℕ) : B < muxLevelBound P N Bks B := by
  unfold muxLevelBound; omega

theorem lifetimeNoise_mono_Bks (P : Params) (N B₀ : ℕ) {Bks Bks' : ℕ} (hk : Bks ≤ Bks') :
    ∀ d, lifetimeNoise P N Bks B₀ d ≤ lifetimeNoise P N Bks' B₀ d
  | 0 => le_rfl
  | d + 1 => muxLevelBound_mono hk (lifetimeNoise_mono_Bks P N B₀ hk d)

theorem lifetimeNoise_mono_depth (P : Params) (N Bks B₀ : ℕ) {d d' : ℕ} (h : d ≤ d') :
    lifetimeNoise P N Bks B₀ d ≤ lifetimeNoise P N Bks B₀ d' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (lt_muxLevelBound P N Bks _).le

/-- The largest relinearization-noise allowance at which two unrefreshed levels still clear Mini's
margin (`≈ 2^52.39`), exact: one more and depth 2 is refused. -/
def relinAllowance : ℕ := 5906122434943769

/-- **Depth 2 is admitted** on Mini's parameters, at the full relinearization allowance. -/
theorem lifetime_two_admitted :
    lifetimeMarginHolds fheRs4096 4096 relinAllowance freshNoise 2 = true := by decide

/-- The allowance is exact: one unit more relinearization noise and depth 2 is refused. -/
theorem lifetime_two_refused_past_allowance :
    lifetimeMarginHolds fheRs4096 4096 (relinAllowance + 1) freshNoise 2 = false := by decide

/-- Depth 3 is refused even with zero relinearization noise. -/
theorem lifetime_three_refused_at_zero :
    lifetimeMarginHolds fheRs4096 4096 0 freshNoise 3 = false := by decide

theorem lifetimeMarginHolds_anti {P : Params} {N B₀ : ℕ} {Bks Bks' d d' : ℕ}
    (hk : Bks ≤ Bks') (hd : d ≤ d') (h : lifetimeMarginHolds P N Bks' B₀ d' = true) :
    lifetimeMarginHolds P N Bks B₀ d = true := by
  unfold lifetimeMarginHolds at *
  rw [miniMarginHolds_iff] at *
  exact miniMargin_anti
    (le_trans (lifetimeNoise_mono_Bks P N B₀ hk d) (lifetimeNoise_mono_depth P N Bks' B₀ hd)) h

/-- **The third unrefreshed use is refused, at every relinearization allowance and every depth
`≥ 3`** — the deleted native profile's "third unrefreshed invocation refuses", as a theorem about the
noise budget rather than a test of a counter. -/
theorem lifetime_three_refused (Bks d : ℕ) (hd : 3 ≤ d) :
    lifetimeMarginHolds fheRs4096 4096 Bks freshNoise d = false := by
  cases h : lifetimeMarginHolds fheRs4096 4096 Bks freshNoise d
  · rfl
  · have := lifetimeMarginHolds_anti (Nat.zero_le Bks) hd h
    rw [lifetime_three_refused_at_zero] at this
    exact absurd this (by decide)

/-- **The exact lifetime characterization:** for every relinearization allowance up to
`relinAllowance`, Mini's margin check admits lifetime depth `d` iff `d ≤ 2`. -/
theorem mini_lifetime_iff (Bks : ℕ) (hk : Bks ≤ relinAllowance) (d : ℕ) :
    lifetimeMarginHolds fheRs4096 4096 Bks freshNoise d = true ↔ d ≤ 2 := by
  constructor
  · intro h
    by_contra hd
    rw [lifetime_three_refused Bks d (by omega)] at h
    exact absurd h (by decide)
  · intro hd
    exact lifetimeMarginHolds_anti hk hd lifetime_two_admitted

/-- **The refusal is carried by the ring budget.** Without the expansion factor (`N = 1`, the
scalar model alone) the same check admits depth 3: the scalar model cannot see why a third
unrefreshed use is unsafe. -/
theorem scalar_budget_admits_three :
    lifetimeMarginHolds fheRs4096 1 0 freshNoise 3 = true := by decide

/-! ### Soundness of the per-level bound in the ported scalar model -/

theorem Ct.eq_encrypt_noiseAt {P : Params} (c : Ct P) (m : ℕ) :
    c = encrypt P m (c.noiseAt m) := by
  cases c; simp [encrypt, Ct.noiseAt]

/-- **`muxLevelBound` bounds a real (scalar-model) mux level.** For any ciphertexts `c`, `a` with
messages `≤ t−1` and noise `≤ B`, and relinearization noise `≤ Bks`, the level
`relin(c·a) + a` carries noise (relative to `m_c·m_a + m_a`) at most `muxLevelBound P N Bks B`, for
every ring budget `N ≥ 1`. Proved from Bread's `mul_relin_noise_le` and `noiseAt_add`. -/
theorem muxLevel_sound (P : Params) (N : ℕ) (hN : 1 ≤ N) (c a : Ct P) (mc ma : ℕ) (eks : ℤ)
    (B Bks : ℕ) (hmc : mc ≤ P.t - 1) (hma : ma ≤ P.t - 1)
    (hc : |c.noiseAt mc| ≤ B) (ha : |a.noiseAt ma| ≤ B) (hks : |eks| ≤ Bks) :
    |(((c.mul a).relin eks).add a).noiseAt (mc * ma + ma)| ≤ (muxLevelBound P N Bks B : ℤ) := by
  rw [noiseAt_add]
  have hmul := mul_relin_noise_le P mc ma (c.noiseAt mc) (a.noiseAt ma) eks
    ((P.t - 1 : ℕ) : ℤ) ((P.t - 1 : ℕ) : ℤ) (B : ℤ) (B : ℤ) (Bks : ℤ)
    (by exact_mod_cast hmc) (by exact_mod_cast hma) hc ha hks
  rw [← Ct.eq_encrypt_noiseAt c mc, ← Ct.eq_encrypt_noiseAt a ma] at hmul
  have hsplit : mulNoiseBound P ((P.t - 1 : ℕ) : ℤ) ((P.t - 1 : ℕ) : ℤ) (B : ℤ) (B : ℤ) (Bks : ℤ)
      = ((mulNoiseBoundN P (P.t - 1) (P.t - 1) B B 0 : ℕ) : ℤ) + (Bks : ℤ) := by
    rw [mulNoiseBoundN_cast]; unfold mulNoiseBound; push_cast; ring
  rw [hsplit] at hmul
  set X : ℕ := mulNoiseBoundN P (P.t - 1) (P.t - 1) B B 0
  have hNX : (X : ℤ) ≤ (N : ℤ) * (X : ℤ) := by
    have : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    nlinarith [(Nat.cast_nonneg X : (0 : ℤ) ≤ X)]
  have hmb : (muxLevelBound P N Bks B : ℤ) = (N : ℤ) * (X : ℤ) + Bks + B + 1 := by
    unfold muxLevelBound; push_cast; ring
  rw [hmb]
  calc |((c.mul a).relin eks).noiseAt (mc * ma) + a.noiseAt ma|
      ≤ |((c.mul a).relin eks).noiseAt (mc * ma)| + |a.noiseAt ma| := abs_add_le _ _
    _ ≤ ((X : ℤ) + Bks) + B := add_le_add hmul ha
    _ ≤ (N : ℤ) * (X : ℤ) + Bks + B + 1 := by linarith

/-- The level premises are inhabited: fresh encryptions of Boolean messages with noise
`≤ freshNoise` (here `0` and `1` with noise `freshNoise`). -/
theorem muxLevel_premises_inhabited :
    (1 : ℕ) ≤ fheRs4096.t - 1 ∧
      |(encrypt fheRs4096 1 (freshNoise : ℤ)).noiseAt 1| ≤ (freshNoise : ℤ) := by
  refine ⟨by decide, ?_⟩
  rw [encrypt_noiseAt]
  exact le_of_eq (abs_of_nonneg (by positivity))

/-- **Depth two decrypts exactly (scalar model).** The level-2 envelope at the full relinearization
allowance satisfies the `Δ·m`-lift decrypt margin, so any level-2 ciphertext whose message is below
`t` and whose noise is inside the envelope decrypts to its message. -/
theorem depth_two_decrypts_exact (c : Ct fheRs4096) (m : ℕ) (hm : m < fheRs4096.t)
    (hnoise : |c.noiseAt m| ≤
      (lifetimeNoise fheRs4096 4096 relinAllowance freshNoise 2 : ℤ)) :
    c.decrypt = m := by
  have hsafe : SafeNoise fheRs4096
      ((lifetimeNoise fheRs4096 4096 relinAllowance freshNoise 2 : ℕ) : ℤ) := by
    rw [safeNoise_natCast_iff]; decide
  have hphase : c.phase = (fheRs4096.Δ : ℤ) * m + c.noiseAt m := by
    unfold Ct.noiseAt; ring
  show decryptPhase fheRs4096 c.phase = m
  rw [hphase]
  exact decrypt_exact fheRs4096 m _ hm (SafeNoise.mono hnoise hsafe)

/-! ## 6. The threshold-decrypt release precondition (smudging window) -/

/-- **The release precondition.** A threshold decryption of a ciphertext whose noise is at most `B`,
by `parties` parties each adding a uniform smudge on `[-S, S]`, may be released at `secbits` of
statistical hiding when the smudge floods the envelope (`2^secbits·2B ≤ 2S+1`) and the summed
smudge still clears Mini's margin. Both jaws are needed: `release_hides`, `release_decrypts`. -/
structure ReleaseWindow (P : Params) (parties secbits S B : ℕ) : Prop where
  floods : 2 ^ secbits * (2 * B) ≤ 2 * S + 1
  clears : MiniMargin P (B + parties * S)

/-- Jaw 1: inside the window, any two in-envelope secrets give share distributions within
`2^-secbits`. -/
theorem ReleaseWindow.hides {P : Params} {parties secbits S B : ℕ}
    (w : ReleaseWindow P parties secbits S B) (pub e₁ e₂ : ℤ)
    (h₁ : |e₁| ≤ B) (h₂ : |e₂| ≤ B) :
    Smudging.sd S (pub + e₁) (pub + e₂) ≤ 1 / (2 : ℚ) ^ secbits :=
  Smudging.partial_decrypt_hides_exp S secbits pub e₁ e₂ B h₁ h₂ (by exact_mod_cast w.floods)

/-- Jaw 2: inside the window, the smudged threshold decryption returns exactly the message. -/
theorem ReleaseWindow.decrypts {P : Params} {parties secbits S B : ℕ}
    (w : ReleaseWindow P parties secbits S B) (m : ℕ) (e u : ℤ)
    (he : |e| ≤ B) (hu : |u| ≤ (parties : ℤ) * S) :
    decryptPhase P (liftEncode P m + (e + u)) = m := by
  apply decrypt_exact_lift P m (e + u) (B + parties * S) _ w.clears
  have := abs_add_le e u
  push_cast
  linarith

/-- The window is inhabited on Mini's parameters for fresh ciphertexts: 16 parties, 48 bits,
`S = 2^80`. -/
theorem fresh_release_window : ReleaseWindow fheRs4096 16 48 (2 ^ 80) freshNoise :=
  ⟨by decide, by unfold MiniMargin; decide⟩

/-- **Hiding forces the radius.** By the exact distance formula `sd_eq`, a smudge that hides the
two extreme secrets `±B` to `2^-secbits` (`secbits ≥ 1`) must satisfy `2^secbits·2B ≤ 2S+1`: the
flooding condition is necessary, not just sufficient. -/
theorem hiding_requires_radius (S secbits B : ℕ) (hs : 1 ≤ secbits) (pub : ℤ)
    (h : Smudging.sd S (pub + B) (pub + -(B : ℤ)) ≤ 1 / (2 : ℚ) ^ secbits) :
    2 ^ secbits * (2 * B) ≤ 2 * S + 1 := by
  rw [Smudging.sd_eq] at h
  have habs : |pub + (B : ℤ) - (pub + -(B : ℤ))| = 2 * (B : ℤ) := by
    rw [show pub + (B : ℤ) - (pub + -(B : ℤ)) = 2 * (B : ℤ) by ring]
    exact abs_of_nonneg (by positivity)
  rw [habs] at h
  have hn : (0 : ℚ) < 2 * (S : ℚ) + 1 := by positivity
  have hp : (2 : ℚ) ≤ (2 : ℚ) ^ secbits := by
    calc (2 : ℚ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ secbits := pow_le_pow_right₀ (by norm_num) hs
  by_contra hcon
  push Not at hcon
  rcases le_or_gt (2 * (B : ℤ)) (2 * (S : ℤ) + 1) with hle | hgt
  · rw [max_eq_right (by linarith)] at h
    have hcast : (((2 * (S : ℤ) + 1 - 2 * (B : ℤ)) : ℤ) : ℚ)
        = (2 * (S : ℚ) + 1) - 2 * (B : ℚ) := by push_cast; ring
    rw [hcast, sub_div, div_self hn.ne'] at h
    have h2 : 2 * (B : ℚ) / (2 * (S : ℚ) + 1) ≤ 1 / (2 : ℚ) ^ secbits := by linarith
    rw [div_le_div_iff₀ hn (by positivity)] at h2
    have hc : ((2 * S + 1 : ℕ) : ℚ) < ((2 ^ secbits * (2 * B) : ℕ) : ℚ) := by exact_mod_cast hcon
    push_cast at hc
    nlinarith
  · rw [max_eq_left (by linarith)] at h
    simp at h
    have h3 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℚ) ≤ 2 ^ secbits)
    rw [mul_inv_cancel₀ (by positivity), mul_one] at h3
    linarith

/-- The worst-case noise of a depth-1 mux output (zero relinearization noise). -/
theorem lifetimeNoise_one_value :
    lifetimeNoise fheRs4096 4096 0 freshNoise 1 = 31275279119892501 := by decide

/-- **No release window for a depth-1 mux output.** With the worst-case depth-1 envelope (even at
zero relinearization noise), any single-party smudge that hides the envelope's extremes to
`2^-48` breaks Mini's margin: threshold release at 48 bits is unavailable past depth 0 on this
modulus chain. -/
theorem no_release_window_depth_one (S : ℕ) (pub : ℤ)
    (h : Smudging.sd S (pub + (lifetimeNoise fheRs4096 4096 0 freshNoise 1 : ℕ))
      (pub + -((lifetimeNoise fheRs4096 4096 0 freshNoise 1 : ℕ) : ℤ)) ≤ 1 / (2 : ℚ) ^ 48) :
    ¬ MiniMargin fheRs4096 (lifetimeNoise fheRs4096 4096 0 freshNoise 1 + 1 * S) := by
  have hr := hiding_requires_radius S 48 _ (by norm_num) pub h
  rw [lifetimeNoise_one_value] at hr ⊢
  unfold MiniMargin
  have hq : fheRs4096.q = q4096 := rfl
  have ht : fheRs4096.t = 1032193 := rfl
  rw [hq, ht]
  unfold q4096
  omega

end Minidregg.Theory.Bfv
