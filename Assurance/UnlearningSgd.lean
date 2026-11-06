/-
# Assurance.UnlearningSgd — what an SGD deletion certificate can say: a bound, never equality.

For an iterative learner there is no subtraction. Two runs are compared: the run that used record `d`
(`x_{t+1} = f_t x_t`) and the prescribed run without it (`y_{t+1} = g_t y_t`, `d`'s slot empty). They differ only
at the steps whose batch held `d`, by at most `γ_t` there (one removed summand: `η ‖∇ℓ_d‖ / B₀`).

* `traj_gap` — if every `f_t` is `ρ`-Lipschitz, `‖x_T − y_T‖ ≤ Σ_{t<T} ρ^{T−1−t} γ_t` (Hardt–Recht–Singer's
  non-expansiveness argument; C23's contraction inequality with no injection).
* `sgd_delete_bound` — the same with `γ` supported on `d`'s steps: the residual influence of `d` is the
  contraction-discounted sum over the steps that used it. The bound holds whatever the host did about the
  deletion (including nothing): its whole content is the number it certifies (Thudi et al.).
* `sgd_delete_bound_audited` — the host term, composed with the landed displacement bound. Under SAMPLED audits the
  host may deviate (re-inject `d`'s gradient, say) on corrupt rounds. Indexing the run by audit histories, with the
  process stopping at the first alarm (the alarming round's update applied), and `ρ ≤ 1`:
  `E ‖actual − comparator‖ ≤ G + 2B/q`, where `G` bounds the discounted influence sum at every horizon and
  `2B/q` is `Selvage.Round.displacement_bound` (envelope `B` on applied and honest updates, detection `q`). It
  bounds the state at the stop, not after it: nothing runs after an alarm (DL30's qualification).

**Teeth**: `traj_gap_false_without_lip` (an expansive map, claimed `ρ = 1`, beats the bound at `T = 2`);
`audited_fires` (the composed theorem on `AuditWitness.round`, every hypothesis satisfied).
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Selvage.AuditDisplacement

namespace Minidregg.Assurance.Unlearning

open Finset Minidregg.Selvage

variable {V : Type} [NormedAddCommGroup V]

/-- The contraction-discounted influence sum `Σ_{t<T} ρ^{T−1−t} γ_t`. -/
noncomputable def disc (ρ : ℝ) (γ : ℕ → ℝ) (T : ℕ) : ℝ := ∑ t ∈ range T, ρ ^ (T - 1 - t) * γ t

lemma disc_succ (ρ : ℝ) (γ : ℕ → ℝ) (T : ℕ) : disc ρ γ (T + 1) = ρ * disc ρ γ T + γ T := by
  unfold disc
  rw [sum_range_succ, mul_sum, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
  congr 1
  refine sum_congr rfl (fun t ht => ?_)
  have : t < T := mem_range.mp ht
  rw [← mul_assoc, ← pow_succ']
  congr 2
  omega

/-- **`traj_gap`.** Lipschitz updates propagate a per-step gap with discount `ρ`. -/
theorem traj_gap (f g : ℕ → V → V) {ρ : ℝ} (hρ : 0 ≤ ρ) (γ : ℕ → ℝ)
    (hlip : ∀ t x y, ‖f t x - f t y‖ ≤ ρ * ‖x - y‖) (hgap : ∀ t x, ‖f t x - g t x‖ ≤ γ t)
    (x y : ℕ → V) (hx : ∀ t, x (t + 1) = f t (x t)) (hy : ∀ t, y (t + 1) = g t (y t)) (h0 : x 0 = y 0) :
    ∀ T, ‖x T - y T‖ ≤ disc ρ γ T := by
  intro T
  induction T with
  | zero => simp [disc, h0]
  | succ T ih =>
    rw [hx, hy, disc_succ]
    calc ‖f T (x T) - g T (y T)‖
        ≤ ‖f T (x T) - f T (y T)‖ + ‖f T (y T) - g T (y T)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ρ * ‖x T - y T‖ + γ T := add_le_add (hlip _ _ _) (hgap _ _)
      _ ≤ ρ * disc ρ γ T + γ T := by gcongr

/-- **`sgd_delete_bound`.** The runs agree off `d`'s steps `uses` and differ by at most `Γ` on them: the residual
influence of `d` at step `T` is at most the discounted count of `d`'s steps before `T`. -/
theorem sgd_delete_bound (f g : ℕ → V → V) {ρ Γ : ℝ} (hρ : 0 ≤ ρ) (uses : Finset ℕ)
    (hlip : ∀ t x y, ‖f t x - f t y‖ ≤ ρ * ‖x - y‖)
    (hoff : ∀ t, t ∉ uses → ∀ x, f t x = g t x) (hon : ∀ t x, ‖f t x - g t x‖ ≤ Γ)
    (x y : ℕ → V) (hx : ∀ t, x (t + 1) = f t (x t)) (hy : ∀ t, y (t + 1) = g t (y t)) (h0 : x 0 = y 0)
    (T : ℕ) : ‖x T - y T‖ ≤ ∑ t ∈ (range T).filter (· ∈ uses), ρ ^ (T - 1 - t) * Γ := by
  have h := traj_gap f g hρ (fun t => if t ∈ uses then Γ else 0) hlip (fun t z => by
    by_cases ht : t ∈ uses
    · simp only [ht, ite_true]; exact hon t z
    · simp only [ht, ite_false]; rw [hoff t ht z, sub_self, norm_zero]) x y hx hy h0 T
  unfold disc at h
  simpa [mul_ite, mul_zero, sum_filter] using h

/-! ## The host term: sampled audits, composed with `Round.displacement_bound` -/

namespace Audited

variable {Ω : Type}

/-- The number of live (pre-stop) rounds: the step index of the next update. -/
def liveLen (R : Round Ω) : List Ω → ℕ
  | [] => 0
  | _ :: h => if R.stopped h then liveLen R h else liveLen R h + 1

/-- The deployed state: the applied update `delta h` on every live round, frozen after the first alarm. -/
def actual (R : Round Ω) (x₀ : V) (delta : List Ω → V) : List Ω → V
  | [] => x₀
  | _ :: h => if R.stopped h then actual R x₀ delta h else actual R x₀ delta h + delta h

/-- The comparator: the prescribed run WITHOUT `d`, on the same live rounds. -/
def comp (R : Round Ω) (x₀ : V) (g : ℕ → V → V) : List Ω → V
  | [] => x₀
  | _ :: h => if R.stopped h then comp R x₀ g h else g (liveLen R h) (comp R x₀ g h)

/-- The honest update the prescribed learner WITH `d` would apply from the deployed state. -/
def honest (R : Round Ω) (x₀ : V) (f : ℕ → V → V) (delta : List Ω → V) (h : List Ω) : V :=
  f (liveLen R h) (actual R x₀ delta h) - actual R x₀ delta h

lemma injected_nonneg (R : Round Ω) (delta hon : List Ω → V) : ∀ h, 0 ≤ R.injected delta hon h
  | [] => le_refl _
  | _ :: h => by
    show 0 ≤ R.injected delta hon h + (if R.stopped h then 0 else ‖delta h - hon h‖)
    have := injected_nonneg R delta hon h
    split_ifs <;> [linarith; linarith [norm_nonneg (delta h - hon h)]]

/-- Pathwise: distance to the comparator ≤ discounted influence + injected displacement. -/
theorem pathwise (R : Round Ω) (x₀ : V) (f g : ℕ → V → V) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (γ : ℕ → ℝ) (hlip : ∀ t x y, ‖f t x - f t y‖ ≤ ρ * ‖x - y‖) (hgap : ∀ t x, ‖f t x - g t x‖ ≤ γ t)
    (delta : List Ω → V) :
    ∀ h, ‖actual R x₀ delta h - comp R x₀ g h‖
      ≤ disc ρ γ (liveLen R h) + R.injected delta (honest R x₀ f delta) h
  | [] => by simp [actual, comp, liveLen, disc, Round.injected]
  | ω :: h => by
    have ih := pathwise R x₀ f g hρ0 hρ1 γ hlip hgap delta h
    have hinj := injected_nonneg R delta (honest R x₀ f delta) h
    show ‖actual R x₀ delta (ω :: h) - comp R x₀ g (ω :: h)‖
      ≤ disc ρ γ (liveLen R (ω :: h)) + (R.injected delta (honest R x₀ f delta) h +
        if R.stopped h then 0 else ‖delta h - honest R x₀ f delta h‖)
    by_cases hs : R.stopped h = true
    · simp only [actual, comp, liveLen, hs, ite_true, add_zero]
      exact ih
    · simp only [Bool.not_eq_true] at hs
      simp only [actual, comp, liveLen, hs, Bool.false_eq_true, ite_false]
      set a := actual R x₀ delta h
      set b := comp R x₀ g h
      set k := liveLen R h
      have hfa : a + honest R x₀ f delta h = f k a := by simp [honest, a, k]
      calc ‖a + delta h - g k b‖
          ≤ ‖(a + honest R x₀ f delta h) - g k b‖ + ‖delta h - honest R x₀ f delta h‖ := by
            have := norm_sub_le_norm_sub_add_norm_sub (a + delta h) (a + honest R x₀ f delta h) (g k b)
            have e : a + delta h - (a + honest R x₀ f delta h) = delta h - honest R x₀ f delta h := by abel
            rw [e] at this; linarith
        _ = ‖f k a - g k b‖ + ‖delta h - honest R x₀ f delta h‖ := by rw [hfa]
        _ ≤ (ρ * ‖a - b‖ + γ k) + ‖delta h - honest R x₀ f delta h‖ := by
            gcongr
            calc ‖f k a - g k b‖ ≤ ‖f k a - f k b‖ + ‖f k b - g k b‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
              _ ≤ ρ * ‖a - b‖ + γ k := add_le_add (hlip _ _ _) (hgap _ _)
        _ ≤ (ρ * (disc ρ γ k + R.injected delta (honest R x₀ f delta) h) + γ k)
              + ‖delta h - honest R x₀ f delta h‖ := by gcongr
        _ ≤ disc ρ γ (k + 1) + (R.injected delta (honest R x₀ f delta) h
              + ‖delta h - honest R x₀ f delta h‖) := by
            rw [disc_succ]
            nlinarith [mul_le_of_le_one_left hinj hρ1]

/-- **`sgd_delete_bound_audited`.** Influence of `d` (bounded by `G` at every horizon) plus what a host can inject
before a sampled audit alarms (the landed `2B/q`): the expected distance of the deployed state from the run
that never used `d`. -/
theorem sgd_delete_bound_audited [Fintype Ω] [Nonempty Ω] (R : Round Ω) (x₀ : V) (f g : ℕ → V → V)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (γ : ℕ → ℝ)
    (hlip : ∀ t x y, ‖f t x - f t y‖ ≤ ρ * ‖x - y‖) (hgap : ∀ t x, ‖f t x - g t x‖ ≤ γ t)
    {G : ℝ} (hG : ∀ k, disc ρ γ k ≤ G) (delta : List Ω → V) {B q : ℝ} (hq : 0 < q)
    (hactual : ∀ h, ‖delta h‖ ≤ B) (hhonest : ∀ h, ‖honest R x₀ f delta h‖ ≤ B)
    (hcoverage : ∀ h, R.corrupt h = false → delta h = honest R x₀ f delta h)
    (hdetect : ∀ h, R.stopped h = false → R.corrupt h = true →
      q ≤ uniformProb Ω (fun ω => R.alarms h ω))
    (n : ℕ) :
    expOver Ω n (fun h => ‖actual R x₀ delta h - comp R x₀ g h‖) [] ≤ G + (2 * B) / q := by
  have hpt : ∀ h, ‖actual R x₀ delta h - comp R x₀ g h‖
      ≤ G + R.injected delta (honest R x₀ f delta) h := fun h =>
    (pathwise R x₀ f g hρ0 hρ1 γ hlip hgap delta h).trans (by linarith [hG (liveLen R h)])
  have hadd : expOver Ω n (fun h => G + R.injected delta (honest R x₀ f delta) h) []
      = G + expOver Ω n (R.injected delta (honest R x₀ f delta)) [] := by
    have := expOver.sub (fun h => G + R.injected delta (honest R x₀ f delta) h)
      (R.injected delta (honest R x₀ f delta)) n []
    simp only [add_sub_cancel_right, expOver.const] at this
    linarith
  calc expOver Ω n (fun h => ‖actual R x₀ delta h - comp R x₀ g h‖) []
      ≤ expOver Ω n (fun h => G + R.injected delta (honest R x₀ f delta) h) [] := expOver.mono hpt n []
    _ = G + expOver Ω n (R.injected delta (honest R x₀ f delta)) [] := hadd
    _ ≤ G + (2 * B) / q := by
        gcongr
        exact Round.displacement_bound R delta _ hq hactual hhonest hcoverage hdetect n

end Audited

/-! ## Teeth -/

namespace UnlearningSgdTeeth

/-- **Without `hlip` the bound is false.** `f x = 2x + 1`, `g x = 2x` (gap 1 every step), claimed `ρ = 1`:
the bound at `T = 2` is `2` but the runs are `3` apart. -/
theorem traj_gap_false_without_lip :
    ¬ ∀ (f g : ℕ → ℝ → ℝ) (x y : ℕ → ℝ),
      (∀ t z, ‖f t z - g t z‖ ≤ 1) → (∀ t, x (t + 1) = f t (x t)) → (∀ t, y (t + 1) = g t (y t)) →
      x 0 = y 0 → ‖x 2 - y 2‖ ≤ disc 1 (fun _ => 1) 2 := by
  intro h
  have := h (fun _ z => 2 * z + 1) (fun _ z => 2 * z) (fun t => 2 ^ t - 1) (fun _ => 0)
    (fun t z => by norm_num) (fun t => by rw [pow_succ]; ring) (fun t => by ring) (by norm_num)
  norm_num [disc, Finset.sum_range_succ] at this

/-- **The composed premise is inhabited and fires** on `AuditWitness.round` (always corrupt, alarms with
probability `1/2`): applied update `1`, the learner with and without `d` both the identity (`f = g`, `γ = 0`,
`G = 0`), `B = 1`, `q = 1/2`. Then honest updates are `0`, every hypothesis holds, and the bound is `4`. -/
theorem audited_fires (n : ℕ) :
    expOver (Fin 4) n (fun h => ‖Audited.actual AuditWitness.round (0 : ℝ) (fun _ => 1) h
      - Audited.comp AuditWitness.round (0 : ℝ) (fun _ z => z) h‖) [] ≤ 0 + (2 * 1) / (1 / 2) := by
  refine Audited.sgd_delete_bound_audited AuditWitness.round 0 (fun _ z => z) (fun _ z => z)
    zero_le_one (le_refl 1) (fun _ => 0) (fun _ x y => by simp) (fun _ _ => by simp)
    (fun k => by simp [disc]) (fun _ => 1) (by norm_num) (fun _ => by simp) (fun _ => by simp [Audited.honest])
    (fun h hc => by simp [AuditWitness.round] at hc) DisplacementRefutation.detect_half n

end UnlearningSgdTeeth

/-- info: 'Minidregg.Assurance.Unlearning.traj_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms traj_gap
/-- info: 'Minidregg.Assurance.Unlearning.sgd_delete_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sgd_delete_bound
/-- info: 'Minidregg.Assurance.Unlearning.Audited.sgd_delete_bound_audited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Audited.sgd_delete_bound_audited
/-- info: 'Minidregg.Assurance.Unlearning.UnlearningSgdTeeth.traj_gap_false_without_lip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UnlearningSgdTeeth.traj_gap_false_without_lip
/-- info: 'Minidregg.Assurance.Unlearning.UnlearningSgdTeeth.audited_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UnlearningSgdTeeth.audited_fires

end Minidregg.Assurance.Unlearning
