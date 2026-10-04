/-
# Bfv.Fold — the end-to-end fold theorem: K homomorphic adds decrypt to the EXACT clear sum.

**The composition this module delivers:** `Bfv.NoWrap` kills the plaintext wrap (class C),
`Bfv.Noise` kills the silent mis-decrypt (class A) — this module composes them over the actual
fold shape (a `List.foldl` of homomorphic adds over per-order encryptions, exactly the
`fhegg-fhe/src/additive.rs` loop: `Ciphertext::zero` then `+=` per order) and produces the two
operational artifacts:

  1. **`fold_decrypts_exact`** — the parametric keystone: fold ≤ K fresh encryptions (each noise
     `≤ B`), keep the plaintext sum under `t`, keep `2t·K·B + 2(t−1)·r < q` — then decrypting the
     folded ciphertext yields the EXACT integer sum of the order quantities. Not approximately:
     exactly, as an equation.
  2. **`noiseMargin` / `marginHolds`** — the Lean-emitted noise-margin OBSERVABLE. `noiseMargin`
     is the signed slack of the keystone's hypothesis; `marginHolds` is its computable ℕ-side
     check. `marginHolds_safe` proves the check implies the hypothesis, so a Rust-side gate that
     refuses to decrypt when the emitted margin is exhausted is enforcing a THEOREM's hypothesis,
     not a heuristic. The class-A cliff becomes a METER (watch the margin), not a silent edge.
  3. **`deployed_fold_decrypts_exact`** — the deployed-numbers corollary, with BOTH gates at
     their honest tight values: full-range u16 quantities, ≤ 15 orders (the `Bfv.NoWrap` tight
     capacity), fresh noise ≤ 2^20 (the fhe.rs pk-encryption scale for this set — an ASSUMPTION
     here, see honesty notes). One theorem, both silent-failure classes closed.
  4. **`fold_phase_lt_q`** — inside the envelope the fold's phase magnitude never reaches `q`,
     so the ℤ-phase model and the real mod-`q` machine agree on the fold path (with
     `Bfv.Noise.decryptPhase_add_q` closing the correspondence for a hypothetical wrap).

## Honesty notes (what the hypotheses mean, not hide)

  * `B` (the fresh-noise bound) is an INPUT: proving `B_fresh ≈ 2^20` for fhe.rs pk-encryption
    at n = 4096 requires the polynomial-product expansion — Phase-2, named, not done. The
    theorems are conditional on it and their emitted margin is only as good as that bound.
  * The margin pins prove the deployed envelope has ~enormous slack (fold noise ~2^32 against a
    budget ~2^88) — AND `margin_fails_big_noise` pins a case where the check says NO. A meter
    that cannot read empty is not a meter.

Pure. No axioms beyond the kernel triple.

**Port provenance (Mini, 2026-10-04).** Copied from breadstuffs `metatheory/Bfv/Fold.lean`
(sha256 `405494f5b88b491f8620bb1c61deb74dfcc6dc8ac276b1f9a441fb2b61baf2de`), renamespaced `Bfv` → `Minidregg.Theory.Bfv`; statements and proofs
unchanged; Bread's `#assert_all_clean` lists became Mini's `#print axioms` pins, recorded
against Bread's own axiom sets in `docs/BREAD-PORTS.md`. Mathlib-only imports.
-/
import Theory.BfvParams
import Theory.BfvNoWrap
import Theory.BfvNoise

namespace Minidregg.Theory.Bfv

variable {P : Params}

/-! ## 1. The fold, exactly as the Rust loop computes it. -/

/-- The homomorphic fold: start from `Ciphertext::zero` (phase 0), `+=` one fresh encryption per
order. `os` carries each order's (quantity, fresh-noise) pair. -/
def foldEnc (P : Params) (os : List (ℕ × ℤ)) : Ct P :=
  os.foldl (fun acc o => acc.add (encrypt P o.1 o.2)) ⟨0⟩

/-- Fold-phase decomposition (generalized accumulator): the folded phase is
`acc + Δ·(Σ quantities) + (Σ noises)` — homomorphic addition is EXACT linear algebra on phases. -/
theorem foldEnc_go (P : Params) (os : List (ℕ × ℤ)) (c : Ct P) :
    (os.foldl (fun acc o => acc.add (encrypt P o.1 o.2)) c).phase
      = c.phase + (P.Δ : ℤ) * ((os.map Prod.fst).sum : ℕ) + (os.map Prod.snd).sum := by
  induction os generalizing c with
  | nil => simp
  | cons o os ih =>
    rw [List.foldl_cons, ih]
    simp only [Ct.add, encrypt, List.map_cons, List.sum_cons]
    push_cast
    ring

/-- The folded ciphertext's phase is `Δ·(Σ quantities) + (Σ noises)`. -/
theorem foldEnc_phase (P : Params) (os : List (ℕ × ℤ)) :
    (foldEnc P os).phase
      = (P.Δ : ℤ) * ((os.map Prod.fst).sum : ℕ) + (os.map Prod.snd).sum := by
  have h := foldEnc_go P os ⟨0⟩
  simpa [foldEnc] using h

/-! ## 2. K-fold noise growth: the sound worst-case bound is `K·B`. -/

/-- Summed noise obeys the iterated triangle inequality: `|Σ e_i| ≤ (#orders)·B` when each
`|e_i| ≤ B`. (Linear worst-case — the SOUND bound; see `Bfv.Noise` for why the variance-doubling
story is a heuristic and not what is proved.) -/
theorem abs_sum_le_length_mul (es : List ℤ) (B : ℤ) (h : ∀ e ∈ es, |e| ≤ B) :
    |es.sum| ≤ (es.length : ℤ) * B := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := h e List.mem_cons_self
    have hs := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    calc |(e :: es).sum| = |e + es.sum| := by simp
      _ ≤ |e| + |es.sum| := abs_add_le _ _
      _ ≤ B + (es.length : ℤ) * B := by linarith
      _ = ((e :: es).length : ℤ) * B := by push_cast [List.length_cons]; ring

/-- `SafeNoise` is downward-closed: a bound that is safe stays safe for any smaller bound. -/
theorem SafeNoise.mono {B B' : ℤ} (hle : B' ≤ B) (h : SafeNoise P B) : SafeNoise P B' := by
  unfold SafeNoise at *
  have ht : (0 : ℤ) ≤ 2 * (P.t : ℤ) := by positivity
  have := mul_le_mul_of_nonneg_left hle ht
  linarith

/-! ## 3. THE END-TO-END KEYSTONE. -/

/-- **The fold decrypts to the exact clear sum.** For any order list `os`:
  * every fresh noise bounded (`|e_i| ≤ B`),
  * the plaintext sum under `t` (the `Bfv.NoWrap` gate discharges this from `N·qmax < t`),
  * the accumulated noise margin holds (`SafeNoise P (#os·B)`, the emitted-meter hypothesis),
then decrypting the homomorphic fold returns EXACTLY the integer sum of the quantities. Both
silent-failure classes are excluded at once: no plaintext wrap (the sum is below `t` and survives
the readout), no noise mis-decrypt (the margin keeps rounding exact). -/
theorem fold_decrypts_exact (P : Params) (os : List (ℕ × ℤ)) (B : ℤ)
    (hfresh : ∀ o ∈ os, |o.2| ≤ B)
    (hnowrap : (os.map Prod.fst).sum < P.t)
    (hmargin : SafeNoise P ((os.length : ℤ) * B)) :
    (foldEnc P os).decrypt = ((os.map Prod.fst).sum : ℤ) := by
  have habs : |(os.map Prod.snd).sum| ≤ (os.length : ℤ) * B := by
    have h := abs_sum_le_length_mul (os.map Prod.snd) B (by
      intro e he
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp he
      exact hfresh o ho)
    simpa using h
  have hsafe : SafeNoise P |(os.map Prod.snd).sum| := SafeNoise.mono habs hmargin
  show decryptPhase P (foldEnc P os).phase = _
  rw [foldEnc_phase]
  exact decrypt_exact P _ _ hnowrap hsafe

/-! ## 4. The phase stays inside `(−q, q)` — the mod-q model correspondence, discharged
in-envelope. -/

/-- Inside the margin, a phase `Δ·m + e` has magnitude `< q` — so the ℤ-phase model and the
mod-`q` machine coincide on the fold path (no hidden `±q` wrap to correspond across; and if there
were one, `decryptPhase_add_q` says it shifts the readout by exactly `t`). -/
theorem phase_lt_q (P : Params) (m : ℕ) (e : ℤ)
    (hm : m < P.t) (hbound : SafeNoise P |e|) :
    |(P.Δ : ℤ) * m + e| < (P.q : ℤ) := by
  unfold SafeNoise at hbound
  set T : ℤ := (P.t : ℤ) with hT_def
  set Q : ℤ := (P.q : ℤ) with hQ_def
  set D : ℤ := (P.Δ : ℤ) with hD_def
  set R : ℤ := (P.r : ℤ) with hR_def
  set M : ℤ := (m : ℤ) with hM_def
  have hQeq : Q = D * T + R := by
    rw [hQ_def, hD_def, hT_def, hR_def]; exact_mod_cast P.q_eq
  have hT0 : (0 : ℤ) < T := by rw [hT_def]; exact_mod_cast P.t_pos
  have hD0 : (0 : ℤ) ≤ D := by rw [hD_def]; exact_mod_cast Nat.zero_le _
  have hR0 : (0 : ℤ) ≤ R := by rw [hR_def]; exact_mod_cast Nat.zero_le _
  have hM0 : (0 : ℤ) ≤ M := by rw [hM_def]; exact_mod_cast Nat.zero_le _
  have hMT : M < T := by rw [hM_def, hT_def]; exact_mod_cast hm
  -- triangle: |Δm + e| ≤ Δm + |e|
  have htri : |D * M + e| ≤ D * M + |e| := by
    calc |D * M + e| ≤ |D * M| + |e| := abs_add_le _ _
      _ = D * M + |e| := by rw [abs_of_nonneg (mul_nonneg hD0 hM0)]
  -- scale the target by T and reason on atoms
  have hDM_le : D * M ≤ D * (T - 1) := mul_le_mul_of_nonneg_left (by omega) hD0
  have hTDM_le : T * (D * M) ≤ T * (D * (T - 1)) :=
    mul_le_mul_of_nonneg_left hDM_le hT0.le
  have hr_le_tr : R ≤ T * R := le_mul_of_one_le_left hR0 (by omega)
  have hDT0 : (0 : ℤ) ≤ D * T := mul_nonneg hD0 hT0.le
  have hTR0 : (0 : ℤ) ≤ T * R := mul_nonneg hT0.le hR0
  have htr0 : (0 : ℤ) ≤ (T - 1) * R := mul_nonneg (by omega) hR0
  -- from the margin: 2·T·|e| < Q = D·T + R
  have habs2 : 2 * T * |e| < Q := by linarith
  have hscaled : T * (D * M + |e|) < T * Q := by
    have hexp : T * (D * M + |e|) = T * (D * M) + T * |e| := by ring
    have hexp2 : T * Q = T * (D * (T - 1)) + D * T + T * R := by rw [hQeq]; ring
    -- 2T|e| < D·T + R ≤ D·T + T·R  and  0 ≤ D·T + T·R  give  T|e| < D·T + T·R
    nlinarith [habs2, hr_le_tr, hDT0, hTR0, hTDM_le]
  have hfinal : D * M + |e| < Q := lt_of_mul_lt_mul_left hscaled hT0.le
  linarith
/-- Fold-level corollary of `phase_lt_q`: the honest fold's phase never reaches `±q`. -/
theorem fold_phase_lt_q (P : Params) (os : List (ℕ × ℤ)) (B : ℤ)
    (hfresh : ∀ o ∈ os, |o.2| ≤ B)
    (hnowrap : (os.map Prod.fst).sum < P.t)
    (hmargin : SafeNoise P ((os.length : ℤ) * B)) :
    |(foldEnc P os).phase| < (P.q : ℤ) := by
  have habs : |(os.map Prod.snd).sum| ≤ (os.length : ℤ) * B := by
    have h := abs_sum_le_length_mul (os.map Prod.snd) B (by
      intro e he
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp he
      exact hfresh o ho)
    simpa using h
  rw [foldEnc_phase]
  exact phase_lt_q P _ _ hnowrap (SafeNoise.mono habs hmargin)

/-! ## 5. The noise-margin OBSERVABLE (the emitted meter). -/

/-- The Lean-emitted noise margin: the signed slack of the keystone's hypothesis after `K` adds of
noise-`≤ B` ciphertexts. Positive ⇒ decrypt is provably exact (`margin_pos_safe`). This number —
not "did the KAT pass" — is the class-A observable: a METER that degrades before it fails. -/
def noiseMargin (P : Params) (K : ℕ) (B : ℤ) : ℤ :=
  (P.q : ℤ) - (2 * (P.t : ℤ) * ((K : ℤ) * B) + 2 * ((P.t : ℤ) - 1) * (P.r : ℤ))

/-- A positive margin IS the keystone's hypothesis. -/
theorem margin_pos_safe (P : Params) (K : ℕ) (B : ℤ)
    (h : 0 < noiseMargin P K B) : SafeNoise P ((K : ℤ) * B) := by
  unfold noiseMargin at h
  unfold SafeNoise
  linarith

/-- The computable ℕ-side margin check — the thing to EMIT for the Rust gate (compare against
this exact inequality; the `decide` pins below evaluate it in the kernel). -/
def marginHolds (P : Params) (K B : ℕ) : Bool :=
  decide (2 * P.t * (K * B) + 2 * (P.t - 1) * P.r < P.q)

/-- The check is sound: `marginHolds = true` implies the keystone hypothesis `SafeNoise`. So a
production decrypt gated on the emitted check enforces a theorem's hypothesis, not a vibe. -/
theorem marginHolds_safe (P : Params) (K B : ℕ)
    (h : marginHolds P K B = true) : SafeNoise P ((K : ℤ) * (B : ℤ)) := by
  unfold marginHolds at h
  have hnat := of_decide_eq_true h
  have h1 : (1 : ℕ) ≤ P.t := P.t_pos
  unfold SafeNoise
  zify [h1] at hnat
  linarith

/-! ## 6. Deployed-numbers pins — the meter reads FULL on the real envelope, and it CAN read
empty. -/

/-- **The deployed envelope is safe with ~2^56 to spare:** 4096 orders × fresh noise 2^20
(`K·B = 2^32` against a ~2^88 budget). Kernel-evaluated on the real 109-bit `q`. -/
theorem deployed_margin_holds : marginHolds fheRs4096 4096 (2 ^ 20) = true := by decide

/-- **The meter can read EMPTY** — one ciphertext of noise `2^90` (past the ~2^88 budget) is
REFUSED by the same check. A margin check that cannot fail would be a fake meter. -/
theorem margin_fails_big_noise : marginHolds fheRs4096 1 (2 ^ 90) = false := by decide

/-- **THE DEPLOYED KEYSTONE, both gates at their honest tight values:** ≤ 15 full-range-u16
orders (the tight `Bfv.NoWrap` capacity), fresh noise ≤ 2^20 — the fold decrypts to the exact
clear sum on the fhe.rs degree-4096 parameters. Class (A) and class (C) closed in one statement. -/
theorem deployed_fold_decrypts_exact (os : List (ℕ × ℤ))
    (hqty : ∀ o ∈ os, o.1 ≤ 65535)
    (hlen : os.length ≤ 15)
    (hfresh : ∀ o ∈ os, |o.2| ≤ 2 ^ 20) :
    (foldEnc fheRs4096 os).decrypt = ((os.map Prod.fst).sum : ℤ) := by
  apply fold_decrypts_exact fheRs4096 os (2 ^ 20) hfresh
  · -- no-wrap gate, discharged by the tight u16 capacity
    apply u16_bucket_capacity
    · intro q hq
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hq
      exact hqty o ho
    · simpa using hlen
  · -- noise margin: len ≤ 15 ≤ 4096, so the deployed pin covers it
    apply SafeNoise.mono _ (marginHolds_safe fheRs4096 4096 (2 ^ 20) deployed_margin_holds)
    have hlen' : (os.length : ℤ) ≤ 4096 := by exact_mod_cast hlen.trans (by norm_num)
    have hB : (0 : ℤ) ≤ 2 ^ 20 := by positivity
    push_cast
    nlinarith [hlen', hB]

/-- info: 'Minidregg.Theory.Bfv.foldEnc_phase' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms foldEnc_phase
/-- info: 'Minidregg.Theory.Bfv.abs_sum_le_length_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms abs_sum_le_length_mul
/-- info: 'Minidregg.Theory.Bfv.SafeNoise.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SafeNoise.mono
/-- info: 'Minidregg.Theory.Bfv.fold_decrypts_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_decrypts_exact
/-- info: 'Minidregg.Theory.Bfv.phase_lt_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms phase_lt_q
/-- info: 'Minidregg.Theory.Bfv.fold_phase_lt_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_phase_lt_q
/-- info: 'Minidregg.Theory.Bfv.margin_pos_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms margin_pos_safe
/-- info: 'Minidregg.Theory.Bfv.marginHolds_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms marginHolds_safe
/-- info: 'Minidregg.Theory.Bfv.deployed_margin_holds' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_margin_holds
/-- info: 'Minidregg.Theory.Bfv.margin_fails_big_noise' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms margin_fails_big_noise
/-- info: 'Minidregg.Theory.Bfv.deployed_fold_decrypts_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_fold_decrypts_exact

end Minidregg.Theory.Bfv
