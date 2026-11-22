/-
# Theory.WetwareSafetyAndDuress — Vinge "Mysterious Stranger" defenses for a wearable SHE

When the cryptography holds, the attacker goes above and around it. Two organs, each stated
over what the wearer actually sees or what the adversary actually holds — never over the
guard's internal state:

* **Part A `WetwareSafety`.** A per-channel stateful AR scrubber: quantize (drop the
  sub-perceptual LSBs) → slew clamp (`|o_{t+1} - o_t| ≤ dmax`) → reversal hold-off (a change
  of luminance direction is released only `H` frames after the previous one).
  `scrubber_enforces_slew_and_reversal_bound` is stated over an *observer's* reading of the
  emitted trace of the channel it runs on (deployed: the luma plane `Y'`; per-`R/G/B` guarding
  does not bound luma — `tooth_per_channel_rgb_misses_luma_flicker`) (`revAt`, defined from the output alone); `revSpaced_count_le` turns the
  spacing into a sliding-window count (at `60` fps with `H = 12`: at most `5` reversals in any
  `60`-frame window, i.e. fewer than three flash pairs per second — the ITU-R BT.1702 /
  Harding three-flash line). `scrubber_kills_subthreshold_stego` / `scrubber_zero_covert_capacity`:
  the emitted video, audio and release cadence are a function of the high bits and the cadence
  bucket alone, so an LSB or sub-tick-jitter channel through the lens carries `0` bits.
* **Part B `DuressChaffVolume`.** A fixed-geometry `N`-slot vault: every slot is one element of
  an additive group (deployed: 64-byte XOR blocks, `body ‖ tag` masked by a cSHAKE256 pad).
  `duress_adversary_cannot_distinguish_sovereign_from_chaff`: for every distinguisher that
  holds the duress key and the whole image, the acceptance count with sovereign slots present
  equals the count with pure chaff (pointwise-equal view distributions: TVD `= 0`).

Modeling boundary (stated, not hidden): Part B is the *ideal-XOF* model — the sovereign root's
pads are an independent uniform vector. With deployed cSHAKE256 the advantage is bounded by a
PRF advantage against cSHAKE256 under the sovereign root; that reduction is not mechanised here.
The `#tooth` theorems show each premise is load-bearing (no quantization ⇒ LSBs leak; no
hold-off ⇒ a 15 Hz strobe passes; variable-length tables or root-unseparated pads ⇒ advantage).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card

namespace Minidregg.Theory.WetwareSafetyAndDuress

open Finset

/-! ## §1. Part A — the scrubber (one byte channel; frames are pointwise products) -/

/-- `Q`: sub-perceptual quantum (LSB bucket); `dmax`: per-frame slew; `H`: reversal hold-off. -/
structure ScrubParams where
  Q : Nat
  dmax : Nat
  H : Nat
  deriving Repr, DecidableEq

structure ScrubParams.Valid (p : ScrubParams) : Prop where
  q_pos : 0 < p.Q
  q_dvd : p.Q ∣ p.dmax
  h_pos : 0 < p.H

/-- The deployed wearable profile at 60 fps: drop 2 LSBs, slew 16/frame, hold-off 12 frames. -/
def wearable60 : ScrubParams := ⟨4, 16, 12⟩

theorem wearable60_valid : wearable60.Valid := ⟨by decide, by decide, by decide⟩

inductive Dir where
  | flat
  | up
  | down
  deriving DecidableEq, Repr

structure PixState where
  prev : Nat
  dir : Dir
  since : Nat
  deriving DecidableEq, Repr

/-- Perceptual quantization of a byte: the high bits only. -/
def quant (Q x : Nat) : Nat := min x 255 / Q * Q

def slewClamp (d prev target : Nat) : Nat :=
  if prev + d < target then prev + d
  else if target + d < prev then prev - d
  else target

def dirOf (a b : Nat) : Dir :=
  if a < b then .up else if b < a then .down else .flat

/-- `s` reverses `d`: both nonzero and opposite. -/
def isRev (d s : Dir) : Bool := s != .flat && d != .flat && s != d

/-- The decision after the slew clamp proposed `y`: hold, release a reversal, or follow. -/
def stepCore (p : ScrubParams) (st : PixState) (y : Nat) : PixState :=
  let s := dirOf st.prev y
  if isRev st.dir s then
    if st.since + 1 < p.H then { st with since := min (st.since + 1) p.H }
    else ⟨y, s, 0⟩
  else if s = .flat then { st with since := min (st.since + 1) p.H }
  else ⟨y, s, min (st.since + 1) p.H⟩

def step (p : ScrubParams) (st : PixState) (x : Nat) : PixState :=
  stepCore p st (slewClamp p.dmax st.prev (quant p.Q x))

def initState (p : ScrubParams) (p0 : Nat) : PixState := ⟨p0, .flat, p.H⟩

def run (p : ScrubParams) (p0 : Nat) (x : Nat → Nat) : Nat → PixState
  | 0 => initState p p0
  | t + 1 => step p (run p p0 x t) (x t)

/-- The emitted trace: `out 0 = p0`; `out (t+1)` is emitted after consuming input frame `t`. -/
def out (p : ScrubParams) (p0 : Nat) (x : Nat → Nat) (t : Nat) : Nat := (run p p0 x t).prev

/-! ## §2. The observer's specification (defined from the emitted trace alone) -/

/-- Direction of the most recent nonzero change of a trace. -/
def odir (o : Nat → Nat) : Nat → Dir
  | 0 => .flat
  | t + 1 => if o (t + 1) = o t then odir o t else dirOf (o t) (o (t + 1))

/-- A luminance reversal at frame `t` (the edge of a flash), read off the trace. -/
def revAt (o : Nat → Nat) : Nat → Bool
  | 0 => false
  | t + 1 => decide (o (t + 1) ≠ o t) && isRev (odir o t) (dirOf (o t) (o (t + 1)))

def SlewBounded (d : Nat) (o : Nat → Nat) : Prop :=
  ∀ t, o (t + 1) ≤ o t + d ∧ o t ≤ o (t + 1) + d

def RevSpaced (H : Nat) (o : Nat → Nat) : Prop :=
  ∀ i j, revAt o i = true → revAt o j = true → i < j → H ≤ j - i

def PhotosafeTrace (p : ScrubParams) (o : Nat → Nat) : Prop :=
  SlewBounded p.dmax o ∧ RevSpaced p.H o

/-! ## §3. Step lemmas -/

theorem dirOf_eq_flat_iff {a b : Nat} : dirOf a b = .flat ↔ a = b := by
  unfold dirOf
  by_cases h1 : a < b
  · simp only [h1, ↓reduceIte, reduceCtorEq, false_iff]; omega
  · by_cases h2 : b < a
    · simp only [h1, h2, ↓reduceIte, reduceCtorEq, false_iff]; omega
    · simp only [h1, h2, ↓reduceIte, true_iff]; omega

theorem isRev_flat {d s : Dir} (h : isRev d s = true) : s ≠ .flat := by
  cases d <;> cases s <;> simp_all [isRev]

theorem slewClamp_bounds (d prev tgt : Nat) :
    slewClamp d prev tgt ≤ prev + d ∧ prev ≤ slewClamp d prev tgt + d := by
  unfold slewClamp; split_ifs <;> omega

section StepLemmas
variable (p : ScrubParams) (st : PixState) (x : Nat)

theorem step_slew :
    (step p st x).prev ≤ st.prev + p.dmax ∧ st.prev ≤ (step p st x).prev + p.dmax := by
  have h := slewClamp_bounds p.dmax st.prev (quant p.Q x)
  simp only [step, stepCore]
  split_ifs <;> simp only <;> omega

theorem step_since_le : (step p st x).since ≤ st.since + 1 := by
  simp only [step, stepCore]
  split_ifs <;> simp only <;> omega

theorem stepCore_dir (y : Nat) : (stepCore p st y).dir =
    if (stepCore p st y).prev = st.prev then st.dir else dirOf st.prev (stepCore p st y).prev := by
  unfold stepCore
  by_cases h1 : isRev st.dir (dirOf st.prev y) = true
  · have hne : y ≠ st.prev := fun he => isRev_flat h1 (dirOf_eq_flat_iff.mpr he.symm)
    by_cases h2 : st.since + 1 < p.H
    · simp [h1, h2]
    · simp [h1, h2, hne]
  · by_cases h3 : dirOf st.prev y = .flat
    · simp [h3, isRev]
    · have hne : y ≠ st.prev := fun he => h3 (dirOf_eq_flat_iff.mpr he.symm)
      simp [h1, h3, hne]

theorem step_dir : (step p st x).dir =
    if (step p st x).prev = st.prev then st.dir else dirOf st.prev (step p st x).prev :=
  stepCore_dir p st _

theorem step_rev_branch (hne : (step p st x).prev ≠ st.prev)
    (hrev : isRev st.dir (dirOf st.prev (step p st x).prev) = true) :
    (step p st x).since = 0 ∧ p.H ≤ st.since + 1 := by
  simp only [step, stepCore] at hne hrev ⊢
  split_ifs at hne hrev ⊢ with h1 h2 h3 <;> simp_all

end StepLemmas

/-! ## §4. `scrubber_enforces_slew_and_reversal_bound` -/

section Main
variable (p : ScrubParams) (p0 : Nat) (x : Nat → Nat)

theorem run_dir_eq_odir : ∀ t, (run p p0 x t).dir = odir (out p p0 x) t
  | 0 => rfl
  | t + 1 => by
    have ih := run_dir_eq_odir t
    show (step p (run p p0 x t) (x t)).dir = _
    rw [step_dir, ih]
    rfl

theorem revAt_out_succ (t : Nat) (h : revAt (out p p0 x) (t + 1) = true) :
    (run p p0 x (t + 1)).since = 0 ∧ p.H ≤ (run p p0 x t).since + 1 := by
  simp only [revAt, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hne, hrev⟩ := h
  rw [← run_dir_eq_odir] at hrev
  exact step_rev_branch p (run p p0 x t) (x t) hne hrev

theorem since_le_after_rev (i : Nat) (hi : revAt (out p p0 x) i = true) :
    ∀ k, (run p p0 x (i + k)).since ≤ k
  | 0 => by
    cases i with
    | zero => simp [revAt] at hi
    | succ i => exact (revAt_out_succ p p0 x i hi).1.le
  | k + 1 => by
    have ih := since_le_after_rev i hi k
    have hs := step_since_le p (run p p0 x (i + k)) (x (i + k))
    show (step p (run p p0 x (i + k)) (x (i + k))).since ≤ k + 1
    omega

theorem scrubber_slew : SlewBounded p.dmax (out p p0 x) :=
  fun t => step_slew p (run p p0 x t) (x t)

theorem scrubber_reversal_spacing : RevSpaced p.H (out p p0 x) := by
  intro i j hi hj hij
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have h1 := (revAt_out_succ p p0 x j' hj).2
  have h2 := since_le_after_rev p p0 x i hi (j' - i)
  rw [show i + (j' - i) = j' by omega] at h2
  omega

/-- **No untrusted grain stream can drive an unsafe strobe through the lens**: for every raw
input, the emitted trace is slew-bounded and its reversals are at least `H` frames apart. -/
theorem scrubber_enforces_slew_and_reversal_bound : PhotosafeTrace p (out p p0 x) :=
  ⟨scrubber_slew p p0 x, scrubber_reversal_spacing p p0 x⟩

end Main

/-! ## §5. Sliding-window reversal count -/

theorem revSpaced_window_le_one {H : Nat} {o : Nat → Nat} (hs : RevSpaced H o) (a : Nat) :
    ((range H).filter (fun k => revAt o (a + k) = true)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro u hu v hv
  simp only [Finset.mem_filter, Finset.mem_range] at hu hv
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := hs _ _ hu.2 hv.2 (by omega); omega
  · have := hs _ _ hv.2 hu.2 (by omega); omega

/-- Any window of `n·H` consecutive frames holds at most `n` reversals. -/
theorem revSpaced_count_le {H : Nat} {o : Nat → Nat} (hs : RevSpaced H o) (a n : Nat) :
    ((range (n * H)).filter (fun k => revAt o (a + k) = true)).card ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hw := revSpaced_window_le_one hs (a + n * H)
    rw [Finset.card_filter] at ih hw ⊢
    rw [Nat.succ_mul, Finset.sum_range_add]
    simp only [← Nat.add_assoc] at hw ⊢
    omega

/-- At 60 fps the deployed profile admits at most 5 reversals in any one-second window (fewer
than three flash pairs per second), whatever the grain sends. -/
theorem wearable60_at_most_5_reversals_per_second (p0 : Nat) (x : Nat → Nat) (a : Nat) :
    ((range 60).filter (fun k => revAt (out wearable60 p0 x) (a + k) = true)).card ≤ 5 :=
  revSpaced_count_le (scrubber_reversal_spacing wearable60 p0 x) a 5

/-! ## §6. `scrubber_kills_subthreshold_stego` — zero covert LSB / jitter capacity -/

theorem step_congr (p : ScrubParams) (st : PixState) {a b : Nat}
    (h : quant p.Q a = quant p.Q b) : step p st a = step p st b := by
  simp only [step, h]

theorem run_congr (p : ScrubParams) (p0 : Nat) {x x' : Nat → Nat}
    (h : ∀ t, quant p.Q (x t) = quant p.Q (x' t)) : ∀ t, run p p0 x t = run p p0 x' t
  | 0 => rfl
  | t + 1 => by
    simp only [run]
    rw [run_congr p p0 h t]
    exact step_congr p _ (h t)

theorem quant_eq_of_hi {Q a b : Nat} (ha : a < 256) (hb : b < 256) (h : a / Q = b / Q) :
    quant Q a = quant Q b := by
  simp only [quant, Nat.min_eq_left (show a ≤ 255 by omega),
    Nat.min_eq_left (show b ≤ 255 by omega), h]

/-- Audio: offset-binary samples, drop `k` LSBs. -/
def quantAudio (k s : Nat) : Nat := s / 2 ^ k * 2 ^ k

/-- Frame-release cadence snapping: a frame requested at tick `τ` is released at the next
vsync boundary of period `P`. -/
def snapRelease (P τ : Nat) : Nat := (τ / P + 1) * P

theorem snapRelease_bounds {P : Nat} (hP : 0 < P) (τ : Nat) :
    τ < snapRelease P τ ∧ snapRelease P τ ≤ τ + P ∧ P ∣ snapRelease P τ := by
  have h1 := Nat.div_add_mod' τ P
  have h2 := Nat.mod_lt τ hP
  refine ⟨?_, ?_, Nat.dvd_mul_left _ _⟩ <;>
  · simp only [snapRelease, Nat.add_mul, Nat.one_mul]; omega

theorem snapRelease_kills_jitter (P n j j' : Nat) (hj : j < P) (hj' : j' < P) :
    snapRelease P (n * P + j) = snapRelease P (n * P + j') := by
  have hP : 0 < P := by omega
  simp only [snapRelease, Nat.add_comm (n * P), Nat.add_mul_div_right _ _ hP,
    Nat.div_eq_of_lt hj, Nat.div_eq_of_lt hj']

/-- A frame stream of `P` byte channels, `A` audio samples and requested release ticks. -/
structure AVStream (P A : Nat) where
  vid : Fin P → Nat → Nat
  aud : Fin A → Nat → Nat
  tick : Nat → Nat

structure ScrubCfg where
  px : ScrubParams
  audioK : Nat
  period : Nat
  p0 : Nat

def scrubAV {P A : Nat} (c : ScrubCfg) (s : AVStream P A) :
    (Fin P → Nat → Nat) × (Fin A → Nat → Nat) × (Nat → Nat) :=
  (fun i => out c.px c.p0 (s.vid i), fun j t => quantAudio c.audioK (s.aud j t),
    fun t => snapRelease c.period (s.tick t))

/-- Two raw streams that agree on everything a human can perceive: bytes, same high bits,
same audio high bits, same cadence bucket (they may differ in every LSB and every sub-tick). -/
def SubPerceptualTwin {P A : Nat} (c : ScrubCfg) (s s' : AVStream P A) : Prop :=
  (∀ i t, s.vid i t < 256 ∧ s'.vid i t < 256 ∧ s.vid i t / c.px.Q = s'.vid i t / c.px.Q) ∧
  (∀ j t, s.aud j t / 2 ^ c.audioK = s'.aud j t / 2 ^ c.audioK) ∧
  (∀ t, s.tick t / c.period = s'.tick t / c.period)

/-- **Sub-perceptual LSB / sub-tick jitter differences map to the identical scrubbed stream.** -/
theorem scrubber_kills_subthreshold_stego {P A : Nat} (c : ScrubCfg) (s s' : AVStream P A)
    (h : SubPerceptualTwin c s s') : scrubAV c s = scrubAV c s' := by
  obtain ⟨hv, ha, ht⟩ := h
  simp only [scrubAV, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext i t
    exact congrArg PixState.prev (run_congr c.px c.p0
      (fun t => quant_eq_of_hi (hv i t).1 (hv i t).2.1 (hv i t).2.2) t)
  · funext j t; simp only [quantAudio, ha j t]
  · funext t; simp only [snapRelease, ht t]

/-- The perceptual projection of a raw stream. -/
def highBits {P A : Nat} (c : ScrubCfg) (s : AVStream P A) :
    (Fin P → Nat → Nat) × (Fin A → Nat → Nat) × (Nat → Nat) :=
  (fun i t => s.vid i t / c.px.Q, fun j t => s.aud j t / 2 ^ c.audioK,
    fun t => s.tick t / c.period)

/-- **`0` bits/frame covert capacity**: the scrubbed stream factors through the perceptual
projection, so the LSB / jitter residue has no influence on anything the wearer receives. -/
theorem scrubber_zero_covert_capacity {P A : Nat} (c : ScrubCfg) (hQ : 0 < c.px.Q)
    (hP : 0 < c.period) :
    ∃ F : (Fin P → Nat → Nat) × (Fin A → Nat → Nat) × (Nat → Nat) →
        (Fin P → Nat → Nat) × (Fin A → Nat → Nat) × (Nat → Nat),
      ∀ s : AVStream P A, (∀ i t, s.vid i t < 256) → scrubAV c s = F (highBits c s) := by
  refine ⟨fun h => scrubAV c ⟨fun i t => h.1 i t * c.px.Q, fun j t => h.2.1 j t * 2 ^ c.audioK,
    fun t => h.2.2 t * c.period⟩, fun s hs => scrubber_kills_subthreshold_stego c _ _ ?_⟩
  have hk : 0 < 2 ^ c.audioK := Nat.two_pow_pos _
  refine ⟨fun i t => ⟨hs i t, ?_, ?_⟩, fun j t => ?_, fun t => ?_⟩
  · have := Nat.div_mul_le_self (s.vid i t) c.px.Q; have := hs i t
    simp only [highBits]; omega
  · simp only [highBits, Nat.mul_div_cancel _ hQ]
  · simp only [highBits, Nat.mul_div_cancel _ hk]
  · simp only [highBits, Nat.mul_div_cancel _ hP]

/-! ## §7. Idempotence: the scrubber is the identity on safe canonical streams -/

/-- The emitted-trace view of an input stream that starts from `p0`. -/
def ext (p0 : Nat) (x : Nat → Nat) : Nat → Nat
  | 0 => p0
  | t + 1 => x t

structure SafeCanonical (p : ScrubParams) (p0 : Nat) (x : Nat → Nat) : Prop where
  bytes : ∀ t, x t < 256
  lattice : ∀ t, p.Q ∣ x t
  photosafe : PhotosafeTrace p (ext p0 x)

section Fixpoint
variable {p : ScrubParams} {p0 : Nat} {x : Nat → Nat}

theorem fixpoint_inv (hp : p.Valid) (h : SafeCanonical p p0 x) : ∀ t,
    (run p p0 x t).prev = ext p0 x t ∧ (run p p0 x t).dir = odir (ext p0 x) t ∧
    ((run p p0 x t).since < p.H →
      ∃ i ≤ t, revAt (ext p0 x) i = true ∧ (run p p0 x t).since = t - i)
  | 0 => ⟨rfl, rfl, fun hlt => absurd hlt (by simp [run, initState])⟩
  | t + 1 => by
    obtain ⟨hprev, hdir, hsince⟩ := fixpoint_inv hp h t
    have hq : quant p.Q (x t) = ext p0 x (t + 1) := by
      simp only [quant, Nat.min_eq_left (show x t ≤ 255 by have := h.bytes t; omega), ext]
      exact Nat.div_mul_cancel (h.lattice t)
    have hy : slewClamp p.dmax (run p p0 x t).prev (quant p.Q (x t)) = ext p0 x (t + 1) := by
      rw [hq, hprev]; have := h.photosafe.1 t; unfold slewClamp; split_ifs <;> omega
    have hrevE : revAt (ext p0 x) (t + 1) =
        (decide (ext p0 x (t + 1) ≠ ext p0 x t) &&
          isRev (odir (ext p0 x) t) (dirOf (ext p0 x t) (ext p0 x (t + 1)))) := rfl
    have hodE : odir (ext p0 x) (t + 1) = if ext p0 x (t + 1) = ext p0 x t then odir (ext p0 x) t
        else dirOf (ext p0 x t) (ext p0 x (t + 1)) := rfl
    have hrun : run p p0 x (t + 1) = step p (run p p0 x t) (x t) := rfl
    rw [hrun]
    simp only [step, stepCore, hy]
    rw [hprev, hdir] at *
    split_ifs with h1 h2 h3 <;> dsimp only
    · -- hold branch is unreachable: the input reversal is spaced
      exfalso
      have hne : ext p0 x (t + 1) ≠ ext p0 x t := fun he =>
        isRev_flat h1 (dirOf_eq_flat_iff.mpr he.symm)
      obtain ⟨i, hi, hri, hs⟩ := hsince (by omega)
      have := h.photosafe.2 i (t + 1) hri (by rw [hrevE]; simp [hne, h1]) (by omega)
      omega
    · have hne : ext p0 x (t + 1) ≠ ext p0 x t := fun he =>
        isRev_flat h1 (dirOf_eq_flat_iff.mpr he.symm)
      refine ⟨rfl, by rw [hodE]; simp [hne], fun _ => ⟨t + 1, le_rfl, ?_, by simp⟩⟩
      rw [hrevE]; simp [hne, h1]
    · have he : ext p0 x t = ext p0 x (t + 1) := dirOf_eq_flat_iff.mp h3
      refine ⟨he, by rw [hodE]; simp [he], fun hlt => ?_⟩
      obtain ⟨i, hi, hri, hs⟩ := hsince (by omega)
      exact ⟨i, by omega, hri, by omega⟩
    · have hne : ext p0 x (t + 1) ≠ ext p0 x t := fun he => h3 (dirOf_eq_flat_iff.mpr he.symm)
      refine ⟨rfl, by rw [hodE]; simp [hne], fun hlt => ?_⟩
      obtain ⟨i, hi, hri, hs⟩ := hsince (by omega)
      exact ⟨i, by omega, hri, by omega⟩

/-- A safe, canonical input passes the lens unchanged. -/
theorem scrubber_fixpoint_on_safe_canonical (hp : p.Valid) (h : SafeCanonical p p0 x) :
    ∀ t, out p p0 x t = ext p0 x t :=
  fun t => (fixpoint_inv hp h t).1

end Fixpoint

theorem quant_le (Q x : Nat) : quant Q x ≤ 255 :=
  le_trans (Nat.div_mul_le_self _ _) (Nat.min_le_right _ _)

theorem quant_dvd (Q x : Nat) : Q ∣ quant Q x := Nat.dvd_mul_left _ _

/-- The emitted trace is a byte on the quantization lattice (the Rust `u8` storage is exact). -/
theorem scrubber_output_is_lattice_byte (p : ScrubParams) (hp : p.Valid) (p0 : Nat) (x : Nat → Nat)
    (h0 : p0 ≤ 255) (hq0 : p.Q ∣ p0) : ∀ t, out p p0 x t ≤ 255 ∧ p.Q ∣ out p p0 x t
  | 0 => ⟨h0, hq0⟩
  | t + 1 => by
    obtain ⟨ih1, ih2⟩ := scrubber_output_is_lattice_byte p hp p0 x h0 hq0 t
    have hb := quant_le p.Q (x t)
    have hd := quant_dvd p.Q (x t)
    have hy : slewClamp p.dmax (out p p0 x t) (quant p.Q (x t)) ≤ 255 ∧
        p.Q ∣ slewClamp p.dmax (out p p0 x t) (quant p.Q (x t)) := by
      unfold slewClamp
      split_ifs with h1 h2
      · exact ⟨by omega, Nat.dvd_add ih2 hp.q_dvd⟩
      · exact ⟨by omega, Nat.dvd_sub ih2 hp.q_dvd⟩
      · exact ⟨hb, hd⟩
    show (step p (run p p0 x t) (x t)).prev ≤ 255 ∧ p.Q ∣ (step p (run p p0 x t) (x t)).prev
    simp only [step, stepCore]
    split_ifs <;> first | exact ⟨ih1, ih2⟩ | exact hy

/-- **`scrubber_idempotent_on_safe_canonical`**: scrubbing the scrubbed stream again changes
nothing — the scrubber's own output is safe canonical, hence a fixpoint. -/
theorem scrubber_idempotent_on_safe_canonical (p : ScrubParams) (hp : p.Valid) (p0 : Nat)
    (x : Nat → Nat) (h0 : p0 ≤ 255) (hq0 : p.Q ∣ p0) :
    ∀ t, out p p0 (fun t => out p p0 x (t + 1)) t = out p p0 x t := by
  have hext : ext p0 (fun t => out p p0 x (t + 1)) = out p p0 x := by
    funext t; cases t <;> rfl
  have hsafe : SafeCanonical p p0 (fun t => out p p0 x (t + 1)) :=
    ⟨fun t => by have := (scrubber_output_is_lattice_byte p hp p0 x h0 hq0 (t + 1)).1; omega,
     fun t => (scrubber_output_is_lattice_byte p hp p0 x h0 hq0 (t + 1)).2,
     by rw [hext]; exact scrubber_enforces_slew_and_reversal_bound p p0 x⟩
  intro t
  rw [scrubber_fixpoint_on_safe_canonical hp hsafe t, hext]

/-! ## §8. `#tooth` — a 15 Hz strobe and a 2-bit LSB key-exfiltration stream -/

/-- A 15 Hz full-swing strobe at 60 fps (period 4 frames). -/
def strobe15 (t : Nat) : Nat := if t % 4 < 2 then 0 else 252

/-- `#tooth`: the raw strobe is not photosafe (reversals at frames 5 and 7). -/
theorem tooth_raw_15hz_strobe_not_photosafe : ¬ RevSpaced wearable60.H (ext 0 strobe15) := by
  intro h
  have := h 5 7 (by decide) (by decide) (by decide)
  simp [wearable60] at this

/-- `#tooth`: the scrubber holds the second edge of the strobe (frame 7 stays dark). -/
theorem tooth_15hz_strobe_caught :
    revAt (out wearable60 0 strobe15) 5 = true ∧ revAt (out wearable60 0 strobe15) 7 = false ∧
      out wearable60 0 strobe15 7 = 0 := by
  decide

/-- Without the hold-off (`H = 1`), the slew clamp alone lets the strobe through. -/
def noHold : ScrubParams := ⟨4, 16, 1⟩

theorem tooth_hold_off_load_bearing : ¬ RevSpaced wearable60.H (out noHold 0 strobe15) := by
  intro h
  have := h 5 7 (by decide) (by decide) (by decide)
  simp [wearable60] at this

def coverBase (t : Nat) : Nat := 128 + 4 * (t % 8)
/-- Two bits per frame of a key byte, hidden in the two LSBs. -/
def keyBits (key t : Nat) : Nat := key / 4 ^ (t % 4) % 4
def stegoA (t : Nat) : Nat := coverBase t + keyBits 0xB4 t
def stegoB (t : Nat) : Nat := coverBase t + keyBits 0x1F t

theorem stego_twins_hi (t : Nat) : stegoA t < 256 ∧ stegoB t < 256 ∧ stegoA t / 4 = stegoB t / 4 := by
  have h1 : keyBits 0xB4 t < 4 := Nat.mod_lt _ (by decide)
  have h2 : keyBits 0x1F t < 4 := Nat.mod_lt _ (by decide)
  have h3 : t % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [stegoA, stegoB, coverBase]
  omega

/-- `#tooth`: the raw streams carry different key bits, the scrubbed streams are identical. -/
theorem tooth_lsb_keystream_killed :
    stegoA 0 ≠ stegoB 0 ∧ ∀ t, out wearable60 128 stegoA t = out wearable60 128 stegoB t := by
  refine ⟨by decide, fun t => ?_⟩
  exact congrArg PixState.prev (run_congr wearable60 128
    (fun t => quant_eq_of_hi (stego_twins_hi t).1 (stego_twins_hi t).2.1 (stego_twins_hi t).2.2) t)

/-- Without quantization (`Q = 1`) the key bits reach the wearer's retina. -/
def noQuant : ScrubParams := ⟨1, 16, 12⟩

theorem tooth_no_quant_leaks : out noQuant 128 stegoA 1 ≠ out noQuant 128 stegoB 1 := by
  decide

/-- Two channels, each monotone (zero reversals), stepping on alternate frames in opposite
directions: their sum flickers at 30 Hz. -/
def rampR (t : Nat) : Nat := 16 * ((t + 1) / 2)
def rampG (t : Nat) : Nat := 200 - 16 * (t / 2)

/-- `#tooth` / scope: **per-RGB-channel guarding does not bound luma reversals.** Each channel is
reversal-free over frames `0..9`, yet `R + G` reverses at frames 2, 3, 4, …; the photosafety
theorem binds the channel it is run on, so the deployed guard runs on the luma plane `Y'` of a
`Y'CbCr` surface (and on `Cb`, `Cr`), never on `R`, `G`, `B` separately. -/
theorem tooth_per_channel_rgb_misses_luma_flicker :
    (∀ i < 9, revAt rampR i = false ∧ revAt rampG i = false) ∧
      revAt (fun t => rampR t + rampG t) 2 = true ∧ revAt (fun t => rampR t + rampG t) 3 = true := by
  decide

/-! ## §9. Part B — `DuressChaffVolume`: fixed-geometry dual-root vault -/

section Vault
variable {N : Nat} {S : Type*} [AddCommGroup S] [Fintype S]

/-- The image under the ideal-XOF model: decoy slots are the duress root's sealed blocks;
sovereign slots are `seal + R i`; every other slot is the uniform `R i` (chaff). -/
def realImage (D Sov : Finset (Fin N)) (decoy sealS R : Fin N → S) : Fin N → S :=
  fun i => if i ∈ D then decoy i else if i ∈ Sov then sealS i + R i else R i

/-- The same image with no sovereign root at all: every non-decoy slot is chaff. -/
def chaffImage (D : Finset (Fin N)) (decoy U : Fin N → S) : Fin N → S :=
  fun i => if i ∈ D then decoy i else U i

def sovShift (D Sov : Finset (Fin N)) (sealS : Fin N → S) : (Fin N → S) ≃ (Fin N → S) :=
  Equiv.piCongrRight fun i => Equiv.addLeft (if i ∈ D then 0 else if i ∈ Sov then sealS i else 0)

omit [Fintype S] in
theorem realImage_eq_chaff_shift (D Sov : Finset (Fin N)) (decoy sealS R : Fin N → S) :
    realImage D Sov decoy sealS R = chaffImage D decoy (sovShift D Sov sealS R) := by
  funext i
  simp only [realImage, chaffImage, sovShift, Equiv.piCongrRight_apply, Equiv.coe_addLeft]
  by_cases hD : i ∈ D <;> by_cases hS : i ∈ Sov <;> simp [hD, hS]

/-- **TVD = 0.** For every distinguisher (it may hold the duress key, the salts and the decoy
plaintexts — all are fixed outside `A`) the acceptance count over the sovereign pads equals the
acceptance count over pure chaff. -/
theorem duress_adversary_cannot_distinguish_sovereign_from_chaff
    (D Sov : Finset (Fin N)) (decoy sealS : Fin N → S) (A : (Fin N → S) → Bool) :
    (univ.filter fun R => A (realImage D Sov decoy sealS R) = true).card =
      (univ.filter fun U => A (chaffImage D decoy U) = true).card :=
  Finset.card_equiv (sovShift D Sov sealS) (by intro R; simp [realImage_eq_chaff_shift])

/-- Pointwise-equal view distributions. -/
theorem duress_view_distribution_equal [DecidableEq S] (D Sov : Finset (Fin N)) (decoy sealS v : Fin N → S) :
    (univ.filter fun R => realImage D Sov decoy sealS R = v).card =
      (univ.filter fun U => chaffImage D decoy U = v).card := by
  simpa using duress_adversary_cannot_distinguish_sovereign_from_chaff D Sov decoy sealS
    (fun w => decide (w = v))

/-- Even the number of sovereign slots is hidden: any two sovereign populations look alike. -/
theorem sovereign_population_hidden (D Sov₁ Sov₂ : Finset (Fin N)) (decoy s₁ s₂ : Fin N → S)
    (A : (Fin N → S) → Bool) :
    (univ.filter fun R => A (realImage D Sov₁ decoy s₁ R) = true).card =
      (univ.filter fun R => A (realImage D Sov₂ decoy s₂ R) = true).card := by
  rw [duress_adversary_cannot_distinguish_sovereign_from_chaff,
    duress_adversary_cannot_distinguish_sovereign_from_chaff]

end Vault

/-! ## §10. The deployed slot construction and duress unlock -/

section Scheme
variable {K Salt B : Type*} [AddCommGroup B] [DecidableEq B]

/-- A slot is `(body, tag)` masked by the root's XOF pad (XOR in the deployed bytes). -/
structure SlotScheme (K Salt B : Type*) where
  xof : K → Salt → B × B
  mac : K → Salt → B → B

def SlotScheme.seal (sc : SlotScheme K Salt B) (k : K) (s : Salt) (m : B) : B × B :=
  (m, sc.mac k s m) + sc.xof k s

def SlotScheme.open_ (sc : SlotScheme K Salt B) (k : K) (s : Salt) (c : B × B) : Option B :=
  let q := c - sc.xof k s
  if sc.mac k s q.1 = q.2 then some q.1 else none

theorem SlotScheme.open_seal (sc : SlotScheme K Salt B) (k : K) (s : Salt) (m : B) :
    sc.open_ k s (sc.seal k s m) = some m := by
  simp [SlotScheme.open_, SlotScheme.seal]

/-- **Duress unlock is correct** whatever the sovereign population and pads: the duress root
opens every decoy slot to its decoy plaintext. -/
theorem duress_unlock_correct {N : Nat} (sc : SlotScheme K Salt B) (dk : K) (salt : Fin N → Salt)
    (D Sov : Finset (Fin N)) (mD : Fin N → B) (sealS R : Fin N → B × B) (i : Fin N) (hi : i ∈ D) :
    sc.open_ dk (salt i)
      (realImage D Sov (fun j => sc.seal dk (salt j) (mD j)) sealS R i) = some (mD i) := by
  simp only [realImage, hi, ↓reduceIte, SlotScheme.open_seal]

end Scheme

/-! ## §11. `#tooth` — variable geometry and root-unseparated (shared-salt) pads -/

/-- A variable-length slot table: only occupied slots are written. -/
def varImage {N : Nat} {S : Type*} [Add S] (D Sov : Finset (Fin N)) (decoy sealS R : Fin N → S) :
    List S :=
  ((List.finRange N).filter (fun i => decide (i ∈ D ∨ i ∈ Sov))).map
    (fun i => if i ∈ D then decoy i else sealS i + R i)

abbrev S2 := Fin 2 × Fin 2

def D2 : Finset (Fin 4) := {0, 1}

/-- `#tooth`: with a variable-length table, the length test has advantage 1 for every pad. -/
theorem tooth_variable_geometry_breaks (decoy sealS R : Fin 4 → S2) :
    decide (2 < (varImage D2 {2} decoy sealS R).length) = true ∧
      decide (2 < (varImage D2 ∅ decoy sealS R).length) = false := by
  simp only [varImage, List.length_map]
  decide

/-- Root-unseparated pad: derived from the (shared) salt alone, so the duress holder can strip it. -/
def sharedPad (s : Fin 2) : S2 := (s, s + 1)
/-- Sovereign plaintext carries a format header `1` in the first coordinate. -/
def sovPlain (m : Fin 2) : S2 := (1, m)
/-- The distinguisher: strip the shared pad, look for the header. -/
def headerTest (s : Fin 2) (c : S2) : Bool := decide ((c - sharedPad s).1 = 1)

/-- `#tooth`: with a shared-salt pad the sovereign slot is always flagged, chaff only half the
time (advantage `1/2`); with an independent pad the main theorem forces equal counts. -/
theorem tooth_shared_salt_kdf_breaks :
    (univ.filter fun _R : S2 => headerTest 0 (sovPlain 1 + sharedPad 0) = true).card = 4 ∧
      (univ.filter fun U : S2 => headerTest 0 U = true).card = 2 := by
  decide

/-! ## §12. Conformance vectors (mirrored byte-exactly by `prover/src/wetware_duress_guard.rs`) -/

/-- A safe canonical triangle (half-period 12, slope 16): passes unchanged. -/
def triangle (t : Nat) : Nat := let ph := (t + 1) % 24; 16 * (if ph ≤ 12 then ph else 24 - ph)
def chaotic (t : Nat) : Nat := (t * 37 + t * t * 11 + 5) % 256

def emitted (p : ScrubParams) (p0 : Nat) (x : Nat → Nat) (n : Nat) : List Nat :=
  (List.range n).map fun t => out p p0 x (t + 1)


/-- info: [0, 0, 252, 252, 0, 0, 252, 252, 0, 0, 252, 252, 0, 0, 252, 252, 0, 0, 252, 252, 0, 0, 252, 252, 0, 0, 252, 252, 0, 0, 252, 252, 0, 0, 252, 252, 0, 0, 252, 252, 0, 0, 252, 252, 0, 0, 252, 252] -/
#guard_msgs (whitespace := lax) in #eval (List.range 48).map strobe15
/-- info: [0, 0, 16, 32, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 32, 32, 32, 48, 64, 64, 64, 80, 96, 96, 96, 112, 128, 112, 96, 96, 96, 80, 64, 64, 64, 48, 32, 32, 32, 16, 0, 16, 32] -/
#guard_msgs (whitespace := lax) in #eval emitted wearable60 0 strobe15 48
/-- info: [128, 133, 139, 142, 144, 149, 155, 158, 128, 133, 139, 142, 144, 149, 155, 158, 128, 133, 139, 142, 144, 149, 155, 158, 128, 133, 139, 142, 144, 149, 155, 158] -/
#guard_msgs (whitespace := lax) in #eval (List.range 32).map stegoA
/-- info: [131, 135, 137, 140, 147, 151, 153, 156, 131, 135, 137, 140, 147, 151, 153, 156, 131, 135, 137, 140, 147, 151, 153, 156, 131, 135, 137, 140, 147, 151, 153, 156] -/
#guard_msgs (whitespace := lax) in #eval (List.range 32).map stegoB
/-- info: [128, 132, 136, 140, 144, 148, 152, 156, 140, 132, 132, 132, 132, 132, 132, 132, 128, 128, 128, 128, 144, 148, 152, 156, 156, 156, 156, 156, 156, 156, 156, 156] -/
#guard_msgs (whitespace := lax) in #eval emitted wearable60 128 stegoA 32
/-- info: [128, 132, 136, 140, 144, 148, 152, 156, 140, 132, 132, 132, 132, 132, 132, 132, 128, 128, 128, 128, 144, 148, 152, 156, 156, 156, 156, 156, 156, 156, 156, 156] -/
#guard_msgs (whitespace := lax) in #eval emitted wearable60 128 stegoB 32
/-- info: [16, 32, 48, 64, 80, 96, 112, 128, 144, 160, 176, 192, 176, 160, 144, 128, 112, 96, 80, 64, 48, 32, 16, 0, 16, 32, 48, 64, 80, 96, 112, 128, 144, 160, 176, 192, 176, 160, 144, 128, 112, 96, 80, 64, 48, 32, 16, 0] -/
#guard_msgs (whitespace := lax) in #eval (List.range 48).map triangle
/-- info: [16, 32, 48, 64, 80, 96, 112, 128, 144, 160, 176, 192, 176, 160, 144, 128, 112, 96, 80, 64, 48, 32, 16, 0, 16, 32, 48, 64, 80, 96, 112, 128, 144, 160, 176, 192, 176, 160, 144, 128, 112, 96, 80, 64, 48, 32, 16, 0] -/
#guard_msgs (whitespace := lax) in #eval emitted wearable60 0 triangle 48
/-- info: [5, 53, 123, 215, 73, 209, 111, 35, 237, 205, 195, 207, 241, 41, 119, 219, 85, 229, 139, 71, 25, 1, 255, 19, 61, 125, 211, 63, 193, 89, 7, 203, 165, 149, 155, 183, 233, 49, 143, 3, 141, 45, 227, 175, 145, 137, 151, 187] -/
#guard_msgs (whitespace := lax) in #eval (List.range 48).map chaotic
/-- info: [112, 96, 112, 128, 128, 144, 144, 144, 160, 176, 192, 204, 220, 220, 204, 204, 188, 188, 172, 156, 140, 124, 124, 108, 92, 92, 108, 108, 124, 124, 124, 140, 156, 156, 156, 172, 188, 188, 172, 156, 140, 124, 124, 124, 124, 124, 124, 124] -/
#guard_msgs (whitespace := lax) in #eval emitted wearable60 128 chaotic 48
/-- info: [112, 96, 112, 128, 128, 144, 144, 144, 160, 176, 192, 207, 223, 223, 207, 207, 191, 191, 175, 159, 143, 127, 127, 111, 95, 95, 111, 111, 127, 127, 127, 143, 159, 159, 159, 175, 191, 191, 175, 159, 143, 127, 127, 127, 127, 127, 127, 127] -/
#guard_msgs (whitespace := lax) in #eval emitted noQuant 128 chaotic 48
/-- info: [0, 24, 48, 72, 72, 96, 104, 80, 80, 80, 80, 80, 80, 56, 80, 104, 104, 128, 136, 136, 112, 88, 88, 64, 56, 56, 80, 80, 104, 104, 104, 128, 152, 144, 144, 144, 144, 120, 120, 96, 120, 120, 144, 168, 168, 168, 144, 144] -/
#guard_msgs (whitespace := lax) in #eval emitted ⟨8, 24, 6⟩ 0 chaotic 48
/-- info: [16667, 16667, 33334, 33334, 1000020] -/
#guard_msgs (whitespace := lax) in #eval [(16667, 0), (16667, 16666), (16667, 16667), (16667, 33333), (16667, 1000003)].map fun (P, τ) => snapRelease P τ
/-- info: [0, 0, 32752, 32768, 65520, 12288] -/
#guard_msgs (whitespace := lax) in #eval [(2, 0), (2, 3), (4, 32767), (4, 32768), (4, 65535), (8, 12345)].map fun (k, s) => quantAudio k s


/-! ## §13. Axiom pins -/

/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.dirOf_eq_flat_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirOf_eq_flat_iff
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.slewClamp_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms slewClamp_bounds
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.step_slew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_slew
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.step_rev_branch' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms step_rev_branch
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.run_dir_eq_odir' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_dir_eq_odir
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.since_le_after_rev' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms since_le_after_rev
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.scrubber_slew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scrubber_slew
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.scrubber_reversal_spacing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scrubber_reversal_spacing
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.scrubber_enforces_slew_and_reversal_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scrubber_enforces_slew_and_reversal_bound
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.revSpaced_window_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revSpaced_window_le_one
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.revSpaced_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revSpaced_count_le
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.wearable60_at_most_5_reversals_per_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wearable60_at_most_5_reversals_per_second
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.run_congr' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms run_congr
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.snapRelease_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms snapRelease_bounds
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.snapRelease_kills_jitter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms snapRelease_kills_jitter
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.scrubber_kills_subthreshold_stego' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scrubber_kills_subthreshold_stego
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.scrubber_zero_covert_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scrubber_zero_covert_capacity
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.scrubber_fixpoint_on_safe_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scrubber_fixpoint_on_safe_canonical
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.scrubber_output_is_lattice_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scrubber_output_is_lattice_byte
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.scrubber_idempotent_on_safe_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scrubber_idempotent_on_safe_canonical
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.tooth_raw_15hz_strobe_not_photosafe' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_raw_15hz_strobe_not_photosafe
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.tooth_15hz_strobe_caught' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms tooth_15hz_strobe_caught
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.tooth_hold_off_load_bearing' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_hold_off_load_bearing
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.tooth_lsb_keystream_killed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_lsb_keystream_killed
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.tooth_no_quant_leaks' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_no_quant_leaks
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.tooth_per_channel_rgb_misses_luma_flicker' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms tooth_per_channel_rgb_misses_luma_flicker
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.realImage_eq_chaff_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms realImage_eq_chaff_shift
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.duress_adversary_cannot_distinguish_sovereign_from_chaff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms duress_adversary_cannot_distinguish_sovereign_from_chaff
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.duress_view_distribution_equal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms duress_view_distribution_equal
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.sovereign_population_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sovereign_population_hidden
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.SlotScheme.open_seal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SlotScheme.open_seal
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.duress_unlock_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms duress_unlock_correct
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.tooth_variable_geometry_breaks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_variable_geometry_breaks
/-- info: 'Minidregg.Theory.WetwareSafetyAndDuress.tooth_shared_salt_kdf_breaks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_shared_salt_kdf_breaks

end Minidregg.Theory.WetwareSafetyAndDuress
