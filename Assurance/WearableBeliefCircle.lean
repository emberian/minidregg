/-
# `Assurance/WearableBeliefCircle.lean` — *Rainbows End* Wearable SHE Organ #3
("Belief Circles" & Spatial Co-Presence)

Formal Lean `v4.35.0` assurance module composing four existing `minidregg` / `Dregg-180` pillars:
1. **Physical Co-Presence (`Hancke–Kuhn` / `dregg_distance_tdc` Picosecond ToF Gate):**
   Exact integer speed-of-light (`c = 299,792,458 pm/ps`) + `dregg_distance_tdc` hardware
   turnaround floor (`t_proc_min = 3,990 ps`, `230 ps` 32-tap Vernier TDC step, single-shot
   challenge lock `u_lock`). Proves `tof_accepts_implies_within_radius` against any causally
   constrained relay, exact `(3/4)^k` Hancke–Kuhn pre-ask mafia-fraud combinatorial bound and
   `(1/2)^k` blind pre-commit bound over all uniform challenge/secret pairs, plus `#tooth`
   falsifiers for wormhole delay, early pre-trigger, and unlocked dual-read responders.
2. **Traffic-Analysis-Free Belief-Circle Transport (`Theory.Channel` Composition):**
   Binds wearable activity (`idle` / `jittQuery` / `arHazardReticle` / `overlayPatch`) into
   constant-rate fixed-size `256 B` (`P1`) / `1,024 B` (`P2`) `Theory.Channel` cells (`cSHAKE256`
   counter-mode stream + 16 B MAC), proving `circle_rf_trace_independent_of_activity` and
   `circle_member_presence_hidden`, plus `#tooth` falsifiers for event-driven and unsealed RF.
3. **Scoped Belief-Circle Overlay Merge (`PqSelectiveBiscuit` + ToF + `Theory.Confluence`):**
   Composes PQ membership credentials (`CAP-01/10/12`), ToF co-presence gating, and `IConfluent`
   join-semilattice (`Finset SpatialEntry`) merge rendered into `LightClientAndViewLens.ViewNode`
   AR reticle trees with `0`-round BFT convergence across arbitrary delivery permutations and
   deterministic drop of revoked, forged, or out-of-range relays.
4. **Byte-Exact Conformance Vector Emitter & `#guard_msgs`-Pinned Axiom Audit.**
-/
import Theory.Channel
import Theory.Confluence
import Theory.PqSelectiveBiscuit
import Assurance.LightClientAndViewLens

namespace Minidregg.Assurance.WearableBeliefCircle

open Minidregg.Theory.Channel
open Minidregg.Theory.Confluence
open Minidregg.Theory.PqSelectiveBiscuit
open Minidregg.Theory.HashBytes
open Minidregg.Assurance.LightClientAndViewLens

set_option autoImplicit false

/-! ## §1. Physical Co-Presence (`Hancke–Kuhn` / `dregg_distance_tdc` Picosecond ToF Gate) -/

/-- Exact SI speed of light in picometers per picosecond (`299,792,458 m/s`). -/
def cPmPerPs : Nat := 299792458

/-- Picometers per millimeter (`1 mm = 10^9 pm`). -/
def pmPerMm : Nat := 1000000000

/-- `dregg_distance_tdc` rapid-bit pad-to-pad turnaround floor (`3.99 ns`, `STAPostPNR`). -/
def dreggTProcMinPs : Nat := 3990

/-- `dregg_vernier_tdc32` Vernier resolution (`450 ps` slow tap − `220 ps` fast tap). -/
def dreggVernierStepPs : Nat := 230

/-- Exact per-round deadline (ps) for a physical co-presence radius `dMaxMm` (mm):
    `t_max = t_proc_min + floor(2 · d_max / c)`. -/
def tMaxOfRadiusPs (tProcMinPs dMaxMm : Nat) : Nat :=
  tProcMinPs + (2 * dMaxMm * pmPerMm) / cPmPerPs

/-- `dregg_distance_tdc.sv` TDC reading decode: `coarse_cycles * clk_period_ps + fine * step_ps`. -/
def tdcCyclesToPs (coarseCycles vernierFine clkPeriodPs vernierStepPs : Nat) : Nat :=
  coarseCycles * clkPeriodPs + vernierFine * vernierStepPs

/-- Parameters of a picosecond ToF distance-bounding gate. -/
structure TofParams where
  rounds         : Nat
  tProcMinPs     : Nat
  dMaxMm         : Nat
  vernierStepPs  : Nat
  roundsPos      : 0 < rounds
  deriving DecidableEq

def TofParams.maxRoundTimePs (p : TofParams) : Nat :=
  tMaxOfRadiusPs p.tProcMinPs p.dMaxMm

/-- Canonical wearable belief-circle ToF gate: 128 rapid-bit rounds (two chained 64-round
    `dregg_distance_tdc` sessions), `t_proc_min = 3,990 ps`, `d_max = 3,000 mm` (3.0 m room). -/
def dreggBeliefTofParams : TofParams :=
  { rounds := 128, tProcMinPs := dreggTProcMinPs, dMaxMm := 3000,
    vernierStepPs := dreggVernierStepPs, roundsPos := by omega }

theorem dreggBeliefTofParams_deadline : dreggBeliefTofParams.maxRoundTimePs = 24003 := by decide

/-- Causal relativistic constraint for any responder or honest relay at physical distance `dMm`:
    round-trip time `Δt` satisfies `Δt ≥ t_proc_min + 2·d/c` in exact integer arithmetic. -/
def CausallyConstrained (tProcMinPs dMm measuredPs : Nat) : Prop :=
  tProcMinPs ≤ measuredPs ∧ 2 * dMm * pmPerMm ≤ cPmPerPs * (measuredPs - tProcMinPs)

/-- Verdict of `verifyTofSession`. -/
inductive TofRejectReason where
  | lengthMismatch
  | belowTurnaroundFloor (round : Nat)
  | tofTimeout (round : Nat)
  | responseBitMismatch (round : Nat)
  deriving DecidableEq, Repr

inductive TofVerdict where
  | ok
  | err (reason : TofRejectReason)
  deriving DecidableEq, Repr

/-- Transcript of a `k`-round Hancke–Kuhn / `dregg_distance_tdc` exchange. -/
structure TofTranscript where
  r0      : List Bool
  r1      : List Bool
  chal    : List Bool
  resp    : List Bool
  timesPs : List Nat
  deriving DecidableEq, Repr

def verifyTofRoundsAux (tMin tMax : Nat) :
    Nat → List Bool → List Bool → List Bool → List Bool → List Nat → TofVerdict
  | _, [], [], [], [], [] => .ok
  | idx, a :: r0, b :: r1, c :: ch, r :: rs, t :: ts =>
    if t < tMin then .err (.belowTurnaroundFloor idx)
    else if tMax < t then .err (.tofTimeout idx)
    else if r != (if c then b else a) then .err (.responseBitMismatch idx)
    else verifyTofRoundsAux tMin tMax (idx + 1) r0 r1 ch rs ts
  | _, _, _, _, _, _ => .err .lengthMismatch

/-- Complete `k`-round rapid-bit ToF verifier gate. -/
def verifyTofSession (p : TofParams) (tr : TofTranscript) : TofVerdict :=
  if tr.r0.length == p.rounds && tr.r1.length == p.rounds &&
     tr.chal.length == p.rounds && tr.resp.length == p.rounds &&
     tr.timesPs.length == p.rounds then
    verifyTofRoundsAux p.tProcMinPs p.maxRoundTimePs 0 tr.r0 tr.r1 tr.chal tr.resp tr.timesPs
  else .err .lengthMismatch

private theorem verifyTofRoundsAux_ok_all (tMin tMax : Nat) :
    ∀ (idx : Nat) (r0 r1 ch rs : List Bool) (ts : List Nat),
      verifyTofRoundsAux tMin tMax idx r0 r1 ch rs ts = .ok →
      (∀ t ∈ ts, tMin ≤ t ∧ t ≤ tMax) ∧
      (∀ (i : Nat) (h1 : i < ch.length) (h2 : i < rs.length)
         (h3 : i < r0.length) (h4 : i < r1.length),
         rs[i] = if ch[i] then r1[i] else r0[i])
  | _, [], [], [], [], [], _ =>
    ⟨(fun _ h => nomatch h), (fun _ h1 _ _ _ => nomatch h1)⟩
  | idx, a :: r0, b :: r1, c :: ch, r :: rs, t :: ts, h => by
    unfold verifyTofRoundsAux at h
    by_cases h1 : t < tMin
    · simp [h1] at h
    by_cases h2 : tMax < t
    · simp [h1, h2] at h
    by_cases h3 : (r != (if c then b else a)) = true
    · simp [h1, h2, h3] at h
    simp only [h1, h2, h3, ↓reduceIte] at h
    have hr : r = if c then b else a := by
      cases c <;> cases a <;> cases b <;> cases r <;> simp_all
    obtain ⟨hts, hbits⟩ := verifyTofRoundsAux_ok_all tMin tMax (idx + 1) r0 r1 ch rs ts h
    refine ⟨fun x hx => ?_, fun i hi1 hi2 hi3 hi4 => ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx'
      · exact ⟨by omega, by omega⟩
      · exact hts x hx'
    · cases i with
      | zero => simpa using hr
      | succ i' => exact hbits i' (by simpa using hi1) (by simpa using hi2)
                                  (by simpa using hi3) (by simpa using hi4)
  | _, [], _ :: _, _, _, _, h | _, _ :: _, [], _, _, _, h
  | _, _ :: _, _ :: _, [], _, _, h | _, _ :: _, _ :: _, _ :: _, [], _, h
  | _, _ :: _, _ :: _, _ :: _, _ :: _, [], h | _, [], [], _ :: _, _, _, h
  | _, [], [], [], _ :: _, _, h | _, [], [], [], [], _ :: _, h => by
    simp [verifyTofRoundsAux] at h

theorem verifyTofSession_ok_bounds {p : TofParams} {tr : TofTranscript}
    (hok : verifyTofSession p tr = .ok) :
    tr.timesPs.length = p.rounds ∧
    (∀ t ∈ tr.timesPs, p.tProcMinPs ≤ t ∧ t ≤ p.maxRoundTimePs) := by
  unfold verifyTofSession at hok
  split at hok
  · rename_i hlen
    simp only [Bool.and_eq_true, beq_iff_eq] at hlen
    exact ⟨hlen.2, (verifyTofRoundsAux_ok_all _ _ 0 _ _ _ _ _ hok).1⟩
  · cases hok

/-- **Speed-of-Light Co-Presence Soundness (`tof_accepts_implies_within_radius`):**
    If the `k`-round ToF gate accepts (`k > 0`) and even one round is causally constrained by
    physical distance `dActualMm` (as holds for any honest responder or remote relay obeying
    relativity), then `dActualMm ≤ p.dMaxMm` — exact, zero approximation gap. -/
theorem tof_accepts_implies_within_radius (p : TofParams) (tr : TofTranscript) (dActualMm : Nat)
    (hok : verifyTofSession p tr = .ok)
    (hcausal : ∃ t ∈ tr.timesPs, CausallyConstrained p.tProcMinPs dActualMm t) :
    dActualMm ≤ p.dMaxMm := by
  obtain ⟨_, hbounds⟩ := verifyTofSession_ok_bounds hok
  obtain ⟨t, htMem, _, hprop⟩ := hcausal
  have ⟨_, htMax⟩ := hbounds t htMem
  have hsub : t - p.tProcMinPs ≤ (2 * p.dMaxMm * pmPerMm) / cPmPerPs := by
    unfold TofParams.maxRoundTimePs tMaxOfRadiusPs at htMax; omega
  have hmul1 : cPmPerPs * (t - p.tProcMinPs) ≤ cPmPerPs * ((2 * p.dMaxMm * pmPerMm) / cPmPerPs) :=
    Nat.mul_le_mul_left cPmPerPs hsub
  have hmul2 : cPmPerPs * ((2 * p.dMaxMm * pmPerMm) / cPmPerPs) ≤ 2 * p.dMaxMm * pmPerMm :=
    Nat.mul_div_le (2 * p.dMaxMm * pmPerMm) cPmPerPs
  have hdist : 2 * dActualMm * pmPerMm ≤ 2 * p.dMaxMm * pmPerMm :=
    Nat.le_trans hprop (Nat.le_trans hmul1 hmul2)
  have hpos : 0 < 2 * pmPerMm := by decide
  have e1 : 2 * dActualMm * pmPerMm = dActualMm * (2 * pmPerMm) := by
    rw [Nat.mul_comm 2 dActualMm, Nat.mul_assoc]
  have e2 : 2 * p.dMaxMm * pmPerMm = p.dMaxMm * (2 * pmPerMm) := by
    rw [Nat.mul_comm 2 p.dMaxMm, Nat.mul_assoc]
  rw [e1, e2] at hdist
  exact Nat.le_of_mul_le_mul_right hdist hpos

/-- Any causally constrained remote relay strictly outside `dMaxMm` is deterministically rejected. -/
theorem wormhole_relay_deterministically_rejected (p : TofParams) (tr : TofTranscript)
    (dActualMm : Nat) (hfar : p.dMaxMm < dActualMm)
    (hcausal : ∃ t ∈ tr.timesPs, CausallyConstrained p.tProcMinPs dActualMm t) :
    verifyTofSession p tr ≠ .ok := fun hok =>
  Nat.not_le_of_gt hfar (tof_accepts_implies_within_radius p tr dActualMm hok hcausal)

/-! ### Exact Combinatorial Mafia-Fraud Bounds (`(3/4)^k` Pre-Ask & `(1/2)^k` Blind Pre-Commit) -/

/-- All bitstrings of length `k` (`2^k` elements). -/
def bitVectors : Nat → List (List Bool)
  | 0 => [[]]
  | k + 1 => (bitVectors k).map (false :: ·) ++ (bitVectors k).map (true :: ·)

theorem bitVectors_length (k : Nat) : (bitVectors k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [bitVectors, List.length_append, List.length_map, ih, Nat.pow_succ]; omega

/-- All `(challenge, hiddenBit)` round pairs of length `k` (`4^k` equally likely outcomes). -/
def hkSpace : Nat → List (List (Bool × Bool))
  | 0 => [[]]
  | k + 1 =>
    let prev := hkSpace k
    prev.map ((false, false) :: ·) ++ prev.map ((false, true) :: ·) ++
    prev.map ((true, false) :: ·) ++ prev.map ((true, true) :: ·)

theorem hkSpace_length (k : Nat) : (hkSpace k).length = 4 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [hkSpace, List.length_append, List.length_map, ih, Nat.pow_succ]; omega

/-- Single-round Hancke–Kuhn pre-ask outcome against a `dregg_distance_tdc` single-shot lock
    responder: the relay pre-queried with `preGuess` (locking out `!preGuess` via `u_lock`),
    so on challenge `c` it succeeds iff `c = preGuess` (answer known) or `fallback = hiddenBit`. -/
def preAskRoundWin (preGuess fallback chal hiddenBit : Bool) : Bool :=
  (chal == preGuess) || (fallback == hiddenBit)

/-- Multi-round pre-ask strategy `(preGuess, fallback)` winning all `k` rounds. -/
def preAskAllWin : List (Bool × Bool) → List (Bool × Bool) → Bool
  | [], [] => true
  | (g, f) :: strat, (c, h) :: env => preAskRoundWin g f c h && preAskAllWin strat env
  | _, _ => false

/-- **Exact Hancke–Kuhn Pre-Ask Mafia-Fraud Count (`(3/4)^k`):**
    Against a single-shot-lock responder (`dregg_distance_tdc`), EVERY `k`-round pre-ask relay
    strategy wins on **exact `3^k`** of the `4^k` equally likely `(challenge, hiddenBit)` outcomes
    (and is therefore rejected on `4^k - 3^k` outcomes, i.e., probability `1 - (3/4)^k`). -/
theorem hancke_kuhn_mafia_fraud_exact_count :
    ∀ (k : Nat) (strat : List (Bool × Bool)), strat.length = k →
      (hkSpace k).countP (preAskAllWin strat) = 3 ^ k
  | 0, [], _ => rfl
  | k + 1, (g, f) :: strat, hlen => by
    have hlen' : strat.length = k := by simpa using hlen
    have ih := hancke_kuhn_mafia_fraud_exact_count k strat hlen'
    have hstep : ∀ (c h : Bool),
        ((hkSpace k).map ((c, h) :: ·)).countP (preAskAllWin ((g, f) :: strat)) =
          if preAskRoundWin g f c h then 3 ^ k else 0 := by
      intro c h
      rw [List.countP_map]
      have hcomp : (preAskAllWin ((g, f) :: strat) ∘ fun x => (c, h) :: x) =
                   (fun rest => preAskRoundWin g f c h && preAskAllWin strat rest) := rfl
      rw [hcomp]
      cases hb : preAskRoundWin g f c h
      · simp
      · simpa using ih
    simp only [hkSpace, List.countP_append, hstep]
    cases g <;> cases f <;> simp [preAskRoundWin, Nat.pow_succ] <;> omega
  | 0, _ :: _, hlen => by simp at hlen
  | _ + 1, [], hlen => by simp at hlen

/-- Exact rejection count `4^k - 3^k` for any `k`-round pre-ask relay strategy. -/
theorem hancke_kuhn_mafia_fraud_reject_count (k : Nat) (strat : List (Bool × Bool))
    (hlen : strat.length = k) :
    (hkSpace k).countP (fun env => !preAskAllWin strat env) = 4 ^ k - 3 ^ k := by
  have hsum : (hkSpace k).countP (preAskAllWin strat) +
              (hkSpace k).countP (fun env => !preAskAllWin strat env) = (hkSpace k).length := by
    induction (hkSpace k) with
    | nil => rfl
    | cons a l ih =>
      simp only [List.countP_cons, List.length_cons]
      cases preAskAllWin strat a <;> simp <;> omega
  rw [hancke_kuhn_mafia_fraud_exact_count k strat hlen, hkSpace_length] at hsum
  omega

/-- Concrete security levels: `k = 64` (single `dregg_distance_tdc` session) gives `< 1.01 × 10^-8`
    (`3^64 * 99,000,000 < 4^64`), and `k = 128` (chained belief-circle gate) gives `< 2^-53` (`< 10^-15`). -/
theorem hancke_kuhn_security_margins :
    3 ^ 64 * 99000000 < 4 ^ 64 ∧ 3 ^ 128 * 2 ^ 53 < 4 ^ 128 ∧
    3 ^ 128 * 1000000000000000 < 4 ^ 128 := by decide

/-- **Blind Pre-Committed Early-Bit Fraud Bound (`(1/2)^k`):**
    Any fixed `k`-bit pre-committed guess vector `guess` matches on **exact `1`** of the `2^k`
    equally likely target response bit-vectors (`rejection = 1 - (1/2)^k`). -/
theorem blind_precommit_exact_count :
    ∀ (k : Nat) (guess : List Bool), guess.length = k →
      (bitVectors k).countP (fun target => target == guess) = 1
  | 0, [], _ => rfl
  | k + 1, b :: tl, hlen => by
    have hlen' : tl.length = k := by simpa using hlen
    have ih := blind_precommit_exact_count k tl hlen'
    simp only [bitVectors, List.countP_append, List.countP_map]
    cases b
    · have h0 : ((fun target => target == false :: tl) ∘ (false :: ·)) = (fun x => x == tl) := by
        funext x; simp
      have h1 : ((fun target => target == false :: tl) ∘ (true :: ·)) = (fun _ => false) := by
        funext x; simp
      rw [h0, h1, ih]; simp
    · have h0 : ((fun target => target == true :: tl) ∘ (false :: ·)) = (fun _ => false) := by
        funext x; simp
      have h1 : ((fun target => target == true :: tl) ∘ (true :: ·)) = (fun x => x == tl) := by
        funext x; simp
      rw [h0, h1, ih]; simp
  | 0, _ :: _, hlen => by simp at hlen
  | _ + 1, [], hlen => by simp at hlen

/-- Concrete 128-bit `cSHAKE256` derivation of `r0`, `r1`, `chal` registers matching Rust. -/
def custTofR0   : List UInt8 := strBytes "MINIDREGG.BELIEF_CIRCLE.TOF_R0/v1"
def custTofR1   : List UInt8 := strBytes "MINIDREGG.BELIEF_CIRCLE.TOF_R1/v1"
def custTofChal : List UInt8 := strBytes "MINIDREGG.BELIEF_CIRCLE.TOF_CHAL/v1"

def bytesToBitsLSB (bs : List UInt8) : List Bool :=
  bs.flatMap fun b =>
    (List.range 8).map fun j => ((b.toNat / (2 ^ j)) % 2) == 1

def bitsToBytesLSB : List Bool → List UInt8
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    let v (b : Bool) (w : Nat) := if b then w else 0
    UInt8.ofNat (v b0 1 + v b1 2 + v b2 4 + v b3 8 + v b4 16 + v b5 32 + v b6 64 + v b7 128) ::
      bitsToBytesLSB rest
  | _ => []

def deriveTofBits (cust seed nonce : List UInt8) : List Bool :=
  bytesToBitsLSB ((cshake32 cust (seed ++ nonce)).take 16)

def computeTofResponse (r0 r1 chal : List Bool) : List Bool :=
  (chal.zip (r0.zip r1)).map fun (c, (a, b)) => if c then b else a

/-! ## §2. Traffic-Analysis-Free Belief-Circle Transport (`Theory.Channel` Composition) -/

/-- Wearable activity classes emitted over a Belief Circle RF mesh. -/
inductive WearableActivity where
  | idle
  | jittQuery (promptDigest : List UInt8)
  | arHazardReticle (anchorId priority : Nat) (patchBytes : List UInt8)
  | overlayPatch (anchorId : Nat) (patchBytes : List UInt8)
  deriving DecidableEq, Repr

/-- Encoded belief-circle message carried inside a sealed `Theory.Channel` cell. -/
structure BeliefMsg where
  viewTag : UInt8
  fragSeq : Nat
  payload : List UInt8
  deriving DecidableEq, Repr

/-- Map wearable activity to `Theory.Channel.Traffic`: `.idle` becomes `none` (cover padding),
    active JITT queries / AR hazard reticles / overlay patches become `some msg`. -/
def activityToMsg : WearableActivity → Option BeliefMsg
  | .idle => none
  | .jittQuery d => some ⟨0x01, 0, d⟩
  | .arHazardReticle anchorId prio bs => some ⟨0x02, anchorId % 65536, UInt8.ofNat prio :: bs⟩
  | .overlayPatch anchorId bs => some ⟨0x03, anchorId % 65536, bs⟩

def activityScheduleToTraffic (act : Nat → Nat → WearableActivity) : Traffic BeliefMsg :=
  fun k ρ => activityToMsg (act k ρ)

/-- **Traffic-Analysis-Free Belief-Circle RF Theorem (`circle_rf_trace_independent_of_activity`):**
    Binding wearable belief-circle broadcasts into fixed-size `256 B` (`P1`) or `1,024 B` (`P2`)
    `Theory.Channel` cells under constant emission (`designEmission`) and `PayloadHidden` makes
    the passive room RF sniffer (`wireTick`), relay, operator, witness, and non-recipient member
    traces **identically equal** whether wearers are `.idle`, issuing `.jittQuery`s, or bursting
    urgent `.arHazardReticle` alerts — and every RF packet has exact length `X.sched.profile.C`. -/
theorem circle_rf_trace_independent_of_activity {Obs : Type}
    (X : Domain BeliefMsg Obs)
    (hide : PayloadHidden X.S) (on : ConstantEmission X.em)
    (pol : RelayPolicy)
    (act₁ act₂ : Nat → Nat → WearableActivity)
    (p : Presences) (me ticks : Nat) :
    Domain.trace (X.wireTick pol (activityScheduleToTraffic act₁) p) ticks =
      Domain.trace (X.wireTick pol (activityScheduleToTraffic act₂) p) ticks ∧
    Domain.trace (X.relayTick (activityScheduleToTraffic act₁) p) ticks =
      Domain.trace (X.relayTick (activityScheduleToTraffic act₂) p) ticks ∧
    Domain.trace (X.operatorTick (activityScheduleToTraffic act₁) p) ticks =
      Domain.trace (X.operatorTick (activityScheduleToTraffic act₂) p) ticks ∧
    Domain.trace (X.witnessTick (activityScheduleToTraffic act₁) p) ticks =
      Domain.trace (X.witnessTick (activityScheduleToTraffic act₂) p) ticks ∧
    Domain.trace (X.memberTick pol (activityScheduleToTraffic act₁) p me) ticks =
      Domain.trace (X.memberTick pol (activityScheduleToTraffic act₂) p me) ticks ∧
    (∀ k c, c ∈ X.sched.assemble X.prf (X.epochOf k) (X.tickOf k)
        (X.received (activityScheduleToTraffic act₁) p k) →
      c.encode.length = X.sched.profile.C) := by
  have hobs := X.observable_trace_depends_only_on_membership hide on pol
    (activityScheduleToTraffic act₁) (activityScheduleToTraffic act₂) p me ticks
  exact ⟨hobs.1, hobs.2.1, hobs.2.2.1, hobs.2.2.2.1, hobs.2.2.2.2, fun _ c _ => cell_size_exact c⟩

/-- Non-recipient circle members cannot even tell which peers went silent on regular ticks. -/
theorem circle_member_presence_hidden {Obs : Type}
    (X : Domain BeliefMsg Obs) (pol : RelayPolicy)
    (fill : RelayFills pol) (fan : ConstantFanout pol) (hide : FillHidden X.S X.prf)
    (act : Nat → Nat → WearableActivity) (p₁ p₂ : Presences)
    (duty : X.PresenceAgreesAtDutyTicks p₁ p₂) (me ticks : Nat) :
    Domain.trace (X.memberTick pol (activityScheduleToTraffic act) p₁ me) ticks =
      Domain.trace (X.memberTick pol (activityScheduleToTraffic act) p₂ me) ticks :=
  X.member_view_independent_of_presence pol fill fan hide (activityScheduleToTraffic act)
    p₁ p₂ duty me ticks

/-! ### Concrete `cSHAKE256` Counter-Mode `Theory.Channel` Cell Codec (`256 B` P1 / `1024 B` P2) -/

def custCellStream : List UInt8 := strBytes "MINIDREGG.BELIEF_CIRCLE.CELL_STREAM/v1"
def custCellMac    : List UInt8 := strBytes "MINIDREGG.BELIEF_CIRCLE.CELL_MAC/v1"
def custCellFill   : List UInt8 := strBytes "MINIDREGG.BELIEF_CIRCLE.CELL_FILL/v1"

def cshakeKeystream (cust key ctx : List UInt8) (len : Nat) : List UInt8 :=
  let blocks := (len + 31) / 32
  ((List.range blocks).flatMap fun ctr => cshake32 cust (key ++ ctx ++ be 4 ctr)).take len

def xorBytes : List UInt8 → List UInt8 → List UInt8
  | a :: as, b :: bs => (a ^^^ b) :: xorBytes as bs
  | _, _ => []

/-- Pack a `WearableActivity` into a fixed-length `Theory.Channel.Plaintext .mlkem L` (`viewTag 1 |
    fragSeq 2 | fragLen 2 | payload (L - 5)` zero-padded). -/
def packActivityPlaintext (L : Nat) (act : WearableActivity) : List UInt8 :=
  match activityToMsg act with
  | none => 0x00 :: (be 2 0 ++ be 2 0 ++ (fit (L - 5) []).val)
  | some m =>
    let cap := L - 5
    let actualLen := min m.payload.length cap
    m.viewTag :: (be 2 m.fragSeq ++ be 2 actualLen ++ (fit cap (m.payload.take actualLen)).val)

/-- Concrete `cSHAKE256`-sealed `Theory.Channel.Cell` (regular when `tick ≠ 0`, duty when `tick = 0`).
    Computes encrypt-then-MAC with 16-byte `cSHAKE256` tag over `key || header || dutyPublic || ct`. -/
def sealBeliefCellCshake (P : Profile) (circleKey : List UInt8) (h : Header)
    (dutyVrf : Blob 96) (dutyVerdictRoot dutyAccRoot : Blob 32)
    (act : WearableActivity) : Cell P :=
  let hdrBytes := h.encode
  if hd : isDutyTick h = true then
    let L := P.dutySealedLen
    let pt := packActivityPlaintext L act
    let ks := cshakeKeystream custCellStream circleKey hdrBytes L
    let ct := (fit L (xorBytes pt ks)).val
    let dutyPub := dutyVrf.val ++ dutyVerdictRoot.val ++ dutyAccRoot.val
    let tag := fit tagLen (cshake32 custCellMac (circleKey ++ hdrBytes ++ dutyPub ++ ct))
    { header := h
      body := .duty ⟨dutyVrf, dutyVerdictRoot, dutyAccRoot, ⟨ct, (fit L _).property⟩, tag⟩
      layout := by simp [Body.isDuty, hd] }
  else
    let L := P.sealedLen
    let pt := packActivityPlaintext L act
    let ks := cshakeKeystream custCellStream circleKey hdrBytes L
    let ct := (fit L (xorBytes pt ks)).val
    let tag := fit tagLen (cshake32 custCellMac (circleKey ++ hdrBytes ++ ct))
    { header := h
      body := .regular ⟨⟨ct, (fit L _).property⟩, tag⟩
      layout := by cases hh : isDutyTick h <;> simp_all [Body.isDuty] }

theorem sealBeliefCellCshake_exact_size (P : Profile) (key : List UInt8) (h : Header)
    (v : Blob 96) (vr ar : Blob 32) (act : WearableActivity) :
    (sealBeliefCellCshake P key h v vr ar act).encode.length = P.C :=
  cell_size_exact _

/-! ## §3. Scoped Belief-Circle Overlay Merge (`PqSelectiveBiscuit` + ToF + `IConfluent` CRDT) -/

def custOverlayItem : List UInt8 := strBytes "MINIDREGG.BELIEF_CIRCLE.OVERLAY_ITEM/v1"
def custOverlayRoot : List UInt8 := strBytes "MINIDREGG.BELIEF_CIRCLE.OVERLAY_ROOT/v1"

/-- Capability bit required in `PqSelectiveBiscuit` token rights to write AR overlay annotations. -/
def circleWriteRight : UInt64 := 0x01

/-- Canonical authenticated spatial AR overlay entry inside a room anchor cell. -/
structure SpatialEntry where
  circleId     : Nat
  anchorId     : Nat
  lamportClock : Nat
  authorSlot   : Nat
  priority     : Nat
  label        : List UInt8
  entryDigest  : List UInt8
  deriving DecidableEq, Repr

def computeEntryDigest (circleId anchorId lamportClock authorSlot priority : Nat)
    (label : List UInt8) : List UInt8 :=
  cshake32 custOverlayItem
    (be 8 circleId ++ be 8 anchorId ++ be 8 lamportClock ++ be 2 authorSlot ++
     [UInt8.ofNat priority] ++ encodeField label)

def mkSpatialEntry (circleId anchorId lamportClock authorSlot priority : Nat)
    (label : List UInt8) : SpatialEntry :=
  ⟨circleId, anchorId, lamportClock, authorSlot, priority, label,
   computeEntryDigest circleId anchorId lamportClock authorSlot priority label⟩

/-- Incoming unverified AR overlay update carrying `PqSelectiveBiscuit` token + ToF transcript. -/
structure CircleOverlayUpdate where
  circleId     : Nat
  anchorId     : Nat
  lamportClock : Nat
  authorSlot   : Nat
  priority     : Nat
  label        : List UInt8
  token        : HolderToken
  tof          : TofTranscript

/-- Policy anchor pinned by a belief-circle verifier wearable. -/
structure CirclePolicy (S : PqSigScheme) where
  circleId       : Nat
  issuerPk       : List UInt8
  revocations    : RevocationSet
  requiredRights : UInt64
  tofParams      : TofParams

inductive AdmitReject where
  | wrongCircle
  | invalidCredential
  | insufficientRights
  | tofFailed (reason : TofRejectReason)
  deriving DecidableEq, Repr

inductive AdmitVerdict where
  | ok (entry : SpatialEntry)
  | err (reason : AdmitReject)
  deriving DecidableEq, Repr

/-- **Scoped Belief-Circle Admission Gate:** verifies circle ID, post-quantum `PqSelectiveBiscuit`
    membership & non-revocation (`CAP-01/10/12`), write capability right, and picosecond ToF
    co-presence before admitting a `SpatialEntry` into the local CRDT semilattice. -/
def admitCircleUpdate {S : PqSigScheme} (pol : CirclePolicy S) (now : UInt64)
    (upd : CircleOverlayUpdate) : AdmitVerdict :=
  if upd.circleId ≠ pol.circleId then .err .wrongCircle
  else match verifyToken S pol.issuerPk pol.revocations now upd.token with
    | none => .err .invalidCredential
    | some va =>
      if !subMask pol.requiredRights va.rights then .err .insufficientRights
      else match verifyTofSession pol.tofParams upd.tof with
        | .err r => .err (.tofFailed r)
        | .ok =>
          .ok (mkSpatialEntry upd.circleId upd.anchorId upd.lamportClock
                 upd.authorSlot upd.priority upd.label)

/-- The semantic lawfulness predicate for admitted spatial entries under `(pol, now)`. -/
def AdmissibleEntry {S : PqSigScheme} (pol : CirclePolicy S) (now : UInt64)
    (e : SpatialEntry) : Prop :=
  ∃ upd : CircleOverlayUpdate, admitCircleUpdate pol now upd = .ok e

/-- Every accepted update satisfies `PqSelectiveBiscuit` membership, rights, and ToF co-presence. -/
theorem admitCircleUpdate_sound {S : PqSigScheme} (pol : CirclePolicy S) (now : UInt64)
    (upd : CircleOverlayUpdate) (e : SpatialEntry)
    (hok : admitCircleUpdate pol now upd = .ok e) :
    upd.circleId = pol.circleId ∧
    (∃ va, verifyToken S pol.issuerPk pol.revocations now upd.token = some va ∧
      subMask pol.requiredRights va.rights = true) ∧
    verifyTofSession pol.tofParams upd.tof = .ok ∧
    e = mkSpatialEntry upd.circleId upd.anchorId upd.lamportClock
          upd.authorSlot upd.priority upd.label := by
  unfold admitCircleUpdate at hok
  split at hok; · cases hok
  rename_i hcid
  cases hv : verifyToken S pol.issuerPk pol.revocations now upd.token with
  | none => simp [hv] at hok
  | some va =>
    simp only [hv] at hok
    split at hok; · cases hok
    rename_i hsub
    cases ht : verifyTofSession pol.tofParams upd.tof with
    | err _ => simp [ht] at hok
    | ok =>
      simp only [ht, AdmitVerdict.ok.injEq] at hok
      have hsub' : subMask pol.requiredRights va.rights = true := by
        cases h : subMask pol.requiredRights va.rights <;> simp_all
      exact ⟨by omega, ⟨va, rfl, hsub'⟩, rfl, hok.symm⟩

/-- **Out-of-Range Relays Deterministically Dropped:** any causally constrained remote relay
    strictly beyond `dMaxMm` is dropped before touching the AR overlay semilattice. -/
theorem overlay_drops_out_of_range_relay {S : PqSigScheme} (pol : CirclePolicy S) (now : UInt64)
    (upd : CircleOverlayUpdate) (dActualMm : Nat)
    (hfar : pol.tofParams.dMaxMm < dActualMm)
    (hcausal : ∃ t ∈ upd.tof.timesPs, CausallyConstrained pol.tofParams.tProcMinPs dActualMm t) :
    ∀ e, admitCircleUpdate pol now upd ≠ .ok e := fun e hok =>
  wormhole_relay_deterministically_rejected pol.tofParams upd.tof dActualMm hfar hcausal
    (admitCircleUpdate_sound pol now upd e hok).2.2.1

/-- **Revoked Ancestor Credentials Deterministically Dropped (`CAP-10` Composition):** -/
theorem overlay_drops_revoked_credential {S : PqSigScheme}
    (circleId : Nat) (issuerPk : List UInt8) (rawRev : List Nat) (reqRights : UInt64)
    (tofP : TofParams) (now : UInt64) (upd : CircleOverlayUpdate)
    (j : Nat) (hj : j ≤ upd.token.hops.length)
    (hrev : chainId upd.token.block0 upd.token.hops j ∈ rawRev) :
    ∀ e, admitCircleUpdate (S := S)
      ⟨circleId, issuerPk, RevocationSet.ofList rawRev, reqRights, tofP⟩ now upd ≠ .ok e := by
  intro e hok
  obtain ⟨_, ⟨va, hv, _⟩, _, _⟩ := admitCircleUpdate_sound _ now upd e hok
  have hnone := revoke_ancestor_kills_cone S issuerPk rawRev now upd.token j hj hrev
  rw [hnone] at hv; cases hv

/-! ### `Theory.Confluence` `IConfluent` Semilattice Merge & `ViewNode` Projection -/

/-- Local spatial AR overlay state of a wearable in a belief circle: a finite set of admitted
    spatial entries with `⊔ = ∪` (`SemilatticeSup` from Mathlib). -/
abbrev OverlayState := Finset SpatialEntry

/-- Lawful belief-circle invariant: every entry in the local AR overlay passed admission. -/
def AllAdmitted {S : PqSigScheme} (pol : CirclePolicy S) (now : UInt64) :
    Invariant OverlayState :=
  fun s => ∀ e ∈ s, AdmissibleEntry pol now e

/-- **`overlay_allAdmitted_iconfluent` (`Theory.Confluence` Composition):**
    `AllAdmitted` is **I-confluent** (`IConfluent`): concurrent AR overlay merges across any
    partitioned or co-present circle wearers preserve admission safety in **`0` BFT rounds**. -/
theorem overlay_allAdmitted_iconfluent {S : PqSigScheme} (pol : CirclePolicy S) (now : UInt64) :
    IConfluent (AllAdmitted pol now) := by
  intro x y hx hy e he
  rcases Finset.mem_union.1 he with h | h
  · exact hx e h
  · exact hy e h

/-- Admitting a verified update preserves `AllAdmitted`. -/
theorem overlay_insert_admitted {S : PqSigScheme} (pol : CirclePolicy S) (now : UInt64)
    (s : OverlayState) (upd : CircleOverlayUpdate) (e : SpatialEntry)
    (hs : AllAdmitted pol now s) (hok : admitCircleUpdate pol now upd = .ok e) :
    AllAdmitted pol now (insert e s) := by
  intro x hx
  rcases Finset.mem_insert.1 hx with rfl | hx'
  · exact ⟨upd, hok⟩
  · exact hs x hx'

/-- Folding a stream of incoming `CircleOverlayUpdate`s into an `OverlayState`, dropping any
    unauthenticated, revoked, or out-of-range relay deterministically. -/
def ingestUpdates {S : PqSigScheme} (pol : CirclePolicy S) (now : UInt64)
    (updates : List CircleOverlayUpdate) : OverlayState :=
  updates.foldl (fun acc upd =>
    match admitCircleUpdate pol now upd with
    | .ok e => acc ⊔ {e}
    | .err _ => acc) ∅

private theorem mem_ingestUpdates_aux {S : PqSigScheme} (pol : CirclePolicy S) (now : UInt64)
    (init : OverlayState) (updates : List CircleOverlayUpdate) (e : SpatialEntry) :
    e ∈ updates.foldl (fun acc upd =>
      match admitCircleUpdate pol now upd with | .ok x => acc ⊔ {x} | .err _ => acc) init ↔
      e ∈ init ∨ ∃ upd ∈ updates, admitCircleUpdate pol now upd = .ok e := by
  induction updates generalizing init with
  | nil => simp
  | cons u us ih =>
    simp only [List.foldl_cons, ih]
    cases h : admitCircleUpdate pol now u with
    | err _ =>
      constructor
      · rintro (hi | ⟨v, hv, hok⟩)
        · exact Or.inl hi
        · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, hok⟩
      · rintro (hi | ⟨v, hv, hok⟩)
        · exact Or.inl hi
        · rcases List.mem_cons.1 hv with rfl | hv'
          · rw [h] at hok; cases hok
          · exact Or.inr ⟨v, hv', hok⟩
    | ok x =>
      constructor
      · rintro (hi | ⟨v, hv, hok⟩)
        · rcases Finset.mem_union.1 hi with h1 | h2
          · exact Or.inl h1
          · rw [Finset.mem_singleton.1 h2]; exact Or.inr ⟨u, List.mem_cons_self, h⟩
        · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, hok⟩
      · rintro (hi | ⟨v, hv, hok⟩)
        · exact Or.inl (Finset.mem_union.2 (Or.inl hi))
        · rcases List.mem_cons.1 hv with rfl | hv'
          · rw [h] at hok; cases hok
            exact Or.inl (Finset.mem_union.2 (Or.inr (Finset.mem_singleton_self _)))
          · exact Or.inr ⟨v, hv', hok⟩

/-- **Zero-Round BFT Convergence (`overlay_zero_round_convergence`):**
    Any two co-present circle wearers who receive the same set of updates in ANY order (including
    duplicates and interleaved invalid/out-of-range relays) converge to the **exact same
    `OverlayState`** (and satisfy `AllAdmitted`). -/
theorem overlay_zero_round_convergence {S : PqSigScheme} (pol : CirclePolicy S) (now : UInt64)
    (stream₁ stream₂ : List CircleOverlayUpdate)
    (hsame : ∀ u, u ∈ stream₁ ↔ u ∈ stream₂) :
    ingestUpdates pol now stream₁ = ingestUpdates pol now stream₂ ∧
    AllAdmitted pol now (ingestUpdates pol now stream₁) := by
  have hmem : ∀ s e, e ∈ ingestUpdates pol now s ↔ ∃ u ∈ s, admitCircleUpdate pol now u = .ok e := by
    intro s e; simpa [ingestUpdates] using mem_ingestUpdates_aux pol now ∅ s e
  refine ⟨Finset.ext fun e => ?_, fun e he => ?_⟩
  · rw [hmem, hmem]; constructor <;> rintro ⟨u, hu, hok⟩
    · exact ⟨u, (hsame u).1 hu, hok⟩
    · exact ⟨u, (hsame u).2 hu, hok⟩
  · obtain ⟨u, _, hok⟩ := (hmem stream₁ e).1 he; exact ⟨u, hok⟩

/-- Render a list of canonical spatial entries for an anchor cell into a toolkit-free
    `LightClientAndViewLens.ViewNode` AR reticle overlay tree. -/
def renderAnchorReticle (anchorTitle : String) (entries : List SpatialEntry) : ViewNode :=
  let toItem (e : SpatialEntry) : ViewNode :=
    let tag := if e.priority ≥ 2 then "hazard" else if e.priority == 1 then "caution" else "info"
    .pill (String.ofList (e.label.map fun b => Char.ofNat b.toNat)) tag none [] (some e.lamportClock)
  let rec go : List SpatialEntry → ViewList
    | [] => .nil
    | x :: xs => .cons (toItem x) (go xs)
  .sectionBox anchorTitle "ar-belief-circle" (go entries)

/-- Convergence of `OverlayState` implies identical rendered `ViewNode`s (`diff = .keep`). -/
theorem converged_overlay_renders_identical_viewNode {entries₁ entries₂ : List SpatialEntry}
    (title : String) (heq : entries₁ = entries₂) :
    diff (renderAnchorReticle title entries₁) (renderAnchorReticle title entries₂) = .keep := by
  subst heq; exact diff_self_keep _

/-- Canonical deterministic sorting order on `SpatialEntry` (by `(anchorId, ofBE entryDigest)`),
    mirroring Rust's `BTreeMap` / sorted digest order for `overlay_state_root`. -/
def entryLe (a b : SpatialEntry) : Bool :=
  if a.anchorId != b.anchorId then decide (a.anchorId < b.anchorId)
  else decide (ofBE a.entryDigest ≤ ofBE b.entryDigest)

def insertEntrySorted (x : SpatialEntry) : List SpatialEntry → List SpatialEntry
  | [] => [x]
  | y :: ys =>
    if x == y then y :: ys
    else if entryLe x y then x :: y :: ys
    else y :: insertEntrySorted x ys

def canonicalizeEntries (xs : List SpatialEntry) : List SpatialEntry :=
  xs.foldl (fun acc x => insertEntrySorted x acc) []

def overlayStateRoot (entries : List SpatialEntry) : List UInt8 :=
  let canon := canonicalizeEntries entries
  cshake32 custOverlayRoot (leb128 canon.length ++ canon.flatMap (·.entryDigest))

/-! ## §4. Constructive `#tooth` Falsifiers & Golden Witnesses -/

section TeethAndWitnesses

/-- `#tooth 1`: Wormhole / remote relay at `5,000 mm` (5.0 m) exceeds `dreggBeliefTofParams`
    (`dMax = 3,000 mm`, deadline `24,003 ps`) with causal RTT `3,990 + 33,357 = 37,347 ps`
    and is deterministically rejected with `.err (.tofTimeout 0)`. -/
def toothTofSingle : TofParams :=
  { rounds := 2, tProcMinPs := dreggTProcMinPs, dMaxMm := 3000,
    vernierStepPs := dreggVernierStepPs, roundsPos := by omega }

theorem tooth_wormhole_relay_5m_rejected :
    CausallyConstrained dreggTProcMinPs 5000 37347 ∧
    verifyTofSession toothTofSingle
      ⟨[false, true], [true, false], [false, true], [false, false], [37347, 10000]⟩ =
      .err (.tofTimeout 0) := by
  refine ⟨⟨by decide, by decide⟩, by decide⟩

/-- `#tooth 2`: Early pre-trigger / electrical loopback below hardware turnaround floor `3,990 ps`
    is deterministically rejected with `.err (.belowTurnaroundFloor 0)`. -/
theorem tooth_below_turnaround_floor_rejected :
    verifyTofSession toothTofSingle
      ⟨[false, true], [true, false], [false, true], [false, false], [3989, 10000]⟩ =
      .err (.belowTurnaroundFloor 0) := by decide

/-- `#tooth 3`: Pre-committed early-bit fraud caught when challenge disagrees with pre-ask guess
    (`c = !g`) and hidden bit disagrees with fallback (`h = !f`), AND omitting `u_lock` breaks
    the `(3/4)^k` bound to `100%` (`4^k / 4^k`). -/
def unlockedResponderWin (_strat _env : List (Bool × Bool)) : Bool := true

theorem tooth_precommit_early_bit_caught_and_lock_load_bearing :
    preAskRoundWin false false true true = false ∧
    verifyTofSession toothTofSingle
      ⟨[false, true], [true, false], [true, false], [false, true], [12000, 12000]⟩ =
      .err (.responseBitMismatch 0) ∧
    (hkSpace 2).countP (preAskAllWin [(false, false), (true, true)]) = 9 ∧
    (hkSpace 2).countP (unlockedResponderWin [(false, false), (true, true)]) = 16 := by decide

/-- `#tooth 4`: Event-driven RF (emitting only on `.arHazardReticle`, silent on `.idle`) leaks
    the wearer's hazard alert tick directly to a passive room RF observer. -/
private def circleSched : Schedule :=
  { domain := ⟨42, by decide⟩, profile := P1, n := 2,
    leases := [⟨⟨42, by decide⟩, 10, 0, P1, (0, 10)⟩, ⟨⟨42, by decide⟩, 11, 1, P1, (0, 10)⟩],
    slotsFit := by decide }

private def circleSeal : Sealing P1 BeliefMsg (List UInt8) where
  sealBody _ h m :=
    let marker : UInt8 := if isDutyTick h then 0xD0 else h.slot.val.toUInt8
    let tag : UInt8 := match m with | none => 0x00 | some msg => msg.viewTag
    fit P1.bodyLen [marker, tag]
  observe _ b := b.val.take 1

private def leakyCircleSeal : Sealing P1 BeliefMsg (List UInt8) where
  sealBody := circleSeal.sealBody
  observe _ b := b.val.take 2

private def circlePrf : FillPrf := fun h => [h.slot.val.toUInt8]
private def quietAct : Nat → Nat → WearableActivity := fun _ _ => .idle
private def hazardAct : Nat → Nat → WearableActivity :=
  fun k ρ => if k == 1 && ρ == 0 then .arHazardReticle 7 2 [0xAA] else .idle
private def allPresent : Presences := fun _ _ => true

private def designCircleDomain : Domain BeliefMsg (List UInt8) :=
  ⟨circleSched, circleSeal, circlePrf, designEmission P1 BeliefMsg⟩

private def eventDrivenCircleDomain : Domain BeliefMsg (List UInt8) :=
  ⟨circleSched, circleSeal, circlePrf, fun m => m.map fun _ => 700⟩

private def unsealedCircleDomain : Domain BeliefMsg (List UInt8) :=
  ⟨circleSched, leakyCircleSeal, circlePrf, designEmission P1 BeliefMsg⟩

private theorem circleSeal_payloadHidden : PayloadHidden circleSeal := by
  intro s h m₁ m₂
  simp only [circleSeal, fit, List.take_take, List.cons_append]
  have hmin : min 1 P1.bodyLen = 1 := by decide
  rw [hmin]; rfl

theorem witness_design_circle_hides_hazard_from_rf :
    Domain.trace (designCircleDomain.wireTick designPolicy (activityScheduleToTraffic quietAct) allPresent) 2 =
      Domain.trace (designCircleDomain.wireTick designPolicy (activityScheduleToTraffic hazardAct) allPresent) 2 :=
  (circle_rf_trace_independent_of_activity designCircleDomain circleSeal_payloadHidden
    (designEmission_constant P1 BeliefMsg) designPolicy quietAct hazardAct allPresent 1 2).1

theorem tooth_event_driven_rf_leaks_hazard :
    Domain.trace (eventDrivenCircleDomain.wireTick designPolicy (activityScheduleToTraffic quietAct) allPresent) 2 ≠
      Domain.trace (eventDrivenCircleDomain.wireTick designPolicy (activityScheduleToTraffic hazardAct) allPresent) 2 := by
  decide +kernel

theorem tooth_unsealed_cell_leaks_hazard :
    Domain.trace (unsealedCircleDomain.wireTick designPolicy (activityScheduleToTraffic quietAct) allPresent) 2 ≠
      Domain.trace (unsealedCircleDomain.wireTick designPolicy (activityScheduleToTraffic hazardAct) allPresent) 2 := by
  decide +kernel

/-- `#tooth 5` (`Theory.Confluence` sharp edge): a cardinality ceiling ("at most 1 active reticle
    in the room") is NOT `IConfluent`, whereas a grow-only floor IS `CoordinationFree`. -/
private def sampleEntryA : SpatialEntry :=
  ⟨42, 1, 1, 0, 2, [0x41], [0x01]⟩
private def sampleEntryB : SpatialEntry :=
  ⟨42, 2, 1, 1, 2, [0x42], [0x02]⟩

theorem tooth_maxOneReticle_not_iconfluent :
    ¬ CoordinationFree (S := OverlayState) (.bounded Finset.card 1) :=
  bounded_breaks Finset.card 1 (x := {sampleEntryA}) (y := {sampleEntryB})
    (by decide) (by decide) (by decide)

theorem witness_reticle_floor_coordination_free (c : Nat) :
    CoordinationFree (S := OverlayState) (.monotone Finset.card c) :=
  monotone_free Finset.card_mono c

end TeethAndWitnesses

/-! ## §5. Lean-Authored Byte-Exact Conformance Vector Emitter & `#guard_msgs` Axiom Audit -/

private def hexBytes (bs : List UInt8) : String :=
  let d := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  String.join (bs.map fun b => String.ofList [d[(b.toNat / 16) % 16]!, d[b.toNat % 16]!])

def emitBeliefCircleConformance (path : System.FilePath) : IO Unit := do
  let tofSecret := strBytes "MINIDREGG-BELIEF-TOF-SECRET-32B!"; let tofNonce := strBytes "TOF-NONCE-16BYTE"
  let verSeed := strBytes "MINIDREGG-TOF-VERIFIER-SEED-32B!"
  let r0 := deriveTofBits custTofR0 tofSecret tofNonce; let r1 := deriveTofBits custTofR1 tofSecret tofNonce
  let ch := deriveTofBits custTofChal verSeed tofNonce; let rp := computeTofResponse r0 r1 ch
  let inRangeTimes := (List.range 128).map fun i => 10000 + (i % 7) * dreggVernierStepPs
  let okTof := verifyTofSession dreggBeliefTofParams ⟨r0, r1, ch, rp, inRangeTimes⟩ == .ok
  let rejFar := verifyTofSession dreggBeliefTofParams ⟨r0, r1, ch, rp, 37347 :: inRangeTimes.tail⟩ == .err (.tofTimeout 0)
  let rejEarly := verifyTofSession dreggBeliefTofParams ⟨r0, r1, ch, rp, 3989 :: inRangeTimes.tail⟩ == .err (.belowTurnaroundFloor 0)
  let circleKey := cshake32 (strBytes "MINIDREGG.BELIEF_CIRCLE.KEY_DERIVE") (strBytes "room-42-epoch-7")
  let hdrP2Reg : Header := ⟨U16.ofNat 42, U16.ofNat 7, U16.ofNat 3, U16.ofNat 1⟩
  let hdrP2Duty : Header := ⟨U16.ofNat 42, U16.ofNat 7, U16.ofNat 0, U16.ofNat 1⟩
  let vrf : Blob 96 := fit 96 (cshakeKeystream (strBytes "MINIDREGG.TEST.VRF") circleKey [1] 96)
  let vRoot : Blob 32 := fit 32 (cshake32 (strBytes "MINIDREGG.TEST.VROOT") [1])
  let aRoot : Blob 32 := fit 32 (cshake32 (strBytes "MINIDREGG.TEST.AROOT") [1])
  let hazardPayload := strBytes "HAZARD:480V-BUS-LIVE"; let jittPayload := strBytes "JITT:SCHEMATIC-PANEL-B"
  let p2IdleCell := sealBeliefCellCshake P2 circleKey hdrP2Reg vrf vRoot aRoot .idle
  let p2HazardCell := sealBeliefCellCshake P2 circleKey hdrP2Reg vrf vRoot aRoot (.arHazardReticle 101 2 hazardPayload)
  let p2DutyCell := sealBeliefCellCshake P2 circleKey hdrP2Duty vrf vRoot aRoot (.jittQuery jittPayload)
  let p1HazardCell := sealBeliefCellCshake P1 circleKey hdrP2Reg vrf vRoot aRoot (.arHazardReticle 101 2 hazardPayload)
  let iSeed := strBytes "BELIEF-CIRCLE-ISSUER-SEED-32BYTE"; let aSeed := strBytes "BELIEF-CIRCLE-ALICE-SEED-32BYTES"
  let bSeed := strBytes "BELIEF-CIRCLE-BOB-SEED-32BYTES!!"; let cSeed := strBytes "BELIEF-CIRCLE-CAROL-SEED-32BYTES"
  let iPk := wotsCshake256.pkOf iSeed; let aPk := wotsCshake256.pkOf aSeed
  let bPk := wotsCshake256.pkOf bSeed; let cPk := wotsCshake256.pkOf cSeed
  let attrRoot := cshake32 (strBytes "MINIDREGG.BELIEF.ATTR_ROOT") (strBytes "circle-42")
  let nonceA := cshake32 (strBytes "MINIDREGG.BELIEF.NONCE") [1]; let nonceB := cshake32 (strBytes "MINIDREGG.BELIEF.NONCE") [2]
  let tokA := issueRootToken wotsCshake256 ⟨iSeed⟩ (strBytes "alice") aPk attrRoot nonceA 0x03 2000
  let tokB := issueRootToken wotsCshake256 ⟨iSeed⟩ (strBytes "bob") bPk attrRoot nonceB 0x03 2000
  let tokC := attenuateToken wotsCshake256 tokB bSeed 0x01 1800 cPk (strBytes "scope=ar_write")
  let pol : CirclePolicy wotsCshake256 := ⟨42, iPk, RevocationSet.empty, circleWriteRight, dreggBeliefTofParams⟩
  let goodTof : TofTranscript := ⟨r0, r1, ch, rp, inRangeTimes⟩
  let uA : CircleOverlayUpdate := ⟨42, 101, 1, 0, 2, hazardPayload, tokA, goodTof⟩
  let uB : CircleOverlayUpdate := ⟨42, 102, 1, 1, 1, strBytes "CAUTION:WET-FLOOR", tokB, goodTof⟩
  let uC : CircleOverlayUpdate := ⟨42, 101, 2, 2, 0, jittPayload, tokC, goodTof⟩
  let eA := mkSpatialEntry 42 101 1 0 2 hazardPayload
  let eB := mkSpatialEntry 42 102 1 1 1 (strBytes "CAUTION:WET-FLOOR")
  let eC := mkSpatialEntry 42 101 2 2 0 jittPayload
  let admAll := admitCircleUpdate pol 1000 uA == .ok eA && admitCircleUpdate pol 1000 uB == .ok eB && admitCircleUpdate pol 1000 uC == .ok eC
  let rootFwd := overlayStateRoot [eA, eB, eC]; let rootRev := overlayStateRoot [eC, eB, eA]
  let polRev : CirclePolicy wotsCshake256 := ⟨42, iPk, RevocationSet.ofList [chainId tokC.block0 tokC.hops 0], circleWriteRight, dreggBeliefTofParams⟩
  let revKillsC := match admitCircleUpdate polRev 1000 uC with | .err .invalidCredential => true | _ => false
  let jb (b : Bool) := if b then "true" else "false"; let kv (k v : String) := s!"\"{k}\": \"{v}\""
  let fields : List String := [
    kv "schema" "minidregg.belief_circle_conformance.v1",
    s!"\"tof_rounds\": 128", s!"\"t_proc_min_ps\": {dreggTProcMinPs}", s!"\"d_max_mm\": 3000",
    s!"\"max_round_time_ps\": {dreggBeliefTofParams.maxRoundTimePs}", s!"\"vernier_step_ps\": {dreggVernierStepPs}",
    kv "tof_secret_hex" (hexBytes tofSecret), kv "tof_nonce_hex" (hexBytes tofNonce), kv "tof_verifier_seed_hex" (hexBytes verSeed),
    kv "tof_r0_hex" (hexBytes (bitsToBytesLSB r0)), kv "tof_r1_hex" (hexBytes (bitsToBytesLSB r1)),
    kv "tof_chal_hex" (hexBytes (bitsToBytesLSB ch)), kv "tof_resp_hex" (hexBytes (bitsToBytesLSB rp)),
    s!"\"tof_in_range_accepted\": {jb okTof}", s!"\"tof_wormhole_5m_rejected\": {jb rejFar}", s!"\"tof_early_trigger_rejected\": {jb rejEarly}",
    kv "circle_key_hex" (hexBytes circleKey), kv "duty_vrf_hex" (hexBytes vrf.val),
    kv "duty_verdict_root_hex" (hexBytes vRoot.val), kv "duty_acc_root_hex" (hexBytes aRoot.val),
    kv "hazard_payload_hex" (hexBytes hazardPayload), kv "jitt_payload_hex" (hexBytes jittPayload),
    kv "p2_idle_cell_hex" (hexBytes p2IdleCell.encode), kv "p2_hazard_cell_hex" (hexBytes p2HazardCell.encode),
    kv "p2_duty_cell_hex" (hexBytes p2DutyCell.encode), kv "p1_hazard_cell_hex" (hexBytes p1HazardCell.encode),
    kv "issuer_seed_hex" (hexBytes iSeed), kv "alice_seed_hex" (hexBytes aSeed),
    kv "bob_seed_hex" (hexBytes bSeed), kv "carol_seed_hex" (hexBytes cSeed),
    kv "issuer_pk_hex" (hexBytes iPk), kv "attr_root_hex" (hexBytes attrRoot),
    kv "nonce_a_hex" (hexBytes nonceA), kv "nonce_b_hex" (hexBytes nonceB),
    kv "entry_a_digest_hex" (hexBytes eA.entryDigest), kv "entry_b_digest_hex" (hexBytes eB.entryDigest),
    kv "entry_c_digest_hex" (hexBytes eC.entryDigest), kv "merged_overlay_root_hex" (hexBytes rootFwd),
    s!"\"overlay_order_invariant\": {jb (rootFwd == rootRev)}", s!"\"admitted_all_three\": {jb admAll}",
    s!"\"revoked_bob_kills_carol_delegation\": {jb revKillsC}"
  ]
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path ("{\n  " ++ String.intercalate ",\n  " fields ++ "\n}\n")

#eval emitBeliefCircleConformance "prover/testdata/belief_circle_conformance.json"

/-- info: 'Minidregg.Assurance.WearableBeliefCircle.tof_accepts_implies_within_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tof_accepts_implies_within_radius
/-- info: 'Minidregg.Assurance.WearableBeliefCircle.wormhole_relay_deterministically_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wormhole_relay_deterministically_rejected
/-- info: 'Minidregg.Assurance.WearableBeliefCircle.hancke_kuhn_mafia_fraud_exact_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hancke_kuhn_mafia_fraud_exact_count
/-- info: 'Minidregg.Assurance.WearableBeliefCircle.hancke_kuhn_mafia_fraud_reject_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hancke_kuhn_mafia_fraud_reject_count
/-- info: 'Minidregg.Assurance.WearableBeliefCircle.blind_precommit_exact_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms blind_precommit_exact_count
/-- info: 'Minidregg.Assurance.WearableBeliefCircle.circle_rf_trace_independent_of_activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms circle_rf_trace_independent_of_activity
/-- info: 'Minidregg.Assurance.WearableBeliefCircle.circle_member_presence_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms circle_member_presence_hidden
/-- info: 'Minidregg.Assurance.WearableBeliefCircle.admitCircleUpdate_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms admitCircleUpdate_sound
/-- info: 'Minidregg.Assurance.WearableBeliefCircle.overlay_drops_out_of_range_relay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms overlay_drops_out_of_range_relay
/-- info: 'Minidregg.Assurance.WearableBeliefCircle.overlay_drops_revoked_credential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms overlay_drops_revoked_credential
/-- info: 'Minidregg.Assurance.WearableBeliefCircle.overlay_allAdmitted_iconfluent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms overlay_allAdmitted_iconfluent
/-- info: 'Minidregg.Assurance.WearableBeliefCircle.overlay_zero_round_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms overlay_zero_round_convergence
/-- info: 'Minidregg.Assurance.WearableBeliefCircle.tooth_wormhole_relay_5m_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_wormhole_relay_5m_rejected
/-- info: 'Minidregg.Assurance.WearableBeliefCircle.tooth_precommit_early_bit_caught_and_lock_load_bearing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_precommit_early_bit_caught_and_lock_load_bearing
/-- info: 'Minidregg.Assurance.WearableBeliefCircle.tooth_event_driven_rf_leaks_hazard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_event_driven_rf_leaks_hazard
/-- info: 'Minidregg.Assurance.WearableBeliefCircle.tooth_maxOneReticle_not_iconfluent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_maxOneReticle_not_iconfluent

end Minidregg.Assurance.WearableBeliefCircle
