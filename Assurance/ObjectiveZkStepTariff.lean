import Assurance.ObjectiveZkLiteralInstance
import Assurance.ObjectiveBendCommittedSource

/- The step-count leak (scout F §6; CONSTRUCTION-PROOF-CONTRACTS §5 "Plan(false,false)")
stated over the Objective machine and the actual physical graph.

* `plan`: a Core4 program whose secret Nat selects a branch. Both secrets observe
  `natural 0` (`plan_same_meaning`), but stepRaw needs 5 vs 8 steps (`plan_steps`).
* `measuredView`: the public physical tick count chosen from the measured run (what
  Verify/ObjectiveDemandGraphArtifact does with its literal `physicalTicks 9` for an
  8-step program). `measured_view_leaks`: equal meaning, different public view.
* `tariffView`: ticks taken from a signed public envelope. `tariffView_eq_of_within`
  is the noninterference statement: any two programs that complete within the tariff
  have equal public views. Its content is `rawRun_complete_absorbing` (completion is
  a fixed point of stepRaw), and physically `nat7_run_padded` (the actual graph keeps
  handled = true after completion, so the SAME final row is accepted at every public
  tick count ≥ 2).
* `tariff_residual`: the success bit is still public; a tariff below the worst case
  over the secret domain distinguishes. The tariff must be a public bound for the
  whole secret domain, with refusal public by design.
* `nat7_envelope_run`: the emitter side of the fix. For every public rate and
  signed envelope granting at least the completion time, the actual graph has an
  accepted run of EXACTLY `rate.ticks capacity` ticks from the pinned bits to the
  completed row, so the receiving statement
  (ObjectiveBendCommittedSource.arithmetic_observes_source, unrolled at
  `rate.ticks capacity`) is instantiable without any measured count. -/
namespace Minidregg.Assurance.ObjectiveZkStepTariff
open Minidregg.Compiler Minidregg.Theory
open ObjectiveBendOpenRecursion ObjectiveBendDemandMachine ObjectiveBendDemandAdequacy
open ObjectiveBendDemandInvariant
open ObliviousNetwork ObliviousUnroll
open Minidregg.Assurance.ObjectiveZkLiteralInstance
set_option autoImplicit false

/-! ### Source side -/

/-- Secret `s` selects the branch; the public result is `0` either way. -/
def plan (secret : Nat) : Term :=
  .ifZero (.nat secret) (.nat 0) (.app (.lam (.nat 0)) (.nat 0))

def completed (state : State) : Bool :=
  match state.control with
  | .complete _ => true
  | _ => false

/-- Least tick count reaching completion, searched up to `fuel`. -/
def stepsToComplete (state : State) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel+1, count => if completed (rawRun count state) then some count
      else stepsToComplete state fuel (count+1)

theorem plan_steps :
    stepsToComplete (ObjectiveBendDemandMachine.initial (plan 0)) 32 0 = some 5 ∧
    stepsToComplete (ObjectiveBendDemandMachine.initial (plan 1)) 32 0 = some 8 := by
  decide

theorem plan0_complete :
    (rawRun 5 (ObjectiveBendDemandMachine.initial (plan 0))).control = .complete (.natural 0) := by
  rfl
theorem plan1_complete :
    (rawRun 8 (ObjectiveBendDemandMachine.initial (plan 1))).control = .complete (.natural 0) := by
  rfl

theorem plan_closed (secret : Nat) : Scoped 0 (plan secret) :=
  .condition (.natural secret) (.natural 0) (.app (.lam (.natural 0)) (.natural 0))

/-- Same permitted result, by the source adequacy theorems (not by running the graph). -/
theorem plan_same_meaning : Evaluates (plan 0) (.nat 0) ∧ Evaluates (plan 1) (.nat 0) :=
  ⟨rawRun_natural_sound (plan_closed 0) plan0_complete,
   rawRun_natural_sound (plan_closed 1) plan1_complete⟩

/-! ### Completion is absorbing (general) -/

theorem rawRun_add : ∀ (n k : Nat) (state : State), rawRun (n + k) state = rawRun k (rawRun n state)
  | 0, k, state => by
      show rawRun (0 + k) state = rawRun k state
      rw [Nat.zero_add]
  | n+1, k, state => by
      rw [Nat.add_right_comm]
      show rawRun (n + k) (stepRaw state) = rawRun k (rawRun n (stepRaw state))
      exact rawRun_add n k (stepRaw state)

theorem stepRaw_complete {state : State} {value : RuntimeValue}
    (complete : state.control = .complete value) : stepRaw state = state := by
  unfold stepRaw
  simp only [complete]

theorem rawRun_fixed {state : State} {value : RuntimeValue}
    (complete : state.control = .complete value) : ∀ k, rawRun k state = state
  | 0 => rfl
  | k+1 => by
      show rawRun k (stepRaw state) = state
      rw [stepRaw_complete complete]
      exact rawRun_fixed complete k

theorem rawRun_complete_absorbing {n m : Nat} {state : State} {value : RuntimeValue}
    (complete : (rawRun n state).control = .complete value) (le : n ≤ m) :
    rawRun m state = rawRun n state := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le le
  rw [rawRun_add]
  exact rawRun_fixed complete k

/-! ### Public views -/

/-- What the proof artifact publishes about time: its physical tick count (the
unrolled graph `build original ticks` is a function of it) and the success pin. -/
structure PublicView where
  ticks : Nat
  success : Bool
  deriving DecidableEq, Repr

/-- Signed before execution; never derived from the run. -/
structure Envelope where
  ticks : Nat
  deriving DecidableEq, Repr

def measuredView (fuel : Nat) (source : Term) : PublicView :=
  match stepsToComplete (ObjectiveBendDemandMachine.initial source) fuel 0 with
  | some steps => ⟨steps, true⟩
  | none => ⟨fuel, false⟩

def tariffView (envelope : Envelope) (source : Term) : PublicView :=
  ⟨envelope.ticks, completed (rawRun envelope.ticks (ObjectiveBendDemandMachine.initial source))⟩

/-- THE LEAK: equal source meaning, different public view under a measured tick count. -/
theorem measured_view_leaks :
    Evaluates (plan 0) (.nat 0) ∧ Evaluates (plan 1) (.nat 0) ∧
    measuredView 32 (plan 0) ≠ measuredView 32 (plan 1) :=
  ⟨plan_same_meaning.1, plan_same_meaning.2, by decide⟩

theorem completed_of_control {state : State} {value : RuntimeValue}
    (complete : state.control = .complete value) : completed state = true := by
  simp only [completed, complete]

/-- THE FIX: under a public tariff, every pair of programs that completes within it has
the same public view. The secret enters only through the completion time, which the
absorbing law erases. -/
theorem tariffView_eq_of_within (envelope : Envelope) {left right : Term}
    {leftSteps rightSteps : Nat} {leftValue rightValue : RuntimeValue}
    (leftDone : (rawRun leftSteps (ObjectiveBendDemandMachine.initial left)).control = .complete leftValue)
    (rightDone : (rawRun rightSteps (ObjectiveBendDemandMachine.initial right)).control = .complete rightValue)
    (leftWithin : leftSteps ≤ envelope.ticks) (rightWithin : rightSteps ≤ envelope.ticks) :
    tariffView envelope left = tariffView envelope right := by
  unfold tariffView
  rw [rawRun_complete_absorbing leftDone leftWithin, rawRun_complete_absorbing rightDone rightWithin,
    completed_of_control leftDone, completed_of_control rightDone]

theorem plan_tariff_hides (envelope : Envelope) (covers : 8 ≤ envelope.ticks) :
    tariffView envelope (plan 0) = tariffView envelope (plan 1) :=
  tariffView_eq_of_within envelope plan0_complete plan1_complete
    (Nat.le_trans (by decide) covers) covers

/-- The residual channel: below the worst case over the secret domain the success
pin distinguishes. Refusal is public by design; the tariff must cover the domain. -/
theorem tariff_residual :
    tariffView ⟨6⟩ (plan 0) ≠ tariffView ⟨6⟩ (plan 1) := by
  decide

/-! ### Physical side: the actual graph accepts the same final row at every tariff -/

theorem acceptedRun_snoc {network : Network} : ∀ {ticks : Nat} {input final next : Array Bool},
    AcceptedRun network ticks input final → next? network final = some next →
    AcceptedRun network (ticks+1) input next
  | _, _, _, _, .done input, stepped => acceptedRun_of_next stepped (.done _)
  | _, _, _, _, .step evaluated handled tail, stepped =>
      .step evaluated handled (acceptedRun_snoc tail stepped)

/-- A row the graph re-accepts unchanged absorbs any number of further ticks. -/
theorem acceptedRun_pad {network : Network} {ticks : Nat} {input final : Array Bool}
    (run : AcceptedRun network ticks input final) (stutters : next? network final = some final) :
    ∀ extra, AcceptedRun network (ticks + extra) input final
  | 0 => run
  | extra+1 => acceptedRun_snoc (acceptedRun_pad run stutters extra) stutters

/-- For every public tick count `T + 2`, the actual literal graph has an accepted run
from the pinned initial bits ending in the completed row, whose reader returns 7.
The public unrolled graph is then a function of `T` alone. -/
theorem nat7_run_padded (T : Nat) : AcceptedRun graph (T+2) nat7.initialBits nat7Tick2 := by
  rw [Nat.add_comm]
  exact acceptedRun_pad nat7_run nat7_complete_stutters T

/-- The emitter's tick count comes from the signed envelope: whenever it covers the
completion time, the run that the envelope-tick statement speaks about exists and
ends in the completed row whose derived reader answers `7`. -/
theorem nat7_envelope_run (rate : ObjectiveBendCommittedSource.PhysicalRate)
    (capacity : ObjectiveInvocationClaim.Capacity) (covers : 2 ≤ rate.ticks capacity) :
    AcceptedRun graph (rate.ticks capacity) nat7.initialBits nat7Tick2 ∧
      regionCodec.read nat7Tick2 = some (.natural 7) := by
  obtain ⟨T, same⟩ := Nat.exists_eq_add_of_le covers
  refine ⟨?_, nat7_read⟩
  rw [same, Nat.add_comm]
  exact nat7_run_padded T

/-- The envelope premise is inhabited: the unit rate and a two-tick envelope. -/
theorem nat7_envelope_inhabited :
    2 ≤ (⟨1, 1, 0⟩ : ObjectiveBendCommittedSource.PhysicalRate).ticks
      { typeFuel := 0, sourceTicks := 2, heap := 0, stack := 0, outputNodes := 0, outputBytes := 0,
        inputBytes := 0, scalarBits := 0, memoryTouches := 0, proofWork := 0, feeDebit := 0,
        turnBytes := 0, witnessBytes := 0, storageBytes := 0, sideEffectCount := 0,
        networkBytes := 0, leaseByteBlocks := 0, incidences := 0 } := by
  decide

#assert_axioms plan_steps
#assert_axioms plan_same_meaning
#assert_axioms rawRun_complete_absorbing
#assert_axioms measured_view_leaks
#assert_axioms tariffView_eq_of_within
#assert_axioms plan_tariff_hides
#assert_axioms tariff_residual
#assert_axioms acceptedRun_snoc
#assert_axioms acceptedRun_pad
#assert_compiled nat7_run_padded
#assert_compiled nat7_envelope_run
#assert_axioms nat7_envelope_inhabited
end Minidregg.Assurance.ObjectiveZkStepTariff
