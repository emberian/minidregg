/- Named poles for the Objective Bend families the hypothesis ledger reads.

`scripts/HypothesisLedger.lean` now imports the `ObjectiveProofs` modules (through
`Kernel.ObjectiveResumeContract`, for the open premise `ForcingTransparent`), so it reads
four families it never saw before, each consumed and each TOOTHLESS: no named instance
showed it can hold AND can fail. These are those instances, one satisfying and one
refuting per family, over the real definitions. -/
import Theory.ObjectiveBendDemandPreservation
namespace Minidregg.Theory.ObjectiveBendLedgerPoles
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandInvariant
open Minidregg.Theory.ObjectiveBendDemandAdequacy (MeaningsScoped EvaluatingSegment)
open Minidregg.Theory.ObjectiveBendDemandTyping (ConversionPath)
open Minidregg.Theory.ObjectiveBendDemandPreservation (HeadNormalizes head_normalizes_unique same_type_preserves_head)
open Minidregg.Theory.ObjectiveBendTypes (Ty)
open Minidregg.Theory.ObjectiveBendTyping (Assumptions)
set_option autoImplicit false

/-! ## `MeaningsScoped` -/

/-- No address is allocated below 0: any meaning is scoped there. -/
theorem meaningsScoped_unallocated : MeaningsScoped 0 (fun _ => .bound 0) :=
  fun _ below => absurd below (Nat.not_lt_zero _)

/-- An allocated address meaning an open term is not scoped. -/
theorem not_meaningsScoped_open : ¬ MeaningsScoped 1 (fun _ => .bound 0) := by
  intro allScoped
  have := allScoped 0 (by decide)
  simp at this

/-! ## `EvaluatingSegment` -/

def poleEntered : State := ⟨#[.suspended ⟨.nat 1, []⟩], .enter 0, []⟩

/-- Entering a suspended cell starts its evaluating segment. -/
theorem evaluatingSegment_started :
    EvaluatingSegment 0 ⟨.nat 1, []⟩ poleEntered (stepRaw poleEntered) :=
  .start rfl rfl

theorem evaluatingSegment_entry_cell {address : Address} {origin : Closure} {entered state : State}
    (segment : EvaluatingSegment address origin entered state) :
    entered.heap[address]? = some (.suspended origin) := by
  induction segment with
  | start _ found => exact found
  | next _ _ ih => exact ih

/-- No segment starts at an address the heap does not hold. -/
theorem not_evaluatingSegment_unallocated (state : State) :
    ¬ EvaluatingSegment 0 ⟨.nat 1, []⟩ ⟨#[], .enter 0, []⟩ state := by
  intro segment
  have := evaluatingSegment_entry_cell segment
  simp at this

/-! ## `ConversionPath` -/

theorem conversionPath_natural : ConversionPath ({} : Assumptions) .natural .natural := .refl _

theorem conversionPath_head {assumptions : Assumptions} {first last result : Ty}
    (path : ConversionPath assumptions first last)
    (normal : HeadNormalizes assumptions.bounds first result) :
    HeadNormalizes assumptions.bounds last result := by
  induction path with
  | refl => exact normal
  | step _ agreement ih => exact same_type_preserves_head agreement ih

/-- No conversion path turns a natural into a boolean. -/
theorem not_conversionPath_natural_boolean : ¬ ConversionPath ({} : Assumptions) .natural .boolean := by
  intro path
  have natural : HeadNormalizes ({} : Assumptions).bounds .natural Ty.natural.canonical := .direct _ rfl
  have boolean : HeadNormalizes ({} : Assumptions).bounds .boolean Ty.boolean.canonical := .direct _ rfl
  have same := head_normalizes_unique (conversionPath_head path natural) boolean
  simp [Ty.canonical] at same

/-! ## `StepCases` -/

theorem stepCases_trivial : StepCases (fun _ => True) := by
  constructor <;> intros <;> trivial

theorem not_stepCases_false : ¬ StepCases (fun _ => False) :=
  fun cases => cases.complete ⟨#[], .complete (.natural 0), []⟩ (.natural 0) rfl

#assert_axioms meaningsScoped_unallocated not_meaningsScoped_open evaluatingSegment_started
  evaluatingSegment_entry_cell not_evaluatingSegment_unallocated conversionPath_natural conversionPath_head
  not_conversionPath_natural_boolean stepCases_trivial not_stepCases_false

end Minidregg.Theory.ObjectiveBendLedgerPoles
