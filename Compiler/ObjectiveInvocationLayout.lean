/- Objective invocation layout: what the native gate's output adapters read
from a command, and what they do not.

The quotation producer (Host/ObjectiveInvocationQuote) derives the final signed
command from a locally retained request. This module fixes the three facts that
producer depends on:

* `*Source_exact`: the source-level outcome of every output adapter (decoded
  native Plan, result data/bytes) is a function of the applied source term and
  the signed capacity ALONE. Any adapter token for ANY command carries exactly
  the command-free `*Source` value. The producer evaluates once, with no command.
* `effectsOf_layout`: a command laid out as [effect targets in plan order] ++
  [inert targets] reports exactly those ordered payloads through
  `BendWorldPlan.effectsOf`. Order is not assumed by the gate: `matchesCommand`
  compares indices and order, so a command whose target order differs from the
  plan order refuses there.
* `placeholder_draft_refuses_effects`: the refuted design. A draft whose roles
  are all read placeholders reports no effects, so the gate's exact comparison
  refuses every effectful plan on it. Adapters bind by payload, not only by
  resource and root (`ObjectiveBendNativePlanData.bindEffect.payloadExact`,
  `ObjectiveBendResultAdapter.storesReturn`). -/
import Compiler.ObjectiveBendPlanAdapter
import Compiler.ObjectiveBendResultAdapter
import Compiler.ObjectiveBendCombinedResult
import Compiler.ObjectiveBendGenericResult
import Kernel.ObjectiveBendPreparedOutput
import Theory.AssertAxioms
namespace Minidregg.Compiler.ObjectiveInvocationLayout
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandData
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false

/-! ## Command-free source outcomes -/

/-- Scalar-record codec: the decoded native Plan. -/
def scalarSource (capacity : ObjectiveBendDemandCapacity.Profile) (limits : Limits)
    (budget : Budget) (term : ObjectiveBendOpenRecursion.Term) :
    Option ObjectiveNativeScalarBinding.NativePlan :=
  match executeWith (ObjectiveBendDemandCapacity.allows capacity) limits budget term with
  | .error _ => none
  | .ok execution => ObjectiveBendPlanAdapter.decode execution.extraction.result.value

/-- Clear result codec: the complete ground value. -/
def resultSource (capacity : ObjectiveBendDemandCapacity.Profile) (limits : Limits)
    (budget : Budget) (term : ObjectiveBendOpenRecursion.Term) : Option Data :=
  match executeWith (ObjectiveBendDemandCapacity.allows capacity) limits budget term with
  | .error _ => none
  | .ok execution => some execution.extraction.result.value

/-- Combined {plan,result} envelope over the scalar-record plan codec. -/
def combinedSource (capacity : ObjectiveBendDemandCapacity.Profile) (limits : Limits)
    (budget : Budget) (term : ObjectiveBendOpenRecursion.Term) :
    Option (ObjectiveNativeScalarBinding.NativePlan × Data) :=
  match executeWith (ObjectiveBendDemandCapacity.allows capacity) limits budget term with
  | .error _ => none
  | .ok execution =>
    match execution.extraction.result.value with
    | .record [("plan",planData),("result",resultData)] =>
      (ObjectiveBendPlanAdapter.decode planData).map fun native => (native,resultData)
    | _ => none

/-- Generic {plan,result} envelope over native typed payloads. -/
def genericSource (capacity : ObjectiveBendDemandCapacity.Profile) (limits : Limits)
    (budget : Budget) (term : ObjectiveBendOpenRecursion.Term) :
    Option (ObjectiveBendNativePlanData.NativePlan × Data) :=
  match executeWith (ObjectiveBendDemandCapacity.allows capacity) limits budget term with
  | .error _ => none
  | .ok execution =>
    match execution.extraction.result.value with
    | .record [("plan",planData),("result",resultData)] =>
      (ObjectiveBendNativePlanData.decode capacity planData).map fun native => (native,resultData)
    | _ => none

section
variable {deployment : CanonicalCellRegistry.Deployment}
  {loaded : Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry}
  {profile : ObjectiveBendResultAdapter.Profile} {command : Command} {source : AnnotatedTerm}
  {limits : Limits} {budget : Budget} {capacity : ObjectiveBendDemandCapacity.Profile}

theorem scalarSource_exact
    (prepared : Kernel.ObjectiveBendPreparedOutput.Prepared deployment loaded command source limits budget capacity) :
    scalarSource capacity limits budget source.term = some prepared.proposal := by
  have lowered := prepared.lowerExact
  unfold scalarSource
  rw [prepared.runExact]
  unfold ObjectiveBendPlanAdapter.lower at lowered
  cases decoded : ObjectiveBendPlanAdapter.decode prepared.execution.extraction.result.value with
  | none => simp [decoded] at lowered
  | some native =>
    cases bound : ObjectiveNativeScalarBinding.bindPlan deployment loaded command native with
    | none => simp [decoded, bound] at lowered
    | some plan =>
      simp only [decoded, bound, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Sigma.mk.injEq] at lowered
      rw [← lowered.1]
      exact decoded

theorem resultSource_exact
    (prepared : ObjectiveBendResultAdapter.PreparedResult profile command source limits budget capacity) :
    resultSource capacity limits budget source.term = some prepared.execution.extraction.result.value := by
  unfold resultSource
  rw [prepared.runExact]

theorem combinedSource_exact
    (prepared : ObjectiveBendCombinedResult.Prepared deployment loaded profile command source limits budget capacity) :
    combinedSource capacity limits budget source.term = some (prepared.native,prepared.resultData) := by
  unfold combinedSource
  rw [prepared.runExact]
  simp only [prepared.dataShape, prepared.decodedPlan, Option.map_some]

theorem genericSource_exact
    (prepared : ObjectiveBendGenericResult.Prepared deployment loaded profile command source limits budget capacity) :
    genericSource capacity limits budget source.term = some (prepared.native,prepared.resultData) := by
  unfold genericSource
  rw [prepared.runExact]
  simp only [prepared.dataShape, prepared.decodedPlan, Option.map_some]
end

/-! ## What `effectsOf` reads -/

/-- `effectsOf`'s per-target step, by explicit position. -/
def step (index : Nat) (target : Target) : Option BendWorldPlan.Effect :=
  match target.payload with
  | .read | .kindRead | .computeFunding _ => none
  | payload => some ⟨index,payload⟩

/-- Payloads `effectsOf` reports verbatim. -/
def verbatim : Payload → Bool
  | .read | .kindRead | .computeFunding _ => false
  | _ => true

/-- Payloads `effectsOf` never reports. -/
def inert : Payload → Bool
  | .read | .kindRead | .computeFunding _ => true
  | _ => false

theorem finRange_pairs {α : Type} (l : List α) :
    (List.finRange l.length).map (fun i => (l[i],i.val)) = l.zipIdx := by
  apply List.ext_getElem
  · simp
  · intro n h₁ h₂
    simp [List.getElem_zipIdx]

theorem filterMap_finRange {α β : Type} (l : List α) (f : Nat → α → Option β) :
    (List.finRange l.length).filterMap (fun i => f i.val l[i]) = l.zipIdx.filterMap (fun p => f p.2 p.1) := by
  rw [← finRange_pairs, List.filterMap_map]
  rfl

theorem effectsOf_finRange (command : Command) :
    BendWorldPlan.effectsOf command =
      (List.finRange command.targets.length).filterMap (fun i => step i.val command.targets[i]) := by
  unfold BendWorldPlan.effectsOf
  congr 1

theorem effectsOf_zipIdx (command : Command) :
    BendWorldPlan.effectsOf command = command.targets.zipIdx.filterMap (fun p => step p.2 p.1) := by
  rw [effectsOf_finRange, filterMap_finRange command.targets step]

theorem step_inert {index : Nat} {target : Target} (h : inert target.payload = true) :
    step index target = none := by
  unfold step
  revert h
  cases target.payload <;> simp [inert]

theorem step_verbatim {index : Nat} {target : Target} (h : verbatim target.payload = true) :
    step index target = some ⟨index,target.payload⟩ := by
  unfold step
  revert h
  cases target.payload <;> simp [verbatim]

theorem filterMap_verbatim (targets : List Target) (k : Nat)
    (h : ∀ t ∈ targets, verbatim t.payload = true) :
    (targets.zipIdx k).filterMap (fun p => step p.2 p.1) =
      (targets.zipIdx k).map (fun p => (⟨p.2,p.1.payload⟩ : BendWorldPlan.Effect)) := by
  induction targets generalizing k with
  | nil => rfl
  | cons t rest ih =>
    simp only [List.zipIdx_cons, List.filterMap_cons, List.map_cons]
    rw [step_verbatim (h t (by simp))]
    simp only [List.cons.injEq, true_and]
    exact ih (k+1) (fun t' m => h t' (by simp [m]))

theorem filterMap_inert (targets : List Target) (k : Nat)
    (h : ∀ t ∈ targets, inert t.payload = true) :
    (targets.zipIdx k).filterMap (fun p => step p.2 p.1) = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro p member
  exact step_inert (h p.1 (List.fst_mem_of_mem_zipIdx member))

/-! ## The producer's layout -/

/-- Effect targets first, in source Plan order; then inert targets (read
placeholders for observed roles, the source read, funding last). -/
def layout (effects : List Target) (inertTargets : List Target) : List Target :=
  effects ++ inertTargets

theorem effectsOf_layout (subject : TypedAuthorization.SubjectId) (nonce : Nat)
    (effects inertTargets : List Target) (run : Option Kernel.Run.RunClaim)
    (family : Option NativeInvocationStatement.Family)
    (effectsVerbatim : ∀ t ∈ effects, verbatim t.payload = true)
    (restInert : ∀ t ∈ inertTargets, inert t.payload = true) :
    BendWorldPlan.effectsOf ⟨subject,nonce,layout effects inertTargets,run,family⟩ =
      effects.zipIdx.map (fun p => (⟨p.2,p.1.payload⟩ : BendWorldPlan.Effect)) := by
  rw [effectsOf_zipIdx]
  simp only [layout, List.zipIdx_append, List.filterMap_append]
  rw [filterMap_verbatim effects 0 effectsVerbatim, filterMap_inert inertTargets _ restInert,
    List.append_nil]

/-! ## The refuted design -/

theorem effectsOf_placeholders (command : Command)
    (reads : ∀ t ∈ command.targets, t.payload = .read) :
    BendWorldPlan.effectsOf command = [] := by
  rw [effectsOf_zipIdx]
  exact filterMap_inert command.targets 0 (fun t m => by simp [reads t m, inert])

/-- A draft whose roles are read placeholders cannot carry any effectful plan
through the gate's exact comparison: the producer must lay out final payloads
before any adapter binds. -/
theorem placeholder_draft_refuses_effects {plan : BendWorldPlan.Plan} {command : Command}
    (reads : ∀ t ∈ command.targets, t.payload = .read)
    (accepted : BendWorldPlan.matchesCommand plan command = true) : plan.effects = [] := by
  rw [BendWorldPlan.ordered_payloads_exact accepted, effectsOf_placeholders command reads]

#assert_axioms scalarSource_exact
#assert_axioms resultSource_exact
#assert_axioms combinedSource_exact
#assert_axioms genericSource_exact
#assert_axioms effectsOf_layout
#assert_axioms placeholder_draft_refuses_effects
end Minidregg.Compiler.ObjectiveInvocationLayout
