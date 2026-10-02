/-
Shared accepted histories and the bridge from a checked resource leg to its
committed law. Sheet, item and story laws use this one kernel-level contract.
-/
import Kernel.LawView

namespace Minidregg.Kernel.LawHistory

open Minidregg.Pred (Pred eval)
open Minidregg.Kernel.LawView (Turn admits)
open Minidregg.Kernel.DeclaredResourceProjection (Values)
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- The (pre, turn) pairs of a log started at `v`: each turn's pre-state is the previous post. -/
def stepsOf : Values → List Turn → List (Values × Turn)
  | _, [] => []
  | v, t :: ts => (v, t) :: stepsOf t.post ts

/-- The field store after the whole log. -/
def final : Values → List Turn → Values
  | v, [] => v
  | _, t :: ts => final t.post ts

/-- A cell's write history: every step is a mutate (verb 2) the law admits from the state the
previous step left. (The durable CAS is what makes each step's pre the previous post; a turn
prepared against an older root is refused `staleReadGuard` before the law is read,
`DurableDataIntent.stale_read_guard_rejected`.) -/
def Accepted (law : Pred) (v : Values) (ts : List Turn) : Prop :=
  ∀ s ∈ stepsOf v ts, s.2.verb = 2 ∧ admits law s.1 s.2 = true

instance (law : Pred) (v : Values) (ts : List Turn) : Decidable (Accepted law v ts) := by
  unfold Accepted; infer_instance

theorem Accepted.tail {law : Pred} {v : Values} {t : Turn} {ts : List Turn}
    (h : Accepted law v (t :: ts)) : Accepted law t.post ts :=
  fun s hs => h s (by simp [stepsOf, hs])

theorem Accepted.head {law : Pred} {v : Values} {t : Turn} {ts : List Turn}
    (h : Accepted law v (t :: ts)) : t.verb = 2 ∧ admits law v t = true :=
  h (v, t) (by simp [stepsOf])

/-- Any value of the canonical `Authorized` type forces the resolved committed predicate to hold on
the bound step context. -/
theorem authorized_policy_eval {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) (context : PolicyStepContext)
    (canonical : config.stepBinding = .canonical context)
    {state : AuthState} {kind : ResourceKind} {request : Request kind}
    (authorized : Authorized config.portal state request) :
    ∃ committed, config.registry.resolve request.policyId request.policyRevision = some committed ∧
      eval committed.record.predicate context.oldState context.newState = true := by
  have verified := authorized.policyVerified
  rw [portal_verifyCommittedPolicy, Bool.and_eq_true] at verified
  exact (canonical_context_verifies_sound context canonical verified.2).2.2.2

variable {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient}
  {durable : Durable} {command : Command}

/-- A source-authenticated component of the effective closure whose selector
applies to this exact step. Extra inherited restrictions remain in the closure;
there is no requirement that the whole conjunction equal the application law. -/
def ActiveComponent (config : ComposedPolicyAdmission.Config F) (law : Pred) : Prop :=
  ∀ graph : PolicyComponentResolution.LoadedGraph config.snapshot config.store
      config.profile.semantics config.target config.additional,
    PolicyComponentResolution.loadTarget config.snapshot config.store config.profile.semantics
      config.target config.resolutionBudget config.additional = .ok graph →
    ∃ node ∈ Minidregg.Theory.LawComposition.canonicalOrder graph.resolved.postorder,
      node.component.predicate = law ∧
      eval node.component.selector.predicate config.step.oldState config.step.newState = true

/-- Derive the application premise from the cached, authenticated graph.
Only source identity and the component selector are inspected here; the actual
predicate verdict remains the shared admission evaluator's responsibility. -/
def checkActiveComponent {config : ComposedPolicyAdmission.Config F}
    (resolved : ComposedPolicyAdmission.PreparedLaw config) (law : Pred) :
    Option (PLift (ActiveComponent config law)) :=
  let nodes := Minidregg.Theory.LawComposition.canonicalOrder resolved.graph.resolved.postorder
  if present : nodes.any (fun node => decide (node.component.predicate = law) &&
      eval node.component.selector.predicate config.step.oldState config.step.newState) = true then
    some ⟨by
      intro graph loaded
      have same : resolved.graph = graph := Except.ok.inj (resolved.graphExact.symm.trans loaded)
      subst graph
      obtain ⟨node, member, componentMatches⟩ := List.any_eq_true.mp present
      rw [Bool.and_eq_true] at componentMatches
      exact ⟨node, member, of_decide_eq_true componentMatches.1, componentMatches.2⟩⟩
  else none

/-- A selected component follows from the effective conjunction at the same
source snapshot and exact step. No additional inherited restriction is removed. -/
theorem ActiveComponent.evaluated {config : ComposedPolicyAdmission.Config F} {law : Pred}
    (installed : ActiveComponent config law)
    (graph : PolicyComponentResolution.LoadedGraph config.snapshot config.store
      config.profile.semantics config.target config.additional)
    (loaded : PolicyComponentResolution.loadTarget config.snapshot config.store config.profile.semantics
      config.target config.resolutionBudget config.additional = .ok graph)
    (holds : eval (ResolvedLawCompilation.predicate graph.resolved)
      config.step.oldState config.step.newState = true) :
    eval law config.step.oldState config.step.newState = true := by
  obtain ⟨node, member, predicateExact, selected⟩ := installed graph loaded
  have guarded := Minidregg.Theory.LawComposition.inherited_never_widens
    (Minidregg.Theory.LawComposition.canonicalOrder graph.resolved.postorder)
    config.step.oldState config.step.newState holds node member
  simpa [Minidregg.Theory.LawComposition.Component.guarded,
    Minidregg.Pred.eval_any, Minidregg.Pred.eval_not, selected, predicateExact] using guarded

/-- Shared assurance bridge for every consumer of the composed portal, including
policy installation. The supplied authorization checks the complete closure. -/
theorem authorized_component_eval (config : ComposedPolicyAdmission.Config F)
    {kind : ResourceKind} (request : Request kind)
    (authorized : Authorized config.portal config.snapshot.authState request)
    (law : Pred) (installed : ActiveComponent config law) :
    eval law config.step.oldState config.step.newState = true := by
  obtain ⟨graph, loaded, holds⟩ :=
    ComposedPolicyAdmission.authorized_effective_law config request authorized
  exact installed.evaluated graph loaded holds

/-- Every checked leg satisfies the complete authenticated effective law on
exactly the controller's old/new step, including active ambient restrictions. -/
theorem checked_leg_policy_eval
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command} {envelope : List UInt8}
    (leg : CheckedLeg prepared tuple incidence envelope) :
    let config := policyConfig prepared tuple incidence
    ∃ graph : PolicyComponentResolution.LoadedGraph config.snapshot config.store
        config.profile.semantics config.target config.additional,
      PolicyComponentResolution.loadTarget config.snapshot config.store config.profile.semantics
        config.target config.resolutionBudget config.additional = .ok graph ∧
      eval (ResolvedLawCompilation.predicate graph.resolved)
        (step prepared tuple incidence).oldState (step prepared tuple incidence).newState = true := by
  have authorized : Authorized (policyConfig prepared tuple incidence).portal
      prepared.authority.snapshot.authState (tuple.request incidence).2 := by
    with_unfolding_all exact leg.authorization
  exact ComposedPolicyAdmission.authorized_effective_law
    (policyConfig prepared tuple incidence) (tuple.request incidence).2 authorized

/-- An admitted intersection satisfies every authenticated selected component,
so application assurances survive additional room, kind or explicit imports. -/
theorem checked_leg_component_eval
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command} {envelope : List UInt8}
    (leg : CheckedLeg prepared tuple incidence envelope) (law : Pred)
    (installed : ActiveComponent (policyConfig prepared tuple incidence) law) :
    eval law (step prepared tuple incidence).oldState
      (step prepared tuple incidence).newState = true := by
  obtain ⟨graph, resolved, holds⟩ := checked_leg_policy_eval leg
  exact installed.evaluated graph resolved holds

/-- info: 'Minidregg.Kernel.LawHistory.Accepted.tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.tail
/-- info: 'Minidregg.Kernel.LawHistory.Accepted.head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.head
/-- info: 'Minidregg.Kernel.LawHistory.authorized_policy_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authorized_policy_eval
/-- info: 'Minidregg.Kernel.LawHistory.checked_leg_policy_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_leg_policy_eval

/-- info: 'Minidregg.Kernel.LawHistory.checked_leg_component_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_leg_component_eval

/-- info: 'Minidregg.Kernel.LawHistory.ActiveComponent.evaluated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ActiveComponent.evaluated
/-- info: 'Minidregg.Kernel.LawHistory.authorized_component_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authorized_component_eval

end Minidregg.Kernel.LawHistory
