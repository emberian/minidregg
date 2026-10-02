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

/-- **Every checked leg satisfies its installed law** on the controller's own step context. -/
theorem checked_leg_policy_eval
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command} {envelope : List UInt8}
    (leg : CheckedLeg prepared tuple incidence envelope) :
    ∃ committed, (policyConfig prepared tuple incidence).registry.resolve
        (tuple.request incidence).2.policyId (tuple.request incidence).2.policyRevision = some committed ∧
      eval committed.record.predicate (step prepared tuple incidence).oldState
        (step prepared tuple incidence).newState = true := by
  have authorized : Authorized (policyConfig prepared tuple incidence).portal
      prepared.authority.snapshot.authState (tuple.request incidence).2 := by
    with_unfolding_all exact leg.authorization
  exact authorized_policy_eval _ _ rfl authorized

/-- info: 'Minidregg.Kernel.LawHistory.Accepted.tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.tail
/-- info: 'Minidregg.Kernel.LawHistory.Accepted.head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.head
/-- info: 'Minidregg.Kernel.LawHistory.authorized_policy_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authorized_policy_eval
/-- info: 'Minidregg.Kernel.LawHistory.checked_leg_policy_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_leg_policy_eval

end Minidregg.Kernel.LawHistory
