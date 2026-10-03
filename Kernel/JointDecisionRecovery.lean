/- Required-participant last-YES and private durable recovery for exact Mini
invocation projections. The transition system consumes locally finalized facts;
network signatures and Simplex finality are a separate, unclaimed refinement.
-/
import Kernel.JointInvocationCandidate

namespace Minidregg.Kernel.JointDecisionRecovery

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Kernel.JointInvocationCandidate
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DeclaredResourceController

set_option autoImplicit false

inductive Vote where
  | pending | yes | no
  deriving DecidableEq, Repr

inductive RecoveryPhase where
  | collecting | installing | releasing | complete
  deriving DecidableEq, Repr

/-- Private source-authorized continuation. The access capability and participant
mask must travel inside the protected task; a public receipt is insufficient. -/
structure RecoveryJob where
  accessCapability : List UInt8
  opaqueParticipantMask : List UInt8
  evidence : List (List UInt8)
  originFence : Nat
  phase : RecoveryPhase
  sequence : Nat
  deriving DecidableEq, Repr

/-- All functions have the finite, candidate-owned participant index. Persistence
stores the action journal and replays it, never serializes arbitrary functions. -/
structure State {Custody : Type} (plan : Plan Custody) where
  votes : Fin plan.candidate.participants.length → Vote
  applied : Fin plan.candidate.participants.length → Bool
  certificates : Fin plan.candidate.participants.length → List UInt8
  recovery : Option RecoveryJob
  epoch : Nat
  closed : Bool

def initial {Custody : Type} (plan : Plan Custody) (epoch : Nat) : State plan :=
  ⟨fun _ => .pending, fun _ => false, fun _ => [], none, epoch, false⟩

def Commit {Custody : Type} {plan : Plan Custody} (s : State plan) : Prop :=
  ∀ i, s.votes i = .yes

def Abort {Custody : Type} {plan : Plan Custody} (s : State plan) : Prop :=
  ∃ i, s.votes i = .no

def Ready {Custody : Type} {plan : Plan Custody} (s : State plan) : Prop :=
  Commit s ∧ ∀ i, s.applied i = true

theorem commit_abort_exclusive {Custody : Type} {plan : Plan Custody} (s : State plan) :
    ¬ (Commit s ∧ Abort s) := by
  rintro ⟨commit, i, no⟩
  have yes := commit i
  rw [no] at yes
  cases yes

/-- The final required domain keeps its abort option until all other YES and
recovery body evidence have been retained. `evidence` is opaque here; validating
its bodies/custody is a separate admission prerequisite, not length checking. -/
def LastReady {Custody : Type} {plan : Plan Custody} (s : State plan) : Prop :=
  (∀ i, i ≠ plan.last → s.votes i = .yes) ∧
    match s.recovery with
    | none => False
    | some job => job.originFence = plan.candidate.originFence ∧
        ∀ i, i ≠ plan.last → s.certificates i ≠ [] ∧ s.certificates i ∈ job.evidence

instance {Custody : Type} {plan : Plan Custody} (s : State plan) : Decidable (LastReady s) := by
  unfold LastReady
  cases s.recovery <;> infer_instance

/-- Internal transition: exported entrypoints add actual source admission or
verified remote evidence. A NO is permanent, and no YES is removed by timeout. -/
def decideVote {Custody : Type} {plan : Plan Custody} (s : State plan)
    (i : Fin plan.candidate.participants.length) (v : Vote)
    (certificate : List UInt8) : Option (State plan) :=
  if certificate = [] then none
  else if s.closed then none
  else if s.votes i ≠ .pending then none
  else if v = .pending then none
  else if i = plan.last ∧ v = .yes ∧ ¬ LastReady s then none
  else some { s with votes := fun j => if j = i then v else s.votes j
                     certificates := fun j => if j = i then certificate else s.certificates j }

theorem decideVote_preserves_decided {Custody : Type} {plan : Plan Custody}
    (s t : State plan) (i j : Fin plan.candidate.participants.length) (v : Vote) (certificate : List UInt8)
    (step : decideVote s i v certificate = some t) (decided : s.votes j ≠ .pending) :
    t.votes j = s.votes j := by
  unfold decideVote at step
  split at step
  · cases step
  split at step
  · cases step
  split at step
  · cases step
  next pending =>
    have pi : s.votes i = .pending := by simpa using pending
    split at step
    · cases step
    split at step
    · cases step
    cases Option.some.inj step
    have different : j ≠ i := by intro equal; subst j; exact decided pi
    simp [different]

theorem no_survives_late_yes {Custody : Type} {plan : Plan Custody}
    (s t : State plan) (i j : Fin plan.candidate.participants.length) (certificate : List UInt8)
    (step : decideVote s i .yes certificate = some t) (no : s.votes j = .no) :
    t.votes j = .no := by
  rw [decideVote_preserves_decided s t i j .yes certificate step (by simp [no]), no]

theorem final_no_precludes_commit {Custody : Type} {plan : Plan Custody}
    (s : State plan) (no : s.votes plan.last = .no) : ¬ Commit s := by
  intro commit
  have yes := commit plan.last
  rw [no] at yes
  cases yes

theorem decideVote_final_yes_requires_others {Custody : Type} {plan : Plan Custody}
    (s t : State plan) (certificate : List UInt8)
    (step : decideVote s plan.last .yes certificate = some t) : LastReady s := by
  unfold decideVote at step
  split at step
  · cases step
  split at step
  · cases step
  split at step
  · cases step
  split at step
  · cases step
  split at step
  · cases step
  next ready => simpa using ready

/-- Retain a continuation before promising YES. Replacement preserves the fence,
requires monotone sequence, and cannot silently discard retained evidence. -/
def retainRecovery {Custody : Type} {plan : Plan Custody} (s : State plan)
    (job : RecoveryJob) : Option (State plan) :=
  if job.originFence ≠ plan.candidate.originFence then none
  else match s.recovery with
    | none => some { s with recovery := some job }
    | some old =>
        if old.sequence ≤ job.sequence ∧ old.evidence.IsPrefix job.evidence ∧
            old.accessCapability = job.accessCapability ∧
            old.opaqueParticipantMask = job.opaqueParticipantMask then
          some { s with recovery := some job }
        else none

/-- Installation is enabled only by the common decision, and never fabricates a
new authority choice. Physical install evidence must come from the real receiver. -/
def recordApplied {Custody : Type} {plan : Plan Custody} (s : State plan)
    (i : Fin plan.candidate.participants.length) : Option (State plan) :=
  if ∀ j, s.votes j = .yes then
    some { s with applied := fun j => if j = i then true else s.applied j }
  else none

theorem applied_requires_commit {Custody : Type} {plan : Plan Custody}
    (s t : State plan) (i : Fin plan.candidate.participants.length)
    (step : recordApplied s i = some t) : Commit s := by
  unfold recordApplied at step
  split at step
  next commit => exact commit
  next => cases step

/-- Closing is a terminal semantic cut; the local consensus continuation itself
must still run. It does not erase possible old certificates or recovery jobs. -/
def close {Custody : Type} {plan : Plan Custody} (s : State plan) : State plan :=
  { s with closed := true }

/-- Handoff transports every slot and liability. This is not permission to change
candidate participant identities or silently migrate a private generation. -/
def handoff {Custody : Type} {plan : Plan Custody} (s : State plan)
    (nextEpoch : Nat) : Option (State plan) :=
  if s.closed ∧ s.epoch < nextEpoch then
    some { s with epoch := nextEpoch, closed := false }
  else none

@[simp] theorem close_votes {Custody : Type} {plan : Plan Custody}
    (s : State plan) : (close s).votes = s.votes := rfl

@[simp] theorem close_recovery {Custody : Type} {plan : Plan Custody}
    (s : State plan) : (close s).recovery = s.recovery := rfl

theorem handoff_retains_liabilities {Custody : Type} {plan : Plan Custody}
    (s t : State plan) (epoch : Nat) (step : handoff s epoch = some t) :
    t.votes = s.votes ∧ t.applied = s.applied ∧ t.certificates = s.certificates ∧ t.recovery = s.recovery := by
  unfold handoff at step
  split at step
  · cases Option.some.inj step; exact ⟨rfl, rfl, rfl, rfl⟩
  · cases step

/-- Every permitted semantic/recovery transition, including restart handoff. -/
inductive Step {Custody : Type} {plan : Plan Custody} : State plan → State plan → Prop
  | vote (s t : State plan) (i : Fin plan.candidate.participants.length)
      (v : Vote) (certificate : List UInt8)
      (result : decideVote s i v certificate = some t) : Step s t
  | recovery (s t : State plan) (job : RecoveryJob)
      (result : retainRecovery s job = some t) : Step s t
  | applied (s t : State plan) (i : Fin plan.candidate.participants.length)
      (result : recordApplied s i = some t) : Step s t
  | close (s : State plan) : Step s (JointDecisionRecovery.close s)
  | handoff (s t : State plan) (epoch : Nat)
      (result : JointDecisionRecovery.handoff s epoch = some t) : Step s t

theorem Step.preserves_decided {Custody : Type} {plan : Plan Custody}
    {s t : State plan} (step : Step s t) (i : Fin plan.candidate.participants.length)
    (decided : s.votes i ≠ .pending) : t.votes i = s.votes i := by
  cases step with
  | vote t j v certificate result =>
      exact decideVote_preserves_decided s t j i v certificate result decided
  | recovery t job result =>
      unfold retainRecovery at result
      split at result
      · cases result
      split at result
      · cases Option.some.inj result; rfl
      · split at result
        · cases Option.some.inj result; rfl
        · cases result
  | applied t j result =>
      unfold recordApplied at result
      split at result
      · cases Option.some.inj result; rfl
      · cases result
  | close => rfl
  | handoff t epoch result =>
      exact congrFun (handoff_retains_liabilities s t epoch result).1 i

inductive Trace {Custody : Type} {plan : Plan Custody} : State plan → State plan → Prop
  | refl (s : State plan) : Trace s s
  | next {s middle t : State plan} (prior : Trace s middle)
      (step : Step middle t) : Trace s t

theorem Trace.preserves_decided {Custody : Type} {plan : Plan Custody}
    {s t : State plan} (trace : Trace s t) (i : Fin plan.candidate.participants.length)
    (decided : s.votes i ≠ .pending) : t.votes i = s.votes i := by
  induction trace with
  | refl => rfl
  | next prior step ih =>
      exact (step.preserves_decided i (by rw [ih]; exact decided)).trans ih

/-- Delayed certificates, recovery and epoch changes cannot revive an aborted
candidate: the statement is over every finite execution, not one tally. -/
theorem abort_stable_under_trace {Custody : Type} {plan : Plan Custody}
    {s t : State plan} (trace : Trace s t) (aborted : Abort s) : Abort t ∧ ¬ Commit t := by
  obtain ⟨i, no⟩ := aborted
  have noLater : t.votes i = .no := by
    rw [trace.preserves_decided i (by simp [no]), no]
  refine ⟨⟨i, noLater⟩, ?_⟩
  intro commit
  exact commit_abort_exclusive t ⟨commit, i, noLater⟩

/-- A source-admitted proposal, NOT a final YES or a reservation grant. Native
integration must atomically compare the exact source image, acquire the source-
authorized reservation and order it before emitting finality evidence. -/
structure LocalYesProposal where
  participant : Nat
  candidateBytes : List UInt8
  sourceImageBytes : List UInt8
  projectionBytes : List UInt8
  deriving DecidableEq, Repr

def proposeLocalYes {Custody F : Type} [Field F] [DecidableEq F]
    (custodyCodec : Minidregg.Compiler.Tower256ConcreteBackend.StreamCodec Custody)
    {plan : Plan Custody} (i : Fin plan.candidate.participants.length)
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {command : Command} {signed : SignedCommand}
    (_admission : CurrentAdmission deployment profile ambient durable command signed
      plan.candidate.participants[i]) : Option LocalYesProposal :=
  if plan.candidate.commandBytes = commandCodec.encode command ∧
      plan.candidate.semantics = profile.semantics then
    some ⟨i.val, (candidateStream custodyCodec).encode plan.candidate,
      DurableReceiverCodec.encode durable.image,
      (projectionStream custodyCodec).encode plan.candidate.participants[i]⟩
  else none

/-- Successful physical installation is the existing exact durable execute, not
an alternate root updater. The admission/reservation layer must establish its
current preflight; a failed install remains a recovery liability, never Applied. -/
def installProjection {Custody : Type} {plan : Plan Custody} (s : State plan)
    (i : Fin plan.candidate.participants.length)
    (before : DataSnapshot ResourceBirthCodec.rootBytes) :
    Option (State plan × DataSnapshot ResourceBirthCodec.rootBytes) := do
  let intent ← plan.candidate.participants[i].intent.bind? ResourceBirthCodec.rootBytes
  let marked ← recordApplied s i
  match DurableDataIntent.execute .complete before intent with
  | .accepted after => some (marked, after)
  | _ => none

end Minidregg.Kernel.JointDecisionRecovery
