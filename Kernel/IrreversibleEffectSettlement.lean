/-
# Kernel.IrreversibleEffectSettlement -- fail-closed external effect settlement

An accepted semantic turn may ask the outside world to do something which a
cell patch cannot roll back: send a message, charge a card, actuate a device,
publish a packet, or call an administrative API.  The durable commit protocol
already gives roots, nullifiers, budget, history, and retry records one atomic
model transition.  It deliberately does not turn an executor's claim about
the outside world into a theorem.

This module supplies the smaller missing semantics:

* an exact first-order grant authorizes one principal, effect class, target,
  action, time window, attempt bound, and optional compensation;
* handler observations are proof-relevant and indexed by the exact forward or
  compensating command;
* only a definitely performed forward command against the still-current
  logical pre-root can release the intended post-root;
* refusal, uncertainty, failed/uncertain compensation, and a stale pre-root
  preserve the current logical root and emit an auditable receipt;
* a compensation receipt means that the exact compensating command was
  observed as performed.  It does NOT assert that the physical world was
  restored.  Such a claim needs an application-specific physical relation.

A later section states that ceiling as an explicit implementation-refinement
premise over real physical states and steps.  This file constructs no instance
for a database, payment rail, mail server, device, or network.  It does
construct one for a toy keyed-idempotent target (`KeyedTarget`, class 1 of the
taxonomy there), and `Settlement.reconcile` resolves a forward quarantine with
new evidence for the same command.
-/
import Mathlib.Data.Finset.Basic
import Theory.AssertAxioms

namespace Minidregg.Kernel.IrreversibleEffectSettlement

set_option autoImplicit false

universe uTx uGrant uPrincipal uClass uTarget uAction uComp uRoot
  uResult uFailure uUncertainty uEvidence uPhysical uStep

/-! ## Exact intent and finite authority -/

/-- One externally visible action requested by an already accepted semantic
turn.  `expectedPreRoot` and `exactPostRoot` bind release back to that turn;
the handler does not get to report alternate logical roots. -/
structure Intent
    (TxId : Type uTx) (Principal : Type uPrincipal)
    (EffectClass : Type uClass) (Target : Type uTarget)
    (Action : Type uAction) (Compensation : Type uComp)
    (Root : Type uRoot) where
  transactionId : TxId
  principal : Principal
  effectClass : EffectClass
  target : Target
  action : Action
  compensation : Option Compensation
  height : Nat
  attempt : Nat
  expectedPreRoot : Root
  exactPostRoot : Root

/-- A finite capability for irreversible work.  Actions and compensations are
exact values, not executor-supplied predicates or unbound string scopes. -/
structure Grant
    (GrantId : Type uGrant) (Principal : Type uPrincipal)
    (EffectClass : Type uClass) (Target : Type uTarget)
    (Action : Type uAction) (Compensation : Type uComp) where
  grantId : GrantId
  principal : Principal
  effectClass : EffectClass
  target : Target
  actions : Finset Action
  compensations : Finset Compensation
  notBefore : Nat
  notAfter : Nat
  maxAttempt : Nat

namespace Grant

variable
    {TxId : Type uTx} {GrantId : Type uGrant}
    {Principal : Type uPrincipal} {EffectClass : Type uClass}
    {Target : Type uTarget} {Action : Type uAction}
    {Compensation : Type uComp} {Root : Type uRoot}

/-- The complete pure admission relation.  In particular, an exact optional
compensation is authorized at the same time as the forward command. -/
structure Authorizes
    (grant : Grant GrantId Principal EffectClass Target Action Compensation)
    (intent : Intent TxId Principal EffectClass Target Action Compensation Root) :
    Type (max uTx uGrant uPrincipal uClass uTarget uAction uComp uRoot) where
  principal : intent.principal = grant.principal
  effectClass : intent.effectClass = grant.effectClass
  target : intent.target = grant.target
  action : intent.action ∈ grant.actions
  validFrom : grant.notBefore ≤ intent.height
  validUntil : intent.height ≤ grant.notAfter
  attempt : intent.attempt ≤ grant.maxAttempt
  compensation : forall request,
    intent.compensation = some request -> request ∈ grant.compensations

inductive RejectReason
  | wrongPrincipal
  | wrongEffectClass
  | wrongTarget
  | actionOutsideScope
  | tooEarly
  | expired
  | attemptExceeded
  | compensationOutsideScope
  deriving DecidableEq, Repr

/-- Executable, ordered, fail-closed authorization.  Success returns the pure
relation indexed by these exact grant and intent values. -/
def authorize
    [DecidableEq Principal] [DecidableEq EffectClass] [DecidableEq Target]
    [DecidableEq Action] [DecidableEq Compensation]
    (grant : Grant GrantId Principal EffectClass Target Action Compensation)
    (intent : Intent TxId Principal EffectClass Target Action Compensation Root) :
    Except RejectReason (grant.Authorizes intent) :=
  if hPrincipal : intent.principal = grant.principal then
    if hClass : intent.effectClass = grant.effectClass then
      if hTarget : intent.target = grant.target then
        if hAction : intent.action ∈ grant.actions then
          if hFrom : grant.notBefore ≤ intent.height then
            if hUntil : intent.height ≤ grant.notAfter then
              if hAttempt : intent.attempt ≤ grant.maxAttempt then
                match hCompensation : intent.compensation with
                | none =>
                    .ok
                      { principal := hPrincipal
                        effectClass := hClass
                        target := hTarget
                        action := hAction
                        validFrom := hFrom
                        validUntil := hUntil
                        attempt := hAttempt
                        compensation := by
                          intro request exact
                          simp [hCompensation] at exact }
                | some request =>
                    if hAllowed : request ∈ grant.compensations then
                      .ok
                        { principal := hPrincipal
                          effectClass := hClass
                          target := hTarget
                          action := hAction
                          validFrom := hFrom
                          validUntil := hUntil
                          attempt := hAttempt
                          compensation := by
                            intro other exact
                            rw [hCompensation] at exact
                            cases exact
                            exact hAllowed }
                    else
                      .error .compensationOutsideScope
              else
                .error .attemptExceeded
            else
              .error .expired
          else
            .error .tooEarly
        else
          .error .actionOutsideScope
      else
        .error .wrongTarget
    else
      .error .wrongEffectClass
  else
    .error .wrongPrincipal

end Grant

/-! ## Exact commands and handler observations -/

/-- The handler is invoked either for the exact forward intent or for one
explicit compensation named by that intent. -/
inductive Command
    (TxId : Type uTx) (Principal : Type uPrincipal)
    (EffectClass : Type uClass) (Target : Type uTarget)
    (Action : Type uAction) (Compensation : Type uComp)
    (Root : Type uRoot) where
  | forward
      (intent : Intent TxId Principal EffectClass Target Action Compensation Root)
  | compensate
      (intent : Intent TxId Principal EffectClass Target Action Compensation Root)
      (request : Compensation)

/-- `notPerformed` is stronger than failure: it claims no externally visible
forward action happened.  Anything a handler cannot establish at that strength
must be `indeterminate`, which the logical layer quarantines. -/
inductive HandlerObservation
    (Result : Type uResult) (Failure : Type uFailure)
    (Uncertainty : Type uUncertainty) where
  | notPerformed (failure : Failure)
  | performed (result : Result)
  | indeterminate (uncertainty : Uncertainty)

/-- The irreducible boundary.  Evidence is indexed by the exact command and
observation.  A production backend must connect this family to its physical
implementation through `ImplementationRefinement` below. -/
structure HandlerBoundary
    (TxId : Type uTx) (Principal : Type uPrincipal)
    (EffectClass : Type uClass) (Target : Type uTarget)
    (Action : Type uAction) (Compensation : Type uComp)
    (Root : Type uRoot)
    (Result : Type uResult) (Failure : Type uFailure)
    (Uncertainty : Type uUncertainty) where
  Evidence :
    Command TxId Principal EffectClass Target Action Compensation Root ->
      HandlerObservation Result Failure Uncertainty -> Type uEvidence

/-- One evidence-backed observation, kept dependent so evidence for a
different command or different result is unusable here. -/
structure Observed
    {TxId : Type uTx} {Principal : Type uPrincipal}
    {EffectClass : Type uClass} {Target : Type uTarget}
    {Action : Type uAction} {Compensation : Type uComp}
    {Root : Type uRoot}
    {Result : Type uResult} {Failure : Type uFailure}
    {Uncertainty : Type uUncertainty}
    (boundary : HandlerBoundary TxId Principal EffectClass Target Action
      Compensation Root Result Failure Uncertainty)
    (command : Command TxId Principal EffectClass Target Action Compensation Root) where
  observation : HandlerObservation Result Failure Uncertainty
  evidence : boundary.Evidence command observation

/-! ## Total settlement and exact receipts -/

/-- After a definitely performed forward action, the coordinator either tries
to release the logical post or invokes the exact pre-authorized compensation.
The compensation observation is included, so settlement never infers it from
a timeout or success Boolean. -/
inductive Plan
    {TxId : Type uTx} {Principal : Type uPrincipal}
    {EffectClass : Type uClass} {Target : Type uTarget}
    {Action : Type uAction} {Compensation : Type uComp}
    {Root : Type uRoot}
    {Result : Type uResult} {Failure : Type uFailure}
    {Uncertainty : Type uUncertainty}
    (boundary : HandlerBoundary TxId Principal EffectClass Target Action
      Compensation Root Result Failure Uncertainty)
    (intent : Intent TxId Principal EffectClass Target Action Compensation Root) where
  | commit
  | compensate (request : Compensation)
      (exact : intent.compensation = some request)
      (observed : Observed boundary (.compensate intent request))

inductive Status
  | committed
  | refused
  | compensated
  | quarantinedForward
  | quarantinedStale
  | quarantinedCompensation
  deriving DecidableEq, Repr

/-- The proof-relevant settlement receipt.  Only `committed` exposes the
intended post-root.  Every other constructor leaves the current logical root
unchanged.  `compensated` records two performed commands but intentionally has
no field claiming equality of physical worlds before and after them. -/
inductive Settlement
    {TxId : Type uTx} {GrantId : Type uGrant}
    {Principal : Type uPrincipal} {EffectClass : Type uClass}
    {Target : Type uTarget} {Action : Type uAction}
    {Compensation : Type uComp} {Root : Type uRoot}
    {Result : Type uResult} {Failure : Type uFailure}
    {Uncertainty : Type uUncertainty}
    (boundary : HandlerBoundary TxId Principal EffectClass Target Action
      Compensation Root Result Failure Uncertainty)
    (grant : Grant GrantId Principal EffectClass Target Action Compensation)
    (intent : Intent TxId Principal EffectClass Target Action Compensation Root)
    (authorized : grant.Authorizes intent) (currentRoot : Root) where
  | committed (result : Result)
      (forwardEvidence : boundary.Evidence (.forward intent) (.performed result))
      (fresh : currentRoot = intent.expectedPreRoot)
  | refused (failure : Failure)
      (forwardEvidence : boundary.Evidence (.forward intent) (.notPerformed failure))
  | compensated (result compensationResult : Result)
      (forwardEvidence : boundary.Evidence (.forward intent) (.performed result))
      (request : Compensation) (exact : intent.compensation = some request)
      (compensationEvidence :
        boundary.Evidence (.compensate intent request) (.performed compensationResult))
  | quarantinedForward (uncertainty : Uncertainty)
      (forwardEvidence :
        boundary.Evidence (.forward intent) (.indeterminate uncertainty))
  | quarantinedStale (result : Result)
      (forwardEvidence : boundary.Evidence (.forward intent) (.performed result))
      (stale : currentRoot ≠ intent.expectedPreRoot)
  | quarantinedCompensationNotPerformed (result : Result)
      (forwardEvidence : boundary.Evidence (.forward intent) (.performed result))
      (request : Compensation) (exact : intent.compensation = some request)
      (failure : Failure)
      (compensationEvidence :
        boundary.Evidence (.compensate intent request) (.notPerformed failure))
  | quarantinedCompensationIndeterminate (result : Result)
      (forwardEvidence : boundary.Evidence (.forward intent) (.performed result))
      (request : Compensation) (exact : intent.compensation = some request)
      (uncertainty : Uncertainty)
      (compensationEvidence :
        boundary.Evidence (.compensate intent request) (.indeterminate uncertainty))

namespace Settlement

variable
    {TxId : Type uTx} {GrantId : Type uGrant}
    {Principal : Type uPrincipal} {EffectClass : Type uClass}
    {Target : Type uTarget} {Action : Type uAction}
    {Compensation : Type uComp} {Root : Type uRoot}
    {Result : Type uResult} {Failure : Type uFailure}
    {Uncertainty : Type uUncertainty}
    {boundary : HandlerBoundary TxId Principal EffectClass Target Action
      Compensation Root Result Failure Uncertainty}
    {grant : Grant GrantId Principal EffectClass Target Action Compensation}
    {intent : Intent TxId Principal EffectClass Target Action Compensation Root}
    {authorized : grant.Authorizes intent} {currentRoot : Root}

def status : Settlement boundary grant intent authorized currentRoot -> Status
  | .committed .. => .committed
  | .refused .. => .refused
  | .compensated .. => .compensated
  | .quarantinedForward .. => .quarantinedForward
  | .quarantinedStale .. => .quarantinedStale
  | .quarantinedCompensationNotPerformed .. => .quarantinedCompensation
  | .quarantinedCompensationIndeterminate .. => .quarantinedCompensation

/-- User-visible logical state.  Audit receipt persistence is a separate
durable lane; an uncertain physical outcome never releases a candidate post. -/
def logicalRoot :
    Settlement boundary grant intent authorized currentRoot -> Root
  | .committed .. => intent.exactPostRoot
  | .refused .. => currentRoot
  | .compensated .. => currentRoot
  | .quarantinedForward .. => currentRoot
  | .quarantinedStale .. => currentRoot
  | .quarantinedCompensationNotPerformed .. => currentRoot
  | .quarantinedCompensationIndeterminate .. => currentRoot

def forwardObservation :
    Settlement boundary grant intent authorized currentRoot ->
      HandlerObservation Result Failure Uncertainty
  | .committed result .. => .performed result
  | .refused failure .. => .notPerformed failure
  | .compensated result .. => .performed result
  | .quarantinedForward uncertainty .. => .indeterminate uncertainty
  | .quarantinedStale result .. => .performed result
  | .quarantinedCompensationNotPerformed result .. => .performed result
  | .quarantinedCompensationIndeterminate result .. => .performed result

def compensationObservation :
    Settlement boundary grant intent authorized currentRoot ->
      Option (HandlerObservation Result Failure Uncertainty)
  | .compensated _ compensationResult .. => some (.performed compensationResult)
  | .quarantinedCompensationNotPerformed _ _ _ _ failure _ =>
      some (.notPerformed failure)
  | .quarantinedCompensationIndeterminate _ _ _ _ uncertainty _ =>
      some (.indeterminate uncertainty)
  | _ => none

/-- First-order projection suitable for the durable history/event lane.  It
binds the exact transaction, grant, action, optional compensation, handler
observations, logical before/after roots, and final status. -/
structure Receipt where
  transactionId : TxId
  grantId : GrantId
  principal : Principal
  effectClass : EffectClass
  target : Target
  action : Action
  compensation : Option Compensation
  forward : HandlerObservation Result Failure Uncertainty
  compensationOutcome : Option (HandlerObservation Result Failure Uncertainty)
  logicalBefore : Root
  logicalAfter : Root
  intendedPost : Root
  status : Status

def toReceipt
    (settlement : Settlement boundary grant intent authorized currentRoot) :
    Receipt (TxId := TxId) (GrantId := GrantId) (Principal := Principal)
      (EffectClass := EffectClass) (Target := Target) (Action := Action)
      (Compensation := Compensation) (Root := Root) (Result := Result)
      (Failure := Failure) (Uncertainty := Uncertainty) :=
  { transactionId := intent.transactionId
    grantId := grant.grantId
    principal := intent.principal
    effectClass := intent.effectClass
    target := intent.target
    action := intent.action
    compensation := intent.compensation
    forward := settlement.forwardObservation
    compensationOutcome := settlement.compensationObservation
    logicalBefore := currentRoot
    logicalAfter := settlement.logicalRoot
    intendedPost := intent.exactPostRoot
    status := settlement.status }

@[simp] theorem receipt_transaction_exact
    (settlement : Settlement boundary grant intent authorized currentRoot) :
    settlement.toReceipt.transactionId = intent.transactionId := rfl

@[simp] theorem receipt_action_exact
    (settlement : Settlement boundary grant intent authorized currentRoot) :
    settlement.toReceipt.action = intent.action := rfl

@[simp] theorem receipt_logical_after_exact
    (settlement : Settlement boundary grant intent authorized currentRoot) :
    settlement.toReceipt.logicalAfter = settlement.logicalRoot := rfl

/-- Central fail-closed logical atomicity: every settlement exposes either the
complete current root or the complete intended post-root. -/
theorem no_partial_logical_commit
    (settlement : Settlement boundary grant intent authorized currentRoot) :
    settlement.logicalRoot = currentRoot \/
      settlement.logicalRoot = intent.exactPostRoot := by
  cases settlement <;> simp [logicalRoot]

/-- Compensation is a recorded mitigation, never permission to expose the
forward logical post. -/
@[simp] theorem compensated_preserves_current
    (result compensationResult : Result)
    (forwardEvidence : boundary.Evidence (.forward intent) (.performed result))
    (request : Compensation) (exact : intent.compensation = some request)
    (compensationEvidence :
      boundary.Evidence (.compensate intent request) (.performed compensationResult)) :
    logicalRoot (.compensated result compensationResult forwardEvidence request exact
      compensationEvidence :
      Settlement boundary grant intent authorized currentRoot) = currentRoot :=
  rfl

end Settlement

/-! ## Executable coordinator -/

/-- Total settlement over exact observations.  Authorization is already in the
type.  The only runtime comparison is the last-moment logical pre-root check;
if it has gone stale after the physical action, the action is quarantined and
the current logical root remains visible. -/
def settle
    {TxId : Type uTx} {GrantId : Type uGrant}
    {Principal : Type uPrincipal} {EffectClass : Type uClass}
    {Target : Type uTarget} {Action : Type uAction}
    {Compensation : Type uComp} {Root : Type uRoot}
    {Result : Type uResult} {Failure : Type uFailure}
    {Uncertainty : Type uUncertainty}
    [DecidableEq Root]
    (boundary : HandlerBoundary TxId Principal EffectClass Target Action
      Compensation Root Result Failure Uncertainty)
    (grant : Grant GrantId Principal EffectClass Target Action Compensation)
    (intent : Intent TxId Principal EffectClass Target Action Compensation Root)
    (authorized : grant.Authorizes intent) (currentRoot : Root)
    (forward : Observed boundary (.forward intent))
    (plan : Plan boundary intent) :
    Settlement boundary grant intent authorized currentRoot :=
  match forward with
  | ⟨.notPerformed failure, evidence⟩ => .refused failure evidence
  | ⟨.indeterminate uncertainty, evidence⟩ =>
      .quarantinedForward uncertainty evidence
  | ⟨.performed result, forwardEvidence⟩ =>
      match plan with
      | .commit =>
          if fresh : currentRoot = intent.expectedPreRoot then
            .committed result forwardEvidence fresh
          else
            .quarantinedStale result forwardEvidence fresh
      | .compensate request exact observed =>
          match observed with
          | ⟨.performed compensationResult, compensationEvidence⟩ =>
              .compensated result compensationResult forwardEvidence request exact
                compensationEvidence
          | ⟨.notPerformed failure, compensationEvidence⟩ =>
              .quarantinedCompensationNotPerformed result forwardEvidence request exact
                failure compensationEvidence
          | ⟨.indeterminate uncertainty, compensationEvidence⟩ =>
              .quarantinedCompensationIndeterminate result forwardEvidence request exact
                uncertainty compensationEvidence

/-! ## Explicit physical refinement ceiling -/

/-- One entry in the abstract handler trace.  The trace records observations;
it does not equip `performed compensation` with a universal inverse law. -/
structure TraceEntry
    (TxId : Type uTx) (Principal : Type uPrincipal)
    (EffectClass : Type uClass) (Target : Type uTarget)
    (Action : Type uAction) (Compensation : Type uComp)
    (Root : Type uRoot)
    (Result : Type uResult) (Failure : Type uFailure)
    (Uncertainty : Type uUncertainty) where
  command : Command TxId Principal EffectClass Target Action Compensation Root
  observation : HandlerObservation Result Failure Uncertainty

/-- A real handler earns use of `Observed` only through an application-specific
simulation from its physical state and steps to this evidence-backed trace.
The relation `Represents` is where a payment rail, mail server, filesystem, or
device must say what its physical observations mean. -/
structure ImplementationRefinement
    {TxId : Type uTx} {Principal : Type uPrincipal}
    {EffectClass : Type uClass} {Target : Type uTarget}
    {Action : Type uAction} {Compensation : Type uComp}
    {Root : Type uRoot}
    {Result : Type uResult} {Failure : Type uFailure}
    {Uncertainty : Type uUncertainty}
    (boundary : HandlerBoundary TxId Principal EffectClass Target Action
      Compensation Root Result Failure Uncertainty)
    (PhysicalState : Type uPhysical)
    (PhysicalStep : PhysicalState ->
      Command TxId Principal EffectClass Target Action Compensation Root ->
      PhysicalState -> Type uStep)
    (Represents : PhysicalState ->
      List (TraceEntry TxId Principal EffectClass Target Action Compensation
        Root Result Failure Uncertainty) -> Prop) : Prop where
  simulates : forall {physicalBefore physicalAfter trace command},
    Represents physicalBefore trace ->
    PhysicalStep physicalBefore command physicalAfter ->
    exists observed : Observed boundary command,
      Represents physicalAfter
        (trace ++ [{ command := command
                     observation := observed.observation }])

/-- Conditional extraction of an exact model observation from one physical
step.  No theorem in this module manufactures the refinement premise. -/
theorem physical_step_observed
    {TxId : Type uTx} {Principal : Type uPrincipal}
    {EffectClass : Type uClass} {Target : Type uTarget}
    {Action : Type uAction} {Compensation : Type uComp}
    {Root : Type uRoot}
    {Result : Type uResult} {Failure : Type uFailure}
    {Uncertainty : Type uUncertainty}
    {boundary : HandlerBoundary TxId Principal EffectClass Target Action
      Compensation Root Result Failure Uncertainty}
    {PhysicalState : Type uPhysical}
    {PhysicalStep : PhysicalState ->
      Command TxId Principal EffectClass Target Action Compensation Root ->
      PhysicalState -> Type uStep}
    {Represents : PhysicalState ->
      List (TraceEntry TxId Principal EffectClass Target Action Compensation
        Root Result Failure Uncertainty) -> Prop}
    (refinement : ImplementationRefinement boundary PhysicalState PhysicalStep Represents)
    {physicalBefore physicalAfter : PhysicalState}
    {trace : List (TraceEntry TxId Principal EffectClass Target Action Compensation
      Root Result Failure Uncertainty)}
    {command : Command TxId Principal EffectClass Target Action Compensation Root}
    (represented : Represents physicalBefore trace)
    (stepped : PhysicalStep physicalBefore command physicalAfter) :
    exists observed : Observed boundary command,
      Represents physicalAfter
        (trace ++ [{ command := command
                     observation := observed.observation }]) :=
  refinement.simulates represented stepped

/-! ## Closed non-vacuity witnesses for the logical protocol -/

namespace ClosedInstance

abbrev ClosedIntent := Intent Nat Nat Nat Nat Nat Nat Nat
abbrev ClosedGrant := Grant Nat Nat Nat Nat Nat Nat

def grant : ClosedGrant where
  grantId := 41
  principal := 7
  effectClass := 3
  target := 11
  actions := {5}
  compensations := {9}
  notBefore := 10
  notAfter := 20
  maxAttempt := 2

def intent : ClosedIntent where
  transactionId := 99
  principal := 7
  effectClass := 3
  target := 11
  action := 5
  compensation := some 9
  height := 12
  attempt := 1
  expectedPreRoot := 100
  exactPostRoot := 101

def authorized : grant.Authorizes intent where
  principal := rfl
  effectClass := rfl
  target := rfl
  action := by simp [grant, intent]
  validFrom := by decide
  validUntil := by decide
  attempt := by decide
  compensation := by
    intro request exact
    simp [intent] at exact
    subst request
    simp [grant]

abbrev ClosedBoundary :=
  HandlerBoundary Nat Nat Nat Nat Nat Nat Nat Nat Nat Nat

/-- `Unit` witnesses only inhabit the abstract logical boundary.  They are not
a physical implementation refinement, and no such refinement is built here. -/
def boundary : ClosedBoundary where
  Evidence := fun _ _ => Unit

def forwardPerformed : Observed boundary (.forward intent) :=
  ⟨.performed 77, ()⟩

def compensationPerformed : Observed boundary (.compensate intent 9) :=
  ⟨.performed 88, ()⟩

def committed : Settlement boundary grant intent authorized 100 :=
  settle boundary grant intent authorized 100 forwardPerformed .commit

@[simp] theorem committed_releases_exact_post : committed.logicalRoot = 101 := by
  rfl

def stale : Settlement boundary grant intent authorized 200 :=
  settle boundary grant intent authorized 200 forwardPerformed .commit

@[simp] theorem stale_preserves_current : stale.logicalRoot = 200 := by
  rfl

def compensated : Settlement boundary grant intent authorized 100 :=
  settle boundary grant intent authorized 100 forwardPerformed
    (.compensate 9 rfl compensationPerformed)

@[simp] theorem compensation_preserves_current : compensated.logicalRoot = 100 := by
  rfl

@[simp] theorem compensation_receipt_binds_both_observations :
    compensated.toReceipt.forward = .performed 77 /\
      compensated.toReceipt.compensationOutcome = some (.performed 88) := by
  exact ⟨rfl, rfl⟩

def forwardUncertain : Observed boundary (.forward intent) :=
  ⟨.indeterminate 404, ()⟩

def quarantined : Settlement boundary grant intent authorized 100 :=
  settle boundary grant intent authorized 100 forwardUncertain .commit

@[simp] theorem uncertainty_preserves_current : quarantined.logicalRoot = 100 := by
  rfl

theorem authorization_executes : Grant.authorize grant intent = .ok authorized := by
  rfl

end ClosedInstance

/-! ## Reconciling an uncertain forward observation

`quarantinedForward` is not final when the target can answer for the exact
command later.  `Settlement.reconcile` takes new evidence for the SAME forward
command (the `Observed` type is indexed by it, so evidence about any other
command does not typecheck) and settles again: performed against a still-fresh
pre-root commits, not performed refuses, still indeterminate stays
quarantined, and performed against a stale pre-root is quarantined as stale.
Only a forward-quarantined settlement is reconciled; a committed, refused or
compensated one is final. -/

namespace Settlement

variable
    {TxId : Type uTx} {GrantId : Type uGrant}
    {Principal : Type uPrincipal} {EffectClass : Type uClass}
    {Target : Type uTarget} {Action : Type uAction}
    {Compensation : Type uComp} {Root : Type uRoot}
    {Result : Type uResult} {Failure : Type uFailure}
    {Uncertainty : Type uUncertainty}
    {boundary : HandlerBoundary TxId Principal EffectClass Target Action
      Compensation Root Result Failure Uncertainty}
    {grant : Grant GrantId Principal EffectClass Target Action Compensation}
    {intent : Intent TxId Principal EffectClass Target Action Compensation Root}
    {authorized : grant.Authorizes intent} {currentRoot : Root}

def reconcile [DecidableEq Root] :
    (settlement : Settlement boundary grant intent authorized currentRoot) →
      settlement.status = .quarantinedForward →
      Observed boundary (.forward intent) →
      Settlement boundary grant intent authorized currentRoot
  | .quarantinedForward .., _, again =>
      settle boundary grant intent authorized currentRoot again .commit
  | .committed .., quarantined, _ => nomatch quarantined
  | .refused .., quarantined, _ => nomatch quarantined
  | .compensated .., quarantined, _ => nomatch quarantined
  | .quarantinedStale .., quarantined, _ => nomatch quarantined
  | .quarantinedCompensationNotPerformed .., quarantined, _ => nomatch quarantined
  | .quarantinedCompensationIndeterminate .., quarantined, _ => nomatch quarantined

/-- Reconciliation still exposes a whole root: the current one or the exact
intended post. -/
theorem reconcile_no_partial_commit [DecidableEq Root]
    (settlement : Settlement boundary grant intent authorized currentRoot)
    (quarantined : settlement.status = .quarantinedForward)
    (again : Observed boundary (.forward intent)) :
    (settlement.reconcile quarantined again).logicalRoot = currentRoot ∨
      (settlement.reconcile quarantined again).logicalRoot = intent.exactPostRoot :=
  no_partial_logical_commit _

/-- Reconciliation never manufactures a compensation: its status is one of the
four outcomes of the forward command alone. -/
theorem reconcile_status [DecidableEq Root]
    (settlement : Settlement boundary grant intent authorized currentRoot)
    (quarantined : settlement.status = .quarantinedForward)
    (again : Observed boundary (.forward intent)) :
    (settlement.reconcile quarantined again).status ∈
      [Status.committed, .refused, .quarantinedForward, .quarantinedStale] := by
  cases settlement <;> simp only [status, reduceCtorEq] at quarantined
  obtain ⟨observation, evidence⟩ := again
  cases observation <;> simp only [reconcile, settle] <;> (try split) <;> simp [status]

/-- Performed evidence against a fresh pre-root commits the exact post. -/
theorem reconcile_performed_commits [DecidableEq Root]
    (settlement : Settlement boundary grant intent authorized currentRoot)
    (quarantined : settlement.status = .quarantinedForward)
    (result : Result) (evidence : boundary.Evidence (.forward intent) (.performed result))
    (fresh : currentRoot = intent.expectedPreRoot) :
    (settlement.reconcile quarantined ⟨.performed result, evidence⟩).logicalRoot =
      intent.exactPostRoot := by
  cases settlement <;> simp only [status, reduceCtorEq] at quarantined
  simp [reconcile, settle, fresh, logicalRoot]

/-- Not-performed evidence refuses; the current root stays. -/
theorem reconcile_notPerformed_refuses [DecidableEq Root]
    (settlement : Settlement boundary grant intent authorized currentRoot)
    (quarantined : settlement.status = .quarantinedForward)
    (failure : Failure) (evidence : boundary.Evidence (.forward intent) (.notPerformed failure)) :
    (settlement.reconcile quarantined ⟨.notPerformed failure, evidence⟩).status = .refused ∧
      (settlement.reconcile quarantined ⟨.notPerformed failure, evidence⟩).logicalRoot =
        currentRoot := by
  cases settlement <;> simp only [status, reduceCtorEq] at quarantined
  exact ⟨rfl, rfl⟩

end Settlement

/-! ## Class 1: a keyed-idempotent target, refined

Targets differ in what they can attest about an uncertain command, and the
ledger can promise no more than the target attests:

1. **keyed-idempotent**: the target deduplicates by the intent key and answers
   for a key on request, so an indeterminate observation can be reconciled;
2. **readable-state**: resolvable only when the effect is distinguishable from
   concurrent changes in the state the target exposes;
3. **fire-and-forget** (an actuator, a service performed in person):
   indeterminate is final for the logic and goes to compensation or human
   policy.

This section is the first `ImplementationRefinement` instance, for class 1,
over a toy keyed target.  Its physical state is the list of transaction keys
it has applied; a key's physical effect count is its multiplicity there.  The
instance shows the target applies each key at most once in every represented
state, a duplicate forward command changes nothing physical, and a lost reply
is reconciled by asking again. -/

namespace KeyedTarget

abbrev KIntent := Intent Nat Nat Nat Nat Nat Nat Nat
abbrev KCommand := Command Nat Nat Nat Nat Nat Nat Nat
abbrev KTraceEntry := TraceEntry Nat Nat Nat Nat Nat Nat Nat Nat Nat Nat

/-- The keys this target has applied, in order. -/
structure Physical where
  applied : List Nat

/-- The intent key a command is about. -/
def key : KCommand → Nat
  | .forward intent => intent.transactionId
  | .compensate intent _ => intent.transactionId

/-- The physical steps of the target.  A new key is applied, with the reply
delivered or lost; a known key is answered from the key table and nothing is
applied; a new key may be refused unapplied.  The target has no compensating
action: every compensation is refused without effect. -/
inductive Step : Physical → KCommand → Physical → Type
  | apply (intent : KIntent) (state : Physical)
      (fresh : intent.transactionId ∉ state.applied) :
      Step state (.forward intent) ⟨state.applied ++ [intent.transactionId]⟩
  | applyReplyLost (intent : KIntent) (state : Physical)
      (fresh : intent.transactionId ∉ state.applied) :
      Step state (.forward intent) ⟨state.applied ++ [intent.transactionId]⟩
  | answer (intent : KIntent) (state : Physical)
      (known : intent.transactionId ∈ state.applied) :
      Step state (.forward intent) state
  | refuse (intent : KIntent) (state : Physical)
      (fresh : intent.transactionId ∉ state.applied) :
      Step state (.forward intent) state
  | refuseCompensation (intent : KIntent) (request : Nat) (state : Physical) :
      Step state (.compensate intent request) state

/-- A performed forward observation carries the target's receipt, which must
be the intent's own key; no other observation carries evidence beyond the
represented physical state. -/
def boundary : HandlerBoundary Nat Nat Nat Nat Nat Nat Nat Nat Nat Nat where
  Evidence
    | .forward intent, .performed receipt => PLift (receipt = intent.transactionId)
    | _, _ => Unit

def isForward : KCommand → Bool
  | .forward _ => true
  | .compensate _ _ => false

def isNotPerformed : HandlerObservation Nat Nat Nat → Bool
  | .notPerformed _ => true
  | _ => false

def isPerformed : HandlerObservation Nat Nat Nat → Bool
  | .performed _ => true
  | _ => false

/-- What the trace says about the target: no key applied twice; every applied
key was the subject of a forward command not observed as not performed; and
every forward command observed as performed was applied. -/
def Represents (state : Physical) (trace : List KTraceEntry) : Prop :=
  state.applied.Nodup ∧
    (∀ k ∈ state.applied, ∃ entry ∈ trace,
      isForward entry.command = true ∧ key entry.command = k ∧
        isNotPerformed entry.observation = false) ∧
    ∀ entry ∈ trace, isForward entry.command = true → isPerformed entry.observation = true →
      key entry.command ∈ state.applied

theorem represents_empty : Represents ⟨[]⟩ [] := by
  simp [Represents]

/-- **The class-1 refinement**: every physical step of the keyed target is
simulated by an evidence-backed observation of the same command. -/
theorem refinement : ImplementationRefinement boundary Physical Step Represents where
  simulates := by
    intro before after trace command represented step
    obtain ⟨nodup, applied, performed⟩ := represented
    cases step with
    | apply intent state fresh =>
        refine ⟨⟨.performed intent.transactionId, PLift.up rfl⟩, ?_, ?_, ?_⟩
        · exact List.nodup_append.mpr ⟨nodup, List.nodup_singleton _,
            fun a member b same => by simp at same; subst same; exact fun e => fresh (e ▸ member)⟩
        · intro k member
          rcases List.mem_append.mp member with old | new
          · obtain ⟨entry, inTrace, facts⟩ := applied k old
            exact ⟨entry, List.mem_append_left _ inTrace, facts⟩
          · simp at new; subst new
            exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl, rfl⟩
        · intro entry member forward isPerf
          rcases List.mem_append.mp member with old | new
          · exact List.mem_append_left _ (performed entry old forward isPerf)
          · simp at new; subst new; simp [key]
    | applyReplyLost intent state fresh =>
        refine ⟨⟨.indeterminate 0, ()⟩, ?_, ?_, ?_⟩
        · exact List.nodup_append.mpr ⟨nodup, List.nodup_singleton _,
            fun a member b same => by simp at same; subst same; exact fun e => fresh (e ▸ member)⟩
        · intro k member
          rcases List.mem_append.mp member with old | new
          · obtain ⟨entry, inTrace, facts⟩ := applied k old
            exact ⟨entry, List.mem_append_left _ inTrace, facts⟩
          · simp at new; subst new
            exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl, rfl⟩
        · intro entry member forward isPerf
          rcases List.mem_append.mp member with old | new
          · exact List.mem_append_left _ (performed entry old forward isPerf)
          · simp at new; subst new; simp [isPerformed] at isPerf
    | answer intent state known =>
        refine ⟨⟨.performed intent.transactionId, PLift.up rfl⟩, nodup, ?_, ?_⟩
        · intro k member
          obtain ⟨entry, inTrace, facts⟩ := applied k member
          exact ⟨entry, List.mem_append_left _ inTrace, facts⟩
        · intro entry member forward isPerf
          rcases List.mem_append.mp member with old | new
          · exact performed entry old forward isPerf
          · simp at new; subst new; exact known
    | refuse intent state fresh =>
        refine ⟨⟨.notPerformed 0, ()⟩, nodup, ?_, ?_⟩
        · intro k member
          obtain ⟨entry, inTrace, facts⟩ := applied k member
          exact ⟨entry, List.mem_append_left _ inTrace, facts⟩
        · intro entry member forward isPerf
          rcases List.mem_append.mp member with old | new
          · exact performed entry old forward isPerf
          · simp at new; subst new; simp [isPerformed] at isPerf
    | refuseCompensation intent request state =>
        refine ⟨⟨.notPerformed 0, ()⟩, nodup, ?_, ?_⟩
        · intro k member
          obtain ⟨entry, inTrace, facts⟩ := applied k member
          exact ⟨entry, List.mem_append_left _ inTrace, facts⟩
        · intro entry member forward isPerf
          rcases List.mem_append.mp member with old | new
          · exact performed entry old forward isPerf
          · simp at new; subst new; simp [isForward] at forward

/-- **A duplicate forward command produces no second physical effect**: once a
key is applied, every step on a forward command for it leaves the target's
state unchanged. -/
theorem duplicate_forward_no_second_effect {state after : Physical} {intent : KIntent}
    (known : intent.transactionId ∈ state.applied)
    (step : Step state (.forward intent) after) : after = state := by
  cases step with
  | apply _ _ fresh => exact absurd known fresh
  | applyReplyLost _ _ fresh => exact absurd known fresh
  | answer => rfl
  | refuse _ _ fresh => exact absurd known fresh

/-- **At most once, in every represented state**: the target has applied each
key at most once. -/
theorem applied_at_most_once {state : Physical} {trace : List KTraceEntry}
    (represented : Represents state trace) (k : Nat) :
    state.applied.count k ≤ 1 :=
  List.nodup_iff_count_le_one.mp represented.1 k

/-- The first forward command of the closed intent (key 99): applied, reply lost. -/
def lostReplyFirst : Step ⟨[]⟩ (.forward ClosedInstance.intent) ⟨[99]⟩ :=
  .applyReplyLost ClosedInstance.intent ⟨[]⟩ (by decide)

/-- The retry: key 99 is known, so the target answers from its key table. -/
def lostReplyRetry : Step ⟨[99]⟩ (.forward ClosedInstance.intent) ⟨[99]⟩ :=
  .answer ClosedInstance.intent ⟨[99]⟩ (by decide)

/-- The quarantine the lost reply leaves: the logical root stays at 100. -/
def lostReplySettlement :
    Settlement boundary ClosedInstance.grant ClosedInstance.intent ClosedInstance.authorized 100 :=
  settle boundary ClosedInstance.grant ClosedInstance.intent ClosedInstance.authorized 100
    ⟨.indeterminate 0, ()⟩ .commit

/-- **The class-1 story**: the lost reply quarantines (root 100 stays); the
retry's answer, a receipt for the same key, reconciles it to the exact post
101; and the retry applied nothing (`duplicate_forward_no_second_effect`), so
key 99 was applied once. -/
theorem lost_reply_reconciled :
    lostReplySettlement.status = .quarantinedForward ∧
      lostReplySettlement.logicalRoot = 100 ∧
      (lostReplySettlement.reconcile rfl ⟨.performed 99, PLift.up rfl⟩).logicalRoot = 101 ∧
      (⟨[99]⟩ : Physical).applied.count 99 = 1 := by
  refine ⟨rfl, rfl, rfl, by decide⟩

end KeyedTarget

#assert_axioms Settlement.reconcile_status
#assert_axioms Settlement.reconcile_performed_commits
#assert_axioms KeyedTarget.refinement
#assert_axioms KeyedTarget.duplicate_forward_no_second_effect
#assert_axioms KeyedTarget.applied_at_most_once
#assert_axioms KeyedTarget.lost_reply_reconciled

end Minidregg.Kernel.IrreversibleEffectSettlement
