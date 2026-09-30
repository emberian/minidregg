/-
The exact joint command shape for an application-dispatch candidate. This
module constructs and compares signed *candidates* only. The special receiver
must obtain each old page and root from the loaded image, derive the session
enrollment and installed interface from guarded content, then use ordinary
DRC signature/current-law admission before constructing its dispatch witness.
In particular, equality with this command is not an HTTP delivery permit.
-/
import Kernel.ApplicationDispatchIngress
import Kernel.ApplicationGrainSession
import Kernel.AgentGrain

namespace Minidregg.Kernel.ApplicationDispatchCommand

open Minidregg.Compiler
open Minidregg.Kernel.ApplicationDispatchCodec
open Minidregg.Kernel.ApplicationDispatchIngress
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- Only the session and optional parent are DRC mutation witnesses. The
app, installed manifest and enrollment are separately observed under source-
derived native requests and durable read guards. -/
structure Selection where
  sessionRoot : Digest
  sessionObserve : CapabilityId

/-- An agent parent is a mandatory second joint witness for an agent-origin
session. The state's actual old values must be recovered from the loaded page. -/
structure Parent where
  task : Nat
  state : AgentGrain.State
  capability : CapabilityId
  root : Digest
  observe : CapabilityId

def parentTarget (parent : Parent) : DeclaredResourceController.Target :=
  AgentGrain.Operation.target .input parent.task parent.capability parent.root
    parent.state (some parent.observe)

def sessionState (dispatch : Dispatch) : ApplicationGrainSession.State :=
  { app := dispatch.session.appResource
    appGeneration := dispatch.session.appGeneration
    generation := dispatch.session.generation
    status := .active
    kind := if dispatch.session.kind = .web then .web else .api }

def sessionTarget (dispatch : Dispatch) (selection : Selection) :
    DeclaredResourceController.Target :=
  ApplicationGrainSession.Operation.target .activeWitness
    dispatch.session.resource dispatch.session.capability selection.sessionRoot
    (sessionState dispatch) (some selection.sessionObserve)

def parentMatches (origin : Origin) (parent : Option Parent) : Bool :=
  match origin, parent with
  | .human, none => true
  | .agent task generation, some parent =>
      decide (parent.task = task ∧ parent.state.generation = generation ∧
        (parent.state.status = 3 ∨ parent.state.status = 4))
  | _, _ => false

def targets (ingress : Ingress) (selection : Selection) (parent : Option Parent) :
    List DeclaredResourceController.Target :=
  sessionTarget ingress.dispatch selection :: parent.toList.map parentTarget

/-- `parentMatches` is checked separately. An agent-origin request with no
parent cannot pass the command shape; a human session never inherits a task's
cgroup fence merely because an agent happens to relay its HTTP bytes. -/
def command (ingress : Ingress) (selection : Selection) (parent : Option Parent) :
    DeclaredResourceController.Command :=
  { subject := ingress.dispatch.session.subject
    nonce := (requestDigest ingress).value
    targets := targets ingress selection parent }

def matchesCommand (ingress : Ingress) (selection : Selection) (parent : Option Parent)
    (actual : DeclaredResourceController.Command) : Bool :=
  parentMatches ingress.dispatch.session.origin parent &&
    decide (actual = command ingress selection parent)

theorem matches_exact (ingress : Ingress) (selection : Selection) (parent : Option Parent)
    (actual : DeclaredResourceController.Command)
    (accepted : matchesCommand ingress selection parent actual = true) :
    actual = command ingress selection parent := by
  simp [matchesCommand, Bool.and_eq_true] at accepted
  exact accepted.2

theorem matches_subject (ingress : Ingress) (selection : Selection)
    (parent : Option Parent) (actual : DeclaredResourceController.Command)
    (accepted : matchesCommand ingress selection parent actual = true) :
    actual.subject = ingress.dispatch.session.subject := by
  rw [matches_exact ingress selection parent actual accepted]
  rfl

theorem human_has_no_parent (ingress : Ingress) (selection : Selection)
    (parent : Option Parent) (actual : DeclaredResourceController.Command)
    (origin : ingress.dispatch.session.origin = .human)
    (accepted : matchesCommand ingress selection parent actual = true) : parent = none := by
  have compatible : parentMatches ingress.dispatch.session.origin parent = true := by
    simp only [matchesCommand, Bool.and_eq_true] at accepted
    exact accepted.1
  rw [origin] at compatible
  cases parent with
  | none => rfl
  | some _ => simp [parentMatches] at compatible

theorem agent_has_parent (ingress : Ingress) (selection : Selection)
    (parent : Option Parent) (actual : DeclaredResourceController.Command)
    (task : Nat) (generation : Int)
    (origin : ingress.dispatch.session.origin = .agent task generation)
    (accepted : matchesCommand ingress selection parent actual = true) :
    parent.isSome = true := by
  have compatible : parentMatches ingress.dispatch.session.origin parent = true := by
    simp only [matchesCommand, Bool.and_eq_true] at accepted
    exact accepted.1
  rw [origin] at compatible
  cases parent with
  | none => simp [parentMatches] at compatible
  | some _ => rfl

theorem human_targets_one (ingress : Ingress) (selection : Selection)
    (parent : Option Parent) (actual : DeclaredResourceController.Command)
    (origin : ingress.dispatch.session.origin = .human)
    (accepted : matchesCommand ingress selection parent actual = true) :
    actual.targets = [sessionTarget ingress.dispatch selection] := by
  rw [matches_exact ingress selection parent actual accepted]
  rw [human_has_no_parent ingress selection parent actual origin accepted]
  rfl

end Minidregg.Kernel.ApplicationDispatchCommand
