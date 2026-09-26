/-
The local fn consumer gateway is an independently configured Mini principal.
Its content-resource law must select the gateway subject at the current policy
head before a new fn operation is authored. This check does not turn a local
fn poll into a portable fn-issued Store attestation.
-/
import Kernel.NativeHostContext

namespace Minidregg.Kernel.FnGatewayPolicy

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Pred

set_option autoImplicit false

abbrev Pin := NativeHost.FnGatewayPin

/-- A deliberately conservative, inspectable fragment: the current mutation
law is exactly the gateway-subject equality. A stronger equivalent law needs
an explicit extension with its own implication proof. -/
def subjectLocked (subject : SubjectId) : Pred → Bool
  | .eq slot value => slot == "request/subject" && value == Int.ofNat subject.value
  | _ => false

/-- The exact pinned law forces the actual projected request subject when
the source evaluator admits the step. The receiver's policy compiler is
separately proved faithful to that evaluator. -/
theorem subjectLocked_sound (subject : SubjectId) (predicate : Pred)
    (old new : State) (locked : subjectLocked subject predicate = true)
    (accepted : Pred.eval predicate old new = true) :
    new.get "request/subject" = some (Int.ofNat subject.value) := by
  cases predicate <;> simp [subjectLocked] at locked
  rcases locked with ⟨rfl, rfl⟩
  simpa [Pred.eval, Pred.evalWith] using accepted

/-- Together with the receiver's source-derived request projection, this
excludes every other signed subject from an admitted gateway mutation. -/
theorem admitted_subject_eq_gateway (gateway actual : SubjectId)
    (predicate : Pred) (old new : State)
    (locked : subjectLocked gateway predicate = true)
    (accepted : Pred.eval predicate old new = true)
    (projected : new.get "request/subject" = some (Int.ofNat actual.value)) :
    actual = gateway := by
  have selected := subjectLocked_sound gateway predicate old new locked accepted
  rw [projected] at selected
  have equal : actual.value = gateway.value := by
    have eqInt : (actual.value : Int) = gateway.value := Option.some.inj selected
    omega
  cases actual
  cases gateway
  simp_all

theorem non_gateway_subject_refused (gateway actual : SubjectId)
    (predicate : Pred) (old new : State)
    (locked : subjectLocked gateway predicate = true)
    (projected : new.get "request/subject" = some (Int.ofNat actual.value))
    (different : actual ≠ gateway) : Pred.eval predicate old new = false := by
  cases admission : Pred.eval predicate old new with
  | false => rfl
  | true =>
      exact False.elim (different (admitted_subject_eq_gateway
        gateway actual predicate old new locked admission projected))

/-- Resolve from the loaded complete authority and policy-source cell, never
from a caller-supplied policy object. A changed current law needs an explicit
new operator pin before another fn consumer command is prepared. -/
def checkCurrent (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (pin : Pin) : Except String Unit := do
  let some head := CredentialAuthorityDomain.headAt
      opened.authority.snapshot.logical ⟨pin.target⟩
    | throw "fn gateway target has no current policy head"
  unless head.address == pin.policyAddress do
    throw "fn gateway current policy differs from operator pin"
  let some source := CanonicalCellRegistry.loadPolicySource config.deployment.domain
      opened.directory.directory head.address
    | throw "fn gateway current policy source is unavailable"
  unless source.record.policyId == ⟨pin.target⟩ &&
      source.record.semantics == config.profile.semantics &&
      subjectLocked pin.subject source.record.predicate do
    throw "fn gateway current policy does not lock mutation to gateway subject"

end Minidregg.Kernel.FnGatewayPolicy
