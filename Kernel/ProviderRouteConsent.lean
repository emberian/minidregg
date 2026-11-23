/-
# Kernel.ProviderRouteConsent -- local consent honours the pinned provider services

A deployment that pins provider services (`providerServices`: resource id and
per-route tariff) has its semantic Host author every law at a service resource
as `ProviderRoute.policy schedule base`, the schedule taken from the pin
(`Host.Json` birth and policy-install authoring). The consent provider reads
the same settings file and checks what custody is about to sign against it: a
draft that births or re-installs the law of a service resource must install
exactly the pinned route law. A draft carrying another schedule, or no route
law, is refused by name before any key signs; this does not trust the
semantic Host that authored the draft.

`check_binds` states what the pin binds: every policy record a consented draft
installs at a service resource is the pinned route law over some base, so
(`ProviderRoute.installed_route_law`) every mutation that law admits satisfies
the pinned schedule's `transition`. `other_schedule_refused` is the refusal pole.
-/
module

public import Kernel.ProviderRoute
public import Kernel.PolicyInstallController
public import Compiler.PolicyRecordCodec
public import Compiler.GrainResourceBirthHostCodec
public import Compiler.CanonicalCellRegistry
public import Compiler.NativeObservationCodec

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Kernel.ProviderRouteConsent

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Pred
open Minidregg.Kernel.ProviderMetering (Schedule)

set_option autoImplicit false

/-- The pinned services: resource id and the per-operation fees of its tariff. -/
abbrev Services := List (Nat × Schedule)

private theorem all_inj_iff {a b : List Pred} : Pred.all a = Pred.all b ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun p => match p with | .allL ps => ps.toList | _ => []) h
    simpa [Pred.all] using this
  · rintro rfl; rfl

private theorem any_inj_iff {a b : List Pred} : Pred.any a = Pred.any b ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun p => match p with | .anyL ps => ps.toList | _ => []) h
    simpa [Pred.any] using this
  · rintro rfl; rfl

/-- Whether `predicate` is the route law of `schedule` over its own base. -/
def carries (schedule : Schedule) : Pred → Bool
  | .all [base, guard] => decide (Pred.all [base, guard] = ProviderRoute.policy schedule base)
  | _ => false

theorem carries_iff (schedule : Schedule) (predicate : Pred) :
    carries schedule predicate = true ↔ ∃ base, predicate = ProviderRoute.policy schedule base := by
  constructor
  · intro accepted
    unfold carries at accepted
    split at accepted
    · exact ⟨_, of_decide_eq_true accepted⟩
    · cases accepted
  · rintro ⟨base, rfl⟩
    simp [carries, ProviderRoute.policy, Pred.all, PredList.ofList]

/-- Distinct schedules give distinct route laws. -/
theorem transition_injective : Function.Injective ProviderRoute.transition := by
  rintro ⟨au, ap, ah⟩ ⟨bu, bp, bh⟩ same
  simp only [ProviderRoute.transition, ProviderRoute.reserveRule, ProviderRoute.settleRule,
    all_inj_iff, any_inj_iff, List.cons.injEq, Pred.eq.injEq, Pred.not.injEq, Pred.le.injEq,
    Pred.memberOf.injEq, true_and, and_true] at same
  simp only [Schedule.mk.injEq]
  omega

/-- The policy records a draft would install: a birth's initial policies (either
birth source encoding) and an installation's declared source. Other drafts
install no law. A birth or installation whose bytes do not decode refuses. -/
def policiesOf : Draft → Except String (List PolicyRecord)
  | .birth bytes _ => do
      let descriptor ← match GrainResourceBirthHostCodec.sourceCodec.decode bytes with
        | some source => pure source.birth
        | none => match CanonicalCellRegistry.sourceEncoding.codec.decode bytes with
          | some descriptor => pure descriptor
          | none => throw "noncanonical birth draft"
      descriptor.initialPolicies.mapM fun initial =>
        match PolicyRecordCodec.decode initial.canonicalBytes with
        | some record => pure record
        | none => throw "birth draft carries a noncanonical initial policy"
  | .install _ _ bytes | .installWithRoster _ _ bytes _ =>
      match PolicyInstallController.decodeDeclaration bytes with
      | some declaration => pure [declaration.source]
      | none => throw "noncanonical install declaration"
  | _ => pure []

def refusal (resource : Nat) : String :=
  s!"provider service {resource}: the law this draft installs does not carry the pinned per-route schedule"

/-- One record against the pins: a record at a service resource must carry
that service's schedule. -/
def checkRecord (services : Services) (record : PolicyRecord) : Except String Unit :=
  match services.lookup record.policyId.value with
  | none => pure ()
  | some schedule =>
      if carries schedule record.predicate then pure () else throw (refusal record.policyId.value)

/-- The consent check. With no pinned service it reads nothing. -/
def check (services : Services) (draft : Draft) : Except String Unit :=
  if services.isEmpty then pure () else do
    (← policiesOf draft).forM (checkRecord services)

/-- The check on a retained intent: only a `prepare` intent carries a draft. -/
def checkIntent (services : Services) (intent : NativeObservationCodec.Intent) : Except String Unit :=
  match intent.purpose with
  | .prepare draft => check services draft
  | .query _ => pure ()

private theorem forM_ok {α : Type} (f : α → Except String Unit) :
    ∀ (xs : List α), xs.forM f = .ok () → ∀ x ∈ xs, f x = .ok ()
  | [], _, x, mem => by simp at mem
  | y :: ys, h, x, mem => by
      cases hy : f y with
      | error e => simp [List.forM_cons, hy, bind, Except.bind] at h
      | ok u =>
          simp [List.forM_cons, hy] at h
          cases mem with
          | head => exact hy
          | tail _ mem => exact forM_ok f ys h x mem

/-- What the pinned schedule binds. When consent accepts a draft, every policy
record the draft installs at a pinned service resource is that service's route
law over some base, and every mutation that law admits satisfies the pinned
schedule's `transition` (`ProviderRoute.installed_route_law`). -/
theorem check_binds (services : Services) (draft : Draft) (records : List PolicyRecord)
    (accepted : check services draft = .ok ()) (installs : policiesOf draft = .ok records)
    (record : PolicyRecord) (member : record ∈ records) (schedule : Schedule)
    (pinned : services.lookup record.policyId.value = some schedule) :
    (∃ base, record.predicate = ProviderRoute.policy schedule base) ∧
    ∀ old st, eval record.predicate old st = true → st.get "request/verb" = some 2 →
      eval (ProviderRoute.transition schedule) old st = true := by
  have nonempty : services.isEmpty = false := by
    cases services with
    | nil => simp at pinned
    | cons _ _ => rfl
  unfold check at accepted
  rw [nonempty, if_neg (by simp), installs] at accepted
  have one := forM_ok (checkRecord services) records accepted record member
  simp only [checkRecord, pinned] at one
  have carried : carries schedule record.predicate = true := by
    cases h : carries schedule record.predicate with
    | true => rfl
    | false => simp [h] at one
  obtain ⟨base, shape⟩ := (carries_iff schedule record.predicate).mp carried
  refine ⟨⟨base, shape⟩, fun old st admitted mutation => ?_⟩
  rw [shape] at admitted
  exact ProviderRoute.installed_route_law schedule base old st admitted mutation

/-- The refusal pole: a record at a service resource whose law is the route law
of another schedule is refused by name. -/
theorem other_schedule_refused (services : Services) (record : PolicyRecord)
    (schedule other : Schedule) (pinned : services.lookup record.policyId.value = some schedule)
    (base : Pred) (law : record.predicate = ProviderRoute.policy other base)
    (differs : other ≠ schedule) :
    checkRecord services record = .error (refusal record.policyId.value) := by
  have absent : carries schedule record.predicate = false := by
    cases h : carries schedule record.predicate with
    | false => rfl
    | true =>
        obtain ⟨base2, shape⟩ := (carries_iff schedule record.predicate).mp h
        rw [law] at shape
        simp only [ProviderRoute.policy] at shape
        simp only [all_inj_iff, any_inj_iff, List.cons.injEq] at shape
        exact absurd (transition_injective shape.2.1.2.1) differs
  simp only [checkRecord, pinned, absent]
  rfl

#assert_axioms carries_iff
#assert_axioms transition_injective
#assert_axioms check_binds
#assert_axioms other_schedule_refused

end Minidregg.Kernel.ProviderRouteConsent
