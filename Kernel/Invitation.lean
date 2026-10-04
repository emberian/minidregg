/- Invitations: the exclusive, assayable right to play one role of one contract
instance (Agoric Zoe's invitation; Miller, Van Cutsem, Tulloh, ESOP 2013 §6,
the contract host's single-use token).

An invitation names the contract instance it admits to, the package (code
identity) that instance runs, the role, and terms the holder can read before
using it. It is minted only by a turn of the instance it names, carrying that
instance's own package (on the native route: a `mint` member of the Plan the
instance's own package method returns, under an id the receiver derives from the
instance, the invoking turn and the member's index, so the code chooses role,
terms and holder but never the id or the package); it is held by exactly one
subject, who may hand it over; and it is spent like a nullifier by the `offer`
that creates a seat (`Kernel.Seat`; natively also a durable claim). A spent id
can never be minted or used again.

This module is pure data and pure rules; `Kernel.Seat` runs them inside the
seat world's one transition function. -/
import Theory.CanonicalResourceKernel
import Theory.AxiomPin
import Pred.Core

namespace Minidregg.Kernel.Invitations
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
set_option autoImplicit false

abbrev InstanceId := Nat
abbrev InvitationId := Nat

/-- A contract instance as the seat world knows it: its id, the package it
runs, and the contract's own clause. The clause is judged on the instance's
reallocations; it is never consulted for an `exit` (`Kernel.Seat`). -/
structure Instance where
  id : InstanceId
  package : Digest
  clause : Minidregg.Pred.Pred
  deriving DecidableEq, Repr

structure Invitation where
  id : InvitationId
  inst : InstanceId
  package : Digest
  role : String
  /-- Terms the holder can assay before offering (Zoe's `customDetails`). -/
  terms : List (String × Nat)
  holder : SubjectId
  deriving DecidableEq, Repr

inductive Refusal where
  | instanceMissing (inst : InstanceId)
  | notTheInstance (inst : InstanceId)
  | packageMismatch
  | idUsed (id : InvitationId)
  | invitationMissing (id : InvitationId)
  | notHolder (id : InvitationId)
  | assayFailed (id : InvitationId)
  deriving DecidableEq, Repr

/-- The live invitations, the spent ids, the live instances and the retired
instance ids (a retired id is never created again). On the native route this is
the part of the stored registry a turn loads (`Kernel.SeatStore`). -/
structure Registry where
  instances : List Instance
  live : List Invitation
  spent : List InvitationId
  retired : List InstanceId := []
  deriving DecidableEq, Repr

def Registry.instance? (registry : Registry) (inst : InstanceId) : Option Instance :=
  registry.instances.find? (fun i => i.id == inst)

def Registry.invitation? (registry : Registry) (id : InvitationId) : Option Invitation :=
  registry.live.find? (fun v => v.id == id)

/-- An id is fresh when it was never minted (live) and never spent. -/
def Registry.fresh (registry : Registry) (id : InvitationId) : Bool :=
  (registry.invitation? id).isNone && !(registry.spent.contains id)

/-- Mint: only a turn OF the named instance, only with that instance's own
package, only under a fresh id. -/
def mint (registry : Registry) (actingInstance : InstanceId) (invitation : Invitation) :
    Except Refusal Registry :=
  match registry.instance? invitation.inst with
  | none => .error (.instanceMissing invitation.inst)
  | some inst =>
    if actingInstance ≠ invitation.inst then .error (.notTheInstance invitation.inst)
    else if inst.package ≠ invitation.package then .error .packageMismatch
    else if !registry.fresh invitation.id then .error (.idUsed invitation.id)
    else .ok { registry with live := invitation :: registry.live }

/-- Hand over: only the holder moves an invitation; it stays the same right. -/
def handOver (registry : Registry) (subject : SubjectId) (id : InvitationId) (recipient : SubjectId) :
    Except Refusal Registry :=
  match registry.invitation? id with
  | none => .error (.invitationMissing id)
  | some invitation =>
    if invitation.holder ≠ subject then .error (.notHolder id)
    else .ok { registry with
      live := registry.live.map (fun v => if v.id = id then { v with holder := recipient } else v) }

/-- What the offerer expects to be playing; checked against the invitation
before anything is escrowed (the assay). -/
structure Expectation where
  inst : InstanceId
  package : Digest
  role : String
  deriving DecidableEq, Repr

/-- The registry after `id` is spent. -/
def Registry.spend (registry : Registry) (id : InvitationId) : Registry :=
  { registry with
    live := registry.live.filter (fun v => v.id ≠ id)
    spent := id :: registry.spent }

/-- Spend: the holder presents the invitation, it must assay as expected, and
its id moves to `spent` in the same transition (a nullifier). -/
def spend (registry : Registry) (subject : SubjectId) (id : InvitationId) (expect : Expectation) :
    Except Refusal (Invitation × Registry) :=
  match registry.invitation? id with
  | none => .error (.invitationMissing id)
  | some invitation =>
    if invitation.holder ≠ subject then .error (.notHolder id)
    else if invitation.inst ≠ expect.inst ∨ invitation.package ≠ expect.package ∨ invitation.role ≠ expect.role then
      .error (.assayFailed id)
    else if (registry.instance? invitation.inst).isNone then .error (.instanceMissing invitation.inst)
    else .ok (invitation, registry.spend id)

theorem spend_result {registry next : Registry} {subject : SubjectId} {id : InvitationId}
    {expect : Expectation} {invitation : Invitation}
    (spent : spend registry subject id expect = .ok (invitation, next)) : next = registry.spend id := by
  unfold spend at spent
  split at spent
  · cases spent
  · split at spent
    · cases spent
    · split at spent
      · cases spent
      · split at spent
        · cases spent
        · cases spent; rfl

theorem spent_not_live (registry : Registry) (id : InvitationId) :
    (registry.spend id).invitation? id = none := by
  unfold Registry.invitation? Registry.spend
  rw [List.find?_eq_none]
  intro v member
  simp only [List.mem_filter, decide_eq_true_eq] at member
  simpa using member.2

/-- A spent invitation is no longer live: a second `spend` of the same id is
refused. -/
theorem spend_once {registry next : Registry} {subject subject' : SubjectId} {id : InvitationId}
    {expect expect' : Expectation} {invitation : Invitation}
    (spent : spend registry subject id expect = .ok (invitation, next)) :
    spend next subject' id expect' = .error (.invitationMissing id) := by
  rw [spend_result spent]
  unfold spend
  rw [spent_not_live]

/-- A spent id can never be minted again. -/
theorem spent_never_minted {registry next : Registry} {subject : SubjectId} {id : InvitationId}
    {expect : Expectation} {invitation : Invitation} (acting : InstanceId) (fresh : Invitation)
    (spent : spend registry subject id expect = .ok (invitation, next)) (sameId : fresh.id = id) :
    ∃ reason, mint next acting fresh = .error reason := by
  rw [spend_result spent]
  unfold mint
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · rename_i notUsed
          exfalso
          apply notUsed
          simp [Registry.fresh, Registry.spend, sameId]

#assert_axioms spend_once spent_never_minted

end Minidregg.Kernel.Invitations
