/-
# Kernel.OwnerGrantDelegated -- a delegated child passes `OwnerGrant`

`PayAssignmentReceiver.OwnerGrant stored subject account` is the fact the pay, purse, job, seat
and activity receivers check on the capability presented for an account debit. It tests three
things of the stored capability: its holder is the signer, its targets are `{account}` or
`under account`, and its policy id is `account`. It does not test the lineage.

A delegation keeps the parent's policy id (`TypedAuthorization.Attenuates.policyId`) and may keep
its targets, and its holder is the recipient. So a delegated child of an owner grant is an
`OwnerGrant` for its recipient (`ownerGrant_of_child`): the name says "owner", the predicate
says "a capability over this account, held by the signer, under this account's law". Whether a
receiver should additionally require a root grant (`parent = none`) is a behaviour change left
to a ruling; this module only states what the predicate admits today, with the root-only
variant beside it and the witness that separates the two.
-/
module

public import Kernel.PayAssignmentOwner
public import Theory.AssertAxioms

@[expose] public section

namespace Minidregg.Kernel.PayAssignmentReceiver
open Minidregg.Theory
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

/-- **A delegated child passes `OwnerGrant`.** A child that attenuates an owner grant, keeps
its targets and is held by `delegate` is an `OwnerGrant` for `delegate`. -/
theorem ownerGrant_of_child {parent child : StoredCapability .account}
    {owner delegate : SubjectId} {account : Nat} {parentage : Parentage}
    (owned : OwnerGrant (some parent) owner account)
    (attenuates : child.head.Attenuates parent.head parentage)
    (held : child.head.holder = .subject delegate)
    (sameTargets : child.head.scope.targets = parent.head.scope.targets) :
    OwnerGrant (some child) delegate account := by
  simp only [OwnerGrant] at owned ⊢
  refine ⟨held, ?_, ?_⟩
  · rw [sameTargets]
    exact owned.2.1
  · rw [attenuates.policyId]
    exact owned.2.2

/-- The root-only reading of ownership: `OwnerGrant`, and the capability has no parent. -/
def RootOwnerGrant (stored : Option (StoredCapability .account)) (subject : SubjectId)
    (account : Nat) : Prop :=
  OwnerGrant stored subject account ∧ ∃ capability, stored = some capability ∧
    capability.head.parent = none

/-- A delegated child is never a `RootOwnerGrant`: its parent is recorded. -/
theorem not_rootOwnerGrant_of_child {parent child : StoredCapability .account}
    {delegate : SubjectId} {account : Nat} {parentage : Parentage}
    (attenuates : child.head.Attenuates parent.head parentage) :
    ¬ RootOwnerGrant (some child) delegate account := by
  rintro ⟨_, capability, same, root⟩
  cases same
  rw [attenuates.parentId] at root
  cases root

#assert_axioms ownerGrant_of_child
#assert_axioms not_rootOwnerGrant_of_child

end Minidregg.Kernel.PayAssignmentReceiver
