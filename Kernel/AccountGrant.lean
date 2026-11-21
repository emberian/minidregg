/-
# Kernel.AccountGrant -- the two facts a receiver asks of a presented account capability

A receiver that acts on an account checks the stored capability its request presents, beside
the typed authorization of the request itself. There are two facts, and each receiver names
the one it needs:

* `Held stored subject account`: the capability is held by the signer, targets the account
  itself (`{account}` or `under account`, never a containing room) and is governed by the
  account's own policy. It does not test the lineage: a delegated child that keeps its
  parent's targets passes for its recipient (`held_of_child`). The receivers that debit the
  account ask for this one (purse refill, job fund and claim, seat turn, activity payer); what
  a delegate may debit there is limited by the balance bound its grant must carry
  (`Theory.CapabilityValueBound.StrictBound`).
* `RootOwner stored subject account`: `Held`, and the capability has no parent. Only the grant
  the account was born or enrolled with passes; a delegated child never does
  (`not_rootOwner_of_child`). The pay assignment asks for this one: it binds the account's one
  deposit index, a write no balance bound limits and nothing undoes.
-/
module

public import Theory.CredentialAuthorityEffects
public import Theory.AssertAxioms

@[expose] public section

namespace Minidregg.Kernel.AccountGrant
open Minidregg.Theory
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

/-- The two target forms a grant on `account` itself takes: genesis issues
`explicit {account}`; a workspace birth issues `under account` (the owner holds
the cell as a room, K-ROOM). An `under R` grant for a room `R` containing the
account is not a grant on it: it is governed by `R`'s law, not `account`'s. -/
def Targets (targets : TargetSet .account) (account : Nat) : Prop :=
  targets = .explicit {⟨account⟩} ∨ targets = .under account

instance (targets : TargetSet .account) (account : Nat) :
    Decidable (Targets targets account) := by
  unfold Targets; infer_instance

/-- The signer holds a grant on this account: the presented account capability is held by
`subject`, targets `{account}` or `under account`, and is governed by `account`'s policy. The
lineage is not tested, so the holder may be the owner or a delegate. -/
def Held (stored : Option (StoredCapability .account)) (subject : SubjectId)
    (account : Nat) : Prop :=
  match stored with
  | none => False
  | some stored =>
      stored.head.holder = .subject subject ∧ Targets stored.head.scope.targets account ∧
        stored.head.policyId.value = account

instance (stored : Option (StoredCapability .account)) (subject : SubjectId) (account : Nat) :
    Decidable (Held stored subject account) := by
  unfold Held
  split <;> infer_instance

/-- The signer owns this account: `Held`, by a root capability (`parent = none`), the grant a
birth, an enrolment or genesis issues to the owner
(`ResourceBirthPolicyController.Concrete.RootGrantShape`). -/
def RootOwner (stored : Option (StoredCapability .account)) (subject : SubjectId)
    (account : Nat) : Prop :=
  match stored with
  | none => False
  | some capability => Held (some capability) subject account ∧ capability.head.parent = none

instance (stored : Option (StoredCapability .account)) (subject : SubjectId) (account : Nat) :
    Decidable (RootOwner stored subject account) := by
  unfold RootOwner
  split <;> infer_instance

/-- A root owner holds a grant on the account. -/
theorem RootOwner.held {stored : Option (StoredCapability .account)} {subject : SubjectId}
    {account : Nat} (owner : RootOwner stored subject account) : Held stored subject account := by
  cases stored with
  | none => exact owner.elim
  | some capability => exact owner.1

/-- `RootOwner` is exactly `Held` by a parentless capability. -/
theorem rootOwner_iff {capability : StoredCapability .account} {subject : SubjectId}
    {account : Nat} :
    RootOwner (some capability) subject account ↔
      Held (some capability) subject account ∧ capability.head.parent = none :=
  Iff.rfl

/-- **A delegated child passes `Held`.** A child that attenuates a grant on the account, keeps
its targets and is held by `delegate` is a grant on the account for `delegate`. -/
theorem held_of_child {parent child : StoredCapability .account}
    {owner delegate : SubjectId} {account : Nat} {parentage : Parentage}
    (owned : Held (some parent) owner account)
    (attenuates : child.head.Attenuates parent.head parentage)
    (held : child.head.holder = .subject delegate)
    (sameTargets : child.head.scope.targets = parent.head.scope.targets) :
    Held (some child) delegate account := by
  simp only [Held] at owned ⊢
  refine ⟨held, ?_, ?_⟩
  · rw [sameTargets]
    exact owned.2.1
  · rw [attenuates.policyId]
    exact owned.2.2

/-- **A delegated child is never a `RootOwner`**: its parent is recorded. -/
theorem not_rootOwner_of_child {parent child : StoredCapability .account}
    {delegate : SubjectId} {account : Nat} {parentage : Parentage}
    (attenuates : child.head.Attenuates parent.head parentage) :
    ¬ RootOwner (some child) delegate account := by
  rintro ⟨_, root⟩
  rw [attenuates.parentId] at root
  cases root

#assert_axioms RootOwner.held
#assert_axioms held_of_child
#assert_axioms not_rootOwner_of_child

end Minidregg.Kernel.AccountGrant
