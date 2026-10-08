/- Account ownership predicate shared by the pay and OB receivers. -/
import Theory.CredentialAuthorityEffects

namespace Minidregg.Kernel.PayAssignmentReceiver
open Minidregg.Theory
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

/-- The two target forms an owner grant on `account` takes: genesis issues
`explicit {account}`; a workspace birth issues `under account` (the owner holds
the cell as a room, K-ROOM). An `under R` grant for a room `R` containing the
account is not ownership of it: it is governed by `R`'s law, not `account`'s. -/
def OwnerTargets (targets : TargetSet .account) (account : Nat) : Prop :=
  targets = .explicit {⟨account⟩} ∨ targets = .under account

instance (targets : TargetSet .account) (account : Nat) :
    Decidable (OwnerTargets targets account) := by
  unfold OwnerTargets; infer_instance

/-- The owner-grant fact: the presented account capability is held by
`subject`, targets `{account}` or `under account`, and is governed by `account`'s policy
(`ResourceBirth.AuthorityGrant.NativeForBirth` with its holder). -/
def OwnerGrant (stored : Option (StoredCapability .account)) (subject : SubjectId)
    (account : Nat) : Prop :=
  match stored with
  | none => False
  | some stored =>
      stored.head.holder = .subject subject ∧ OwnerTargets stored.head.scope.targets account ∧
        stored.head.policyId.value = account

instance (stored : Option (StoredCapability .account)) (subject : SubjectId) (account : Nat) :
    Decidable (OwnerGrant stored subject account) := by
  unfold OwnerGrant
  split <;> infer_instance


end Minidregg.Kernel.PayAssignmentReceiver
