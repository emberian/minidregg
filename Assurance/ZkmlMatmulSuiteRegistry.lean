/-
# Assurance.ZkmlMatmulSuiteRegistry — the one suite registry both checkers bind

`Assurance.ZkmlMatmulAuditTurn` introduced the versioned audit identity and the
bounded registry it is a member of.  The succinct contraction checker
(`Assurance.ZkmlMatmulSuccinctChecker`) must bind the same registered suite,
and a later audit turn will consume that checker; so the registry lives here,
below both, and neither file carries a second copy.

Nothing in this file is production: the registry is one literal entry,
membership is evidence, and an authenticated upgrade policy remains separate.
The identity tuple and the runnable byte checker's expected profile are proved
to be the same first-order data (`auditIdentity_matches_checker`).
-/
import Assurance.ZkmlMatmulChecker
import Theory.TypedAuthorization

namespace Minidregg.Assurance.ZkmlMatmulSuiteRegistry

open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

structure AuditIdentity where
  suiteId : Digest
  checkerId : Digest
  statementId : Digest
  planningArtifactId : Digest
  nativeRequestId : Digest
  codecVersion : Nat
  deriving DecidableEq, Repr

def auditIdentity : AuditIdentity :=
  ⟨⟨101⟩, ⟨102⟩, ⟨103⟩, ⟨104⟩, ⟨105⟩, 1⟩

/-- The bounded registry selected by this slice.  Membership is evidence; a
production registry and authenticated upgrade policy remain separate. -/
def auditRegistry : List AuditIdentity := [auditIdentity]

theorem auditIdentity_registered : auditIdentity ∈ auditRegistry := by simp [auditRegistry]

/-- The durable evidence identity and the runnable byte checker's profile are
the same first-order tuple.  The planning and native request ids are bindings,
not authorization witnesses. -/
theorem auditIdentity_matches_checker :
    auditIdentity.codecVersion =
        ZkmlMatmulChecker.expected.codecVersion.toNat ∧
    auditIdentity.suiteId.value =
        ZkmlMatmulChecker.expected.suiteId.toNat ∧
    auditIdentity.checkerId.value =
        ZkmlMatmulChecker.expected.checkerId.toNat ∧
    auditIdentity.statementId.value =
        ZkmlMatmulChecker.expected.statementId.toNat ∧
    auditIdentity.planningArtifactId.value =
        ZkmlMatmulChecker.expected.planningArtifactId.toNat ∧
    auditIdentity.nativeRequestId.value =
        ZkmlMatmulChecker.expected.requestId.toNat := by
  decide

/-- An identity that differs from the registered one only in its suite digest
is not registered.  This is the refusal the succinct checker's wrong-suite
tooth consumes; it is decided, not assumed. -/
def unregisteredIdentity : AuditIdentity :=
  { auditIdentity with suiteId := ⟨100⟩ }

theorem unregisteredIdentity_not_registered :
    unregisteredIdentity ∉ auditRegistry := by
  decide

end Minidregg.Assurance.ZkmlMatmulSuiteRegistry
