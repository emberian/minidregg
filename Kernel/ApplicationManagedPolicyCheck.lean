/- Source checks for explicit member-owned lifecycle delegation. -/
import Kernel.ApplicationGrain

namespace Minidregg.Kernel.ApplicationManagedPolicyCheck
open Minidregg.Kernel.ApplicationGrain
open Minidregg.Pred

private def pending : ApplicationGrain.State := ⟨4, 3, 2, 1⟩
private def claimed : ApplicationGrain.State := ⟨4, 9, 2, 1⟩

theorem owner_keeps_install_and_revoke :
    eval (managedPolicy 102 103 17 8) ⟨[]⟩
      ⟨[("request/verb", 4), ("request/subject", 17)]⟩ = true ∧
    eval (managedPolicy 102 103 17 8) ⟨[]⟩
      ⟨[("request/verb", 5), ("request/subject", 17)]⟩ = true := by decide

theorem manager_cannot_install_or_revoke :
    eval (managedPolicy 102 103 17 8) ⟨[]⟩
      ⟨[("request/verb", 4), ("request/subject", 8)]⟩ = false ∧
    eval (managedPolicy 102 103 17 8) ⟨[]⟩
      ⟨[("request/verb", 5), ("request/subject", 8)]⟩ = false := by decide

theorem manager_claims_exact_pending :
    eval (managedPolicy 102 103 17 8) ⟨[]⟩
      ⟨slots pending claimed ++ [("request/verb", 2), ("request/subject", 8)]⟩ = true := by decide

theorem unrelated_actor_cannot_claim :
    eval (managedPolicy 102 103 17 8) ⟨[]⟩
      ⟨slots pending claimed ++ [("request/verb", 2), ("request/subject", 9)]⟩ = false := by decide

theorem exact_owner_derived_from_installed_source :
    managedPolicyOwner 102 103 8 (some (managedPolicy 102 103 17 8)) = some 17 := by decide

theorem substituted_manager_refused :
    managedPolicyOwner 102 103 9 (some (managedPolicy 102 103 17 8)) = none := by decide

theorem exact_linked_laws :
    managedPoliciesMatch 101 102 103 8
      (some (managedPolicy 102 103 17 8)) (some (managedPackagePolicy 101 17 8)) = true := by decide

theorem mixed_owner_law_refused :
    managedPoliciesMatch 101 102 103 8
      (some (managedPolicy 102 103 17 8)) (some (managedPackagePolicy 101 18 8)) = false := by decide

theorem mixed_app_law_refused :
    managedPoliciesMatch 101 102 103 8
      (some (managedPolicy 102 103 17 8)) (some (managedPackagePolicy 104 17 8)) = false := by decide

theorem manager_package_write_requires_joint_version :
    eval (managedPackagePolicy 101 17 8) ⟨[]⟩
      ⟨[("request/verb", 2), ("request/subject", 8)]⟩ = false ∧
    eval (managedPackagePolicy 101 17 8) ⟨[]⟩
      ⟨[("request/verb", 2), ("request/subject", 8),
        ("joint/target/101/resource/field/2/delta", 1)]⟩ = true := by decide

theorem owner_dispatch_retains_issuer :
    managedPoliciesMatchOwner 101 102 103 17
      (some (managedPolicy 102 103 17 8)) (some (managedPackagePolicy 101 17 8)) = true := by decide

theorem manager_dispatch_cannot_become_owner_issuer :
    managedPoliciesMatchOwner 101 102 103 8
      (some (managedPolicy 102 103 17 8)) (some (managedPackagePolicy 101 17 8)) = false := by decide

theorem owner_dispatch_mixed_manager_refused :
    managedPoliciesMatchOwner 101 102 103 17
      (some (managedPolicy 102 103 17 8)) (some (managedPackagePolicy 101 17 9)) = false := by decide

theorem package_owner_admin_manager_refused :
    eval (managedPackagePolicy 101 17 8) ⟨[]⟩
      ⟨[("request/verb", 4), ("request/subject", 17)]⟩ = true ∧
    eval (managedPackagePolicy 101 17 8) ⟨[]⟩
      ⟨[("request/verb", 4), ("request/subject", 8)]⟩ = false := by decide

theorem snapshot_owner_admin_manager_refused :
    eval (managedSnapshotPolicy 101 17 8) ⟨[]⟩
      ⟨[("request/verb", 5), ("request/subject", 17)]⟩ = true ∧
    eval (managedSnapshotPolicy 101 17 8) ⟨[]⟩
      ⟨[("request/verb", 5), ("request/subject", 8)]⟩ = false := by decide

end Minidregg.Kernel.ApplicationManagedPolicyCheck
