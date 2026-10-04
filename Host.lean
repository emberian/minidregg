/-
# Host — root of the native receiving process's Lean source.

`Host.Main` is the `minidregg-host` executable's root. The `*Check`/`*Audit`
modules are executable regressions over Host code: each runs its check with
`#eval` while it elaborates, so a changed result fails `lake build`.
-/
import Host.Main
import Host.ApplicationBirthAuthoringCheck
import Host.ApplicationPermissionSchemaAuthoringCheck
import Host.ApplicationPermissionSchemaRouteCheck
import Host.CapabilityInspectionCheck
import Host.ProviderUsageAudit

import Host.KeyRotationInspectionChecks
import Host.ReceiptContinuityCheck

import Host.ApplicationManagedPolicyAuthoringCheck

import Host.ObjectiveActivityJson  -- the kernel activity's JSON surface: command authoring, plan/ingress inspection, the public view (op 214), the activity artifact
