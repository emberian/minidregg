/-
# Deployed — the deployed Host's umbrella (UMBRELLA-SPLIT, 2026-10-01)

Everything the deployed system is: the core (`Theory`), the kernel (`Kernel`), the
predicate algebra (`Pred`), the effect registry (`Effects`) and the native host
(`Host`, with every `Host.*` module the exe target does not root). It leaves out
the proof-system research: `Selvage` and the proof-system `Assurance` apex
theorems, which `Minidregg` (the research umbrella) still builds. Mini admits
by re-execution, not by proof (decision 10-01), so no deployed module needs them.

`AxiomCensus` checks this umbrella; `AxiomCensusResearch` checks `Minidregg`.
`scripts/lane/ub.sh` builds this; `scripts/lane/rb.sh` builds the research set.

Residual: the Host still imports 12 `Selvage` modules through the Tower256
digest backend (`Compiler.Tower256ConcreteBackend` -> `BinaryTower256Profile` ->
`Tower256CshakeMerkleController` -> `Selvage.BinaryLookup`); see the task opened
with this split.
-/
import Theory
import Kernel
import Pred
import Effects
import Assurance.StoryLaw  -- P-STORY: a sealed story's table is the law on every player's cell (sealed_story_scene_monotone, sealed_story_never_relawed); kernel-level, not proof-system Assurance: it imports Kernel.LawView and Kernel only
import Host
-- Kernel and policy modules `Minidregg` roots beside the per-directory roots
-- (none imports Selvage or Assurance; the arithmetization and zkML roots stay research):
import Kernel.ApplicationDispatchUpper
import Kernel.ApplicationGrainLaws
import Kernel.ApplicationLifecycleBeginCheck
import Kernel.ApplicationLifecycleClaimPolicyCheck
import Kernel.ApplicationLifecycleClaimReceiver
import Kernel.ApplicationLifecycleClaimVerified
import Kernel.ApplicationShareIssueHistorical
import Kernel.ApplicationSpkProfileProofs
import Kernel.FnSelectedHistoricalStep
import Kernel.FnSelectiveReleaseProofs
import Kernel.Job
import Compiler.BoundedQuantifiedPolicyAdmission
import Compiler.DeclaredEffectCellRegistry
import Host.ApplicationAgentLifetimeDispatchInspection
import Host.ApplicationAgentLifetimeDispatchPaidInspection
import Host.ApplicationAgentLifetimeGrantAuthoring
import Host.ApplicationAgentLifetimeGrantInspection
import Host.ApplicationAgentLifetimePaidIngressInspection
import Host.ApplicationCurrentBirthAuthoring
import Host.ApplicationDispatchAgentInspection
import Host.ApplicationDispatchAgentPaidInspection
import Host.ApplicationDispatchInspection
import Host.ApplicationGrainSessionEnrollmentAuthoring
import Host.ApplicationGrainSessionEnrollmentInspection
import Host.ApplicationLifecycleBeginOperator
import Host.ApplicationLifecycleClaimInspection
import Host.ApplicationLifecycleClaimOperator
import Host.ApplicationLifecycleClaimV3Inspection
import Host.ApplicationLifecycleCompletionAuthoring
import Host.ApplicationLifecycleCompletionOperator
import Host.ApplicationLifecycleLaunchBeginAuthoring
import Host.ApplicationLifecycleLaunchBeginInspection
import Host.ApplicationLifecycleLaunchClaimAuthoring
import Host.ApplicationLifecycleLaunchClaimInspection
import Host.ApplicationLifecycleLaunchCompletionAuthoring
import Host.ApplicationLifecycleLaunchCompletionInspection
import Host.ApplicationLifecycleLaunchReportAuthoring
import Host.ApplicationLifecycleStopClaimInspection
import Host.ApplicationPermissionSchemaAuthoring
import Host.ApplicationShareIssueGrainInspection
import Host.ApplicationSpkLaunchDescriptorAuthoring
import Host.BirthRuntimeProfile
import Host.CapabilityInspection
import Host.CurrentResourceBirthAuthoring
import Host.FnConsumerFrontierPlan
import Host.FnConsumerNamespacePlan
import Host.FnInboxView
import Host.FnSelectiveReleaseAuthoring
import Host.FnSelectiveReleaseFnAck
import Host.FnSelectiveReleaseFnReceiving
import Host.FnSelectiveReleaseSourceAuthoring
import Host.GrainOriginCommand
import Host.GrainOriginPreparation
import Host.GrainOriginSource
import Host.Json
import Host.Main
import Host.ProviderUsage
import Host.ProviderUsageAudit
