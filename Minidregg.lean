/-
# Minidregg — root module.

Imports the stable per-directory roots. The explicit Bend/Simplex qualification
targets and opt-in authored research target are described in
docs/LEAN-QUALIFICATION.md. A declared target is not a compiler PASS. The carve is ATLAS.md §7; the import boundary between the
candidate-independent `Theory`/`Selvage` libs and everything else is mechanically
enforced by `scripts/check-import-boundary.sh`.
-/
import Theory      -- candidate-independent core: verify/find seam, Holds, product camera
import Kernel      -- the 3 verbs (create · gwrite · move) over the camera; hyperedge turn shape
import Pred        -- the ONE predicate algebra, syntactic AST end-to-end
import Effects     -- open handler registry: one declaration per effect, proof fields for the floor
import Compiler    -- arithmetization spine: syntactic-leaf IR + fold_unique
import Compiler.BoundedQuantifiedPolicyAdmission  -- bounded quantified policies reach committed-policy AIR reflection
import Compiler.DeclaredActionAir  -- canonical action bytes and sparse guard execution are equivalent to one emitted descriptor
import Compiler.DeclaredEffectCellRegistry  -- the declared-effect store cell (any field count) enters the dependent cell registry
import Selvage        -- the proof system
import Host      -- the native receiving process (the minidregg-host exe root) and its executable regressions
import Assurance   -- cross-boundary apex theorems (hand-written, pinned per theorem)
import Assurance.CredentialFoundationMigrationAudit  -- exact pins for revision/generation separation and explicit delegation
import Assurance.CredentialDelegationLineageAudit
import Assurance.CredentialSourceAdmissionAudit
import Compiler.DistributiveLaw  -- N4 stated and inhabited: DistLaw over a Signature's polynomial functor and a PFunctor behaviour, Bialgebra, the initial (Term, opModel) and final (PFunctor.M, denModel) bialgebras, N4_adequacy (fold denModel = M.corec opModel, the unique bialgebra morphism) and N4_congruence; FailClosed as a SEPARATE keystone with teeth — strictLaw and openLaw are BOTH laws (laws_inhabited), only one is fail-closed, and open_joint_commits exhibits the half-committed joint turn by rfl. Rooted here rather than in Compiler.lean, which carries uncommitted owner edits. Residuals [N4-home] [N4-hyperedge-instance] [N4-gsos]

-- Library modules no per-directory root imported (found by olean census at wave S4); rooted so the umbrella covers them.
import Compiler.PredCastHashProofs
import Compiler.PredCompileOrderWitness
import Compiler.PredCompileSlotWitness
import Compiler.PredOrderGadgetWitness
import Compiler.ZkmlEltwiseAir
import Compiler.ZkmlTraceCheck
import Kernel.ApplicationFailedStartRecoveryReceiver  -- with the three V4 retry receivers: receivers no Host module imports any more; `Deployed` roots them, so this umbrella (and the censuses over it) does too
import Kernel.ApplicationGrainLaws
import Kernel.ApplicationLifecycleRetryBeginV4Receiver
import Kernel.ApplicationLifecycleRetryClaimV4Receiver
import Kernel.ApplicationLifecycleRetryCompletionV4Receiver
import Kernel.ApplicationShareIssueHistorical
import Kernel.ApplicationSpkProfileProofs
import Kernel.FnSelectedHistoricalStep
import Kernel.FnSelectiveReleaseProofs
import Kernel.Job  -- docs/COMPUTE.md §8 C1: the job lifecycle as one Pred law (native/resource-client/templates/job/law.job); both poles per edge, no_double_settle, bond_slashed_iff_mismatch, settle_requires_match_or_timeout, caller_cannot_forge_truth
import Kernel.AppsRequest  -- APP-MARKET: the app-install request law (the template is its rendering): choice_frozen_after_setup, outcome_once_by_manager, no_install_no_revoke
import Kernel.SealedMarket  -- SEALED-MARKET: the sealed-bid market law (the template is its rendering) and its guarantees

-- Previously orphaned general carry claims and their regression gates.
import Theory.CheckedCarry
import Verify.JointDecisionRecovery
-- The Objective Bend front end's compiled vectors (the front end itself is reached through Host.Main).
import Compiler.Sha256Vectors
import Compiler.ObjectiveBendC4Vectors
