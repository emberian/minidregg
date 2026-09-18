/-
# Minidregg — root module.

Imports every per-directory root so the default `lake build` target covers the
whole tree. The carve is ATLAS.md §7; the import boundary between the
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
import Compiler.DeclaredEffectPageRegistry  -- bounded declared-effect pages enter the dependent cell registry
import Selvage        -- the proof system
import Assurance   -- generated ledger machinery: pins, keystone audit, Bound/Forced
import Assurance.CredentialFoundationMigrationAudit  -- exact pins for revision/generation separation and explicit delegation
import Compiler.DistributiveLaw  -- N4 stated and inhabited: DistLaw over a Signature's polynomial functor and a PFunctor behaviour, Bialgebra, the initial (Term, opModel) and final (PFunctor.M, denModel) bialgebras, N4_adequacy (fold denModel = M.corec opModel, the unique bialgebra morphism) and N4_congruence; FailClosed as a SEPARATE keystone with teeth — strictLaw and openLaw are BOTH laws (laws_inhabited), only one is fail-closed, and open_joint_commits exhibits the half-committed joint turn by rfl. Rooted here rather than in Compiler.lean, which carries uncommitted owner edits. Residuals [N4-home] [N4-hyperedge-instance] [N4-gsos]
