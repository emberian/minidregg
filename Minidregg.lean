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
