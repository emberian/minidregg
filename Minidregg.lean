/-
# Minidregg — root module.

Imports every per-directory root so the default `lake build` target covers the
whole tree. The carve is ATLAS.md §7; the import boundary between the
candidate-independent `Theory`/`Loom` libs and everything else is mechanically
enforced by `scripts/check-import-boundary.sh`.
-/
import Theory      -- candidate-independent core: verify/find seam, Holds, product camera
import Kernel      -- the 3 verbs (create · gwrite · move) over the camera; hyperedge turn shape
import Pred        -- the ONE predicate algebra, syntactic AST end-to-end
import Effects     -- open handler registry: one declaration per effect, proof fields for the floor
import Compiler    -- arithmetization spine: syntactic-leaf IR + fold_unique
import Loom        -- the proof system
import Assurance   -- generated ledger machinery: pins, keystone audit, Bound/Forced
