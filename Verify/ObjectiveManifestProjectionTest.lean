import Verify.ObjectiveManifest

open Lean

namespace Minidregg.ObjectiveManifestProjectionTest

/-- A raw projection whose structure type is its only named constant. -/
def projectionOnly : Expr := .proj `ProjectionOnlyStructure 0 (.bvar 0)

-- `usedConstants` runs a pointer-cached traversal in `ST`, so kernel reduction cannot prove the
-- result by `rfl`. This elaboration-time check fails the module build if the edge disappears.
run_meta
  unless ObjectiveManifest.usedConstants projectionOnly |>.contains `ProjectionOnlyStructure do
    throwError "objective manifest collector omitted ProjectionOnlyStructure from raw Expr.proj"

end Minidregg.ObjectiveManifestProjectionTest
