import Verify.ObjectiveManifest

open Lean

namespace Minidregg.ObjectiveManifestProjectionTest

/-- The manifest collector reaches a structure type carried only by a raw projection. -/
theorem raw_projection_collects_structure_type :
    ObjectiveManifest.usedConstants (.proj `ProjectionOnlyStructure 0 (.bvar 0)) =
      #[`ProjectionOnlyStructure] := by
  rfl

end Minidregg.ObjectiveManifestProjectionTest
