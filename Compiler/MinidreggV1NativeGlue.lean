/-
# Compiler.MinidreggV1NativeGlue — concrete generated Rust glue target

This module binds the concrete `MinidreggV1Artifact.bundle` to the generic
data-only native glue generator.  Evaluation writes constants, DTOs, and the
buffer/error work-dispatch trait only.  It creates no Rust verifier, semantic
decision, policy procedure, or acceptance API.
-/
import Compiler.MinidreggV1Artifact
import Compiler.NativeGlueGen

namespace Minidregg.Compiler.MinidreggV1NativeGlue

/-- Concrete, Lean-owned source generation target for the V1 artifact. -/
def buildTarget : Minidregg.Compiler.NativeGlueGen.BuildTarget where
  path := "prover/generated/semantic_artifact_v1.rs"
  bundle := Minidregg.Compiler.MinidreggV1Artifact.bundle
  nativeCatalogWellFormed :=
    Minidregg.Compiler.MinidreggV1Artifact.bundle_native_catalog_wellFormed

/-- The generated dispatch catalog is literally the catalog inside the
canonical artifact encoding; there is no generator-local work selector. -/
theorem generated_catalog_is_authenticated :
    buildTarget.bundle.canonicalEncoding.nativeWorkCatalog =
      [Minidregg.Compiler.MinidreggV1Artifact.tower256DotProductWork] := by
  rfl

theorem generated_source_is_artifact_derived :
    Minidregg.Compiler.NativeGlueGen.rustSource buildTarget.bundle
        buildTarget.nativeCatalogWellFormed =
      Minidregg.Compiler.NativeGlueGen.rustSourceFromEncoding
        buildTarget.bundle.canonicalEncoding := by
  rfl

/- Materialize the generated data-only Rust integration surface. -/
#eval buildTarget.run

/-- info: 'Minidregg.Compiler.MinidreggV1NativeGlue.generated_catalog_is_authenticated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms generated_catalog_is_authenticated
/-- info: 'Minidregg.Compiler.MinidreggV1NativeGlue.generated_source_is_artifact_derived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms generated_source_is_artifact_derived

end Minidregg.Compiler.MinidreggV1NativeGlue
