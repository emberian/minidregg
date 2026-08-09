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

/- Materialize the generated data-only Rust integration surface. -/
#eval buildTarget.run

end Minidregg.Compiler.MinidreggV1NativeGlue
