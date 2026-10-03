/- Immutable source lookup below the native transaction dependency. Actual
current observe admission and CAS dependencies belong to the receiving caller.
This module provides canonical content/schema/core identity, not authority. -/
import Compiler.BendWorldProgramCodec
import Compiler.BendCoreAdmission
import Kernel.ContentResource
namespace Minidregg.Kernel.BendArtifactSource
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

def schema : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.SOURCE-SCHEMA/v1".toUTF8.toList []).digest

def checkedArtifact (artifact : BendWorldProgramCodec.Artifact) : Bool :=
  match BendCoreAdmission.admit artifact.book with
  | .error _ => false
  | .ok core => (BendCoreAdmission.entry core artifact.entry).isOk

def lookup (store : ContentResource.ContentStore) (id : AtomId) :
    Option BendWorldProgramCodec.Artifact := do
  let record ← Hyperdocument.lookup store .atoms id
  if record.tombstonedAt.isSome then none else do
    let .inlineObject selectedSchema := record.kind | none
    if selectedSchema != schema then none else do
      let artifact ← BendWorldProgramCodec.decode record.payload
      if BendWorldProgramCodec.wellFormed artifact && checkedArtifact artifact &&
          decide (BendWorldProgramCodec.artifactId artifact = id.digest) then
        some artifact
      else none
end Minidregg.Kernel.BendArtifactSource
