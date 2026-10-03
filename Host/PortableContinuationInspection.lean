/- Narrow actual-source capture/restore consumer. The existing native session
and genesis re-admission walk supply source truth. No synthetic app-counter
image, supplied root summary, manifest flag or private archive is admission.
No service deployment or current-source successor activation is performed here.
-/
import Kernel.NativeHostSession
import Compiler.PortableContinuationArchiveIO

namespace Minidregg.Host.PortableContinuationInspection
open Minidregg.Kernel
open Minidregg.Compiler
open Minidregg.Kernel.PortableContinuationManifest
set_option autoImplicit false

structure Audited (config : NativeHost.Config) where
  private mk ::
  manifest : Manifest
  source : NativeHostSession.Walked config
  exactImage : manifest.image = DurableReceiverCodec.encode source.target.image

/-- Preserve actual genesis-walk provenance while deriving one full custody image.
This accepts a verified native walk, never an arbitrary source image. -/
def fromWalked (config : NativeHost.Config) (source : NativeHostSession.Walked config)
    (generation : Nat) (predecessor : Bytes) (artifacts : List Artifact) : Audited config :=
  let identity : Identity := ⟨config.deployment.domain,config.profile.semantics,config.expectedSeed⟩
  let manifest := PortableContinuationManifestCodec.fromImage identity source.target.image
    generation predecessor artifacts
  ⟨manifest,source,rfl⟩

/-- Inventories are supplied by the existing pause/custody/obligation owners.
Their completeness must be source-derived before activation; this API makes
no completeness claim for an arbitrary list of physical inventory blobs. -/
def capture (config : NativeHost.Config) (generation : Nat) (predecessor : Bytes)
    (artifacts : List Artifact) : IO (Except String (Audited config)) := do
  match ← NativeHostSession.startWalked config with
  | .error detail => return .error detail
  | .ok source =>
    let identity : Identity := ⟨config.deployment.domain, config.profile.semantics, config.expectedSeed⟩
    let manifest := PortableContinuationManifestCodec.fromImage identity source.target.image
      generation predecessor artifacts
    return .ok ⟨manifest, source, rfl⟩

/-- Reopening a repaired independent Store must reproduce the WHOLE exact image
and re-admit all records under the original pinned native source configuration.
Returning an audited candidate does not activate an old worker or new holder. -/
def checkRestored (config : NativeHost.Config) (pin : ParticipantPin)
    (sourceRequired : List Artifact) (manifest : Manifest)
    (extension : ReceiptContinuity.Extension) : IO (Except String (Audited config)) := do
  let identity : Identity := ⟨config.deployment.domain, config.profile.semantics, config.expectedSeed⟩
  if manifest.prefix.identity != identity then return .error "portable source identity differs"
  match ← NativeHostSession.startWalked config with
  | .error detail => return .error detail
  | .ok source =>
    if exactImage : manifest.image = DurableReceiverCodec.encode source.target.image then
      if manifest.prefix != PortableContinuationManifestCodec.prefixOf identity source.target.image ||
          manifest.point != PortableContinuationManifestCodec.pointOf identity source.target.image then
        return .error "portable complete image or public endpoint differs"
      match acceptRepair pin sourceRequired manifest extension with
      | none => return .error "portable acknowledged history or source obligation missing"
      | some _ => return .ok ⟨manifest, source, exactImage⟩
    else return .error "portable restored complete source image differs"

end Minidregg.Host.PortableContinuationInspection
