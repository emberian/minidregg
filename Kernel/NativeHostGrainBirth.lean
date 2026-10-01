/-
Source-owned signing plan for the grain-backed birth. The public host first
authorizes the exact observation footprint; this helper then finalizes only
authority-allocated auxiliary cells and derives every current signing header.
-/
import Kernel.NativeHostContext
import Kernel.GrainResourceBirthAdmission
import Compiler.GrainResourceBirthHostCodec

namespace Minidregg.Kernel.NativeHostGrainBirth

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.GrainResourceBirthHostCodec
open Minidregg.Kernel.NativeHost
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local irreducible] NativeHost.Config.profile
  CanonicalRuntimeProfile.Profile.compilerProfile

private def slot (snapshot : CredentialAuthorityDomain.Snapshot)
    (marker role index : Nat) (wanted : PackedEffectRequest) :
    Except String SigningSlot := do
  let header ← (CredentialSignatureAdmission.signingHeader snapshot marker wanted).mapError
    (fun reason => s!"signing key selection: {repr reason}")
  pure ⟨role, index, CredentialSignedEnvelopeController.headerCodec.encode header⟩

def branchLabel {tariff : GrainResourceBirthController.Tariff}
    {source : GrainResourceBirthController.Source} :
    GrainResourceBirthAdmission.Branch tariff source → Nat × Nat
  | .inl .factory => (0, 0)
  | .inl .authority => (1, 0)
  | .inl (.allocation index) => (2, index.val)
  | .inl (.source index) => (3, index.val)
  | .inr index => (4, index.val)

/-- Output bytes retain the complete source with source-generated auxiliary
creates and its derived command. Detached assembly copies the inner source
bytes into strict ingress; the input must still be an unfinalized draft. -/
def prepareLoaded (config : Config) (opened : Opened config)
    (sourceBytes : List UInt8) (capabilities : List CapabilityId) :
    Except String (List UInt8 × List SigningSlot) := do
  let source ← need "noncanonical grain-backed birth source"
    (sourceCodec.decode sourceBytes)
  let tariff ← config.grainBirthTariffValue
  let profile := config.profile
  let marker := GrainResourceBirthAdmission.useMarker profile config.deployment tariff source
  let draft ← (ResourceBirthController.Concrete.prepareGrainDraft profile.compilerProfile
    profile.disabledEvaluators config.deployment opened.pins opened.durable source.birth marker).mapError
      (fun reason => s!"grain-backed birth draft: {repr reason}")
  let source := source.withAuxiliaryCreates draft.descriptor.auxiliaryCreates
  let birth ← (GrainResourceBirthController.prepareSourceBirth profile.compilerProfile
    profile.disabledEvaluators config.deployment opened.pins opened.durable profile.semantics tariff source).mapError
      (fun reason => s!"grain-backed birth preparation: {repr reason}")
  let ambient : DeclaredResourceController.Ambient :=
    ⟨config.federation, logicalHeight config opened.durable⟩
  let grain ← (GrainResourceBirthTransaction.prepareTargets profile config.deployment
    opened.pins opened.durable ambient tariff source birth).mapError
      (fun reason => s!"grain-backed target preparation: {repr reason}")
  let _pending ← (GrainResourceBirthAdmission.preparePending profile config.deployment
    opened.pins opened.durable ambient tariff source birth grain).mapError
      (fun reason => s!"grain-backed tuple preparation: {repr reason}")
  check (capabilities.length == source.birth.resourceBatch.operations.length)
    "grain-backed birth source capability count mismatch"
  let snapshot := birth.prepared.pre.authority.snapshot
  let marker := GrainResourceBirthAdmission.useMarker profile config.deployment tariff source
  let branches ← (GrainResourceBirthAdmission.branches tariff source).mapM fun branch =>
    let label := branchLabel branch
    slot snapshot marker label.1 label.2
      (GrainResourceBirthAdmission.branchRequest birth grain ambient.height branch)
  let observations ← (List.finRange (source.grainCommand tariff).targets.length).mapM
    fun index => slot snapshot marker 8 index.val
      ⟨(source.grainCommand tariff).targets[index].kind,
        GrainResourceBirthAdmission.readRequest birth grain index⟩
  let finalized := finalizedCodec.encode
    ⟨sourceCodec.encode source,
      DeclaredResourceController.commandCodec.encode (source.grainCommand tariff)⟩
  pure (finalized, branches ++ observations)

end Minidregg.Kernel.NativeHostGrainBirth
