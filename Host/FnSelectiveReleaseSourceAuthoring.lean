/-
Source-owned signing plan for an explicit selected-publication request. The
source Mini image selects the current content page and current signing key;
only exact canonical header bytes leave for custody signing. Assembly is not
admission. The source receiver checks the native signature, `.delegateObject`
capability, installed law, selected content and root before durable settlement.
-/
import Kernel.FnSelectiveReleaseSourceAuthority
import Kernel.NativeHostContext

namespace Minidregg.Host.FnSelectiveReleaseSourceAuthoring

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.FnSelectiveReleaseSignature
open Minidregg.Kernel.FnSelectiveReleaseSourcePublication

set_option autoImplicit false

structure Plan where
  specBytes : List UInt8
  headerBytes : List UInt8
  sourceRoot : Minidregg.Theory.TypedAuthorization.Digest

def planLoaded (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (packetBytes : List UInt8) (delegateCapability :
      Minidregg.Theory.TypedAuthorization.CapabilityId) :
    Except String Plan := do
  let some packet := packetCodec.decode packetBytes
    | throw "selected source packet is noncanonical"
  let spec : Spec := ⟨packet, delegateCapability⟩
  let context : ResourceObservationAdmission.Context config.deployment opened.durable :=
    ⟨opened.directory, opened.authority⟩
  let prepared ← FnSelectiveReleaseSourceAuthority.prepare context config.profile
    config.federation (NativeHost.logicalHeight config opened.durable) spec
  let header ← (CredentialSignatureAdmission.signingHeader
    opened.authority.snapshot (marker spec) ⟨.object, prepared.wanted⟩).mapError
      (fun _ => "selected source signer refused")
  pure ⟨specCodec.encode spec,
    CredentialSignedEnvelopeController.headerCodec.encode header,
    prepared.root⟩

def assemble (specBytes envelopeBytes : List UInt8) : Except String (List UInt8) := do
  let some spec := specCodec.decode specBytes
    | throw "selected source spec is noncanonical"
  let some _ := CredentialSignatureAdmission.canonicalEnvelopeCodec.decode envelopeBytes
    | throw "selected source envelope is noncanonical"
  pure <| ingressCodec.encode ⟨spec, envelopeBytes⟩

end Minidregg.Host.FnSelectiveReleaseSourceAuthoring
