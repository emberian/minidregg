/-
Source-owned signing plan for an explicit selected-publication request. The
source Mini image selects the current content page and current signing key;
only exact canonical header bytes leave for custody signing. Assembly is not
admission. The source receiver checks the native signature, `.delegateObject`
capability, installed law, selected content and root before durable settlement.
-/
import Kernel.FnSelectiveReleaseSourceAuthority
import Kernel.FnSelectiveReleaseArticle
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

def assemble (specBytes headerBytes signatureBytes : List UInt8) :
    Except String (List UInt8) := do
  let some spec := specCodec.decode specBytes
    | throw "selected source spec is noncanonical"
  let some header := CredentialSignedEnvelopeController.headerCodec.decode headerBytes
    | throw "selected source signing header is noncanonical"
  if CredentialSignedEnvelopeController.headerCodec.encode header != headerBytes then
    throw "selected source signing header is noncanonical"
  if signatureBytes.length != 64 then
    throw "selected source signature must be 64 bytes"
  let envelopeBytes := CredentialSignatureAdmission.canonicalEnvelopeCodec.encode
    ⟨header, signatureBytes⟩
  pure <| ingressCodec.encode ⟨spec, envelopeBytes⟩

/-- A source authorization event binds the packet, not arbitrary fn bytes.
Check the exact canonical article before custody transfers it to fn. -/
def checkArticle (packetBytes articleBytes : List UInt8) : Except String Unit := do
  let some packet := packetCodec.decode packetBytes
    | throw "selected source packet is noncanonical"
  let article ← FnSelectiveReleaseArticle.extract articleBytes
  unless article.packet == packet do
    throw "selected source article carries a different packet"
  let canonical ← article.render
  unless canonical == articleBytes do
    throw "selected source article bytes are noncanonical"

def checkIngressArticle (ingressBytes articleBytes : List UInt8) : Except String Unit := do
  let some ingress := ingressCodec.decode ingressBytes
    | throw "selected source ingress is noncanonical"
  checkArticle (packetCodec.encode ingress.spec.packet) articleBytes

end Minidregg.Host.FnSelectiveReleaseSourceAuthoring
