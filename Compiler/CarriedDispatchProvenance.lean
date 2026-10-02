/-
Exact opaque descriptor commitments from an audited old grain issue.
The stable outer wire is decoded; no old descriptor is decoded or re-encoded
under the target registry. This preserves the issuer's original scope digests.
-/
import Compiler.CarriedApplicationProvenance
import Compiler.GrainResourceBirthHostCodec

namespace Minidregg.Compiler.CarriedDispatchProvenance

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.CarriedApplicationProvenance
open Minidregg.Kernel
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure CarriedDispatchIssue (config : Config) (current : Durable) where
  private mk ::
  issue : CarriedIssue config current
  raw : GrainResourceBirthPolicyController.SignedIngress
  rawExact : GrainResourceBirthPolicyController.ingressCodec.decode issue.ingress.grainIngress =
    some raw
  wire : GrainResourceBirthHostCodec.SourceWire
  sourceCanonical : GrainResourceBirthHostCodec.sourceFrame ++
    GrainResourceBirthHostCodec.sourceWireStream.encode wire = raw.sourceBytes

def CarriedDispatchIssue.originalSourceBytes {config : Config} {current : Durable}
    (selected : CarriedDispatchIssue config current) : List UInt8 :=
  ApplicationShareIssueSource.sourceBytesFromDescriptorBytes selected.issue.spec selected.wire.1

/-- Selection is authenticated before any descriptor-byte extraction. The old
native audit supplies the meaning of the opaque descriptor and its source. -/
def fromIssue {config : Config} {current : Durable} (issue : CarriedIssue config current) :
    Except String (CarriedDispatchIssue config current) := do
  match rawExact : GrainResourceBirthPolicyController.ingressCodec.decode issue.ingress.grainIngress with
  | none => throw "carried grain issue outer signed carrier differs"
  | some raw =>
    if raw.sourceBytes.length > GrainResourceBirthPolicyController.maxSourceBytes then
      throw "carried grain issue source exceeds original bound"
    if raw.sourceBytes.take GrainResourceBirthHostCodec.sourceFrame.length !=
        GrainResourceBirthHostCodec.sourceFrame then
      throw "carried grain source wire version unsupported"
    let some wire := GrainResourceBirthHostCodec.sourceWireStream.toLawful.decode
        (raw.sourceBytes.drop GrainResourceBirthHostCodec.sourceFrame.length)
      | throw "carried grain source wire malformed"
    if sourceCanonical : GrainResourceBirthHostCodec.sourceFrame ++
        GrainResourceBirthHostCodec.sourceWireStream.encode wire = raw.sourceBytes then
      return ⟨issue, raw, rawExact, wire, sourceCanonical⟩
    else throw "carried grain source wire noncanonical"

/-- No caller chooses an unauthenticated descriptor or issue certificate.
The exact outer issue bytes choose their original retained absolute index. -/
def select {config : Config} {current : Durable}
    (custody : CarriedSegmentIO.PreservedPrefix config current) (issueBytes : List UInt8) :
    Except String (CarriedDispatchIssue config current) := do
  let some index := custody.source.durable.image.accepted.findIdx? (fun record =>
      record.event.codecVersion == 22 && record.event.canonicalBytes == issueBytes)
    | throw "carried dispatch issue absent from retained original profile"
  let issue ← selectIssue custody index
  fromIssue issue

theorem CarriedDispatchIssue.descriptor_bytes_opaque {config : Config} {current : Durable}
    (selected : CarriedDispatchIssue config current) :
    selected.originalSourceBytes =
      ApplicationShareIssueSource.sourceBytesFromDescriptorBytes
        selected.issue.spec selected.wire.1 := rfl

end Minidregg.Compiler.CarriedDispatchProvenance
