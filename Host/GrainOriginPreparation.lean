/-
Verified preparation of a complete-prefix Mini grain article source.

This is a read-only file-authoring boundary. The caller selects an independent
origin Config, exact bounded package bytes, article context and named targets.
The explicit disclosure intent records that the caller requested a source
containing the *whole* original Mini genesis and accepted prefix for the
selected Newsgroups audience. It is not a grant, consent proof, redaction,
fn signature, article admission, or public transport authorization.
-/
import Host.GrainOriginSource
import Compiler.Sp800185Cshake256Core

namespace Minidregg.Host.GrainOriginPreparation

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel
open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- Explicit local source-render request. The destination Newsgroups header is
not an enforced recipient set after fn peering; the acknowledgement is a
recorded operator statement, not proof of earlier contributors' consent. -/
structure DisclosureIntent where
  wholePrefixDisclosure : Bool
  destinationNewsgroup : String
  audienceAcknowledgement : String
  deriving DecidableEq, Repr

private def printableBounded (value : String) : Bool :=
  !value.isEmpty && value.length ≤ 256 && value.toUTF8.data.toList.all
    (fun b => 32 ≤ b.toNat && b.toNat ≤ 126)

def DisclosureIntent.valid (intent : DisclosureIntent)
    (context : GrainOriginSource.ArticleContext) : Bool :=
  intent.wholePrefixDisclosure &&
    intent.destinationNewsgroup == context.group &&
    printableBounded intent.audienceAcknowledgement && context.valid

/-- These digests identify exact byte strings for a later custody record. They
do not imply collision freedom as a Lean theorem, nor authorize disclosure. -/
def packageDigest (bytes : List UInt8) : List UInt8 :=
  cshake256Bytes "DREGG/FN/ORIGIN-PACKAGE/v1".toUTF8.toList bytes

def prefixDigest (bytes : List UInt8) : List UInt8 :=
  cshake256Bytes "DREGG/FN/ORIGIN-PREFIX/v1".toUTF8.toList bytes

structure FullPrefixScope where
  originDomain : Digest
  originSemantics : Digest
  originGenesisPin : Digest
  originalReceipt : Receipt
  acceptedCount : Nat
  packageLength : Nat
  packageDigest : List UInt8
  prefixLength : Nat
  prefixDigest : List UInt8
  destinationNewsgroup : String
  audienceAcknowledgement : String
  deriving Repr

structure Prepared where
  private mk ::
  disclosureIntent : DisclosureIntent
  scope : FullPrefixScope
  rendered : GrainOriginSource.Rendered

/-- Verify the entire original accepted Mini prefix against the independently
selected native config before rendering. A successful result is only a
prepared local source and its exact disclosure scope; public delivery is not
performed here. -/
def prepareForDisclosure (originConfig : NativeHost.Config)
    (packageBytes : List UInt8) (context : GrainOriginSource.ArticleContext)
    (selection : GrainOriginSource.Selection) (intent : DisclosureIntent) :
    IO (Except String Prepared) := do
  unless intent.valid context do
    return .error "explicit whole-prefix disclosure intent must name the article Newsgroups destination and acknowledge the broader audience"
  unless packageBytes.length ≤ FnEvidenceCodec.maxPackageBytes do
    return .error "Mini origin package exceeds selected portable profile"
  let receipt ← match ← FnEvidence.verify originConfig packageBytes with
    | .error detail => return .error s!"independent original prefix verification: {detail}"
    | .ok receipt => pure receipt
  let package ← match FnEvidenceCodec.decodeChecked packageBytes with
    | .error detail => return .error s!"verified package decode: {detail}"
    | .ok package => pure package
  let rendered ← match GrainOriginSource.render packageBytes receipt context selection with
    | .error detail => return .error detail
    | .ok rendered => pure rendered
  let scope : FullPrefixScope :=
    ⟨originConfig.deployment.domain, originConfig.profile.semantics,
      originConfig.expectedSeed, receipt, receipt.acceptedCount,
      packageBytes.length, packageDigest packageBytes,
      package.acceptedPrefix.length, prefixDigest package.acceptedPrefix,
      intent.destinationNewsgroup, intent.audienceAcknowledgement⟩
  return .ok ⟨intent, scope, rendered⟩

end Minidregg.Host.GrainOriginPreparation
