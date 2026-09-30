/-
Owner-side authoring for one selected public content atom. A signed Mini query
authorizes the exact current resource read. This constructs an owner signature
preimage; it does not attest that a claimed historical source operation was
accepted. The recipient separately verifies the signature and current law.
-/
import Host.Json
import Kernel.FnSelectiveReleaseArticle
import Kernel.FnSelectiveReleaseIngress
import Kernel.ContentResource

namespace Minidregg.Host.FnSelectiveReleaseAuthoring

open Lean
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.FnSelectiveRelease
open Minidregg.Kernel.FnSelectiveReleaseSignature
open Minidregg.Kernel.FnSelectiveReleaseArticle
open Minidregg.Kernel.FnSelectiveReleaseIngress
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument

set_option autoImplicit false

structure Request where
  signedQuery : List UInt8
  atom : AtomId
  destination : Destination
  owner : OwnerScope
  fromMailbox : String
  date : String
  subject : String

structure Prepared where
  release : Release
  preimage : List UInt8
  sourceRoot : Digest
  selectedAtom : AtomId

private def requestFields : List String :=
  ["signedQueryHex", "atom", "destinationDomain", "destinationSemantics",
   "destinationTarget", "group", "messageId", "policyRoot", "keysetRoot",
   "epoch", "ownerSubject", "ownerNonce", "expiresAt", "from", "date",
   "subject"]

private def fail {α : Type} (reason : String) : Except String α :=
  .error s!"selected-release authoring: {reason}"

private def member (object : Std.TreeMap.Raw String Lean.Json compare)
    (name : String) : Except String Lean.Json :=
  match object.get? name with
  | some value => .ok value
  | none => fail s!"missing {name}"

private def textField (object : Std.TreeMap.Raw String Lean.Json compare)
    (name : String) : Except String String := do
  match (← member object name).getStr? with
  | .ok value => pure value
  | .error _ => fail s!"{name} must be a string"

private def natField (object : Std.TreeMap.Raw String Lean.Json compare)
    (name : String) : Except String Nat := do
  let value ← textField object name
  let some number := value.toNat?
    | fail s!"{name} must be canonical decimal"
  unless toString number == value do fail s!"{name} must be canonical decimal"
  pure number

/-- No implicit owner, resource, or source bytes enter authoring. The signed
query supplies the selected resource; the current native view supplies bytes
and parent root. Duplicate/unknown JSON keys are rejected. -/
def parseRequest (source : String) : Except String Request := do
  unless source.toUTF8.size ≤ 262144 do fail "request JSON exceeds bound"
  let json ← Minidregg.Host.Json.parse source
  let object ← json.getObj?.mapError (fun _ => "selected-release request must be an object")
  let names := object.foldl (init := []) (fun names key _ => key :: names)
  unless names.length == requestFields.length &&
      names.all (fun name => requestFields.contains name) do
    fail "request has missing or unknown fields"
  let queryHex ← textField object "signedQueryHex"
  unless queryHex.length ≤ 131072 do fail "signed query exceeds bound"
  let signedQuery ← Minidregg.Host.Json.decodeHex "signedQueryHex" (.str queryHex)
  let atom : AtomId := ⟨⟨← natField object "atom"⟩⟩
  let policyRoot : Digest := ⟨← natField object "policyRoot"⟩
  let epoch ← natField object "epoch"
  let destination : Destination :=
    { domain := ⟨← natField object "destinationDomain"⟩
      semantics := ⟨← natField object "destinationSemantics"⟩
      target := ← natField object "destinationTarget"
      group := (← textField object "group").toUTF8.toList
      messageId := (← textField object "messageId").toUTF8.toList
      audience := ⟨.publicPeerable, policyRoot,
        ⟨← natField object "keysetRoot"⟩, epoch⟩ }
  let owner : OwnerScope :=
    { policyRoot := policyRoot
      subject := ← natField object "ownerSubject"
      epoch := epoch
      nonce := ⟨← natField object "ownerNonce"⟩
      expiresAt := ← natField object "expiresAt" }
  pure ⟨signedQuery, atom, destination, owner,
    ← textField object "from", ← textField object "date",
    ← textField object "subject"⟩

private def selectedPayload (view : List UInt8) (atom : AtomId) :
    Except String (Digest × List UInt8) := do
  let some (packed, _) := NativeObservationController.resourceViewCodec.decode view
    | fail "noncanonical signed resource view"
  let some cell := Minidregg.Theory.CellRegistry.PackedCell.decode
      CanonicalCellRegistry.registry packed
    | fail "noncanonical resource cell"
  match cell with
  | ⟨.content, materialized⟩ =>
      let some record := Minidregg.Theory.Hyperdocument.lookup materialized.logical .atoms atom
        | fail "selected atom is absent from the current content cell"
      unless record.tombstonedAt.isNone && !record.payload.isEmpty do
        fail "selected atom is tombstoned or empty"
      pure (materialized.root, record.payload)
  | _ => fail "selected source is not a content resource"

/-- Reads only an exact current atom through the existing signed observation
gate, then binds its content cell root and bytes into the canonical owner preimage. -/
def prepareLoaded (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (request : Request) : IO (Except String Prepared) := do
  let some signed := NativeObservationCodec.signedCodec.decode request.signedQuery
    | return fail "noncanonical signed source query"
  let .query query := signed.challenge.intent.purpose
    | return fail "source observation is not a query"
  unless query.kind == .object && query.view == .resource do
    return fail "source query must read an object resource"
  let [grant] := signed.challenge.intent.grants
    | return fail "source query must contain one exact grant"
  unless grant.kind == .object && grant.target == query.target do
    return fail "source query grant differs from selected target"
  unless signed.challenge.intent.subject.value == request.owner.subject do
    return fail "source query subject differs from proposed release owner"
  let .ok view ← NativeHost.queryLoaded config opened request.signedQuery
    | return fail "signed source query refused"
  let .ok (root, content) := selectedPayload view request.atom
    | return fail "selected atom could not be read"
  let release : Release :=
    { source := ⟨config.deployment.domain, config.profile.semantics,
        query.target, root, request.atom.digest.value⟩
      destination := request.destination
      owner := request.owner
      content := content }
  unless release.bounded && release.destination.audience.visibility == .publicPeerable do
    return fail "selected public release exceeds profile"
  return .ok ⟨release, signedPreimage release, root, request.atom⟩

def prepareJsonLoaded (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (source : String) : IO (Except String Prepared) := do
  match parseRequest source with
  | .error reason => return .error reason
  | .ok request => prepareLoaded config opened request

/-- Exact source-owned validation gate for custody signing. This checks bytes
and public transport profile, not a claim of source-history admission. -/
def checkPreimage (preimage : List UInt8) : Except String Release := do
  unless preimage.length ≤ FnEvidenceCodec.maxCarrierBytes + 4096 do
    fail "owner preimage exceeds bound"
  let some release := releaseCodec.decode preimage
    | fail "noncanonical owner preimage"
  unless signedPreimage release == preimage && release.bounded &&
      release.destination.audience.visibility == .publicPeerable do
    fail "owner preimage is unbounded or not public-peerable"
  let sample : Article :=
    ⟨"owner@example.invalid", "Sun, 27 Sep 2026 12:00:00 +0000",
      "Selected release", ⟨release, List.replicate 64 0⟩⟩
  let _ ← sample.render
  pure release

/-- Assembly accepts only a canonical preimage and 64-byte detached signature.
The signature's *validity* is checked at recipient admission, not inferred here. -/
def assemble (preimage signature : List UInt8)
    (fromMailbox date subject : String) : Except String (List UInt8 × List UInt8) := do
  unless signature.length == 64 do fail "owner signature must contain 64 bytes"
  let release ← checkPreimage preimage
  let packet : Packet := ⟨release, signature⟩
  let article : Article := ⟨fromMailbox, date, subject, packet⟩
  let source ← article.render
  pure (packetCodec.encode packet, source)

/-- Canonical ingress assembly only. Caller-supplied capability and roots are
rechecked against the recipient's current opened state by admission. -/
def assembleIngress (packetBytes : List UInt8) (capability : CapabilityId)
    (targetRoot : Digest) : Except String (List UInt8) := do
  let some packet := packetCodec.decode packetBytes
    | fail "noncanonical owner packet"
  unless packet.signature.length == 64 && packet.release.bounded do
    fail "owner packet exceeds release profile"
  pure <| ingressCodec.encode ⟨packet, capability, targetRoot⟩

end Minidregg.Host.FnSelectiveReleaseAuthoring
