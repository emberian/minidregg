/- Operator-local receiving for the closed neutral policy lift. The signing
request supplies artifact custody and a nonce, never replacement state or an
admission assertion. Independent operator authority comes from Host settings.
This module stages a verified target; it never publishes a live service pointer. -/
import Compiler.NeutralCarriedSegmentIO
import Host.CarryInspection
import Host.Json

namespace Minidregg.Host.NeutralCarryReceiving

open Lean
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.CarriedSegment

set_option autoImplicit false

private def field (value : Json) (name : String) : Except String Json := value.getObjVal? name
private def stringField (value : Json) (name : String) : Except String String :=
  (field value name).bind Json.getStr?
private def hex32 (value : Json) : Except String (List UInt8) := do
  let text ← value.getStr?
  let bytes ← Minidregg.Host.Json.decodeHex "carry artifact" value
  if bytes.length != 32 || CarryInspection.encodeHex bytes != text then
    throw "carry artifact requires canonical lowercase 32-byte hexadecimal"
  pure bytes

private def parseCapsule (value : Json) : Except String CarriedSegmentIO.SourceCapsule := do
  let path := fun name => System.FilePath.mk <$> stringField value name
  let pins ← field value "pins"
  return {
    host := ← path "host"
    configuration := ← path "configuration"
    profile := ← path "profile"
    signatureVerifier := ← path "signatureVerifier"
    storage := { binary := ← path "storageBinary", root := ← path "storageRoot",
      key := ← path "checkpointKey" }
    identity := ← CarryInspection.parseIdentity (← field value "identity")
    pins := {
      host := ← hex32 (← field pins "host")
      storageHelper := ← hex32 (← field pins "storageHelper")
      signatureVerifier := ← hex32 (← field pins "signatureVerifier")
      configuration := ← hex32 (← field pins "configuration")
      profile := ← hex32 (← field pins "profile") } }

private def request (value : Json) : Except String
    (CarriedSegmentIO.SourceCapsule × CarriedSegmentIO.SourceCapsule × List UInt8) := do
  if (← stringField value "algorithm") != "minidregg-neutral-policy-carry-v1" then
    throw "unsupported carry transformation request"
  return (← parseCapsule (← field value "source"),
    ← parseCapsule (← field value "target"), ← hex32 (← field value "nonce"))

/-- Reviewable exact endpoints and detached signing bytes. The unsigned edge
is not a receiving certificate until its signature is installed and verified. -/
def plan (config : NativeHost.Config) (currentConfiguration : System.FilePath)
    (trustedOperator : List UInt8) (value : Json) :
    IO (Except String Json) := do
  let .ok (source, target, nonce) := request value | return .error "invalid carry request"
  if target.configuration != currentConfiguration then
    return .error "carry target must be the configuration running this receiver"
  match ← NeutralCarriedSegmentIO.prepare config source target trustedOperator nonce with
  | .error detail => return .error detail
  | .ok prepared =>
      let edge := NeutralCarriedSegmentIO.unsignedEdge config prepared
      return .ok <| Json.mkObj [
        ("algorithm", .str "minidregg-neutral-policy-carry-plan-v1"),
        ("edge", CarryInspection.edgeJson edge),
        ("signingBytes", .str (CarryInspection.encodeHex edge.signingBytes))]

/-- Re-derive against actual retained state, verify the independent authority,
and stage one exact carry. Its registry is operator-private output. -/
def receive (config : NativeHost.Config) (currentConfiguration : System.FilePath)
    (trustedOperator : List UInt8) (value edgeValue : Json) : IO (Except String Json) := do
  let .ok (source, target, nonce) := request value | return .error "invalid carry request"
  if target.configuration != currentConfiguration then
    return .error "carry target must be the configuration running this receiver"
  let .ok edge := CarryInspection.parseSeal edgeValue | return .error "invalid carry edge"
  if edge.body.nonce != nonce then return .error "carry nonce differs from prepared request"
  match ← NeutralCarriedSegmentIO.receive config source target trustedOperator edge with
  | .error detail => return .error detail
  | .ok opened =>
      return .ok <| Json.mkObj [
        ("algorithm", .str "minidregg-neutral-policy-carry-staged-v1"),
        ("height", .str (toString opened.durable.height)),
        ("worldRoot", .str (toString opened.durable.worldRoot.value)),
        ("registry", Json.mkObj [("source", (field value "source").toOption.getD .null),
          ("edge", CarryInspection.edgeJson edge)])]

end Minidregg.Host.NeutralCarryReceiving
