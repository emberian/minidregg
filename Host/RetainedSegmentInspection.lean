/- Operator-local dispatch for one retained, audited carry edge. Requests never
select paths, executables, a historical semantic implementation, or a trust key.
The immutable capsule must remain in operator custody throughout dispatch.
This initial registry supports one old segment, not arbitrary carry chains. -/
import Compiler.CarriedSegmentIO
import Host.CarryInspection

namespace Minidregg.Host.RetainedSegmentInspection

open Lean
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.CarriedSegment
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

def lookupAlgorithm : String := "minidregg-carried-call-lookup-v1"
def maxRawCall : Nat := 12102759
def maxLookupFrame : Nat := 12103788
def maxResponse : Nat := 1048576

/-- The trust key is separately configured operator authority, not seal content.
The carry staging boundary pins all target artifacts before publication.
Later compatible current-runtime upgrades retain their ordinary operator trust;
this historical service binds current identity, accepted event and endpoint. -/
structure Registry where
  capsule : CarriedSegmentIO.SourceCapsule
  edge : EdgeSeal
  trustedOperator : List UInt8

private def field (value : Json) (name : String) : Except String Json := value.getObjVal? name
private def stringField (value : Json) (name : String) : Except String String :=
  (field value name).bind Json.getStr?
private def liftResult {α : Type} (value : Except String α) : IO α := IO.ofExcept value
private def natural (value : Json) : Except String Nat := do
  let text ← value.getStr?
  if text.length > 80 then throw "integer exceeds bound"
  let some result := text.toNat? | throw "integer must be decimal"
  if toString result != text then throw "integer must be canonical decimal"
  return result
private def digest (value : Json) : Except String Digest := do
  let result ← natural value
  if result ≥ 2^256 then throw "digest exceeds 256 bits"
  return ⟨result⟩
private def parseIdentity (value : Json) : Except String Identity := do
  if (← stringField value "algorithm") != Kernel.ReceiptContinuity.algorithm then
    throw "identity algorithm differs"
  return ⟨← digest (← field value "domain"), ← digest (← field value "semantics"),
    ← digest (← field value "expectedSeed")⟩
private def continuityIdentity (value : Identity) : Kernel.ReceiptContinuity.Identity :=
  ⟨value.domain, value.semantics, value.genesis⟩

/-- Read only from an operator-local settings path, never from request bytes. -/
def parseRegistry (value : Json) (trustedOperator : List UInt8) : Except String Registry := do
  if trustedOperator.length != 32 then throw "retained registry requires an independent operator key"
  let edge ← CarryInspection.parseSeal (← field value "edge")
  let source ← field value "source"
  let path := fun name => System.FilePath.mk <$> stringField source name
  let capsule : CarriedSegmentIO.SourceCapsule := {
    host := ← path "host"
    configuration := ← path "configuration"
    profile := ← path "profile"
    signatureVerifier := ← path "signatureVerifier"
    storage := {
      binary := ← path "storageBinary"
      root := ← path "storageRoot"
      key := ← path "checkpointKey" }
    identity := edge.body.source
    pins := edge.body.sourceCapsule }
  return ⟨capsule, edge, trustedOperator⟩

/-- Bind the local capsule to the actual accepted carry record, the immutable
original Image, and the current new-profile endpoint. No semantic boolean or
self-asserted registry digest can replace these checks. -/
def validate (config : NativeHost.Config) (current : NativeHost.Durable)
    (registry : Registry) : IO (Except String CarriedSegmentIO.AuditedSource) := do
  try
    let body := registry.edge.body
    let configured : Identity := ⟨config.deployment.domain, config.profile.semantics, config.expectedSeed⟩
    if configured != body.target then return .error "retained registry target differs"
    if registry.capsule.identity != body.source || registry.capsule.pins != body.sourceCapsule then
      return .error "retained registry capsule differs"
    discard <| liftResult (checkPublic body.source registry.trustedOperator registry.edge)
    match ← CredentialSignatureIO.verify config.signature registry.trustedOperator
        registry.edge.signingBytes registry.edge.signature with
    | .ok true => pure ()
    | _ => throw (IO.userError "retained registry operator seal refused")
    let source ← liftResult (← CarriedSegmentIO.auditSource registry.capsule)
    if DurableReceiverCodec.seedStream.encode source.durable.image.seed !=
        DurableReceiverCodec.seedStream.encode current.image.seed then
      return .error "retained registry original seed differs"
    if (current.image.accepted.take body.cut.height).map DurableReceiverCodec.intentStream.encode !=
        source.durable.image.accepted.map DurableReceiverCodec.intentStream.encode then
      return .error "retained registry original prefix differs"
    let some record := current.image.accepted[body.cut.height]?
      | return .error "retained registry carry record absent"
    if record.transactionId != body.id || record.event.eventId != body.id ||
        record.event.canonicalBytes != body.bytes then
      return .error "retained registry carry event differs"
    let changes := record.writes.map fun write => (write.cellId, write.canonicalPostBytes)
    liftResult (checkBody registry.capsule.identity registry.trustedOperator source.durable body changes)
    let expected := DurableReceiver.IntentRecord.ofIntent (intent source.durable.snapshot body changes)
    if DurableReceiverCodec.intentStream.encode record != DurableReceiverCodec.intentStream.encode expected then
      return .error "retained registry carry intent differs"
    let selectedPrefix ← liftResult (DurableReceiverIO.loadImage ResourceBirthCodec.rootBytes
      current.logStart (current.prefixImage registry.edge.targetStart.height))
    if pointOf selectedPrefix != registry.edge.targetStart then
      return .error "retained registry new start differs"
    return .ok source
  catch _ => return .error "retained capsule validation failed"

/-- Recheck the exact old cut after dispatch; a concurrently extended or
replaced capsule cannot supply a response for this immutable registry entry. -/
private def unchanged (registry : Registry) : IO Unit := do
  let source ← liftResult (← CarriedSegmentIO.auditSource registry.capsule)
  if pointOf source.durable != registry.edge.body.cut ||
      imageDigest source.durable.image != registry.edge.body.sourceImage ||
      originIndexDigest source.durable.image != registry.edge.body.originIndex then
    throw (IO.userError "retained source changed during dispatch")

private def readBounded (path : System.FilePath) (bound : Nat) : IO (List UInt8) := do
  let file ← IO.FS.Handle.mk path .read
  let mut bytes := ByteArray.empty
  while bytes.size ≤ bound do
    let part ← file.read (bound + 1 - bytes.size).toUSize
    if part.isEmpty then return bytes.toList
    bytes := bytes ++ part
  throw (IO.userError "retained output exceeds bound")

private def readJsonBounded (path : System.FilePath) : IO Json := do
  let bytes ← readBounded path maxResponse
  let some text := String.fromUTF8? bytes.toByteArray
    | throw (IO.userError "retained output is not UTF-8")
  liftResult (Json.parse text)

/-- Only fixed readonly verbs are passed by callers below. No public socket,
submit, or application-start action is reachable from retained dispatch. -/
private def readonlyCli (registry : Registry) (args : Array String) : IO Bool :=
  CarriedSegmentIO.withExecutionConfig registry.capsule fun executionConfig => do
    let child ← IO.Process.spawn {
      cmd := "/usr/bin/timeout"
      args := #["--kill-after=2s", "30s", registry.capsule.host.toString,
        executionConfig.toString] ++ args
      stdin := .null
      stdout := .null
      stderr := .null }
    return (← child.wait) == 0

private def readExact (handle : IO.FS.Handle) (count : Nat) : IO ByteArray := do
  let mut bytes := ByteArray.empty
  while bytes.size < count do
    let part ← handle.read (count - bytes.size).toUSize
    if part.isEmpty then throw (IO.userError "truncated retained frame")
    bytes := bytes ++ part
  return bytes
private def lengthBytes (length : Nat) : ByteArray :=
  [UInt8.ofNat length, UInt8.ofNat (length / 256), UInt8.ofNat (length / 65536),
    UInt8.ofNat (length / 16777216)].toByteArray
private def frameLength (bytes : List UInt8) : Nat :=
  bytes.foldr (fun byte rest => byte.toNat + 256 * rest) 0

private def oldContinuity (registry : Registry) (payload : List UInt8) : IO Json :=
  CarriedSegmentIO.withExecutionConfig registry.capsule fun executionConfig => do
    let child ← IO.Process.spawn {
      cmd := "/usr/bin/timeout"
      args := #["--kill-after=2s", "30s", registry.capsule.host.toString,
        executionConfig.toString, "stdio"]
      stdin := .piped
      stdout := .piped
      stderr := .null }
    let (input, child) ← child.takeStdin
    try
      input.write (lengthBytes (payload.length + 1) ++ ((151 : UInt8) :: payload).toByteArray)
      input.flush
      let size := frameLength (← readExact child.stdout 4).toList
      if size < 1 || size > maxResponse + 1 then throw (IO.userError "retained continuity response bound")
      let bytes := (← readExact child.stdout size).toList
      if bytes.head? != some (151 : UInt8) then throw (IO.userError "retained continuity refused")
      let some text := String.fromUTF8? (bytes.drop 1).toByteArray
        | throw (IO.userError "retained continuity is not UTF-8")
      liftResult (Json.parse text)
    finally
      child.kill
      discard child.wait

/-- Historical roots come from the retained executable's 151 endpoint. Decode,
verify and reconstruct the hash-only response; never forward arbitrary JSON. -/
def serveContinuity (config : NativeHost.Config) (current : NativeHost.Durable)
    (registry : Registry) (payload : List UInt8) : IO (Except String (List UInt8)) := do
  try
    if payload.length > 65536 then return .error "retained continuity request exceeds bound"
    let some text := String.fromUTF8? payload.toByteArray
      | return .error "retained continuity request malformed"
    let request ← liftResult (Json.parse text >>= ReceiptContinuity.parseRequest)
    if request.query.identity != continuityIdentity registry.edge.body.source then
      return .error "retained continuity origin differs"
    if request.query.target.height > registry.edge.body.cut.height then
      return .error "retained continuity exceeds original cut"
    discard <| liftResult (← validate config current registry)
    let extension ← liftResult (ReceiptContinuity.parseExtension (← oldContinuity registry payload))
    discard <| liftResult (Kernel.ReceiptContinuity.verify request.query extension)
    unchanged registry
    let result := (ReceiptContinuity.extensionJson extension).compress.toUTF8.toList
    if result.length > maxResponse then return .error "retained continuity response exceeds bound"
    return .ok result
  catch _ => return .error "retained continuity unavailable"

structure LookupRequest where
  origin : Identity
  raw : List UInt8

/-- Four little-endian header-length bytes, at most 1024 JSON bytes, then the
exact original SignedCall. The transport opcode counts toward maxLookupFrame. -/
def parseLookup (payload : List UInt8) : Except String LookupRequest := do
  if payload.length + 1 > maxLookupFrame || payload.length < 5 then throw "malformed-call"
  let width := frameLength (payload.take 4)
  if width == 0 || width > 1024 || 4 + width ≥ payload.length then throw "malformed-call"
  let some text := String.fromUTF8? ((payload.drop 4).take width).toByteArray
    | throw "malformed-call"
  let header ← (Json.parse text).mapError fun _ => "malformed-call"
  if (← stringField header "algorithm") != lookupAlgorithm then throw "malformed-call"
  let origin ← parseIdentity (← field header "originIdentity")
  let raw := payload.drop (4 + width)
  if raw.length > maxRawCall then throw "malformed-call"
  return ⟨origin, raw⟩

private def refused (reason : String) : Json :=
  Json.mkObj [("type", .str "refused"), ("reason", .str reason)]
private def decimal (value : Nat) : Json := .str (toString value)

/-- Only these source-selected fields leave the old outcome inspector. Old
phase/detail/leaf/diagnostic or arbitrary JSON never crosses this boundary. -/
private def receiptMetadata (registry : Registry) (value : Json) : Except String Json := do
  let kind ← stringField value "type"
  if kind == "absent" then return Json.mkObj [("type", .str "absent")]
  if kind == "refused" then
    let reason ← stringField value "reason"
    return refused (if reason == "malformed" then "malformed-call" else "lookup-refused")
  if kind != "confirmed" then return refused "lookup-refused"
  if (← stringField value "confirmation") != "replayed" then throw "receipt-invalid"
  let transaction ← digest (← field value "transactionId")
  let event ← digest (← field value "eventId")
  let count ← natural (← field value "acceptedCount")
  let root ← digest (← field value "worldRoot")
  if count == 0 || count > registry.edge.body.cut.height then throw "receipt-invalid"
  return Json.mkObj [("type", .str "confirmed"), ("confirmation", .str "replayed"),
    ("transactionId", decimal transaction.value), ("eventId", decimal event.value),
    ("acceptedCount", decimal count), ("worldRoot", decimal root.value)]

private def lookupOutcome (config : NativeHost.Config) (current : NativeHost.Durable)
    (registry : Registry) (request : LookupRequest) (input directory : System.FilePath) : IO Json := do
  if request.origin != registry.edge.body.source then return refused "origin-mismatch"
  if let .error _ ← validate config current registry then return refused "capsule-unavailable"
  try
    let output := directory / "outcome.bin"
    if !(← readonlyCli registry #["lookup", input.toString, output.toString]) then
      return refused "lookup-refused"
    -- Bound the opaque old outcome before asking its own inspector to parse it.
    discard <| readBounded output maxResponse
    let inspected := directory / "outcome.json"
    if !(← readonlyCli registry #["inspect", "outcome", output.toString, inspected.toString]) then
      return refused "receipt-invalid"
    let value ← readJsonBounded inspected
    let result := (receiptMetadata registry value).toOption.getD (refused "receipt-invalid")
    unchanged registry
    return result
  catch _ => return refused "capsule-unavailable"

/-- Exact-ingress read-only lookup does not reauthorize at the current grant
state and never falls back to submit. Original receipt roots remain historical. -/
def serveLookup (config : NativeHost.Config) (current : NativeHost.Durable)
    (registry : Registry) (payload : List UInt8) : IO (Except String (List UInt8)) := do
  try
    let request ← liftResult (parseLookup payload)
    IO.FS.withTempDir fun directory => do
      let input := directory / "call.bin"
      IO.FS.writeBinFile input request.raw.toByteArray
      let callDigest ← liftResult (← RetainedArtifactIO.fileSha256 input)
      let outcome ← lookupOutcome config current registry request input directory
      let response := Json.mkObj [("algorithm", .str lookupAlgorithm),
        ("originIdentity", CarryInspection.identityJson request.origin),
        ("callDigest", .str callDigest), ("outcome", outcome)]
      let bytes := response.compress.toUTF8.toList
      if bytes.length > maxResponse then return .error "receipt-invalid"
      return .ok bytes
  catch _ => return .error "malformed-call"

end Minidregg.Host.RetainedSegmentInspection
