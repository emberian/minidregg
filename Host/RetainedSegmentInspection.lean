/- Operator-local dispatch for one retained, audited carry edge. Requests never
select paths, executables, a historical semantic implementation, or a trust key.
The immutable capsule must remain in operator custody throughout dispatch.
This initial registry supports one old segment, not arbitrary carry chains. -/
import Compiler.CarriedSegmentIO
import Host.CarryInspection
import Compiler.DurableHistoryStore
import Compiler.ReceiptContinuityIO
import Kernel.NativeHistorySelection

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
    (registry : Registry) : IO (Except String (CarriedSegmentIO.PreservedPrefix config current)) := do
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
    -- The current Store's history is read through its authenticated `Reader`
    -- (the audited retained source is another Store, with its own image).
    let ⟨_, reader⟩ ← liftResult (← DurableHistoryStore.readerOf config.transport
      ResourceBirthCodec.rootBytes current)
    if DurableReceiverCodec.seedStream.encode source.durable.image.seed !=
        DurableReceiverCodec.seedStream.encode reader.seed then
      return .error "retained registry original seed differs"
    -- The first `cut.height` current records equal the source's, window by
    -- window; the source must be exhausted exactly at the cut.
    let compared ← NativeHistorySelection.foldRange reader 1 body.cut.height
      (source.durable.image.accepted)
      fun remaining window =>
        if window.length ≤ remaining.length &&
            window.map DurableReceiverCodec.intentStream.encode ==
              (remaining.take window.length).map DurableReceiverCodec.intentStream.encode then
          .ok (remaining.drop window.length)
        else .error "retained registry original prefix differs"
    match compared with
    | .error detail => return .error detail
    | .ok leftover =>
        if !leftover.isEmpty then return .error "retained registry original prefix differs"
    let record ← match ← reader.atHeight (body.cut.height + 1) with
      | .error refusal => return .error s!"retained registry carry record refused: {refusal.message}"
      | .ok read => pure read.record
    if record.transactionId != body.id || record.event.eventId != body.id ||
        record.event.canonicalBytes != body.bytes then
      return .error "retained registry carry event differs"
    let changes := record.writes.map fun write => (write.cellId, write.canonicalPostBytes)
    liftResult (checkBody registry.capsule.identity registry.trustedOperator source.durable body changes)
    let expected := DurableReceiver.IntentRecord.ofIntent (intent source.durable.snapshot body changes)
    if DurableReceiverCodec.intentStream.encode record != DurableReceiverCodec.intentStream.encode expected then
      return .error "retained registry carry intent differs"
    let selectedPoint ← match ← ReceiptContinuityIO.atHeight reader current
        registry.edge.targetStart.height with
      | .error detail => return .error detail
      | .ok witness => pure (⟨witness.point.height, witness.point.worldRoot, witness.chain⟩ : Point)
    if selectedPoint != registry.edge.targetStart then
      return .error "retained registry new start differs"
    let prepared ← liftResult (CarriedSegmentIO.prepareDerived config source
      registry.trustedOperator body changes)
    let authorized ← liftResult (← CarriedSegmentIO.authorizePrepared config prepared
      registry.trustedOperator registry.edge.signature)
    if authorized.edge != registry.edge then return .error "retained exact authorization differs"
    return CarriedSegmentIO.bindPreservedPrefix config authorized current
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

/-- The retained process exposes only this closed read-only opcode set. -/
private inductive ReadonlyOperation where
  | continuity
  | receiptByTransaction
  | dispatchLookup

private def ReadonlyOperation.opcode : ReadonlyOperation → UInt8
  | .continuity => 151
  | .receiptByTransaction => 102
  | .dispatchLookup => 35

private def readonlyFrame (registry : Registry) (operation : ReadonlyOperation)
    (payload : List UInt8) : IO (List UInt8) :=
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
      input.write (lengthBytes (payload.length + 1) ++ (operation.opcode :: payload).toByteArray)
      input.flush
      let size := frameLength (← readExact child.stdout 4).toList
      if size < 1 || size > maxResponse + 1 then throw (IO.userError "retained readonly response bound")
      let bytes := (← readExact child.stdout size).toList
      if bytes.head? != some operation.opcode then throw (IO.userError "retained readonly refused")
      return bytes.drop 1
    finally
      child.kill
      discard child.wait

private def oldContinuity (registry : Registry) (payload : List UInt8) : IO Json := do
  let bytes ← readonlyFrame registry .continuity payload
  let some text := String.fromUTF8? bytes.toByteArray
    | throw (IO.userError "retained continuity is not UTF-8")
  liftResult (Json.parse text)

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
  if kind == "unavailable" || kind == "uncertain" then return refused "capsule-unavailable"
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


/-- Preflight for ordinary lookup AND submit on a carried service. Only an
explicit absent/malformed old-profile result permits trying the target path.
Confirmed receipts are original metadata, never fresh target admission. -/
def serveOriginalCall (config : NativeHost.Config) (current : NativeHost.Durable)
    (registry : Registry) (rawSignedCall : List UInt8) :
    IO (Except String NativeHostCodec.Outcome) := do
  try
    if rawSignedCall.isEmpty || rawSignedCall.length > maxRawCall then
      return .ok (.refused .malformed "retained-lookup".toUTF8.toList
        "malformed original call".toUTF8.toList)
    IO.FS.withTempDir fun directory => do
      let input := directory / "original-call.bin"
      IO.FS.writeBinFile input rawSignedCall.toByteArray
      let metadata ← lookupOutcome config current registry
        ⟨registry.edge.body.source, rawSignedCall⟩ input directory
      let kind ← liftResult (stringField metadata "type")
      if kind == "absent" then return .ok .absent
      if kind == "refused" then
        let reason ← liftResult (stringField metadata "reason")
        if reason == "malformed-call" then
          return .ok (.refused .malformed "retained-lookup".toUTF8.toList
            "old profile cannot decode this call".toUTF8.toList)
        if reason == "capsule-unavailable" then
          return .ok (.unavailable "retained original capsule unavailable".toUTF8.toList)
        return .ok (.refused .conflict "retained-lookup".toUTF8.toList
          "old profile reports an original transaction conflict".toUTF8.toList)
      if kind != "confirmed" then return .error "retained original outcome unsupported"
      let transaction ← liftResult (digest (← liftResult (field metadata "transactionId")))
      let event ← liftResult (digest (← liftResult (field metadata "eventId")))
      let count ← liftResult (natural (← liftResult (field metadata "acceptedCount")))
      let root ← liftResult (digest (← liftResult (field metadata "worldRoot")))
      return .ok (.confirmed .replayed ⟨transaction, event, count, root⟩)
  catch _ => return .error "retained original call lookup unavailable"

/-- Original transaction receipt metadata comes from the retained executable,
never from recomputing an old prefix using today's profile. The accepted index
and transaction/event identity must agree with the audited retained image. -/
def serveReceiptByTransaction (config : NativeHost.Config) (current : NativeHost.Durable)
    (registry : Registry) (transactionId : Nat) : IO (Except String Json) := do
  try
    if transactionId ≥ 2^256 then return .error "retained receipt transaction exceeds digest bound"
    let custody ← liftResult (← validate config current registry)
    let bytes ← readonlyFrame registry .receiptByTransaction (toString transactionId).toUTF8.toList
    let some text := String.fromUTF8? bytes.toByteArray
      | return .error "retained receipt response is not UTF-8"
    let response ← liftResult (Json.parse text)
    let selected := custody.source.durable.image.accepted.findIdx?
      (fun record => record.transactionId.value == transactionId)
    let result ← match selected with
    | none => do
      if (← liftResult (stringField response "type")) != "absent" ||
          (← liftResult (natural (← liftResult (field response "transactionId")))) != transactionId then
        throw (IO.userError "retained receipt absence differs from audited source")
      pure (Json.mkObj [("type", .str "absent"), ("transactionId", decimal transactionId)])
    | some index => do
      let some record := custody.source.durable.image.accepted[index]?
        | throw (IO.userError "retained receipt record unavailable")
      if (← liftResult (stringField response "type")) != "confirmed" then
        throw (IO.userError "retained receipt lookup lost audited original")
      let receipt ← liftResult (field response "receipt")
      let transaction ← liftResult (digest (← liftResult (field receipt "transactionId")))
      let event ← liftResult (digest (← liftResult (field receipt "eventId")))
      let count ← liftResult (natural (← liftResult (field receipt "acceptedCount")))
      let root ← liftResult (digest (← liftResult (field receipt "worldRoot")))
      if transaction.value != transactionId || event != record.event.eventId ||
          count != index + 1 || count > registry.edge.body.cut.height then
        throw (IO.userError "retained receipt metadata differs from audited original")
      pure (Json.mkObj [("type", .str "confirmed"), ("receipt", Json.mkObj [
        ("transactionId", decimal transaction.value), ("eventId", decimal event.value),
        ("acceptedCount", decimal count), ("worldRoot", decimal root.value)])])
    unchanged registry
    return .ok result
  catch _ => return .error "retained transaction receipt unavailable"

/-- Exact old special-dispatch recovery is receipt-only. Neither this route nor
the old process can issue a physical delivery permit or submit an absent call. -/
def serveDispatchLookup (config : NativeHost.Config) (current : NativeHost.Durable)
    (registry : Registry) (payload : List UInt8) : IO (Except String NativeHostCodec.Receipt) := do
  try
    if payload.isEmpty || payload.length > maxRawCall then
      return .error "retained dispatch request exceeds bound"
    let custody ← liftResult (← validate config current registry)
    let some index := custody.source.durable.image.accepted.findIdx? (fun record =>
        record.event.codecVersion == 11 && record.event.canonicalBytes == payload)
      | return .error "exact dispatch is absent from retained original segment"
    let some record := custody.source.durable.image.accepted[index]?
      | return .error "retained dispatch original unavailable"
    IO.FS.withTempDir fun directory => do
      let outcome := directory / "dispatch-outcome.bin"
      IO.FS.writeBinFile outcome (← readonlyFrame registry .dispatchLookup payload).toByteArray
      let inspected := directory / "dispatch-outcome.json"
      if !(← readonlyCli registry #["inspect", "outcome", outcome.toString, inspected.toString]) then
        return .error "retained dispatch receipt inspection refused"
      let value ← liftResult (receiptMetadata registry (← readJsonBounded inspected))
      if (← liftResult (stringField value "type")) != "confirmed" then
        return .error "retained dispatch lookup lost audited original"
      let count ← liftResult (natural (← liftResult (field value "acceptedCount")))
      let transaction ← liftResult (digest (← liftResult (field value "transactionId")))
      let event ← liftResult (digest (← liftResult (field value "eventId")))
      let root ← liftResult (digest (← liftResult (field value "worldRoot")))
      if count != index + 1 || transaction != record.transactionId || event != record.event.eventId then
        return .error "retained dispatch receipt differs from audited original"
      unchanged registry
      return .ok ⟨transaction, event, count, root⟩
  catch _ => return .error "retained dispatch receipt unavailable"

end Minidregg.Host.RetainedSegmentInspection
