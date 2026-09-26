/-
Compiled Mini host. The operator selects one config at startup. Binary calls
and replies use Lean's strict source-owned codecs; this process never handles
private signing keys. `assemble` combines detached custody signatures only.

stdio framing: four-byte little-endian length, then one operation byte and
payload. 0=describe, 1=authorized prepare, 2=submit, 3=lookup, 4=challenge,
5=authorized query. Reply operation byte matches; failures use 255 plus a
strict Outcome. Max frame is 1 MiB. EOF at a
frame boundary ends normally; truncated/oversized/unknown frames terminate.
-/
import Kernel.NativeHost
import Kernel.NativeHostSession
import Kernel.NativeHostGenesis
import Kernel.FnEvidence
import Kernel.FnConsumerOperation
import Kernel.FnReplyPublication
import Kernel.FnReplyConsumption
import Kernel.FnPortableSource
import Host.Json
import Lean.Data.Json

open Lean
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel

namespace Minidregg.Host

structure GatewayPinSettings where
  application : String
  subject : Nat
  target : Nat
  capability : Nat
  policyAddress : Nat
  deriving FromJson, ToJson

def GatewayPinSettings.pin (source : GatewayPinSettings) : NativeHost.FnGatewayPin :=
  ⟨source.application.toUTF8.toList, ⟨source.subject⟩, source.target,
    ⟨source.capability⟩, ⟨source.policyAddress⟩⟩

/-- Paths are operator configuration, never fields in a client frame. The
service copies the four bounded manifests into its private lifetime directory
before accepting frames; the fn control endpoint remains an OS custody seam. -/
structure FnPollServiceSettings where
  originConfigPath : String
  fnPinPath : String
  scopePath : String
  policyPath : String
  controlPath : String
  deriving FromJson, ToJson

structure FnPollService where
  originConfigPath : String
  fnPinPath : String
  scopePath : String
  policyPath : String
  controlPath : String

structure Settings where
  domain : Nat
  federation : Nat
  factoryId : Nat
  resourceBookId : Nat
  authorityCatalogueId : Nat
  issuer : Nat
  ownerBudget : Nat
  lifetime : Nat
  tariffBase : Nat
  tariffPerBirth : Nat
  tariffPerGrant : Nat
  tariffPerInitialPayloadByte : Nat
  collector : Nat
  asset : Nat
  genesisHeight : Nat
  expectedSeed : Nat
  storageBinary : String
  storageRoot : String
  signatureBinary : String
  fnGateway : Option GatewayPinSettings := none
  fnPoll : Option FnPollServiceSettings := none
  deriving FromJson, ToJson

def Settings.config (settings : Settings) : NativeHost.Config where
  deployment := ⟨⟨settings.domain⟩, settings.factoryId, settings.resourceBookId, settings.authorityCatalogueId⟩
  federation := ⟨settings.federation⟩
  template := ⟨⟨settings.issuer⟩, settings.ownerBudget, settings.lifetime⟩
  tariff := ⟨settings.tariffBase, settings.tariffPerBirth, settings.tariffPerGrant,
    settings.tariffPerInitialPayloadByte, settings.collector, settings.asset⟩
  genesisHeight := settings.genesisHeight
  expectedSeed := ⟨settings.expectedSeed⟩
  storage := ⟨settings.storageBinary, settings.storageRoot⟩
  signature := ⟨settings.signatureBinary⟩
  fnGateway := settings.fnGateway.map GatewayPinSettings.pin

def loadSettings (path : System.FilePath) : IO Settings := do
  let text ← IO.FS.readFile path
  let json ← IO.ofExcept (Minidregg.Host.Json.parse text)
  let settings : Settings ← IO.ofExcept (fromJson? json)
  pure settings

/-- Immutable operator-selected protocol metadata. Available before bootstrap;
this reads neither storage nor protected resource values. Full-width integers
are decimal strings so clients cannot silently round a digest. -/
def profileDescription (config : NativeHost.Config) : Lean.Json :=
  let n := fun value : Nat => toJson (toString value)
  Lean.Json.mkObj
    [("runtime", toJson "minidregg-native"),
     ("semantics", n config.profile.semantics.value),
     ("domain", n config.deployment.domain.value),
     ("federation", n config.federation.value),
     ("factoryId", n config.deployment.factoryId),
     ("resourceBookId", n config.deployment.resourceBookId),
     ("authorityCatalogueId", n config.deployment.authorityCatalogueId),
     ("fieldModulus", n Minidregg.Compiler.babyBearP),
     ("orderDifferenceWidth", n NativeHostProfile.orderWidth),
     ("genesisHeight", n config.genesisHeight),
     ("template", Lean.Json.mkObj [("issuer", n config.template.issuer.value),
       ("ownerBudget", n config.template.ownerBudget), ("lifetime", n config.template.lifetime)]),
     ("tariff", Lean.Json.mkObj [("base", n config.tariff.base),
       ("perBirth", n config.tariff.perBirth), ("perGrant", n config.tariff.perGrant),
       ("perInitialPayloadByte", n config.tariff.perInitialPayloadByte),
       ("collector", n config.tariff.collector), ("asset", n config.tariff.asset)]),
     ("runtimeParameters", toJson (Minidregg.Host.Json.encodeHex config.runtimeParameters)),
     ("nativeChecked", toJson true), ("succinctProofDeployment", toJson false)]

def descriptionLoaded (config : NativeHost.Config) : Lean.Json := Id.run do
  let n := fun value : Nat => toJson (toString value)
  return Lean.Json.mkObj
    [("runtime", toJson "minidregg-native"),
     ("semantics", n config.profile.semantics.value),
     ("domain", n config.deployment.domain.value),
     ("fieldModulus", n Minidregg.Compiler.babyBearP),
     ("orderDifferenceWidth", n NativeHostProfile.orderWidth),
     ("nativeChecked", toJson true), ("succinctProofDeployment", toJson false),
     ("operations", toJson (["birth", "invoke", "install", "delegate", "revoke"] : List String)),
     ("jointInvocation", toJson true), ("typedContent", toJson true),
     ("authorizedQueries", toJson true), ("delegation", toJson true)]

def description (config : NativeHost.Config) : IO Lean.Json := do
  discard <| IO.ofExcept (← NativeHost.openExisting config)
  return descriptionLoaded config

def failure (phase detail : String) : List UInt8 :=
  outcomeCodec.encode (.refused phase.toUTF8.toList detail.toUTF8.toList)

def dispatch (config : NativeHost.Config) (operation : UInt8) (payload : List UInt8) :
    IO (UInt8 × List UInt8) := do
  match operation with
  | 0 =>
      unless payload.isEmpty do throw (IO.userError "describe does not accept a payload")
      pure (0, (← description config).compress.toUTF8.toList)
  | 1 =>
      match ← NativeHost.prepare config payload with
      | .ok plan => pure (1, signingPlanCodec.encode plan)
      | .error detail => pure (255, failure "prepare" detail)
  | 2 => pure (2, outcomeCodec.encode (← NativeHost.submit config payload))
  | 3 => pure (3, outcomeCodec.encode (← NativeHost.lookup config payload))
  | 4 =>
      match ← NativeHost.challenge config payload with
      | .ok challenge => pure (4, NativeObservationCodec.challengeCodec.encode challenge)
      | .error detail => pure (255, failure "observation" detail)
  | 5 =>
      match ← NativeHost.query config payload with
      | .ok view => pure (5, view)
      | .error detail => pure (255, failure "observation" detail)
  | _ => throw (IO.userError "unsupported native host operation")

/-- Session state is poisoned on any physical read, decode, prefix, or replay
failure. A new process must revalidate the entire history before serving again. -/
def sessionOpened (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config))) :
    IO (NativeHost.Opened config) := do
  let some prior ← state.get
    | throw (IO.userError "native host session invalidated")
  match ← NativeHostSession.refresh config prior with
  | .error detail =>
      state.set none
      throw (IO.userError detail)
  | .ok current =>
      state.set (some current)
      return current.opened

def sessionConfirmed (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (kind : DurableReceiverIO.Confirmation)
    (transactionId eventId : Minidregg.Theory.TypedAuthorization.Digest) :
    IO NativeHostCodec.Outcome := do
  try
    let opened ← sessionOpened config state
    match NativeHost.historicalReceipt config opened.durable transactionId eventId with
    | none => return .uncertain "original receipt prefix unavailable".toUTF8.toList
    | some receipt => return .confirmed kind receipt
  catch error => return .uncertain s!"receipt readback: {error}".toUTF8.toList

def splitKind (payload : List UInt8) : IO (String × List UInt8) := do
  unless payload.length ≥ 2 do throw (IO.userError "short native host kind frame")
  let width := payload[0]!.toNat + 256 * payload[1]!.toNat
  unless width > 0 && width ≤ payload.length - 2 do
    throw (IO.userError "invalid native host kind length")
  let some kind := String.fromUTF8? (payload.drop 2 |>.take width).toByteArray
    | throw (IO.userError "native host kind is not UTF-8")
  return (kind, payload.drop (2 + width))

def splitPair (payload : List UInt8) : IO (List UInt8 × List UInt8) := do
  unless payload.length ≥ 4 do throw (IO.userError "short native host pair frame")
  let width := payload[0]!.toNat + 256 * payload[1]!.toNat +
    65536 * payload[2]!.toNat + 16777216 * payload[3]!.toNat
  unless width ≤ payload.length - 4 do throw (IO.userError "invalid native host pair length")
  return ((payload.drop 4).take width, payload.drop (4 + width))

def decodeSignatures (bytes : List UInt8) : IO (List (List UInt8)) := do
  let signaturesCodec := ResourceBirthCodec.strictCodec (StreamCodec.list bytesStream).toLawful
  let some signatures := signaturesCodec.decode bytes
    | throw (IO.userError "noncanonical signature list")
  return signatures

/-- The live protocol keeps exact source-owned authoring and inspection in
memory, while every state-dependent operation refreshes the verified tip. -/
def dispatchSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (fnDispatch : UInt8 → List UInt8 → IO (UInt8 × List UInt8))
    (operation : UInt8) (payload : List UInt8) : IO (UInt8 × List UInt8) := do
  match operation with
  | 0 =>
      unless payload.isEmpty do throw (IO.userError "describe does not accept a payload")
      discard <| sessionOpened config state
      return (0, (descriptionLoaded config).compress.toUTF8.toList)
  | 1 =>
      let opened ← sessionOpened config state
      match ← NativeHost.prepareAuthorizedLoaded config opened payload with
      | .ok plan => return (1, signingPlanCodec.encode plan)
      | .error detail => return (255, failure "prepare" detail)
  | 2 =>
      let opened ← sessionOpened config state
      let result ← match callCodec.decode payload with
        | none => pure (NativeHostCodec.Outcome.refused "wire".toUTF8.toList
            "noncanonical or unsupported native host call".toUTF8.toList)
        | some call => NativeHost.submitLoadedWith config opened call (sessionConfirmed config state)
      return (2, outcomeCodec.encode (NativeHost.publicSubmissionOutcome result))
  | 3 =>
      let opened ← sessionOpened config state
      let result := match callCodec.decode payload with
        | none => NativeHostCodec.Outcome.refused "wire".toUTF8.toList "noncanonical native host call".toUTF8.toList
        | some call => NativeHost.lookupLoaded config opened call
      return (3, outcomeCodec.encode result)
  | 4 =>
      let opened ← sessionOpened config state
      match NativeHost.challengeLoaded config opened payload with
      | .ok challenge => return (4, NativeObservationCodec.challengeCodec.encode challenge)
      | .error detail => return (255, failure "observation" detail)
  | 5 =>
      let opened ← sessionOpened config state
      match ← NativeHost.queryLoaded config opened payload with
      | .ok view => return (5, view)
      | .error detail => return (255, failure "observation" detail)
  | 6 =>
      unless payload.isEmpty do throw (IO.userError "profile does not accept a payload")
      return (6, (profileDescription config).compress.toUTF8.toList)
  | 7 =>
      let (kind, source) ← splitKind payload
      let some text := String.fromUTF8? source.toByteArray
        | throw (IO.userError "native host author source is not UTF-8")
      let value ← IO.ofExcept (Minidregg.Host.Json.parse text)
      return (7, ← IO.ofExcept (Minidregg.Host.Json.author kind value))
  | 8 =>
      let (kind, source) ← splitKind payload
      let value ← IO.ofExcept (Minidregg.Host.Json.inspect kind source)
      return (8, value.compress.toUTF8.toList)
  | 9 =>
      let some text := String.fromUTF8? payload.toByteArray
        | throw (IO.userError "native host signatures source is not UTF-8")
      let value ← IO.ofExcept (Minidregg.Host.Json.parse text)
      return (9, ← IO.ofExcept (Minidregg.Host.Json.signatures value))
  | 10 =>
      let (challengeBytes, signaturesBytes) ← splitPair payload
      let some challenge := NativeObservationCodec.challengeCodec.decode challengeBytes
        | throw (IO.userError "noncanonical observation challenge")
      let signatures ← decodeSignatures signaturesBytes
      let signed ← IO.ofExcept (NativeObservationCodec.assemble challenge signatures)
      return (10, NativeObservationCodec.signedCodec.encode signed)
  | 11 =>
      let (planBytes, signaturesBytes) ← splitPair payload
      let some plan := signingPlanCodec.decode planBytes
        | throw (IO.userError "noncanonical signing plan")
      let signatures ← decodeSignatures signaturesBytes
      let call ← IO.ofExcept (NativeHost.assemble plan signatures)
      return (11, callCodec.encode call)
  | _ => fnDispatch operation payload

def maxFrame : Nat := 1048576

partial def readExactly (input : IO.FS.Stream) (count : Nat) (acc : ByteArray := ByteArray.empty) :
    IO ByteArray := do
  if acc.size == count then return acc
  let chunk ← input.read (count - acc.size).toUSize
  if chunk.isEmpty then throw (IO.userError "truncated native host frame")
  readExactly input count (acc ++ chunk)

def frameLength (bytes : ByteArray) : Nat :=
  bytes.toList.foldr (fun byte rest => byte.toNat + 256 * rest) 0

def lengthBytes (length : Nat) : ByteArray :=
  [UInt8.ofNat length, UInt8.ofNat (length / 256),
    UInt8.ofNat (length / 65536), UInt8.ofNat (length / 16777216)].toByteArray

partial def serve (config : NativeHost.Config) (input output : IO.FS.Stream) : IO Unit := do
  let first ← input.read 1
  if first.isEmpty then return
  let lengthWire ← readExactly input 4 first
  let length := frameLength lengthWire
  if length == 0 || length > maxFrame then throw (IO.userError "invalid native host frame length")
  let frame ← readExactly input length
  let (operation, payload) ← match frame.toList with
    | [] => throw (IO.userError "empty native host frame")
    | operation :: payload => dispatch config operation payload
  let response := (operation :: payload).toByteArray
  if response.size > maxFrame then throw (IO.userError "native host response exceeds frame budget")
  output.write (lengthBytes response.size ++ response)
  output.flush
  serve config input output

partial def serveSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (fnDispatch : UInt8 → List UInt8 → IO (UInt8 × List UInt8))
    (input output : IO.FS.Stream) : IO Unit := do
  let first ← input.read 1
  if first.isEmpty then return
  let lengthWire ← readExactly input 4 first
  let length := frameLength lengthWire
  if length == 0 || length > maxFrame then throw (IO.userError "invalid native host frame length")
  let frame ← readExactly input length
  let (operation, payload) ← match frame.toList with
    | [] => throw (IO.userError "empty native host frame")
    | operation :: payload => dispatchSession config state fnDispatch operation payload
  let response := (operation :: payload).toByteArray
  if response.size > maxFrame then throw (IO.userError "native host response exceeds frame budget")
  output.write (lengthBytes response.size ++ response)
  output.flush
  serveSession config state fnDispatch input output

/-- Execute from one private copy throughout this stdio process. The copy is
the pinned launch artifact; the originally configured pathname may later be
replaced or have a symlink target swapped without changing the session's
historical verifier. The OS must protect this private directory from writes
by other actors for the lifetime of the process. -/
def withPinnedSignature {α : Type} (config : NativeHost.Config)
    (body : NativeHost.Config → IO α) : IO α :=
  IO.FS.withTempDir fun directory => do
    let pinned := directory / "credential-verifier"
    let bytes ← IO.FS.readBinFile config.signature.binary
    IO.FS.writeBinFile pinned bytes
    let permission ← IO.Process.output
      { cmd := "/bin/chmod", args := #["0500", pinned.toString] }
    unless permission.exitCode == 0 do
      throw (IO.userError "cannot make pinned credential verifier executable")
    -- A launch failure is detected before the first semantic replay. The
    -- verifier's usage exit here is expected; it has no arguments yet.
    discard <| IO.Process.output { cmd := pinned.toString, args := #[] }
    body { config with signature := ⟨pinned⟩ }

def readBytes (path : String) : IO (List UInt8) :=
  return (← IO.FS.readBinFile path).toList

/-- Evidence files are capped while reading, before any source-owned decoder. -/
partial def readBoundedLoop (input : IO.FS.Handle) (limit : Nat)
    (acc : ByteArray := ByteArray.empty) : IO (List UInt8) := do
  if acc.size > limit then throw (IO.userError "Mini evidence input exceeds byte bound")
  let chunk ← input.read (min 4096 (limit + 1 - acc.size)).toUSize
  if chunk.isEmpty then return acc.toList
  readBoundedLoop input limit (acc ++ chunk)

def readBoundedBytes (path : String) (limit : Nat) : IO (List UInt8) := do
  let input ← IO.FS.Handle.mk path .read
  readBoundedLoop input limit

def evidenceReceiptJson (receipt : NativeHostCodec.Receipt) : Lean.Json :=
  let n := fun value : Nat => toJson (toString value)
  Lean.Json.mkObj
    [("type", toJson "verified-mini-native-prefix-v1"),
     ("transactionId", n receipt.transactionId.value),
     ("eventId", n receipt.eventId.value),
     ("acceptedCount", n receipt.acceptedCount),
     ("imageBoundary", n receipt.imageBoundary.value)]

structure ConsumerReportSource where
  application : String
  operation : String
  history : String
  incarnation : String
  sourceIdentity : String
  fnVerdictRef : String
  subject : Nat
  target : Nat
  capability : Nat
  expectedAuthorityRoot : Nat
  expectedTargetRoot : Nat
  deriving FromJson

structure ConsumerPolicySource where
  application : String
  subject : Nat
  target : Nat
  capability : Nat
  deriving FromJson

structure FnPortablePin where
  fnBinary : String
  mlPublicKey : String
  principal : String
  edPublicKey : String
  mlPublicKeyHex : String
  deriving FromJson

structure FnReplyCreationSource where
  fromMailbox : String
  newsgroup : String
  messageIdDomain : String
  date : String
  deriving FromJson

def FnReplyCreationSource.context (source : FnReplyCreationSource) :
    FnReplyPublication.CreationContext :=
  ⟨source.fromMailbox, source.newsgroup, source.messageIdDomain, source.date⟩

structure FnReplySignerPin where
  principal : String
  edPublicKey : String
  mlPublicKeyHex : String
  creation : FnReplyCreationSource
  deriving FromJson

structure FnPortableClaim where
  sourceIdentity : String
  messageId : String
  groups : String
  deriving FromJson

def requireExactFields (name : String) (expected : List String)
    (json : Lean.Json) : Except String Unit := do
  let object ← json.getObj? |>.mapError (fun e => s!"{name}: {e}")
  let actual := object.foldl (init := []) (fun fields key _ => key :: fields)
  for key in expected do
    unless actual.contains key do throw s!"{name}: missing field {key}"
  for key in actual do
    unless expected.contains key do throw s!"{name}: unknown field {key}"

structure FnPortableVerified where
  principal : List UInt8
  sourceIdentity : List UInt8
  edPublicKey : List UInt8
  mlPublicKey : List UInt8
  source : List UInt8

/-- ACL2's bounded projection of one exact schema-1 poll pair. A projection of
caller-supplied files is structural evidence only; the authenticated local
consumer poll transport separately establishes historical Store provenance. -/
structure FnPollProjection where
  history : List UInt8
  incarnation : List UInt8
  consumer : List UInt8
  principal : List UInt8
  query : List UInt8
  queryVersion : Nat
  viewVersion : Nat
  registrationEpoch : Nat
  position : Nat
  sequence : Nat
  transactionId : Nat
  sourceIdentity : List UInt8
  messageId : List UInt8
  source : List UInt8
  received : List UInt8
  verdictPrincipal : List UInt8
  verdictEvent : List UInt8

structure FnPollScopePin where
  history : String
  incarnation : String
  consumer : String
  principal : String
  query : String
  queryVersion : Nat
  viewVersion : Nat
  registrationEpoch : Nat
  deriving FromJson

def decodeCanonicalHex (label value : String) : Except String (List UInt8) := do
  let bytes ← Minidregg.Host.Json.decodeHex label (.str value)
  unless Minidregg.Host.Json.encodeHex bytes == value do
    throw s!"{label} is not canonical lowercase hexadecimal"
  pure bytes

def exactDecimal (name value : String) : Except String Nat := do
  let some parsed := value.toNat? | throw s!"{name} is not a decimal number"
  unless toString parsed == value do throw s!"{name} is not canonical decimal"
  pure parsed

def parseFnPortableLine (output : String) : Except String FnPortableVerified := do
  unless output.length ≤ 70000 do throw "fn portable verifier output exceeds bound"
  let line ← match output.splitOn "\n" with
    | [line, ""] => pure line
    | _ => throw "fn portable verifier output has unexpected framing"
  let (principalHex, idHex, edHex, mlHex, sourceHex) ← match line.splitOn " " with
    | [tag, principal, identifier, ed, ml, source] =>
        if tag == "fn-portable-v1" then pure (principal, identifier, ed, ml, source)
        else throw "fn portable verifier output has unexpected version"
    | _ => throw "fn portable verifier output has unexpected fields"
  let principal ← decodeCanonicalHex "principal" principalHex
  let sourceIdentity ← decodeCanonicalHex "source identity" idHex
  let edPublicKey ← decodeCanonicalHex "Ed25519 key" edHex
  let mlPublicKey ← decodeCanonicalHex "ML-DSA-65 key" mlHex
  let source ← decodeCanonicalHex "exact source" sourceHex
  unless principal.length == 32 && sourceIdentity.length == 48 &&
      edPublicKey.length == 32 && mlPublicKey.length == 1952 &&
      source.length ≤ 32768 do
    throw "fn portable verifier output has invalid field width"
  pure ⟨principal, sourceIdentity, edPublicKey, mlPublicKey, source⟩

def parseFnHybridSignLine (output : String) : Except String (List UInt8 × List UInt8) := do
  unless output.length ≤ 7000 do throw "fn hybrid signer output exceeds bound"
  let (edHex, mlHex) ← match output.splitOn "\n" with
    | [edLine, mlLine, ""] =>
        match edLine.splitOn " ", mlLine.splitOn " " with
        | ["ed25519", ed], ["ml-dsa-65", ml] => pure (ed, ml)
        | _, _ => throw "fn hybrid signer output has unexpected fields"
    | _ => throw "fn hybrid signer output has unexpected framing"
  let ed ← decodeCanonicalHex "fn Ed25519 signature" edHex
  let ml ← decodeCanonicalHex "fn ML-DSA-65 signature" mlHex
  unless ed.length == 64 && ml.length == 3309 do
    throw "fn hybrid signer output has invalid signature width"
  pure (ed, ml)

def parseFnPollProjectLine (output : String) : Except String FnPollProjection := do
  unless output.length ≤ 400000 do throw "fn consumer projection output exceeds bound"
  let line ← match output.splitOn "\n" with
    | [line, ""] => pure line
    | _ => throw "fn consumer projection has unexpected framing"
  let fields ← match line.splitOn " " with
    | [tag, history, incarnation, consumer, principal, query,
       qver, view, epoch, position, sequence, txid, sourceId,
       msgid, source, received, verdictPrincipal, verdict] =>
        if tag == "fn-consumer-project-v1" then
          pure (history, incarnation, consumer, principal, query,
            qver, view, epoch, position, sequence, txid, sourceId,
            msgid, source, received, verdictPrincipal, verdict)
        else throw "fn consumer projection has unexpected version"
    | _ => throw "fn consumer projection has unexpected fields"
  let (history, incarnation, consumer, principal, query,
       qver, view, epoch, position, sequence, txid, sourceId,
       msgid, source, received, verdictPrincipal, verdict) := fields
  let history ← decodeCanonicalHex "fn history" history
  let incarnation ← decodeCanonicalHex "fn incarnation" incarnation
  let consumer ← decodeCanonicalHex "fn consumer" consumer
  let principal ← decodeCanonicalHex "fn local principal" principal
  let query ← decodeCanonicalHex "fn query" query
  let sourceIdentity ← decodeCanonicalHex "fn source identity" sourceId
  let messageId ← decodeCanonicalHex "fn Message-ID" msgid
  let source ← decodeCanonicalHex "fn authored source" source
  let received ← decodeCanonicalHex "fn received article" received
  let verdictPrincipal ← decodeCanonicalHex "fn verdict principal" verdictPrincipal
  let verdictEvent ← decodeCanonicalHex "fn historical verdict" verdict
  let queryVersion ← exactDecimal "fn query version" qver
  let viewVersion ← exactDecimal "fn view version" view
  let registrationEpoch ← exactDecimal "fn registration epoch" epoch
  let position ← exactDecimal "fn Store position" position
  let sequence ← exactDecimal "fn Store sequence" sequence
  let transactionId ← exactDecimal "fn Store transaction" txid
  unless [history, incarnation, consumer, principal, query].all
      (fun value => !value.isEmpty && value.length ≤ 64) &&
      sourceIdentity.length == 48 && !messageId.isEmpty &&
      messageId.length ≤ 256 && !source.isEmpty && source.length ≤ 32768 &&
      !received.isEmpty && received.length ≤ 32768 &&
      verdictPrincipal.length == 32 &&
      !verdictEvent.isEmpty && verdictEvent.length ≤ 65538 &&
      [queryVersion, viewVersion, registrationEpoch, position,
       sequence, transactionId].all (· ≤ 4294967295) &&
      registrationEpoch > 0 && position == sequence + 1 do
    throw "fn consumer projection has invalid field width or sequence binding"
  pure ⟨history, incarnation, consumer, principal, query,
    queryVersion, viewVersion, registrationEpoch, position, sequence,
    transactionId, sourceIdentity, messageId, source, received,
    verdictPrincipal, verdictEvent⟩

def FnPollScopePin.check (pin : FnPollScopePin)
    (projection : FnPollProjection) : Except String Unit := do
  let history ← decodeCanonicalHex "pinned fn history" pin.history
  let incarnation ← decodeCanonicalHex "pinned fn incarnation" pin.incarnation
  let consumer ← decodeCanonicalHex "pinned fn consumer" pin.consumer
  let principal ← decodeCanonicalHex "pinned fn local principal" pin.principal
  let query ← decodeCanonicalHex "pinned fn query" pin.query
  unless projection.history == history &&
      projection.incarnation == incarnation &&
      projection.consumer == consumer && projection.principal == principal &&
      projection.query == query &&
      projection.queryVersion == pin.queryVersion &&
      projection.viewVersion == pin.viewVersion &&
      projection.registrationEpoch == pin.registrationEpoch do
    throw "fn poll cursor differs from independently pinned consumer scope"

def projectFnPoll (fnBinary : String) (pin : FnPollScopePin)
    (cursorPath reportPath : String) : IO (List UInt8 × List UInt8 × FnPollProjection) := do
  let cursor ← readBoundedBytes cursorPath 346
  let report ← readBoundedBytes reportPath 196608
  unless !cursor.isEmpty && !report.isEmpty do
    throw (IO.userError "fn poll has no schema-1 report and cursor")
  let child ← IO.Process.spawn
    { cmd := fnBinary, args := #["--fn", "consumer-project", cursorPath,
      reportPath], stdin := .null, stdout := .piped, stderr := .null }
  let lineBytes ← try readBoundedLoop child.stdout 400000
    catch error =>
      child.kill
      discard <| child.wait
      throw error
  let exitCode ← child.wait
  unless exitCode == 0 do
    throw (IO.userError "fn native consumer projection refused")
  unless cursor == (← readBoundedBytes cursorPath 346) &&
      report == (← readBoundedBytes reportPath 196608) do
    throw (IO.userError "fn poll files changed during native projection")
  unless lineBytes.all (fun byte => byte.toNat < 128) do
    throw (IO.userError "fn consumer projection is not ASCII")
  let projection ← IO.ofExcept (parseFnPollProjectLine
    (String.fromUTF8! lineBytes.toByteArray))
  IO.ofExcept (pin.check projection)
  pure (cursor, report, projection)

/-- Invoke the actual same-UID fn local consumer route under an operator
selected absolute control socket and independently pinned cursor scope. The
two output files must be new; no ack is sent on any result. -/
def invokeFnConsumerPoll (fnBinary : String) (scope : FnPollScopePin)
    (controlPath cursorPath reportPath carrierPath : String) :
    IO (List UInt8 × List UInt8 × List UInt8) := do
  unless [controlPath, cursorPath, reportPath, carrierPath].all
      (fun path => path.startsWith "/") do
    throw (IO.userError "fn local control and output paths must be absolute")
  unless cursorPath != reportPath && cursorPath != carrierPath &&
      reportPath != carrierPath do
    throw (IO.userError "fn poll outputs must have distinct paths")
  for path in [cursorPath, reportPath, carrierPath] do
    if ← (System.FilePath.mk path).pathExists then
      throw (IO.userError "fn poll output path already exists")
  let consumer ← IO.ofExcept (decodeCanonicalHex "pinned fn consumer" scope.consumer)
  unless !consumer.isEmpty && consumer.length ≤ 64 &&
      consumer.all (fun b => 33 ≤ b.toNat && b.toNat ≤ 126) do
    throw (IO.userError "pinned fn consumer is outside local CLI ASCII profile")
  let child ← IO.Process.spawn
    { cmd := fnBinary, args := #["--fn", "consumer", "poll", controlPath,
      String.fromUTF8! consumer.toByteArray, cursorPath, reportPath],
      stdin := .null, stdout := .piped, stderr := .null }
  let output ← try readBoundedLoop child.stdout 512
    catch error =>
      child.kill
      discard <| child.wait
      throw error
  let exitCode ← child.wait
  unless exitCode == 0 && output.all (fun b => b.toNat < 128) do
    throw (IO.userError "authenticated fn local consumer poll refused or was uncertain")
  let (cursor, event, projected) ←
    projectFnPoll fnBinary scope cursorPath reportPath
  IO.FS.writeBinFile carrierPath projected.received.toByteArray
  pure (cursor, event, projected.received)

def verifyFnCarrier (pin : FnPortablePin) (claim : FnPortableClaim)
    (carrierPath : String) : IO (List UInt8 × FnPortableVerified) := do
  let carrier ← readBoundedBytes carrierPath 32768
  unless !carrier.isEmpty do throw (IO.userError "empty fn carrier")
  let expectedPrincipal ← IO.ofExcept (decodeCanonicalHex "pinned principal" pin.principal)
  let expectedEd ← IO.ofExcept (decodeCanonicalHex "pinned Ed25519 key" pin.edPublicKey)
  let expectedMl ← IO.ofExcept (decodeCanonicalHex "pinned ML-DSA-65 key" pin.mlPublicKeyHex)
  let expectedId ← IO.ofExcept (decodeCanonicalHex "claimed source identity" claim.sourceIdentity)
  unless expectedPrincipal.length == 32 && expectedEd.length == 32 &&
      expectedMl.length == 1952 && expectedId.length == 48 do
    throw (IO.userError "fn pin or claim has invalid field width")
  let child ← IO.Process.spawn
    { cmd := pin.fnBinary, args := #["--fn", "hybrid-verify-source", carrierPath,
      pin.mlPublicKey], stdin := .null, stdout := .piped, stderr := .null }
  let lineBytes ← try readBoundedLoop child.stdout 70000
    catch error =>
      child.kill
      discard <| child.wait
      throw error
  let exitCode ← child.wait
  unless exitCode == 0 do
    throw (IO.userError "fn native portable carrier verifier refused")
  unless carrier == (← readBoundedBytes carrierPath 32768) do
    throw (IO.userError "fn carrier changed during native verification")
  unless lineBytes.all (fun byte => byte.toNat < 128) do
    throw (IO.userError "fn portable verifier output is not ASCII")
  let verified ← IO.ofExcept (parseFnPortableLine
    (String.fromUTF8! lineBytes.toByteArray))
  unless verified.principal == expectedPrincipal &&
      verified.edPublicKey == expectedEd &&
      verified.mlPublicKey == expectedMl &&
      verified.sourceIdentity == expectedId do
    throw (IO.userError "fn portable identity differs from independent pin or claim")
  pure (carrier, verified)

def verifyFnPortable (pin : FnPortablePin) (claim : FnPortableClaim)
    (carrierPath : String) : IO (List UInt8 × FnPortableVerified × FnPortableSource.Extracted) := do
  let (carrier, verified) ← verifyFnCarrier pin claim carrierPath
  let extracted ← IO.ofExcept (FnPortableSource.extract verified.source)
  unless extracted.messageId == claim.messageId && extracted.groups == claim.groups do
    throw (IO.userError "fn source metadata differs from claimed exact report")
  pure (carrier, verified, extracted)

/-- An acknowledgement is for the exact carrier and signed source retained
inside the accepted Mini operation, even after its mutation grant is revoked.
The current fn projection must match that source byte for byte. -/
def verifyAckSource (pin : FnPortablePin) (projection : FnPollProjection)
    (retainedCarrier retainedSource : List UInt8) : IO FnPortableVerified := do
  unless projection.received == retainedCarrier do
    throw (IO.userError "fn ack carrier differs from accepted Mini inbox")
  let extracted ← IO.ofExcept (FnPortableSource.extract retainedSource)
  let claim : FnPortableClaim :=
    { sourceIdentity := Minidregg.Host.Json.encodeHex projection.sourceIdentity,
      messageId := extracted.messageId,
      groups := extracted.groups }
  IO.FS.withTempDir fun directory => do
    let path := directory / "retained-carrier.eml"
    IO.FS.writeBinFile path retainedCarrier.toByteArray
    let (_, verified, _) ← verifyFnPortable pin claim path.toString
    unless verified.source == retainedSource && projection.source == retainedSource &&
        verified.sourceIdentity == projection.sourceIdentity do
      throw (IO.userError "fn ack source differs from accepted Mini inbox")
    return verified

/-- Join ACL2's exact fn-e/fncu projection to the independent native hybrid
verifier. The caller must separately establish that these files were returned
by an authenticated consumer poll; file possession alone is not Store proof. -/
def verifyFnPollFiles (pin : FnPortablePin) (scope : FnPollScopePin)
    (claim : FnPortableClaim) (cursorPath reportPath carrierPath : String) :
    IO (List UInt8 × List UInt8 × FnPollProjection × List UInt8 ×
      FnPortableVerified × FnPortableSource.Extracted) := do
  let (cursor, report, projection) ←
    projectFnPoll pin.fnBinary scope cursorPath reportPath
  let (carrier, verified, extracted) ← verifyFnPortable pin claim carrierPath
  unless projection.received == carrier &&
      projection.source == verified.source &&
      projection.sourceIdentity == verified.sourceIdentity &&
      projection.verdictPrincipal == verified.principal &&
      projection.messageId == extracted.messageId.toUTF8.toList do
    throw (IO.userError "fn Store projection differs from verified exact carrier")
  pure (cursor, report, projection, carrier, verified, extracted)

def ConsumerPolicySource.policy (source : ConsumerPolicySource) :
    FnConsumerOperation.Policy :=
  ⟨source.application.toUTF8.toList, ⟨source.subject⟩, source.target,
    ⟨source.capability⟩⟩

def ConsumerReportSource.report (source : ConsumerReportSource) (package : List UInt8) :
    FnConsumerOperation.Report :=
  ⟨source.application.toUTF8.toList, source.operation.toUTF8.toList,
    ⟨source.history.toUTF8.toList, source.incarnation.toUTF8.toList,
      source.sourceIdentity.toUTF8.toList, source.fnVerdictRef.toUTF8.toList⟩,
    package, ⟨source.subject⟩, source.target, ⟨source.capability⟩,
    ⟨source.expectedAuthorityRoot⟩, ⟨source.expectedTargetRoot⟩, none, none⟩

/-- Portable authorship has no fn Store history, incarnation or T10 verdict.
The reserved literal fields make that absence explicit in the v1 P1 binding
codec. The operation selects the pinned Mini origin and re-admitted origin
transaction, never the fn source identity. -/
def portableConsumerReport (policy : FnConsumerOperation.Policy)
    (authorityRoot targetRoot : Minidregg.Theory.TypedAuthorization.Digest)
    (verified : FnPortableVerified)
    (carrier package : List UInt8) (origin : FnEvidenceCodec.Package) :
    FnConsumerOperation.Report :=
  ⟨policy.application, FnConsumerOperation.originOperation origin,
    ⟨"fn-store-unestablished".toUTF8.toList,
      "fn-store-unestablished".toUTF8.toList,
      verified.sourceIdentity,
      "fn-portable-authorship-v1".toUTF8.toList⟩,
    package, policy.subject, policy.target, policy.capability,
    authorityRoot, targetRoot,
    some ⟨carrier, verified.sourceIdentity, verified.principal,
      verified.edPublicKey, verified.mlPublicKey⟩, none⟩

/-- Build Mini's report solely from the already joined ACL2 projection and
portable verifier. Caller-supplied scope or verdict flags never become fields
of the signed Mini command. -/
def pollConsumerReport (policy : FnConsumerOperation.Policy)
    (authorityRoot targetRoot : Minidregg.Theory.TypedAuthorization.Digest)
    (verified : FnPortableVerified) (carrier package : List UInt8)
    (origin : FnEvidenceCodec.Package) (cursor event : List UInt8)
    (projection : FnPollProjection) (controlBinding : Option (String × String)) :
    FnConsumerOperation.Report :=
  let base := portableConsumerReport policy authorityRoot targetRoot
    verified carrier package origin
  let storeInbox : FnConsumerOperation.StorePollInbox :=
    ⟨cursor, event, controlBinding.isSome, projection.sourceIdentity,
      projection.sequence, projection.transactionId, projection.messageId,
      projection.verdictPrincipal, projection.verdictEvent,
      match controlBinding with
      | none => []
      | some (fnBinary, controlPath) =>
          FnConsumerOperation.pollControlBinding fnBinary controlPath⟩
  { base with
    provenance := ⟨projection.history, projection.incarnation,
      projection.sourceIdentity,
      FnConsumerOperation.storePollVerdictRef storeInbox⟩,
    storePoll := some storeInbox }

def consumerDecisionJson (decision : FnConsumerOperation.Decision) : Lean.Json :=
  match decision with
  | .fresh _ reply => .mkObj
      [("type", "proposed-fresh"),
       ("reply", toJson (Minidregg.Host.Json.encodeHex
         (FnConsumerOperation.replyCodec.encode reply)))]
  | .repeated reply => .mkObj
      [("type", "historical-repeat"),
       ("reply", toJson (Minidregg.Host.Json.encodeHex
         (FnConsumerOperation.replyCodec.encode reply)))]
  | .carrierVariation _ reply => .mkObj
      [("type", "proposed-carrier-variation-evidence"),
       ("reply", toJson (Minidregg.Host.Json.encodeHex
         (FnConsumerOperation.replyCodec.encode reply)))]
  | .carrierVariationRecorded reply => .mkObj
      [("type", "historical-carrier-variation-evidence"),
       ("reply", toJson (Minidregg.Host.Json.encodeHex
         (FnConsumerOperation.replyCodec.encode reply)))]
  | .conflict _ => .mkObj [("type", "proposed-conflict-evidence")]
  | .conflictRecorded => .mkObj [("type", "historical-conflict-evidence")]
  | .refused detail => .mkObj [("type", "refused"), ("detail", toJson detail)]

def requireGateway (config : NativeHost.Config) : IO NativeHost.FnGatewayPin := do
  let some pin := config.fnGateway
    | throw (IO.userError "fn gateway is not pinned in operator config")
  return pin

/-- Export only from a source-owned, re-admitted accepted event. The typed
inbox keeps exact carrier octets; this asserts Mini retention, not an fn Store
receipt or current fn authorship policy. -/
def exportConsumerInbox (config : NativeHost.Config) (transactionId : Nat) :
    IO (Except String (FnConsumerOperation.PortableInbox × String × Nat)) := do
  let some gateway := config.fnGateway
    | return .error "fn gateway is not pinned in operator config"
  let opened ← match ← NativeHost.openExisting config with
    | .ok opened => pure opened
    | .error detail => return .error detail
  let some record := opened.durable.image.accepted.find?
      (fun entry => entry.transactionId.value == transactionId)
    | return .error "exact Mini consumer transaction is absent"
  match FnConsumerOperation.originalBindingWithInbox gateway config.deployment.domain
      config.profile.semantics record with
  | some (binding, some inbox, _) =>
      return .ok (inbox, "operation",
        (FnConsumerOperation.operationInboxAtom config.deployment.domain
          config.profile.semantics binding.application binding.operation).digest.value)
  | _ =>
      match FnConsumerOperation.originalConflictWithInbox gateway config.deployment.domain
          config.profile.semantics record with
      | some (conflict, some inbox, store) =>
          let report : FnConsumerOperation.Report :=
            { application := conflict.application, operation := conflict.operation,
              provenance := conflict.provenance, package := conflict.package,
              subject := ⟨0⟩, target := 0, capability := ⟨0⟩,
              expectedAuthorityRoot := ⟨0⟩, expectedTargetRoot := ⟨0⟩,
              portableInbox := some inbox, storePoll := store }
          return .ok (inbox, "conflict",
            (FnConsumerOperation.conflictInboxAtom config.deployment.domain
              config.profile.semantics report).digest.value)
      | _ => return .error "transaction has no canonical portable inbox"

/-- Read the exact fn poll pair from Mini's original signed accepted command,
after the ordinary native open has re-admitted its durable history. -/
def exportConsumerPoll (config : NativeHost.Config) (transactionId : Nat) :
    IO (Except String (FnConsumerOperation.StorePollInbox × String × Nat)) := do
  let some gateway := config.fnGateway
    | return .error "fn gateway is not pinned in operator config"
  let opened ← match ← NativeHost.openExisting config with
    | .ok opened => pure opened
    | .error detail => return .error detail
  let some record := opened.durable.image.accepted.find?
      (fun entry => entry.transactionId.value == transactionId)
    | return .error "exact Mini consumer transaction is absent"
  match FnConsumerOperation.originalBindingWithInbox gateway config.deployment.domain
      config.profile.semantics record with
  | some (binding, some _, some store) =>
      return .ok (store, "operation",
        (FnConsumerOperation.storeOperationAtom config.deployment.domain
          config.profile.semantics binding.application binding.operation).digest.value)
  | _ =>
      match FnConsumerOperation.originalConflictWithInbox gateway config.deployment.domain
          config.profile.semantics record with
      | some (conflict, some portable, some store) =>
          let report : FnConsumerOperation.Report :=
            { application := conflict.application, operation := conflict.operation,
              provenance := conflict.provenance, package := conflict.package,
              subject := ⟨0⟩, target := 0, capability := ⟨0⟩,
              expectedAuthorityRoot := ⟨0⟩, expectedTargetRoot := ⟨0⟩,
              portableInbox := some portable, storePoll := some store }
          return .ok (store, "conflict",
            (FnConsumerOperation.storeConflictAtom config.deployment.domain
              config.profile.semantics report).digest.value)
      | _ => return .error "transaction has no canonical Store poll inbox"

def writeBytes (path : String) (bytes : List UInt8) : IO Unit :=
  IO.FS.writeBinFile path bytes.toByteArray

def readJson (path : String) : IO Lean.Json :=
  return ← IO.ofExcept (Minidregg.Host.Json.parse (← IO.FS.readFile path))

def writeJson (path : String) (value : Lean.Json) : IO Unit :=
  IO.FS.writeFile path value.pretty

/-- This is the only Mini decision body for both file-only and observed
polls. Only the caller that actually invokes fn's control route can set the
local observation bit retained in the signed inbox atom. -/
def runPollConsumerDecisionLoaded (config : NativeHost.Config)
    (opened : NativeHost.Opened config)
    (controlBinding : Option (String × String))
    (originPath pinPath scopePath claimPath policyPath cursorPath reportPath
     carrierPath intentPath resultPath : String) : IO UInt32 := do
  let gateway ← requireGateway config
  let origin := (← loadSettings originPath).config
  let pinJson ← readJson pinPath
  let scopeJson ← readJson scopePath
  let claimJson ← readJson claimPath
  let policyJson ← readJson policyPath
  IO.ofExcept (requireExactFields "fn pin"
    ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
  IO.ofExcept (requireExactFields "fn poll scope"
    ["history", "incarnation", "consumer", "principal", "query",
     "queryVersion", "viewVersion", "registrationEpoch"] scopeJson)
  IO.ofExcept (requireExactFields "fn claim"
    ["sourceIdentity", "messageId", "groups"] claimJson)
  IO.ofExcept (requireExactFields "consumer policy"
    ["application", "subject", "target", "capability"] policyJson)
  let pin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
  let scope : FnPollScopePin ← IO.ofExcept (fromJson? scopeJson)
  let claim : FnPortableClaim ← IO.ofExcept (fromJson? claimJson)
  let policySource : ConsumerPolicySource ← IO.ofExcept (fromJson? policyJson)
  let (cursor, event, projection, carrier, verified, extracted) ←
    verifyFnPollFiles pin scope claim cursorPath reportPath carrierPath
  unless event.length ≤ FnConsumerOperation.maxStoreEventBytes do
    throw (IO.userError "fn report exceeds Mini's first bounded Store inbox profile")
  let receipt ← IO.ofExcept (← FnEvidence.verify origin extracted.package)
  let originPackage ← IO.ofExcept (FnEvidenceCodec.decodeChecked extracted.package)
  unless originPackage.originalReceipt == receipt do
    throw (IO.userError "poll source Mini receipt differs from re-admitted package")
  let policy := policySource.policy
  let probeTarget : DeclaredResourceController.Target :=
    ⟨.object, policy.target, policy.capability, 1, ⟨0⟩,
      .content ⟨[]⟩, none⟩
  let targetRoot ← IO.ofExcept <| (do
    let .present cell := opened.directory.directory.slots policy.target
      | throw "poll consumer target is absent"
    let some pre := DeclaredResourceController.selectTarget
      config.deployment probeTarget cell
      | throw "poll consumer target is not a valid content resource"
    pure pre.root : Except String Minidregg.Theory.TypedAuthorization.Digest)
  let report := pollConsumerReport policy opened.authority.snapshot.cell.root
    targetRoot verified carrier extracted.package originPackage
    cursor event projection controlBinding
  let decision ← IO.ofExcept (FnConsumerOperation.evaluateVerified config
    gateway policy report receipt opened)
  writeJson resultPath <| Lean.Json.mkObj
    [("type", toJson "fn-poll-consumer-decision-v1"),
     ("portableAuthorship", toJson "verified"),
     ("storeAdmission", toJson (if controlBinding.isSome then
      "observed-control-poll" else "unestablished-from-files")),
     ("sourceIdentity", toJson
       (Minidregg.Host.Json.encodeHex projection.sourceIdentity)),
     ("storeSequence", toJson (toString projection.sequence)),
     ("storeTransactionId", toJson (toString projection.transactionId)),
     ("application", toJson policySource.application),
     ("operation", toJson (String.fromUTF8! report.operation.toByteArray)),
     ("miniOrigin", evidenceReceiptJson receipt),
     ("decision", consumerDecisionJson decision)]
  match decision.intent report with
  | some intent =>
      writeBytes intentPath (NativeObservationCodec.intentCodec.encode intent)
      pure 0
  | none =>
      match decision with
      | .refused _ => pure 1
      | _ => pure 0

def runPollConsumerDecision (config : NativeHost.Config)
    (controlBinding : Option (String × String))
    (originPath pinPath scopePath claimPath policyPath cursorPath reportPath
     carrierPath intentPath resultPath : String) : IO UInt32 := do
  let opened ← IO.ofExcept (← NativeHost.openExisting config)
  runPollConsumerDecisionLoaded config opened controlBinding originPath pinPath
    scopePath claimPath policyPath cursorPath reportPath carrierPath intentPath resultPath

/-- A's observed local Q poll is admitted only after independently reopening
the original R Mini package. The fn projection supplies Store history; the
native hybrid verifier supplies exact portable authorship. -/
def runReplyConsumerPollDecisionLoaded (config : NativeHost.Config)
    (opened : NativeHost.Opened config)
    (originPath rPinPath rClaimPath rCarrierPath qPinPath scopePath qClaimPath
     policyPath controlPath cursorPath reportPath carrierPath intentPath
     resultPath : String) : IO UInt32 := do
  let gateway ← requireGateway config
  let origin := (← loadSettings originPath).config
  let rPinJson ← readJson rPinPath
  let rClaimJson ← readJson rClaimPath
  let qPinJson ← readJson qPinPath
  let scopeJson ← readJson scopePath
  let qClaimJson ← readJson qClaimPath
  let policyJson ← readJson policyPath
  for (label, value) in [("R fn pin", rPinJson), ("Q fn pin", qPinJson)] do
    IO.ofExcept (requireExactFields label
      ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] value)
  for (label, value) in [("R fn claim", rClaimJson), ("Q fn claim", qClaimJson)] do
    IO.ofExcept (requireExactFields label ["sourceIdentity", "messageId", "groups"] value)
  IO.ofExcept (requireExactFields "A fn scope"
    ["history", "incarnation", "consumer", "principal", "query",
     "queryVersion", "viewVersion", "registrationEpoch"] scopeJson)
  IO.ofExcept (requireExactFields "A reply policy"
    ["application", "subject", "target", "capability"] policyJson)
  let rPin : FnPortablePin ← IO.ofExcept (fromJson? rPinJson)
  let rClaim : FnPortableClaim ← IO.ofExcept (fromJson? rClaimJson)
  let qPin : FnPortablePin ← IO.ofExcept (fromJson? qPinJson)
  let scope : FnPollScopePin ← IO.ofExcept (fromJson? scopeJson)
  let qClaim : FnPortableClaim ← IO.ofExcept (fromJson? qClaimJson)
  let policySource : ConsumerPolicySource ← IO.ofExcept (fromJson? policyJson)
  let (_, rVerified, rExtracted) ← verifyFnPortable rPin rClaim rCarrierPath
  let originReceipt ← IO.ofExcept (← FnEvidence.verify origin rExtracted.package)
  let originPackage ← IO.ofExcept (FnEvidenceCodec.decodeChecked rExtracted.package)
  unless originPackage.originalReceipt == originReceipt do
    throw (IO.userError "R package receipt differs from Mini's re-admitted origin")
  let (cursor, event, _) ←
    invokeFnConsumerPoll qPin.fnBinary scope controlPath cursorPath reportPath carrierPath
  let (projectedCursor, projectedEvent, projection) ←
    projectFnPoll qPin.fnBinary scope cursorPath reportPath
  unless cursor == projectedCursor && event == projectedEvent do
    throw (IO.userError "A fn poll changed before Mini projection")
  let (carrier, verified) ← verifyFnCarrier qPin qClaim carrierPath
  let extracted ← IO.ofExcept (FnReplySource.extract verified.source)
  unless projection.received == carrier && projection.source == verified.source &&
      projection.sourceIdentity == verified.sourceIdentity &&
      projection.verdictPrincipal == verified.principal &&
      projection.messageId == extracted.messageId.toUTF8.toList &&
      qClaim.messageId == extracted.messageId && qClaim.groups == "fn.test" do
    throw (IO.userError "A historical verdict differs from exact native Q carrier")
  let policy := policySource.policy
  let probeTarget : DeclaredResourceController.Target :=
    ⟨.object, policy.target, policy.capability, 1, ⟨0⟩,
      .content ⟨[]⟩, none⟩
  let targetRoot ← IO.ofExcept <| (do
    let .present cell := opened.directory.directory.slots policy.target
      | throw "A reply consumer target is absent"
    let some pre := DeclaredResourceController.selectTarget
      config.deployment probeTarget cell
      | throw "A reply consumer target is not a valid content resource"
    pure pre.root : Except String Minidregg.Theory.TypedAuthorization.Digest)
  let storePoll : FnConsumerOperation.StorePollInbox :=
    ⟨cursor, event, true, projection.sourceIdentity, projection.sequence,
      projection.transactionId, projection.messageId,
      projection.verdictPrincipal, projection.verdictEvent,
      FnConsumerOperation.pollControlBinding qPin.fnBinary controlPath⟩
  let report : FnReplyConsumption.Report :=
    ⟨policy.application, FnConsumerOperation.originOperation originPackage,
      rVerified.sourceIdentity, rExtracted.messageId.toUTF8.toList,
      originReceipt, verified.source, verified.sourceIdentity,
      extracted.messageId.toUTF8.toList,
      ⟨carrier, verified.sourceIdentity, verified.principal,
        verified.edPublicKey, verified.mlPublicKey⟩, storePoll,
      policy.subject, policy.target, policy.capability,
      opened.authority.snapshot.cell.root, targetRoot⟩
  let decision ← IO.ofExcept (FnReplyConsumption.evaluateVerified config opened
    gateway ⟨policy.application, policy.subject,
      policy.target, policy.capability⟩ report)
  let verdict := match decision with
    | .fresh _ _ => "proposed-fresh"
    | .repeated _ => "repeated"
    | .conflict _ => "proposed-conflict"
    | .conflictRecorded => "conflict-recorded"
    | .refused _ => "refused"
  writeJson resultPath <| Lean.Json.mkObj
    [("type", toJson "fn-a-reply-consumer-decision-v1"),
     ("decision", toJson verdict),
     ("operation", toJson (String.fromUTF8! report.operation.toByteArray)),
     ("qSourceIdentity", toJson
       (Minidregg.Host.Json.encodeHex verified.sourceIdentity)),
     ("fnStoreSequence", toJson (toString projection.sequence)),
     ("fnStoreTransactionId", toJson (toString projection.transactionId)),
     ("miniOrigin", evidenceReceiptJson originReceipt)]
  match decision.intent report with
  | some intent =>
      writeBytes intentPath (NativeObservationCodec.intentCodec.encode intent)
      pure 0
  | none =>
      match decision with
      | .refused _ => pure 1
      | _ => pure 0

def runReplyConsumerPollDecision (config : NativeHost.Config)
    (originPath rPinPath rClaimPath rCarrierPath qPinPath scopePath qClaimPath
     policyPath controlPath cursorPath reportPath carrierPath intentPath
     resultPath : String) : IO UInt32 := do
  let opened ← IO.ofExcept (← NativeHost.openExisting config)
  runReplyConsumerPollDecisionLoaded config opened originPath rPinPath rClaimPath
    rCarrierPath qPinPath scopePath qClaimPath policyPath controlPath cursorPath
    reportPath carrierPath intentPath resultPath

def usage : String :=
  "minidregg-host CONFIG.json profile|describe|stdio|author KIND INPUT.json OUTPUT.bin|inspect KIND INPUT.bin OUTPUT.json|derive grain INPUT.json OUTPUT.json|signatures INPUT.json OUTPUT.bin|genesis SOURCE-CONFIG.bin GENESIS.bin PINNED-CONFIG.json|bootstrap GENESIS.bin|challenge INTENT.bin CHALLENGE.bin|observe-assemble CHALLENGE.bin SIGNATURES.bin SIGNED.bin PLAN.bin|prepare SIGNED.bin PLAN.bin|query SIGNED.bin VIEW.bin|assemble PLAN.bin SIGNATURES.bin CALL.bin|submit CALL.bin OUTCOME.bin|lookup CALL.bin OUTCOME.bin|export-evidence CALL.bin PACKAGE.bin|verify-evidence PACKAGE.bin RESULT.json|portable-verify-fn FN-PIN.json CLAIM.json CARRIER.eml SOURCE.bin PACKAGE.bin RESULT.json|consumer-verify-poll-files FN-PIN.json SCOPE-PIN.json CLAIM.json CURSOR.fncu REPORT.fn-e CARRIER.eml RESULT.json|portable-consumer-decide ORIGIN-PIN.json FN-PIN.json CLAIM.json POLICY.json CARRIER.eml INTENT.bin DECISION.json|poll-consumer-decide ORIGIN-PIN.json FN-PIN.json SCOPE-PIN.json CLAIM.json POLICY.json CURSOR.fncu REPORT.fn-e CARRIER.eml INTENT.bin DECISION.json|consumer-poll-decide ORIGIN-PIN.json FN-PIN.json SCOPE-PIN.json CLAIM.json POLICY.json CONTROL.sock CURSOR.fncu REPORT.fn-e CARRIER.eml INTENT.bin DECISION.json|consumer-export-inbox TRANSACTION-ID INBOX.bin CARRIER.eml RESULT.json|consumer-export-poll TRANSACTION-ID CURSOR.fncu REPORT.fn-e RESULT.json|consumer-ack-poll FN-PIN.json SCOPE-PIN.json CONTROL.sock MINI-TRANSACTION CURSOR.fncu REPORT.fn-e RESULT.json|reply-consumer-poll-decide ORIGIN-PIN.json R-FN-PIN.json R-CLAIM.json R-CARRIER.eml Q-FN-PIN.json A-SCOPE.json Q-CLAIM.json POLICY.json A-CONTROL.sock CURSOR.fncu REPORT.fn-e Q-CARRIER.eml INTENT.bin DECISION.json|reply-consumer-export-result MINI-TRANSACTION RESULT.bin INBOX.bin CURSOR.fncu REPORT.fn-e|reply-consumer-ack-poll Q-FN-PIN.json A-SCOPE.json A-CONTROL.sock MINI-TRANSACTION CURSOR.fncu REPORT.fn-e RESULT.json|consumer-export-reply TRANSACTION-ID REPLY.bin|consumer-stage-reply-plan SIGNER.json MINI-TRANSACTION OUTBOX_ROOT CANDIDATE.bin READBACK.bin SOURCE.eml RESULT.json|consumer-stage-reply-sign FN-PIN.json PRINCIPAL.bin ED-PUBLIC.bin ED-SECRET ML-SECRET MINI-TRANSACTION PLAN_ROOT SIGNED_ROOT PLAN-READBACK.bin SOURCE.eml CARRIER.eml SIGNED-CANDIDATE.bin SIGNED-READBACK.bin ED-SIG.bin ML-SIG.bin RESULT.json|consumer-decide-test ORIGIN-PIN.json POLICY.json REPORT.json PACKAGE.bin INTENT.bin DECISION.json"

def run (arguments : List String) : IO UInt32 := do
  match arguments with
  | configPath :: command :: rest =>
      let settings ← loadSettings configPath
      let config := settings.config
      match command, rest with
      | "profile", [] => IO.println (profileDescription config).pretty; pure 0
      | "author", [kind, input, output] =>
          let bytes ← IO.ofExcept (Minidregg.Host.Json.author kind (← readJson input))
          writeBytes output bytes
          pure 0
      | "inspect", [kind, input, output] =>
          let value ← IO.ofExcept (Minidregg.Host.Json.inspect kind (← readBytes input))
          writeJson output value
          pure 0
      | "derive", [kind, input, output] =>
          let value ← IO.ofExcept (Minidregg.Host.Json.derive kind (← readJson input))
          writeJson output value
          pure 0
      | "signatures", [input, output] =>
          let bytes ← IO.ofExcept (Minidregg.Host.Json.signatures (← readJson input))
          writeBytes output bytes
          pure 0
      | "genesis", [input, imageOutput, configOutput] =>
          let ⟨source, built⟩ ← IO.ofExcept <|
            (NativeHostGenesis.buildBytes config.profile (← readBytes input)).mapError (fun error => s!"{repr error}")
          unless source.deployment == config.deployment && source.federation == config.federation &&
              source.tariff == config.tariff && source.genesisHeight == config.genesisHeight do
            throw (IO.userError "genesis source and operator runtime manifest differ")
          let pinned := { settings with expectedSeed := (NativeHost.seedIdentity built.seed).value }
          let genesis := DurableReceiverCodec.encode built.image
          discard <| IO.ofExcept <| do
            let loaded ← DurableReceiverIO.loadBytes ResourceBirthCodec.rootBytes genesis
            NativeHost.validateLoaded pinned.config loaded
          writeBytes imageOutput genesis
          IO.FS.writeFile configOutput (toJson pinned).pretty
          pure 0
      | "describe", [] => IO.println (← description config).pretty; pure 0
      | "stdio", [] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            serveSession pinnedConfig state (← IO.getStdin) (← IO.getStdout)
          pure 0
      | "bootstrap", [path] =>
          IO.ofExcept (← NativeHost.bootstrap config (← readBytes path))
          pure 0
      | "prepare", [input, output] =>
          let plan ← IO.ofExcept (← NativeHost.prepare config (← readBytes input))
          writeBytes output (signingPlanCodec.encode plan)
          pure 0
      | "challenge", [input, output] =>
          let challenge ← IO.ofExcept (← NativeHost.challenge config (← readBytes input))
          writeBytes output (NativeObservationCodec.challengeCodec.encode challenge)
          pure 0
      | "observe-assemble", [challengePath, signaturesPath, output] =>
          let some challenge := NativeObservationCodec.challengeCodec.decode (← readBytes challengePath)
            | throw (IO.userError "noncanonical observation challenge")
          let signaturesCodec := ResourceBirthCodec.strictCodec (StreamCodec.list bytesStream).toLawful
          let some signatures := signaturesCodec.decode (← readBytes signaturesPath)
            | throw (IO.userError "noncanonical signature list")
          let signed ← IO.ofExcept (NativeObservationCodec.assemble challenge signatures)
          writeBytes output (NativeObservationCodec.signedCodec.encode signed)
          pure 0
      | "query", [input, output] =>
          writeBytes output (← IO.ofExcept (← NativeHost.query config (← readBytes input)))
          pure 0
      | "assemble", [planPath, signaturesPath, output] =>
          let some plan := signingPlanCodec.decode (← readBytes planPath)
            | throw (IO.userError "noncanonical signing plan")
          let signaturesCodec := ResourceBirthCodec.strictCodec (StreamCodec.list bytesStream).toLawful
          let some signatures := signaturesCodec.decode (← readBytes signaturesPath)
            | throw (IO.userError "noncanonical signature list")
          let call ← IO.ofExcept (NativeHost.assemble plan signatures)
          writeBytes output (callCodec.encode call)
          pure 0
      | "submit", [input, output] =>
          writeBytes output (outcomeCodec.encode (← NativeHost.submit config (← readBytes input)))
          pure 0
      | "lookup", [input, output] =>
          writeBytes output (outcomeCodec.encode (← NativeHost.lookup config (← readBytes input)))
          pure 0
      | "export-evidence", [input, output] =>
          let call ← readBoundedBytes input FnEvidenceCodec.maxCallBytes
          let package ← IO.ofExcept (← FnEvidence.exportPackage config call)
          writeBytes output package
          pure 0
      | "verify-evidence", [input, output] =>
          let package ← readBoundedBytes input FnEvidenceCodec.maxPackageBytes
          let receipt ← IO.ofExcept (← FnEvidence.verify config package)
          writeJson output (evidenceReceiptJson receipt)
          pure 0
      | "portable-verify-fn", [pinPath, claimPath, carrierPath, sourcePath, packagePath, resultPath] =>
          let pinJson ← readJson pinPath
          let claimJson ← readJson claimPath
          IO.ofExcept (requireExactFields "fn pin"
            ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
          IO.ofExcept (requireExactFields "fn claim"
            ["sourceIdentity", "messageId", "groups"] claimJson)
          let pin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
          let claim : FnPortableClaim ← IO.ofExcept (fromJson? claimJson)
          let (_, verified, extracted) ← verifyFnPortable pin claim carrierPath
          let receipt ← IO.ofExcept (← FnEvidence.verify config extracted.package)
          writeBytes sourcePath verified.source
          writeBytes packagePath extracted.package
          writeJson resultPath <| Lean.Json.mkObj
            [("type", toJson "verified-fn-portable-mini-e1-v1"),
             ("sourceIdentity", toJson (Minidregg.Host.Json.encodeHex verified.sourceIdentity)),
             ("principal", toJson (Minidregg.Host.Json.encodeHex verified.principal)),
             ("edPublicKey", toJson (Minidregg.Host.Json.encodeHex verified.edPublicKey)),
             ("mlPublicKey", toJson (Minidregg.Host.Json.encodeHex verified.mlPublicKey)),
             ("messageId", toJson extracted.messageId),
             ("groups", toJson extracted.groups),
             ("portableAuthorship", toJson "verified"),
             ("storeAdmission", toJson "unestablished"),
             ("miniOrigin", evidenceReceiptJson receipt)]
          pure 0
      | "consumer-verify-poll-files",
          [pinPath, scopePath, claimPath, cursorPath, reportPath,
           carrierPath, resultPath] =>
          let pinJson ← readJson pinPath
          let scopeJson ← readJson scopePath
          let claimJson ← readJson claimPath
          IO.ofExcept (requireExactFields "fn pin"
            ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
          IO.ofExcept (requireExactFields "fn poll scope"
            ["history", "incarnation", "consumer", "principal", "query",
             "queryVersion", "viewVersion", "registrationEpoch"] scopeJson)
          IO.ofExcept (requireExactFields "fn claim"
            ["sourceIdentity", "messageId", "groups"] claimJson)
          let pin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
          let scope : FnPollScopePin ← IO.ofExcept (fromJson? scopeJson)
          let claim : FnPortableClaim ← IO.ofExcept (fromJson? claimJson)
          let (cursor, report, projected, _, _, extracted) ←
            verifyFnPollFiles pin scope claim cursorPath reportPath carrierPath
          let receipt ← IO.ofExcept (← FnEvidence.verify config extracted.package)
          writeJson resultPath <| Lean.Json.mkObj
            [("type", toJson "fn-consumer-poll-files-joined-v1"),
             ("sourceIdentity", toJson
               (Minidregg.Host.Json.encodeHex projected.sourceIdentity)),
             ("storeSequence", toJson (toString projected.sequence)),
             ("storeTransactionId", toJson (toString projected.transactionId)),
             ("cursorOctets", toJson cursor.length),
             ("reportOctets", toJson report.length),
             ("portableAuthorship", toJson "verified"),
             ("storeAdmission", toJson "unestablished-from-files"),
             ("miniOrigin", evidenceReceiptJson receipt)]
          pure 0
      | "portable-consumer-decide",
          [originPath, pinPath, claimPath, policyPath,
           carrierPath, intentPath, resultPath] =>
          let origin := (← loadSettings originPath).config
          let pinJson ← readJson pinPath
          let claimJson ← readJson claimPath
          let policyJson ← readJson policyPath
          IO.ofExcept (requireExactFields "fn pin"
            ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
          IO.ofExcept (requireExactFields "fn claim"
            ["sourceIdentity", "messageId", "groups"] claimJson)
          IO.ofExcept (requireExactFields "consumer policy"
            ["application", "subject", "target", "capability"] policyJson)
          let pin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
          let claim : FnPortableClaim ← IO.ofExcept (fromJson? claimJson)
          let policySource : ConsumerPolicySource ← IO.ofExcept (fromJson? policyJson)
          let started : Nat ← IO.monoNanosNow
          let (carrier, verified, extracted) ← verifyFnPortable pin claim carrierPath
          let afterFn : Nat ← IO.monoNanosNow
          let receipt ← IO.ofExcept (← FnEvidence.verify origin extracted.package)
          let originPackage ← IO.ofExcept (FnEvidenceCodec.decodeChecked extracted.package)
          unless originPackage.originalReceipt == receipt do
            throw (IO.userError "portable origin receipt differs from re-admitted package")
          let afterOrigin : Nat ← IO.monoNanosNow
          let policy := policySource.policy
          let opened ← IO.ofExcept (← NativeHost.openExisting config)
          let afterConsumer : Nat ← IO.monoNanosNow
          let probeTarget : DeclaredResourceController.Target :=
            ⟨.object, policy.target, policy.capability, 1, ⟨0⟩,
              .content ⟨[]⟩, none⟩
          let targetRoot ← IO.ofExcept <| (do
            let .present cell := opened.directory.directory.slots policy.target
              | throw "portable consumer target is absent"
            let some pre := DeclaredResourceController.selectTarget
              config.deployment probeTarget cell
              | throw "portable consumer target is not a valid content resource"
            pure pre.root : Except String Minidregg.Theory.TypedAuthorization.Digest)
          let report := portableConsumerReport policy
            opened.authority.snapshot.cell.root
            targetRoot verified carrier
            extracted.package originPackage
          let gateway ← requireGateway config
          let decision ← IO.ofExcept (FnConsumerOperation.evaluateVerified config
            gateway policy report receipt opened)
          let afterDecision : Nat ← IO.monoNanosNow
          let intent := decision.intent report
          let intentBytes := intent.map NativeObservationCodec.intentCodec.encode
          let afterEncoding : Nat ← IO.monoNanosNow
          writeJson resultPath <| Lean.Json.mkObj
            [("type", toJson "fn-portable-consumer-decision-v1"),
             ("portableAuthorship", toJson "verified"),
             ("storeAdmission", toJson "unestablished"),
             ("sourceIdentity", toJson (Minidregg.Host.Json.encodeHex verified.sourceIdentity)),
             ("application", toJson policySource.application),
             ("operation", toJson (String.fromUTF8! report.operation.toByteArray)),
             ("miniOrigin", evidenceReceiptJson receipt),
             ("timingNs", Lean.Json.mkObj
               [("fnPortableAndExtraction", toJson (toString (afterFn - started))),
                ("miniOriginReplay", toJson (toString (afterOrigin - afterFn))),
                ("miniConsumerReplay", toJson (toString (afterConsumer - afterOrigin))),
                ("grantAndDecision", toJson (toString (afterDecision - afterConsumer))),
                ("intentEncoding", toJson (toString (afterEncoding - afterDecision)))]),
             ("decision", consumerDecisionJson decision)]
          match intentBytes with
          | some bytes =>
              writeBytes intentPath bytes
              pure 0
          | none =>
              match decision with
              | .refused _ => pure 1
              | _ => pure 0
      | "poll-consumer-decide",
          [originPath, pinPath, scopePath, claimPath, policyPath,
           cursorPath, reportPath, carrierPath, intentPath, resultPath] =>
          runPollConsumerDecision config none originPath pinPath scopePath
            claimPath policyPath cursorPath reportPath carrierPath intentPath resultPath
      | "consumer-poll-decide",
          [originPath, pinPath, scopePath, claimPath, policyPath,
           controlPath, cursorPath, reportPath, carrierPath,
           intentPath, resultPath] =>
          let pinJson ← readJson pinPath
          let scopeJson ← readJson scopePath
          IO.ofExcept (requireExactFields "fn pin"
            ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
          IO.ofExcept (requireExactFields "fn poll scope"
            ["history", "incarnation", "consumer", "principal", "query",
             "queryVersion", "viewVersion", "registrationEpoch"] scopeJson)
          let pin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
          let scope : FnPollScopePin ← IO.ofExcept (fromJson? scopeJson)
          let (polledCursor, polledEvent, polledCarrier) ←
            invokeFnConsumerPoll pin.fnBinary scope controlPath
              cursorPath reportPath carrierPath
          let exitCode ← runPollConsumerDecision config
            (some (pin.fnBinary, controlPath)) originPath pinPath
            scopePath claimPath policyPath cursorPath reportPath carrierPath
            intentPath resultPath
          unless polledCursor == (← readBoundedBytes cursorPath 346) &&
              polledEvent == (← readBoundedBytes reportPath 196608) &&
              polledCarrier == (← readBoundedBytes carrierPath 32768) do
            throw (IO.userError "fn poll output changed before Mini decision completed")
          pure exitCode
      | "reply-consumer-poll-decide",
          [originPath, rPinPath, rClaimPath, rCarrierPath,
           qPinPath, scopePath, qClaimPath, policyPath, controlPath,
           cursorPath, reportPath, carrierPath, intentPath, resultPath] =>
          runReplyConsumerPollDecision config originPath rPinPath rClaimPath
            rCarrierPath qPinPath scopePath qClaimPath policyPath controlPath
            cursorPath reportPath carrierPath intentPath resultPath
      | "reply-consumer-export-result",
          [transaction, resultPath, inboxPath, cursorPath, reportPath] =>
          let gateway ← requireGateway config
          let transactionId ← IO.ofExcept (exactDecimal "Mini transaction ID" transaction)
          let opened ← IO.ofExcept (← NativeHost.openExisting config)
          let some record := opened.durable.image.accepted.find?
              (fun entry => entry.transactionId.value == transactionId)
            | throw (IO.userError "A reply result transaction is absent")
          let some (result, inbox) :=
              FnReplyConsumption.originalResult gateway config.deployment.domain
                config.profile.semantics record
            | throw (IO.userError "A reply result is not a canonical accepted operation")
          unless inbox.storePoll.pollCallObserved do
            throw (IO.userError "A reply result lacks an observed fn poll")
          writeBytes resultPath (FnReplyConsumption.resultCodec.encode result)
          writeBytes inboxPath (FnReplyConsumption.reportCodec.encode inbox)
          writeBytes cursorPath inbox.storePoll.cursor
          writeBytes reportPath inbox.storePoll.event
          pure 0
      | "reply-consumer-ack-poll",
          [pinPath, scopePath, controlPath, transaction,
           cursorPath, eventPath, resultPath] =>
          let gateway ← requireGateway config
          let transactionId ← IO.ofExcept (exactDecimal "Mini transaction ID" transaction)
          unless controlPath.startsWith "/" && cursorPath.startsWith "/" &&
              eventPath.startsWith "/" do
            throw (IO.userError "A reply ack paths must be absolute")
          let pinJson ← readJson pinPath
          let scopeJson ← readJson scopePath
          IO.ofExcept (requireExactFields "Q fn pin"
            ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
          IO.ofExcept (requireExactFields "A fn scope"
            ["history", "incarnation", "consumer", "principal", "query",
             "queryVersion", "viewVersion", "registrationEpoch"] scopeJson)
          let pin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
          let scope : FnPollScopePin ← IO.ofExcept (fromJson? scopeJson)
          let opened ← IO.ofExcept (← NativeHost.openExisting config)
          let some record := opened.durable.image.accepted.find?
              (fun entry => entry.transactionId.value == transactionId)
            | throw (IO.userError "A reply result transaction is absent")
          let some (_, inbox) := FnReplyConsumption.originalResult gateway
              config.deployment.domain config.profile.semantics record
            | throw (IO.userError "A reply result is not a reopened accepted operation")
          let stored := inbox.storePoll
          unless stored.pollCallObserved && stored.controlBinding ==
              FnConsumerOperation.pollControlBinding pin.fnBinary controlPath do
            throw (IO.userError "A reply ack control differs from durable observed poll")
          let (cursor, event, projected) ←
            projectFnPoll pin.fnBinary scope cursorPath eventPath
          unless cursor == stored.cursor && event == stored.event &&
              projected.sourceIdentity == stored.sourceIdentity &&
              projected.sequence == stored.sequence &&
              projected.transactionId == stored.transactionId &&
              projected.messageId == stored.messageId &&
              projected.verdictPrincipal == stored.verdictPrincipal &&
              projected.verdictEvent == stored.verdictEvent do
            throw (IO.userError "A reply ack pair differs from durable Mini inbox")
          let verified ← verifyAckSource pin projected inbox.portableInbox.carrier inbox.replySource
          unless projected.verdictPrincipal == inbox.portableInbox.principal &&
              verified.principal == inbox.portableInbox.principal &&
              verified.edPublicKey == inbox.portableInbox.edPublicKey &&
              verified.mlPublicKey == inbox.portableInbox.mlPublicKey do
            throw (IO.userError "A reply ack principal differs from accepted Mini inbox")
          let child ← IO.Process.spawn
            { cmd := pin.fnBinary,
              args := #["--fn", "consumer", "ack", controlPath, cursorPath],
              stdin := .null, stdout := .piped, stderr := .null }
          let output ← try readBoundedLoop child.stdout 128
            catch error =>
              child.kill
              discard <| child.wait
              throw error
          let exitCode ← child.wait
          unless cursor == (← readBoundedBytes cursorPath 346) &&
              event == (← readBoundedBytes eventPath 196608) do
            throw (IO.userError "A reply ack inputs changed during local call")
          let status := if exitCode == 0 && output == "consumer accepted\n".toUTF8.toList then
              "durable-accepted"
            else if exitCode == 2 then "refused"
            else if exitCode == 3 then "uncertain"
            else "transport-fault"
          writeJson resultPath <| Lean.Json.mkObj
            [("type", toJson "fn-a-reply-ack-after-mini-v1"),
             ("miniTransactionId", toJson transaction),
             ("miniResult", toJson "reopened-accepted"),
             ("fnStoreSequence", toJson (toString stored.sequence)),
             ("fnStoreTransactionId", toJson (toString stored.transactionId)),
             ("fnAck", toJson status)]
          if status == "durable-accepted" then pure 0
          else if status == "refused" then pure 2
          else if status == "uncertain" then pure 3
          else pure 4
      | "consumer-export-inbox", [transaction, inboxPath, carrierPath, resultPath] =>
          let transactionId ← IO.ofExcept (exactDecimal "transaction ID" transaction)
          let (inbox, kind, atomId) ← IO.ofExcept
            (← exportConsumerInbox config transactionId)
          writeBytes inboxPath (FnConsumerOperation.portableInboxCodec.encode inbox)
          writeBytes carrierPath inbox.carrier
          writeJson resultPath <| Lean.Json.mkObj
            [("type", toJson "retained-mini-portable-inbox-v1"),
             ("miniTransactionId", toJson transaction),
             ("kind", toJson kind),
             ("atomId", toJson (toString atomId)),
             ("sourceIdentity", toJson (Minidregg.Host.Json.encodeHex inbox.sourceIdentity)),
             ("storeAdmission", toJson "unestablished")]
          pure 0
      | "consumer-export-poll", [transaction, cursorPath, eventPath, resultPath] =>
          let transactionId ← IO.ofExcept (exactDecimal "transaction ID" transaction)
          let (poll, kind, atomId) ← IO.ofExcept
            (← exportConsumerPoll config transactionId)
          writeBytes cursorPath poll.cursor
          writeBytes eventPath poll.event
          writeJson resultPath <| Lean.Json.mkObj
            [("type", toJson "retained-mini-fn-poll-inbox-v1"),
             ("miniTransactionId", toJson transaction),
             ("kind", toJson kind),
             ("atomId", toJson (toString atomId)),
             ("sourceIdentity", toJson
               (Minidregg.Host.Json.encodeHex poll.sourceIdentity)),
             ("fnStoreSequence", toJson (toString poll.sequence)),
             ("fnStoreTransactionId", toJson (toString poll.transactionId)),
             ("pollCallObserved", toJson poll.pollCallObserved),
             ("controlBinding", toJson
               (Minidregg.Host.Json.encodeHex poll.controlBinding)),
             ("fnStoreAttribution", toJson "unestablished-from-files")]
          pure 0
      | "consumer-ack-poll",
          [pinPath, scopePath, controlPath, transaction,
           cursorPath, eventPath, resultPath] =>
          let transactionId ← IO.ofExcept (exactDecimal "Mini transaction ID" transaction)
          unless controlPath.startsWith "/" && cursorPath.startsWith "/" &&
              eventPath.startsWith "/" do
            throw (IO.userError "fn control and poll paths must be absolute")
          let pinJson ← readJson pinPath
          let scopeJson ← readJson scopePath
          IO.ofExcept (requireExactFields "fn pin"
            ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
          IO.ofExcept (requireExactFields "fn poll scope"
            ["history", "incarnation", "consumer", "principal", "query",
             "queryVersion", "viewVersion", "registrationEpoch"] scopeJson)
          let pin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
          let scope : FnPollScopePin ← IO.ofExcept (fromJson? scopeJson)
          let (stored, kind, _) ← IO.ofExcept (← exportConsumerPoll config transactionId)
          unless kind == "operation" && stored.pollCallObserved do
            throw (IO.userError "Mini has no durable operation from observed fn poll")
          unless stored.controlBinding ==
              FnConsumerOperation.pollControlBinding pin.fnBinary controlPath do
            throw (IO.userError "fn ack control endpoint differs from observed poll")
          let (cursor, event, projected) ←
            projectFnPoll pin.fnBinary scope cursorPath eventPath
          unless cursor == stored.cursor && event == stored.event &&
              projected.sourceIdentity == stored.sourceIdentity &&
              projected.sequence == stored.sequence &&
              projected.transactionId == stored.transactionId &&
              projected.messageId == stored.messageId &&
              projected.verdictPrincipal == stored.verdictPrincipal &&
              projected.verdictEvent == stored.verdictEvent do
            throw (IO.userError "fn ack cursor/report differ from durable Mini inbox")
          let (portable, portableKind, _) ← IO.ofExcept
            (← exportConsumerInbox config transactionId)
          unless portableKind == "operation" do
            throw (IO.userError "fn ack has no accepted portable operation inbox")
          let extracted ← IO.ofExcept (FnPortableSource.extract projected.source)
          let verified ← verifyAckSource pin projected portable.carrier projected.source
          unless extracted.messageId.toUTF8.toList == stored.messageId &&
              projected.verdictPrincipal == portable.principal &&
              portable.sourceIdentity == stored.sourceIdentity &&
              verified.principal == portable.principal &&
              verified.edPublicKey == portable.edPublicKey &&
              verified.mlPublicKey == portable.mlPublicKey do
            throw (IO.userError "fn ack source metadata differs from accepted Mini inbox")
          let child ← IO.Process.spawn
            { cmd := pin.fnBinary,
              args := #["--fn", "consumer", "ack", controlPath, cursorPath],
              stdin := .null, stdout := .piped, stderr := .null }
          let output ← try readBoundedLoop child.stdout 128
            catch error =>
              child.kill
              discard <| child.wait
              throw error
          let exitCode ← child.wait
          unless cursor == (← readBoundedBytes cursorPath 346) &&
              event == (← readBoundedBytes eventPath 196608) do
            throw (IO.userError "fn ack inputs changed during local control call")
          let status := if exitCode == 0 && output == "consumer accepted\n".toUTF8.toList then
              "durable-accepted"
            else if exitCode == 2 then "refused"
            else if exitCode == 3 then "uncertain"
            else "transport-fault"
          writeJson resultPath <| Lean.Json.mkObj
            [("type", toJson "fn-consumer-ack-after-mini-v1"),
             ("miniTransactionId", toJson transaction),
             ("miniOperation", toJson "reopened-accepted"),
             ("fnStoreSequence", toJson (toString stored.sequence)),
             ("fnStoreTransactionId", toJson (toString stored.transactionId)),
             ("fnAck", toJson status)]
          if status == "durable-accepted" then pure 0
          else if status == "refused" then pure 2
          else if status == "uncertain" then pure 3
          else pure 4
      | "consumer-export-reply", [transaction, replyPath] =>
          let gateway ← requireGateway config
          let transactionId ← IO.ofExcept (exactDecimal "transaction ID" transaction)
          let opened ← IO.ofExcept (← NativeHost.openExisting config)
          let some record := opened.durable.image.accepted.find?
              (fun entry => entry.transactionId.value == transactionId)
            | throw (IO.userError "exact Mini consumer transaction is absent")
          let some (binding, some _, _) :=
              FnConsumerOperation.originalBindingWithInbox gateway config.deployment.domain
                config.profile.semantics record
            | throw (IO.userError "transaction has no canonical portable Q")
          writeBytes replyPath (FnConsumerOperation.replyCodec.encode binding.reply)
          pure 0
      | "consumer-stage-reply-plan",
          [signerPath, transaction, outboxRoot, candidatePath,
           readbackPath, sourcePath, resultPath] =>
          let gateway ← requireGateway config
          unless [outboxRoot, candidatePath, readbackPath, sourcePath,
              resultPath].all (·.startsWith "/") &&
              ([(candidatePath, readbackPath), (candidatePath, sourcePath),
                (readbackPath, sourcePath)].all (fun pair => pair.1 != pair.2)) do
            throw (IO.userError "reply plan paths must be absolute and distinct")
          for path in [candidatePath, readbackPath, sourcePath, resultPath] do
            if ← (System.FilePath.mk path).pathExists then
              throw (IO.userError "reply plan output path already exists")
          let transactionId ← IO.ofExcept (exactDecimal "Mini transaction ID" transaction)
          let signerJson ← readJson signerPath
          IO.ofExcept (requireExactFields "fn reply signer"
            ["principal", "edPublicKey", "mlPublicKeyHex", "creation"] signerJson)
          let creationJson ← IO.ofExcept (signerJson.getObjVal? "creation")
          IO.ofExcept (requireExactFields "fn reply creation"
            ["fromMailbox", "newsgroup", "messageIdDomain", "date"] creationJson)
          let signer : FnReplySignerPin ← IO.ofExcept (fromJson? signerJson)
          unless signer.creation.context.valid do
            throw (IO.userError "fn reply creation context is invalid")
          let principal ← IO.ofExcept (decodeCanonicalHex "fn reply principal" signer.principal)
          let edPublicKey ← IO.ofExcept (decodeCanonicalHex "fn reply Ed25519 key" signer.edPublicKey)
          let mlPublicKey ← IO.ofExcept (decodeCanonicalHex "fn reply ML-DSA-65 key" signer.mlPublicKeyHex)
          let opened ← IO.ofExcept (← NativeHost.openExisting config)
          let some record := opened.durable.image.accepted.find?
              (fun entry => entry.transactionId.value == transactionId)
            | throw (IO.userError "exact Mini consumer transaction is absent")
          let some (binding, some _, some store) :=
              FnConsumerOperation.originalBindingWithInbox gateway config.deployment.domain
                config.profile.semantics record
            | throw (IO.userError "transaction has no canonical observed fn poll and Q")
          unless store.pollCallObserved do
            throw (IO.userError "reply plan requires durable observed fn poll")
          let selection : FnReplyPublication.Selection :=
            { domain := config.deployment.domain,
              semantics := config.profile.semantics,
              miniTransaction := record.transactionId,
              miniEvent := record.event.eventId,
              reply := binding.reply,
              parentSourceIdentity := store.sourceIdentity,
              parentMessageId := store.messageId,
              principal := principal, edPublicKey := edPublicKey,
              mlPublicKey := mlPublicKey,
              creation := signer.creation.context }
          let prepared ← IO.ofExcept selection.prepare
          writeBytes candidatePath (FnReplyPublication.preparedCodec.encode prepared)
          let publish ← IO.Process.spawn
            { cmd := settings.storageBinary,
              args := #["publish", outboxRoot, candidatePath],
              stdin := .null, stdout := .piped, stderr := .null }
          let _ ← readBoundedLoop publish.stdout 128
          let _ ← publish.wait
          let readback ← IO.Process.spawn
            { cmd := settings.storageBinary,
              args := #["read-to", outboxRoot, readbackPath],
              stdin := .null, stdout := .piped, stderr := .null }
          let _ ← readBoundedLoop readback.stdout 128
          let readbackExit ← readback.wait
          if readbackExit != 0 then
            writeJson resultPath <| Lean.Json.mkObj
              [("type", toJson "fn-reply-plan-stage-v1"),
               ("stage", toJson "uncertain")]
            pure 3
          else
            let bytes? ← try pure (some (← readBoundedBytes readbackPath 8192))
              catch _ => pure none
            let some bytes := bytes?
              | do
                  writeJson resultPath <| Lean.Json.mkObj
                    [("type", toJson "fn-reply-plan-stage-v1"),
                     ("stage", toJson "uncertain")]
                  return 3
            let some retained := FnReplyPublication.preparedCodec.decode bytes
              | do
                  writeJson resultPath <| Lean.Json.mkObj
                    [("type", toJson "fn-reply-plan-stage-v1"),
                     ("stage", toJson "uncertain")]
                  return 3
            unless retained.valid do
              writeJson resultPath <| Lean.Json.mkObj
                [("type", toJson "fn-reply-plan-stage-v1"),
                 ("stage", toJson "uncertain")]
              return 3
            let accepted := retained == prepared
            if accepted then writeBytes sourcePath retained.source
            writeJson resultPath <| Lean.Json.mkObj
              [("type", toJson "fn-reply-plan-stage-v1"),
               ("stage", toJson (if accepted then "durable-accepted" else "conflict")),
               ("miniTransactionId", toJson transaction),
               ("messageId", toJson retained.selection.messageId)]
            pure (if accepted then 0 else 2)
      | "consumer-stage-reply-sign",
          [fnPinPath, principalPath, edPublicPath, edSecretPath,
           mlSecretPath, transaction, preparedRoot, signedRoot,
           planPath, sourcePath, carrierPath, signedCandidatePath,
           signedReadbackPath, edSignaturePath, mlSignaturePath, resultPath] =>
          let gateway ← requireGateway config
          unless [principalPath, edPublicPath, edSecretPath, mlSecretPath,
              preparedRoot, signedRoot, planPath, sourcePath, carrierPath,
              signedCandidatePath, signedReadbackPath, edSignaturePath,
              mlSignaturePath, resultPath].all (·.startsWith "/") do
            throw (IO.userError "reply signer paths must be absolute")
          for path in [planPath, sourcePath, carrierPath, signedCandidatePath,
              signedReadbackPath, edSignaturePath, mlSignaturePath, resultPath] do
            if ← (System.FilePath.mk path).pathExists then
              throw (IO.userError "reply signer output path already exists")
          let transactionId ← IO.ofExcept (exactDecimal "Mini transaction ID" transaction)
          let pinJson ← readJson fnPinPath
          IO.ofExcept (requireExactFields "fn reply signing pin"
            ["fnBinary", "mlPublicKey", "principal", "edPublicKey",
             "mlPublicKeyHex"] pinJson)
          let pin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
          unless pin.fnBinary.startsWith "/" && pin.mlPublicKey.startsWith "/" do
            throw (IO.userError "fn reply signer and public key paths must be absolute")
          let principal ← IO.ofExcept (decodeCanonicalHex "fn reply principal" pin.principal)
          let edPublicKey ← IO.ofExcept (decodeCanonicalHex "fn reply Ed25519 key" pin.edPublicKey)
          let mlPublicKey ← IO.ofExcept (decodeCanonicalHex "fn reply ML-DSA-65 key" pin.mlPublicKeyHex)
          unless principal == (← readBoundedBytes principalPath 32) &&
              edPublicKey == (← readBoundedBytes edPublicPath 32) do
            throw (IO.userError "fn reply signer public files differ from pin")
          let opened ← IO.ofExcept (← NativeHost.openExisting config)
          let some record := opened.durable.image.accepted.find?
              (fun entry => entry.transactionId.value == transactionId)
            | throw (IO.userError "exact Mini consumer transaction is absent")
          let some (binding, some _, some store) :=
              FnConsumerOperation.originalBindingWithInbox gateway config.deployment.domain
                config.profile.semantics record
            | throw (IO.userError "transaction has no canonical observed fn poll and Q")
          unless store.pollCallObserved do
            throw (IO.userError "reply signing requires durable observed fn poll")
          let planRead ← IO.Process.spawn
            { cmd := settings.storageBinary,
              args := #["read-to", preparedRoot, planPath],
              stdin := .null, stdout := .piped, stderr := .null }
          let _ ← readBoundedLoop planRead.stdout 128
          let planExit ← planRead.wait
          if planExit != 0 then
            writeJson resultPath <| Lean.Json.mkObj
              [("type", toJson "fn-reply-sign-stage-v1"),
               ("stage", toJson (if planExit == 3 then "unprepared" else "uncertain"))]
            pure (if planExit == 3 then 2 else 3)
          else
            let preparedBytes? ← try pure (some (← readBoundedBytes planPath 8192))
              catch _ => pure none
            let some preparedBytes := preparedBytes?
              | do
                  writeJson resultPath <| Lean.Json.mkObj
                    [("type", toJson "fn-reply-sign-stage-v1"),
                     ("stage", toJson "uncertain")]
                  return 3
            let some prepared := FnReplyPublication.preparedCodec.decode preparedBytes
              | do
                  writeJson resultPath <| Lean.Json.mkObj
                    [("type", toJson "fn-reply-sign-stage-v1"),
                     ("stage", toJson "uncertain")]
                  return 3
            let selection : FnReplyPublication.Selection :=
              { domain := config.deployment.domain,
                semantics := config.profile.semantics,
                miniTransaction := record.transactionId,
                miniEvent := record.event.eventId,
                reply := binding.reply,
                parentSourceIdentity := store.sourceIdentity,
                parentMessageId := store.messageId,
                principal := principal, edPublicKey := edPublicKey,
                mlPublicKey := mlPublicKey,
                creation := prepared.selection.creation }
            let expected ← IO.ofExcept selection.prepare
            unless prepared.valid && prepared == expected do
              writeJson resultPath <| Lean.Json.mkObj
                [("type", toJson "fn-reply-sign-stage-v1"),
                 ("stage", toJson "conflict")]
              return 2
            let prior ← IO.Process.spawn
              { cmd := settings.storageBinary,
                args := #["read-to", signedRoot, signedReadbackPath],
                stdin := .null, stdout := .piped, stderr := .null }
            let _ ← readBoundedLoop prior.stdout 128
            let priorExit ← prior.wait
            if priorExit != 0 && priorExit != 3 then
              writeJson resultPath <| Lean.Json.mkObj
                [("type", toJson "fn-reply-sign-stage-v1"),
                 ("stage", toJson "uncertain")]
              return 3
            if priorExit == 3 then
              writeBytes sourcePath prepared.source
              let carrier ← IO.Process.spawn
                { cmd := pin.fnBinary,
                  args := #["--fn", "hybrid-sign-carrier", principalPath,
                    edPublicPath, edSecretPath, pin.mlPublicKey, mlSecretPath,
                    sourcePath, carrierPath],
                  stdin := .null, stdout := .piped, stderr := .null }
              let _ ← readBoundedLoop carrier.stdout 128
              let carrierExit ← carrier.wait
              if carrierExit != 0 then
                let stage := if carrierExit == 1 then "refused"
                  else if carrierExit == 3 then "uncertain" else "transport-fault"
                writeJson resultPath <| Lean.Json.mkObj
                  [("type", toJson "fn-reply-sign-stage-v1"),
                   ("stage", toJson stage)]
                return if carrierExit == 1 then 2 else if carrierExit == 3 then 3 else 4
              let verified ← IO.Process.spawn
                { cmd := pin.fnBinary,
                  args := #["--fn", "hybrid-verify-source", carrierPath,
                    pin.mlPublicKey],
                  stdin := .null, stdout := .piped, stderr := .null }
              let verifiedOutput ← readBoundedLoop verified.stdout 70000
              let verifiedExit ← verified.wait
              if verifiedExit != 0 then
                let stage := if verifiedExit == 1 then "refused"
                  else if verifiedExit == 3 then "uncertain" else "transport-fault"
                writeJson resultPath <| Lean.Json.mkObj
                  [("type", toJson "fn-reply-sign-stage-v1"),
                   ("stage", toJson stage)]
                return if verifiedExit == 1 then 2 else if verifiedExit == 3 then 3 else 4
              let verifiedSource ← IO.ofExcept (parseFnPortableLine
                (String.fromUTF8! verifiedOutput.toByteArray))
              unless verifiedSource.source == prepared.source &&
                  verifiedSource.principal == principal &&
                  verifiedSource.edPublicKey == edPublicKey &&
                  verifiedSource.mlPublicKey == mlPublicKey do
                throw (IO.userError "fn reply signed carrier differs from prepared key/source")
              let signer ← IO.Process.spawn
                { cmd := pin.fnBinary,
                  args := #["--fn", "hybrid-sign", principalPath,
                    edPublicPath, edSecretPath, pin.mlPublicKey, mlSecretPath,
                    sourcePath],
                  stdin := .null, stdout := .piped, stderr := .null }
              let signatureOutput ← readBoundedLoop signer.stdout 7000
              let signerExit ← signer.wait
              if signerExit != 0 then
                let stage := if signerExit == 1 then "refused"
                  else if signerExit == 3 then "uncertain" else "transport-fault"
                writeJson resultPath <| Lean.Json.mkObj
                  [("type", toJson "fn-reply-sign-stage-v1"),
                   ("stage", toJson stage)]
                return if signerExit == 1 then 2 else if signerExit == 3 then 3 else 4
              let (edSignature, mlSignature) ← IO.ofExcept (parseFnHybridSignLine
                (String.fromUTF8! signatureOutput.toByteArray))
              let candidate : FnReplyPublication.Signed :=
                ⟨prepared, verifiedSource.sourceIdentity, edSignature, mlSignature⟩
              unless candidate.valid do
                throw (IO.userError "fn reply signed artifact exceeds bound")
              writeBytes signedCandidatePath (FnReplyPublication.signedCodec.encode candidate)
              let publisher ← IO.Process.spawn
                { cmd := settings.storageBinary,
                  args := #["publish", signedRoot, signedCandidatePath],
                  stdin := .null, stdout := .piped, stderr := .null }
              let _ ← readBoundedLoop publisher.stdout 128
              let _ ← publisher.wait
              let reopened ← IO.Process.spawn
                { cmd := settings.storageBinary,
                  args := #["read-to", signedRoot, signedReadbackPath],
                  stdin := .null, stdout := .piped, stderr := .null }
              let _ ← readBoundedLoop reopened.stdout 128
              let reopenedExit ← reopened.wait
              unless reopenedExit == 0 do
                writeJson resultPath <| Lean.Json.mkObj
                  [("type", toJson "fn-reply-sign-stage-v1"),
                   ("stage", toJson "uncertain")]
                return 3
            let signedBytes? ← try pure (some (← readBoundedBytes signedReadbackPath 12288))
              catch _ => pure none
            let some signedBytes := signedBytes?
              | do
                  writeJson resultPath <| Lean.Json.mkObj
                    [("type", toJson "fn-reply-sign-stage-v1"),
                     ("stage", toJson "uncertain")]
                  return 3
            let some retained := FnReplyPublication.signedCodec.decode signedBytes
              | do
                  writeJson resultPath <| Lean.Json.mkObj
                    [("type", toJson "fn-reply-sign-stage-v1"),
                     ("stage", toJson "uncertain")]
                  return 3
            unless retained.valid do
              writeJson resultPath <| Lean.Json.mkObj
                [("type", toJson "fn-reply-sign-stage-v1"),
                 ("stage", toJson "uncertain")]
              return 3
            unless retained.prepared == prepared do
              writeJson resultPath <| Lean.Json.mkObj
                [("type", toJson "fn-reply-sign-stage-v1"),
                 ("stage", toJson "conflict")]
              return 2
            if priorExit == 0 then writeBytes sourcePath retained.prepared.source
            writeBytes edSignaturePath retained.edSignature
            writeBytes mlSignaturePath retained.mlSignature
            writeJson resultPath <| Lean.Json.mkObj
              [("type", toJson "fn-reply-sign-stage-v1"),
               ("stage", toJson "durable-accepted"),
               ("miniTransactionId", toJson transaction),
               ("messageId", toJson retained.prepared.selection.messageId),
               ("sourceIdentity", toJson
                 (Minidregg.Host.Json.encodeHex retained.sourceIdentity))]
            pure 0
      | "consumer-decide-test", [originPath, policyPath, reportPath, packagePath, intentPath, resultPath] =>
          let gateway ← requireGateway config
          let origin := (← loadSettings originPath).config
          let policySource : ConsumerPolicySource ← IO.ofExcept (fromJson? (← readJson policyPath))
          let source : ConsumerReportSource ← IO.ofExcept (fromJson? (← readJson reportPath))
          let report := source.report
            (← readBoundedBytes packagePath FnEvidenceCodec.maxPackageBytes)
          let decision ← IO.ofExcept (← FnConsumerOperation.evaluate origin config
            gateway policySource.policy report)
          writeJson resultPath (consumerDecisionJson decision)
          match decision.intent report with
          | some intent =>
              writeBytes intentPath (NativeObservationCodec.intentCodec.encode intent)
              pure 0
          | none =>
              match decision with
              | .refused _ => pure 1
              | _ => pure 0
      | _, _ => throw (IO.userError usage)
  | _ => throw (IO.userError usage)

end Minidregg.Host

def main (arguments : List String) : IO UInt32 := do
  try Minidregg.Host.run arguments
  catch error =>
    (← IO.getStderr).putStrLn s!"minidregg-host: {error}"
    pure 1
