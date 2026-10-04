/- Narrow ordinary native reader for the actual source-agreement operator.
Every stateful request reopens the same native source. No mutation opcode
is served here; op2 belongs to the four-participant agreement bridge.
JSON grammar is an explicit projection of existing Host.Json. -/
import Kernel.NativeHost
import Kernel.NativeHostGenesis
import Compiler.GenericSimplexSourceAnchor
import Compiler.FnEvidenceCodec
import Host.SourceAgreementBirth
import Host.SourceAgreementJson
import Host.RequestRefusal
import Lean.Data.Json

open Lean Minidregg.Compiler Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend Minidregg.Kernel
namespace Minidregg.Host.SourceAgreementReader

structure JointConsensusSettings where
  context : Minidregg.Compiler.GenericSimplexCodec.Context

instance : FromJson JointConsensusSettings where
  fromJson? json := do
    let value ← json.getStr?
    let bytes ← Minidregg.Host.SourceAgreementJson.decodeHex "jointConsensus" json
    unless Minidregg.Host.SourceAgreementJson.encodeHex bytes == value do
      throw "jointConsensus must use canonical lowercase hex"
    let some context := Minidregg.Compiler.GenericSimplexCodec.contextStream.toLawful.decode bytes
      | throw "jointConsensus is not a canonical Context"
    unless Minidregg.Compiler.GenericSimplexCodec.contextStream.encode context == bytes &&
        context.wellFormed do
      throw "jointConsensus Context is noncanonical or committee is not well formed"
    pure ⟨context⟩

instance : ToJson JointConsensusSettings where
  toJson pin := .str (Minidregg.Host.SourceAgreementJson.encodeHex
    (Minidregg.Compiler.GenericSimplexCodec.contextStream.encode pin.context))

structure Settings where
  domain : Nat
  federation : Nat
  factoryId : Nat
  resourceBookId : Nat
  authorityCellId : Nat
  issuer : Nat
  ownerBudget : Nat
  lifetime : Nat
  birthSlack : Option Nat := none
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
  checkpointKey : Option String := none
  checkpointEvery : Option Nat := none
  jointConsensus : Option JointConsensusSettings := none
  nockFSync : Option Nat := none
  disabledEvaluators : Option (List String) := none
  deriving FromJson, ToJson

def Settings.disabledEvaluatorIds (settings : Settings) :
    List Minidregg.Theory.TypedAuthorization.Digest :=
  (settings.disabledEvaluators.getD []).map fun name =>
    (Minidregg.Compiler.Evaluator.resolveName name).getD (Minidregg.Compiler.Evaluator.idOf name "")

def Settings.checkDisabledEvaluators (settings : Settings) : Except String Unit :=
  (settings.disabledEvaluators.getD []).forM fun name =>
    if (Minidregg.Compiler.Evaluator.resolveName name).isSome then .ok ()
    else .error s!"disabledEvaluators: no compiled-in evaluator named {name}"

def Settings.config (settings : Settings) : NativeHost.Config where
  deployment := ⟨⟨settings.domain⟩, settings.factoryId, settings.resourceBookId, settings.authorityCellId⟩
  federation := ⟨settings.federation⟩
  disabledEvaluators := settings.disabledEvaluatorIds
  template := ⟨⟨settings.issuer⟩, settings.ownerBudget, settings.lifetime,
    settings.birthSlack.getD CanonicalRuntimeProfile.defaultBirthSlack⟩
  tariff := ⟨settings.tariffBase, settings.tariffPerBirth, settings.tariffPerGrant,
    settings.tariffPerInitialPayloadByte, settings.collector, settings.asset⟩
  genesisHeight := settings.genesisHeight
  expectedSeed := ⟨settings.expectedSeed⟩
  storage :=
    { binary := settings.storageBinary
      root := settings.storageRoot
      key := settings.checkpointKey.getD ""
      checkpointEvery := settings.checkpointEvery.getD 64 }
  signature := ⟨settings.signatureBinary⟩
  nockFSync := settings.nockFSync.getD NativeHost.defaultNockFSync
  jointConsensus := settings.jointConsensus.map JointConsensusSettings.context

def Settings.checkJointConsensus (settings : Settings) : Except String Unit := do
  let some pin := settings.jointConsensus | return ()
  let config := settings.config
  unless pin.context.scope ==
      Minidregg.Compiler.Tower256ConcreteBackend.digestStream.encode config.deployment.domain do
    throw "jointConsensus scope differs from native deployment"
  let anchorTag := "MINI-SIMPLEX-SOURCE-GENESIS/v1".toUTF8.toList
  let some (height,seed) := Minidregg.Compiler.GenericSimplexSourceAnchor.anchorStream.toLawful.decode
      (pin.context.instanceBytes.drop anchorTag.length)
    | throw "jointConsensus requires an exact canonical source genesis anchor"
  unless height == config.genesisHeight &&
      Minidregg.Compiler.GenericSimplexSourceAnchor.anchorBytes height seed == pin.context.instanceBytes do
    throw "jointConsensus source anchor height or encoding mismatch"
  unless NativeHost.seedIdentity seed == config.expectedSeed do
    throw "jointConsensus source anchor differs from expectedSeed"
  let genesis ← Minidregg.Compiler.DurableReceiverIO.loadSeed
    Minidregg.Compiler.ResourceBirthCodec.rootBytes (config.logStart seed) seed
  let _ ← NativeHost.validateLoaded config genesis
  pure ()


def loadSettings (path : System.FilePath) : IO Settings := do
  let json ← IO.ofExcept (SourceAgreementJson.parse (← IO.FS.readFile path))
  let object ← IO.ofExcept json.getObj?
  let allowed := ["domain", "federation", "factoryId", "resourceBookId",
    "authorityCellId", "issuer", "ownerBudget", "lifetime", "birthSlack",
    "tariffBase", "tariffPerBirth", "tariffPerGrant", "tariffPerInitialPayloadByte",
    "collector", "asset", "genesisHeight", "expectedSeed", "storageBinary",
    "storageRoot", "signatureBinary", "checkpointKey", "checkpointEvery",
    "jointConsensus", "nockFSync", "disabledEvaluators"]
  unless object.foldl (init := true) (fun valid key _ => valid && allowed.contains key) do
    throw (IO.userError "unsupported settings in ordinary source-agreement reader")
  let settings : Settings ← IO.ofExcept (fromJson? json)
  IO.ofExcept settings.checkDisabledEvaluators
  IO.ofExcept settings.checkJointConsensus
  unless settings.jointConsensus.isSome do
    throw (IO.userError "source-agreement reader requires an explicit consensus pin")
  pure settings

def profileDescription (config : NativeHost.Config)
    : Lean.Json :=
  let n := fun value : Nat => toJson (toString value)
  let base :=
    [("runtime", toJson "minidregg-native"),
     -- Binary capability only: API17 exact-fence continuity plus canonical
     -- invocation height pinning. It is not a current admission receipt.
     ("providerContinuityAdmission", toJson "exact-height-v1"),
     ("semantics", n config.profile.semantics.value),
     ("domain", n config.deployment.domain.value),
     ("expectedSeed", n config.expectedSeed.value),
     ("federation", n config.federation.value),
     ("factoryId", n config.deployment.factoryId),
     ("resourceBookId", n config.deployment.resourceBookId),
     ("authorityCellId", n config.deployment.authorityCellId),
     ("fieldModulus", n NativeHostProfile.characteristic),
     ("orderDifferenceWidth", n NativeHostProfile.orderWidth),
     ("genesisHeight", n config.genesisHeight),
     ("template", Lean.Json.mkObj [("issuer", n config.template.issuer.value),
       ("ownerBudget", n config.template.ownerBudget), ("lifetime", n config.template.lifetime)]),
     ("tariff", Lean.Json.mkObj [("base", n config.tariff.base),
       ("perBirth", n config.tariff.perBirth), ("perGrant", n config.tariff.perGrant),
       ("perInitialPayloadByte", n config.tariff.perInitialPayloadByte),
       ("collector", n config.tariff.collector), ("asset", n config.tariff.asset)]),
     ("runtimeParameters", toJson (Minidregg.Host.SourceAgreementJson.encodeHex config.runtimeParameters)),
     ("nativeChecked", toJson true), ("succinctProofDeployment", toJson false)]
  Lean.Json.mkObj base

def descriptionLoaded (config : NativeHost.Config) : Lean.Json := Id.run do
  let n := fun value : Nat => toJson (toString value)
  return Lean.Json.mkObj
    [("runtime", toJson "minidregg-native"),
     ("semantics", n config.profile.semantics.value),
     ("domain", n config.deployment.domain.value),
     ("payCell", n (Kernel.PayCell.physicalId config.deployment.domain)),
     ("fieldModulus", n NativeHostProfile.characteristic),
     ("orderDifferenceWidth", n NativeHostProfile.orderWidth),
     ("nativeChecked", toJson true), ("succinctProofDeployment", toJson false),
     ("operations", toJson
       ((["birth", "invoke", "install", "delegate", "revoke", "renounce",
          "source-agreement-reader"] : List String) ++
         if config.grainBirthTariff.isSome then ["grain-birth"] else [])),
     ("nockFSync", n config.nockFSync),
     ("jointInvocation", toJson true), ("typedContent", toJson true),
     ("authorizedQueries", toJson true), ("delegation", toJson true)]

def splitKind (payload : List UInt8) : IO (String × List UInt8) := do
  unless payload.length ≥ 2 do throw (RequestRefusal.malformed "short native host kind frame")
  let width := payload[0]!.toNat + 256 * payload[1]!.toNat
  unless width > 0 && width ≤ payload.length - 2 do
    throw (RequestRefusal.malformed "invalid native host kind length")
  let some kind := String.fromUTF8? (payload.drop 2 |>.take width).toByteArray
    | throw (RequestRefusal.malformed "native host kind is not UTF-8")
  return (kind, payload.drop (2 + width))

def splitPair (payload : List UInt8) : IO (List UInt8 × List UInt8) := do
  unless payload.length ≥ 4 do throw (RequestRefusal.malformed "short native host pair frame")
  let width := payload[0]!.toNat + 256 * payload[1]!.toNat +
    65536 * payload[2]!.toNat + 16777216 * payload[3]!.toNat
  unless width ≤ payload.length - 4 do throw (RequestRefusal.malformed "invalid native host pair length")
  return ((payload.drop 4).take width, payload.drop (4 + width))

def decodeSignatures (bytes : List UInt8) : IO (List (List UInt8)) := do
  let signaturesCodec := ResourceBirthCodec.strictCodec (StreamCodec.list bytesStream).toLawful
  let some signatures := signaturesCodec.decode bytes
    | throw (RequestRefusal.malformed "noncanonical signature list")
  return signatures

def maxFrame : Nat := FnEvidenceCodec.maxHostFrameBytes

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

def writeSessionFrame (output : IO.FS.Stream) (operation : UInt8)
    (payload : List UInt8) : IO Unit := do
  let response := (operation :: payload).toByteArray
  if response.size > maxFrame then
    throw (IO.userError "native host response exceeds frame budget")
  output.write (lengthBytes response.size ++ response)
  output.flush

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


def opened (config : NativeHost.Config) : IO (NativeHost.Opened config) := do
  IO.ofExcept (← NativeHost.openExisting config)

def refusalFrame (phase : String) (refusal : Refusal) : List UInt8 :=
  outcomeCodec.encode (NativeHost.refusalOutcome phase refusal)

def dispatch (config : NativeHost.Config) (operation : UInt8)
    (payload : List UInt8) : IO (UInt8 × List UInt8) := do
  match operation with
  | 0 =>
      unless payload.isEmpty do throw (RequestRefusal.malformed "describe does not accept a payload")
      discard <| opened config
      return (0, (descriptionLoaded config).compress.toUTF8.toList)
  | 1 =>
      match ← NativeHost.prepareAuthorizedLoaded config (← opened config) payload with
      | .ok plan => return (1, signingPlanCodec.encode plan)
      | .error detail => return (255, refusalFrame "prepare" detail)
  | 3 =>
      return (3, outcomeCodec.encode (← NativeHost.lookup config payload))
  | 4 =>
      match ← NativeHost.challengeWireLoaded config (← opened config) payload with
      | .ok result => return (4, result)
      | .error detail => return (255, refusalFrame "observation" detail)
  | 5 =>
      match ← NativeHost.queryWireLoaded config (← opened config) payload with
      | .ok result => return (5, result)
      | .error detail => return (255, refusalFrame "observation" detail)
  | 6 =>
      unless payload.isEmpty do throw (RequestRefusal.malformed "profile does not accept a payload")
      return (6, (profileDescription config).compress.toUTF8.toList)
  | 7 =>
      let (kind, source) ← splitKind payload
      let some text := String.fromUTF8? source.toByteArray
        | throw (RequestRefusal.malformed "native host author source is not UTF-8")
      let json ← RequestRefusal.clientBytes (SourceAgreementJson.parse text)
      return (7, ← RequestRefusal.clientBytes (SourceAgreementJson.author kind json (some config)))
  | 8 =>
      let (kind, source) ← splitKind payload
      let value ← RequestRefusal.clientBytes (SourceAgreementJson.inspect kind source)
      return (8, value.compress.toUTF8.toList)
  | 9 =>
      let some text := String.fromUTF8? payload.toByteArray
        | throw (RequestRefusal.malformed "native host signatures source is not UTF-8")
      let json ← RequestRefusal.clientBytes (SourceAgreementJson.parse text)
      return (9, ← RequestRefusal.clientBytes (SourceAgreementJson.signatures json))
  | 10 =>
      let (challengeBytes, signaturesBytes) ← splitPair payload
      let some challenge := NativeObservationCodec.challengeCodec.decode challengeBytes
        | throw (RequestRefusal.malformed "noncanonical observation challenge")
      let signatures ← decodeSignatures signaturesBytes
      let signed ← RequestRefusal.clientBytes (NativeObservationCodec.assemble challenge signatures)
      return (10, NativeObservationCodec.signedCodec.encode signed)
  | 11 =>
      let (planBytes, signaturesBytes) ← splitPair payload
      let some plan := signingPlanCodec.decode planBytes
        | throw (RequestRefusal.malformed "noncanonical signing plan")
      let signatures ← decodeSignatures signaturesBytes
      let call ← RequestRefusal.clientBytes (NativeHost.assemble plan signatures)
      return (11, callCodec.encode call)
  | 91 =>
      let (signedObservationBytes, sourceBytes) ← splitPair payload
      let image ← opened config
      let some source := String.fromUTF8? sourceBytes.toByteArray
        | throw (RequestRefusal.malformed "resource birth request is not UTF-8")
      let json ← RequestRefusal.clientBytes (SourceAgreementJson.parse source)
      let intent ← IO.ofExcept (← SourceAgreementBirth.intentLoadedAuthorized
        config image signedObservationBytes json)
      unless intent.length ≤ maxFrame do
        throw (IO.userError "resource birth intent exceeds host frame bound")
      return (91, intent)
  | 144 =>
      let some text := String.fromUTF8? payload.toByteArray
        | throw (RequestRefusal.malformed "key status query is not UTF-8")
      let query ← RequestRefusal.clientBytes (SourceAgreementJson.parse text)
      let (subject, publicKey) ← RequestRefusal.clientBytes
        (SourceAgreementJson.subjectKeyStatusQuery query)
      match NativeHost.keyStatusLoaded config (← opened config) ⟨subject⟩ publicKey with
      | .error detail => return (255, outcomeCodec.encode
          (.refused .operationRejected "key-status".toUTF8.toList detail.toUTF8.toList))
      | .ok status => return (144,
          (SourceAgreementJson.subjectKeyStatusJson subject status).compress.toUTF8.toList)
  | _ => throw (RequestRefusal.malformed "operation not served by source-agreement reader")

partial def serve (config : NativeHost.Config) (input output : IO.FS.Stream) : IO Unit := do
  let first ← input.read 1
  if first.isEmpty then return
  let lengthWire ← readExactly input 4 first
  let length := frameLength lengthWire
  unless 0 < length && length ≤ maxFrame do
    throw (IO.userError "native host frame exceeds ordinary operation bound")
  let body ← readExactly input length
  let operation := body[0]!
  let answer ← try dispatch config operation (body.toList.drop 1)
    catch error => pure (255, RequestRefusal.frame operation error)
  writeSessionFrame output answer.1 answer.2
  serve config input output

def run (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path, "stdio"] =>
      let settings ← loadSettings path
      withPinnedSignature settings.config fun config => do
        discard <| opened config
        serve config (← IO.getStdin) (← IO.getStdout)
        pure 0
  | _ => throw (IO.userError "usage: minidregg-source-agreement-reader CONFIG stdio")
end Minidregg.Host.SourceAgreementReader

def main (arguments : List String) : IO UInt32 := do
  try Minidregg.Host.SourceAgreementReader.run arguments
  catch error =>
    IO.eprintln s!"minidregg-source-agreement-reader: {error}"
    pure 1
