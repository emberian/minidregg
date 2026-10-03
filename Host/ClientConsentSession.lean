/- Local full-peer consent process. Settings and executable are selected by
local custody. The operator supplies proposed frames only. Initial history is
independently re-admitted once; later frames verify only an exact source suffix.
No protected Store is transmitted by this process. Thin peers need a separate
selective authenticated witness producer; this executable is not that producer.
-/
import Kernel.NativeClientConsent
import Kernel.NativeHostGenesis
import Compiler.GenericSimplexSourceAnchor
import Compiler.FnEvidenceCodec
import Host.SourceAgreementJson
import Host.RequestRefusal
import Lean.Data.Json

open Lean Minidregg.Compiler Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend Minidregg.Kernel
namespace Minidregg.Host.ClientConsentSession
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

structure GatewayPinSettings where
  application : String
  subject : Nat
  target : Nat
  capability : Nat
  policyAddress : String
  deriving FromJson, ToJson

structure GrainBirthTariffSettings where
  base : Nat
  perBirth : Nat
  deriving FromJson, ToJson

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
  fnGateway : Option GatewayPinSettings := none
  grainBirthTariff : Option GrainBirthTariffSettings := none
  completionCustodianKey : Option String := none
  nockFSync : Option Nat := none
  disabledEvaluators : Option (List String) := none
  deriving FromJson, ToJson

def Settings.disabledEvaluatorIds (settings : Settings) :
    List Minidregg.Theory.TypedAuthorization.Digest :=
  (settings.disabledEvaluators.getD []).map fun name =>
    match Minidregg.Compiler.Evaluator.registry.find? (fun E => E.name == name) with
    | some E => E.id
    | none => Minidregg.Compiler.Evaluator.idOf name ""

def Settings.checkDisabledEvaluators (settings : Settings) : Except String Unit :=
  (settings.disabledEvaluators.getD []).forM fun name =>
    if (Minidregg.Compiler.Evaluator.registry.find? (fun E => E.name == name)).isSome then .ok ()
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
  fnGateway := settings.fnGateway.map fun pin =>
    ⟨pin.application.toUTF8.toList, ⟨pin.subject⟩, pin.target,
      ⟨pin.capability⟩, ⟨pin.policyAddress.toNat!⟩⟩
  grainBirthTariff := settings.grainBirthTariff.map fun tariff => ⟨tariff.base, tariff.perBirth⟩
  completionCustodianKey := settings.completionCustodianKey.map fun key =>
    (SourceAgreementJson.decodeHex "completionCustodianKey" (.str key)).toOption.getD []

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
    "jointConsensus", "nockFSync", "disabledEvaluators", "fnGateway",
    "grainBirthTariff", "completionCustodianKey"]
  unless object.foldl (init := true) (fun valid key _ => valid && allowed.contains key) do
    throw (IO.userError "unsupported settings in client consent provider")
  let settings : Settings ← IO.ofExcept (fromJson? json)
  if let some pin := settings.fnGateway then
    let some address := pin.policyAddress.toNat? | throw (IO.userError "invalid gateway policy address")
    unless toString address == pin.policyAddress do
      throw (IO.userError "noncanonical gateway policy address")
  if let some tariff := settings.grainBirthTariff then
    unless 0 < tariff.base do throw (IO.userError "grain birth tariff base must be positive")
  if let some key := settings.completionCustodianKey then
    let bytes ← IO.ofExcept (SourceAgreementJson.decodeHex "completionCustodianKey" (.str key))
    unless bytes.length == 32 && SourceAgreementJson.encodeHex bytes == key do
      throw (IO.userError "noncanonical completion custodian key")
  IO.ofExcept settings.checkDisabledEvaluators
  IO.ofExcept settings.checkJointConsensus
  pure settings

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



/-- The retained proof is updated only by independent native admission. The
physical Store/MAC is merely an input reader, never a semantic trust source. -/
abbrev Session (config : NativeHost.Config) := Sigma (NativeHostReplay.Verified config)

def verifyInitial (config : NativeHost.Config) : IO (Session config) := do
  let target ← IO.ofExcept (← DurableReceiverIO.load config.transport ResourceBirthCodec.rootBytes)
  match ← NativeHostReplay.verifyLoaded config target with
  | .error failure => throw (IO.userError s!"consent prefix refused at {failure.index}: {failure.detail}")
  | .ok verified => pure ⟨target, verified⟩

def refresh (config : NativeHost.Config) (old : Session config) : IO (Session config) := do
  let target ← IO.ofExcept (← DurableReceiverIO.load config.transport ResourceBirthCodec.rootBytes)
  match ← NativeHostReplay.extendVerified config old.2 target with
  | .error failure => throw (IO.userError s!"consent extension refused at {failure.index}: {failure.detail}")
  | .ok verified => pure ⟨target, verified⟩

def headersBytes (headers : List (List UInt8)) : List UInt8 :=
  (Lean.toJson (headers.map SourceAgreementJson.encodeHex)).compress.toUTF8.toList

def consent (config : NativeHost.Config) (session : Session config) (operation : UInt8)
    (payload : List UInt8) : IO (List UInt8) := do
  let (intentBytes, rest) ← splitPair payload
  let some wanted := NativeObservationCodec.intentCodec.decode intentBytes
    | throw (IO.userError "noncanonical retained local intent")
  match operation with
  | 220 =>
      -- Before even the first intent signature, bind subject/current key to
      -- locally chosen custody, rather than a remote JSON subject label.
      let key ← IO.ofExcept ((NativeObservationController.intentKey
        (NativeHost.observationContext config session.2.opened) wanted.subject).mapError
        (fun _ => "local intent subject has no current signing key"))
      unless rest.length == 32 && key == rest do
        throw (IO.userError "local intent subject differs from custody signer")
      pure intentBytes
  | 221 =>
      let (signature, candidate) ← splitPair rest
      let checked ← IO.ofExcept (NativeClientConsent.checkObservation config session.2 wanted signature candidate)
      pure (headersBytes checked.headers)
  | 222 =>
      let headers ← IO.ofExcept (NativeClientConsent.checkIntentPlan config session.2 wanted rest)
      pure (headersBytes headers)
  | _ => throw (IO.userError "unsupported consent operation")

partial def serve (config : NativeHost.Config) (session : Session config)
    (input output : IO.FS.Stream) : IO Unit := do
  let first ← input.read 1
  if first.isEmpty then return
  let lengthWire ← readExactly input 4 first
  let length := frameLength lengthWire
  unless 0 < length && length ≤ maxFrame do throw (IO.userError "consent frame exceeds bound")
  let body ← readExactly input length
  let operation := body[0]!
  -- A failed refresh terminates the provider: no cached success may survive
  -- an observed rollback, rewritten prefix, or failed semantic suffix.
  let updated ← refresh config session
  let answer ← try pure (operation, ← consent config updated operation (body.toList.drop 1))
    catch error => pure (255, error.toString.toUTF8.toList)
  writeSessionFrame output answer.1 answer.2
  serve config updated input output

def run (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path, "stdio"] =>
      let settings ← loadSettings path
      withPinnedSignature settings.config fun config => do
        let session ← verifyInitial config
        serve config session (← IO.getStdin) (← IO.getStdout)
        pure 0
  | _ => throw (IO.userError "usage: minidregg-client-consent CONFIG stdio")
end Minidregg.Host.ClientConsentSession

def main (arguments : List String) : IO UInt32 := do
  try Minidregg.Host.ClientConsentSession.run arguments
  catch error =>
    IO.eprintln s!"minidregg-client-consent: {error}"
    pure 1
