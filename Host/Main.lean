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
import Kernel.NativeHostGenesis
import Kernel.FnEvidence
import Kernel.FnConsumerOperation
import Kernel.FnPortableSource
import Host.Json
import Lean.Data.Json

open Lean
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel

namespace Minidregg.Host

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

def description (config : NativeHost.Config) : IO Lean.Json := do
  discard <| IO.ofExcept (← NativeHost.openExisting config)
  let n := fun value : Nat => toJson (toString value)
  pure <| Lean.Json.mkObj
    [("runtime", toJson "minidregg-native"),
     ("semantics", n config.profile.semantics.value),
     ("domain", n config.deployment.domain.value),
     ("fieldModulus", n Minidregg.Compiler.babyBearP),
     ("orderDifferenceWidth", n NativeHostProfile.orderWidth),
     ("nativeChecked", toJson true), ("succinctProofDeployment", toJson false),
     ("operations", toJson (["birth", "invoke", "install", "delegate", "revoke"] : List String)),
     ("jointInvocation", toJson true), ("typedContent", toJson true),
     ("authorizedQueries", toJson true), ("delegation", toJson true)]

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

def decodeCanonicalHex (label value : String) : Except String (List UInt8) := do
  let bytes ← Minidregg.Host.Json.decodeHex label (.str value)
  unless Minidregg.Host.Json.encodeHex bytes == value do
    throw s!"{label} is not canonical lowercase hexadecimal"
  pure bytes

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

def verifyFnPortable (pin : FnPortablePin) (claim : FnPortableClaim)
    (carrierPath : String) : IO (List UInt8 × FnPortableVerified × FnPortableSource.Extracted) := do
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
  let extracted ← IO.ofExcept (FnPortableSource.extract verified.source)
  unless extracted.messageId == claim.messageId && extracted.groups == claim.groups do
    throw (IO.userError "fn source metadata differs from claimed exact report")
  pure (carrier, verified, extracted)

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
    ⟨source.expectedAuthorityRoot⟩, ⟨source.expectedTargetRoot⟩⟩

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
  | .conflict _ => .mkObj [("type", "proposed-conflict-evidence")]
  | .conflictRecorded => .mkObj [("type", "historical-conflict-evidence")]
  | .refused detail => .mkObj [("type", "refused"), ("detail", toJson detail)]

def writeBytes (path : String) (bytes : List UInt8) : IO Unit :=
  IO.FS.writeBinFile path bytes.toByteArray

def readJson (path : String) : IO Lean.Json :=
  return ← IO.ofExcept (Minidregg.Host.Json.parse (← IO.FS.readFile path))

def writeJson (path : String) (value : Lean.Json) : IO Unit :=
  IO.FS.writeFile path value.pretty

def usage : String :=
  "minidregg-host CONFIG.json profile|describe|stdio|author KIND INPUT.json OUTPUT.bin|inspect KIND INPUT.bin OUTPUT.json|derive grain INPUT.json OUTPUT.json|signatures INPUT.json OUTPUT.bin|genesis SOURCE-CONFIG.bin GENESIS.bin PINNED-CONFIG.json|bootstrap GENESIS.bin|challenge INTENT.bin CHALLENGE.bin|observe-assemble CHALLENGE.bin SIGNATURES.bin SIGNED.bin|prepare SIGNED.bin PLAN.bin|query SIGNED.bin VIEW.bin|assemble PLAN.bin SIGNATURES.bin CALL.bin|submit CALL.bin OUTCOME.bin|lookup CALL.bin OUTCOME.bin|export-evidence CALL.bin PACKAGE.bin|verify-evidence PACKAGE.bin RESULT.json|portable-verify-fn FN-PIN.json CLAIM.json CARRIER.eml SOURCE.bin PACKAGE.bin RESULT.json|consumer-decide-test ORIGIN-PIN.json POLICY.json REPORT.json PACKAGE.bin INTENT.bin DECISION.json"

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
          discard <| IO.ofExcept (← NativeHost.openExisting config)
          serve config (← IO.getStdin) (← IO.getStdout)
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
      | "consumer-decide-test", [originPath, policyPath, reportPath, packagePath, intentPath, resultPath] =>
          let origin := (← loadSettings originPath).config
          let policySource : ConsumerPolicySource ← IO.ofExcept (fromJson? (← readJson policyPath))
          let source : ConsumerReportSource ← IO.ofExcept (fromJson? (← readJson reportPath))
          let report := source.report
            (← readBoundedBytes packagePath FnEvidenceCodec.maxPackageBytes)
          let decision ← IO.ofExcept (← FnConsumerOperation.evaluate origin config
            policySource.policy report)
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
