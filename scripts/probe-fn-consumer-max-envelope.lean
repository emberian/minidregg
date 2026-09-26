/-
Pure maximal Mini fn consumer envelope probe. This deliberately does not claim
that its synthetic bytes are fn-authenticated evidence or an admitted call.
It measures the local command/observation codecs at the selected V2 bounds.
-/
import Host.Main
import Kernel.FnConsumerOperationProofs

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel
open Minidregg.Kernel.FnConsumerOperation

set_option autoImplicit false

private def require (ok : Bool) (message : String) : IO Unit := do
  unless ok do throw (IO.userError message)

def probeMain : IO Unit := do
  let fullDigest : Digest := ⟨2 ^ 256 - 1⟩
  let originReceipt : Receipt := ⟨fullDigest, fullDigest, 4294967295, fullDigest⟩
  let basePackage : FnEvidenceCodec.Package :=
    ⟨⟨8501⟩, ⟨6⟩, ⟨104⟩, List.replicate 260000 (1 : UInt8),
      originReceipt, List.replicate FnEvidenceCodec.maxPrefixBytes (2 : UInt8)⟩
  let baseBytes ← IO.ofExcept (FnEvidenceCodec.encodeChecked basePackage)
  let padding := FnEvidenceCodec.maxPackageBytes - baseBytes.length
  let paddedCall := List.replicate
    (basePackage.signedCall.length + padding) (1 : UInt8)
  let fullPackage : FnEvidenceCodec.Package :=
    { basePackage with signedCall := paddedCall }
  let packageBytes ← IO.ofExcept (FnEvidenceCodec.encodeChecked fullPackage)
  require (packageBytes.length == FnEvidenceCodec.maxPackageBytes)
    "canonical native-prefix package did not fill selected maximum"
  let decodedPackage ← IO.ofExcept (FnEvidenceCodec.decodeChecked packageBytes)
  require (if (FnEvidenceCodec.packageCodec.encode decodedPackage).toByteArray =
      packageBytes.toByteArray then true else false)
    "maximal canonical native-prefix package did not round trip"
  let sourceIdentity := List.replicate 48 (7 : UInt8)
  let verdictEvent := List.replicate
    FnEvidenceCodec.maxHistoricalVerdictEventBytes (8 : UInt8)
  let store : StorePollInbox :=
    ⟨[1], List.replicate maxStoreEventBytes (9 : UInt8), true,
      sourceIdentity, 1, 1, [10], List.replicate 32 (11 : UInt8),
      verdictEvent, [12]⟩
  let portable : PortableInbox :=
    ⟨List.replicate FnEvidenceCodec.maxCarrierBytes (13 : UInt8),
      sourceIdentity, List.replicate 32 (14 : UInt8),
      List.replicate 32 (15 : UInt8), List.replicate 1952 (16 : UInt8)⟩
  let portableBytes := portableInboxCodec.encode portable
  require (portableBytes.length ≤ maxInboxBytes)
    "maximal portable inbox exceeds selected bound"
  let some decodedPortable := portableInboxCodec.decode portableBytes
    | throw (IO.userError "maximal portable inbox did not strictly decode")
  require (if (portableInboxCodec.encode decodedPortable).toByteArray =
      portableBytes.toByteArray then true else false)
    "maximal portable inbox did not round trip exact bytes"
  let storeBytes := storePollCodec.encode store
  require (storeBytes.length ≤ maxStoreInboxBytes)
    "maximal Store poll inbox exceeds selected bound"
  let some decodedStore := storePollCodec.decode storeBytes
    | throw (IO.userError "maximal Store poll inbox did not strictly decode")
  require (if (storePollCodec.encode decodedStore).toByteArray =
      storeBytes.toByteArray then true else false)
    "maximal Store poll inbox did not round trip exact bytes"
  let report : Report :=
    { application := [17], operation := [18],
      provenance := ⟨[19], [20], sourceIdentity, storePollVerdictRef store⟩,
      package := packageBytes,
      subject := ⟨7⟩, target := 600, capability := ⟨61⟩,
      expectedAuthorityRoot := ⟨1⟩, expectedTargetRoot := ⟨2⟩,
      portableInbox := some portable, storePoll := some store }
  let .ok () := checkReport report
    | throw (IO.userError "maximal report rejected selected Mini profile")
  let receipt : Receipt := ⟨⟨3⟩, ⟨4⟩, 2, ⟨5⟩⟩
  let reply : Reply := ⟨report.application, report.operation,
    sourceIdentity, receipt⟩
  let binding : Binding :=
    ⟨report.application, report.operation, report.provenance, packageBytes, reply⟩
  let bindingBytes := bindingCodec.encode binding
  require (bindingBytes.length ≤ maxBindingBytes)
    "maximal binding exceeds selected bound"
  let some decodedBinding := bindingCodec.decode bindingBytes
    | throw (IO.userError "maximal binding did not strictly decode")
  require (if (bindingCodec.encode decodedBinding).toByteArray =
      bindingBytes.toByteArray then true else false)
    "maximal binding did not round trip exact bytes"
  let command ← IO.ofExcept (bindingCommand ⟨8501⟩ ⟨6⟩ report receipt)
  let commandBytes := DeclaredResourceController.commandCodec.encode command
  require (commandBytes.length ≤ FnEvidenceCodec.maxHostFrameBytes)
    "maximal command exceeds selected native host frame"
  let some decoded := DeclaredResourceController.commandCodec.decode commandBytes
    | throw (IO.userError "maximal command did not strictly decode")
  require (if (DeclaredResourceController.commandCodec.encode decoded).toByteArray =
      commandBytes.toByteArray then true else false)
    "maximal command did not round trip exact bytes"
  let some intent := (Decision.fresh command reply).intent report
    | throw (IO.userError "fresh command had no observation intent")
  let intentBytes := NativeObservationCodec.intentCodec.encode intent
  require (intentBytes.length ≤ FnEvidenceCodec.maxHostFrameBytes)
    "maximal observation intent exceeds selected native host frame"
  let some decodedIntent := NativeObservationCodec.intentCodec.decode intentBytes
    | throw (IO.userError "maximal observation intent did not strictly decode")
  require (if (NativeObservationCodec.intentCodec.encode decodedIntent).toByteArray =
      intentBytes.toByteArray then true else false)
    "maximal observation intent did not round trip exact bytes"
  -- This is the complete op12 wrapper built by runFnPollSession around the
  -- decision file built by runPollConsumerDecisionLoaded. Synthetic metadata
  -- uses the maximal u32 Store IDs and a full-size native receipt identifier.
  let pollDecisionJson := Lean.Json.mkObj
    [("type", .str "fn-poll-consumer-decision-v1"),
     ("portableAuthorship", .str "verified"),
     ("storeAdmission", .str "observed-control-poll"),
     ("sourceIdentity", .str (Minidregg.Host.Json.encodeHex sourceIdentity)),
     ("storeSequence", .str "4294967295"),
     ("storeTransactionId", .str "4294967295"),
     ("application", .str (Minidregg.Host.Json.encodeHex report.application)),
     ("operation", .str (String.fromUTF8! report.operation.toByteArray)),
     ("miniOrigin", Minidregg.Host.evidenceReceiptJson originReceipt),
     ("decision", Minidregg.Host.consumerDecisionJson (.fresh command reply))]
  let responseJson := Lean.Json.mkObj
    [("type", .str "fn-consumer-poll-session-v1"),
     ("status", .str "accepted-decision"),
     ("decision", pollDecisionJson),
     ("intentHex", .str (Minidregg.Host.Json.encodeHex intentBytes))]
  let responseBytes := (12 :: responseJson.compress.toUTF8.toList)
  require (responseBytes.length ≤ FnEvidenceCodec.maxHostFrameBytes)
    "maximal opcode-12 JSON response exceeds selected native host frame"
  let nonce := conflictNonce ⟨8501⟩ ⟨6⟩ report
  let conflictEvidence : ConflictEvidence :=
    ⟨report.application, report.operation, report.provenance, packageBytes⟩
  let conflictEvidenceBytes := conflictCodec.encode conflictEvidence
  require (conflictEvidenceBytes.length ≤ maxBindingBytes)
    "maximal conflict evidence exceeds selected bound"
  let some decodedConflictEvidence := conflictCodec.decode conflictEvidenceBytes
    | throw (IO.userError "maximal conflict evidence did not strictly decode")
  require (if (conflictCodec.encode decodedConflictEvidence).toByteArray =
      conflictEvidenceBytes.toByteArray then true else false)
    "maximal conflict evidence did not round trip exact bytes"
  let storeConflictId := storeConflictAtom ⟨8501⟩ ⟨6⟩ report
  require (storeConflictId.digest.value > 2 ^ 259)
    "store conflict atom did not use reserved namespace"
  let conflict := conflictCommand ⟨8501⟩ ⟨6⟩ report
  require (conflict.nonce == nonce) "conflict nonce differs from command"
  let conflictBytes := DeclaredResourceController.commandCodec.encode conflict
  require (conflictBytes.length ≤ FnEvidenceCodec.maxHostFrameBytes)
    "maximal conflict command exceeds selected native host frame"
  let some decodedConflict := DeclaredResourceController.commandCodec.decode conflictBytes
    | throw (IO.userError "maximal conflict command did not strictly decode")
  require (if (DeclaredResourceController.commandCodec.encode decodedConflict).toByteArray =
      conflictBytes.toByteArray then true else false)
    "maximal conflict command did not round trip exact bytes"
  IO.println s!"PASS maximal fn consumer envelope: binding={bindingBytes.length} \
    portable={portableBytes.length} store={storeBytes.length} \
    command={commandBytes.length} intent={intentBytes.length} \
    op12Frame={responseBytes.length} \
    conflict={conflictBytes.length} \
    frame={FnEvidenceCodec.maxHostFrameBytes}"

#eval probeMain
