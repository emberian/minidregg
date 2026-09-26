/-
Pure selected-profile response-size probe for Host.Main opcode 16. It mirrors
runFnOriginOutboxSession's complete JSON response fields and opcode byte using
the actual Host JSON helpers. Carrier bytes are synthetic; native fn carrier
verification and receiving admission are tested separately.
-/
import Host.Main

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.FnOriginOutbox
open Lean

set_option autoImplicit false

private def require (condition : Bool) (detail : String) : IO Unit := do
  unless condition do throw (IO.userError detail)

def originOutboxOp16FrameProbe : IO Unit := do
  let domain : Digest := ⟨8501⟩
  let semantics : Digest := ⟨6⟩
  let largestDigest : Digest := ⟨2 ^ 256 - 1⟩
  let receipt : NativeHostCodec.Receipt :=
    ⟨largestDigest, largestDigest, 4294967295, largestDigest⟩
  let package : FnEvidenceCodec.Package :=
    ⟨domain, semantics, ⟨104⟩, [1], receipt, [2]⟩
  let packageBytes ← IO.ofExcept (FnEvidenceCodec.encodeChecked package)
  let prepared : Prepared :=
    ⟨[17], FnConsumerOperation.originOperation package,
      [60] ++ List.replicate 254 65 ++ [62], List.replicate 48 3,
      List.replicate FnEvidenceCodec.maxCarrierBytes (4 : UInt8),
      packageIdentity packageBytes, callIdentity package.signedCall,
      receipt, List.replicate 32 5, List.replicate 32 6,
      List.replicate 1952 7⟩
  let report : Report :=
    ⟨prepared, packageBytes, ⟨7⟩, 600, ⟨61⟩, ⟨11⟩, ⟨12⟩, true, true⟩
  let pin : FnGatewayPolicy.Pin := ⟨[17], ⟨7⟩, 600, ⟨61⟩, ⟨99⟩⟩
  let policy : FnConsumerOperation.Policy := ⟨[17], ⟨7⟩, 600, ⟨61⟩⟩
  let .ok () := checkReport pin policy report
    | throw (IO.userError "maximal prepared R exceeds selected outbox profile")
  let some intent := (Decision.fresh (outboxCommand domain semantics report)).intent report
    | throw (IO.userError "maximal prepared R had no observation intent")
  let intentBytes := NativeObservationCodec.intentCodec.encode intent
  let response := Lean.Json.mkObj
    [("type", toJson "fn-a-origin-outbox-session-v1"),
     ("status", toJson "prepared-decision"),
     ("decision", toJson "proposed-fresh"),
     ("messageId", toJson (String.fromUTF8! prepared.messageId.toByteArray)),
     ("sourceIdentity", toJson
       (Minidregg.Host.Json.encodeHex prepared.sourceIdentity)),
     ("miniOrigin", Minidregg.Host.evidenceReceiptJson receipt),
     ("intentHex", toJson (Minidregg.Host.Json.encodeHex intentBytes))]
  let responseBytes := (16 :: response.compress.toUTF8.toList)
  require (responseBytes.length ≤ FnEvidenceCodec.maxHostFrameBytes)
    "maximal opcode-16 JSON response exceeds selected native host frame"
  IO.println s!"PASS maximal prepared R op16 response: intent={intentBytes.length} jsonOpcodeFrame={responseBytes.length} cap={FnEvidenceCodec.maxHostFrameBytes} margin={FnEvidenceCodec.maxHostFrameBytes - responseBytes.length}"

#eval originOutboxOp16FrameProbe
