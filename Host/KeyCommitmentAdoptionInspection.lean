/- Narrow JSON edge for first next-key commitment planning and inspection.
The wire command and both signed frames remain source-owned. -/
import Kernel.NativeHostKeyCommitmentAdoption
import Host.CarryInspection

namespace Minidregg.Host.KeyCommitmentAdoptionInspection
open Lean Minidregg.Compiler Minidregg.Kernel Minidregg.Theory
open Minidregg.Theory.CredentialSigningKey
set_option autoImplicit false

private def natural (json : Json) (field : String) : Except String Nat := do
  let text ← (← json.getObjVal? field).getStr?
  if text.length > 80 then throw "adoption integer exceeds bound"
  let some value := text.toNat? | throw "adoption integer must be decimal"
  if toString value != text then throw "adoption integer must be canonical decimal"
  return value

private def nibble (character : Char) : Option Nat :=
  if '0' ≤ character && character ≤ '9' then some (character.toNat - '0'.toNat)
  else if 'a' ≤ character && character ≤ 'f' then some (character.toNat - 'a'.toNat + 10)
  else none

private def hexBytes : List Char → Option (List UInt8)
  | [] => some []
  | left :: right :: rest => do
    let a ← nibble left
    let b ← nibble right
    let tail ← hexBytes rest
    return UInt8.ofNat (16*a+b) :: tail
  | _ => none

private def publicKey (json : Json) (field : String) : Except String (List UInt8) := do
  let text ← (← json.getObjVal? field).getStr?
  if text.length != 64 then throw "adoption public key must be hex32"
  let some bytes := hexBytes text.toList | throw "adoption public key is not lowercase hex"
  return bytes

def parseRequest (json : Json) : Except String NativeHostKeyCommitmentAdoption.PlanRequest := do
  return ⟨⟨← natural json "subject"⟩, ← natural json "nonce",
    ← publicKey json "currentPublicKey", ← publicKey json "nextPublicKey"⟩

private def decimal (n : Nat) : Json := .str (toString n)
private def hex (bytes : List UInt8) : Json := .str (CarryInspection.encodeHex bytes)

def keyJson (key : KeyRecord) : Json := Json.mkObj [
  ("keyId", decimal key.keyId), ("keyEpoch", decimal key.keyEpoch), ("algorithm", decimal key.algorithm),
  ("subject", decimal key.subject), ("publicKey", hex key.publicKey),
  ("activeFrom", decimal key.activeFrom), ("activeUntil", decimal key.activeUntil),
  ("nextKeyDigest", match key.nextKeyDigest with | none => .null | some digest => decimal digest.value)]

def commandJson (command : SubjectKeyCommitmentAdoption.Command) : Json := Json.mkObj [
  ("subject", decimal command.subject.value), ("nonce", decimal command.nonce),
  ("expectedCurrent", keyJson command.expectedCurrent), ("nextPublicKey", hex command.nextPublicKey)]

def inspectPlan (bytes : List UInt8) : Except String Json := do
  let some plan := SubjectKeyCommitmentAdoption.signingPlanCodec.decode bytes
    | throw "noncanonical adoption plan"
  let some command := SubjectKeyCommitmentAdoption.commandCodec.decode plan.commandBytes
    | throw "noncanonical adoption plan command"
  if plan.currentAuthorizationHeader != SubjectKeyCommitmentAdoption.authorizationFrame plan.domain plan.semantics command ||
      plan.nextPossessionHeader != SubjectKeyCommitmentAdoption.possessionFrame plan.domain plan.semantics command then
    throw "adoption plan signing frames differ"
  return Json.mkObj [
    ("type", .str "subject-key-adoption-plan-v1"),
    ("domain", decimal plan.domain.value), ("semantics", decimal plan.semantics.value),
    ("command", commandJson command), ("commandBytes", hex plan.commandBytes),
    ("currentAuthorizationHeader", hex plan.currentAuthorizationHeader),
    ("nextPossessionHeader", hex plan.nextPossessionHeader)]

def inspectIngress (bytes : List UInt8) : Except String Json := do
  let some ingress := SubjectKeyCommitmentAdoption.decodeIngress bytes
    | throw "noncanonical adoption ingress"
  return Json.mkObj [
    ("type", .str "subject-key-adoption-ingress-v1"),
    ("command", commandJson ingress.command), ("commandBytes", hex ingress.ingress.commandBytes),
    ("currentSignature", hex ingress.ingress.currentSignature),
    ("nextPossessionSignature", hex ingress.ingress.nextPossessionSignature)]

def planLoaded (config : NativeHost.Config) (opened : NativeHost.Opened config) (bytes : List UInt8) :
    Except String (List UInt8) := do
  if bytes.length > 4096 then throw "adoption plan request exceeds bound"
  let some text := String.fromUTF8? bytes.toByteArray | throw "adoption request is not UTF-8"
  let request ← parseRequest (← Json.parse text)
  return SubjectKeyCommitmentAdoption.signingPlanCodec.encode (← NativeHostKeyCommitmentAdoption.planLoaded config opened request)
end Minidregg.Host.KeyCommitmentAdoptionInspection
