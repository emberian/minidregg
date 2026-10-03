/- Source-owned JSON lowering/presentation for the narrow physical recovery report. -/
import Host.ApplicationFailedStartRecoveryAuthoring
import Host.ApplicationFailedStartRecoveryInspection
import Lean.Data.Json

namespace Minidregg.Host.ApplicationFailedStartRecoveryTools
open Lean
open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel
open ApplicationFailedStartRecoveryReport
set_option autoImplicit false

private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
private def str (j : Json) (key : String) : Except String String := do
  (← field j key).getStr?
private def nat (j : Json) (key : String) : Except String Nat := do
  let s ← str j key
  let some n := s.toNat? | throw s!"invalid decimal {key}"
  unless toString n == s do throw s!"noncanonical decimal {key}"
  return n
private def integer (j : Json) (key : String) : Except String Int := do
  let s ← str j key
  let some n := s.toInt? | throw s!"invalid integer {key}"
  unless toString n == s do throw s!"noncanonical integer {key}"
  return n
private def bool (j : Json) (key : String) : Except String Bool := do
  (← field j key).getBool?
private def text (j : Json) (key : String) : Except String (List UInt8) := do
  return (← str j key).toUTF8.toList
private def digit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none
private def unhex (s : String) : Except String (List UInt8) := do
  let chars := s.toList
  unless chars.length % 2 == 0 do throw "odd hex length"
  let rec go : List Char → Except String (List UInt8)
    | [] => .ok []
    | a :: b :: tail => do
        let some x := digit a | throw "noncanonical hex"
        let some y := digit b | throw "noncanonical hex"
        return UInt8.ofNat (16*x+y) :: (← go tail)
    | _ => .error "odd hex length"
  go chars
private def bytes (j : Json) (key : String) : Except String (List UInt8) := do
  unhex (← str j key)
private def nibble (n : Nat) : Char := "0123456789abcdef".toList[n]?.getD '0'
private def hex (bs : List UInt8) : Json := .str <| String.ofList <|
  bs.flatMap fun b => [nibble (b.toNat / 16), nibble (b.toNat % 16)]
private def decimal (n : Nat) : Json := .str (toString n)
private def utf8 (bs : List UInt8) : Json := .str (String.fromUTF8! bs.toByteArray)

private def parseAudit (j : Json) : Except String Audit := do
  unless (← str j "protocol") == "mini-spk-failed-start-audit-v1" do
    throw "failed START audit protocol refused"
  unless (← field j "childPid") == Json.null do throw "failed START child remains"
  return {
    app := ← nat j "app", generation := ← integer j "generation"
    operationId := ← nat j "operationId"
    transactionId := ⟨← nat j "transactionId"⟩, eventId := ⟨← nat j "eventId"⟩
    imageIdentity := ← bytes j "imageIdentity", unit := ← text j "unit"
    recordedInvocationId := ← text j "recordedInvocationId"
    recordedControlGroup := ← text j "recordedControlGroup"
    recordPhase := ← text j "recordPhase", childPid := none
    managerLoaded := ← bool j "managerLoaded"
    managerActiveState := ← text j "managerActiveState"
    managerMainPid := ← nat j "managerMainPid"
    managerJobEmpty := ← bool j "managerJobEmpty"
    managerInvocationId := ← text j "managerInvocationId"
    managerControlGroup := ← text j "managerControlGroup"
    recordedCgroupUnpopulated := ← bool j "recordedCgroupUnpopulated" }

def auditJson (a : Audit) : Json := .mkObj
  [("protocol", "mini-spk-failed-start-audit-v1"), ("app", decimal a.app),
   ("generation", .str (toString a.generation)), ("operationId", decimal a.operationId),
   ("transactionId", decimal a.transactionId.value), ("eventId", decimal a.eventId.value),
   ("imageIdentity", hex a.imageIdentity), ("unit", utf8 a.unit),
   ("recordedInvocationId", utf8 a.recordedInvocationId),
   ("recordedControlGroup", utf8 a.recordedControlGroup), ("recordPhase", utf8 a.recordPhase),
   ("childPid", Json.null), ("managerLoaded", .bool a.managerLoaded),
   ("managerActiveState", utf8 a.managerActiveState), ("managerMainPid", decimal a.managerMainPid),
   ("managerJobEmpty", .bool a.managerJobEmpty), ("managerInvocationId", utf8 a.managerInvocationId),
   ("managerControlGroup", utf8 a.managerControlGroup),
   ("recordedCgroupUnpopulated", .bool a.recordedCgroupUnpopulated)]

def reportSource (r : Report) : Json :=
  let begin := r.claim.originalClaim.originalBegin
  .mkObj [("originalBeginHex", hex begin.canonicalBytes),
    ("originalClaimHex", hex r.claim.originalClaim.canonicalBytes),
    ("committedClaimHex", hex r.claim.canonicalBytes), ("audit", auditJson r.audit),
    ("semantics", decimal begin.base.semantics.value)]

def authorReport (j : Json) : Except String (List UInt8) := do
  let some begin := ApplicationLifecycleBeginV3Ingress.codec.decode (← bytes j "originalBeginHex")
    | throw "noncanonical original BEGIN"
  let some claim := ApplicationLifecycleClaimV3Ingress.codec.decode (← bytes j "originalClaimHex")
    | throw "noncanonical original claim"
  let some committed := ApplicationLifecycleClaimV3Projection.codec.decode (← bytes j "committedClaimHex")
    | throw "noncanonical committed claim"
  let r : Report := ⟨committed, ← parseAudit (← field j "audit")⟩
  unless committed.originalClaim == claim && claim.originalBegin == begin &&
      (← nat j "semantics") == begin.base.semantics.value && r.validFor begin do
    throw "failed START report differs from original admitted identities"
  unless reportSource r == j do throw "failed START report source not exact"
  return r.canonicalBytes

def inspectReport (bs : List UInt8) : Except String Json := do
  let some r := codec.decode bs | throw "noncanonical failed START report"
  let begin := r.claim.originalClaim.originalBegin
  unless r.validFor begin do throw "invalid failed START audit"
  return .mkObj [("type", "application-failed-start-report-v1"),
    ("canonicalReportHex", hex bs), ("source", reportSource r),
    ("signingHeaderHex", hex <| signingFrame begin.base.domain begin.base.semantics r)]

def authorSignedReport (j : Json) : Except String (List UInt8) := do
  let some r := codec.decode (← bytes j "reportHex") | throw "noncanonical failed START report"
  let publicKey ← bytes j "publicKeyHex"
  let signature ← bytes j "signatureHex"
  unless publicKey.length == 32 && signature.length == 64 &&
      r.validFor r.claim.originalClaim.originalBegin do throw "invalid signed failed START report"
  return signedCodec.encode ⟨r, signature⟩

def authorRequest (j : Json) : Except String (List UInt8) := do
  let request : ApplicationFailedStartRecoveryAuthoring.Request :=
    ⟨← bytes j "originalBeginHex", ← bytes j "originalClaimHex", ← bytes j "signedReportHex"⟩
  let encoded := ApplicationFailedStartRecoveryAuthoring.requestCodec.encode request
  let _ ← ApplicationFailedStartRecoveryInspection.inspectRequest encoded
  return encoded

end Minidregg.Host.ApplicationFailedStartRecoveryTools
