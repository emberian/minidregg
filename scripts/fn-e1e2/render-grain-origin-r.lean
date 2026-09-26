/-
Render a fresh fn R source from an accepted Mini grain publication. Mini's
existing export-evidence command first selects the exact accepted signed call;
this script independently re-admits its package, checks the named source
coordinates, and authors only the strict application MIME source. fn still
owns hybrid signing, Store admission, peering, and source identity.

Usage under the pinned Mini tree:
  lake env lean --run scripts/fn-e1e2/render-grain-origin-r.lean \
    HOST CONFIG.json PACKAGE.bin GRAIN-TASK PARENT-TASK PUBLICATION-TARGET GROUP RFC-DATE R.source
-/
import Kernel.FnPortableSource
import Kernel.AgentGrain
import Lean.Data.Json

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def cleanHeader (value : String) (max : Nat) : Bool :=
  !value.isEmpty && value.length ≤ max && value.toUTF8.data.toList.all
    (fun b => 32 ≤ b.toNat && b.toNat ≤ 126)

private def cleanGroup (value : String) : Bool :=
  cleanHeader value 128 && value.toList.all (fun c =>
    c.isAlphanum || c == '.' || c == '-' || c == '_')

private def alphabet : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

private def base64Line (bytes : ByteArray) (start stop : Nat) : String := Id.run do
  let mut chars : Array Char := #[]
  let mut i := start
  while i < stop do
    let a := bytes[i]!.toNat
    let b := if i + 1 < stop then bytes[i + 1]!.toNat else 0
    let c := if i + 2 < stop then bytes[i + 2]!.toNat else 0
    chars := chars.push alphabet[a / 4]!
    chars := chars.push alphabet[(a % 4) * 16 + b / 16]!
    chars := chars.push (if i + 1 < stop then alphabet[(b % 16) * 4 + c / 64]! else '=')
    chars := chars.push (if i + 2 < stop then alphabet[c % 64]! else '=')
    i := i + 3
  return String.ofList chars.toList

private def base64Lines (bytes : ByteArray) : String := Id.run do
  let mut lines : Array String := #[]
  let mut i := 0
  while i < bytes.size do
    let stop := min bytes.size (i + 57)
    lines := lines.push (base64Line bytes i stop)
    i := stop
  return String.intercalate "\r\n" lines.toList ++ "\r\n"

private def writePair (task field : Nat) : Minidregg.Theory.DeclaredActionLowering.Action →
    Option (Int × Int)
  | .write (.objectField resource fieldId) (some before) after =>
      if resource.value == task && fieldId.value == field then some (before, after) else none
  | _ => none

private def grainStates (task : Nat) (actions : List Minidregg.Theory.DeclaredActionLowering.Action) :
    Option (AgentGrain.State × AgentGrain.State) := do
  let [a, b, c, d] := actions | none
  let p0 ← writePair task 0 a
  let p1 ← writePair task 1 b
  let p2 ← writePair task 2 c
  let p3 ← writePair task 3 d
  return (⟨p0.1, p1.1, p2.1, p3.1⟩, ⟨p0.2, p1.2, p2.2, p3.2⟩)

def main (args : List String) : IO Unit := do
  let [hostPath, configPath, packagePath, grainText, parentText,
       targetText, group, date, outputPath] := args
    | throw (IO.userError
        "usage: render-grain-origin-r.lean HOST CONFIG.json PACKAGE.bin GRAIN-TASK PARENT-TASK PUBLICATION-TARGET GROUP RFC-DATE R.source")
  let some grainTask := grainText.toNat?
    | throw (IO.userError "grain task must be decimal")
  let some parentTask := parentText.toNat?
    | throw (IO.userError "parent task must be decimal")
  let some publicationTarget := targetText.toNat?
    | throw (IO.userError "publication target must be decimal")
  require (grainTask != parentTask && grainTask != publicationTarget &&
    parentTask != publicationTarget) "grain, parent, and publication targets must be distinct"
  require (cleanGroup group) "fn group is outside the single-group source profile"
  require (cleanHeader date 128) "RFC Date header is empty, oversized, or non-ASCII"
  let output := System.FilePath.mk outputPath
  require (!(← output.pathExists)) "refusing to replace an existing R source"
  let verificationPath := outputPath ++ ".verified.json"
  require (!(← (System.FilePath.mk verificationPath).pathExists))
    "refusing to replace an existing Mini verification result"
  let packageBytes := (← IO.FS.readBinFile packagePath).toList
  let .ok package := FnEvidenceCodec.decodeChecked packageBytes
    | throw (IO.userError "Mini evidence package is noncanonical or exceeds its profile")
  let result ← IO.Process.output { cmd := hostPath, args := #[configPath, "verify-evidence", packagePath, verificationPath] }
  require (result.exitCode == 0) "Mini host did not re-admit the original accepted package"
  let receipt := package.originalReceipt
  let verification ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile verificationPath))
  require (verification.getObjValAs? String "type" == .ok "verified-mini-native-prefix-v1" &&
    verification.getObjValAs? String "transactionId" == .ok (toString receipt.transactionId.value) &&
    verification.getObjValAs? String "eventId" == .ok (toString receipt.eventId.value) &&
    verification.getObjValAs? String "acceptedCount" == .ok (toString receipt.acceptedCount))
    "Mini verification result differs from package receipt"
  let some (.invoke signed) := callCodec.decode package.signedCall
    | throw (IO.userError "origin evidence is not an ordinary signed resource invocation")
  let some command := DeclaredResourceController.commandCodec.decode signed.commandBytes
    | throw (IO.userError "origin signed command is noncanonical")
  let grainTarget :: witness :: publications := command.targets
    | throw (IO.userError "origin command has no grain, parent witness, and publication legs")
  require (grainTarget.kind == .object && grainTarget.target == grainTask)
    "original call does not lead with the named grain task"
  let some (.scalar grainActions) := some grainTarget.payload
    | throw (IO.userError "origin grain leg is not scalar")
  let some (grainBefore, grainAfter) := grainStates grainTask grainActions
    | throw (IO.userError "origin grain leg is not the four-coordinate AgentGrain shape")
  let charge := grainBefore.remaining + grainBefore.reserved - grainAfter.remaining
  require ((grainBefore.status == 3 || grainBefore.status == 4) &&
    decide (0 ≤ charge) && decide (charge ≤ grainBefore.reserved) &&
    decide (grainAfter = AgentGrain.settle grainBefore charge) &&
    AgentGrain.accepts grainBefore grainAfter)
    "origin grain leg is not an admitted reserved-to-settled transition"
  require (witness.kind == .object && witness.target == parentTask)
    "origin call has no named parent witness in its second leg"
  let some (.scalar witnessActions) := some witness.payload
    | throw (IO.userError "origin parent witness is not scalar")
  let some (parentBefore, parentAfter) := grainStates parentTask witnessActions
    | throw (IO.userError "origin parent witness is not the four-coordinate shape")
  require (decide (parentBefore = parentAfter) &&
    (parentBefore.status == 3 || parentBefore.status == 4))
    "origin parent witness did not preserve a reserved prompt"
  require (publications.any (fun t => t.kind == .object &&
    t.target == publicationTarget && match t.payload with
      | .scalar actions => !actions.isEmpty
      | .content command => !command.actions.isEmpty))
    "original call has no authored publication to the named resource"
  let messageId := s!"<mini-grain-{receipt.transactionId.value}-{receipt.eventId.value}@mini.invalid>"
  require (messageId.length ≤ 256) "derived Message-ID exceeds Mini source profile"
  let source := "From: mini-grain@example.invalid\r\n" ++
    "Date: " ++ date ++ "\r\n" ++
    "Newsgroups: " ++ group ++ "\r\n" ++
    "Subject: Mini AgentGrain publication\r\n" ++
    "Message-ID: " ++ messageId ++ "\r\n" ++
    "Content-Type: application/vnd.dregg.fn-native-prefix; version=1\r\n" ++
    "Content-Transfer-Encoding: base64\r\n\r\n" ++
    base64Lines packageBytes.toByteArray
  let .ok extracted := FnPortableSource.extract source.toUTF8.toList
    | throw (IO.userError "authored fn source fails Mini's strict source parser")
  require (extracted.package.toByteArray == packageBytes.toByteArray &&
    extracted.messageId == messageId &&
    extracted.groups == group) "authored source does not round-trip its exact package"
  IO.FS.writeBinFile output source.toUTF8
  IO.println s!"R source: {messageId}; Mini accepted={receipt.acceptedCount}; publication target={publicationTarget}"
