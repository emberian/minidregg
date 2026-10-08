import Kernel.ObjectiveActivityReceiver

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityReceiver
open Minidregg.Theory.TypedAuthorization

private def check (name : String) (cause : Reject) (bound : Nat) : IO Unit := do
  let bytes := rejectCodec.encode cause
  unless bytes.length < bound do
    throw (IO.userError s!"{name}: {bytes.length} bytes exceeds bound {bound}")
  let some decoded := rejectCodec.decode bytes
    | throw (IO.userError s!"{name}: decode refused")
  unless reprStr decoded == reprStr cause do
    throw (IO.userError s!"{name}: typed cause changed")
  unless rejectCodec.decode ("DREGG/OBJECTIVE/ACTIVITY/REJECT/v1".toUTF8.toList ++ bytes) |>.isNone do
    throw (IO.userError s!"{name}: old codec edition loaded")
  let source : StableEvent := ⟨1, ⟨1⟩, ⟨2⟩, [1, 2, 3]⟩
  let stored := failedEvent source cause
  let some (recovered, disposition) := recordedDisposition stored
    | throw (IO.userError s!"{name}: recorded disposition refused")
  unless recovered == source do
    throw (IO.userError s!"{name}: original ingress event changed")
  match disposition with
  | .confirmed => throw (IO.userError s!"{name}: charged disposition became confirmed")
  | .charged terminal =>
      unless reprStr terminal == reprStr cause do
        throw (IO.userError s!"{name}: recorded cause changed")
  IO.println s!"PASS {name}: rejectBytes={bytes.length} recordBytes={stored.canonicalBytes.length}"

def main : IO Unit := do
  let originalLeaf : LawLeaf :=
    ⟨[2], .anyL (.cons (.eq "request/subject" 7) .nil), none, none⟩
  IO.println s!"c6-law-serialized-bytes={(LawLeaf.stream.encode originalLeaf).length}"
  check "c6-no-grant" (.call
    (.extractionAccount (.lawDenied 11 "deposit" (.lawDenied originalLeaf)) 3199929 71)
    ⟨17476, 87088, 0, 0⟩) 1000
  let text := String.ofList (List.replicate 2048 'x')
  let leaf : LawLeaf := ⟨[0, 1, 2], .eq text 7, some 6, some 7⟩
  let conflict := (List.range 64).foldl
    (fun reason _ => ObjectRecord.WriteRefusal.upgradeConflict reason) (.lawDenied leaf)
  let terminal := ObjectiveCall.CallRefusal.lawDenied 11 text conflict
  let accounted := (List.range 64).foldl
    (fun reason n => ObjectiveCall.CallRefusal.extractionAccount reason (1000 + n) n) terminal
  check "long-law-and-recursive-accounts" (.call accounted ⟨100, 200, 300, 400⟩) 20000
  check "list-of-long-field-names" (.kernel (.fieldsForgotten [text, text, text])) 20000
  check "long-signature-footprint" (.signature (.footprintStale (List.replicate 4096 255))) 10000
  check "long-process-detail" (.signature (.envelope (.nativeVerify (.processFailed 42 text)))) 10000
  check "domain-law" (.kernel (.domainLawDenied ⟨42⟩ leaf)) 10000
