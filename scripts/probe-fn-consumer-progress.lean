/-
Pure selector and replay probe for Mini's typed empty-page progress. The
synthetic signed record is not an admitted receiver record; native admission
and the actual fn local poll are separate end-to-end obligations.
-/
import Kernel.FnConsumerProgress

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.FnConsumerProgress

set_option autoImplicit false

private def require (ok : Bool) (message : String) : IO Unit := do
  unless ok do throw (IO.userError message)

def main : IO Unit := do
  let domain : Digest := ⟨8501⟩
  let semantics : Digest := ⟨6⟩
  let scope : Scope := ⟨[1], [2], [3], [4], [5], 1, 1, 1⟩
  let evidence : Evidence := ⟨[17], scope, [102, 110, 99, 117],
    0, 16, [8], true⟩
  let report : Report := ⟨evidence, ⟨7⟩, 600, ⟨61⟩, ⟨11⟩, ⟨12⟩⟩
  let pin : FnGatewayPolicy.Pin := ⟨[17], ⟨7⟩, 600, ⟨61⟩, ⟨99⟩⟩
  let policy : FnConsumerOperation.Policy := ⟨[17], ⟨7⟩, 600, ⟨61⟩⟩
  let .ok () := checkReport pin policy report
    | throw (IO.userError "advancing observed empty page was refused")
  require (match decide pin scope domain semantics report [] with
    | .fresh _ => true | _ => false)
    "empty page did not propose a progress-only command"
  let command := progressCommand domain semantics report
  let signed : DeclaredResourceController.SignedCommand :=
    ⟨DeclaredResourceController.commandCodec.encode command, [], [], []⟩
  let event := DeclaredResourceController.invocationEvent domain semantics command signed
  let record : DurableReceiver.IntentRecord :=
    ⟨marker domain semantics report.subject evidence, [], [], [],
      fun _ => 0, event⟩
  require (originalSkip pin scope domain semantics record == some evidence)
    "historical selector lost exact signed progress record"
  let [target] := command.targets
    | throw (IO.userError "progress command did not have one target")
  let nonProgress := { command with targets := [{ target with kind := .account }] }
  let nonProgressSigned : DeclaredResourceController.SignedCommand :=
    { signed with commandBytes := DeclaredResourceController.commandCodec.encode nonProgress }
  let nonProgressRecord := { record with
    event := DeclaredResourceController.invocationEvent domain semantics
      nonProgress nonProgressSigned }
  require ((originalSkip pin scope domain semantics nonProgressRecord).isNone)
    "historical selector treated a non-progress target kind as an empty-page skip"
  require (match decide pin scope domain semantics report [record] with
    | .repeated => true | _ => false)
    "exact progress retry proposed a second write"
  require ((originalSkip { pin with subject := ⟨8⟩ } scope domain semantics record).isNone)
    "historical selector accepted another gateway subject"
  require ((originalSkip pin { scope with query := [6] } domain semantics record).isNone)
    "historical selector accepted another fn consumer scope"
  require (!{ evidence with toPosition := 17 }.valid)
    "skip crossed the selected 16-event scan window"
  require (!{ evidence with toPosition := 0 }.valid)
    "idle cursor became a progress record"
  IO.println "PASS fn empty-page progress selector, exact retry, pin and scan window"

#eval main
