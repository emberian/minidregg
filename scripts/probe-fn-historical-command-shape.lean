/-
Pure historical selector probe. Records below are synthetic signed envelopes,
not receiver-admitted events; the native end-to-end run separately exercises
the exact accepted B and A commands. This checks selector shape only.
-/
import Kernel.FnConsumerOperation

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.FnConsumerOperation

set_option autoImplicit false

private def require (condition : Bool) (detail : String) : IO Unit := do
  unless condition do throw (IO.userError detail)

private def syntheticRecord (domain semantics : Digest)
    (command : DeclaredResourceController.Command) : DurableReceiver.IntentRecord :=
  let signed : DeclaredResourceController.SignedCommand :=
    ⟨DeclaredResourceController.commandCodec.encode command, [], [], []⟩
  ⟨marker domain semantics command.subject command.nonce, [], [], [],
    fun _ => 0, DeclaredResourceController.invocationEvent domain semantics command signed⟩

private def changedTarget (command : DeclaredResourceController.Command)
    (change : DeclaredResourceController.Target → DeclaredResourceController.Target) :
    Option DeclaredResourceController.Command := do
  let [target] := command.targets | none
  some { command with targets := [change target] }

def historicalShapeProbe : IO Unit := do
  let domain : Digest := ⟨8501⟩
  let semantics : Digest := ⟨6⟩
  let receipt : NativeHostCodec.Receipt := ⟨⟨101⟩, ⟨102⟩, 2, ⟨103⟩⟩
  let report : Report :=
    { application := [17], operation := [18],
      provenance := ⟨[19], [20], [21], [22]⟩,
      package := [23], subject := ⟨7⟩, target := 600,
      capability := ⟨61⟩, expectedAuthorityRoot := ⟨11⟩,
      expectedTargetRoot := ⟨12⟩ }
  let pin : FnGatewayPolicy.Pin := ⟨[17], ⟨7⟩, 600, ⟨61⟩, ⟨99⟩⟩
  let .ok binding := bindingCommand domain semantics report receipt
    | throw (IO.userError "binding constructor refused small probe")
  let bindingRecord := syntheticRecord domain semantics binding
  require ((originalBindingWithInbox pin domain semantics bindingRecord).isSome)
    "canonical historical binding was lost"
  let conflict := conflictCommand domain semantics report
  let conflictRecord := syntheticRecord domain semantics conflict
  require ((originalConflictWithInbox pin domain semantics conflictRecord).isSome)
    "canonical historical conflict was lost"
  let changes : List (String × (DeclaredResourceController.Target →
      DeclaredResourceController.Target)) :=
      [("kind", fun target => { target with kind := .account }),
       ("schema", fun target => { target with schemaVersion := 2 }),
       ("observe", fun target => { target with observeCapability := some ⟨9⟩ })]
  for (name, change) in changes do
    let some badBinding := changedTarget binding change
      | throw (IO.userError "binding target was absent")
    let some badConflict := changedTarget conflict change
      | throw (IO.userError "conflict target was absent")
    require ((originalBindingWithInbox pin domain semantics
      (syntheticRecord domain semantics badBinding)).isNone)
      s!"historical binding accepted altered target {name}"
    require ((originalConflictWithInbox pin domain semantics
      (syntheticRecord domain semantics badConflict)).isNone)
      s!"historical conflict accepted altered target {name}"
  IO.println "PASS exact historical consumer binding/conflict command shape"

#eval historicalShapeProbe
