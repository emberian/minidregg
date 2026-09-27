/-
Pure historical selector probe for A's own-R article progress. Synthetic
records here do not establish physical fn polling or Mini receiver admission;
a separate fresh native A/fn gate must cover those obligations.
-/
import Kernel.FnCatalogOwnRProgress

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.FnCatalogOwnRProgress

set_option autoImplicit false

private def require (condition : Bool) (reason : String) : IO Unit := do
  unless condition do throw (IO.userError reason)

private def recordFor (domain semantics : Digest)
    (command : DeclaredResourceController.Command) (transaction : Digest) :
    DurableReceiver.IntentRecord :=
  let signed : DeclaredResourceController.SignedCommand :=
    ⟨DeclaredResourceController.commandCodec.encode command, [], [], []⟩
  ⟨transaction, [], [], [], fun _ => 0,
    DeclaredResourceController.invocationEvent domain semantics command signed⟩

def main : IO Unit := do
  let domain : Digest := ⟨8501⟩
  let semantics : Digest := ⟨6⟩
  let scope : FnConsumerProgress.Scope := ⟨[1], [2], [3], [4], [5], 1, 1, 1⟩
  let pin : FnGatewayPolicy.Pin := ⟨[17], ⟨7⟩, 600, ⟨61⟩, ⟨99⟩⟩
  let policy : FnConsumerOperation.Policy := ⟨[17], ⟨7⟩, 600, ⟨61⟩⟩
  let sourceId := List.replicate 48 (17 : UInt8)
  let principal := List.replicate 32 (18 : UInt8)
  let ed := List.replicate 32 (19 : UInt8)
  let ml := List.replicate 1952 (20 : UInt8)
  let prepared : FnOriginOutbox.Prepared :=
    ⟨[17], [21], "<r>".toUTF8.toList, sourceId, [30], ⟨1⟩, ⟨2⟩,
      ⟨⟨3⟩, ⟨4⟩, 1, ⟨5⟩⟩, principal, ed, ml⟩
  let outboxReport : FnOriginOutbox.Report :=
    ⟨prepared, [], ⟨7⟩, 600, ⟨61⟩, ⟨11⟩, ⟨12⟩, true, true⟩
  let outbox := recordFor domain semantics
    (FnOriginOutbox.outboxCommand domain semantics outboxReport)
    (FnOriginOutbox.marker domain semantics ⟨7⟩ prepared)
  let portable : FnConsumerOperation.PortableInbox :=
    ⟨[31], sourceId, principal, ed, ml⟩
  let poll : FnConsumerOperation.StorePollInbox :=
    ⟨[32], [33], true, sourceId, 3, 4, "<r>".toUTF8.toList,
      principal, [34], [35]⟩
  let evidence : Evidence :=
    ⟨[17], scope, 0, 4, outbox.transactionId, portable, poll⟩
  let report : Report := ⟨evidence, ⟨7⟩, 600, ⟨61⟩, ⟨13⟩, ⟨14⟩⟩
  let .ok () := checkReport pin policy scope domain semantics [outbox] report
    | throw (IO.userError "matching accepted own R was refused")
  let .fresh _ := decide pin scope domain semantics report [outbox]
    | throw (IO.userError "own R did not propose fresh progress")
  let progress := recordFor domain semantics
    (progressCommand domain semantics report)
    (marker domain semantics report.subject evidence)
  require ((originalOwnR pin scope domain semantics progress
    [outbox, progress]).isSome) "complete own-R signed progress was not recognized"
  require (match decide pin scope domain semantics report [outbox, progress] with
    | .repeated => true | _ => false) "exact retry proposed another write"
  require ((originalOwnR { pin with subject := ⟨8⟩ } scope domain semantics
    progress [outbox, progress]).isNone) "foreign gateway recognized own-R progress"
  require ((originalOwnR pin { scope with query := [6] } domain semantics
    progress [outbox, progress]).isNone) "foreign scope recognized own-R progress"
  require ((originalOwnR pin scope domain semantics progress [progress]).isNone)
    "own-R progress survived loss of its accepted outbox"
  let command := progressCommand domain semantics report
  let [target] := command.targets
    | throw (IO.userError "own-R command has unexpected target count")
  let wrongKind := { command with targets := [{ target with kind := .account }] }
  let foreign := recordFor domain semantics wrongKind progress.transactionId
  require ((originalOwnR pin scope domain semantics foreign
    [outbox, foreign]).isNone) "non-object target recognized as own-R progress"
  let oldEvidence : FnConsumerProgress.Evidence :=
    ⟨[17], scope, [32], 0, 4, [35], true⟩
  let oldReport : FnConsumerProgress.Report :=
    ⟨oldEvidence, ⟨7⟩, 600, ⟨61⟩, ⟨13⟩, ⟨14⟩⟩
  let old := recordFor domain semantics
    (FnConsumerProgress.progressCommand domain semantics oldReport)
    (FnConsumerProgress.marker domain semantics ⟨7⟩ oldEvidence)
  require ((originalOwnR pin scope domain semantics old [outbox, old]).isNone)
    "legacy empty-page tag-9 record was reinterpreted as own-R article"
  require ((FnConsumerProgress.originalSkip pin scope domain semantics progress).isNone)
    "own-R article was reinterpreted as empty-page progress"
  require (!{ evidence with toPosition := 17 }.valid)
    "own-R cursor crossed qualified sixteen-event scan bound"
  IO.println "PASS own-R distinct tag-9 selector, outbox, pin, scope, exact retry, and scan bound"

#eval main
