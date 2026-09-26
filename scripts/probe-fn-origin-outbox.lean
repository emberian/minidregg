/-
Pure prepared-R outbox selector and conflict probe. The carrier is synthetic;
the native verifier, Mini historical replay, and receiver admission remain
separate live-path obligations.
-/
import Kernel.FnOriginOutbox

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.FnOriginOutbox

set_option autoImplicit false

private def require (condition : Bool) (detail : String) : IO Unit := do
  unless condition do throw (IO.userError detail)

def originOutboxProbe : IO Unit := do
  let domain : Digest := ⟨8501⟩
  let semantics : Digest := ⟨6⟩
  let receipt : NativeHostCodec.Receipt := ⟨⟨101⟩, ⟨102⟩, 2, ⟨103⟩⟩
  let package : FnEvidenceCodec.Package :=
    ⟨domain, semantics, ⟨104⟩, [1], receipt, [2]⟩
  let packageBytes ← IO.ofExcept (FnEvidenceCodec.encodeChecked package)
  let prepared : Prepared :=
    ⟨[17], FnConsumerOperation.originOperation package,
      "<r@x>".toUTF8.toList, List.replicate 48 3, [4],
      packageIdentity packageBytes, callIdentity package.signedCall,
      receipt, List.replicate 32 5, List.replicate 32 6,
      List.replicate 1952 7⟩
  let report : Report :=
    ⟨prepared, packageBytes, ⟨7⟩, 600, ⟨61⟩, ⟨11⟩, ⟨12⟩, true, true⟩
  let pin : FnGatewayPolicy.Pin := ⟨[17], ⟨7⟩, 600, ⟨61⟩, ⟨99⟩⟩
  let policy : FnConsumerOperation.Policy := ⟨[17], ⟨7⟩, 600, ⟨61⟩⟩
  let .ok () := checkReport pin policy report
    | throw (IO.userError "small prepared R report was refused")
  require (match decide pin domain semantics report [] with
    | .fresh _ => true | _ => false)
    "fresh prepared R did not propose one gateway command"
  let command := outboxCommand domain semantics report
  let signed : DeclaredResourceController.SignedCommand :=
    ⟨DeclaredResourceController.commandCodec.encode command, [], [], []⟩
  let record : DurableReceiver.IntentRecord :=
    ⟨marker domain semantics report.subject prepared, [], [], [], fun _ => 0,
      DeclaredResourceController.invocationEvent domain semantics command signed⟩
  require (originalPrepared pin domain semantics record == some prepared)
    "historical prepared R did not reopen exactly"
  let .ok (selected, _) := selectUniqueParent pin domain semantics
      prepared.messageId [record]
    | throw (IO.userError "unique R parent lookup failed")
  require (FnConsumerOperation.sameBytes (preparedCodec.encode selected)
      (preparedCodec.encode prepared)) "unique parent lookup changed prepared R"
  let secondPackage : FnEvidenceCodec.Package :=
    { package with signedCall := [3] }
  let secondPackageBytes ← IO.ofExcept (FnEvidenceCodec.encodeChecked secondPackage)
  let secondOperation := FnConsumerOperation.originOperation secondPackage
  let secondPackageIdentity := packageIdentity secondPackageBytes
  let secondCallIdentity := callIdentity secondPackage.signedCall
  let secondPrepared : Prepared :=
    ⟨prepared.application, secondOperation, "<r2@x>".toUTF8.toList,
      prepared.sourceIdentity, [8], secondPackageIdentity,
      secondCallIdentity, prepared.originReceipt, prepared.principal,
      prepared.edPublicKey, prepared.mlPublicKey⟩
  let secondReport : Report :=
    { report with prepared := secondPrepared, package := secondPackageBytes }
  let .ok () := checkReport pin policy secondReport
    | throw (IO.userError "second prepared R report was refused")
  let secondCommand := outboxCommand domain semantics secondReport
  let secondSigned : DeclaredResourceController.SignedCommand :=
    ⟨DeclaredResourceController.commandCodec.encode secondCommand, [], [], []⟩
  let secondRecord : DurableReceiver.IntentRecord :=
    ⟨marker domain semantics secondReport.subject secondPrepared, [], [], [], fun _ => 0,
      DeclaredResourceController.invocationEvent domain semantics secondCommand secondSigned⟩
  let .ok (firstOfTwo, _) := selectUniqueParent pin domain semantics
      prepared.messageId [record, secondRecord]
    | throw (IO.userError "two-R catalog did not select first parent")
  let .ok (secondOfTwo, _) := selectUniqueParent pin domain semantics
      secondPrepared.messageId [record, secondRecord]
    | throw (IO.userError "two-R catalog did not select second parent")
  require (firstOfTwo == prepared && secondOfTwo == secondPrepared)
    "two-R catalog selected the wrong prepared origin"
  require (match decide pin domain semantics report [record] with
    | .repeated => true | _ => false)
    "exact prepared R retry proposed a second outbox write"
  let altered : Report := { report with prepared := { prepared with carrier := [9] } }
  require (match decide pin domain semantics altered [record] with
    | .refused _ => true | _ => false)
    "same Message-ID with changed carrier did not conflict"
  let [target] := command.targets
    | throw (IO.userError "outbox command had no target")
  let badCommand := { command with targets := [{ target with kind := .account }] }
  let badSigned : DeclaredResourceController.SignedCommand :=
    { signed with commandBytes := DeclaredResourceController.commandCodec.encode badCommand }
  let badRecord := { record with event :=
    DeclaredResourceController.invocationEvent domain semantics badCommand badSigned }
  require ((originalPrepared pin domain semantics badRecord).isNone)
    "historical selector accepted an altered resource kind"
  require (match selectUniqueParent pin domain semantics prepared.messageId
      [record, record] with
    | .error _ => true | .ok _ => false)
    "ambiguous parent lookup was accepted"
  IO.println "PASS prepared R exact reopen, two-parent selection, retry/conflict, altered shape"

#eval originOutboxProbe
