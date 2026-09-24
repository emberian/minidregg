import Kernel.FnReplyConsumption

open Minidregg.Kernel
open Minidregg.Kernel.FnReplyConsumption

def require (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)

def refused (result : Except String Result) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

def main (args : List String) : IO Unit := do
  let [sourcePath] := args
    | throw (IO.userError "usage: check_reply_consumption.lean Q-SOURCE")
  let source := (← IO.FS.readBinFile sourcePath).toList
  let parsed ← IO.ofExcept (FnReplySource.extract source)
  let qSourceId : List UInt8 := List.replicate 48 17
  let qPrincipal : List UInt8 := List.replicate 32 18
  let application := parsed.reply.application
  let operation := parsed.reply.operation
  let poll : FnConsumerOperation.StorePollInbox :=
    ⟨[1], [2], true, qSourceId, 7, 5,
      parsed.messageId.toUTF8.toList, qPrincipal, [3], [4]⟩
  let policy : Policy := ⟨application, ⟨23⟩, 42, ⟨11⟩⟩
  let report : Report :=
    ⟨application, operation, parsed.reply.sourceIdentity,
      parsed.parentMessageId.toUTF8.toList, parsed.reply.miniReceipt,
      source, qSourceId, parsed.messageId.toUTF8.toList,
      ⟨[5], qSourceId, qPrincipal, List.replicate 32 6,
        List.replicate 1952 7⟩, poll,
      policy.subject, policy.target, policy.capability, ⟨0⟩, ⟨0⟩⟩
  let result ← IO.ofExcept (check policy report)
  require (result.reply == parsed.reply) "Q result changed decoded Mini reply"
  let some decoded := reportCodec.decode (reportCodec.encode report)
    | throw (IO.userError "A reply inbox codec did not decode")
  require (reportCodec.encode decoded == reportCodec.encode report)
    "A reply inbox codec is not canonical"
  let .fresh command _ := evaluate ⟨1⟩ ⟨2⟩ policy report []
    | throw (IO.userError "valid A Q report did not prepare fresh result")
  require (command.nonce == resultNonce ⟨1⟩ ⟨2⟩ application operation)
    "A Q command did not use the source-independent operation marker"
  let newAuthorityRoot := { report with expectedAuthorityRoot := ⟨123⟩ }
  let newRoots := { newAuthorityRoot with expectedTargetRoot := ⟨456⟩ }
  require (report.evidenceBytes == newRoots.evidenceBytes &&
      conflictNonce ⟨1⟩ ⟨2⟩ report == conflictNonce ⟨1⟩ ⟨2⟩ newRoots)
    "current CAS roots changed A reply evidence identity"
  let unobservedPoll : FnConsumerOperation.StorePollInbox :=
    { poll with pollCallObserved := false, controlBinding := [] }
  let noPoll := { report with storePoll := unobservedPoll }
  require (refused (check policy noPoll)) "unobserved Q poll was accepted"
  let changedParent := { report with parentSourceIdentity := List.replicate 48 9 }
  require (refused (check policy changedParent)) "changed R source identity was accepted"
  let changedOperation := { report with operation := "other".toUTF8.toList }
  require (refused (check policy changedOperation)) "changed operation was accepted"
  let alteredSource := { report with
    replySource := (String.fromUTF8! source.toByteArray).replace
      "Date: Wed" "Date: Thu" |>.toUTF8.toList }
  require (refused (check policy alteredSource)) "altered exact Q source was accepted"
  IO.println "A reply source, correlation, native-poll guard, and codec PASS"
