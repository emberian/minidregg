import Kernel.FnReplyPublication
import Kernel.FnPortableSource

open Minidregg.Kernel.FnConsumerOperation
open Minidregg.Kernel.FnReplyPublication
open Minidregg.Compiler

def require (ok : Bool) (detail : String) : IO Unit :=
  unless ok do throw (IO.userError detail)

/-- Read-only original-consumer correlation. Native fn must first verify the
carrier and export the exact source/keyset; this program does not verify
cryptography or assert a durable A-side application transition. -/
def main (args : List String) : IO Unit := do
  let [planPath, signedPath, replyPath, rSourcePath, rIdentityPath, aSourcePath] := args
    | throw (IO.userError
        "usage: check_a_reply.lean PLAN SIGNED Q.bin R.source R-IDENTITY.bin A-Q.source")
  let some plan := preparedCodec.decode (← IO.FS.readBinFile planPath).toList
    | throw (IO.userError "noncanonical prepared Mini Q")
  require plan.valid "invalid durable prepared Mini Q"
  let some signed := signedCodec.decode (← IO.FS.readBinFile signedPath).toList
    | throw (IO.userError "noncanonical signed Mini Q")
  require signed.valid "invalid durable signed Mini Q"
  require (signed.prepared == plan) "signed slot differs from prepared plan"
  let qBytes := (← IO.FS.readBinFile replyPath).toList
  let some q := replyCodec.decode qBytes
    | throw (IO.userError "noncanonical application Q")
  require (plan.selection.reply == q) "A's Q differs from Mini's retained Q"
  let rSource := (← IO.FS.readBinFile rSourcePath).toList
  let .ok r := Minidregg.Kernel.FnPortableSource.extract rSource
    | throw (IO.userError "R is not a bounded application source")
  let rIdentity := (← IO.FS.readBinFile rIdentityPath).toList
  require (rIdentity.length == 48) "R native identity width differs"
  require (q.sourceIdentity == rIdentity &&
           plan.selection.parentSourceIdentity == rIdentity)
    "Q does not bind exact R source identity"
  require (plan.selection.parentMessageId == r.messageId.toUTF8.toList)
    "Q does not bind R's exact Message-ID"
  let aSource := (← IO.FS.readBinFile aSourcePath).toList
  require (aSource == plan.source)
    "A's independently native-verified Q source differs from Mini's durable plan"
  require ((← IO.ofExcept plan.selection.source) == aSource)
    "A's Q source differs from the source-owned constructor"
  IO.println s!"PASS A Q correlation: {r.messageId} -> {plan.selection.messageId}"
