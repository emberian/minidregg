/-
Receipt-only lookup for grain-backed share issue event 22, on the light opening's
history Reader: the original re-admitted at its own selected prefix, exact source bytes
and full IntentRecord equality, never event-shaped journal bytes alone.
-/
module

public import Kernel.ApplicationShareIssueGrainReceiver
public import Kernel.NativeHostReplay

@[expose] public section

namespace Minidregg.Kernel.ApplicationShareIssueGrainLookup

open Minidregg.Compiler
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

inductive Error where
  | malformed
  | transactionConflict
  | nativeHistoryUnavailable
  /-- The Store's history could not be read or verified for the issue (law 10: a read failure
  names itself, never a conflict); `detail` is the Reader's refusal, naming the height. -/
  | historyRefused (detail : String)
  deriving DecidableEq, Repr

/-- **Receipt-only lookup through the Store's history.** The issue's transaction id is read by
the Reader; its record (the record at that height) is the original issue only when the issue
re-admitted at its own prefix (`NativeHostReplay.selectIssue`: native admission on the state
before it, complete `IntentRecord` equality) has exactly these ingress bytes; its receipt is that
record's. A transaction recorded with any other original is a conflict; event-shaped journal
bytes alone never answer. -/
def lookupLight (config : Config) {store : DurableHistory.StoreIdentity}
    (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store)
    (pins : Minidregg.Theory.ResourceBirth.FactoryPins) (bytes : List UInt8) :
    IO (Except Error (Option NativeHostCodec.Receipt)) := do
  let some ingress := ApplicationShareIssueGrainSource.codec.decode bytes
    | return .error .malformed
  let some grain := ingress.decodeGrain
    | return .error .malformed
  let transactionId := grain.source.birth.transactionId
  match ← reader.byTx transactionId with
  | .error refusal => return .error (.historyRefused refusal.message)
  | .ok (.absent _) => return .ok none
  | .ok (.present found) =>
      if found.height = 0 then return .error .nativeHistoryUnavailable
      let index := found.height - 1
      match ← NativeHostReplay.selectIssue config reader pins reader.head.height index with
      | .error (.history detail) => return .error (.historyRefused detail)
      | .error (.refused _) => return .error .transactionConflict
      | .ok issue =>
          let receipt := issue.receipt
          if issue.evidence.ingressBytes == bytes &&
              issue.candidate.record.event.codecVersion == 22 &&
              receipt.transactionId == transactionId &&
              receipt.acceptedCount == found.height then
            return .ok (some receipt)
          else return .error .transactionConflict

end Minidregg.Kernel.ApplicationShareIssueGrainLookup
