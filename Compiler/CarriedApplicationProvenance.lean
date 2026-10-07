/-
Historical event22 provenance for an explicitly authorized carried custody.
Old native admission is supplied by the retained capsule audit, never recreated
under the target profile. Only the stable outer share carrier is decoded here;
its grain birth bytes and old descriptor remain opaque. The original receipt's root
is read from the source Store at use (`AuditedSource.reader`), never by replaying the
source history from its genesis.
-/
import Compiler.CarriedSegmentIO
import Kernel.ApplicationShareIssueGrainReceiver

namespace Minidregg.Compiler.CarriedApplicationProvenance

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

/-- The constructor needs a receiver-minted preserved-custody token. A bare
record, claimed audit, receipt, or target-profile issue cannot mint this value. -/
structure CarriedIssue (config : Config) (current : Durable) where
  private mk ::
  custody : CarriedSegmentIO.PreservedPrefix config current
  index : Nat
  beforeCut : index < custody.edge.body.cut.height
  record : DurableReceiver.IntentRecord
  sourcePresent : custody.source.durable.image.accepted[index]? = some record
  currentPresent : current.image.accepted[index]? = some record
  ingress : ApplicationShareIssueGrainSource.Ingress
  decoded : ApplicationShareIssueGrainSource.codec.decode record.event.canonicalBytes =
    some ingress
  eventExact : record.event =
    ApplicationShareIssueGrainReceiver.event custody.source.capsule.identity.domain ingress
  /-- The source Store this issue was read from, under its own key and log start. -/
  store : DurableHistory.StoreIdentity
  head : DurableHistory.Head store
  /-- The record at the issue's height in the source Store, verified at use against the
  source Store's MAC-bound head: it carries the root the source Host served there. -/
  original : DurableHistoryReader.Record head (index + 1)
  originalExact : original.record = record

/-- The original receipt: the OLD source Store's height and the root its Host served
after this record (carried by the record's verified entry). The carry start's root and
the target profile never replace this receipt. -/
def CarriedIssue.receipt {config : Config} {current : Durable}
    (issue : CarriedIssue config current) : NativeHostCodec.Receipt :=
  ⟨issue.record.transactionId, issue.record.event.eventId, issue.index + 1,
    issue.original.verified.root⟩

def CarriedIssue.spec {config : Config} {current : Durable}
    (issue : CarriedIssue config current) : ApplicationShareIssueSource.Spec :=
  issue.ingress.spec

private theorem current_record_exact (current : Durable) (index : Nat)
    (record : DurableReceiver.IntentRecord)
    (bytes : (current.image.accepted[index]?.map DurableReceiverCodec.intentStream.encode) =
      some (DurableReceiverCodec.intentStream.encode record)) :
    current.image.accepted[index]? = some record := by
  cases found : current.image.accepted[index]? with
  | none => simp [found] at bytes
  | some selected =>
      simp only [found, Option.map_some, Option.some.injEq] at bytes
      have exact := (lawful_encode_injective
        DurableReceiverCodec.intentStream.toLawful) bytes
      simpa only [found, Option.some.injEq] using exact

/-- Select by absolute original index, checking exact retained membership on
both sides. No decoding of the opaque old grain birth is attempted. -/
def selectIssue {config : Config} {current : Durable}
    (custody : CarriedSegmentIO.PreservedPrefix config current) (index : Nat) :
    IO (Except String (CarriedIssue config current)) := do
  if beforeCut : index < custody.edge.body.cut.height then
    match sourcePresent : custody.source.durable.image.accepted[index]? with
    | none => return .error "carried original issue index absent"
    | some record =>
      match decoded : ApplicationShareIssueGrainSource.codec.decode record.event.canonicalBytes with
      | none => return .error "carried original is not a canonical outer grain issue"
      | some ingress =>
        if eventExact : record.event =
            ApplicationShareIssueGrainReceiver.event custody.source.capsule.identity.domain ingress then
          if bytes : (current.image.accepted[index]?.map DurableReceiverCodec.intentStream.encode) =
              some (DurableReceiverCodec.intentStream.encode record) then
            match ← custody.source.reader with
            | .error detail => return .error s!"carried source history: {detail}"
            | .ok ⟨store, reader⟩ =>
              match ← reader.atHeight (index + 1) with
              | .error refusal => return .error refusal.message
              | .ok original =>
                if sameBytes : DurableReceiverCodec.intentStream.encode original.record =
                    DurableReceiverCodec.intentStream.encode record then
                  have originalExact : original.record = record :=
                    lawful_encode_injective DurableReceiverCodec.intentStream.toLawful sameBytes
                  return .ok ⟨custody, index, beforeCut, record, sourcePresent,
                    current_record_exact current index record bytes, ingress, decoded,
                    eventExact, store, reader.head, original, originalExact⟩
                else return .error "carried original issue differs from the source Store's verified record"
          else return .error "carried original issue record differs from current preserved custody"
        else return .error "carried original event22 identity differs"
  else return .error "carried issue index is not before the original cut"

/-- **The original receipt's root is read, verified, from the source Store**: it is the root
carried by a record of the source Store at the issue's height whose inclusion was verified
against the source Store's MAC-bound head, and that record is the selected issue record. -/
theorem CarriedIssue.receipt_root_verified {config : Config} {current : Durable}
    (issue : CarriedIssue config current) :
    ∃ read : DurableHistoryReader.Record issue.head (issue.index + 1),
      read.record = issue.record ∧ issue.receipt.worldRoot = read.verified.root :=
  ⟨issue.original, issue.originalExact, rfl⟩

#assert_axioms CarriedIssue.receipt_root_verified

theorem CarriedIssue.original_receipt_height {config : Config} {current : Durable}
    (issue : CarriedIssue config current) :
    issue.receipt.acceptedCount = issue.index + 1 := rfl

theorem CarriedIssue.original_event22 {config : Config} {current : Durable}
    (issue : CarriedIssue config current) : issue.record.event.codecVersion = 22 := by
  rw [issue.eventExact]
  rfl

theorem CarriedIssue.current_record_exact {config : Config} {current : Durable}
    (issue : CarriedIssue config current) :
    current.image.accepted[issue.index]? = some issue.record := issue.currentPresent

end Minidregg.Compiler.CarriedApplicationProvenance
