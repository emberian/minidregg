/-
Historical event22 provenance for an explicitly authorized carried prefix.
Old native admission is supplied by the retained capsule audit, never recreated
under the target profile. Only the stable outer share carrier is decoded here;
its grain birth bytes and old descriptor remain opaque.
-/
import Compiler.CarriedSegmentIO
import Kernel.ApplicationShareIssueGrainReceiver

namespace Minidregg.Compiler.CarriedApplicationProvenance

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

/-- The constructor needs a receiver-minted preserved-prefix token. A bare
record, claimed audit, receipt, or target-profile issue cannot mint this value. -/
structure CarriedIssue (config : Config) (current : Durable) where
  private mk ::
  prefix : CarriedSegmentIO.PreservedPrefix config current
  index : Nat
  beforeCut : index < prefix.edge.body.cut.height
  record : DurableReceiver.IntentRecord
  sourcePresent : prefix.source.durable.image.accepted[index]? = some record
  currentPresent : current.image.accepted[index]? = some record
  ingress : ApplicationShareIssueGrainSource.Ingress
  decoded : ApplicationShareIssueGrainSource.codec.decode record.event.canonicalBytes =
    some ingress
  eventExact : record.event =
    ApplicationShareIssueGrainReceiver.event prefix.source.capsule.identity.domain ingress
  original : Durable
  originalLoaded : DurableReceiverIO.loadImage rootBytes prefix.source.durable.logStart
    (prefix.source.durable.prefixImage (index + 1)) = .ok original

/-- Compute the original receipt with the OLD log start and original prefix.
The carry start's root and the target profile never replace this receipt. -/
def CarriedIssue.receipt {config : Config} {current : Durable}
    (issue : CarriedIssue config current) : NativeHostCodec.Receipt :=
  ⟨issue.record.transactionId, issue.record.event.eventId, issue.index + 1,
    issue.original.worldRoot⟩

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
    (prefix : CarriedSegmentIO.PreservedPrefix config current) (index : Nat) :
    Except String (CarriedIssue config current) := do
  if beforeCut : index < prefix.edge.body.cut.height then
    match sourcePresent : prefix.source.durable.image.accepted[index]? with
    | none => throw "carried original issue index absent"
    | some record =>
      match decoded : ApplicationShareIssueGrainSource.codec.decode record.event.canonicalBytes with
      | none => throw "carried original is not a canonical outer grain issue"
      | some ingress =>
        if eventExact : record.event =
            ApplicationShareIssueGrainReceiver.event prefix.source.capsule.identity.domain ingress then
          if bytes : (current.image.accepted[index]?.map DurableReceiverCodec.intentStream.encode) =
              some (DurableReceiverCodec.intentStream.encode record) then
            match loaded : DurableReceiverIO.loadImage rootBytes prefix.source.durable.logStart
                (prefix.source.durable.prefixImage (index + 1)) with
            | .error detail => throw detail
            | .ok original =>
              return ⟨prefix, index, beforeCut, record, sourcePresent,
                current_record_exact current index record bytes, ingress, decoded,
                eventExact, original, loaded⟩
          else throw "carried original issue record differs from current preserved prefix"
        else throw "carried original event22 identity differs"
  else throw "carried issue index is not before the original cut"

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
