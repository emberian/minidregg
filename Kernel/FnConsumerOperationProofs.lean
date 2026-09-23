/- Proofs about the actual Lean decision called by the local E1 host route. -/
import Kernel.FnConsumerOperation

namespace Minidregg.Kernel.FnConsumerOperation

open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

theorem occupied_never_proposes_fresh (domain semantics : Digest)
    (report : Report) (receipt : Minidregg.Compiler.NativeHostCodec.Receipt)
    (accepted : List DurableReceiver.IntentRecord)
    (original : DurableReceiver.IntentRecord)
    (occupied : accepted.find? (fun entry =>
      entry.transactionId == marker domain semantics report.subject
        (operationNonce domain semantics report.application report.operation)) = some original)
    (command : DeclaredResourceController.Command) (reply : Reply) :
    decide domain semantics report receipt accepted ≠ .fresh command reply := by
  cases h : originalBinding domain semantics original with
  | none => simp [decide, occupied, h]
  | some binding =>
      simp only [decide, occupied, h]
      split
      · simp
      · split <;> simp

theorem exact_repeat_returns_original_reply (domain semantics : Digest)
    (report : Report) (receipt : Minidregg.Compiler.NativeHostCodec.Receipt)
    (accepted : List DurableReceiver.IntentRecord)
    (original : DurableReceiver.IntentRecord) (binding : Binding)
    (occupied : accepted.find? (fun entry =>
      entry.transactionId == marker domain semantics report.subject
        (operationNonce domain semantics report.application report.operation)) = some original)
    (decoded : originalBinding domain semantics original = some binding)
    (application : binding.application = report.application)
    (operation : binding.operation = report.operation)
    (provenance : binding.provenance = report.provenance)
    (package : binding.package = report.package) :
    decide domain semantics report receipt accepted = .repeated binding.reply := by
  simp [decide, occupied, decoded, application, operation, provenance, package]

theorem changed_source_records_conflict_without_second_effect
    (domain semantics : Digest) (report : Report)
    (receipt : Minidregg.Compiler.NativeHostCodec.Receipt)
    (accepted : List DurableReceiver.IntentRecord)
    (original : DurableReceiver.IntentRecord) (binding : Binding)
    (occupied : accepted.find? (fun entry =>
      entry.transactionId == marker domain semantics report.subject
        (operationNonce domain semantics report.application report.operation)) = some original)
    (decoded : originalBinding domain semantics original = some binding)
    (application : binding.application = report.application)
    (operation : binding.operation = report.operation)
    (source : binding.provenance.sourceIdentity ≠ report.provenance.sourceIdentity) :
    decide domain semantics report receipt accepted =
      .conflict (conflictCommand domain semantics report) := by
  have provenance : binding.provenance ≠ report.provenance := by
    intro same
    exact source (congrArg Provenance.sourceIdentity same)
  simp [decide, occupied, decoded, application, operation, provenance]

end Minidregg.Kernel.FnConsumerOperation
