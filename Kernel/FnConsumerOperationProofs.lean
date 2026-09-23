/- Proofs about the actual Lean decision called by the local E1 host route. -/
import Kernel.FnConsumerOperation

namespace Minidregg.Kernel.FnConsumerOperation

open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

theorem bindingCommand_uses_operation_nonce (domain semantics : Digest)
    (report : Report) (receipt : Minidregg.Compiler.NativeHostCodec.Receipt)
    (command : DeclaredResourceController.Command)
    (built : bindingCommand domain semantics report receipt = .ok command) :
    command.nonce = operationNonce domain semantics report.application report.operation := by
  by_cases size : (bindingCodec.encode
      ⟨report.application, report.operation, report.provenance, report.package,
        ⟨report.application, report.operation, report.provenance.sourceIdentity, receipt⟩⟩).length ≤
      maxBindingBytes
  · simp [bindingCommand, size] at built
    cases built
    rfl
  · simp [bindingCommand, size, Functor.map, Except.map] at built

theorem occupied_never_proposes_fresh (domain semantics : Digest)
    (report : Report) (receipt : Minidregg.Compiler.NativeHostCodec.Receipt)
    (accepted : List DurableReceiver.IntentRecord)
    (original : DurableReceiver.IntentRecord)
    (occupied : accepted.find? (fun entry =>
      entry.transactionId == marker domain semantics report.subject
        (operationNonce domain semantics report.application report.operation)) = some original)
    (command : DeclaredResourceController.Command) (reply : Reply) :
    decide domain semantics report receipt accepted ≠ .fresh command reply := by
  simp only [decide, occupied]
  repeat (first | split | simp_all)

theorem exact_repeat_returns_original_reply (domain semantics : Digest)
    (report : Report) (receipt : Minidregg.Compiler.NativeHostCodec.Receipt)
    (accepted : List DurableReceiver.IntentRecord)
    (original : DurableReceiver.IntentRecord) (binding : Binding)
    (occupied : accepted.find? (fun entry =>
      entry.transactionId == marker domain semantics report.subject
        (operationNonce domain semantics report.application report.operation)) = some original)
    (inbox : Option PortableInbox)
    (decoded : originalBindingWithInbox domain semantics original =
      some (binding, inbox))
    (application : binding.application = report.application)
    (operation : binding.operation = report.operation)
    (provenance : binding.provenance = report.provenance)
    (package : binding.package = report.package)
    (sameInbox : inbox = report.portableInbox) :
    decide domain semantics report receipt accepted = .repeated binding.reply := by
  simp [decide, occupied, decoded, application, operation, provenance, package,
    sameInbox]

theorem changed_source_records_conflict_without_second_effect
    (domain semantics : Digest) (report : Report)
    (receipt : Minidregg.Compiler.NativeHostCodec.Receipt)
    (accepted : List DurableReceiver.IntentRecord)
    (original : DurableReceiver.IntentRecord) (binding : Binding)
    (occupied : accepted.find? (fun entry =>
      entry.transactionId == marker domain semantics report.subject
        (operationNonce domain semantics report.application report.operation)) = some original)
    (inbox : Option PortableInbox)
    (decoded : originalBindingWithInbox domain semantics original =
      some (binding, inbox))
    (application : binding.application = report.application)
    (operation : binding.operation = report.operation)
    (source : binding.provenance.sourceIdentity ≠ report.provenance.sourceIdentity)
    (unrecorded : accepted.find? (fun entry =>
      entry.transactionId == marker domain semantics report.subject
        (conflictNonce domain semantics report)) = none) :
    decide domain semantics report receipt accepted =
      .conflict (conflictCommand domain semantics report) := by
  have provenance : binding.provenance ≠ report.provenance := by
    intro same
    exact source (congrArg Provenance.sourceIdentity same)
  simp [decide, occupied, decoded, application, operation, provenance, unrecorded]

/-- The three atom namespaces used by the atomic operation and a later
conflict cannot overlap for any source identity. -/
theorem operationAtom_ne_conflictAtom (domain semantics : Digest)
    (report : Report) :
    operationAtom domain semantics report.application report.operation ≠
      conflictAtom domain semantics report := by
  intro equal
  have n := congrArg (fun id => id.digest.value) equal
  simp only [operationAtom, conflictAtom] at n
  unfold operationNonce conflictNonce at n
  omega

theorem replyAtom_ne_conflictAtom (domain semantics : Digest)
    (report : Report) :
    replyAtom domain semantics report.application report.operation ≠
      conflictAtom domain semantics report := by
  intro equal
  have n := congrArg (fun id => id.digest.value) equal
  simp only [replyAtom, conflictAtom] at n
  unfold operationNonce conflictNonce at n
  omega

/-- A third atom cannot alias any operation binding, even for a different
application/operation hash value. Existing 0/1/2 residue classes stay fixed. -/
theorem operationInboxAtom_ne_anyOperationAtom (domain semantics : Digest)
    (application operation otherApplication otherOperation : List UInt8) :
    operationInboxAtom domain semantics application operation ≠
      operationAtom domain semantics otherApplication otherOperation := by
  intro equal
  have n := congrArg (fun id => id.digest.value) equal
  simp only [operationInboxAtom, operationAtom] at n
  unfold operationNonce at n
  omega

theorem operationInboxAtom_ne_anyReplyAtom (domain semantics : Digest)
    (application operation otherApplication otherOperation : List UInt8) :
    operationInboxAtom domain semantics application operation ≠
      replyAtom domain semantics otherApplication otherOperation := by
  intro equal
  have n := congrArg (fun id => id.digest.value) equal
  simp only [operationInboxAtom, replyAtom] at n
  unfold operationNonce at n
  omega

theorem operationInboxAtom_ne_anyConflictAtom (domain semantics : Digest)
    (application operation : List UInt8) (report : Report) :
    operationInboxAtom domain semantics application operation ≠
      conflictAtom domain semantics report := by
  intro equal
  have n := congrArg (fun id => id.digest.value) equal
  simp only [operationInboxAtom, conflictAtom] at n
  unfold operationNonce conflictNonce at n
  omega

theorem conflictInboxAtom_ne_anyOperationAtom (domain semantics : Digest)
    (report : Report) (application operation : List UInt8) :
    conflictInboxAtom domain semantics report ≠
      operationAtom domain semantics application operation := by
  intro equal
  have n := congrArg (fun id => id.digest.value) equal
  simp only [conflictInboxAtom, operationAtom] at n
  unfold conflictNonce operationNonce at n
  omega

theorem conflictInboxAtom_ne_anyReplyAtom (domain semantics : Digest)
    (report : Report) (application operation : List UInt8) :
    conflictInboxAtom domain semantics report ≠
      replyAtom domain semantics application operation := by
  intro equal
  have n := congrArg (fun id => id.digest.value) equal
  simp only [conflictInboxAtom, replyAtom] at n
  unfold conflictNonce operationNonce at n
  omega

theorem conflictInboxAtom_ne_anyConflictAtom (domain semantics : Digest)
    (report other : Report) :
    conflictInboxAtom domain semantics report ≠
      conflictAtom domain semantics other := by
  intro equal
  have n := congrArg (fun id => id.digest.value) equal
  simp only [conflictInboxAtom, conflictAtom] at n
  unfold conflictNonce at n
  omega

end Minidregg.Kernel.FnConsumerOperation
