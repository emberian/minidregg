/-
# Kernel.DomainEpochStream — the channel law at the kernel's append

`Kernel.DomainEpoch` is imported by the registry and by the transaction receiver, so the composition
with the receiver's `computeTarget` lives here: the stream append's target computation runs
`DomainEpoch.admitAppend` after its own checks, and a channel record the law refuses is refused
`Reject.channel reason`, the clause named. Two locks hold the author: the stream's birth law
(`StreamResource.authorLaw sequencer`, which refuses every write by another subject, the first record's
included) and `ChannelLaw`'s `foreignAuthor` clause (every record after the first is by the previous
record's author).
-/
import Kernel.StreamResource
import Kernel.DomainEpochLaw
import Theory.AssertAxioms

namespace Minidregg.Kernel.DomainEpochStream

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.Store
open Minidregg.Theory.CellState
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DeclaredResourceController

set_option autoImplicit false

variable (snapshot : AuthoritySnapshot) (semantics : Digest)
  (ambient : Ambient) (command : Command)

/-- **A channel refusal is the kernel's refusal**, by name: when the law refuses, the append's target
computation is `.error (.channel reason)`. -/
theorem computeTarget_channel_refused (kind : ResourceKind) (id : Nat) (capability : CapabilityId)
    (version : Nat) (root : Digest) (request : StreamCell.Append)
    (observe : Option CapabilityId)
    (pre : TargetCell ⟨kind, id, capability, version, root, .append request, observe⟩)
    (object : kind = .object) (current : version = StreamCell.commandVersion) (fresh : root = pre.root)
    (topic : request.topic.length ≤ StreamCell.maxTopicBytes)
    (payload : request.payload.length ≤ StreamCell.maxPayloadBytes)
    {reason : DomainEpoch.Refusal}
    (refused : DomainEpoch.admitAppend pre.logical command.subject request = .error reason) :
    computeTarget snapshot semantics ambient command
        ⟨kind, id, capability, version, root, .append request, observe⟩ pre = .error (.channel reason) := by
  subst object current
  simp [computeTarget, fresh, topic, payload, refused]
  rfl

/-- The admitting pole: when the law admits, the append computes the stream's one new position. -/
theorem computeTarget_channel_admitted (kind : ResourceKind) (id : Nat) (capability : CapabilityId)
    (version : Nat) (root : Digest) (request : StreamCell.Append)
    (observe : Option CapabilityId)
    (pre : TargetCell ⟨kind, id, capability, version, root, .append request, observe⟩)
    (object : kind = .object) (current : version = StreamCell.commandVersion) (fresh : root = pre.root)
    (topic : request.topic.length ≤ StreamCell.maxTopicBytes)
    (payload : request.payload.length ≤ StreamCell.maxPayloadBytes)
    (admitted : DomainEpoch.admitAppend pre.logical command.subject request = .ok ())
    (head : StreamCell.Head) (loaded : StreamCell.headOf pre.logical = some head)
    (room : head.binding = .room) :
    computeTarget snapshot semantics ambient command
        ⟨kind, id, capability, version, root, .append request, observe⟩ pre =
      .ok ((StreamCell.headWriteOp head (StreamCell.appendEntry id head
        (streamRecord snapshot semantics ambient command request))).apply pre.logical) := by
  subst object current
  simp [computeTarget, fresh, topic, payload, admitted, loaded, room]
  rfl

/-- A well-formed record fits the stream's payload bound (the largest class has `E = 64`: 2,095 bytes). -/
theorem wellFormed_payload_fits {r : DomainEpoch.EpochRecord} (wf : r.WellFormed) :
    (DomainEpoch.recordAppend r).payload.length ≤ StreamCell.maxPayloadBytes := by
  obtain ⟨P, cls, roots, _, _⟩ := wf
  have hE : P.E ≤ 64 := by
    unfold Minidregg.Theory.Channel.profileOfId at cls
    split at cls <;> (try cases cls) <;> decide
  show r.encode.length ≤ 4096
  rw [DomainEpoch.epochRecord_size, roots]
  omega

theorem recordAppend_topic_fits (r : DomainEpoch.EpochRecord) :
    (DomainEpoch.recordAppend r).topic.length ≤ StreamCell.maxTopicBytes := by
  show (DomainEpoch.channelTopic r.domain r.epoch).length ≤ 64
  rw [DomainEpoch.channelTopic_length]; decide

section Record
variable (id : Nat) (capability : CapabilityId) (observe : Option CapabilityId)
  (r : DomainEpoch.EpochRecord)
  (root : Digest)
  (pre : TargetCell ⟨.object, id, capability, StreamCell.commandVersion, root, .append (DomainEpoch.recordAppend r), observe⟩)
  (fresh : root = pre.root)
  {p : DomainEpoch.Prev} (last : DomainEpoch.prevOf pre.logical = .ok (some p))
include fresh last

/-- The kernel refuses a gap (epoch `prev + 2` or more) `Reject.channel .epochGap`. -/
theorem kernel_gap_refused (wf : r.WellFormed) (dom : r.domain = p.domain)
    (gap : p.epoch.toNat + 1 < r.epoch.toNat) :
    computeTarget snapshot semantics ambient command
        ⟨.object, id, capability, StreamCell.commandVersion, root, .append (DomainEpoch.recordAppend r), observe⟩ pre =
      .error (.channel .epochGap) :=
  computeTarget_channel_refused snapshot semantics ambient command _ _ _ _ _ _ _ pre rfl rfl fresh
    (recordAppend_topic_fits r) (wellFormed_payload_fits wf)
    (by rw [DomainEpoch.admitAppend_record _ _ _ _ last]; exact DomainEpoch.gap_refused wf dom gap)

/-- The kernel refuses a repeat or an out-of-order record `Reject.channel .epochNotAfter`. -/
theorem kernel_out_of_order_refused (wf : r.WellFormed) (dom : r.domain = p.domain)
    (notAfter : r.epoch.toNat ≤ p.epoch.toNat) :
    computeTarget snapshot semantics ambient command
        ⟨.object, id, capability, StreamCell.commandVersion, root, .append (DomainEpoch.recordAppend r), observe⟩ pre =
      .error (.channel .epochNotAfter) :=
  computeTarget_channel_refused snapshot semantics ambient command _ _ _ _ _ _ _ pre rfl rfl fresh
    (recordAppend_topic_fits r) (wellFormed_payload_fits wf)
    (by rw [DomainEpoch.admitAppend_record _ _ _ _ last]; exact DomainEpoch.out_of_order_refused wf dom notAfter)

/-- The kernel refuses a different channel domain even when the epoch is next. -/
theorem kernel_foreign_domain_refused (wf : r.WellFormed) (dom : r.domain ≠ p.domain) :
    computeTarget snapshot semantics ambient command
        ⟨.object, id, capability, StreamCell.commandVersion, root, .append (DomainEpoch.recordAppend r), observe⟩ pre =
      .error (.channel .foreignDomain) :=
  computeTarget_channel_refused snapshot semantics ambient command _ _ _ _ _ _ _ pre rfl rfl fresh
    (recordAppend_topic_fits r) (wellFormed_payload_fits wf)
    (by rw [DomainEpoch.admitAppend_record _ _ _ _ last]; exact DomainEpoch.foreign_domain_refused wf dom)

/-- The kernel refuses another subject's record `Reject.channel .foreignAuthor`. -/
theorem kernel_foreign_author_refused (wf : r.WellFormed) (dom : r.domain = p.domain)
    (next : r.epoch.toNat = p.epoch.toNat + 1) (foreign : command.subject ≠ p.author) :
    computeTarget snapshot semantics ambient command
        ⟨.object, id, capability, StreamCell.commandVersion, root, .append (DomainEpoch.recordAppend r), observe⟩ pre =
      .error (.channel .foreignAuthor) :=
  computeTarget_channel_refused snapshot semantics ambient command _ _ _ _ _ _ _ pre rfl rfl fresh
    (recordAppend_topic_fits r) (wellFormed_payload_fits wf)
    (by rw [DomainEpoch.admitAppend_record _ _ _ _ last]; exact DomainEpoch.foreign_author_refused wf dom next foreign)

/-- The kernel refuses a record with the wrong root count `Reject.channel .rootCount`. -/
theorem kernel_root_count_refused {P : Minidregg.Theory.Channel.Profile}
    (cls : Minidregg.Theory.Channel.profileOfId r.classId = some P) (count : r.tickRoots.length ≠ P.E)
    (fits : r.encode.length ≤ StreamCell.maxPayloadBytes) :
    computeTarget snapshot semantics ambient command
        ⟨.object, id, capability, StreamCell.commandVersion, root, .append (DomainEpoch.recordAppend r), observe⟩ pre =
      .error (.channel .rootCount) :=
  computeTarget_channel_refused snapshot semantics ambient command _ _ _ _ _ _ _ pre rfl rfl fresh
    (recordAppend_topic_fits r) fits
    (by rw [DomainEpoch.admitAppend_record _ _ _ _ last]; exact DomainEpoch.root_count_refused cls count _)

/-- The well-formed next record by the sequencer is the stream's next position. -/
theorem kernel_next_admitted (wf : r.WellFormed) (dom : r.domain = p.domain)
    (next : r.epoch.toNat = p.epoch.toNat + 1) (seq : command.subject = p.author)
    (head : StreamCell.Head) (loaded : StreamCell.headOf pre.logical = some head)
    (room : head.binding = .room) :
    computeTarget snapshot semantics ambient command
        ⟨.object, id, capability, StreamCell.commandVersion, root, .append (DomainEpoch.recordAppend r), observe⟩ pre =
      .ok ((StreamCell.headWriteOp head (StreamCell.appendEntry id head
        (streamRecord snapshot semantics ambient command (DomainEpoch.recordAppend r)))).apply pre.logical) :=
  computeTarget_channel_admitted snapshot semantics ambient command _ _ _ _ _ _ _ pre rfl rfl fresh
    (recordAppend_topic_fits r) (wellFormed_payload_fits wf)
    (by rw [DomainEpoch.admitAppend_record _ _ _ _ last]; exact DomainEpoch.next_record_admitted wf dom next seq)
    head loaded room

end Record

/-- The receiver's exact derived record extends the admitted history using the
same admission result and head/entry constructors as `computeTarget`. Combined
with `admittedHistory_chain`, historical epoch uniqueness is preserved without
loading the preceding entries. -/
theorem receiver_extends_admitted_history (id : Nat) (head : StreamCell.Head)
    (records : List StreamCell.StreamRecord) (request : StreamCell.Append)
    (history : DomainEpoch.AdmittedHistory id head records)
    (admitted : DomainEpoch.admitAppend (StreamCell.headStore head)
      command.subject request = .ok ()) :
    DomainEpoch.AdmittedHistory id
      (head.append (StreamCell.appendEntry id head
        (streamRecord snapshot semantics ambient command request)))
      (streamRecord snapshot semantics ambient command request :: records) := by
  exact DomainEpoch.AdmittedHistory.append history command.subject request ambient.height
    ⟨operationMarker snapshot.domain semantics command⟩ admitted

#assert_axioms receiver_extends_admitted_history
#assert_axioms computeTarget_channel_refused
#assert_axioms computeTarget_channel_admitted
#assert_axioms wellFormed_payload_fits
#assert_axioms recordAppend_topic_fits
#assert_axioms kernel_gap_refused
#assert_axioms kernel_out_of_order_refused
#assert_axioms kernel_foreign_domain_refused
#assert_axioms kernel_foreign_author_refused
#assert_axioms kernel_root_count_refused
#assert_axioms kernel_next_admitted

end Minidregg.Kernel.DomainEpochStream
