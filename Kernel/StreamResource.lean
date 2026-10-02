/-
# Kernel.StreamResource -- per-author streams in a room (PLACE §2.3, §4.4)

A stream is a `stream` head cell (`Compiler.StreamCell`) born `--in R`, plus
one cell per entry.  Speaking is an ordinary resource transaction whose target
payload is `Payload.append`: the target's patch is one guarded write of the
head's one address (`append_footprint`) and the record is one fresh entry cell
at `entryCellId target (count + 1)` (`append_entry_at_next`,
`DeclaredResourceController.entryWrites`); neither reads or rewrites an earlier
entry.  The plan binds the head's own root and the author's authority footprint
(wave-c's `Theory.PlanBinding`); it reads nothing room-wide, so K authors
writing K streams never stale each other (`append_admits_disjoint_authors`),
while two appends planned from one read of ONE stream serialise: the second is
refused `staleTarget` (`append_same_stream_serialises`), and at the head its
write is no longer enabled (`StreamCell.same_head_refused`).  A fleet topic's
head is not a room stream: an `append` target naming one is refused
`wrongRole` (`room_append_refuses_topic_head`).

The per-author discipline is a law installed at birth (`authorLaw`): every
write is by the author.  A stream born `--in R` is covered by `under R`
(`stream_under_room`); reading it (`tail`, a signed `QueryView.tail`
observation) needs a capability that covers it.
-/
import Kernel.DeclaredResourceController
import Theory.ResourceBirthAuthority

namespace Minidregg.Kernel.StreamResource

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.Store
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DeclaredResourceController

set_option autoImplicit false

/-! ## The per-author law -/

/-- The request-verb codes of the two writing verbs on an object. -/
def writeTags : List Int :=
  [Int.ofNat (CredentialAuthorityEntryCodec.verbTag Verb.mutateObject),
   Int.ofNat (CredentialAuthorityEntryCodec.verbTag Verb.appendObject)]

/-- The law a stream is born with: any write (mutate or append) is by
`author`.  Reads, delegation and control are left to capabilities. -/
def authorLaw (author : SubjectId) : Minidregg.Pred.Pred :=
  Minidregg.Pred.Pred.any
    [.not (.memberOf "request/verb" writeTags), .eq "request/subject" (Int.ofNat author.value)]

/-- Anyone else's write is refused by the law. -/
theorem authorLaw_refuses_other_writer (author : SubjectId) (old new : Minidregg.Pred.State)
    (verb : Int) (writes : new.get "request/verb" = some verb) (isWrite : verb ∈ writeTags)
    (other : new.get "request/subject" ≠ some (Int.ofNat author.value)) :
    Minidregg.Pred.eval (authorLaw author) old new = false := by
  simp [authorLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith_any, Minidregg.Pred.evalWith,
    writes]
  exact ⟨isWrite, other⟩

/-- The author's own write passes the law. -/
theorem authorLaw_admits_author (author : SubjectId) (old new : Minidregg.Pred.State)
    (self : new.get "request/subject" = some (Int.ofNat author.value)) :
    Minidregg.Pred.eval (authorLaw author) old new = true := by
  simp [authorLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith_any, Minidregg.Pred.evalWith, self]

/-! ## The append leg -/

variable (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient) (command : Command)

/-- **`append_footprint`.** The append leg's patch touches exactly one store
address: the stream head's, whatever the stream's length. -/
theorem append_footprint (kind : ResourceKind) (id : Nat) (capability : CapabilityId)
    (version : Nat) (root : Digest) (request : StreamCell.Append) (observe : Option CapabilityId)
    (pre : TargetCell ⟨kind, id, capability, version, root, .append request, observe⟩)
    (head : StreamCell.Head) (loaded : StreamCell.headOf pre.logical = some head) :
    Patch.accessFootprint (targetPatch snapshot semantics ambient command
        ⟨kind, id, capability, version, root, .append request, observe⟩ pre) =
      {StreamCell.headAddress} := by
  change Patch.accessFootprint (match StreamCell.headOf pre.logical with
    | some head => [StreamCell.headWriteOp head (StreamCell.appendEntry id head
        (streamRecord snapshot semantics ambient command request))]
    | none => []) = _
  rw [loaded]
  exact StreamCell.headWrite_footprint _ _

/-- **`append_entry_at_next`.** The record of an append is the one entry at the
head's next position, with the head's tail as its parent. -/
theorem append_entry_at_next (kind : ResourceKind) (id : Nat) (capability : CapabilityId)
    (version : Nat) (root : Digest) (request : StreamCell.Append) (observe : Option CapabilityId)
    (pre : TargetCell ⟨kind, id, capability, version, root, .append request, observe⟩)
    (head : StreamCell.Head) (loaded : StreamCell.headOf pre.logical = some head) :
    appendedEntry snapshot semantics ambient command
        ⟨kind, id, capability, version, root, .append request, observe⟩ pre =
      some ⟨id, head.count + 1, head.tail, streamRecord snapshot semantics ambient command request⟩ := by
  change (StreamCell.headOf pre.logical).map (fun head => StreamCell.appendEntry id head
    (streamRecord snapshot semantics ambient command request)) = _
  rw [loaded]
  rfl

/-- **`room_append_refuses_topic_head`.** A resource-transaction append to a
head bound to a fleet topic is refused `wrongRole`: only the fleet receiver
appends to a topic. -/
theorem room_append_refuses_topic_head (kind : ResourceKind) (id : Nat) (capability : CapabilityId)
    (version : Nat) (root : Digest) (request : StreamCell.Append) (observe : Option CapabilityId)
    (pre : TargetCell ⟨kind, id, capability, version, root, .append request, observe⟩)
    (object : kind = .object) (current : version = StreamCell.commandVersion)
    (unmoved : root = pre.root)
    (topicOk : request.topic.length ≤ StreamCell.maxTopicBytes)
    (payloadOk : request.payload.length ≤ StreamCell.maxPayloadBytes)
    (head : StreamCell.Head) (loaded : StreamCell.headOf pre.logical = some head)
    (stream : Digest) (fleet : head.binding = .topic stream)
    (channel : DomainEpoch.admitAppend pre.logical command.subject request = .ok ()) :
    computeTarget snapshot semantics ambient command
        ⟨kind, id, capability, version, root, .append request, observe⟩ pre = .error .wrongRole := by
  subst object current
  simp [computeTarget, ← unmoved, topicOk, payloadOk, channel, loaded, fleet]
  rfl

/-- **`append_same_stream_serialises`.** An append planned against a stream
root that has since moved is refused `staleTarget`.  Two appends planned from
one read of one stream: the first moves the root, so the second refuses (and
`StreamCell.same_head_refused`: its head write is no longer enabled). -/
theorem append_same_stream_serialises (kind : ResourceKind) (id : Nat) (capability : CapabilityId)
    (version : Nat) (root : Digest) (request : StreamCell.Append) (observe : Option CapabilityId)
    (pre : TargetCell ⟨kind, id, capability, version, root, .append request, observe⟩)
    (object : kind = .object) (current : version = StreamCell.commandVersion)
    (moved : root ≠ pre.root) :
    computeTarget snapshot semantics ambient command
        ⟨kind, id, capability, version, root, .append request, observe⟩ pre = .error .staleTarget := by
  subst object current
  simp [computeTarget, moved]
  rfl

/-- One target's computed outcome at a directory: load its own cell, select
its role, compute.  These are `prepareTarget`'s cell reads; the remaining
read is the target's own (immutable) policy source. -/
def outcomeAt (deployment : Deployment) (directory : Directory Nat Registry) (target : Target) :
    Except Reject target.Outcome :=
  match directory.slots target.target with
  | .absent => .error .missingTarget
  | .present before =>
      match selectTarget deployment target before with
      | none => .error .wrongRole
      | some pre => computeTarget snapshot semantics ambient command target pre

/-- `prepareTarget`'s post is `outcomeAt`'s. -/
theorem prepareTarget_outcome (deployment : Deployment) (directory : Directory Nat Registry)
    (target : Target)
    (prepared : PreparedTarget deployment directory snapshot semantics ambient command target) :
    outcomeAt snapshot semantics ambient command deployment directory target = .ok prepared.post := by
  have computed := prepared.candidate.modeEvidence.down
  unfold outcomeAt
  rw [prepared.present]
  simp only [prepared.selected]
  exact computed

/-- **`append_admits_disjoint_authors`.** Committing one author's stream
write leaves every other stream's outcome exactly as it was planned: a
second author's append computes the same post (so its planned root still
matches and it admits with no re-plan), in either order, and the two writes
commute. -/
theorem append_admits_disjoint_authors (deployment : Deployment)
    (directory : Directory Nat Registry) (first second : Target)
    (distinct : first.target ≠ second.target) (firstPost secondPost : PackedCell Registry) :
    outcomeAt snapshot semantics ambient command deployment
        (Directory.insert Registry directory first.target firstPost) second =
      outcomeAt snapshot semantics ambient command deployment directory second ∧
    (Directory.insert Registry (Directory.insert Registry directory first.target firstPost)
        second.target secondPost).slots =
      (Directory.insert Registry (Directory.insert Registry directory second.target secondPost)
        first.target firstPost).slots := by
  refine ⟨?_, ?_⟩
  · unfold outcomeAt
    rw [Directory.insert_slot_other _ _ (Ne.symm distinct)]
  · simp only [Directory.insert]
    exact Function.update_comm distinct _ _ _

/-! ## Rooms -/

/-- **`stream_under_room`.** A stream born `--in R` is covered by `under R`
in the authority state the birth committed. -/
theorem stream_under_room {registry : TypeRegistry Digest}
    {descriptor : ResourceBirth.Descriptor registry} {state : Store CredentialAuthorityState.layout}
    (final : ResourceBirthAuthority.Postcondition descriptor state)
    {item : ResourceBirth.BirthItem registry} (member : item ∈ descriptor.births)
    {room : Nat} (inRoom : item.parent = some room) (kind : ResourceKind) :
    (TargetSet.under room : TargetSet kind).Covers (CredentialAuthorityState.parentageOf state)
      ⟨item.create.cellId⟩ :=
  Parentage.Descends.ofParent (ResourceBirthAuthority.birth_parent_recorded final member inRoom)

/-- info: 'Minidregg.Kernel.StreamResource.authorLaw_refuses_other_writer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authorLaw_refuses_other_writer
/-- info: 'Minidregg.Kernel.StreamResource.authorLaw_admits_author' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authorLaw_admits_author
/-- info: 'Minidregg.Kernel.StreamResource.append_footprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms append_footprint
/-- info: 'Minidregg.Kernel.StreamResource.append_entry_at_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms append_entry_at_next
/-- info: 'Minidregg.Kernel.StreamResource.room_append_refuses_topic_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms room_append_refuses_topic_head
/-- info: 'Minidregg.Kernel.StreamResource.append_same_stream_serialises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms append_same_stream_serialises
/-- info: 'Minidregg.Kernel.StreamResource.prepareTarget_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prepareTarget_outcome
/-- info: 'Minidregg.Kernel.StreamResource.append_admits_disjoint_authors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms append_admits_disjoint_authors
/-- info: 'Minidregg.Kernel.StreamResource.stream_under_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stream_under_room

end Minidregg.Kernel.StreamResource
