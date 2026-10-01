/-
# Kernel.StreamResource -- per-author streams in a room (PLACE §2.3, §4.4)

A stream is a `stream` cell (`Compiler.StreamCell`) born `--in R`.  Speaking
is an ordinary resource transaction whose target payload is
`Payload.append`: the receiver allocates one record at the stream's
`nextSeq` and nothing else (`append_footprint`).  The plan binds the stream
cell's own root and the author's authority footprint (wave-c's
`Theory.PlanBinding`); it reads nothing room-wide, so K authors writing K
streams never stale each other (`append_admits_disjoint_authors`), while two
appends planned from one read of ONE stream serialise: the second is refused
`staleTarget` (`append_same_stream_serialises`), and at the address level its
position is already allocated (`StreamCell.same_position_refused`).

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
address: the stream's next sequence position. -/
theorem append_footprint (kind : ResourceKind) (id : Nat) (capability : CapabilityId)
    (version : Nat) (root : Digest) (request : StreamCell.Append) (observe : Option CapabilityId)
    (pre : TargetCell ⟨kind, id, capability, version, root, .append request, observe⟩) :
    Patch.accessFootprint (targetPatch snapshot semantics ambient command
        ⟨kind, id, capability, version, root, .append request, observe⟩ pre) =
      {StreamCell.address (StreamCell.nextSeq pre.logical)} :=
  StreamCell.appendOp_footprint _ _

/-- **`append_same_stream_serialises`.** An append planned against a stream
root that has since moved is refused `staleTarget`.  Two appends planned from
one read of one stream: the first moves the root, so the second refuses (and
`StreamCell.same_position_refused`: its position is no longer free). -/
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

/-! ## `tail` -/

/-- `tail stream from n`: the recorded entries at positions `from … from+n-1`. -/
abbrev tail := StreamCell.tail

/-- info: 'Minidregg.Kernel.StreamResource.authorLaw_refuses_other_writer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authorLaw_refuses_other_writer
/-- info: 'Minidregg.Kernel.StreamResource.authorLaw_admits_author' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authorLaw_admits_author
/-- info: 'Minidregg.Kernel.StreamResource.append_footprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms append_footprint
/-- info: 'Minidregg.Kernel.StreamResource.append_same_stream_serialises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms append_same_stream_serialises
/-- info: 'Minidregg.Kernel.StreamResource.prepareTarget_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prepareTarget_outcome
/-- info: 'Minidregg.Kernel.StreamResource.append_admits_disjoint_authors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms append_admits_disjoint_authors
/-- info: 'Minidregg.Kernel.StreamResource.stream_under_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stream_under_room

end Minidregg.Kernel.StreamResource
