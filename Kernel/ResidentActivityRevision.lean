/- Canonical revision/placement records for immutable per-author activity.
A revision is another signed stream append, not a rewrite of historic bytes.
This module interprets supplied participant-admitted entries; it adds no grant.
A malformed/stale/other-author revision remains historic data but cannot change
the current context projection. Cross-room authority transfer is NOT supplied. -/
import Compiler.StreamCell
import Compiler.NativeHostCodec
namespace Minidregg.Kernel.ResidentActivityRevision
open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Compiler.StoreCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

structure Key where
  stream : Nat
  sequence : Nat
  deriving DecidableEq, Repr

structure Activity where
  key : Key
  author : SubjectId
  revision : Nat
  topic : List UInt8
  text : List UInt8
  deriving DecidableEq, Repr

structure Revision where
  key : Key
  before : Nat
  topic : List UInt8
  text : List UInt8
  deriving DecidableEq, Repr

def revisionStream : StreamCodec Revision :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product bytesStream bytesStream))))
    (fun revision => (revision.key.stream, revision.key.sequence, revision.before, revision.topic, revision.text))
    (fun (stream, sequence, before, topic, text) => ⟨⟨stream, sequence⟩, before, topic, text⟩)
    (by intro revision; cases revision; rfl)

def revisionCodec :=
  NativeHostCodec.framed "DREGG/RESIDENT-ACTIVITY-REVISION/v1".toUTF8.toList revisionStream

/-- The signer/stream/reference and exact prior revision must all agree.
Topic moves occur within the currently admitted source stream; topic names
do not export its private bytes or grant another room permission. -/
def apply (current : Activity) (stream sequence : Nat) (record : StreamCell.StreamRecord)
    (payload : List UInt8) : Option Activity := do
  let revision ← revisionCodec.decode payload
  if record.author = current.author ∧ stream = current.key.stream ∧
      revision.key = current.key ∧ record.entry.ref = some (current.key.stream, current.key.sequence) ∧
      revision.before = current.revision ∧ sequence > current.revision ∧
      revision.topic.length ≤ StreamCell.maxTopicBytes ∧
      revision.text.length ≤ StreamCell.maxPayloadBytes ∧
      StreamCell.payloadDigest payload = record.entry.payloadDigest then
    some {current with revision := sequence, topic := revision.topic, text := revision.text}
  else none

theorem other_author_cannot_revise (current : Activity) (stream sequence : Nat)
    (record : StreamCell.StreamRecord) (payload : List UInt8)
    (other : record.author ≠ current.author) :
    apply current stream sequence record payload = none := by
  unfold apply
  cases decoded : revisionCodec.decode payload with
  | none => rfl
  | some revision => simp [other]

theorem stale_revision_cannot_revise (current : Activity) (stream sequence : Nat)
    (record : StreamCell.StreamRecord) (payload : List UInt8) (revision : Revision)
    (decoded : revisionCodec.decode payload = some revision)
    (stale : revision.before ≠ current.revision) :
    apply current stream sequence record payload = none := by
  simp [apply, decoded, stale]

theorem revision_preserves_identity (current next : Activity) (stream sequence : Nat)
    (record : StreamCell.StreamRecord) (payload : List UInt8)
    (accepted : apply current stream sequence record payload = some next) :
    next.key = current.key ∧ next.author = current.author := by
  unfold apply at accepted
  cases decoded : revisionCodec.decode payload with
  | none => simp [decoded] at accepted
  | some revision =>
    simp only [decoded] at accepted
    dsimp at accepted
    split at accepted
    · cases accepted
      exact ⟨rfl, rfl⟩
    · cases accepted

#assert_axioms other_author_cannot_revise
#assert_axioms stale_revision_cannot_revise
#assert_axioms revision_preserves_identity

structure Observed where
  sequence : Nat
  record : StreamCell.StreamRecord
  payload : Option (List UInt8)

structure Fold where
  current : List Activity
  invalidRevisions : Nat
  unavailable : Nat

def step (stream : Nat) (state : Fold) (observed : Observed) : Fold :=
  match observed.payload with
  | none => {state with unavailable := state.unavailable + 1}
  | some bytes =>
    if StreamCell.payloadDigest bytes != observed.record.entry.payloadDigest then
      {state with unavailable := state.unavailable + 1}
    else match revisionCodec.decode bytes with
      | none =>
        {state with current := state.current ++
          [⟨⟨stream, observed.sequence⟩, observed.record.author, observed.sequence,
            observed.record.entry.topic, bytes⟩]}
      | some revision =>
        match state.current.find? (fun current => current.key == revision.key) with
        | none => {state with invalidRevisions := state.invalidRevisions + 1}
        | some current =>
          match apply current stream observed.sequence observed.record bytes with
          | none => {state with invalidRevisions := state.invalidRevisions + 1}
          | some next =>
            {state with current := state.current.map fun prior =>
              if prior.key = next.key then next else prior}

def fold (stream : Nat) (observed : List Observed) : Fold :=
  observed.foldl (step stream) ⟨[], 0, 0⟩

end Minidregg.Kernel.ResidentActivityRevision
