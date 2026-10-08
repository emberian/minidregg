/- Stage-0 certificates bind the exact source intent and its derived Turn.
The durable log still encodes the intent; World-indexed host state is FD-1.
-/
import Kernel.ObjectiveActivityReceiverCore
import Kernel.SeatReceiverCore
import Kernel.HostRefinesWorldCore
import Kernel.DeployedHistory
import Kernel.ObjectiveCheckpointInvariant

namespace Minidregg.Kernel.ObjectiveAdmissible

open Minidregg.Theory Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DeployedBridge
open Minidregg.Kernel.HostRefinesWorld
open Minidregg.Kernel.TurnOfIntent
open Minidregg.Kernel.World

set_option autoImplicit false

abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev W := World deployedR TransactionId Digest
abbrev T := DTurn deployedR Digest

/-- The receiver's checked computation, indexed by its exact output intent.
There is no constructor for an independently substituted post or guard list. -/
inductive Source : ObjectiveActivity.Config → (p : Durable) →
    DataIntent ResourceBirthCodec.rootBytes → Prop
  | activity {F : Type} [Field F] [DecidableEq F]
      {deployment : CanonicalCellRegistry.Deployment} {profile : CanonicalRuntimeProfile.Profile F}
      {ambient : ObjectiveKernelConfig.Ambient} {p : Durable}
      {ingress : ObjectiveActivityReceiver.DecodedIngress}
      (accepted : ObjectiveActivityReceiver.Accepted deployment profile ambient p ingress) :
      Source accepted.prepared.config p (ObjectiveActivityReceiver.intent accepted)
  | failed {F : Type} [Field F] [DecidableEq F]
      {deployment : CanonicalCellRegistry.Deployment} {profile : CanonicalRuntimeProfile.Profile F}
      {ambient : ObjectiveKernelConfig.Ambient} {p : Durable}
      {ingress : ObjectiveActivityReceiver.DecodedIngress}
      (failed : ObjectiveActivityReceiver.Failed deployment profile ambient p ingress) :
      Source failed.gated.config p failed.intent
  | seat {F : Type} [Field F] [DecidableEq F]
      {deployment : CanonicalCellRegistry.Deployment} {profile : CanonicalRuntimeProfile.Profile F}
      {ambient : ObjectiveKernelConfig.Ambient} {p : Durable}
      {ingress : SeatReceiver.DecodedIngress}
      (accepted : SeatReceiver.Accepted deployment profile ambient p ingress)
      (ob : ObjectiveActivity.Config) : Source ob p (SeatReceiver.intent accepted)
  | foreign {ob : ObjectiveActivity.Config} {p : Durable}
      (intent : DataIntent ResourceBirthCodec.rootBytes)
      (gate : ObjectiveActivityGate.ordinaryGate intent = .ok ()) : Source ob p intent

/-- The three receiver routes, stated over the exact source intent. -/
def Route (p : Durable) (intent : DataIntent ResourceBirthCodec.rootBytes) : Prop :=
  (∃ (ob : ObjectiveActivity.Config) (height : Nat)
      (turn : ObjectiveActivity.AdmittedTurn ob p.snapshot height)
      (sealing : ObjectiveActivityWire.Seal) (posts : List ObjectiveActivityWire.Post)
      (extra : List ReadGuard),
      ActivitySeatEnd.finish ob p.snapshot height turn = .ok (posts, extra) ∧
        intent = ActivitySeatEnd.AdmittedTurn.finalIntent sealing posts extra turn) ∨
    (∃ posts : List ObjectiveActivityWire.Post,
      intent.writes = posts.map (ObjectiveActivityWire.Post.write ResourceBirthCodec.rootBytes) ∧
        SeatStore.Inert p.snapshot posts) ∨
    ObjectiveActivityGate.ordinaryGate intent = .ok ()

theorem Source.route {ob : ObjectiveActivity.Config} {p : Durable}
    {intent : DataIntent ResourceBirthCodec.rootBytes} (source : Source ob p intent) :
    Route p intent := by
  cases source with
  | activity accepted =>
    exact Or.inl ⟨_, _, accepted.prepared.decided,
      ObjectiveActivityReceiver.admissionSeal accepted.prepared _, accepted.prepared.final.1,
      accepted.prepared.final.2, accepted.prepared.finalExact, rfl⟩
  | failed failed =>
    exact Or.inl ⟨_, _, .failed failed.request failed.failure,
      { ObjectiveActivityReceiver.sealAt failed.gated.authority _ _ with
        event := ObjectiveActivityReceiver.failedEvent (ObjectiveActivityReceiver.event _ _ _) failed.cause },
      failed.final.1, failed.final.2, failed.finalExact, rfl⟩
  | seat accepted ob =>
    exact Or.inr (Or.inl ⟨accepted.prepared.decided.posts, rfl, accepted.prepared.decided.inert⟩)
  | foreign intent gate => exact Or.inr (Or.inr gate)

#assert_axioms Source.route

/-- Executable data proposed by the receiver, before derivation and preflight. -/
structure Proposal (p : Durable) where
  config : ObjectiveActivity.Config
  intent : DataIntent ResourceBirthCodec.rootBytes
  source : Source config p intent

def Proposal.activity {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : ObjectiveKernelConfig.Ambient} {p : Durable}
    {ingress : ObjectiveActivityReceiver.DecodedIngress}
    (verdict : ObjectiveActivityReceiver.Verdict deployment profile ambient p ingress) : Proposal p :=
  match verdict with
  | .accepted accepted => ⟨accepted.prepared.config, _, .activity accepted⟩
  | .failed failed => ⟨failed.gated.config, _, .failed failed⟩

def Proposal.seat {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : ObjectiveKernelConfig.Ambient} {p : Durable}
    {ingress : SeatReceiver.DecodedIngress}
    (accepted : SeatReceiver.Accepted deployment profile ambient p ingress) : Proposal p :=
  ⟨accepted.prepared.config, _, .seat accepted _⟩

theorem Proposal.activity_intent {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : ObjectiveKernelConfig.Ambient} {p : Durable}
    {ingress : ObjectiveActivityReceiver.DecodedIngress}
    (verdict : ObjectiveActivityReceiver.Verdict deployment profile ambient p ingress) :
    (Proposal.activity verdict).intent = verdict.intent := by cases verdict <;> rfl

#assert_axioms Proposal.activity_intent

/-- Data, not merely a Boolean or proposition: the writer obtains its only
intent from this certificate. Both its run and derived Turn are bound to it. -/
structure CheckedCommit (ob : ObjectiveActivity.Config) (p : Durable) (t : T) where
  intent : DataIntent ResourceBirthCodec.rootBytes
  source : Source ob p intent
  derived : Turn.ofLoaded bridge DeployedHistory.history p intent = .ok t
  installs : Installs (execute .complete p.snapshot intent) = true

/-- Derivation is checked against the current loaded image; a failed check
produces no certificate and hence cannot reach the checked writer. -/
def Proposal.check {p : Durable} (proposal : Proposal p) :
    Except String ((t : T) × {certificate : CheckedCommit proposal.config p t //
      certificate.intent = proposal.intent}) :=
  match derived : Turn.ofLoaded bridge DeployedHistory.history p proposal.intent with
  | .error reason => .error s!"receiver intent has no World turn: {repr reason}"
  | .ok t =>
    if installs : Installs (execute .complete p.snapshot proposal.intent) = true then
      .ok ⟨t, ⟨proposal.intent, proposal.source, derived, installs⟩, rfl⟩
    else .error "receiver intent does not install at this opening"

/-- The logical certificate adds the represented World to the same data used
by the IO writer. It does not construct a second executable World state. -/
structure Admissible (ob : ObjectiveActivity.Config) (w : W) (t : T) where
  loaded : Durable
  represents : DeployedRepresents loaded w
  commit : CheckedCommit ob loaded t

/-- Same receiver authorization means the same decoded signed ingress under
exactly the same deployment, profile, ambient rules and loaded opening. It
never identifies merely equal digests or independently supplied output data. -/
inductive SameAuthorization (p : Durable) :
    DataIntent ResourceBirthCodec.rootBytes → DataIntent ResourceBirthCodec.rootBytes → Prop
  | activity {F : Type} [Field F] [DecidableEq F]
      {deployment : CanonicalCellRegistry.Deployment} {profile : CanonicalRuntimeProfile.Profile F}
      {ambient : ObjectiveKernelConfig.Ambient}
      {ingress : ObjectiveActivityReceiver.DecodedIngress}
      (left right : ObjectiveActivityReceiver.Verdict deployment profile ambient p ingress) :
      SameAuthorization p left.intent right.intent
  | seat {F : Type} [Field F] [DecidableEq F]
      {deployment : CanonicalCellRegistry.Deployment} {profile : CanonicalRuntimeProfile.Profile F}
      {ambient : ObjectiveKernelConfig.Ambient} {ingress : SeatReceiver.DecodedIngress}
      (left right : SeatReceiver.Accepted deployment profile ambient p ingress) :
      SameAuthorization p (SeatReceiver.intent left) (SeatReceiver.intent right)

/-- Authorization determines the complete source intent, including all posts,
refunds, newborn law sources and read guards. -/
theorem SameAuthorization.intent_determined {p : Durable}
    {left right : DataIntent ResourceBirthCodec.rootBytes}
    (same : SameAuthorization p left right) : left = right := by
  cases same with
  | activity left right => exact ObjectiveActivityReceiver.Verdict.intent_determined left right
  | seat left right => exact SeatReceiver.intent_determined left right

/-- The checked derivation is a function of the authorized source intent. -/
theorem CheckedCommit.turn_determined {ob : ObjectiveActivity.Config} {p : Durable} {t t' : T}
    (left : CheckedCommit ob p t) (right : CheckedCommit ob p t')
    (same : SameAuthorization p left.intent right.intent) : t = t' := by
  have intents := same.intent_determined
  have derived := left.derived
  rw [intents, right.derived] at derived
  exact (Except.ok.inj derived).symm

/-- The authorization context includes the same durable opening. This is the
stage-0 Loaded index; replacing Host state with World is the later FD-1 change. -/
def Admissible.SameAuthorization {ob : ObjectiveActivity.Config} {w : W} {t t' : T}
    (left : Admissible ob w t) (right : Admissible ob w t') : Prop :=
  left.loaded = right.loaded ∧
    ObjectiveAdmissible.SameAuthorization left.loaded left.commit.intent right.commit.intent

theorem Admissible.turn_determined {ob : ObjectiveActivity.Config} {w : W} {t t' : T}
    (left : Admissible ob w t) (right : Admissible ob w t')
    (same : left.SameAuthorization right) : t = t' := by
  rcases left with ⟨p, rep, left⟩
  rcases right with ⟨q, rep', right⟩
  rcases same with ⟨opening, authorization⟩
  cases opening
  exact left.turn_determined right authorization

#assert_axioms SameAuthorization.intent_determined CheckedCommit.turn_determined Admissible.turn_determined

/-- The checked receiver supplies precisely the old invariant's step premise.
This lemma is the temporary bridge while the snapshot induction is retained. -/
theorem Source.step {ob : ObjectiveActivity.Config} {p : Durable}
    {intent : DataIntent ResourceBirthCodec.rootBytes} (source : Source ob p intent)
    (schedule : DurableCommitProtocol.Schedule) :
    ObjectiveCheckpointInvariant.Step ob p.snapshot
      ((execute schedule p.snapshot intent).storeAfter p.snapshot) := by
  cases source with
  | activity accepted =>
    exact .turn accepted.prepared.decided
      (ObjectiveActivityReceiver.admissionSeal accepted.prepared _)
      accepted.prepared.final.1 accepted.prepared.final.2 accepted.prepared.finalExact schedule
  | failed failed =>
    exact .turn (.failed failed.request failed.failure)
      { ObjectiveActivityReceiver.sealAt failed.gated.authority _ _ with
        event := ObjectiveActivityReceiver.failedEvent
          (ObjectiveActivityReceiver.event _ _ _) failed.cause }
      failed.final.1 failed.final.2 failed.finalExact schedule
  | seat accepted ob =>
    exact .inert _ accepted.prepared.decided.posts rfl accepted.prepared.decided.inert schedule
  | foreign intent gate => exact .foreign intent gate schedule

/-- One certified step of the deployed World, with the actual successful step
as a separate premise from receiver admission. -/
inductive WStep (ob : ObjectiveActivity.Config) : W → W → Prop
  | mk {w w' : W} {t : T} (cert : Admissible ob w t)
      (step : World.step DeployedHistory.history w t = some w') : WStep ob w w'

inductive Reachable (ob : ObjectiveActivity.Config) (genesis : W) : W → Prop
  | genesis : Reachable ob genesis genesis
  | step {before after : W} : Reachable ob genesis before → WStep ob before after → Reachable ob genesis after

#assert_axioms Source.step

/-! Post-authorization substitution plants. All replacement bytes are canonical
images. Authorization is held fixed by SameAuthorization, not by an assumed
collision-free digest. -/

/-- Replace one post at its exact position; preserve every cell id and pre-root. -/
def replacePost (intent : DataIntent ResourceBirthCodec.rootBytes)
    (before : List DataWrite) (post : DataWrite) (after : List DataWrite)
    (shape : intent.writes = before ++ post :: after) (bytes : List UInt8) :
    DataIntent ResourceBirthCodec.rootBytes :=
  { intent with
    writes := before ++ { post with canonicalPostBytes := bytes, exactPost := ResourceBirthCodec.rootBytes bytes } :: after
    postRootsBound := by
      intro write member
      rcases List.mem_append.mp member with member | member
      · exact intent.postRootsBound write (by rw [shape]; exact List.mem_append_left _ member)
      · rcases List.mem_cons.mp member with same | member
        · subst write; rfl
        · exact intent.postRootsBound write (by rw [shape]; exact List.mem_append_right _ (List.mem_cons_of_mem _ member))
    guardsReadOnly := by
      intro guard member
      simpa [shape] using intent.guardsReadOnly guard member }

theorem replacePost_same_pre (intent : DataIntent ResourceBirthCodec.rootBytes)
    (before : List DataWrite) (post : DataWrite) (after : List DataWrite)
    (shape : intent.writes = before ++ post :: after) (bytes : List UInt8) :
    (replacePost intent before post after shape bytes).writes.map (fun w => (w.cellId, w.expectedPre)) =
      intent.writes.map (fun w => (w.cellId, w.expectedPre)) := by
  simp [replacePost, shape]

theorem replacePost_ne (intent : DataIntent ResourceBirthCodec.rootBytes)
    (before : List DataWrite) (post : DataWrite) (after : List DataWrite)
    (shape : intent.writes = before ++ post :: after) (bytes : List UInt8)
    (different : bytes ≠ post.canonicalPostBytes) :
    replacePost intent before post after shape bytes ≠ intent := by
  intro same
  have writes := congrArg DataIntent.writes same
  change before ++ _ :: after = intent.writes at writes
  rw [shape] at writes
  have atPost := (List.cons.inj (List.append_cancel_left writes)).1
  exact different (congrArg DataWrite.canonicalPostBytes atPost)

/-- The headline dependency rules out every changed intent under the SAME
receiver authorization, while allowing independent authorizations elsewhere. -/
theorem CheckedCommit.reject_substitution {ob : ObjectiveActivity.Config} {p : Durable} {t t' : T}
    (cert : CheckedCommit ob p t) (other : CheckedCommit ob p t')
    (same : SameAuthorization p cert.intent other.intent)
    (mutated : DataIntent ResourceBirthCodec.rootBytes) (changed : mutated ≠ cert.intent) :
    other.intent ≠ mutated := by
  rw [← same.intent_determined]
  exact Ne.symm changed

/-- A different body remains a well-formed lifecycle image at the same role/key. -/
theorem activity_image_decodes (role : ObjectiveActivityCell.Role) (key body : List UInt8) :
    (ResourceBirthCodec.LifecycleImage.codec CanonicalCellRegistry.registry).decode
      (ObjectiveActivity.image role key body) =
      some (.live ⟨.objectiveActivity, ObjectiveActivityCell.cellOf ⟨role, key, body⟩⟩) :=
  ResourceBirthCodec.LifecycleImage.decode_encode CanonicalCellRegistry.registry
    (.live ⟨.objectiveActivity, ObjectiveActivityCell.cellOf ⟨role, key, body⟩⟩)

theorem activity_body_extension_ne (role : ObjectiveActivityCell.Role) (key body : List UInt8) :
    ObjectiveActivity.image role key (body ++ [0]) ≠ ObjectiveActivity.image role key body := by
  intro same
  have payload := congrArg ObjectiveActivity.payloadOf same
  rw [ObjectiveCheckpointInvariant.payloadOf_image, ObjectiveCheckpointInvariant.payloadOf_image] at payload
  have bodies := congrArg (fun p : ObjectiveActivityCell.Payload => p.body) (Option.some.inj payload)
  have lengths := congrArg List.length bodies
  simp only [List.length_append, List.length_cons, List.length_nil] at lengths
  omega

/-- Business post plant: change the body of a state image at the same key. -/
theorem business_write_substitution_excluded {ob : ObjectiveActivity.Config} {p : Durable} {t t' : T}
    (cert : CheckedCommit ob p t) (other : CheckedCommit ob p t')
    (same : SameAuthorization p cert.intent other.intent)
    (before : List DataWrite) (post : DataWrite) (after : List DataWrite)
    (shape : cert.intent.writes = before ++ post :: after) (key body : List UInt8)
    (state : post.canonicalPostBytes = ObjectiveActivity.image .state key body) :
    other.intent ≠ replacePost cert.intent before post after shape
      (ObjectiveActivity.image .state key (body ++ [0])) :=
  cert.reject_substitution other same _ (replacePost_ne _ _ _ _ _ _
    (by rw [state]; exact activity_body_extension_ne .state key body))

/-- Newborn law source plant: change the source body of a package image. The
post's original fresh pre-root and id remain exactly those authorized. -/
theorem law_source_substitution_excluded {ob : ObjectiveActivity.Config} {p : Durable} {t t' : T}
    (cert : CheckedCommit ob p t) (other : CheckedCommit ob p t')
    (same : SameAuthorization p cert.intent other.intent)
    (before : List DataWrite) (post : DataWrite) (after : List DataWrite)
    (shape : cert.intent.writes = before ++ post :: after) (key body : List UInt8)
    (package : post.canonicalPostBytes = ObjectiveActivity.image .package key body) :
    other.intent ≠ replacePost cert.intent before post after shape
      (ObjectiveActivity.image .package key (body ++ [0])) :=
  cert.reject_substitution other same _ (replacePost_ne _ _ _ _ _ _
    (by rw [package]; exact activity_body_extension_ne .package key body))

/-- Canonical Book image of a refund from purse 0 to payee 1, asset 0. The
materializer guarantees a decodable Book for either refund amount. -/
def refundCell (book : CanonicalResourceKernel.Book) (amount : Nat) : ObjectiveActivity.BookCell :=
  CellState.materialize CanonicalResourcePageMaterializer.materializer
    (Store.Store.set 0 CanonicalResourceKernel.bookAddress (some (book.applyPosting ⟨0, 1, 0, amount⟩)))

def refundImage (book : CanonicalResourceKernel.Book) (amount : Nat) : List UInt8 :=
  ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry
    (.live ⟨.resourceBook, refundCell book amount⟩)

theorem refund_image_decodes (book : CanonicalResourceKernel.Book) (amount : Nat) :
    ObjectiveActivity.bookOf (refundImage book amount) = some (refundCell book amount) := by
  unfold ObjectiveActivity.bookOf refundImage
  rw [show ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry _ =
    (ResourceBirthCodec.LifecycleImage.codec CanonicalCellRegistry.registry).encode _ from rfl,
    ResourceBirthCodec.LifecycleImage.decode_encode]

theorem refund_amount_ne (book : CanonicalResourceKernel.Book) (amount : Nat) :
    refundImage book (amount + 1) ≠ refundImage book amount := by
  intro same
  have decoded := congrArg ObjectiveActivity.bookOf same
  rw [refund_image_decodes, refund_image_decodes] at decoded
  have balance := congrArg (fun cell : ObjectiveActivity.BookCell =>
    (CanonicalResourceKernel.logicalBook cell.logical).balance 1 0) (Option.some.inj decoded)
  simp [refundCell, CellState.materialize, CanonicalResourceKernel.logicalBook,
    CanonicalResourceKernel.Book.balance, CanonicalResourceKernel.Book.applyPosting,
    DFinsupp.single_apply] at balance

/-- Refund plant: overpay by one using the Book materializer, preserving the
original write's account-book cell and pre-root. -/
theorem refund_substitution_excluded {ob : ObjectiveActivity.Config} {p : Durable} {t t' : T}
    (cert : CheckedCommit ob p t) (other : CheckedCommit ob p t')
    (same : SameAuthorization p cert.intent other.intent)
    (before : List DataWrite) (post : DataWrite) (after : List DataWrite)
    (shape : cert.intent.writes = before ++ post :: after)
    (book : CanonicalResourceKernel.Book) (amount : Nat)
    (refund : post.canonicalPostBytes = refundImage book amount) :
    other.intent ≠ replacePost cert.intent before post after shape (refundImage book (amount + 1)) :=
  cert.reject_substitution other same _ (replacePost_ne _ _ _ _ _ _ (by rw [refund]; exact refund_amount_ne book amount))

/-- Remove the named domain guard without changing any writes or write roots. -/
def dropGuard (intent : DataIntent ResourceBirthCodec.rootBytes) (guard : ReadGuard) :
    DataIntent ResourceBirthCodec.rootBytes :=
  { intent with readGuards := intent.readGuards.filter (fun g => g != guard)
                guardsReadOnly := fun g member => intent.guardsReadOnly g (List.mem_filter.mp member).1 }

theorem dropGuard_ne (intent : DataIntent ResourceBirthCodec.rootBytes) (guard : ReadGuard)
    (member : guard ∈ intent.readGuards) : dropGuard intent guard ≠ intent := by
  intro same
  have guards := congrArg DataIntent.readGuards same
  rw [← guards] at member
  simp [dropGuard] at member

/-- Domain-guard plant: the exact authorized read set cannot lose a guard. -/
theorem domain_guard_substitution_excluded {ob : ObjectiveActivity.Config} {p : Durable} {t t' : T}
    (cert : CheckedCommit ob p t) (other : CheckedCommit ob p t')
    (same : SameAuthorization p cert.intent other.intent) (domainId : Digest)
    (member : ObjectiveActivity.guardAt p.snapshot (ObjectiveActivity.domainCell ob.domain domainId) ∈
      cert.intent.readGuards) :
    other.intent ≠ dropGuard cert.intent
      (ObjectiveActivity.guardAt p.snapshot (ObjectiveActivity.domainCell ob.domain domainId)) :=
  cert.reject_substitution other same _ (dropGuard_ne _ _ member)

/-- Dropping a guard preserves the entire write list, hence all write ids and
pre-roots. The omitted guard is the sole additional substitution surface. -/
theorem dropGuard_writes (intent : DataIntent ResourceBirthCodec.rootBytes) (guard : ReadGuard) :
    (dropGuard intent guard).writes = intent.writes := rfl

#assert_axioms dropGuard_writes

#assert_axioms replacePost_same_pre replacePost_ne CheckedCommit.reject_substitution
#assert_axioms activity_image_decodes activity_body_extension_ne business_write_substitution_excluded
#assert_axioms law_source_substitution_excluded refund_image_decodes refund_amount_ne refund_substitution_excluded
#assert_axioms dropGuard_ne domain_guard_substitution_excluded

end Minidregg.Kernel.ObjectiveAdmissible
