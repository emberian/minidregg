/-
# Theory.ReactiveReceipt — receipt-driven reactive projections

This file is the candidate-independent reactive UI nucleus.  A committed
transition produces one `ReceiptDelta` with an exact footprint and a frame
theorem.  A view is a pure `Lens` whose dependency set is part of its semantics.
The cache may reuse an old projection precisely when the receipt footprint is
disjoint from those dependencies; otherwise it reprojects from the committed
post-state.

The point is to make the state transition, history event, invalidation event,
and replay cursor one semantic path.  Animation clocks, local drafts, transports,
renderers, and proof systems remain separate interpreters of this core.
-/
import Mathlib.Data.Finset.Empty
import Mathlib.Tactic

namespace Minidregg.Theory.ReactiveReceipt

universe u v w

/-! ## Authoritative committed deltas -/

/-- A logical store.  Concrete realizations may use sparse maps, authenticated
tries, databases, or encrypted state; the semantic reading is total. -/
abbrev Store (Key : Type u) (Value : Type v) := Key → Value

/-- The exact committed state transition carried by a receipt.  `frame` is the
anti-ghost law: every key outside the declared footprint is unchanged. -/
structure ReceiptDelta
    {Key : Type u} {Value : Type v} [DecidableEq Key]
    (pre post : Store Key Value) where
  touched : Finset Key
  frame : ∀ key, key ∉ touched → post key = pre key

/-- A transition attempt indexed by its pre-state.  Rejection contains no
post-state field at all, so its observable post-state is definitionally `pre`.
Only `committed` carries a new state and a receipt delta. -/
inductive Attempt
    {Key : Type u} {Value : Type v} [DecidableEq Key]
    (Receipt Error : Type w) (pre : Store Key Value) where
  | rejected (error : Error)
  | committed (post : Store Key Value) (receipt : Receipt)
      (delta : ReceiptDelta pre post)

/-- The state visible after an attempt. -/
def Attempt.post
    {Key : Type u} {Value : Type v} [DecidableEq Key]
    {Receipt Error : Type w} {pre : Store Key Value} :
    Attempt Receipt Error pre → Store Key Value
  | .rejected _ => pre
  | .committed post _ _ => post

@[simp] theorem Attempt.rejected_atomic
    {Key : Type u} {Value : Type v} [DecidableEq Key]
    {Receipt Error : Type w} {pre : Store Key Value} (error : Error) :
    (Attempt.rejected (Receipt := Receipt) (pre := pre) error).post = pre :=
  rfl

/-! ## Pure dependency-indexed projections -/

/-- A pure view of committed state with an exact finite dependency set.
`locality` says agreement on those keys is sufficient for equal output. -/
structure Lens (Key : Type u) (Value : Type v) (View : Type w)
    [DecidableEq Key] where
  dependencies : Finset Key
  project : Store Key Value → View
  locality : ∀ left right,
    (∀ key ∈ dependencies, left key = right key) →
      project left = project right

/-- A receipt dirties a lens exactly when their semantic footprints intersect. -/
def Lens.Dirty
    {Key : Type u} {Value : Type v} {View : Type w} [DecidableEq Key]
    (lens : Lens Key Value View) {pre post : Store Key Value}
    (delta : ReceiptDelta pre post) : Prop :=
  (lens.dependencies ∩ delta.touched).Nonempty

/-- The load-bearing incremental-render theorem: a clean receipt cannot change
the projection.  This is stronger than trusting an event tag or a cache key; it
uses the receipt's frame law and the lens's declared locality. -/
theorem Lens.project_eq_of_clean
    {Key : Type u} {Value : Type v} {View : Type w} [DecidableEq Key]
    (lens : Lens Key Value View) {pre post : Store Key Value}
    (delta : ReceiptDelta pre post) (clean : ¬ lens.Dirty delta) :
    lens.project post = lens.project pre := by
  apply lens.locality
  intro key hdep
  exact delta.frame key (by
    intro htouched
    exact clean ⟨key, Finset.mem_inter.mpr ⟨hdep, htouched⟩⟩)

/-- A cached view with proof that it is the projection of one committed state. -/
structure Cache
    {Key : Type u} {Value : Type v} {View : Type w} [DecidableEq Key]
    (lens : Lens Key Value View) (state : Store Key Value) where
  rendered : View
  correct : rendered = lens.project state

/-- Advance a cache across a committed receipt.  Dirty views are reprojected;
clean views reuse the exact old value, justified by `project_eq_of_clean`. -/
def Cache.advance
    {Key : Type u} {Value : Type v} {View : Type w} [DecidableEq Key]
    {lens : Lens Key Value View} {pre post : Store Key Value}
    (cache : Cache lens pre) (delta : ReceiptDelta pre post) : Cache lens post := by
  letI : Decidable (lens.Dirty delta) := by
    unfold Lens.Dirty
    infer_instance
  exact if dirty : lens.Dirty delta then
    ⟨lens.project post, rfl⟩
  else
    ⟨cache.rendered,
      cache.correct.trans (lens.project_eq_of_clean delta dirty).symm⟩

@[simp] theorem Cache.advance_clean_reuses
    {Key : Type u} {Value : Type v} {View : Type w} [DecidableEq Key]
    {lens : Lens Key Value View} {pre post : Store Key Value}
    (cache : Cache lens pre) (delta : ReceiptDelta pre post)
    (clean : ¬ lens.Dirty delta) :
    (cache.advance delta).rendered = cache.rendered := by
  simp [Cache.advance, clean]

@[simp] theorem Cache.advance_dirty_reprojects
    {Key : Type u} {Value : Type v} {View : Type w} [DecidableEq Key]
    {lens : Lens Key Value View} {pre post : Store Key Value}
    (cache : Cache lens pre) (delta : ReceiptDelta pre post)
    (dirty : lens.Dirty delta) :
    (cache.advance delta).rendered = lens.project post := by
  simp [Cache.advance, dirty]

/-! ## Local drafts are not committed state -/

/-- Explicit two-tier UI state.  `committed` is receipt-backed semantic state;
`local` is an ephemeral camera/draft/animation value. -/
structure Draft (Committed Local : Type*) where
  committed : Committed
  ephemeral : Local

/-- A local edit cannot mutate committed semantic state. -/
def Draft.editLocal {Committed Local : Type*}
    (draft : Draft Committed Local) (edit : Local → Local) :
    Draft Committed Local :=
  { draft with ephemeral := edit draft.ephemeral }

@[simp] theorem Draft.editLocal_committed
    {Committed Local : Type*} (draft : Draft Committed Local)
    (edit : Local → Local) :
    (draft.editLocal edit).committed = draft.committed :=
  rfl

/-! ## Witness-cursor snapshots -/

/-- A snapshot names a point in verified history, not pixels. -/
structure WitnessCursor (Digest : Type*) where
  height : Nat
  stateRoot : Digest
  receiptHead : Option Digest
  deriving DecidableEq

/-- Honest status of a rehydrated projection.  An approximate reconstruction is
a different constructor and therefore cannot masquerade as live or replayed. -/
inductive Liveness where
  | live
  | replayedDeterministic
  | reconstructedApproximate
  deriving DecidableEq, Repr

/-- Classify a cursor relative to the current head and a root-verified replay
predicate. -/
def classifyCursor {Digest : Type*} [DecidableEq Digest]
    (cursor head : WitnessCursor Digest)
    (replayable : WitnessCursor Digest → Bool) : Liveness :=
  if cursor = head then
    .live
  else if replayable cursor then
    .replayedDeterministic
  else
    .reconstructedApproximate

theorem classifyCursor_live_iff
    {Digest : Type*} [DecidableEq Digest]
    (cursor head : WitnessCursor Digest)
    (replayable : WitnessCursor Digest → Bool) :
    classifyCursor cursor head replayable = .live ↔ cursor = head := by
  by_cases h : cursor = head
  · simp [classifyCursor, h]
  · by_cases hr : replayable cursor = true <;>
      simp [classifyCursor, h, hr]

theorem classifyCursor_replayed_iff
    {Digest : Type*} [DecidableEq Digest]
    (cursor head : WitnessCursor Digest)
    (replayable : WitnessCursor Digest → Bool) :
    classifyCursor cursor head replayable = .replayedDeterministic ↔
      cursor ≠ head ∧ replayable cursor = true := by
  by_cases h : cursor = head <;> simp [classifyCursor, h]

/-! ## Causally bound reactions and visible affordances -/

/-- A reactive request names the exact committed receipt that caused it.  This
prevents an event-driven action from becoming an ambient poll result with lost
provenance.  Replay protection remains the responsibility of the request's
nonce/nullifier domain. -/
structure CausalRequest (ReceiptId Request : Type*) where
  cause : ReceiptId
  ordinal : Nat
  request : Request

/-- A visible affordance is a request template; its enabled state is a pure
projection of the SAME authorization predicate the executor will re-check. -/
structure Affordance (Request Label : Type*) where
  label : Label
  request : Request

structure ProjectedAffordance (Request Label : Type*) where
  affordance : Affordance Request Label
  enabled : Bool

def Affordance.project {Request Label : Type*}
    (affordance : Affordance Request Label) (authorized : Request → Bool) :
    ProjectedAffordance Request Label :=
  ⟨affordance, authorized affordance.request⟩

@[simp] theorem Affordance.project_enabled_iff
    {Request Label : Type*} (affordance : Affordance Request Label)
    (authorized : Request → Bool) :
    (affordance.project authorized).enabled = true ↔
      authorized affordance.request = true :=
  Iff.rfl

/-! ## Small teeth -/

namespace Example

abbrev Key := Fin 3
abbrev State := Store Key Nat

def before : State := fun key => key.val + 10

def afterUnrelated : State
  | ⟨0, _⟩ => 10
  | ⟨1, _⟩ => 11
  | ⟨2, _⟩ => 99

def unrelatedDelta : ReceiptDelta before afterUnrelated where
  touched := {2}
  frame := by
    intro key h
    fin_cases key <;> simp_all [before, afterUnrelated]

def sumFirstTwo : Lens Key Nat Nat where
  dependencies := {0, 1}
  project := fun state => state 0 + state 1
  locality := by
    intro left right h
    rw [h 0 (by simp), h 1 (by simp)]

theorem unrelated_receipt_keeps_projection :
    sumFirstTwo.project afterUnrelated = sumFirstTwo.project before := by
  apply sumFirstTwo.project_eq_of_clean unrelatedDelta
  simp [Lens.Dirty, sumFirstTwo, unrelatedDelta]

def goodCache : Cache sumFirstTwo before :=
  ⟨21, rfl⟩

theorem unrelated_receipt_reuses_cache :
    (goodCache.advance unrelatedDelta).rendered = goodCache.rendered := by
  apply Cache.advance_clean_reuses
  simp [Lens.Dirty, sumFirstTwo, unrelatedDelta]

theorem rejected_transition_keeps_state :
    (Attempt.rejected (Receipt := Unit) (pre := before) "denied").post = before :=
  rfl

end Example

end Minidregg.Theory.ReactiveReceipt
