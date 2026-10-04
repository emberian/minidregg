/-
# Kernel.Contracts.Futures — future-indexed certificates over Mini's accepted history

A RE-STATEMENT (not an import) of lean-uwueave's `Uwueave.Preo.Future`
(WorldModel, FutureDecl, CheckedCertificate, futures_not_interchangeable) and of
`Uwueave.JoinHom.summaryFold_iff_joinHom` / `no_count_merge_without_provenance`,
over Mini's own types (scout R2-5, "worth folding in" items 2 and 6).

The Mini world is a replica's materialized `DurableReceiver.Image` (genesis seed
and accepted records) together with its POOL: records already issued (signed,
retained ingress) whose outcome is not installed here. The answer certified is
the accepted height — `NativeHostCodec.height`, the `acceptedCount` a receipt
carries.

* `Extension` — the accepted-history prefix order (same seed, prefix of records).
* `Delivery` — only already-issued records arrive. `delivery_le_extension`.
* `futures_not_interchangeable` — at a quiesced world and a world with one record
  in flight the materialized image is IDENTICAL; the world-indexed quiescence
  certificate is checked at the first, no stability holds at the second, no
  certificate keyed by the image alone can be checked even at the first, and a
  delivery-stable answer is not extension-stable (restriction runs one way).
  Concrete two-record history: `record 1` accepted, `record 2` issued.
* `summaryFold_iff_joinHom` — shipping summaries agrees with recomputing from
  merged evidence iff the summary is a join homomorphism.
* `no_count_merge_without_provenance` — over the set of accepted transaction ids
  two replicas have seen: no function of the two COUNTS gives the merged count.
-/
import Kernel.DurableReceiver
import Kernel.Contracts.Identities
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Card

namespace Minidregg.Kernel.Contracts.Futures

open Minidregg.Kernel.DurableReceiver (Image IntentRecord Seed)
open Minidregg.Kernel.DurableDataIntent (StableEvent TransactionId)

set_option autoImplicit false

/-! ## §1. World models, futures, checked artifacts -/

structure WorldModel where
  World : Type
  State : Type
  Pool : Type
  observe : World → State
  pool : World → Pool

/-- A world index retains the world; its state is computed from it. -/
structure WorldIndex (M : WorldModel) where
  world : M.World

def WorldIndex.state {M : WorldModel} (i : WorldIndex M) : M.State := M.observe i.world

abbrev Future (W : Type) := W → W → Prop

/-- Every reachable future agrees with `w` on `answer`. -/
def FreeTermination {W R : Type} (F : Future W) (answer : W → R) (w : W) : Prop :=
  ∀ v, F w v → answer v = answer w

def KeyCertSound {W K R : Type} (key : W → K) (answer : W → R) (F : Future W)
    (C : K → Prop) : Prop :=
  ∀ w, C (key w) → FreeTermination F answer w

inductive Scope where
  | delivery
  | extension
  deriving DecidableEq, Repr

structure FutureDecl (M : WorldModel) where
  name : String
  scope : Scope
  future : Future M.World

def FutureDecl.IncludedIn {M : WorldModel} (narrow broad : FutureDecl M) : Prop :=
  ∀ ⦃w v⦄, narrow.future w v → broad.future w v

structure CheckedStability {M : WorldModel} (D : FutureDecl M) {R : Type}
    (answer : M.World → R) (index : WorldIndex M) : Prop where
  proof : FreeTermination D.future answer index.world

structure CheckedCertificate {M : WorldModel} (D : FutureDecl M) {K R : Type}
    (answer : M.World → R) (key : M.World → K) (C : K → Prop) (index : WorldIndex M) : Prop where
  accepted : C (key index.world)
  soundForAll : KeyCertSound key answer D.future C

theorem CheckedCertificate.stability {M : WorldModel} {D : FutureDecl M} {K R : Type}
    {answer : M.World → R} {key : M.World → K} {C : K → Prop} {index : WorldIndex M}
    (a : CheckedCertificate D answer key C index) : CheckedStability D answer index :=
  ⟨a.soundForAll index.world a.accepted⟩

/-- Sound direction: a certificate for a broader future serves a contained one. -/
theorem CheckedCertificate.restrict {M : WorldModel} {narrow broad : FutureDecl M}
    {K R : Type} {answer : M.World → R} {key : M.World → K} {C : K → Prop}
    {index : WorldIndex M} (h : narrow.IncludedIn broad)
    (a : CheckedCertificate broad answer key C index) :
    CheckedCertificate narrow answer key C index :=
  ⟨a.accepted, fun w hC v hv => a.soundForAll w hC v (h hv)⟩

/-! ## §2. Mini's accepted history as the world -/

/-- A replica: its materialized image and the issued records not yet installed. -/
structure World where
  image : Image
  pending : List IntentRecord

abbrev miniModel : WorldModel where
  World := World
  State := Image
  Pool := List IntentRecord
  observe := World.image
  pool := World.pending

/-- The accepted-history prefix order. -/
def Extension : FutureDecl miniModel where
  name := "accepted.extension"
  scope := .extension
  future := fun w v => v.image.seed = w.image.seed ∧ w.image.accepted <+: v.image.accepted

/-- Only already-issued records arrive; nothing new is issued. -/
def Delivery : FutureDecl miniModel where
  name := "accepted.delivery"
  scope := .delivery
  future := fun w v => v.image.seed = w.image.seed ∧
    ∃ d, v.image.accepted = w.image.accepted ++ d ∧ (∀ r ∈ d, r ∈ w.pending) ∧
      ∀ r ∈ v.pending, r ∈ w.pending

theorem delivery_le_extension : Delivery.IncludedIn Extension := by
  intro w v h
  obtain ⟨seed, d, appended, _, _⟩ := h
  exact ⟨seed, d, appended.symm⟩

/-- The accepted height (`NativeHostCodec.height`, a receipt's `acceptedCount`). -/
def height (w : World) : Nat := w.image.accepted.length

def Quiesced (w : World) : Prop := w.pending = []

/-- **A quiesced replica's height is delivery-stable** — for every world. -/
theorem quiescence_is_sound : KeyCertSound (fun w : World => w) height Delivery.future Quiesced := by
  intro w quiet v reached
  obtain ⟨_, d, appended, arrived, _⟩ := reached
  have empty : d = [] := by
    cases d with
    | nil => rfl
    | cons r rest =>
        have member := arrived r (List.mem_cons_self ..)
        rw [show w.pending = [] from quiet] at member
        cases member
  simp [height, appended, empty]

/-! ## §3. A two-record history -/

def record (n : Nat) : IntentRecord :=
  { transactionId := ⟨n⟩, writes := [], readGuards := [], nullifiers := [],
    exactCharge := fun _ => 0, event := ⟨0, ⟨0⟩, ⟨n⟩, []⟩, subject := none }

def genesis : Seed := { absentBytes := [], cells := [], available := fun _ => 0 }

/-- `record 1` accepted, nothing in flight. -/
def wQuiesced : World := ⟨⟨genesis, [record 1]⟩, []⟩
/-- `record 1` accepted, `record 2` issued and not yet installed here. -/
def wPending : World := ⟨⟨genesis, [record 1]⟩, [record 2]⟩
/-- Both accepted. -/
def wDelivered : World := ⟨⟨genesis, [record 1, record 2]⟩, []⟩

def quiescedIndex : WorldIndex miniModel := ⟨wQuiesced⟩
def pendingIndex : WorldIndex miniModel := ⟨wPending⟩

theorem not_stable_at_wPending : ¬ FreeTermination Delivery.future height wPending := by
  intro stable
  have moved := stable wDelivered
    ⟨rfl, [record 2], rfl, by simp [wPending], by simp [wDelivered]⟩
  simp [height, wDelivered, wPending] at moved

theorem extension_wQuiesced_wDelivered : Extension.future wQuiesced wDelivered :=
  ⟨rfl, [record 2], rfl⟩

def quiescedCertificate :
    CheckedCertificate Delivery height (fun w : World => w) Quiesced quiescedIndex :=
  ⟨rfl, quiescence_is_sound⟩

/-- No certificate keyed only by the materialized image can be checked at the
quiesced world: the identical image also occurs at `wPending`. -/
theorem state_certificate_cannot_be_checked_at_quiesced :
    ¬ ∃ C : Image → Prop, CheckedCertificate Delivery height World.image C quiescedIndex := by
  rintro ⟨C, a⟩
  exact not_stable_at_wPending (a.soundForAll wPending a.accepted)

/-- **futures_not_interchangeable.** The same materialized image at two worlds;
a world-indexed certificate at one, no stability at the other, no image-keyed
certificate anywhere; delivery ⊆ extension; and the restriction is one-way. -/
theorem futures_not_interchangeable :
    quiescedIndex.state = pendingIndex.state ∧
    CheckedCertificate Delivery height (fun w : World => w) Quiesced quiescedIndex ∧
    ¬ CheckedStability Delivery height pendingIndex ∧
    (¬ ∃ C : Image → Prop, CheckedCertificate Delivery height World.image C quiescedIndex) ∧
    Delivery.IncludedIn Extension ∧
    CheckedStability Delivery height quiescedIndex ∧
    ¬ CheckedStability Extension height quiescedIndex := by
  refine ⟨rfl, quiescedCertificate, fun s => not_stable_at_wPending s.proof,
    state_certificate_cannot_be_checked_at_quiesced, delivery_le_extension,
    quiescedCertificate.stability, ?_⟩
  intro s
  have moved := s.proof wDelivered extension_wQuiesced_wDelivered
  simp [height, wDelivered, quiescedIndex, wQuiesced] at moved

/-! ## §4. Aggregated views: summaries vs evidence -/

section Summary

variable {S R : Type} [SemilatticeSup S] [SemilatticeSup R]

def JoinHom (f : S → R) : Prop := ∀ x y, f (x ⊔ y) = f x ⊔ f y

def joinAll (init : S) (l : List S) : S := l.foldl (· ⊔ ·) init

/-- Shipping summaries and folding them agrees with recomputing from the merged
evidence, for every gossip history. -/
def SummaryFoldAgrees (f : S → R) : Prop :=
  ∀ (l : List S) (init : S), f (joinAll init l) = joinAll (f init) (l.map f)

theorem summaryFold_iff_joinHom (f : S → R) : SummaryFoldAgrees f ↔ JoinHom f := by
  constructor
  · intro h x y
    simpa [joinAll] using h [y] x
  · intro hf l
    induction l with
    | nil => intro init; rfl
    | cons d rest ih =>
        intro init
        have step := ih (init ⊔ d)
        simp only [joinAll, List.foldl_cons, List.map_cons] at step ⊢
        rw [step, hf]

end Summary

/-- The accepted transactions a replica has seen. -/
abbrev Seen := Finset TransactionId

def seen (image : Image) : Seen := (image.accepted.map IntentRecord.transactionId).toFinset

/-- The evidence view composes over history concatenation by join. -/
theorem seen_append (seed : Seed) (a b : List IntentRecord) :
    seen ⟨seed, a ++ b⟩ = seen ⟨seed, a⟩ ⊔ seen ⟨seed, b⟩ := by
  simp [seen, List.toFinset_append, Finset.sup_eq_union]

/-- A filtered evidence view IS a join homomorphism: replicating it is sound. -/
theorem filter_view_joinHom (p : TransactionId → Prop) [DecidablePred p] :
    JoinHom (fun s : Seen => s.filter p) := by
  intro x y
  simp [Finset.sup_eq_union, Finset.filter_union]

def count (s : Seen) : Nat := s.card

def txA : Seen := {⟨1⟩}
def txB : Seen := {⟨2⟩}

theorem count_txA : count txA = 1 := rfl
theorem count_txB : count txB = 1 := rfl
theorem count_same : count (txA ⊔ txA) = 1 := by decide
theorem count_diff : count (txA ⊔ txB) = 2 := by decide

theorem count_not_joinHom : ¬ JoinHom count := by
  intro h
  have := h txA txB
  rw [count_diff, count_txA, count_txB] at this
  simp at this

/-- **No merge of two replicas' accepted counts is exact.** For every candidate
`m`, two scenarios present the same pair of counts with different truths. -/
theorem no_count_merge_without_provenance (m : Nat → Nat → Nat) :
    ∃ x₁ y₁ x₂ y₂ : Seen,
      count x₁ = count x₂ ∧ count y₁ = count y₂ ∧
      count (x₁ ⊔ y₁) ≠ count (x₂ ⊔ y₂) ∧
      ¬ (m (count x₁) (count y₁) = count (x₁ ⊔ y₁) ∧
          m (count x₂) (count y₂) = count (x₂ ⊔ y₂)) := by
  refine ⟨txA, txA, txA, txB, rfl, by rw [count_txA, count_txB], ?_, ?_⟩
  · rw [count_same, count_diff]; decide
  · rintro ⟨h1, h2⟩
    rw [count_txA, count_same] at h1
    rw [count_txA, count_txB, count_diff] at h2
    omega

theorem count_summary_fold_disagrees : ¬ SummaryFoldAgrees count :=
  fun h => count_not_joinHom ((summaryFold_iff_joinHom count).mp h)

#assert_axioms CheckedCertificate.stability
#assert_axioms CheckedCertificate.restrict
#assert_axioms delivery_le_extension
#assert_axioms quiescence_is_sound
#assert_axioms not_stable_at_wPending
#assert_axioms extension_wQuiesced_wDelivered
#assert_axioms state_certificate_cannot_be_checked_at_quiesced
#assert_axioms futures_not_interchangeable
#assert_axioms summaryFold_iff_joinHom
#assert_axioms seen_append
#assert_axioms filter_view_joinHom
#assert_axioms count_same
#assert_axioms count_diff
#assert_axioms count_not_joinHom
#assert_axioms no_count_merge_without_provenance
#assert_axioms count_summary_fold_disagrees

end Minidregg.Kernel.Contracts.Futures
