/-
# Kernel.DurableView — executing against a per-request view of the history

KN2-STORE-OPEN. The opened Store no longer holds the whole decoded history, so
the snapshot it serves carries the journal, consumed nullifiers and history of
the records SINCE ITS CHECKPOINT only (roots, canonical bytes and allowance are
complete: they are state). Before a request runs the executor, the Host reads
the request's FOOTPRINT from the authenticated history — the recorded intent of
every transaction id the request consults (`History.byTx`) and the spent bit of
every nullifier it carries (`History.spent`), each verified at use — and lays
those answers over the served snapshot: a VIEW.

`execute_view` is why that is enough: the shared executor reads exactly the
journal entry of the intent's own transaction id, the roots of its written and
guarded cells, the consumed bit of its own nullifiers and the allowance
(`DurableDataIntent.execute` / `preflight`). Any full snapshot that agrees with
the view on those reads gives the same outcome, and on acceptance the same
roots, canonical bytes and allowance. Nothing else about the full history can
change the result.
-/
import Kernel.DurableDataIntent
import Theory.AssertAxioms

namespace Minidregg.Kernel.DurableView

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

variable {rootBytes : List UInt8 → Digest}

/-- The answers a request's footprint read from the authenticated history:
recorded intents by transaction id (verified at use) and spent bits by
nullifier (verified at use). -/
structure Footprint where
  recorded : List (TransactionId × Intent TransactionId CellId StableNullifier ReplayEnvelope)
  spent : List (StableNullifier × Bool)

/-- The served snapshot with the footprint's answers laid over its suffix
journal and suffix nullifiers. -/
def view (served : DataSnapshot rootBytes) (footprint : Footprint) : DataSnapshot rootBytes where
  model :=
    { served.model with
      journal := served.model.journal ++ footprint.recorded
      consumed := fun nullifier =>
        served.model.consumed nullifier ||
          (footprint.spent.find? (·.1 = nullifier)).any (·.2) }
  canonicalBytes := served.canonicalBytes
  coherent := served.coherent

/-- Outcomes that agree on everything the executor's result exposes to the
Host: the same rejection, the same replayed record, or an acceptance with the
same roots, canonical bytes and allowance. -/
def Agree : Outcome rootBytes → Outcome rootBytes → Prop
  | .accepted a, .accepted b =>
      a.model.roots = b.model.roots ∧ a.canonicalBytes = b.canonicalBytes ∧
        a.model.available = b.model.available
  | .replayed r, .replayed s => r = s
  | .rejected r, .rejected s => r = s
  | _, _ => False

/-- The reads the executor makes, agreeing between a view and a full snapshot. -/
structure AgreesOn (view full : DataSnapshot rootBytes) (intent : DataIntent rootBytes) : Prop where
  roots : view.model.roots = full.model.roots
  bytes : view.canonicalBytes = full.canonicalBytes
  available : view.model.available = full.model.available
  journal : Snapshot.lookupRecorded intent.transactionId view.model.journal =
    Snapshot.lookupRecorded intent.transactionId full.model.journal
  consumed : ∀ nullifier ∈ intent.nullifiers,
    view.model.consumed nullifier = full.model.consumed nullifier

theorem lower_preflight_eq (view full : DataSnapshot rootBytes) (intent : DataIntent rootBytes)
    (agree : AgreesOn view full intent) :
    intent.erase.preflight view.model = intent.erase.preflight full.model := by
  have fresh : intent.erase.nullifiersFreshCheck view.model =
      intent.erase.nullifiersFreshCheck full.model := by
    apply Bool.eq_iff_iff.mpr
    rw [Intent.nullifiersFreshCheck_eq_true_iff, Intent.nullifiersFreshCheck_eq_true_iff]
    constructor
    · intro all nullifier member
      rw [← agree.consumed nullifier (by simpa [DataIntent.erase] using member)]
      exact all nullifier member
    · intro all nullifier member
      rw [agree.consumed nullifier (by simpa [DataIntent.erase] using member)]
      exact all nullifier member
  unfold Intent.preflight Intent.rootsMatchCheck
  rw [fresh, agree.roots, agree.available]

theorem preflight_eq (view full : DataSnapshot rootBytes) (intent : DataIntent rootBytes)
    (agree : AgreesOn view full intent) :
    intent.preflight view = intent.preflight full := by
  unfold DataIntent.preflight DataIntent.readGuardsMatchCheck
  rw [agree.roots, lower_preflight_eq view full intent agree]

/-- **The executor cannot tell a view from the full snapshot.** -/
theorem execute_view (view full : DataSnapshot rootBytes) (intent : DataIntent rootBytes)
    (agree : AgreesOn view full intent) :
    Agree (DurableDataIntent.execute .complete view intent)
      (DurableDataIntent.execute .complete full intent) := by
  unfold DurableDataIntent.execute
  rw [agree.journal, preflight_eq view full intent agree]
  split
  · split <;> exact rfl
  · split
    · exact rfl
    · refine ⟨?_, ?_, ?_⟩
      · show (fun cellId => _) = (fun cellId => _)
        simp only [DataSnapshot.install, Snapshot.install, agree.roots]
      · show (fun cellId => _) = (fun cellId => _)
        simp only [DataSnapshot.install, agree.bytes]
      · show (fun lane => _) = (fun lane => _)
        simp only [DataSnapshot.install, Snapshot.install, agree.available]

/-- The view's journal lookup of a footprint transaction: the served suffix
journal first (newest records), then the verified footprint answer. -/
theorem view_lookup (served : DataSnapshot rootBytes) (footprint : Footprint)
    (transactionId : TransactionId) :
    Snapshot.lookupRecorded transactionId (view served footprint).model.journal =
      (Snapshot.lookupRecorded transactionId served.model.journal).or
        (Snapshot.lookupRecorded transactionId footprint.recorded) := by
  show Snapshot.lookupRecorded transactionId (served.model.journal ++ footprint.recorded) = _
  induction served.model.journal with
  | nil => simp [Snapshot.lookupRecorded]
  | cons head rest ih =>
      obtain ⟨recordedId, recorded⟩ := head
      simp only [List.cons_append, Snapshot.lookupRecorded]
      split <;> simp_all

#assert_axioms preflight_eq
#assert_axioms execute_view
#assert_axioms view_lookup

end Minidregg.Kernel.DurableView
