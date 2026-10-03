/- Source context is a projection of participant-admitted observations, never a
new history store or a grant. The native caller obtains current signed reads;
these functions select from those reads and retain their exact dependencies.
A started invocation keeps its prior projection even if a later read changes.
External summaries/proposals are authored data, not certified model truth. -/
import Kernel.DocumentHistory
import Compiler.StreamCell

namespace Minidregg.Kernel.ResidentContextProjection
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ContentResource
open Minidregg.Compiler
set_option autoImplicit false

structure SourcePin where
  source : Nat
  root : Digest
  deriving DecidableEq, Repr

structure Dependency where
  source : SourcePin
  element : Nat
  revision : Nat
  parent : Option Nat
  predecessor : Option Nat
  payload : Digest
  deriving DecidableEq, Repr

structure Row where
  dependency : Dependency
  bytes : List UInt8
  deriving DecidableEq, Repr

/-- Exact current placement, including the preceding element in kernel order.
Removing/moving the row does not erase its immutable source identity. -/
def documentRows (source : SourcePin) (store : ContentStore) (document : DocumentId)
    (marks : List (MarkId × MarkRecord)) : List Row :=
  let order := documentOrder store document
  (DocumentHistory.lines store document marks).filterMap fun (element, line) =>
    match line with
    | .atom _ (some record) _ =>
      if record.tombstonedAt.isSome then none else
        some ⟨⟨source, element.digest.value, record.revision.digest.value,
          (parentOf store element).map (fun parent => parent.digest.value),
          (DocumentHistory.predecessor order element).map (fun before => before.digest.value),
          StreamCell.payloadDigest record.bodyBytes⟩, record.bodyBytes⟩
    | _ => none

/-- Bounded stable greedy selection in the source's order. Oversize rows are
omitted, not truncated into another authored value. Coverage is explicit. -/
def takeBudget : Nat → Nat → List Row → List Row
  | 0, _, _ => []
  | _, _, [] => []
  | count + 1, budget, row :: rest =>
    if row.bytes.length ≤ budget then
      row :: takeBudget count (budget - row.bytes.length) rest
    else takeBudget (count + 1) budget rest

def byteCount (rows : List Row) : Nat := (rows.map (fun row => row.bytes.length)).sum

theorem takeBudget_from_source (count budget : Nat) (rows : List Row) (row : Row)
    (selected : row ∈ takeBudget count budget rows) : row ∈ rows := by
  induction rows generalizing count budget with
  | nil => cases count <;> simp [takeBudget] at selected
  | cons head rest induction =>
    cases count with
    | zero => simp [takeBudget] at selected
    | succ count =>
      simp only [takeBudget] at selected
      split at selected
      · rcases List.mem_cons.mp selected with same | tail
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons.mpr (Or.inr (induction _ _ tail))
      · exact List.mem_cons.mpr (Or.inr (induction _ _ selected))

theorem takeBudget_count (count budget : Nat) (rows : List Row) :
    (takeBudget count budget rows).length ≤ count := by
  induction rows generalizing count budget with
  | nil => cases count <;> simp [takeBudget]
  | cons head rest induction =>
    cases count with
    | zero => simp [takeBudget]
    | succ count =>
      simp only [takeBudget]
      split
      · simpa using Nat.succ_le_succ (induction count (budget - head.bytes.length))
      · exact induction (count + 1) budget

theorem takeBudget_bytes (count budget : Nat) (rows : List Row) :
    byteCount (takeBudget count budget rows) ≤ budget := by
  induction rows generalizing count budget with
  | nil => cases count <;> simp [takeBudget, byteCount]
  | cons head rest induction =>
    cases count with
    | zero => simp [takeBudget, byteCount]
    | succ count =>
      simp only [takeBudget]
      split
      · rename_i fits
        have bound := induction count (budget - head.bytes.length)
        simp only [byteCount, List.map_cons, List.sum_cons] at *
        omega
      · exact induction (count + 1) budget

structure Projection where
  rows : List Row
  sourceRows : Nat
  omittedRows : Nat
  maxRows : Nat
  maxBytes : Nat
  deriving DecidableEq, Repr

def project (maxRows maxBytes : Nat) (rows : List Row) : Projection :=
  let selected := takeBudget maxRows maxBytes rows
  ⟨selected, rows.length, rows.length - selected.length, maxRows, maxBytes⟩

/-- Root pins are intentionally conservative: any selected source-cell change,
including placement/annotations, invalidates derived memory. No content-only
fingerprint can resurrect a quarantined or moved source. The roots must come
from the caller's CURRENT admitted observations, not cached controller journals. -/
def supported (dependencies current : List SourcePin) : Bool :=
  dependencies.all fun pin => decide (pin ∈ current)

theorem supported_iff (dependencies current : List SourcePin) :
    supported dependencies current = true ↔ ∀ pin ∈ dependencies, pin ∈ current := by
  simp [supported, List.all_eq_true]

theorem missing_source_invalidates (dependencies current : List SourcePin) (pin : SourcePin)
    (used : pin ∈ dependencies) (missing : pin ∉ current) :
    supported dependencies current = false := by
  cases result : supported dependencies current with
  | false => rfl
  | true => exact False.elim (missing ((supported_iff _ _).mp result pin used))

/-- Existing uncertain/started request custody owns this option. A fresh
projection changes subsequent work; it never substitutes already-started input. -/
def invocationInput (started : Option Projection) (fresh : Projection) : Projection :=
  started.getD fresh

theorem started_keeps_exact_context (started fresh : Projection) :
    invocationInput (some started) fresh = started := rfl

theorem unstarted_uses_current_context (fresh : Projection) :
    invocationInput none fresh = fresh := rfl

/-- Proposal source support and target base must still be current before a
native typed proposal is authored. Passing this is NOT authority or effect
landing: ordinary signed prepare/approve/submit/recovery remains mandatory. -/
def proposalCurrent (support current : List SourcePin) (target : SourcePin) : Bool :=
  supported support current && decide (target ∈ current)

theorem stale_proposal_refused (support current : List SourcePin) (target : SourcePin)
    (stale : target ∉ current) : proposalCurrent support current target = false := by
  simp [proposalCurrent, stale]

#assert_axioms takeBudget_from_source
#assert_axioms takeBudget_count
#assert_axioms takeBudget_bytes
#assert_axioms supported_iff
#assert_axioms missing_source_invalidates
#assert_axioms started_keeps_exact_context
#assert_axioms unstarted_uses_current_context
#assert_axioms stale_proposal_refused
end Minidregg.Kernel.ResidentContextProjection
