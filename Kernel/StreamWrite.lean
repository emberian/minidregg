/-
# Kernel.StreamWrite -- a stream append's physical writes, and reading entries back

An append writes two cells and nothing else (`Compiler.StreamCell`):

* the head, one guarded rewrite of a bounded value (`Head {binding, count, tail}`);
* one fresh entry cell at `entryCellId head n` (`entryWrite`, expected pre the
  fresh root, so a second append planned at the same position cannot commit).

Neither write's bytes depend on any earlier entry (`entryWrite_bytes`,
`headCellBytes` are functions of the head and the new entry alone).  Both the
fleet receiver (`Kernel.FleetTurn`) and resource-transaction `append` targets
(`Kernel.DeclaredResourceController`) emit exactly these writes.

Reading is by position: entry `n` is observed at its derived cell and accepted
only when it names this head and this position (`entryAt`, `mem_window`).
-/
import Kernel.ResourceBirthController

namespace Minidregg.Kernel.StreamWrite

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.StreamCell
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment

def headCell (head : Head) : PackedCell Registry :=
  ⟨.stream, materialize headMaterializer (headStore head)⟩

def entryCell (entry : Entry) : PackedCell Registry :=
  ⟨.streamEntry, materialize entryMaterializer (entryStore entry)⟩

/-- The canonical bytes of a head cell: a function of the head value alone. -/
def headCellBytes (head : Head) : List UInt8 :=
  LifecycleImage.bytes Registry (.live (headCell head))

/-- The one fresh entry cell of an append. -/
def entryWrite (entry : Entry) : DataWrite where
  cellId := ⟨entryCellId entry.head entry.sequence⟩
  expectedPre := physicalRoot (.fresh : LifecycleImage Registry)
  exactPost := physicalRoot (.live (entryCell entry))
  canonicalPostBytes := LifecycleImage.bytes Registry (.live (entryCell entry))

theorem entryWrite_root (entry : Entry) :
    rootBytes (entryWrite entry).canonicalPostBytes = (entryWrite entry).exactPost := rfl

/-- The head write of an append whose head cell is `cellId`, from the image
the head cell holds now (`fresh` before a fleet topic's first entry). -/
def headWrite (cellId : Nat) (pre : LifecycleImage Registry) (post : Head) : DataWrite where
  cellId := ⟨cellId⟩
  expectedPre := physicalRoot pre
  exactPost := physicalRoot (.live (headCell post))
  canonicalPostBytes := headCellBytes post

theorem headWrite_root (cellId : Nat) (pre : LifecycleImage Registry) (post : Head) :
    rootBytes (headWrite cellId pre post).canonicalPostBytes = (headWrite cellId pre post).exactPost :=
  rfl

/-- **`entryWrite_bytes`.** The entry write is the entry's cell, at the cell its
head and position derive, expected fresh: nothing of the stream's earlier
entries enters it. -/
theorem entryWrite_bytes (entry : Entry) :
    (entryWrite entry).cellId = ⟨entryCellId entry.head entry.sequence⟩ ∧
    (entryWrite entry).expectedPre = physicalRoot (.fresh : LifecycleImage Registry) ∧
    (entryWrite entry).canonicalPostBytes = LifecycleImage.bytes Registry (.live (entryCell entry)) :=
  ⟨rfl, rfl, rfl⟩

/-! ## Reading entries back -/

/-- Entry `sequence` of the stream whose head is cell `headCellId`: observed
at its derived cell under the registry law, and accepted only when it names
this head and this position. -/
def entryAt (deployment : Deployment) (directory : Directory Nat Registry)
    (headCellId sequence : Nat) : Option Entry := do
  let observed ← ResourceBirthController.Concrete.observeCell deployment directory
    (entryCellId headCellId sequence) .streamEntry
  let entry ← entryOf observed.payload.logical
  if entry.head = headCellId ∧ entry.sequence = sequence then some entry else none

/-- The entries at positions `start … start + count - 1` that the head has
recorded, in order. A position the head counts but whose cell does not read
back ends nothing silently: it is simply absent from the window, and
`mem_window` says exactly which entries are present. -/
def window (deployment : Deployment) (directory : Directory Nat Registry)
    (headCellId : Nat) (head : Head) (start count : Nat) : List (Nat × Entry) :=
  (List.range' start count).filterMap fun sequence =>
    if 1 ≤ sequence ∧ sequence ≤ head.count then
      (entryAt deployment directory headCellId sequence).map fun entry => (sequence, entry)
    else none

/-- **`mem_window`.** A window holds exactly the recorded positions in range
whose entry cell reads back as this head's entry at that position. -/
theorem mem_window (deployment : Deployment) (directory : Directory Nat Registry)
    (headCellId : Nat) (head : Head) (start count sequence : Nat) (entry : Entry) :
    (sequence, entry) ∈ window deployment directory headCellId head start count ↔
      start ≤ sequence ∧ sequence < start + count ∧ 1 ≤ sequence ∧ sequence ≤ head.count ∧
        entryAt deployment directory headCellId sequence = some entry := by
  simp only [window, List.mem_filterMap, List.mem_range'_1]
  constructor
  · rintro ⟨k, ⟨lo, hi⟩, found⟩
    split at found
    · rename_i bounds
      cases h : entryAt deployment directory headCellId k with
      | none => simp [h] at found
      | some e =>
          simp [h] at found
          obtain ⟨rfl, rfl⟩ := found
          exact ⟨lo, hi, bounds.1, bounds.2, h⟩
    · simp at found
  · rintro ⟨lo, hi, one, upper, found⟩
    exact ⟨sequence, ⟨lo, hi⟩, by simp [one, upper, found]⟩

/-- An entry read back names its head and position. -/
theorem entryAt_bound {deployment : Deployment} {directory : Directory Nat Registry}
    {headCellId sequence : Nat} {entry : Entry}
    (found : entryAt deployment directory headCellId sequence = some entry) :
    entry.head = headCellId ∧ entry.sequence = sequence := by
  unfold entryAt at found
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at found
  obtain ⟨_, _, e, _, bound⟩ := found
  split at bound
  · rename_i ok; cases bound; exact ok
  · cases bound

/-- info: 'Minidregg.Kernel.StreamWrite.entryWrite_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entryWrite_bytes
/-- info: 'Minidregg.Kernel.StreamWrite.mem_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mem_window
/-- info: 'Minidregg.Kernel.StreamWrite.entryAt_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entryAt_bound

end Minidregg.Kernel.StreamWrite
