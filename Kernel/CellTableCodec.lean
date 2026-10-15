/-
# Kernel.CellTableCodec -- the cell table's one encoding (the World checkpoint's cells sub-codec)

STATE-AT's `CellTable` (`Kernel.CellTable`) as bytes: the entry count, then
`(id, bytes)` in strictly ascending id order (`CellTable.entries`).  A decode of
any other order or a repeated id refuses (`decode_refuses_unordered`), so each
table has exactly one encoding; `cellTableStream`'s roundtrip is
`CellTable.ofList_entries`, an equation.
-/
import Kernel.CellTable
import Compiler.Tower256ConcreteBackend
import Theory.AssertAxioms

namespace Minidregg.Kernel.CellTableCodec

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

/-- Strictly ascending ids. -/
def ascending : List (Nat × List UInt8) → Bool
  | a :: b :: rest => decide (a.1 < b.1) && ascending (b :: rest)
  | _ => true

theorem ascending_of_pairwise :
    ∀ (l : List (Nat × List UInt8)), (l.map Prod.fst).Pairwise (· < ·) → ascending l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
      simp only [List.map_cons, List.pairwise_cons, List.mem_cons, List.mem_map] at h
      simp only [ascending, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨h.1 b.1 (.inl rfl), ascending_of_pairwise (b :: rest) ?_⟩
      simpa [List.pairwise_cons] using h.2

/-- The entry list: a count, then `(id, bytes)` pairs. -/
def entryStream : StreamCodec (List (Nat × List UInt8)) :=
  StreamCodec.list (StreamCodec.product StreamCodec.nat bytesStream)

/-- A table's wire entries. -/
def wireOf (t : CellTable) : List (Nat × List UInt8) := t.entries.map fun e => (e.1.value, e.2)

/-- The table of wire entries. -/
def ofWire (l : List (Nat × List UInt8)) : CellTable := CellTable.ofList (l.map fun e => (⟨e.1⟩, e.2))

theorem ofWire_wireOf (t : CellTable) : ofWire (wireOf t) = t := by
  unfold ofWire wireOf
  rw [List.map_map, show ((fun e : Nat × List UInt8 => ((⟨e.1⟩ : DurableDataIntent.CellId), e.2)) ∘
      fun e : DurableDataIntent.CellId × List UInt8 => (e.1.value, e.2)) = _root_.id from funext fun _ => rfl,
    List.map_id]
  exact CellTable.ofList_entries t

theorem wireOf_ascending (t : CellTable) : ascending (wireOf t) = true := by
  apply ascending_of_pairwise
  unfold wireOf
  rw [List.map_map]
  exact CellTable.entries_ascending t

/-- **The cells sub-codec.** -/
def cellTableStream : StreamCodec CellTable where
  encode t := entryStream.encode (wireOf t)
  decodePrefix bytes := do
    let (entries, rest) ← entryStream.decodePrefix bytes
    if ascending entries then some (ofWire entries, rest) else none
  decodePrefix_encode := by
    intro t suffix
    simp only [entryStream.decodePrefix_encode, Option.bind_eq_bind, Option.bind_some,
      wireOf_ascending, if_true, ofWire_wireOf]

/-- **One encoding per table**: an entry list out of ascending id order refuses. -/
theorem decode_refuses_unordered {entries : List (Nat × List UInt8)} (unordered : ascending entries = false)
    (suffix : List UInt8) :
    cellTableStream.decodePrefix (entryStream.encode entries ++ suffix) = none := by
  simp [cellTableStream, entryStream.decodePrefix_encode, unordered]

#assert_axioms ofWire_wireOf
#assert_axioms decode_refuses_unordered

end Minidregg.Kernel.CellTableCodec
