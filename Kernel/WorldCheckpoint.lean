/-
# Kernel.WorldCheckpoint -- the checkpoint IS a World (FD-1 step 1, World v1)

`Image` is what a checkpoint stores of the World: its present cells as a
`CellTable` of canonical encodings (`encodeCell`), its WHOLE system cell
(`WorldSystemCodec.systemStream`: journal, head = (height, log chain),
retired, parent, spent, allowance -- the meter).  Nothing else: the Host debits
the derived turn's charge (the FD-1 charge switch), so the World's meter IS the
Host's.

* `toWorld_ofWorld`: a World's image reads back as exactly that World.
* `imageStream`: the bytes; `imageStream_roundtrip`.
* A table entry that is not a live cell (the absent or retired image, or bytes
  that do not decode) refuses (`toWorld`: absent and retired cells are not
  stored -- a retired cell is its `retired` system row).
-/
import Kernel.CellTableCodec
import Kernel.WorldSystemCodec
import Kernel.DeployedBridge
import Theory.AssertAxioms

namespace Minidregg.Kernel.WorldCheckpoint

open Minidregg.Theory.Store
open Minidregg.Theory.ResourceCost (Lane Charge)
open Minidregg.Kernel.World
open Minidregg.Kernel.CellTableCodec (cellTableStream)
open Minidregg.Kernel.WorldSystemCodec (DSys systemStream)
open Minidregg.Kernel.DeployedBridge (deployedR encodeCell decodeCell)
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent (TransactionId)

set_option autoImplicit false

abbrev DWorld := World deployedR TransactionId Theory.TypedAuthorization.Digest

/-- `none` is the zero of a sparse slot; whether a slot is present is decidable
without comparing what it holds. -/
local instance optionNeZeroDecidable {α : Type} (x : Option α) : Decidable (x ≠ 0) :=
  decidable_of_iff (x.isSome = true) (by cases x <;> simp [Option.isSome] <;> rfl)

theorem mem_of_lookup {l : List (Nat × List UInt8)} {k : Nat} {b : List UInt8}
    (h : l.lookup k = some b) : (k, b) ∈ l := by
  obtain ⟨l₁, l₂, rfl, _⟩ := List.lookup_eq_some_iff.mp h
  simp

theorem lookup_of_mem :
    ∀ {l : List (Nat × List UInt8)} {k : Nat} {b : List UInt8},
      (l.map Prod.fst).Nodup → (k, b) ∈ l → l.lookup k = some b
  | [], _, _, _, m => by cases m
  | (k', b') :: rest, k, b, nodup, m => by
      rcases List.mem_cons.mp m with e | m'
      · cases e; simp [List.lookup]
      · have notin : k' ∉ rest.map Prod.fst := (List.nodup_cons.mp nodup).1
        have ne : k ≠ k' := fun e => notin (e ▸ List.mem_map.mpr ⟨(k, b), m', rfl⟩)
        have : (k == k') = false := by simp [ne]
        simp only [List.lookup, this]
        exact lookup_of_mem (List.nodup_cons.mp nodup).2 m'

/-- The checkpointed World. -/
structure Image where
  cells : CellTable
  system : Store DSys

/-- A live cell's bytes, and only a live cell's. -/
def decodeLive (bytes : List UInt8) : Option (Cell deployedR) :=
  match decodeCell bytes with
  | some (some cell) => some cell
  | _ => none

theorem decodeLive_encodeCell (cell : Cell deployedR) : decodeLive (encodeCell (some cell)) = some cell := by
  simp [decodeLive, Minidregg.Kernel.DeployedBridge.bridge_decode_total_on_registry]

/-- The present cells' table. -/
def tableOf (cells : Cells deployedR) : CellTable :=
  Std.ExtTreeMap.ofList ((cells.support.sort (· ≤ ·)).map fun c => (c, encodeCell (cells c))) compare

/-- Insert one decoded entry. -/
def insertLive (acc : Option (Cells deployedR)) (entry : Nat × List UInt8) : Option (Cells deployedR) :=
  acc.bind fun cells => (decodeLive entry.2).map fun cell => DFinsupp.update cells entry.1 (some cell)

/-- The cells of a table: every entry a live cell, else none. -/
def cellsOfTable (t : CellTable) : Option (Cells deployedR) :=
  t.toList.foldl insertLive (some 0)

theorem foldl_insertLive_none :
    ∀ (l : List (Nat × List UInt8)), l.foldl insertLive none = none
  | [] => rfl
  | _ :: rest => by simp only [List.foldl_cons, insertLive, Option.bind_none]; exact foldl_insertLive_none rest

/-- What folding live entries does at one id: the decoded entry, if the id is a
key of the (distinct-keyed) list, else what was there. -/
theorem foldl_insertLive_apply :
    ∀ (l : List (Nat × List UInt8)) (acc : Cells deployedR) (out : Cells deployedR),
      (l.map Prod.fst).Nodup → l.foldl insertLive (some acc) = some out →
        ∀ c, out c = match l.lookup c with
          | some bytes => decodeLive bytes
          | none => acc c
  | [], acc, out, _, h, c => by
      simp only [List.foldl_nil, Option.some.injEq] at h
      subst h; rfl
  | (k, bytes) :: rest, acc, out, nodup, h, c => by
      simp only [List.foldl_cons, insertLive, Option.bind_some] at h
      cases hd : decodeLive bytes with
      | none =>
          rw [hd] at h
          simp only [Option.map_none] at h
          rw [foldl_insertLive_none] at h; cases h
      | some cell =>
          rw [hd] at h
          simp only [Option.map_some] at h
          have nodup' : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp nodup).2
          have notin : k ∉ rest.map Prod.fst := (List.nodup_cons.mp nodup).1
          rw [foldl_insertLive_apply rest _ out nodup' h c]
          by_cases e : c = k
          · subst e
            have : rest.lookup c = none := by
              cases hl : rest.lookup c with
              | none => rfl
              | some b =>
                  exact absurd (List.mem_map.mpr ⟨(c, b), mem_of_lookup hl, rfl⟩) notin
            simp [List.lookup, this, hd, DFinsupp.coe_update]
          · have ne : (c == k) = false := by simp [e]
            simp only [List.lookup, ne]
            cases rest.lookup c with
            | some b => rfl
            | none => simp [DFinsupp.coe_update, Function.update_of_ne e]

theorem getElem?_tableOf (cells : Cells deployedR) (c : Nat) :
    (tableOf cells)[c]? = if c ∈ cells.support then some (encodeCell (cells c)) else none := by
  unfold tableOf
  split
  · rename_i m
    apply Std.ExtTreeMap.getElem?_ofList_of_mem (Nat.compare_eq_eq.mpr rfl)
    · rw [List.pairwise_map]
      exact (Finset.sort_nodup cells.support (· ≤ ·)).imp fun ne e => ne (Nat.compare_eq_eq.mp e)
    · exact List.mem_map.mpr ⟨c, (Finset.mem_sort _).mpr m, rfl⟩
  · rename_i m
    apply Std.ExtTreeMap.getElem?_ofList_of_contains_eq_false
    apply Bool.eq_false_iff.mpr
    intro found
    obtain ⟨⟨k, v⟩, mem, e⟩ := List.mem_map.mp (List.contains_iff_mem.mp found)
    simp only at e
    subst e
    obtain ⟨c', m', e'⟩ := List.mem_map.mp mem
    simp only [Prod.mk.injEq] at e'
    exact m (e'.1 ▸ (Finset.mem_sort _).mp m')

/-- `lookup` on a table's entries is the table's lookup. -/
theorem lookup_toList (t : CellTable) (c : Nat) : t.toList.lookup c = t[c]? := by
  cases held : t[c]? with
  | some v =>
      have mem := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr held
      have nodup : (t.toList.map Prod.fst).Nodup := by
        have := Std.ExtTreeMap.distinct_keys_toList (t := t)
        rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
        exact this.imp fun h e => h (by rw [e]; exact Nat.compare_eq_eq.mpr rfl)
      exact lookup_of_mem nodup mem
  | none =>
      cases hl : t.toList.lookup c with
      | none => rfl
      | some v =>
          have := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp (mem_of_lookup hl)
          rw [held] at this; cases this

/-- **A World's cells read back from their table.** -/
theorem foldl_insertLive_some :
    ∀ (l : List (Nat × List UInt8)) (acc : Cells deployedR),
      (∀ p ∈ l, (decodeLive p.2).isSome = true) → ∃ out, l.foldl insertLive (some acc) = some out
  | [], acc, _ => ⟨acc, rfl⟩
  | (k, bytes) :: rest, acc, live => by
      obtain ⟨cell, hc⟩ := Option.isSome_iff_exists.mp (live (k, bytes) (by simp))
      simp only [List.foldl_cons, insertLive, Option.bind_some, hc, Option.map_some]
      exact foldl_insertLive_some rest _ fun p m => live p (by simp [m])

theorem mem_support_some {cells : Cells deployedR} {c : Nat} (m : c ∈ cells.support) :
    ∃ cell, cells c = some cell := by
  have := DFinsupp.mem_support_iff.mp m
  cases h : cells c with
  | none => exact absurd h this
  | some cell => exact ⟨cell, rfl⟩

/-- **A World's cells read back from their table.** -/
theorem cellsOfTable_tableOf (cells : Cells deployedR) : cellsOfTable (tableOf cells) = some cells := by
  have nodup : ((tableOf cells).toList.map Prod.fst).Nodup := by
    have := Std.ExtTreeMap.distinct_keys_toList (t := tableOf cells)
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact this.imp fun h e => h (by rw [e]; exact Nat.compare_eq_eq.mpr rfl)
  have live : ∀ p ∈ (tableOf cells).toList, (decodeLive p.2).isSome = true := by
    rintro ⟨k, v⟩ m
    have held := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp m
    rw [getElem?_tableOf] at held
    split at held
    · rename_i sup
      obtain ⟨cell, hc⟩ := mem_support_some sup
      cases held
      simp [hc, decodeLive_encodeCell]
    · cases held
  obtain ⟨out, hout⟩ := foldl_insertLive_some _ 0 live
  unfold cellsOfTable
  rw [hout]
  congr 1
  apply DFinsupp.ext
  intro c
  rw [foldl_insertLive_apply _ 0 out nodup hout c, lookup_toList, getElem?_tableOf]
  by_cases sup : c ∈ cells.support
  · obtain ⟨cell, hc⟩ := mem_support_some sup
    simp [sup, hc, decodeLive_encodeCell]
  · have : cells c = none := by
      by_contra h
      exact sup (DFinsupp.mem_support_iff.mpr h)
    simp only [sup, if_false, this]
    rfl

/-- The World's image. -/
def ofWorld (w : DWorld) : Image := ⟨tableOf w.cells, w.system⟩

/-- The World an image holds; refuses a table entry that is not a live cell. -/
def toWorld (image : Image) : Option DWorld :=
  (cellsOfTable image.cells).map fun cells => ⟨cells, image.system⟩

theorem toWorld_ofWorld (w : DWorld) : toWorld (ofWorld w) = some w := by
  simp [toWorld, ofWorld, cellsOfTable_tableOf]

/-! ## Bytes -/

def imageStream : StreamCodec Image :=
  StreamCodec.xmap (StreamCodec.product cellTableStream systemStream)
    (fun image => (image.cells, image.system))
    (fun pair => ⟨pair.1, pair.2⟩)
    (by intro image; cases image; rfl)

theorem imageStream_roundtrip (image : Image) (suffix : List UInt8) :
    imageStream.decodePrefix (imageStream.encode image ++ suffix) = some (image, suffix) :=
  imageStream.decodePrefix_encode image suffix

#assert_axioms toWorld_ofWorld
#assert_axioms imageStream_roundtrip

end Minidregg.Kernel.WorldCheckpoint
