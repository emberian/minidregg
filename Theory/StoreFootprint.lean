/- One typed-store field footprint, shared by native and world-defined layouts. -/
import Theory.Store
import Theory.TypedAuthorization

namespace Minidregg.Theory.StoreFootprint
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

/-- The addresses among `candidates` one write changed. -/
def changedWithin {L : Layout.{0, 0, 0}} (candidates : Finset (Address L)) (pre post : Store L) :
    Finset (Address L) :=
  candidates.filter fun address => pre address ≠ post address

/-- Every address one write changed. -/
def changed {L : Layout.{0, 0, 0}} (pre post : Store L) : Finset (Address L) :=
  changedWithin (pre.support ∪ post.support) pre post

theorem mem_changed {L : Layout.{0, 0, 0}} {pre post : Store L} {address : Address L} :
    address ∈ changed pre post ↔ pre address ≠ post address := by
  constructor
  · intro member; exact (Finset.mem_filter.mp member).2
  · intro different
    refine Finset.mem_filter.mpr ⟨?_, different⟩
    by_cases before : pre address = none
    · exact Finset.mem_union_right _ (DFinsupp.mem_support_iff.mpr (by
        rw [before] at different; exact fun h => different h.symm))
    · exact Finset.mem_union_left _ (DFinsupp.mem_support_iff.mpr before)

/-- Any candidate set outside which nothing changed finds exactly the changed
addresses. The controller's candidates are the patch's write footprint
(`Patch.run_frame`), so it never scans the whole cell. -/
theorem changedWithin_eq_changed {L : Layout.{0, 0, 0}} {candidates : Finset (Address L)}
    {pre post : Store L} (frame : ∀ address, address ∉ candidates → pre address = post address) :
    changedWithin candidates pre post = changed pre post := by
  ext address
  rw [mem_changed]
  constructor
  · intro member; exact (Finset.mem_filter.mp member).2
  · intro different
    exact Finset.mem_filter.mpr ⟨by_contra fun outside => different (frame address outside),
      different⟩

/-- Excluding a source-owned non-effect address commutes with the exact
patch-footprint reduction. Used by hiding ratchets, not by caller claims. -/
theorem changedWithin_filtered {L : Layout.{0, 0, 0}} {candidates : Finset (Address L)}
    {pre post : Store L} (frame : ∀ address, address ∉ candidates → pre address = post address)
    (keep : Address L → Prop) [DecidablePred keep] :
    changedWithin (candidates.filter keep) pre post = (changed pre post).filter keep := by
  rw [← changedWithin_eq_changed frame]
  ext address
  simp only [changedWithin, Finset.mem_filter]
  tauto

/-- What a write changed, field by field, over a set of changed addresses: the
touched fields, and on each the summed change of its numeric values
(`amount`; absence counts as `0`). -/
def footprintOf {L : Layout.{0, 0, 0}} (changedSet : Finset (Address L))
    (field : Address L → CellField)
    (amount : (address : Address L) → L.Value address.1 → Int) (pre post : Store L) :
    Footprint :=
  let value := fun (store : Store L) (address : Address L) =>
    match store address with | some v => amount address v | none => 0
  { touched := changedSet.image field
    delta := fun named => ∑ address ∈ changedSet.filter (fun a => field a = named),
      (value post address - value pre address) }

/-- The footprint of a write: `footprintOf` at every changed address. -/
def footprint {L : Layout.{0, 0, 0}} (field : Address L → CellField)
    (amount : (address : Address L) → L.Value address.1 → Int) (pre post : Store L) :
    Footprint :=
  footprintOf (changed pre post) field amount pre post

/-- A field is touched exactly when some address of it changed. -/
theorem footprint_touched_exact {L : Layout.{0, 0, 0}} (field : Address L → CellField)
    (amount : (address : Address L) → L.Value address.1 → Int) (pre post : Store L)
    (named : CellField) :
    named ∈ (footprint field amount pre post).touched ↔
      ∃ address, pre address ≠ post address ∧ field address = named := by
  simp only [footprint, footprintOf, Finset.mem_image, mem_changed]

end Minidregg.Theory.StoreFootprint
