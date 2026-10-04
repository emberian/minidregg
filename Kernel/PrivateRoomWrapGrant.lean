/-
# Kernel.PrivateRoomWrapGrant -- J-PRIV-1: a member's grant reads only its own wraps

EVIDENCE (lane s9-rooms, 2026-10-04; there was no warm Lean base, so no `lake build`):
 * COMPILED, whole file: `Theory/TypedAuthorization.lean` (`lean` on the one file against
   a Mathlib build, exit 0, no warning, every pinned `#guard_msgs` axiom line matches).
 * CHECKED IN A STANDALONE HARNESS (not committed; it copies the few definitions these
   proofs stand on): every theorem of THIS module, and `fieldOfLabel_label` with the
   `atoms:N` names of `Compiler/CredentialAuthorityEntryCodec`; 0 errors, 0 warnings.
 * AUTHORED, NOT COMPILED: the edits to `Kernel/ResourceObservationAdmission`
   (`atomField`, `contentFieldAt`, `fieldOf .content`, the two reader theorems and the
   changed pole), `Kernel/DeclaredResourceController` (two lines), `Compiler/WorldKindDescriptor`
   (`bound_scope_covers_only_descriptor`), and this module inside the real import closure
   (`lake build Kernel.PrivateRoomWrapGrant`).  Those need a Lean build before this lands.

## What it states

A private room's keys cell (`Kernel.PrivateRoomKeys`) partitions its atoms by
identifier: the WRAP of epoch `e` and generation `g` for member `m` is
`wrapAtomId e g m`, the member's own ENCRYPTION-KEY RECORD is `recordAtomId m`,
and both have LOW 64 bits `m` (`wrapAtomId_halves`, `recordAtomId_halves`).

`CellField.atomsOf low` (Theory/TypedAuthorization) is a sub-field of a content
cell's `body`: the atoms whose identifier has low half `low`.  So a grant whose
`fields` is `some {atomsOf m}` (what `room invite` delegates once the client
moves to it) names, among the keys cell's atoms, exactly member `m`'s wraps and
record -- across EVERY epoch and generation, so no re-delegation at a rotation --
and no other member's, no link, no annotation.

## What it does not state

* That the Rust client can still verify the epoch lineage from a narrowed view.
  It cannot today: `verify_lineage` checks the whole certificate chain over all
  wraps (docs/PRIVATE-ROOMS-DESIGN.txt section 9(c)); the certificates and the
  founder-key transitions need atoms of their own in a region every member's field
  covers.  That is client work, blocked on this module compiling and landing.
* Hiding: a narrowed reader still receives sealed leaves for the atoms it does not
  cover under the flat root (`narrowPacked`); the per-address tree view of
  K-FIELDS-OBSERVE would also hide their count and positions, and is not on main.
-/
import Kernel.PrivateRoomKeys
import Kernel.ResourceObservationAdmission
import Theory.AssertAxioms

namespace Minidregg.Kernel.PrivateRoomWrapGrant

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ResourceObservationAdmission
open Minidregg.Kernel.PrivateRoomKeys

set_option autoImplicit false

/-- The fields of the grant a member holds on its room's keys cell. -/
def memberFields (member : Nat) : Option (Finset CellField) := some {CellField.atomsOf member}

/-- The field of an atom of the keys cell: what `fieldOf .content` gives it. -/
def fieldOfAtom (id : Nat) : CellField := atomField id

theorem fieldOfAtom_wrap (epoch gen member : Nat) (bound : member < 2 ^ 64) :
    fieldOfAtom (wrapAtomId epoch gen member) = .atomsOf member := by
  have halves := (wrapAtomId_halves epoch gen member bound).2
  simp only [fieldOfAtom, atomField]
  rw [halves]

theorem fieldOfAtom_record (member : Nat) (bound : member < 2 ^ 64) :
    fieldOfAtom (recordAtomId member) = .atomsOf member := by
  have halves := (recordAtomId_halves member bound).2
  simp only [fieldOfAtom, atomField]
  rw [halves]

/-- **A member's grant names its own wrap, at every epoch and generation.** -/
theorem grant_names_own_wrap (epoch gen member : Nat) (bound : member < 2 ^ 64) :
    CellField.NamedBy (memberFields member) (fieldOfAtom (wrapAtomId epoch gen member)) := by
  rw [fieldOfAtom_wrap epoch gen member bound]
  exact CellField.namedBy_of_mem (by simp)

/-- ... and its own record, which the keys law lets it write. -/
theorem grant_names_own_record (member : Nat) (bound : member < 2 ^ 64) :
    CellField.NamedBy (memberFields member) (fieldOfAtom (recordAtomId member)) := by
  rw [fieldOfAtom_record member bound]
  exact CellField.namedBy_of_mem (by simp)

/-- **It does not name another member's wrap**, whatever the epoch or generation:
the premises `other < 2^64` and `member ≠ other` have inhabitants (any two distinct
subjects). -/
theorem grant_refuses_other_wrap (epoch gen member other : Nat)
    (otherBound : other < 2 ^ 64) (different : member ≠ other) :
    ¬ CellField.NamedBy (memberFields member) (fieldOfAtom (wrapAtomId epoch gen other)) := by
  rw [fieldOfAtom_wrap epoch gen other otherBound]
  rintro ⟨outer, isMember, covers⟩
  simp only [Finset.mem_singleton] at isMember
  subst isMember
  simp [CellField.covers, CellField.isAtoms] at covers
  exact different covers

/-- ... nor another member's record. -/
theorem grant_refuses_other_record (member other : Nat)
    (otherBound : other < 2 ^ 64) (different : member ≠ other) :
    ¬ CellField.NamedBy (memberFields member) (fieldOfAtom (recordAtomId other)) := by
  rw [fieldOfAtom_record other otherBound]
  rintro ⟨outer, isMember, covers⟩
  simp only [Finset.mem_singleton] at isMember
  subst isMember
  simp [CellField.covers, CellField.isAtoms] at covers
  exact different covers

/-- The control: the founder's grant (`none`: every field) reads every wrap, so the
narrowing is the member's grant's, not the cell's. -/
theorem founder_grant_names_every_wrap (epoch gen member : Nat) :
    CellField.NamedBy none (fieldOfAtom (wrapAtomId epoch gen member)) := True.intro

/-- A member's grant narrows the room's whole-body grant (so `room invite` can derive
it from the founder's authority) and does not widen it. -/
theorem member_grant_narrows_body (member : Nat) :
    CellField.SetNarrows (memberFields member) (some {CellField.body}) := by
  intro field isMember
  simp only [Finset.mem_singleton] at isMember
  subst isMember
  exact CellField.namedBy_atomsOf_of_body member (by simp)

theorem body_grant_does_not_narrow_member (member : Nat) :
    ¬ CellField.SetNarrows (some {CellField.body}) (memberFields member) := by
  intro narrows
  obtain ⟨outer, isMember, covers⟩ := narrows .body (by simp)
  simp only [Finset.mem_singleton] at isMember
  subst isMember
  simp [CellField.covers, CellField.isAtoms] at covers

#assert_axioms fieldOfAtom_wrap
#assert_axioms fieldOfAtom_record
#assert_axioms grant_names_own_wrap
#assert_axioms grant_names_own_record
#assert_axioms grant_refuses_other_wrap
#assert_axioms grant_refuses_other_record
#assert_axioms founder_grant_names_every_wrap
#assert_axioms member_grant_narrows_body
#assert_axioms body_grant_does_not_narrow_member

end Minidregg.Kernel.PrivateRoomWrapGrant
