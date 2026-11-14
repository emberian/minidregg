/-
# Kernel.AuthoritySpaceGate -- only authority cells are written in the authority space

The entry cells of the credential authority store sit at or above
`ProtectedCell.authorityBase = 2^257` (`Compiler.CredentialAuthorityEntry.entryId`). Three facts
keep that space the authority's alone:

* no resource birth chooses an id there: a user birth is below `2^256`
  (`CanonicalCellRegistry.UserInitial`, `userInitial_below_authority_space`);
* the object kernel's protected coordinates are below it (`ObjectiveActivityGate.Protected` is
  `[2^256, 2^257)`, `protected_not_in_space`), so the ordinary gate's refusals and the object
  kernel's own range are what they were;
* **this gate**, which runs on every durable commit for every facet (`NativeHost.Config.sourceGate`):
  an intent that writes, at or above `2^257`, anything but a live cell of the `.authority` kind is
  refused by name, `RejectReason.authoritySpaceWrite cell`.

Who may write a cell of the `.authority` kind is the registry's law class
(`CanonicalCellRegistry.Kind.lawClass .authority = kernelOnly authorityWriters`), judged by the
Receiver on every write (`ReceivingLaw.kernelOnly_writers`): the sixteen authority writer families
and no other. `space_write_by_authority_writer` joins the two.
-/
module

public import Kernel.DurableDataIntent
public import Kernel.ReceivingLaw
public import Kernel.ObjectiveActivityGate
public import Compiler.CredentialAuthorityLayout

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Kernel.AuthoritySpaceGate

open Minidregg.Kernel.DurableDataIntent
open Minidregg.Compiler
open Minidregg.Compiler.CredentialAuthorityLayout (decodeCell encodeCell decodeCell_canonical
  decodeCell_encodeCell)
open Minidregg.Compiler.CanonicalCellRegistry (Kind FamilyId)
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-- A cell in the authority space. -/
def InSpace (cell : CellId) : Prop := ProtectedCell.authorityBase ≤ cell.value

instance (cell : CellId) : Decidable (InSpace cell) := by unfold InSpace; infer_instance

/-- A write the gate refuses: in the authority space, and its post image is not a live authority
cell (a cell of another kind, a retired image, undecodable bytes). -/
def Foreign (write : DataWrite) : Prop :=
  InSpace write.cellId ∧ (decodeCell write.canonicalPostBytes).isNone = true

instance (write : DataWrite) : Decidable (Foreign write) := by unfold Foreign; infer_instance

/-- **The authority-space gate.** An intent is refused, naming the cell, if it writes anything
but a live authority cell in the authority space. -/
def gate {rootBytes : List UInt8 → Digest} (intent : DataIntent rootBytes) :
    Except RejectReason Unit :=
  match intent.writes.find? fun write => decide (Foreign write) with
  | some write => .error (.authoritySpaceWrite write.cellId)
  | none => .ok ()

/-- The gate admits exactly the intents whose every write in the authority space is a live
authority cell. -/
theorem gate_ok_iff {rootBytes : List UInt8 → Digest} (intent : DataIntent rootBytes) :
    gate intent = .ok () ↔ ∀ write ∈ intent.writes, ¬ Foreign write := by
  unfold gate
  cases found : intent.writes.find? fun write => decide (Foreign write) with
  | none =>
      simp only [true_iff]
      intro write member
      simpa using List.find?_eq_none.mp found write member
  | some write =>
      simp only [reduceCtorEq, false_iff]
      intro clear
      exact clear write (List.mem_of_find?_eq_some found) (by simpa using List.find?_some found)

/-- **The keystone.** Every write of an admitted intent at or above `2^257` is the canonical
live image of a cell of the authority kind. -/
theorem admitted_space_write_is_authority {rootBytes : List UInt8 → Digest}
    {intent : DataIntent rootBytes} (admitted : gate intent = .ok ())
    {write : DataWrite} (member : write ∈ intent.writes) (inSpace : InSpace write.cellId) :
    ∃ cell, write.canonicalPostBytes = encodeCell cell := by
  have clear := (gate_ok_iff intent).mp admitted write member
  cases decoded : decodeCell write.canonicalPostBytes with
  | none => exact absurd ⟨inSpace, by rw [decoded]; rfl⟩ clear
  | some cell => exact ⟨cell, (decodeCell_canonical decoded).symm⟩

/-- **Anything else there is refused by name**: an intent with a write in the authority space
whose post is not a live authority cell is refused `authoritySpaceWrite`, naming a cell of the
authority space the intent writes. -/
theorem foreign_write_refused {rootBytes : List UInt8 → Digest} {intent : DataIntent rootBytes}
    {write : DataWrite} (member : write ∈ intent.writes) (foreign : Foreign write) :
    ∃ cell, gate intent = .error (.authoritySpaceWrite cell) ∧ InSpace cell ∧
      ∃ named ∈ intent.writes, named.cellId = cell := by
  unfold gate
  cases found : intent.writes.find? fun write => decide (Foreign write) with
  | none => exact absurd foreign (by simpa using List.find?_eq_none.mp found write member)
  | some first =>
      have isForeign : Foreign first := by simpa using List.find?_some found
      exact ⟨first.cellId, rfl, isForeign.1, first, List.mem_of_find?_eq_some found, rfl⟩

/-- Satisfiable pole: a write of a live authority cell passes, wherever it sits. -/
theorem authority_write_not_foreign (cellId : CellId) (pre post : Digest)
    (cell : CredentialAuthorityEntry.PhysicalCell) :
    ¬ Foreign ⟨cellId, pre, post, encodeCell cell⟩ := by
  intro foreign
  have decoded := foreign.2
  rw [show (⟨cellId, pre, post, encodeCell cell⟩ : DataWrite).canonicalPostBytes = encodeCell cell from rfl,
    decodeCell_encodeCell] at decoded
  cases decoded

/-- A write below the authority space is never refused by this gate. -/
theorem below_not_foreign {write : DataWrite} (below : write.cellId.value < ProtectedCell.authorityBase) :
    ¬ Foreign write := fun foreign => absurd below (Nat.not_lt.mpr foreign.1)

/-- **Only an authority writer family writes the authority space.** A write of an intent the
gate admitted, in the authority space, is of the authority kind; and in a patch the Receiver
judged fault-free, a write whose kind is the authority kind is by a family the registry names in
`authorityWriters` (`ReceivingLaw.kernelOnly_writers`). -/
theorem space_write_by_authority_writer {S : Type} (laws : ReceivingLaw.Laws S) (family : FamilyId)
    (state : S) {writes : List DataWrite}
    {step : (write : DataWrite) → write ∈ writes → Option CanonicalPolicyAdmission.PolicyStepContext}
    (lawful : ReceivingLaw.lawFault laws family state writes step = none)
    {write : DataWrite} (member : write ∈ writes)
    (kindEq : laws.kindOf state write = some Kind.authority) :
    family ∈ CanonicalCellRegistry.authorityWriters :=
  ReceivingLaw.kernelOnly_writers laws family state lawful member kindEq rfl

/-- **No user birth is in the authority space**: a user birth's id is below `2^256`. -/
theorem userInitial_below_authority_space {deployment : CanonicalCellRegistry.Deployment}
    {cellId : Nat} {cell : Theory.CellRegistry.PackedCell CanonicalCellRegistry.registry}
    (admitted : CanonicalCellRegistry.UserInitial deployment cellId cell) : ¬ InSpace ⟨cellId⟩ := by
  intro inSpace
  have below := admitted.2
  have bases := ProtectedCell.reservedBase_le_authorityBase
  change ProtectedCell.authorityBase ≤ cellId at inSpace
  omega

/-- **The object kernel's range is disjoint from the authority space**: a protected cell is
below `2^257`, so the ordinary gate's refusals are untouched and this gate never refuses a
protected coordinate. -/
theorem protected_not_in_space {cell : CellId} (isProtected : ObjectiveActivityGate.Protected cell) :
    ¬ InSpace cell := fun inSpace => absurd isProtected.2 (Nat.not_lt.mpr inSpace)

/-- Every protected family's coordinate (an activity cell, a seat cell) is still protected by
the ordinary gate and is outside the authority space. -/
theorem coordinate_still_protected (spec : ProtectedCell.Spec) (domain : Digest) (role : spec.Role)
    (key : List UInt8) :
    ObjectiveActivityGate.Protected ⟨ProtectedCell.coordinate spec domain role key⟩ ∧
      ¬ InSpace ⟨ProtectedCell.coordinate spec domain role key⟩ :=
  ⟨ObjectiveActivityGate.coordinate_protected spec domain role key,
    protected_not_in_space (ObjectiveActivityGate.coordinate_protected spec domain role key)⟩

/-- Every authority entry is in the authority space, outside the object kernel's range. -/
theorem entry_in_space (address : Theory.Store.Address Theory.CredentialAuthorityState.layout) :
    InSpace ⟨CredentialAuthorityEntry.entryCellId address⟩ ∧
      ¬ ObjectiveActivityGate.Protected ⟨CredentialAuthorityEntry.entryCellId address⟩ :=
  ⟨CredentialAuthorityEntry.entryCellId_authority address,
    fun isProtected => protected_not_in_space isProtected
      (CredentialAuthorityEntry.entryCellId_authority address)⟩

/-! ## Executed poles -/

/-- An intent with one write: `bytes` at `cellId`, under a constant root function. -/
def intentOf (cellId : CellId) (bytes : List UInt8) : DataIntent (fun _ => ⟨0⟩) where
  transactionId := ⟨1⟩
  writes := [⟨cellId, ⟨0⟩, ⟨0⟩, bytes⟩]
  readGuards := []
  nullifiers := []
  exactCharge := 0
  event := ⟨0, ⟨0⟩, ⟨0⟩, []⟩
  subject := none
  postRootsBound := by intro written member; simp at member; subst member; rfl
  guardsReadOnly := by intro guard member; simp at member

/-- An ordinary intent writing nothing (the never-used image) at `2^257 + 7` is refused, naming
the cell. -/
theorem forged_empty_refused :
    gate (intentOf ⟨ProtectedCell.authorityBase + 7⟩ []) =
      .error (.authoritySpaceWrite ⟨ProtectedCell.authorityBase + 7⟩) := by
  decide

/-- A live cell of another kind (role tag 1, content) born in the authority space is refused,
naming the cell. -/
theorem forged_other_kind_refused :
    gate (intentOf ⟨ProtectedCell.authorityBase + 7⟩ [68, 82, 2, 1, 68, 82, 1, 1, 0]) =
      .error (.authoritySpaceWrite ⟨ProtectedCell.authorityBase + 7⟩) := by
  decide

/-- An ordinary write below both spaces is admitted. -/
theorem ordinary_admitted : gate (intentOf ⟨7⟩ []) = .ok () := by decide

/-- An activity or seat coordinate is still refused by the ordinary gate: the first protected
cell is refused as it was (`ObjectiveActivityGate.forged_protected_write_refused`), and the last
cell below the authority space is protected. -/
theorem last_protected_cell : ObjectiveActivityGate.Protected ⟨ProtectedCell.authorityBase - 1⟩ := by
  decide

#assert_axioms gate_ok_iff
#assert_axioms admitted_space_write_is_authority
#assert_axioms foreign_write_refused
#assert_axioms space_write_by_authority_writer
#assert_axioms userInitial_below_authority_space
#assert_axioms coordinate_still_protected
#assert_axioms entry_in_space
#assert_axioms forged_empty_refused
#assert_axioms forged_other_kind_refused
#assert_axioms ordinary_admitted
#assert_axioms last_protected_cell

end Minidregg.Kernel.AuthoritySpaceGate
