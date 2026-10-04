/-
# Kernel.ObjectiveActivityGate — only the kernel activity writes its coordinates

Every cell of the kernel activity (`Kernel.ObjectiveActivityCell`: an activity
record, an answer slot, an object's declared state, a published package, an
object's record) sits at a coordinate at or above `reservedBase = 2^256`
(`ObjectiveActivityCell.coordinate_reserved`). No resource birth may choose such
an id (`CanonicalCellRegistry.UserInitial`), and every id another receiver
derives is a 256-bit digest. Neither fact stops another receiver's intent from
naming such an id in a write, though. The protection is this gate: an intent from
outside the kernel activity that writes any cell in the protected space is
refused by name, `RejectReason.protectedWrite cell`.

The gate runs on every durable commit. `NativeHost.Config.sourceGate` calls it
for every source facet except the kernel activity's own typed facet
(`ControlFacet.objectiveActivity`), and the receiving loop and the replay walk both judge
through that source gate (`DurableReceiverIO.Loaded.judge`).
So the protected coordinates change only under a turn the kernel activity
admitted. `Kernel.ObjectiveCheckpointInvariant` builds the invariant
`stored_checkpoints_typed` on this, and `Kernel.ObjectiveActivityGateRoute.derived_route`
proves the replay walk's judge admits only these two kinds of record.
-/
import Kernel.DurableDataIntent
import Kernel.ObjectiveActivityCell
import Kernel.ResourceBirthController

namespace Minidregg.Kernel.ObjectiveActivityGate

open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-- A cell in the kernel activity's protected coordinate space. -/
def Protected (cell : CellId) : Prop := ObjectiveActivityCell.reservedBase ≤ cell.value

instance (cell : CellId) : Decidable (Protected cell) := by unfold Protected; infer_instance

/-- The first protected cell a list of writes names. -/
def firstProtected : List DataWrite → Option CellId
  | [] => none
  | write :: rest => if Protected write.cellId then some write.cellId else firstProtected rest

/-- **The ordinary gate.** An intent from outside the kernel activity is
refused, naming the cell, if it writes any protected cell. -/
def ordinaryGate {rootBytes : List UInt8 → Digest} (intent : DataIntent rootBytes) :
    Except RejectReason Unit :=
  match firstProtected intent.writes with
  | some cell => .error (.protectedWrite cell)
  | none => .ok ()

theorem firstProtected_none_iff (writes : List DataWrite) :
    firstProtected writes = none ↔ ∀ write ∈ writes, ¬ Protected write.cellId := by
  induction writes with
  | nil => simp [firstProtected]
  | cons write rest ih =>
    unfold firstProtected
    by_cases hit : Protected write.cellId
    · simp only [hit, if_true, reduceCtorEq, false_iff]
      intro all
      exact all write (List.mem_cons_self ..) hit
    · rw [if_neg hit, ih, List.forall_mem_cons]
      exact ⟨fun rest' => ⟨hit, rest'⟩, And.right⟩

theorem firstProtected_some {writes : List DataWrite} {cell : CellId}
    (found : firstProtected writes = some cell) : Protected cell ∧ ∃ write ∈ writes, write.cellId = cell := by
  induction writes with
  | nil => simp [firstProtected] at found
  | cons write rest ih =>
    unfold firstProtected at found
    by_cases hit : Protected write.cellId
    · simp only [hit, if_true, Option.some.injEq] at found
      subst found
      exact ⟨hit, write, List.mem_cons_self .., rfl⟩
    · simp only [hit, if_false] at found
      obtain ⟨isProtected, other, member, named⟩ := ih found
      exact ⟨isProtected, other, List.mem_cons_of_mem _ member, named⟩

/-- The gate admits exactly the intents that write no protected cell. -/
theorem ordinaryGate_ok_iff {rootBytes : List UInt8 → Digest} (intent : DataIntent rootBytes) :
    ordinaryGate intent = .ok () ↔ ∀ write ∈ intent.writes, ¬ Protected write.cellId := by
  unfold ordinaryGate
  rw [← firstProtected_none_iff]
  cases firstProtected intent.writes <;> simp

/-- **A write to a protected cell is refused by name.** Whatever else the intent
writes, the gate refuses it with `protectedWrite`, naming a protected cell the
intent writes. -/
theorem ordinaryGate_refuses {rootBytes : List UInt8 → Digest} {intent : DataIntent rootBytes}
    {write : DataWrite} (writes : write ∈ intent.writes) (isProtected : Protected write.cellId) :
    ∃ cell, ordinaryGate intent = .error (.protectedWrite cell) ∧ Protected cell ∧
      ∃ named ∈ intent.writes, named.cellId = cell := by
  unfold ordinaryGate
  cases found : firstProtected intent.writes with
  | none =>
    exact absurd isProtected ((firstProtected_none_iff _).mp found write writes)
  | some cell => exact ⟨cell, rfl, firstProtected_some found⟩

/-- Every activity coordinate is protected: a write to any activity cell (any
role, any key, any deployment domain) from outside the kernel activity is
refused. -/
theorem coordinate_refused {rootBytes : List UInt8 → Digest} {intent : DataIntent rootBytes}
    {write : DataWrite} (writes : write ∈ intent.writes) (domain : Digest)
    (role : ObjectiveActivityCell.Role) (key : List UInt8)
    (at_ : write.cellId = ⟨ObjectiveActivityCell.coordinate domain role key⟩) :
    ∃ cell, ordinaryGate intent = .error (.protectedWrite cell) :=
  let ⟨cell, refused, _⟩ := ordinaryGate_refuses writes
    (by rw [at_]; exact ObjectiveActivityCell.coordinate_reserved domain role key)
  ⟨cell, refused⟩

/-- An installed intent the gate admitted leaves every protected cell's bytes
as they were. -/
theorem ordinary_install_protected {rootBytes : List UInt8 → Digest} (before : DataSnapshot rootBytes)
    {intent : DataIntent rootBytes} (admitted : ordinaryGate intent = .ok ()) {cell : CellId}
    (isProtected : Protected cell) :
    (DataSnapshot.install before intent).canonicalBytes cell = before.canonicalBytes cell := by
  rw [DataSnapshot.install_canonicalBytes]
  have none : DataSnapshot.lookupPostBytes cell intent.writes = none := by
    have clear := (ordinaryGate_ok_iff intent).mp admitted
    generalize intent.writes = writes at clear
    induction writes with
    | nil => rfl
    | cons write rest ih =>
      unfold DataSnapshot.lookupPostBytes
      have other : write.cellId ≠ cell := fun same => clear write (List.mem_cons_self ..) (same ▸ isProtected)
      simp only [other, if_false]
      exact ih (fun w member => clear w (List.mem_cons_of_mem _ member))
  rw [none]; rfl

/-- Whatever the schedule, an execution of an intent the gate admitted leaves
every protected cell's bytes as they were (accepted, crashed after install,
replayed or rejected alike). -/
theorem ordinary_execute_protected {rootBytes : List UInt8 → Digest} (schedule : DurableCommitProtocol.Schedule)
    (before : DataSnapshot rootBytes) {intent : DataIntent rootBytes}
    (admitted : ordinaryGate intent = .ok ()) {cell : CellId} (isProtected : Protected cell) :
    ((execute schedule before intent).storeAfter before).canonicalBytes cell = before.canonicalBytes cell := by
  rcases execute_no_partial_data_commit schedule before intent with same | installed
  · rw [same]
  · rw [installed]; exact ordinary_install_protected before admitted isProtected

/-! ## The widened physical-post law is the kernel activity's alone

`ResourceBirthController.Concrete.PhysicalPostLaw` (the law every receiver's
prepared writes obey) admits the registry's retired image, but only at a
protected coordinate: that is how the kernel activity retires an ended record or a
settled slot. The two theorems below tie that widening to this gate. The
retired image is admitted only at protected coordinates, and an intent the
ordinary gate admits writes none, so for every intent from outside the kernel
activity the law is exactly the live-cell law it was before the widening. -/

open Minidregg.Compiler.ResourceBirthCodec (LifecycleImage)
open Minidregg.Kernel.ResourceBirthController.Concrete (PhysicalPostLaw Registry)

/-- **The retired image is admitted only at a protected coordinate.** -/
theorem physicalPostLaw_retired_protected {deployment : Minidregg.Compiler.CanonicalCellRegistry.Deployment}
    {write : DataWrite} (law : PhysicalPostLaw deployment write)
    (retired : (LifecycleImage.codec Registry).decode write.canonicalPostBytes = some .retired) :
    Protected write.cellId := by
  unfold PhysicalPostLaw at law
  rw [retired] at law
  exact law

/-- **Outside the kernel activity the law is the live-cell law.** A write of an
intent the ordinary gate admitted that obeys `PhysicalPostLaw` decodes to a live
cell obeying its registry kind's law at its id; the retired image is not
admitted to anything but the kernel activity. -/
theorem ordinary_physicalPostLaw_live {rootBytes : List UInt8 → Digest} {intent : DataIntent rootBytes}
    (admitted : ordinaryGate intent = .ok ())
    {deployment : Minidregg.Compiler.CanonicalCellRegistry.Deployment} {write : DataWrite}
    (member : write ∈ intent.writes) (law : PhysicalPostLaw deployment write) :
    ∃ cell, (LifecycleImage.codec Registry).decode write.canonicalPostBytes = some (.live cell) ∧
      Minidregg.Compiler.CanonicalCellRegistry.CellLaw deployment write.cellId.value cell := by
  have clear := (ordinaryGate_ok_iff intent).mp admitted write member
  unfold PhysicalPostLaw at law
  split at law
  · rename_i cell decoded
    exact ⟨cell, decoded, law⟩
  · exact absurd law clear
  · exact law.elim

/-! ## Tooth

A forged ordinary intent that writes the first protected coordinate (the
smallest cell id an activity cell can have) is refused, naming that cell. If
the gate is relaxed to admit the write, this theorem fails to check. -/

/-- The forged write: one post image at `reservedBase`. -/
def forgedWrite : DataWrite := ⟨⟨ObjectiveActivityCell.reservedBase⟩, ⟨0⟩, ⟨0⟩, []⟩

/-- The forged intent, under a constant root function. -/
def forgedIntent : DataIntent (fun _ => ⟨0⟩) where
  transactionId := ⟨1⟩
  writes := [forgedWrite]
  readGuards := []
  nullifiers := []
  exactCharge := 0
  event := ⟨0, ⟨0⟩, ⟨0⟩, []⟩
  subject := none
  postRootsBound := by intro write member; simp at member; subst member; rfl
  guardsReadOnly := by intro guard member; simp at member

theorem forged_protected_write_refused :
    ordinaryGate forgedIntent = .error (.protectedWrite ⟨ObjectiveActivityCell.reservedBase⟩) := by
  decide

/-- The gate admits an ordinary write below the protected space. -/
def ordinaryWrite : DataWrite := ⟨⟨7⟩, ⟨0⟩, ⟨0⟩, []⟩

def ordinaryIntent : DataIntent (fun _ => ⟨0⟩) where
  transactionId := ⟨1⟩
  writes := [ordinaryWrite]
  readGuards := []
  nullifiers := []
  exactCharge := 0
  event := ⟨0, ⟨0⟩, ⟨0⟩, []⟩
  subject := none
  postRootsBound := by intro write member; simp at member; subst member; rfl
  guardsReadOnly := by intro guard member; simp at member

theorem ordinary_write_admitted : ordinaryGate ordinaryIntent = .ok () := by decide

#assert_axioms firstProtected_none_iff
#assert_axioms firstProtected_some
#assert_axioms ordinaryGate_ok_iff
#assert_axioms ordinaryGate_refuses
#assert_axioms coordinate_refused
#assert_axioms ordinary_install_protected
#assert_axioms ordinary_execute_protected
#assert_axioms physicalPostLaw_retired_protected
#assert_axioms ordinary_physicalPostLaw_live
#assert_axioms forged_protected_write_refused
#assert_axioms ordinary_write_admitted
end Minidregg.Kernel.ObjectiveActivityGate
