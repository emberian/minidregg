import Kernel.ApplicationShareIssueSource
import Kernel.ResourceBirthReceiver

namespace Minidregg.Kernel.ApplicationShareIssueAtomicBirth
open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ApplicationShareIssueSource
set_option autoImplicit false

/-- Substitute one already admitted fresh allocation's final image. The
identifier and pre-root are preserved; only the source-derived post changes. -/
def replace (original final : DataWrite) (writes : List DataWrite) : List DataWrite :=
  writes.map fun write => if write.cellId = original.cellId then final else write

theorem ids_preserved (original final : DataWrite) (writes : List DataWrite)
    (same : final.cellId = original.cellId) :
    (replace original final writes).map DataWrite.cellId = writes.map DataWrite.cellId := by
  induction writes with
  | nil => rfl
  | cons write rest ih =>
      simp only [replace, List.map_cons] at ih ⊢
      by_cases h : write.cellId = original.cellId
      · simp [h, same, ih]
      · simp [h, ih]

theorem ids_nodup (original final : DataWrite) (writes : List DataWrite)
    (same : final.cellId = original.cellId)
    (unique : (writes.map DataWrite.cellId).Nodup) :
    ((replace original final writes).map DataWrite.cellId).Nodup := by
  rw [ids_preserved original final writes same]
  exact unique

theorem final_present (original final : DataWrite) (writes : List DataWrite)
    (present : original ∈ writes) : final ∈ replace original final writes := by
  apply List.mem_map.mpr
  exact ⟨original, present, by simp⟩

theorem unrelated_unchanged (original final : DataWrite) (writes : List DataWrite)
    (write : DataWrite) (present : write ∈ writes)
    (different : write.cellId ≠ original.cellId) :
    write ∈ replace original final writes := by
  apply List.mem_map.mpr
  exact ⟨write, present, by simp [different]⟩

theorem preserves_readonly (original final : DataWrite) (writes : List DataWrite)
    (same : final.cellId = original.cellId) (guard : ReadGuard)
    (readonly : guard.cellId ∉ writes.map DataWrite.cellId) :
    guard.cellId ∉ (replace original final writes).map DataWrite.cellId := by
  rw [ids_preserved original final writes same]
  exact readonly

theorem roots_bound (original final : DataWrite) (writes : List DataWrite)
    (finalBound : ResourceBirthCodec.rootBytes final.canonicalPostBytes = final.exactPost)
    (oldBound : ∀ write ∈ writes,
      ResourceBirthCodec.rootBytes write.canonicalPostBytes = write.exactPost)
    (write : DataWrite) (member : write ∈ replace original final writes) :
    ResourceBirthCodec.rootBytes write.canonicalPostBytes = write.exactPost := by
  obtain ⟨prior, priorMember, rfl⟩ := List.mem_map.mp member
  by_cases same : prior.cellId = original.cellId
  · simpa [same] using finalBound
  · simpa [same] using oldBound prior priorMember

/-- The post is computed only from the signed share spec's admitted `Ready`;
the old allocation's fresh pre-root is retained exactly. -/
def initializedWrite {domain : Digest} {spec : Spec} {operation : Nat}
    (ready : Ready domain spec operation) : DataWrite :=
  ResourceBirthController.birthWrite
    { ready.birth.create with cell := ready.initializedCell }

theorem initialized_id {domain : Digest} {spec : Spec} {operation : Nat}
    (ready : Ready domain spec operation) :
    (initializedWrite ready).cellId =
      (ResourceBirthController.birthWrite ready.birth.create).cellId := rfl

theorem initialized_pre {domain : Digest} {spec : Spec} {operation : Nat}
    (ready : Ready domain spec operation) :
    (initializedWrite ready).expectedPre =
      (ResourceBirthController.birthWrite ready.birth.create).expectedPre := rfl

theorem initialized_root_bound {domain : Digest} {spec : Spec} {operation : Nat}
    (ready : Ready domain spec operation) :
    ResourceBirthCodec.rootBytes (initializedWrite ready).canonicalPostBytes =
      (initializedWrite ready).exactPost := rfl

/-- Native birth admission still checks the empty source birth. This checked
composition confirms that its allocation write is present in that admitted
intent and that the only substituted post is a valid physical content cell. -/
structure Checked {domain : Digest} {spec : Spec} {operation : Nat}
    (ready : Ready domain spec operation) (deployment : CanonicalCellRegistry.Deployment)
    (writes : List DataWrite) where
  private mk ::
  token : Unit
  originalPresent : ResourceBirthController.birthWrite ready.birth.create ∈ writes
  initializedLaw : ResourceBirthController.Concrete.PhysicalPostLaw deployment
    (initializedWrite ready)

def check {domain : Digest} {spec : Spec} {operation : Nat}
    (ready : Ready domain spec operation) (deployment : CanonicalCellRegistry.Deployment)
    (writes : List DataWrite) : Option (Checked ready deployment writes) :=
  if present : ResourceBirthController.birthWrite ready.birth.create ∈ writes then
    if law : ResourceBirthController.Concrete.PhysicalPostLaw deployment
        (initializedWrite ready) then
      some ⟨(), present, law⟩
    else none
  else none

def Checked.writes {domain : Digest} {spec : Spec} {operation : Nat}
    {ready : Ready domain spec operation} {deployment : CanonicalCellRegistry.Deployment}
    {writes : List DataWrite} (_checked : Checked ready deployment writes) : List DataWrite :=
  replace (ResourceBirthController.birthWrite ready.birth.create)
    (initializedWrite ready) writes

theorem Checked.ids {domain : Digest} {spec : Spec} {operation : Nat}
    {ready : Ready domain spec operation} {deployment : CanonicalCellRegistry.Deployment}
    {writes : List DataWrite} (checked : Checked ready deployment writes) :
    checked.writes.map DataWrite.cellId = writes.map DataWrite.cellId :=
  ids_preserved _ _ _ (initialized_id ready)

theorem Checked.initialized_present {domain : Digest} {spec : Spec} {operation : Nat}
    {ready : Ready domain spec operation} {deployment : CanonicalCellRegistry.Deployment}
    {writes : List DataWrite} (checked : Checked ready deployment writes) :
    initializedWrite ready ∈ checked.writes :=
  final_present _ _ _ checked.originalPresent

theorem Checked.initialized_pre_exact {domain : Digest} {spec : Spec}
    {operation : Nat} {ready : Ready domain spec operation}
    {deployment : CanonicalCellRegistry.Deployment} {writes : List DataWrite}
    (checked : Checked ready deployment writes) (roots : Digest → Digest)
    (old : ∀ write ∈ writes, write.expectedPre = roots write.cellId) :
    (initializedWrite ready).expectedPre = roots (initializedWrite ready).cellId := by
  rw [initialized_pre ready, initialized_id ready]
  exact old _ checked.originalPresent

theorem Checked.unique {domain : Digest} {spec : Spec} {operation : Nat}
    {ready : Ready domain spec operation} {deployment : CanonicalCellRegistry.Deployment}
    {writes : List DataWrite} (checked : Checked ready deployment writes)
    (unique : (writes.map DataWrite.cellId).Nodup) :
    (checked.writes.map DataWrite.cellId).Nodup := by
  rw [checked.ids]
  exact unique

theorem Checked.readonly {domain : Digest} {spec : Spec} {operation : Nat}
    {ready : Ready domain spec operation} {deployment : CanonicalCellRegistry.Deployment}
    {writes : List DataWrite} (checked : Checked ready deployment writes)
    (guard : ReadGuard) (old : guard.cellId ∉ writes.map DataWrite.cellId) :
    guard.cellId ∉ checked.writes.map DataWrite.cellId := by
  rw [checked.ids]
  exact old

theorem Checked.roots_bound {domain : Digest} {spec : Spec} {operation : Nat}
    {ready : Ready domain spec operation} {deployment : CanonicalCellRegistry.Deployment}
    {writes : List DataWrite} (checked : Checked ready deployment writes)
    (old : ∀ write ∈ writes,
      ResourceBirthCodec.rootBytes write.canonicalPostBytes = write.exactPost) :
    ∀ write ∈ checked.writes,
      ResourceBirthCodec.rootBytes write.canonicalPostBytes = write.exactPost := by
  intro write member
  exact ApplicationShareIssueAtomicBirth.roots_bound _ _ _
    (initialized_root_bound ready) old write member

end Minidregg.Kernel.ApplicationShareIssueAtomicBirth
