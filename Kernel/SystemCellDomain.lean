/-
# Kernel.SystemCellDomain — the deployment's system cell, loaded, read and written

The system cell lives at `SystemCell.physicalId deployment.domain`.  `load`
decodes exactly that identifier of one durable snapshot as the registry's
`.system` role (`TailBound.decodeCell`, the decoder the kernel's tail rule
uses); no request supplies a cell, an identifier or a decoder.

A certify is one validated patch of the cell, physically one `DataWrite`
guarded at the loaded root (`Loaded.write_pre_is_loaded_root`).
-/
import Compiler.CredentialAuthorityDomainReceiver
import Kernel.SystemCell
import Kernel.TailBound

namespace Minidregg.Kernel.SystemCellDomain

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalCellRegistry (registry)
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

abbrev PhysicalSnapshot := DataSnapshot ResourceBirthCodec.rootBytes

/-- The durable identifier of the deployment's system cell. -/
def cellIdOf (deployment : CanonicalCellRegistry.Deployment) : CellId :=
  ⟨SystemCell.physicalId deployment.domain⟩

def packedCell (cell : SystemCell.Cell) : PackedCell registry := ⟨.system, cell⟩

def cellBytes (cell : SystemCell.Cell) : List UInt8 :=
  LifecycleImage.bytes registry (.live (packedCell cell))

def cellRoot (cell : SystemCell.Cell) : Digest :=
  ResourceBirthCodec.rootBytes (cellBytes cell)

/-- Decode a live system cell; any other role, a retired or fresh image, and
non-canonical bytes are refused. -/
def decodeCell (bytes : List UInt8) : Option SystemCell.Cell := TailBound.decodeCell bytes

theorem decodeCell_bytes (cell : SystemCell.Cell) : decodeCell (cellBytes cell) = some cell := by
  unfold decodeCell TailBound.decodeCell cellBytes
  rw [show LifecycleImage.bytes registry (.live (packedCell cell)) =
      (LifecycleImage.codec registry).encode (.live (packedCell cell)) from rfl,
    LifecycleImage.decode_encode]
  rfl

theorem decodeCell_canonical {bytes : List UInt8} {cell : SystemCell.Cell}
    (decoded : decodeCell bytes = some cell) : cellBytes cell = bytes := by
  unfold decodeCell TailBound.decodeCell at decoded
  split at decoded
  · rename_i payload image
    cases Option.some.inj decoded
    exact LifecycleImage.decode_canonical registry image
  · cases decoded

/-- The loaded system cell.  The constructor is private: `load` is the only route, so
the cell is exactly what the physical snapshot holds at the pinned identifier,
and `system` is the value that cell holds. -/
structure Loaded (deployment : CanonicalCellRegistry.Deployment) (physical : PhysicalSnapshot) where
  private mk ::
  cell : SystemCell.Cell
  system : SystemCell.System
  observed : physical.canonicalBytes (cellIdOf deployment) = cellBytes cell
  systemExact : SystemCell.systemOf cell.logical = some system

def load (deployment : CanonicalCellRegistry.Deployment) (physical : PhysicalSnapshot) :
    Option (Loaded deployment physical) :=
  match decoded : decodeCell (physical.canonicalBytes (cellIdOf deployment)) with
  | none => none
  | some cell =>
      match present : SystemCell.systemOf cell.logical with
      | none => none
      | some system => some ⟨cell, system, (decodeCell_canonical decoded).symm, present⟩

/-- Satisfiable pole: the system value the snapshot holds is loaded exactly. -/
theorem load_exact (deployment : CanonicalCellRegistry.Deployment) (physical : PhysicalSnapshot)
    (cell : SystemCell.Cell) (system : SystemCell.System)
    (holds : physical.canonicalBytes (cellIdOf deployment) = cellBytes cell)
    (present : SystemCell.systemOf cell.logical = some system) :
    ∃ loaded, load deployment physical = some loaded ∧ loaded.cell = cell ∧ loaded.system = system := by
  unfold load
  split
  · rename_i decoded
    rw [holds, decodeCell_bytes] at decoded
    cases decoded
  · rename_i found decoded
    rw [holds, decodeCell_bytes] at decoded
    cases Option.some.inj decoded
    split
    · rename_i absent
      rw [present] at absent
      cases absent
    · rename_i value same
      rw [present] at same
      exact ⟨_, rfl, rfl, (Option.some.inj same).symm⟩

/-- Refuting pole: an identifier that holds no live system cell loads nothing. -/
theorem load_refuses (deployment : CanonicalCellRegistry.Deployment) (physical : PhysicalSnapshot)
    (undecodable : decodeCell (physical.canonicalBytes (cellIdOf deployment)) = none) :
    load deployment physical = none := by
  unfold load
  split
  · rfl
  · rename_i cell decoded
    rw [undecodable] at decoded
    cases decoded

theorem Loaded.root_exact {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) :
    cellRoot loaded.cell = physical.model.roots (cellIdOf deployment) := by
  unfold cellRoot
  rw [← loaded.observed]
  exact physical.coherent _

/-- The one read dependency of a system-cell reader. -/
def Loaded.readGuard {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (_loaded : Loaded deployment physical) : ReadGuard :=
  { cellId := cellIdOf deployment, expectedRoot := physical.model.roots (cellIdOf deployment) }

theorem Loaded.readGuard_exact {deployment : CanonicalCellRegistry.Deployment}
    {physical : PhysicalSnapshot} (loaded : Loaded deployment physical) :
    loaded.readGuard.expectedRoot = physical.model.roots loaded.readGuard.cellId :=
  rfl

/-- The post cell, written at the pinned identifier and guarded at the
snapshot's root of that same cell. -/
def Loaded.write {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (_loaded : Loaded deployment physical) (post : SystemCell.Cell) : DataWrite where
  cellId := cellIdOf deployment
  expectedPre := physical.model.roots (cellIdOf deployment)
  exactPost := cellRoot post
  canonicalPostBytes := cellBytes post

theorem Loaded.write_root_bound {deployment : CanonicalCellRegistry.Deployment}
    {physical : PhysicalSnapshot} (loaded : Loaded deployment physical) (post : SystemCell.Cell) :
    ResourceBirthCodec.rootBytes (loaded.write post).canonicalPostBytes = (loaded.write post).exactPost :=
  rfl

/-- A certify cannot be applied over any other system state. -/
theorem Loaded.write_pre_is_loaded_root {deployment : CanonicalCellRegistry.Deployment}
    {physical : PhysicalSnapshot} (loaded : Loaded deployment physical) (post : SystemCell.Cell) :
    (loaded.write post).expectedPre = cellRoot loaded.cell :=
  loaded.root_exact.symm

/-! ## The public view -/

/-- What a certifier reads before it signs: the roots a certify pins, the
system value, and the head it would certify with that head's chain value. -/
structure View where
  systemRoot : Digest
  authorityRoot : Digest
  factoryRoot : Digest
  system : SystemCell.System
  head : Nat
  chain : Digest
  deriving DecidableEq, Repr

/-- info: 'Minidregg.Kernel.SystemCellDomain.decodeCell_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decodeCell_bytes
/-- info: 'Minidregg.Kernel.SystemCellDomain.load_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms load_exact
/-- info: 'Minidregg.Kernel.SystemCellDomain.load_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms load_refuses
/-- info: 'Minidregg.Kernel.SystemCellDomain.Loaded.write_pre_is_loaded_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Loaded.write_pre_is_loaded_root

end Minidregg.Kernel.SystemCellDomain
