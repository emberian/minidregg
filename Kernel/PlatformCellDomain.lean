/-
# Kernel.PlatformCellDomain — the deployment's platform cell, loaded and written

The platform cell lives at `PlatformCellLayout.physicalId deployment.domain`. `load` decodes
exactly that identifier of one durable snapshot as the registry's `.platform` role; no request
supplies a cell, an identifier or a decoder. An install is one validated patch of that cell,
physically one `DataWrite` guarded at the loaded root (`Loaded.write_pre_is_loaded_root`).
-/
import Compiler.CredentialAuthorityDomainReceiver
import Kernel.PlatformCellLayout

namespace Minidregg.Kernel.PlatformCellDomain

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
abbrev Cell := PlatformCellLayout.Cell

/-- The durable identifier of the deployment's platform cell. -/
def cellIdOf (deployment : CanonicalCellRegistry.Deployment) : CellId :=
  ⟨PlatformCellLayout.physicalId deployment.domain⟩

def packedCell (cell : Cell) : PackedCell registry := ⟨.platform, cell⟩

def cellBytes (cell : Cell) : List UInt8 :=
  LifecycleImage.bytes registry (.live (packedCell cell))

def cellRoot (cell : Cell) : Digest :=
  ResourceBirthCodec.rootBytes (cellBytes cell)

/-- Decode a live platform cell; any other role, a retired or fresh image, and non-canonical
bytes are refused. -/
def decodeCell (bytes : List UInt8) : Option Cell :=
  match (LifecycleImage.codec registry).decode bytes with
  | some (.live ⟨.platform, payload⟩) => some payload
  | _ => none

theorem decodeCell_bytes (cell : Cell) : decodeCell (cellBytes cell) = some cell := by
  unfold decodeCell cellBytes
  rw [show LifecycleImage.bytes registry (.live (packedCell cell)) =
      (LifecycleImage.codec registry).encode (.live (packedCell cell)) from rfl,
    LifecycleImage.decode_encode]
  rfl

theorem decodeCell_canonical {bytes : List UInt8} {cell : Cell}
    (decoded : decodeCell bytes = some cell) : cellBytes cell = bytes := by
  unfold decodeCell at decoded
  split at decoded
  · rename_i payload image
    cases Option.some.inj decoded
    exact LifecycleImage.decode_canonical registry image
  · cases decoded

/-- The loaded platform cell. The constructor is private: `load` is the only route, so the
cell is exactly what the physical snapshot holds at the pinned identifier. -/
structure Loaded (deployment : CanonicalCellRegistry.Deployment) (physical : PhysicalSnapshot) where
  private mk ::
  cell : Cell
  observed : physical.canonicalBytes (cellIdOf deployment) = cellBytes cell

def load (deployment : CanonicalCellRegistry.Deployment) (physical : PhysicalSnapshot) :
    Option (Loaded deployment physical) :=
  match decoded : decodeCell (physical.canonicalBytes (cellIdOf deployment)) with
  | none => none
  | some cell => some ⟨cell, (decodeCell_canonical decoded).symm⟩

/-- Satisfiable pole: the cell the snapshot holds is loaded exactly. -/
theorem load_exact (deployment : CanonicalCellRegistry.Deployment) (physical : PhysicalSnapshot)
    (cell : Cell) (holds : physical.canonicalBytes (cellIdOf deployment) = cellBytes cell) :
    ∃ loaded, load deployment physical = some loaded ∧ loaded.cell = cell := by
  unfold load
  split
  · rename_i decoded
    rw [holds, decodeCell_bytes] at decoded
    cases decoded
  · rename_i found decoded
    rw [holds, decodeCell_bytes] at decoded
    exact ⟨_, rfl, (Option.some.inj decoded).symm⟩

/-- Refuting pole: an identifier that holds no live platform cell loads nothing (a world born
before the platform cell, or any other role at that identifier). -/
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

/-- The platform cell as a read dependency (a birth that prices against it). -/
def Loaded.readGuard {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (_loaded : Loaded deployment physical) : ReadGuard :=
  { cellId := cellIdOf deployment, expectedRoot := physical.model.roots (cellIdOf deployment) }

/-- The post cell, written at the pinned identifier and guarded at the snapshot's root of
that same cell. -/
def Loaded.write {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (_loaded : Loaded deployment physical) (post : Cell) : DataWrite where
  cellId := cellIdOf deployment
  expectedPre := physical.model.roots (cellIdOf deployment)
  exactPost := cellRoot post
  canonicalPostBytes := cellBytes post

theorem Loaded.write_root_bound {deployment : CanonicalCellRegistry.Deployment}
    {physical : PhysicalSnapshot} (loaded : Loaded deployment physical) (post : Cell) :
    ResourceBirthCodec.rootBytes (loaded.write post).canonicalPostBytes = (loaded.write post).exactPost :=
  rfl

/-- An install cannot be applied over any other platform state. -/
theorem Loaded.write_pre_is_loaded_root {deployment : CanonicalCellRegistry.Deployment}
    {physical : PhysicalSnapshot} (loaded : Loaded deployment physical) (post : Cell) :
    (loaded.write post).expectedPre = cellRoot loaded.cell :=
  loaded.root_exact.symm

theorem Loaded.write_decodes {deployment : CanonicalCellRegistry.Deployment}
    {physical : PhysicalSnapshot} (loaded : Loaded deployment physical) (post : Cell) :
    decodeCell (loaded.write post).canonicalPostBytes = some post :=
  decodeCell_bytes post

/-! ## The signing plan

What the controller signs: the exact source-derived header over the command. The Host
returns it from the plan operation (240) and assembles the signed ingress from it, one
detached signature and, for a custodian rotation, the custodian's cosignature (241). -/
structure SigningPlan where
  domain : Digest
  semantics : Digest
  commandBytes : List UInt8
  header : List UInt8
  deriving DecidableEq, Repr

def signingPlanStream : StreamCodec SigningPlan :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product bytesStream bytesStream)))
    (fun plan => (plan.domain, plan.semantics, plan.commandBytes, plan.header))
    (fun (domain, semantics, command, header) => ⟨domain, semantics, command, header⟩)
    (by intro plan; cases plan; rfl)

def signingPlanCodec : Minidregg.Theory.IndexedProgram.LawfulCodec SigningPlan :=
  (StreamCodec.framed "DREGG/PLATFORM/PLAN/v1".toUTF8.toList signingPlanStream).toLawful

theorem signingPlan_roundtrip (plan : SigningPlan) :
    signingPlanCodec.decode (signingPlanCodec.encode plan) = some plan :=
  signingPlanCodec.decode_encode plan

#assert_axioms signingPlan_roundtrip

#assert_axioms decodeCell_bytes
#assert_axioms decodeCell_canonical
#assert_axioms load_exact
#assert_axioms load_refuses
#assert_axioms Loaded.root_exact
#assert_axioms Loaded.write_pre_is_loaded_root

end Minidregg.Kernel.PlatformCellDomain
