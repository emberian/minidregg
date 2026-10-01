/-
# Kernel.PayCellDomain — the deployment's pay cell, loaded and written

The pay cell lives at `PayCell.physicalId deployment.domain`.  `load` decodes
exactly that identifier of one durable snapshot as the registry's `.pay` role;
no request supplies a cell, an identifier or a decoder.  A pay update is one
validated patch of that cell, physically one `DataWrite` guarded at the loaded
root (`Loaded.write_pre_is_loaded_root`).

The shared signing plan of the pay receivers (`SigningPlan`) is also here: the
Host returns it from the plan operation and assembles the signed ingress from
it and one detached signature.
-/
import Compiler.CredentialAuthorityDomainReceiver
import Kernel.PayCell

namespace Minidregg.Kernel.PayCellDomain

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

/-- The durable identifier of the deployment's pay cell. -/
def cellIdOf (deployment : CanonicalCellRegistry.Deployment) : CellId :=
  ⟨PayCell.physicalId deployment.domain⟩

def packedCell (cell : PayCell.Cell) : PackedCell registry := ⟨.pay, cell⟩

def cellBytes (cell : PayCell.Cell) : List UInt8 :=
  LifecycleImage.bytes registry (.live (packedCell cell))

def cellRoot (cell : PayCell.Cell) : Digest :=
  ResourceBirthCodec.rootBytes (cellBytes cell)

/-- Decode a live pay cell; any other role, a retired or fresh image, and
non-canonical bytes are refused. -/
def decodeCell (bytes : List UInt8) : Option PayCell.Cell :=
  match (LifecycleImage.codec registry).decode bytes with
  | some (.live ⟨.pay, payload⟩) => some payload
  | _ => none

theorem decodeCell_bytes (cell : PayCell.Cell) : decodeCell (cellBytes cell) = some cell := by
  unfold decodeCell cellBytes
  rw [show LifecycleImage.bytes registry (.live (packedCell cell)) =
      (LifecycleImage.codec registry).encode (.live (packedCell cell)) from rfl,
    LifecycleImage.decode_encode]
  rfl

theorem decodeCell_canonical {bytes : List UInt8} {cell : PayCell.Cell}
    (decoded : decodeCell bytes = some cell) : cellBytes cell = bytes := by
  unfold decodeCell at decoded
  split at decoded
  · rename_i payload image
    cases Option.some.inj decoded
    exact LifecycleImage.decode_canonical registry image
  · cases decoded

/-- The loaded pay cell.  The constructor is private: `load` is the only route,
so the cell is exactly what the physical snapshot holds at the pinned
identifier. -/
structure Loaded (deployment : CanonicalCellRegistry.Deployment) (physical : PhysicalSnapshot) where
  private mk ::
  cell : PayCell.Cell
  observed : physical.canonicalBytes (cellIdOf deployment) = cellBytes cell

def load (deployment : CanonicalCellRegistry.Deployment) (physical : PhysicalSnapshot) :
    Option (Loaded deployment physical) :=
  match decoded : decodeCell (physical.canonicalBytes (cellIdOf deployment)) with
  | none => none
  | some cell => some ⟨cell, (decodeCell_canonical decoded).symm⟩

/-- Satisfiable pole: the cell the snapshot holds is loaded exactly. -/
theorem load_exact (deployment : CanonicalCellRegistry.Deployment) (physical : PhysicalSnapshot)
    (cell : PayCell.Cell) (holds : physical.canonicalBytes (cellIdOf deployment) = cellBytes cell) :
    ∃ loaded, load deployment physical = some loaded ∧ loaded.cell = cell := by
  unfold load
  split
  · rename_i decoded
    rw [holds, decodeCell_bytes] at decoded
    cases decoded
  · rename_i found decoded
    rw [holds, decodeCell_bytes] at decoded
    exact ⟨_, rfl, (Option.some.inj decoded).symm⟩

/-- Refuting pole: an identifier that holds no live pay cell loads nothing. -/
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

/-- The post cell, written at the pinned identifier and guarded at the
snapshot's root of that same cell. -/
def Loaded.write {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (_loaded : Loaded deployment physical) (post : PayCell.Cell) : DataWrite where
  cellId := cellIdOf deployment
  expectedPre := physical.model.roots (cellIdOf deployment)
  exactPost := cellRoot post
  canonicalPostBytes := cellBytes post

theorem Loaded.write_root_bound {deployment : CanonicalCellRegistry.Deployment}
    {physical : PhysicalSnapshot} (loaded : Loaded deployment physical) (post : PayCell.Cell) :
    ResourceBirthCodec.rootBytes (loaded.write post).canonicalPostBytes = (loaded.write post).exactPost :=
  rfl

/-- A pay write cannot be applied over any other pay state. -/
theorem Loaded.write_pre_is_loaded_root {deployment : CanonicalCellRegistry.Deployment}
    {physical : PhysicalSnapshot} (loaded : Loaded deployment physical) (post : PayCell.Cell) :
    (loaded.write post).expectedPre = cellRoot loaded.cell :=
  loaded.root_exact.symm

theorem Loaded.write_decodes {deployment : CanonicalCellRegistry.Deployment}
    {physical : PhysicalSnapshot} (loaded : Loaded deployment physical) (post : PayCell.Cell) :
    decodeCell (loaded.write post).canonicalPostBytes = some post :=
  decodeCell_bytes post

/-! ## The shared signing plan -/

/-- What the signer signs: the exact source-derived header over the command. -/
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
  PayTariff.framed "DREGG/PAY/PLAN/v1".toUTF8.toList signingPlanStream

/-! ## The public view

What any caller may read of the pay cell: the three roots a pay command pins,
the tariff, the clock, and the published deposit address book with its
next-free index.  The assignment map (which account pays through which index)
is not in the view; an assignee learns its index from its own signed
command. -/
structure View where
  payRoot : Digest
  authorityRoot : Digest
  factoryRoot : Digest
  tariff : Option PayTariff.Tariff
  clock : Option PayCell.Clock
  nextFree : Nat
  book : List PayTariff.Address32
  deriving DecidableEq, Repr

/-- The book rows in index order, up to the first absent index. -/
def bookRows (store : PayCell.PayStore) : List PayTariff.Address32 :=
  (List.range (PayCell.bookSize store)).filterMap (PayCell.bookAt store)

def viewStream : StreamCodec View :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product (StreamCodec.option PayTariff.tariffStream)
          (StreamCodec.product (StreamCodec.option PayCell.clockStream)
            (StreamCodec.product StreamCodec.nat (StreamCodec.list bytesStream)))))))
    (fun view => (view.payRoot, view.authorityRoot, view.factoryRoot, view.tariff, view.clock,
      view.nextFree, view.book))
    (fun (pay, authority, factory, tariff, clock, next, book) =>
      ⟨pay, authority, factory, tariff, clock, next, book⟩)
    (by intro view; cases view; rfl)

def viewCodec : Minidregg.Theory.IndexedProgram.LawfulCodec View :=
  PayTariff.framed "DREGG/PAY/VIEW/v1".toUTF8.toList viewStream

/-! ## The public enrollment view (PAY §11.5; socket op 112)

What the box's root timer `mini-roster-sync` reads to render proxy login
lines: the chain hour and, per self-enrolled Mini key, its derived subject,
the key, the 51-byte ssh blob, its lease expiry (an hour) and its book index.
No account, no amount, no memo, no journal.  An entry is live iff
`hour < leaseUntil`. -/
structure EnrolmentEntry where
  subject : Nat
  miniKey : List UInt8
  sshBlob : List UInt8
  leaseUntil : Option Nat
  index : Option Nat
  deriving DecidableEq, Repr

structure EnrolmentView where
  hour : Nat
  entries : List EnrolmentEntry
  deriving DecidableEq, Repr

/-- Every enrolment row, in the store codec's canonical order. -/
def enrolments (store : PayCell.PayStore) : List (List UInt8 × PayCell.EnrolRecord) :=
  (StoreCodec.sortedSupport PayCell.wire store).filterMap fun
    | ⟨.enrolment, miniKey⟩ => (PayCell.enrolmentAt store miniKey).map (miniKey, ·)
    | _ => none

def enrolmentView (store : PayCell.PayStore) : EnrolmentView :=
  ⟨((PayCell.clockOf store).map PayCell.Clock.hour).getD 0,
    (enrolments store).map fun (miniKey, record) =>
      ⟨PayEnrolMemo.subjectOf miniKey, miniKey, record.sshBlob, some record.leaseUntil, record.index⟩⟩

def enrolmentEntryStream : StreamCodec EnrolmentEntry :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product bytesStream
        (StreamCodec.product bytesStream
          (StreamCodec.product (StreamCodec.option StreamCodec.nat)
            (StreamCodec.option StreamCodec.nat)))))
    (fun entry => (entry.subject, entry.miniKey, entry.sshBlob, entry.leaseUntil, entry.index))
    (fun (subject, miniKey, sshBlob, lease, index) => ⟨subject, miniKey, sshBlob, lease, index⟩)
    (by intro entry; cases entry; rfl)

def enrolmentViewStream : StreamCodec EnrolmentView :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat (StreamCodec.list enrolmentEntryStream))
    (fun view => (view.hour, view.entries))
    (fun (hour, entries) => ⟨hour, entries⟩)
    (by intro view; cases view; rfl)

def enrolmentViewCodec : Minidregg.Theory.IndexedProgram.LawfulCodec EnrolmentView :=
  PayTariff.framed "DREGG/PAY/ENROLMENT-VIEW/v1".toUTF8.toList enrolmentViewStream

theorem enrolmentView_roundtrip (view : EnrolmentView) :
    enrolmentViewCodec.decode (enrolmentViewCodec.encode view) = some view :=
  enrolmentViewCodec.decode_encode view

/-- **The view lists exactly the enrolled keys**: a (key, record) pair is
listed iff it is the key's enrolment row. -/
theorem mem_enrolments (store : PayCell.PayStore) (miniKey : List UInt8)
    (record : PayCell.EnrolRecord) :
    (miniKey, record) ∈ enrolments store ↔ PayCell.enrolmentAt store miniKey = some record := by
  unfold enrolments
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨address, _, found⟩
    rcases address with ⟨space, key⟩
    cases space <;> simp at found
    obtain ⟨present, same⟩ := found
    cases same
    exact present
  · intro present
    refine ⟨⟨.enrolment, miniKey⟩, ?_, by simp [present]⟩
    rw [StoreCodec.mem_sortedSupport]
    change PayCell.enrolmentAt store miniKey ≠ none
    simp [present]

#assert_axioms decodeCell_bytes
#assert_axioms decodeCell_canonical
#assert_axioms load_exact
#assert_axioms load_refuses
#assert_axioms Loaded.root_exact
#assert_axioms Loaded.write_pre_is_loaded_root
#assert_axioms enrolmentView_roundtrip
#assert_axioms mem_enrolments

end Minidregg.Kernel.PayCellDomain
