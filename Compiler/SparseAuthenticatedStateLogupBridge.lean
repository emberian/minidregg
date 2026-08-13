/-
# Compiler.SparseAuthenticatedStateLogupBridge -- exact sparse buses reach Tower256

`Kernel.SparseAuthenticatedState` deliberately stops at a heterogeneous,
timestamped semantic bus.  This module performs the next typed join without
inventing a native memory semantics:

* each committed LogUp row is one literal row of an accepted sparse execution;
* its table index is the deployment's one canonical encoding of that row's
  typed address, and its Boolean columns are the canonical binary decoding;
* the semantic-trace root is derived from the exact pre-root, post-root, and
  canonically encoded bus rows;
* ROM, append-only, and mutable-RAM rows retain distinct semantic laws; and
* mutable state continuity is an inductive state-threading relation over the
  bus rows (the semantic statement a Twist-style argument must prove).

The final theorem consumes `AcceptedLogupRun`, so the roots-before-challenge
schedule and the exact indexed-evaluation theorem come from the existing Lean
controller bridge.  PCS soundness, commitment binding/collision resistance,
and Fiat--Shamir ROM realization remain explicit premises of that object.
-/

import Kernel.SparseAuthenticatedState
import Compiler.AuthenticatedColumnLogupBridge
import Compiler.Tower256LogupControllerPlan

namespace Minidregg.Compiler.SparseAuthenticatedStateLogupBridge

open Minidregg.Kernel.SparseAuthenticatedState
open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.AuthenticatedColumnLogupBridge
open Minidregg.Compiler.Logup256ReceiptClause
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Selvage

set_option autoImplicit false

universe u v w

/-! ## A row-only, discipline-aware continuity relation -/

/-- The typed address named by a heterogeneous bus row. -/
def busAddress {L : Layout.{u, v, w}} (row : BusRow L) : Address L :=
  ⟨row.space, row.key⟩

/-- The exact one-cell transition asserted by a bus row.  Besides the observed
before/after values it retains a frame theorem for every other typed address.
This is independent of any field encoding or proof protocol. -/
structure CellTransition {L : Layout.{u, v, w}}
    (pre post : Store L) (row : BusRow L) : Prop where
  before_exact : pre row.space row.key = row.before
  after_exact : post row.space row.key = row.after
  frame : ∀ (space : L.Namespace) (key : L.Key space),
    (⟨space, key⟩ : Address L) ≠ busAddress row ->
      post space key = pre space key

/-- Row shapes are separated by namespace discipline.  Reads are legal in all
three disciplines.  ROM has no modifying constructor, append-only has only a
fresh `none -> some` allocation, and RAM has write/allocation/free shapes. -/
inductive DisciplineRowValid {L : Layout.{u, v, w}} : BusRow L -> Prop
  | read (clock : Nat) (space : L.Namespace) (key : L.Key space)
      (observed : Option (L.Value space)) :
      DisciplineRowValid
        ⟨clock, .read, space, key, observed, observed⟩
  | ramWrite (clock : Nat) (space : L.Namespace) (key : L.Key space)
      (before after : L.Value space)
      (discipline : L.discipline space = .ram) :
      DisciplineRowValid
        ⟨clock, .write, space, key, some before, some after⟩
  | ramAllocate (clock : Nat) (space : L.Namespace) (key : L.Key space)
      (value : L.Value space)
      (discipline : L.discipline space = .ram) :
      DisciplineRowValid
        ⟨clock, .allocate, space, key, none, some value⟩
  | appendAllocate (clock : Nat) (space : L.Namespace)
      (key : L.Key space) (value : L.Value space)
      (discipline : L.discipline space = .appendOnly) :
      DisciplineRowValid
        ⟨clock, .allocate, space, key, none, some value⟩
  | ramFree (clock : Nat) (space : L.Namespace) (key : L.Key space)
      (before : L.Value space)
      (discipline : L.discipline space = .ram) :
      DisciplineRowValid
        ⟨clock, .free, space, key, some before, none⟩

/-- The row-only state-continuity statement targeted by a Twist-style memory
argument.  Each next row consumes exactly the state produced by its predecessor;
there is no prover-selected intermediate state or final state. -/
inductive TwistContinuity {L : Layout.{u, v, w}} :
    Store L -> List (BusRow L) -> Store L -> Prop
  | nil (store : Store L) : TwistContinuity store [] store
  | cons {pre middle post : Store L} {row : BusRow L} {rows : List (BusRow L)}
      (discipline : DisciplineRowValid row)
      (transition : CellTransition pre middle row)
      (tail : TwistContinuity middle rows post) :
      TwistContinuity pre (row :: rows) post

namespace DisciplineRowValid

/-- A ROM row is necessarily a read. -/
theorem rom_is_read {L : Layout.{u, v, w}} {row : BusRow L}
    (valid : DisciplineRowValid row)
    (rom : L.discipline row.space = .rom) :
    row.kind = .read := by
  cases valid with
  | read => rfl
  | ramWrite _ _ _ _ _ discipline =>
      exact False.elim (Discipline.noConfusion (discipline.symm.trans rom))
  | ramAllocate _ _ _ _ discipline =>
      exact False.elim (Discipline.noConfusion (discipline.symm.trans rom))
  | appendAllocate _ _ _ _ discipline =>
      exact False.elim (Discipline.noConfusion (discipline.symm.trans rom))
  | ramFree _ _ _ _ discipline =>
      exact False.elim (Discipline.noConfusion (discipline.symm.trans rom))

/-- Every modifying append-only row is literally a fresh allocation row. -/
theorem appendOnly_modification_is_fresh_allocation
    {L : Layout.{u, v, w}} {row : BusRow L}
    (valid : DisciplineRowValid row)
    (appendOnly : L.discipline row.space = .appendOnly)
    (modifies : row.kind ≠ .read) :
    row.kind = .allocate /\ row.before = none := by
  cases valid with
  | read => exact False.elim (modifies rfl)
  | ramWrite _ _ _ _ _ discipline =>
      exact False.elim (Discipline.noConfusion (discipline.symm.trans appendOnly))
  | ramAllocate _ _ _ _ discipline =>
      exact False.elim (Discipline.noConfusion (discipline.symm.trans appendOnly))
  | appendAllocate => exact ⟨rfl, rfl⟩
  | ramFree _ _ _ _ discipline =>
      exact False.elim (Discipline.noConfusion (discipline.symm.trans appendOnly))

end DisciplineRowValid

namespace Op

/-- One enabled sparse operation produces an exact framed row transition. -/
theorem busRow_cellTransition {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace]
    [(space : L.Namespace) -> DecidableEq (L.Key space)]
    (clock : Nat) (store : Store L) (operation : Op L)
    (enabled : operation.Enabled store) :
    CellTransition store (operation.apply store)
      (operation.busRow clock store) := by
  cases operation with
  | read space key observed =>
      exact ⟨enabled, enabled, fun _ _ _ => rfl⟩
  | write space key before after =>
      refine ⟨enabled.2, Store.set_eq store space key (some after), ?_⟩
      intro otherNamespace otherKey different
      exact Store.set_ne store space key (some after)
        otherNamespace otherKey different
  | allocate space key value =>
      refine ⟨enabled.2, Store.set_eq store space key (some value), ?_⟩
      intro otherNamespace otherKey different
      exact Store.set_ne store space key (some value)
        otherNamespace otherKey different
  | free space key before =>
      refine ⟨enabled.2, Store.set_eq store space key none, ?_⟩
      intro otherNamespace otherKey different
      exact Store.set_ne store space key none
        otherNamespace otherKey different

/-- Enabledness derives the exact discipline-specific row constructor. -/
theorem busRow_disciplineValid {L : Layout.{u, v, w}}
    (clock : Nat) (store : Store L) (operation : Op L)
    (enabled : operation.Enabled store) :
    DisciplineRowValid (operation.busRow clock store) := by
  cases operation with
  | read space key observed => exact .read clock space key observed
  | write space key before after =>
      exact .ramWrite clock space key before after enabled.1
  | allocate space key value =>
      cases discipline : L.discipline space with
      | rom => exact False.elim (enabled.1 discipline)
      | ram => exact .ramAllocate clock space key value discipline
      | appendOnly => exact .appendAllocate clock space key value discipline
  | free space key before =>
      exact .ramFree clock space key before enabled.1

end Op

namespace TwistContinuity

/-- The kernel's exact operation-indexed bus relation erases to the row-only
Twist continuity statement without weakening any intermediate state. -/
theorem of_busRelation {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace]
    [(space : L.Namespace) -> DecidableEq (L.Key space)]
    {clock : Nat} {pre post : Store L} {operations : List (Op L)}
    {rows : List (BusRow L)}
    (relation : Trace.BusRelation clock pre operations rows post) :
    TwistContinuity pre rows post := by
  induction relation with
  | nil clock store => exact .nil store
  | @cons clock store post operation operations rows enabled tail induction =>
      exact .cons
        (Op.busRow_disciplineValid clock store operation enabled)
        (Op.busRow_cellTransition clock store operation enabled)
        induction

/-- Every row in a continuous bus has one of the exact discipline shapes. -/
theorem row_valid {L : Layout.{u, v, w}}
    {pre post : Store L} {rows : List (BusRow L)}
    (continuity : TwistContinuity pre rows post)
    {row : BusRow L} (member : row ∈ rows) :
    DisciplineRowValid row := by
  induction continuity with
  | nil => simp at member
  | cons discipline transition tail induction =>
      simp only [List.mem_cons] at member
      exact member.elim (fun equality => equality ▸ discipline) induction

end TwistContinuity

namespace ExactBusClaim

variable {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace]
    [(space : L.Namespace) -> DecidableEq (L.Key space)]
    {materializer : Materializer L Digest}
    {pre : Materialized materializer} {operations : List (Op L)}
    {accepted : AcceptedExecution materializer pre operations}

/-- Exact bus claims already carry the state continuity required by mutable
RAM checking; no additional witness is supplied by the proof compiler. -/
theorem twistContinuity (bus : ExactBusClaim accepted) :
    TwistContinuity pre.logical bus.rows accepted.post.logical :=
  TwistContinuity.of_busRelation bus.rows_semantic

/-- All rows of an exact bus retain their ROM/RAM/append-only classification. -/
theorem row_discipline_valid (bus : ExactBusClaim accepted)
    {row : BusRow L} (member : row ∈ bus.rows) :
    DisciplineRowValid row :=
  TwistContinuity.row_valid
    (ExactBusClaim.twistContinuity bus) member

end ExactBusClaim

/-! ## Canonical finite address and row commitment projections -/

/-- One deployment-owned injection from typed sparse addresses into the LogUp
table.  The index is derived from canonical address bytes; `index_injective`
prevents distinct typed addresses from sharing a semantic table cell. -/
structure CanonicalAddressing (L : Layout.{u, v, w}) (addressLog : Nat) where
  codec : LawfulCodec (Address L)
  indexBytes : List UInt8 -> Fin (2 ^ addressLog)
  index_injective : Function.Injective (fun address => indexBytes (codec.encode address))

def CanonicalAddressing.index {L : Layout.{u, v, w}} {addressLog : Nat}
    (addressing : CanonicalAddressing L addressLog) :
    Address L -> Fin (2 ^ addressLog) :=
  fun address => addressing.indexBytes (addressing.codec.encode address)

theorem CanonicalAddressing.index_inj {L : Layout.{u, v, w}} {addressLog : Nat}
    (addressing : CanonicalAddressing L addressLog) :
    Function.Injective addressing.index :=
  addressing.index_injective

/-- Canonical framing for a sparse semantic trace.  This is only a root
function over exact encoded data; its binding/collision-resistance property is
not asserted here. -/
structure BusCommitment (L : Layout.{u, v, w}) where
  rowCodec : LawfulCodec (BusRow L)
  rootFrames : Digest -> Digest -> List (List UInt8) -> Digest

def BusCommitment.root {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace]
    [(space : L.Namespace) -> DecidableEq (L.Key space)]
    (commitment : BusCommitment L)
    {materializer : Materializer L Digest}
    {pre : Materialized materializer} {operations : List (Op L)}
    {accepted : AcceptedExecution materializer pre operations}
    (bus : ExactBusClaim accepted) : Digest :=
  commitment.rootFrames bus.preRoot bus.postRoot
    (bus.rows.map commitment.rowCodec.encode)

/-- A controller uses power-of-two row domains.  Padding is intentionally not
silent: this bridge accepts an unpadded sparse trace only with an exact row-count
equality.  A later padding dialect must specify and prove its own neutral rows. -/
structure PowerOfTwoRows
    {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace]
    [(space : L.Namespace) -> DecidableEq (L.Key space)]
    {materializer : Materializer L Digest}
    {pre : Materialized materializer} {operations : List (Op L)}
    {accepted : AcceptedExecution materializer pre operations}
    (bus : ExactBusClaim accepted) (rowLog : Nat) : Prop where
  exact : bus.rows.length = 2 ^ rowLog

def rowAt
    {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace]
    [(space : L.Namespace) -> DecidableEq (L.Key space)]
    {materializer : Materializer L Digest}
    {pre : Materialized materializer} {operations : List (Op L)}
    {accepted : AcceptedExecution materializer pre operations}
    {bus : ExactBusClaim accepted} {rowLog : Nat}
    (power : PowerOfTwoRows bus rowLog) (row : Fin (2 ^ rowLog)) : BusRow L :=
  bus.rows.get (Fin.cast power.exact.symm row)

/-- The committed semantic trace is fully derived from the exact sparse bus.
No prover-authored indices or address bits enter this constructor. -/
def committedBusTrace
    {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace]
    [(space : L.Namespace) -> DecidableEq (L.Key space)]
    {materializer : Materializer L Digest}
    {pre : Materialized materializer} {operations : List (Op L)}
    {accepted : AcceptedExecution materializer pre operations}
    {bus : ExactBusClaim accepted} {rowLog addressLog : Nat}
    (power : PowerOfTwoRows bus rowLog)
    (addressing : CanonicalAddressing L addressLog)
    (commitment : BusCommitment L)
    (addressRoot weightsRoot tableRoot : Digest) :
    CommittedSemanticTrace (Fin (2 ^ rowLog)) addressLog where
  semanticTraceRoot := commitment.root bus
  addressRoot := addressRoot
  weightsRoot := weightsRoot
  tableRoot := tableRoot
  index := fun row => addressing.index (busAddress (rowAt power row))
  addressBits := fun row => binaryAddressBits addressLog
    (addressing.index (busAddress (rowAt power row)))

/-- Canonical address linkage is true by construction for a sparse bus trace. -/
theorem committedBusTrace_canonicalAddressLinked
    {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace]
    [(space : L.Namespace) -> DecidableEq (L.Key space)]
    {materializer : Materializer L Digest}
    {pre : Materialized materializer} {operations : List (Op L)}
    {accepted : AcceptedExecution materializer pre operations}
    {bus : ExactBusClaim accepted} {rowLog addressLog : Nat}
    (power : PowerOfTwoRows bus rowLog)
    (addressing : CanonicalAddressing L addressLog)
    (commitment : BusCommitment L)
    (addressRoot weightsRoot tableRoot : Digest) :
    CanonicalAddressLinked
      (committedBusTrace power addressing commitment
        addressRoot weightsRoot tableRoot) := by
  intro row
  rfl

/-- A canonical sparse-memory lookup claim.  The claimed evaluation is the
exact incidence pushforward over the committed bus addresses. -/
noncomputable def canonicalBusClaim
    {F : Type*} [Field F]
    {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace]
    [(space : L.Namespace) -> DecidableEq (L.Key space)]
    {materializer : Materializer L Digest}
    {pre : Materialized materializer} {operations : List (Op L)}
    {accepted : AcceptedExecution materializer pre operations}
    {bus : ExactBusClaim accepted} {rowLog addressLog : Nat}
    (power : PowerOfTwoRows bus rowLog)
    (addressing : CanonicalAddressing L addressLog)
    (commitment : BusCommitment L)
    (addressRoot weightsRoot tableRoot : Digest)
    (weights : Fin (2 ^ rowLog) -> F)
    (table : Fin (2 ^ addressLog) -> F) :
    IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) addressLog :=
  let trace := committedBusTrace power addressing commitment
    addressRoot weightsRoot tableRoot
  { semanticTraceRoot := trace.semanticTraceRoot
    addressRoot := addressRoot
    weightsRoot := weightsRoot
    tableRoot := tableRoot
    weights := weights
    table := table
    claimedEvaluation :=
      logupDot table (committedIncidencePushforward trace weights) }

/-- The exact sparse bus supplies every locally decidable terminal fact.  The
cryptographic premises are deliberately absent from this theorem. -/
theorem canonicalBus_finalStatement
    {F : Type*} [Field F]
    {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace]
    [(space : L.Namespace) -> DecidableEq (L.Key space)]
    {materializer : Materializer L Digest}
    {pre : Materialized materializer} {operations : List (Op L)}
    {accepted : AcceptedExecution materializer pre operations}
    {bus : ExactBusClaim accepted} {rowLog addressLog : Nat}
    (power : PowerOfTwoRows bus rowLog)
    (addressing : CanonicalAddressing L addressLog)
    (commitment : BusCommitment L)
    (addressRoot weightsRoot tableRoot : Digest)
    (weights : Fin (2 ^ rowLog) -> F)
    (table : Fin (2 ^ addressLog) -> F) :
    LogupFinalStatement
      (committedBusTrace power addressing commitment
        addressRoot weightsRoot tableRoot)
      (canonicalBusClaim power addressing commitment
        addressRoot weightsRoot tableRoot weights table) where
  canonicalAddressLinked := committedBusTrace_canonicalAddressLinked
    power addressing commitment addressRoot weightsRoot tableRoot
  towerArithmetic := rfl
  pcsRootsBound := ⟨rfl, rfl, rfl⟩
  semanticTraceRootBound := rfl

/-! ## Accepted controller join -/

/-- Consumer-facing result of proving one exact sparse bus with the authenticated
Tower256/LogUp controller.  `indexedEvaluation` is the canonical lookup relation;
`continuity` is the independent Twist-style state relation for mutable memory. -/
structure AcceptedSparseBusLookup
    {F : Type*} [Field F] [CharP F 2]
    {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace]
    [(space : L.Namespace) -> DecidableEq (L.Key space)]
    {materializer : Materializer L Digest}
    {pre : Materialized materializer} {operations : List (Op L)}
    {accepted : AcceptedExecution materializer pre operations}
    (bus : ExactBusClaim accepted) (rowLog addressLog : Nat)
    (power : PowerOfTwoRows bus rowLog)
    (addressing : CanonicalAddressing L addressLog)
    (trace : CommittedSemanticTrace (Fin (2 ^ rowLog)) addressLog)
    (claim : IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) addressLog) : Prop where
  preRoot_exact : bus.preRoot = pre.root
  postRoot_exact : bus.postRoot = accepted.post.root
  rowIndex_exact : ∀ row,
    trace.index row = addressing.index (busAddress (rowAt power row))
  addressBits_exact : ∀ row,
    trace.addressBits row = binaryAddressBits addressLog (trace.index row)
  addressColumnsBoolean : ∀ bit row,
    committedAddressColumn (F := F) trace bit row = 0 ∨
      committedAddressColumn (F := F) trace bit row = 1
  incidenceIsCanonicalAddress : ∀ row,
    committedIncidence (F := F) trace row =
      binaryUnitVector (addressing.index (busAddress (rowAt power row)))
  pushforwardExact :
    committedIncidencePushforward trace claim.weights =
      logupPushforward
        (fun row => addressing.index (busAddress (rowAt power row)))
        claim.weights
  indexedEvaluation :
    claim.claimedEvaluation =
      logupDot
        (fun row => claim.table (addressing.index (busAddress (rowAt power row))))
        claim.weights
  continuity : TwistContinuity pre.logical bus.rows accepted.post.logical

/-- Main join.  An accepted controller proof over a trace whose row indices are
exactly the canonical sparse addresses yields the sparse lookup equation while
retaining the kernel's state continuity.  The accepted object still contains
its PCS, CR/binding, and ROM premises; this theorem does not discharge them. -/
theorem acceptedSparseBusLookup
    {F : Type*} [Field F] [CharP F 2]
    {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace]
    [(space : L.Namespace) -> DecidableEq (L.Key space)]
    {materializer : Materializer L Digest}
    {pre : Materialized materializer} {operations : List (Op L)}
    {accepted : AcceptedExecution materializer pre operations}
    {bus : ExactBusClaim accepted} {rowLog addressLog : Nat}
    {power : PowerOfTwoRows bus rowLog}
    {addressing : CanonicalAddressing L addressLog}
    {trace : CommittedSemanticTrace (Fin (2 ^ rowLog)) addressLog}
    {claim : IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) addressLog}
    {State : Type} {portal : GlobalTranscriptPortal State}
    {transcriptDomain : Digest}
    {roots : List RootRecord} {draws : List DrawRecord}
    {native : List NativeRecord} {openings : List OpeningRecord}
    {edges : List ReprEqRecord}
    {attestation : TerminalAttestation portal transcriptDomain
      roots draws native openings edges}
    {required : RequiredRoots trace claim}
    {PCSOpeningSound : IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) addressLog ->
      CommittedSemanticTrace (Fin (2 ^ rowLog)) addressLog -> Prop}
    {CommitmentBindingCR : IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) addressLog ->
      CommittedSemanticTrace (Fin (2 ^ rowLog)) addressLog -> Prop}
    {RandomOracleModel :
      IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) addressLog -> Prop}
    (run : AcceptedLogupRun attestation trace claim required
      PCSOpeningSound CommitmentBindingCR RandomOracleModel)
    (rowIndexExact : ∀ row,
      trace.index row = addressing.index (busAddress (rowAt power row)))
    (addressBitsExact : ∀ row,
      trace.addressBits row = binaryAddressBits addressLog (trace.index row)) :
    AcceptedSparseBusLookup bus rowLog addressLog power addressing trace claim where
  preRoot_exact := bus.preRoot_exact
  postRoot_exact := bus.postRoot_exact
  rowIndex_exact := rowIndexExact
  addressBits_exact := addressBitsExact
  addressColumnsBoolean :=
    run.indexedTableReceiptClause_of_attestation.addressColumnsBoolean
  incidenceIsCanonicalAddress := by
    intro row
    rw [run.indexedTableReceiptClause_of_attestation.incidenceIsLiteralUnitVector,
      rowIndexExact row]
  pushforwardExact := by
    rw [run.indexedTableReceiptClause_of_attestation.pushforwardExact]
    apply congrArg (fun index => logupPushforward index claim.weights)
    funext row
    exact rowIndexExact row
  indexedEvaluation := by
    rw [run.indexedEvaluation_of_attestation]
    apply congrArg (fun values => logupDot values claim.weights)
    funext row
    rw [rowIndexExact row]
  continuity := ExactBusClaim.twistContinuity bus

/-- info: 'Minidregg.Compiler.SparseAuthenticatedStateLogupBridge.TwistContinuity.of_busRelation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms TwistContinuity.of_busRelation
/-- info: 'Minidregg.Compiler.SparseAuthenticatedStateLogupBridge.ExactBusClaim.twistContinuity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ExactBusClaim.twistContinuity
/-- info: 'Minidregg.Compiler.SparseAuthenticatedStateLogupBridge.committedBusTrace_canonicalAddressLinked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms committedBusTrace_canonicalAddressLinked
/-- info: 'Minidregg.Compiler.SparseAuthenticatedStateLogupBridge.canonicalBus_finalStatement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonicalBus_finalStatement
/-- info: 'Minidregg.Compiler.SparseAuthenticatedStateLogupBridge.acceptedSparseBusLookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms acceptedSparseBusLookup

end Minidregg.Compiler.SparseAuthenticatedStateLogupBridge
