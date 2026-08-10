/-
# Assurance.AuthenticatedColumnHistoryBridge -- controller openings become WARP messages

This module closes one duplicated PCS boundary.  `AuthenticatedColumnPlan`
owns executable roots and opening checks inside one accepted transcript, while
`SemanticHistoryWARPAdditiveJoin` consumes BCS messages under a Loom
`BindingCommitment`.  The binding adapter is now literal, so an opening that
occurred in the accepted controller attestation becomes the same BCS column
opening: no root, coordinate, value, or proof bytes are reinterpreted.

The cryptographic floor remains explicit.  A deployed scheme must inhabit
`BindingCommitmentScheme`, whose position-binding field is the Merkle/PCS
collision-resistance obligation.  This file neither proves that floor nor
constructs Fiat--Shamir; it proves that the controller and history layers use
one exact floor rather than parallel assumptions.
-/

import Assurance.SemanticHistoryWARPAdditiveJoin
import Compiler.AuthenticatedColumnPlan

namespace Minidregg.Assurance.AuthenticatedColumnHistoryBridge

open Minidregg.Assurance.SemanticHistoryWARPAdditiveJoin
open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Loom
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

noncomputable section

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {C : Submodule F (ι -> F)}
variable {foldRoot : Digest -> F -> Digest -> Digest}
variable {rounds openedCount degree : Nat}

variable {port : ColumnPort F F ι}
variable {scheme : BindingCommitmentScheme port}
variable {schedule : DualRootSchedule
  (C := C) (S := scheme.toLoom) (foldRoot := foldRoot) (rounds := rounds)}
variable {domain : ι ↪ F}
variable {queries : Fin openedCount -> Fin (FiniteCoordinateCount ι)}

variable {State : Type}
variable {portal : GlobalTranscriptPortal State}
variable {transcriptDomain : Digest}
variable {roots : List RootRecord} {draws : List DrawRecord}
variable {native : List NativeRecord} {openingRecords : List OpeningRecord}
variable {edges : List ReprEqRecord}

/-- Exact link columns and openings retained by one accepted authenticated-
column execution.  The represented word is the scheduled semantic link word;
every root and opening record must literally occur in the terminal
attestation's ledger. -/
structure AuthenticatedLinkColumns
    (attestation : TerminalAttestation portal transcriptDomain
      roots draws native openingRecords edges) where
  columns : Fin rounds -> BoundColumn port scheme.toCommitmentScheme
  representedExact : forall round index,
    (columns round).represented index = schedule.base.linkWord round index
  rootRecorded : forall round, (columns round).rootRecord ∈ roots
  openings : forall round, Fin openedCount -> ColumnOpening (columns round)
  openingIndexExact : forall round (query : Fin openedCount),
    (openings round query).index =
      (coordinateEquiv (ι := ι)).symm (queries query)
  openingRecorded : forall round (query : Fin openedCount),
    (openings round query).record ∈ openingRecords

namespace AuthenticatedLinkColumns

variable {attestation : TerminalAttestation portal transcriptDomain
  roots draws native openingRecords edges}

/-- The BCS message uses the controller column's exact root and the accepted
opening's exact representation value and proof bytes. -/
def message
    (links : AuthenticatedLinkColumns
      (port := port) (scheme := scheme) (schedule := schedule)
      (queries := queries) attestation)
    (round : Fin rounds) :
    BcsMsg Digest F (List UInt8) openedCount where
  root := (links.columns round).root
  cols := fun query => (links.openings round query).representationValue
  ops := fun query => (links.openings round query).proofBytes

/-- The message root is the pre-challenge semantic link root.  The equality
comes from the exact represented word, not a separately supplied root bridge. -/
theorem message_root_exact
    (links : AuthenticatedLinkColumns
      (port := port) (scheme := scheme) (schedule := schedule)
      (queries := queries) attestation)
    (round : Fin rounds) :
    (links.message round).root = schedule.linkRoot round := by
  change scheme.commit (links.columns round).represented =
    scheme.commit (schedule.base.linkWord round)
  congr 1
  funext index
  exact links.representedExact round index

/-- Every BCS column opening is exactly the opening already accepted by the
authenticated-column controller, viewed through the literal Loom adapter. -/
theorem message_columns_open
    (links : AuthenticatedLinkColumns
      (port := port) (scheme := scheme) (schedule := schedule)
      (queries := queries) attestation)
    (round : Fin rounds) :
    ColsOpen (reindexCommitment (S := scheme.toLoom)) queries
      (links.message round) := by
  intro query
  have verified := (links.openings round query).verifiesInLoom
  rw [links.openingIndexExact round query] at verified
  exact verified

/-- Package the accepted controller roots/openings as the exact BCS opening
family consumed by the unshifted WARP history theorem. -/
def toBcsLinkOpenings
    (links : AuthenticatedLinkColumns
      (port := port) (scheme := scheme) (schedule := schedule)
      (queries := queries) attestation)
    (degreeLeOpened : degree ≤ openedCount)
    (queriesDistinct : Function.Injective (reindexDomain domain ∘ queries)) :
    BcsLinkOpenings scheme.toLoom schedule domain degree openedCount where
  degreeLeOpened := degreeLeOpened
  queries := queries
  queriesDistinct := queriesDistinct
  messages := links.message
  rootExact := links.message_root_exact
  columnsOpen := links.message_columns_open

/-- The accepted authenticated-column execution therefore projects to the
exact pre-challenge semantic link/challenge stream used by WARP's unshifted
BCS reduction. -/
theorem bcsRounds_exact_of_attestation
    (links : AuthenticatedLinkColumns
      (port := port) (scheme := scheme) (schedule := schedule)
      (queries := queries) attestation)
    (degreeLeOpened : degree ≤ openedCount)
    (queriesDistinct : Function.Injective (reindexDomain domain ∘ queries))
    (codeExact : C = reedSolomonCode domain degree) :
    bcsRounds (reindexDomain domain) degree queries
        (List.ofFn fun round => (links.message round, schedule.challenges round)) =
      List.ofFn fun round =>
        (reindexWord (schedule.base.linkWord round), schedule.challenges round) := by
  exact (links.toBcsLinkOpenings degreeLeOpened queriesDistinct).bcsRounds_exact
    codeExact

/-- Ledger attribution is retained: the root and every opening used by the
BCS message occur in the same accepted terminal attestation. -/
theorem message_records_in_attestation
    (links : AuthenticatedLinkColumns
      (port := port) (scheme := scheme) (schedule := schedule)
      (queries := queries) attestation)
    (round : Fin rounds) (query : Fin openedCount) :
    (links.columns round).rootRecord ∈ roots ∧
      (links.openings round query).record ∈ openingRecords :=
  ⟨links.rootRecorded round, links.openingRecorded round query⟩

end AuthenticatedLinkColumns

/-- info: 'Minidregg.Assurance.AuthenticatedColumnHistoryBridge.AuthenticatedLinkColumns.message_root_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AuthenticatedLinkColumns.message_root_exact
/-- info: 'Minidregg.Assurance.AuthenticatedColumnHistoryBridge.AuthenticatedLinkColumns.message_columns_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AuthenticatedLinkColumns.message_columns_open
/-- info: 'Minidregg.Assurance.AuthenticatedColumnHistoryBridge.AuthenticatedLinkColumns.bcsRounds_exact_of_attestation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AuthenticatedLinkColumns.bcsRounds_exact_of_attestation

end

end Minidregg.Assurance.AuthenticatedColumnHistoryBridge
