/-
# Compiler.HyperdocumentIndexPageMaterializer -- persistent four-slot link index

This is the concrete persistent representation of the bounded semantic index
in `Kernel.HyperdocumentIndexSync`.  A page stores four canonical source
entries, four derived rows, both causal checkpoints, and the checkpoint-bound
sync cursor.  Its lawful prefix codec is framed and rooted by Lean's cSHAKE256
implementation.

Because source and derived rows coexist in the canonical bytes, decode followed
by `status` can detect checkpoint, cursor, completeness, and row drift.  This
module does not claim that the page covers any link outside its four slots, or
that these bytes were written by a real filesystem/database.
-/
import Compiler.HyperdocumentCodec
import Compiler.Sp800185Cshake256
import Kernel.HyperdocumentIndexSync

namespace Minidregg.Compiler.HyperdocumentIndexPageMaterializer

open Minidregg.Compiler.HyperdocumentCodec
open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.HyperdocumentIndexSync
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Exact record codecs -/

abbrev LinkRecordTuple :=
  DocumentId × Option StableRange × LinkTarget × Digest × PrincipalRef ×
    OperationId × Option OperationId

noncomputable def linkRecordTupleStream : StreamCodec LinkRecordTuple :=
  StreamCodec.product (identifierStream .v1 .document)
    (StreamCodec.product (StreamCodec.option storedStableRangeStream)
      (StreamCodec.product linkTargetStream
        (StreamCodec.product digestStream
          (StreamCodec.product principalRefStream
            (StreamCodec.product (identifierStream .v1 .operationIntent)
              (StreamCodec.option
                (identifierStream .v1 .operationIntent)))))))

def linkRecordTuple (record : LinkRecord) : LinkRecordTuple :=
  ⟨record.sourceDocument, record.source, record.target, record.relation,
    record.author, record.operation, record.tombstonedAt⟩

def linkRecordOfTuple (wire : LinkRecordTuple) : LinkRecord where
  sourceDocument := wire.1
  source := wire.2.1
  target := wire.2.2.1
  relation := wire.2.2.2.1
  author := wire.2.2.2.2.1
  operation := wire.2.2.2.2.2.1
  tombstonedAt := wire.2.2.2.2.2.2

@[simp] theorem linkRecordOfTuple_tuple (record : LinkRecord) :
    linkRecordOfTuple (linkRecordTuple record) = record := by
  cases record
  rfl

noncomputable def linkRecordStream : StreamCodec LinkRecord :=
  StreamCodec.xmap linkRecordTupleStream linkRecordTuple linkRecordOfTuple
    linkRecordOfTuple_tuple

noncomputable def sourceEntryStream : StreamCodec SourceEntry :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .link) linkRecordStream)
    (fun entry => (entry.linkId, entry.record))
    (fun wire => ⟨wire.1, wire.2⟩)
    (by intro entry; rfl)

abbrev IndexedRowTuple :=
  LinkId × DocumentId × Option StableRange × LinkTarget × Digest × OperationId

noncomputable def indexedRowTupleStream : StreamCodec IndexedRowTuple :=
  StreamCodec.product (identifierStream .v1 .link)
    (StreamCodec.product (identifierStream .v1 .document)
      (StreamCodec.product (StreamCodec.option storedStableRangeStream)
        (StreamCodec.product linkTargetStream
          (StreamCodec.product digestStream
            (identifierStream .v1 .operationIntent)))))

def indexedRowTuple (row : IndexedRow) : IndexedRowTuple :=
  ⟨row.linkId, row.sourceDocument, row.sourceRange, row.target, row.relation,
    row.operation⟩

def indexedRowOfTuple (wire : IndexedRowTuple) : IndexedRow where
  linkId := wire.1
  sourceDocument := wire.2.1
  sourceRange := wire.2.2.1
  target := wire.2.2.2.1
  relation := wire.2.2.2.2.1
  operation := wire.2.2.2.2.2

@[simp] theorem indexedRowOfTuple_tuple (row : IndexedRow) :
    indexedRowOfTuple (indexedRowTuple row) = row := by
  cases row
  rfl

noncomputable def indexedRowStream : StreamCodec IndexedRow :=
  StreamCodec.xmap indexedRowTupleStream indexedRowTuple indexedRowOfTuple
    indexedRowOfTuple_tuple

def checkpointStream : StreamCodec CausalCheckpoint :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product (identifierStream .v1 .document)
        (StreamCodec.product
          (StreamCodec.option (identifierStream .v1 .versionEvent))
          StreamCodec.nat)))
    (fun checkpoint => (checkpoint.historyDomain, checkpoint.document,
      checkpoint.head, checkpoint.sequence))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro checkpoint; rfl)

def cursorStream : StreamCodec SyncCursor :=
  StreamCodec.xmap (StreamCodec.product checkpointStream StreamCodec.nat)
    (fun cursor => (cursor.checkpoint, cursor.nextSlot))
    (fun wire => ⟨wire.1, wire.2⟩)
    (by intro cursor; rfl)

/-! ## Fixed four-slot page -/

structure Slots (alpha : Type) where
  slot0 : alpha
  slot1 : alpha
  slot2 : alpha
  slot3 : alpha
  deriving DecidableEq

def Slots.at {alpha : Type} (slots : Slots alpha) (slot : Fin 4) : alpha :=
  if slot.val = 0 then slots.slot0
  else if slot.val = 1 then slots.slot1
  else if slot.val = 2 then slots.slot2
  else slots.slot3

def Slots.ofFunction {alpha : Type} (values : Fin 4 -> alpha) : Slots alpha :=
  ⟨values 0, values 1, values 2, values 3⟩

theorem Slots.at_ofFunction {alpha : Type} (values : Fin 4 -> alpha) :
    (Slots.ofFunction values).at = values := by
  funext slot
  fin_cases slot <;> rfl

def slotsStream {alpha : Type} (stream : StreamCodec alpha) :
    StreamCodec (Slots alpha) :=
  StreamCodec.xmap
    (StreamCodec.product stream
      (StreamCodec.product stream (StreamCodec.product stream stream)))
    (fun slots => (slots.slot0, slots.slot1, slots.slot2, slots.slot3))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro slots; cases slots; rfl)

structure Page where
  sourceCheckpoint : CausalCheckpoint
  indexCheckpoint : CausalCheckpoint
  cursor : SyncCursor
  source : Slots (Option SourceEntry)
  derived : Slots (Option IndexedRow)
  deriving DecidableEq

abbrev PageTuple :=
  CausalCheckpoint × CausalCheckpoint × SyncCursor ×
    Slots (Option SourceEntry) × Slots (Option IndexedRow)

noncomputable def pageTupleStream : StreamCodec PageTuple :=
  StreamCodec.product checkpointStream
    (StreamCodec.product checkpointStream
      (StreamCodec.product cursorStream
        (StreamCodec.product (slotsStream (StreamCodec.option sourceEntryStream))
          (slotsStream (StreamCodec.option indexedRowStream)))))

def pageTuple (page : Page) : PageTuple :=
  ⟨page.sourceCheckpoint, page.indexCheckpoint, page.cursor, page.source,
    page.derived⟩

def pageOfTuple (wire : PageTuple) : Page where
  sourceCheckpoint := wire.1
  indexCheckpoint := wire.2.1
  cursor := wire.2.2.1
  source := wire.2.2.2.1
  derived := wire.2.2.2.2

@[simp] theorem pageOfTuple_tuple (page : Page) :
    pageOfTuple (pageTuple page) = page := by
  cases page
  rfl

noncomputable def pageStream : StreamCodec Page :=
  StreamCodec.xmap pageTupleStream pageTuple pageOfTuple pageOfTuple_tuple

def Page.toSnapshot (page : Page) : Snapshot 4 where
  sourceCheckpoint := page.sourceCheckpoint
  indexCheckpoint := page.indexCheckpoint
  corpus := page.source.at
  index := page.derived.at
  cursor := page.cursor

def Page.ofSnapshot (snapshot : Snapshot 4) : Page where
  sourceCheckpoint := snapshot.sourceCheckpoint
  indexCheckpoint := snapshot.indexCheckpoint
  cursor := snapshot.cursor
  source := Slots.ofFunction snapshot.corpus
  derived := Slots.ofFunction snapshot.index

@[simp] theorem Page.toSnapshot_ofSnapshot (snapshot : Snapshot 4) :
    (Page.ofSnapshot snapshot).toSnapshot = snapshot := by
  cases snapshot
  simp [Page.ofSnapshot, Page.toSnapshot, Slots.at_ofFunction]

def Page.Fresh (page : Page) : Prop := page.toSnapshot.Fresh

def Page.status (page : Page) : Status :=
  Minidregg.Kernel.HyperdocumentIndexSync.status page.toSnapshot

def Page.advance (page : Page) (delta : Delta 4) : Page :=
  Page.ofSnapshot (page.toSnapshot.advance delta)

theorem Page.advance_fresh (page : Page) (delta : Delta 4)
    (fresh : page.Fresh) : (page.advance delta).Fresh := by
  unfold Page.advance Page.Fresh
  rw [Page.toSnapshot_ofSnapshot]
  exact Snapshot.advance_fresh page.toSnapshot delta fresh

/-! ## Framed canonical materializer -/

def schema : CellState.Schema where
  Field := Unit
  FieldType := fun _ => Page
  Resource := Empty
  ResourceType := Empty.elim
  Authority := fun resource => nomatch resource
  Evidence := fun resource => nomatch resource

instance : DecidableEq schema.Field := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq schema.Resource := fun resource => resource.elim

def stateOfOption : Option Page -> LogicalState schema
  | none =>
      { fields := 0
        resources := fun resource => nomatch resource }
  | some page =>
      { fields := (0 : FieldStore schema).write () page
        resources := fun resource => nomatch resource }

def pageAt (state : LogicalState schema) : Option Page := state.fields ()

theorem state_ext (state : LogicalState schema) :
    state = stateOfOption (pageAt state) := by
  cases state with
  | mk fields resources =>
      have resourcesExact : resources = fun resource => nomatch resource := by
        funext resource
        exact Empty.elim resource
      cases present : fields () with
      | none =>
          have fieldsExact : fields = (0 : FieldStore schema) := by
            apply DFinsupp.ext
            intro field
            cases field
            simpa using present
          rw [fieldsExact, resourcesExact]
          rfl
      | some page =>
          have fieldsExact :
              fields = (0 : FieldStore schema).write () page := by
            apply DFinsupp.ext
            intro field
            cases field
            simp [present]
          rw [fieldsExact, resourcesExact]
          rfl

noncomputable def stateStream : StreamCodec (LogicalState schema) :=
  StreamCodec.xmap (StreamCodec.option pageStream) pageAt stateOfOption
    (by intro state; exact (state_ext state).symm)

/-- `LOOM/HDOC/INDEXPAGE`, wire version 1, capacity 4. -/
def wireFrame : List UInt8 :=
  [76, 79, 79, 77, 47, 72, 68, 79, 67, 47, 73, 78, 68, 69, 88, 80, 65, 71,
    69, 1, 4]

noncomputable def decodeState : List UInt8 -> Option (LogicalState schema)
  | 76 :: 79 :: 79 :: 77 :: 47 :: 72 :: 68 :: 79 :: 67 :: 47 ::
      73 :: 78 :: 68 :: 69 :: 88 :: 80 :: 65 :: 71 :: 69 :: 1 :: 4 :: payload =>
      stateStream.toLawful.decode payload
  | _ => none

noncomputable def stateCodec : LawfulCodec (LogicalState schema) where
  encode state := wireFrame ++ stateStream.encode state
  decode := decodeState
  decode_encode := by
    intro state
    change stateStream.toLawful.decode (stateStream.encode state) = some state
    exact stateStream.toLawful.decode_encode state

def rootCustomization : List UInt8 :=
  [76, 79, 79, 77, 46, 72, 68, 79, 67, 46, 73, 78, 68, 69, 88, 80, 65, 71,
    69, 46, 82, 79, 79, 84, 47, 118, 49]

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash rootCustomization bytes).digest

noncomputable def materializer : CellState.Materializer schema Digest where
  codec := stateCodec
  rootBytes := rootBytes

@[simp] theorem decode_encode (state : LogicalState schema) :
    stateCodec.decode (stateCodec.encode state) = some state :=
  stateCodec.decode_encode state

@[simp] theorem reject_wrong_version (payload : List UInt8) :
    decodeState
      ([76, 79, 79, 77, 47, 72, 68, 79, 67, 47, 73, 78, 68, 69, 88, 80,
        65, 71, 69, 2, 4] ++ payload) = none := by
  simp [decodeState]

@[simp] theorem reject_wrong_capacity (payload : List UInt8) :
    decodeState
      ([76, 79, 79, 77, 47, 72, 68, 79, 67, 47, 73, 78, 68, 69, 88, 80,
        65, 71, 69, 1, 5] ++ payload) = none := by
  simp [decodeState]

/-! ## Pair-scoped binding boundary -/

structure Collision (left right : LogicalState schema) : Prop where
  statesDifferent : left ≠ right
  bytesDifferent : stateCodec.encode left ≠ stateCodec.encode right
  rootsEqual : rootBytes (stateCodec.encode left) =
    rootBytes (stateCodec.encode right)

structure PairBindingPremise (left right : LogicalState schema) : Prop where
  noCollision : ¬ Collision left right

theorem state_eq_of_root_eq {left right : LogicalState schema}
    (binding : PairBindingPremise left right)
    (sameRoot : rootBytes (stateCodec.encode left) =
      rootBytes (stateCodec.encode right)) : left = right := by
  by_contra different
  apply binding.noCollision
  refine ⟨different, ?_, sameRoot⟩
  intro sameBytes
  apply different
  have decoded := congrArg stateCodec.decode sameBytes
  simpa using decoded

/-! ## Axiom audit -/

/-- info: 'Minidregg.Compiler.HyperdocumentIndexPageMaterializer.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decode_encode
/-- info: 'Minidregg.Compiler.HyperdocumentIndexPageMaterializer.Page.advance_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Page.advance_fresh
/-- info: 'Minidregg.Compiler.HyperdocumentIndexPageMaterializer.state_eq_of_root_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms state_eq_of_root_eq

end Minidregg.Compiler.HyperdocumentIndexPageMaterializer
