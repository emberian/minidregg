/-
# Compiler.HyperdocumentEventPageMaterializer -- a bounded production page

The generic Hyperdocument event log is an unbounded dependent sparse map.  Its
existing deployed witness deliberately chooses a codec from `Countable` and a
byte-length root; that proves non-vacuity but is not a wire-format decision.

This module makes one narrower production decision.  A history segment is a
four-slot page.  Every slot is either empty or contains the exact typed event
key and `VersionEventRecord`; the page also binds its history domain, document,
and page number.  The canonical cell codec is a concrete prefix codec with a
stable version/capacity frame, and its root is the Lean cSHAKE256 computation
over those exact framed bytes.  A page projects into the existing sparse event
log, rather than defining a second history meaning.

Four slots bound the materialized *scope*, not the global history: another
page number names the next segment.  Digest collision resistance remains an
explicit pair-scoped premise.  In particular this file does not assert an
impossible injection from all byte strings into a 256-bit hash range.
-/
import Compiler.HyperdocumentCodec
import Compiler.Sp800185Cshake256
import Kernel.HyperdocumentEventLog

namespace Minidregg.Compiler.HyperdocumentEventPageMaterializer

open Minidregg.Compiler.HyperdocumentCodec
open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CausalVersionDag
open Minidregg.Theory.CellState
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Exact event codecs -/

/-- First-order wire tuple for the generic causal event preimage. -/
abbrev EventPreimageTuple :=
  Digest × Digest × SchemaRef × Nat × Digest × Digest × Digest × List Digest ×
    Digest × Digest × Digest × Digest

def eventPreimageTupleStream : StreamCodec EventPreimageTuple :=
  StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product schemaRefStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product digestStream (StreamCodec.product digestStream
        (StreamCodec.product digestStream
          (StreamCodec.product (StreamCodec.list digestStream)
            (StreamCodec.product digestStream (StreamCodec.product digestStream
              (StreamCodec.product digestStream digestStream))))))))))

def eventPreimageTuple (event : EventPreimage) : EventPreimageTuple :=
  ⟨event.historyDomain, event.streamId, event.schema, event.semanticVersion,
    event.semanticObjectRoot, event.preStateRoot, event.postStateRoot,
    event.parentFrontier, event.authorId, event.principalId, event.requestId,
    event.effectId⟩

def eventPreimageOfTuple (tuple : EventPreimageTuple) : EventPreimage where
  historyDomain := tuple.1
  streamId := tuple.2.1
  schema := tuple.2.2.1
  semanticVersion := tuple.2.2.2.1
  semanticObjectRoot := tuple.2.2.2.2.1
  preStateRoot := tuple.2.2.2.2.2.1
  postStateRoot := tuple.2.2.2.2.2.2.1
  parentFrontier := tuple.2.2.2.2.2.2.2.1
  authorId := tuple.2.2.2.2.2.2.2.2.1
  principalId := tuple.2.2.2.2.2.2.2.2.2.1
  requestId := tuple.2.2.2.2.2.2.2.2.2.2.1
  effectId := tuple.2.2.2.2.2.2.2.2.2.2.2

@[simp] theorem eventPreimageOfTuple_tuple (event : EventPreimage) :
    eventPreimageOfTuple (eventPreimageTuple event) = event :=
  rfl

/-- Compact base-255 naturals and length-delimited lists make this an actual
wire codec, rather than a countability-selected inhabitant. -/
def eventPreimageStream : StreamCodec EventPreimage :=
  StreamCodec.xmap eventPreimageTupleStream eventPreimageTuple
    eventPreimageOfTuple eventPreimageOfTuple_tuple

def eventPreimageCodec : LawfulCodec EventPreimage :=
  eventPreimageStream.toLawful

/-- A stored event is encoded as its complete causal preimage plus the typed
author needed to reconstruct `VersionEventRecord`.  The projection's author
and principal digests are therefore committed twice and checked by page
validity below, rather than silently trusted during decode. -/
def versionEventRecordStream : StreamCodec VersionEventRecord :=
  StreamCodec.xmap
    (StreamCodec.product eventPreimageStream principalRefStream)
    (fun event => (event.toCausalPreimage, event.author))
    (fun wire => VersionEventRecord.ofCausalPreimage wire.2 wire.1)
    VersionEventRecord.ofCausalPreimage_toCausalPreimage

def versionEventRecordCodec : LawfulCodec VersionEventRecord :=
  versionEventRecordStream.toLawful

/-! ## A four-slot canonical history page -/

structure Entry where
  key : VersionEventId
  record : VersionEventRecord
  deriving DecidableEq, Repr

def entryStream : StreamCodec Entry :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .versionEvent)
      versionEventRecordStream)
    (fun entry => (entry.key, entry.record))
    (fun wire => ⟨wire.1, wire.2⟩)
    (by intro entry; rfl)

/-- A page is deliberately fixed at four slots.  This gives a finite opening
scope without claiming that the history, identifiers, or semantic values are
globally finite. -/
structure Page where
  historyDomain : Digest
  document : DocumentId
  pageNumber : Nat
  slot0 : Option Entry
  slot1 : Option Entry
  slot2 : Option Entry
  slot3 : Option Entry
  deriving DecidableEq, Repr

abbrev PageTuple :=
  Digest × DocumentId × Nat × Option Entry × Option Entry × Option Entry ×
    Option Entry

def pageTupleStream : StreamCodec PageTuple :=
  StreamCodec.product digestStream
    (StreamCodec.product (identifierStream .v1 .document)
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product (StreamCodec.option entryStream)
          (StreamCodec.product (StreamCodec.option entryStream)
            (StreamCodec.product (StreamCodec.option entryStream)
              (StreamCodec.option entryStream))))))

def pageTuple (page : Page) : PageTuple :=
  ⟨page.historyDomain, page.document, page.pageNumber, page.slot0, page.slot1,
    page.slot2, page.slot3⟩

def pageOfTuple (tuple : PageTuple) : Page where
  historyDomain := tuple.1
  document := tuple.2.1
  pageNumber := tuple.2.2.1
  slot0 := tuple.2.2.2.1
  slot1 := tuple.2.2.2.2.1
  slot2 := tuple.2.2.2.2.2.1
  slot3 := tuple.2.2.2.2.2.2

@[simp] theorem pageOfTuple_tuple (page : Page) :
    pageOfTuple (pageTuple page) = page :=
  rfl

def pageStream : StreamCodec Page :=
  StreamCodec.xmap pageTupleStream pageTuple pageOfTuple pageOfTuple_tuple

def Page.entries (page : Page) : List Entry :=
  [page.slot0, page.slot1, page.slot2, page.slot3].filterMap id

@[simp] theorem Page.entries_length_le_four (page : Page) :
    page.entries.length ≤ 4 := by
  rcases page with ⟨historyDomain, document, pageNumber, slot0, slot1, slot2, slot3⟩
  cases slot0 <;> cases slot1 <;> cases slot2 <;> cases slot3 <;>
    simp [Page.entries, _root_.id]

/-! ## The exact bounded cell materializer -/

/-- One typed page payload and no resource side table. -/
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

def pageAt (state : LogicalState schema) : Option Page :=
  state.fields ()

theorem state_ext (state : LogicalState schema) :
    state = stateOfOption (pageAt state) := by
  cases state with
  | mk fields resources =>
      have resourcesExact :
          resources = fun resource => nomatch resource := by
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

def stateStream : StreamCodec (LogicalState schema) :=
  StreamCodec.xmap (StreamCodec.option pageStream) pageAt stateOfOption
    (by intro state; exact (state_ext state).symm)

/-- Stable outer marker: `LOOM/HDOC/EVENTPAGE`, wire version 1, capacity 4. -/
def wireFrame : List UInt8 :=
  [76, 79, 79, 77, 47, 72, 68, 79, 67, 47, 69, 86, 69, 78, 84, 80, 65, 71, 69,
    1, 4]

def decodeState : List UInt8 -> Option (LogicalState schema)
  | 76 :: 79 :: 79 :: 77 :: 47 :: 72 :: 68 :: 79 :: 67 :: 47 ::
      69 :: 86 :: 69 :: 78 :: 84 :: 80 :: 65 :: 71 :: 69 :: 1 :: 4 :: payload =>
      stateStream.toLawful.decode payload
  | _ => none

/-- The concrete deployed codec.  Absence/presence is tagged by
`StreamCodec.option`; every sequence and natural is prefix decodable. -/
def stateCodec : LawfulCodec (LogicalState schema) where
  encode state := wireFrame ++ stateStream.encode state
  decode := decodeState
  decode_encode := by
    intro state
    change stateStream.toLawful.decode (stateStream.encode state) = some state
    exact stateStream.toLawful.decode_encode state

/-- Exact cSHAKE customization for page roots. -/
def rootCustomization : List UInt8 :=
  [76, 79, 79, 77, 46, 72, 68, 79, 67, 46, 69, 86, 69, 78, 84, 80, 65, 71, 69,
    46, 82, 79, 79, 84, 47, 118, 49]

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash rootCustomization bytes).digest

def materializer : CellState.Materializer schema Digest where
  codec := stateCodec
  rootBytes := rootBytes

@[simp] theorem encode_absent :
    stateCodec.encode (stateOfOption none) = wireFrame ++ [0] :=
  rfl

@[simp] theorem encode_present (page : Page) :
    stateCodec.encode (stateOfOption (some page)) =
      wireFrame ++ 1 :: pageStream.encode page :=
  rfl

@[simp] theorem decode_encode (state : LogicalState schema) :
    stateCodec.decode (stateCodec.encode state) = some state :=
  stateCodec.decode_encode state

/-- Wire version and capacity are admission data, not advisory metadata. -/
@[simp] theorem reject_wrong_version (payload : List UInt8) :
    decodeState
      ([76, 79, 79, 77, 47, 72, 68, 79, 67, 47, 69, 86, 69, 78, 84, 80,
        65, 71, 69, 2, 4] ++ payload) = none := by
  simp [decodeState]

@[simp] theorem reject_wrong_capacity (payload : List UInt8) :
    decodeState
      ([76, 79, 79, 77, 47, 72, 68, 79, 67, 47, 69, 86, 69, 78, 84, 80,
        65, 71, 69, 1, 5] ++ payload) = none := by
  simp [decodeState]

/-! ## Honest root binding boundary -/

/-- The precise collision event exposed by this representation.  It names two
different canonical payloads, their different framed bytes, and one equal
cSHAKE root. -/
structure Collision (left right : LogicalState schema) : Prop where
  statesDifferent : left ≠ right
  bytesDifferent : stateCodec.encode left ≠ stateCodec.encode right
  rootsEqual : rootBytes (stateCodec.encode left) =
    rootBytes (stateCodec.encode right)

theorem collision_of_root_eq_of_ne
    {left right : LogicalState schema} (different : left ≠ right)
    (sameRoot : rootBytes (stateCodec.encode left) =
      rootBytes (stateCodec.encode right)) :
    Collision left right where
  statesDifferent := different
  bytesDifferent := by
    intro sameBytes
    apply different
    exact lawfulCodec_encode_injective stateCodec sameBytes
  rootsEqual := sameRoot

/-- Pair-scoped collision-resistance premise.  A concrete security reduction
must discharge this for the compared canonical page payloads; no universal
finite-digest injection is postulated. -/
structure PairBindingPremise (left right : LogicalState schema) : Prop where
  noCollision : ¬ Collision left right

theorem state_eq_of_root_eq
    {left right : LogicalState schema}
    (binding : PairBindingPremise left right)
    (sameRoot : rootBytes (stateCodec.encode left) =
      rootBytes (stateCodec.encode right)) :
    left = right := by
  by_contra different
  exact binding.noCollision (collision_of_root_eq_of_ne different sameRoot)

/-! ## Projection into the canonical append-only event log -/

def installEntry
    (store : Kernel.HyperdocumentEventLog.Sparse.Store) (entry : Entry) :
    Kernel.HyperdocumentEventLog.Sparse.Store :=
  Minidregg.Kernel.SparseAuthenticatedState.Store.set store .events entry.key
    (some entry.record)

/-- A page is only a bounded representation segment.  Its meaning is the
existing canonical sparse event-log store obtained by installing each occupied
slot in slot order. -/
def Page.toSparseStore (page : Page) :
    Kernel.HyperdocumentEventLog.Sparse.Store :=
  page.entries.foldl installEntry Kernel.HyperdocumentEventLog.Sparse.empty

/-- The cSHAKE content-addressing scheme used to validate page entries. -/
def eventCustomization : List UInt8 :=
  [76, 79, 79, 77, 46, 72, 68, 79, 67, 46, 86, 69, 82, 83, 73, 79, 78, 46,
    69, 86, 69, 78, 84, 47, 118, 49]

theorem root_and_event_domains_distinct :
    rootCustomization ≠ eventCustomization := by
  decide

def eventDerivation : DigestDerivation where
  digestBytes bytes := (Sp800185Cshake256.hash eventCustomization bytes).digest

def eventScheme : ContentAddressing :=
  causalVersionAddressing eventPreimageCodec eventDerivation

def Entry.ValidFor (page : Page) (entry : Entry) : Prop :=
  entry.record.historyDomain = page.historyDomain ∧
  entry.record.document = page.document ∧
  entry.record.CausallyWellFormed ∧
  entry.key.digest = eventScheme.address entry.record.toCausalPreimage

/-- Representation validity is separate from decoding.  It checks page scope,
canonical event addressing, and duplicate-key exclusion without allowing a
decoder to manufacture proof objects. -/
structure Page.Valid (page : Page) : Prop where
  entriesValid : ∀ entry, entry ∈ page.entries -> entry.ValidFor page
  keysNodup : (page.entries.map Entry.key).Nodup

/-! ## A closed deployed page and accepted materialization -/

def exampleAuthor : PrincipalRef :=
  ⟨⟨7⟩, .object, ⟨11⟩⟩

def exampleRecord : VersionEventRecord where
  historyDomain := ⟨1001⟩
  document := ⟨⟨2002⟩⟩
  schema := ⟨⟨3003⟩, 1⟩
  semanticVersion := 1
  operation := ⟨⟨4004⟩⟩
  parents := []
  preStateRoot := ⟨5005⟩
  postStateRoot := ⟨5006⟩
  requestId := ⟨6006⟩
  effectId := ⟨7007⟩
  author := exampleAuthor

def exampleEntry : Entry where
  key := deriveVersionEventId eventPreimageCodec eventDerivation exampleRecord
  record := exampleRecord

def examplePage : Page where
  historyDomain := exampleRecord.historyDomain
  document := exampleRecord.document
  pageNumber := 0
  slot0 := some exampleEntry
  slot1 := none
  slot2 := none
  slot3 := none

theorem examplePage_valid : examplePage.Valid := by
  constructor
  · intro entry member
    have entryExact : entry = exampleEntry := by
      simpa [examplePage, Page.entries, _root_.id] using member
    subst entryExact
    have wellFormed : exampleRecord.CausallyWellFormed := by
      constructor <;>
        simp [exampleRecord, VersionEventRecord.toCausalPreimage]
    exact ⟨rfl, rfl, wellFormed,
      deriveVersionEventId_address_exact eventPreimageCodec eventDerivation
        exampleRecord⟩
  · simp [examplePage, Page.entries]

def emptyCell : Materialized materializer :=
  CellState.materialize materializer (stateOfOption none)

def exampleCell : Materialized materializer :=
  CellState.materialize materializer (stateOfOption (some examplePage))

@[simp] theorem exampleCell_bytes :
    exampleCell.bytes = wireFrame ++ 1 :: pageStream.encode examplePage :=
  rfl

@[simp] theorem exampleCell_root :
    exampleCell.root =
      (Sp800185Cshake256.hash rootCustomization
        (wireFrame ++ 1 :: pageStream.encode examplePage)).digest :=
  rfl

@[simp] theorem exampleSparseStore_contains :
    examplePage.toSparseStore .events exampleEntry.key =
      some exampleRecord := by
  simp [Page.toSparseStore, Page.entries, examplePage, installEntry,
    exampleEntry, _root_.id]
  rfl

/-- The exact one-field patch which installs this four-slot page. -/
def installPatch : CellState.Patch schema Digest where
  expectedPreRoot := emptyCell.root
  fieldFootprint := {()}
  resourceFootprint := ∅
  fieldWrites := [{ field := (), value := some examplePage }]
  resourceWrites := []

theorem installPatch_accepted :
    ∃ validated : CellState.ValidatedPatch materializer emptyCell installPatch,
      CellState.validate materializer emptyCell installPatch =
        CellState.ValidationOutcome.accepted validated := by
  unfold CellState.validate
  rw [dif_pos (show installPatch.expectedPreRoot = emptyCell.root from rfl)]
  rw [dif_pos
    (show installPatch.fieldFootprint = installPatch.namedFields by decide)]
  rw [dif_pos
    (show installPatch.resourceFootprint = installPatch.namedResources by decide)]
  exact ⟨_, rfl⟩

theorem accepted_post_exact
    (validated : CellState.ValidatedPatch materializer emptyCell installPatch) :
    validated.apply = exampleCell := by
  apply CellState.Materialized.ext
  congr 1

/-! ## Axiom pins -/

/-- info: 'Minidregg.Compiler.HyperdocumentEventPageMaterializer.eventPreimageOfTuple_tuple' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms eventPreimageOfTuple_tuple
/-- info: 'Minidregg.Compiler.HyperdocumentEventPageMaterializer.stateCodec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stateCodec
/-- info: 'Minidregg.Compiler.HyperdocumentEventPageMaterializer.collision_of_root_eq_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms collision_of_root_eq_of_ne
/-- info: 'Minidregg.Compiler.HyperdocumentEventPageMaterializer.examplePage_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms examplePage_valid
/-- info: 'Minidregg.Compiler.HyperdocumentEventPageMaterializer.installPatch_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms installPatch_accepted

end Minidregg.Compiler.HyperdocumentEventPageMaterializer
