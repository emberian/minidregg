/-
# Compiler.DeclaredEffectPageMaterializer -- bounded declared-effect shards

`DeclaredTurn.effectSchema` is an unbounded sparse map.  Its deployed
materializer is an honest inhabitation witness, but its countability-selected
codec and byte-length root are not a production representation.  This module
adds one deliberately narrower representation: a four-entry shard of the
canonical declared-effect state, with stable V1 bytes and a Lean cSHAKE256
root over those exact bytes.

The shard does not pretend that all effect addresses fit in one finite cell.
Addresses are assigned to one of sixteen shards; admission rejects an address
owned by another shard and rejects a fifth resident key.  A page projects into
the existing `DeclaredTurn.effectSchema`, so it introduces no second effect
meaning.  `AcceptedDelta` ties an already-authorized `AcceptedCellEffect` to
exact pre/post pages and derives the only page patch, bytes, and root from that
pair.  The closed transfer witness below crosses this boundary end to end.

Collision resistance and physical persistence remain separate premises.  In
particular, no finite page is claimed to be a total representation of the
unbounded canonical schema.
-/
import Compiler.Sp800185Cshake256
import Compiler.Tower256ConcreteBackend
import Kernel.DeclaredHyperedgeWitness
import Theory.DeclaredActionLowering

namespace Minidregg.Compiler.DeclaredEffectPageMaterializer

open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CanonicalTransition
open Minidregg.Theory.CellState
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Stable first-order entries -/

def intStream : StreamCodec Int :=
  StreamCodec.xmap StreamCodec.nat EffectDeclaration.encodeInt decodeInt
    decodeInt_encodeInt

def stateKeyStream : StreamCodec StateKey where
  encode
    | .objectField object field =>
        0 :: StreamCodec.nat.encode object.value ++ digestStream.encode field
    | .accountBalance account resource =>
        1 :: StreamCodec.nat.encode account.value ++ digestStream.encode resource
    | .programCode program =>
        2 :: StreamCodec.nat.encode program.value
  decodePrefix
    | 0 :: bytes => do
        let (object, afterObject) <- StreamCodec.nat.decodePrefix bytes
        let (field, suffix) <- digestStream.decodePrefix afterObject
        some (.objectField ⟨object⟩ field, suffix)
    | 1 :: bytes => do
        let (account, afterAccount) <- StreamCodec.nat.decodePrefix bytes
        let (resource, suffix) <- digestStream.decodePrefix afterAccount
        some (.accountBalance ⟨account⟩ resource, suffix)
    | 2 :: bytes => do
        let (program, suffix) <- StreamCodec.nat.decodePrefix bytes
        some (.programCode ⟨program⟩, suffix)
    | _ => none
  decodePrefix_encode := by
    intro key suffix
    cases key with
    | objectField object field =>
        simp [List.append_assoc, StreamCodec.nat.decodePrefix_encode,
          digestStream.decodePrefix_encode]
    | accountBalance account resource =>
        simp [List.append_assoc, StreamCodec.nat.decodePrefix_encode,
          digestStream.decodePrefix_encode]
    | programCode program =>
        simp [StreamCodec.nat.decodePrefix_encode]

structure Entry where
  key : StateKey
  value : Int
  deriving DecidableEq, Repr

def entryStream : StreamCodec Entry :=
  StreamCodec.xmap (StreamCodec.product stateKeyStream intStream)
    (fun entry => (entry.key, entry.value))
    (fun wire => ⟨wire.1, wire.2⟩)
    (by intro entry; rfl)

def Entry.install
    (fields : FieldStore DeclaredTurn.effectSchema.{0, 0}) (entry : Entry) :
    FieldStore DeclaredTurn.effectSchema.{0, 0} :=
  fields.write entry.key entry.value

/-! ## Four-entry, sixteen-way address shards -/

def shardCount : Nat := 16

/-- Account balances are sharded by their complete resource identifier, so a
balanced source/destination move remains local.  Object and program state are
sharded by their primary typed resource identifier. -/
def addressShard : StateKey -> Nat
  | .objectField object _ => object.value % shardCount
  | .accountBalance _ resource => resource.value % shardCount
  | .programCode program => program.value % shardCount

structure Page where
  effectDomain : Digest
  shardNumber : Nat
  slot0 : Option Entry
  slot1 : Option Entry
  slot2 : Option Entry
  slot3 : Option Entry
  deriving DecidableEq, Repr

abbrev PageTuple :=
  Digest × Nat × Option Entry × Option Entry × Option Entry ×
    Option Entry

def pageTupleStream : StreamCodec PageTuple :=
  StreamCodec.product digestStream
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product (StreamCodec.option entryStream)
        (StreamCodec.product (StreamCodec.option entryStream)
          (StreamCodec.product (StreamCodec.option entryStream)
            (StreamCodec.option entryStream)))))

def pageTuple (page : Page) : PageTuple :=
  ⟨page.effectDomain, page.shardNumber, page.slot0, page.slot1, page.slot2,
    page.slot3⟩

def pageOfTuple (tuple : PageTuple) : Page where
  effectDomain := tuple.1
  shardNumber := tuple.2.1
  slot0 := tuple.2.2.1
  slot1 := tuple.2.2.2.1
  slot2 := tuple.2.2.2.2.1
  slot3 := tuple.2.2.2.2.2

@[simp] theorem pageOfTuple_tuple (page : Page) :
    pageOfTuple (pageTuple page) = page :=
  rfl

def pageStream : StreamCodec Page :=
  StreamCodec.xmap pageTupleStream pageTuple pageOfTuple pageOfTuple_tuple

def Page.entries (page : Page) : List Entry :=
  [page.slot0, page.slot1, page.slot2, page.slot3].filterMap _root_.id

def Page.keys (page : Page) : List StateKey :=
  page.entries.map Entry.key

def Page.Owns (page : Page) (key : StateKey) : Prop :=
  addressShard key = page.shardNumber

def Page.Valid (page : Page) : Prop :=
  page.shardNumber < shardCount /\ page.keys.Nodup /\
    ∀ entry ∈ page.entries, page.Owns entry.key

instance pageValidDecidable (page : Page) : Decidable page.Valid := by
  unfold Page.Valid Page.Owns Page.keys
  infer_instance

instance pageOwnsDecidable (page : Page) (key : StateKey) :
    Decidable (page.Owns key) := by
  unfold Page.Owns
  infer_instance

@[simp] theorem Page.entries_length_le_four (page : Page) :
    page.entries.length ≤ 4 := by
  rcases page with ⟨domain, shard, slot0, slot1, slot2, slot3⟩
  cases slot0 <;> cases slot1 <;> cases slot2 <;> cases slot3 <;>
    simp [Page.entries]

def Page.toCanonicalState (page : Page) :
    LogicalState DeclaredTurn.effectSchema.{0, 0} where
  fields := page.entries.foldl Entry.install 0
  resources := fun resource => nomatch resource

def Page.lookup (page : Page) (key : StateKey) : Option Int :=
  page.toCanonicalState.fields key

/-! ## Executable fail-closed checked-write admission -/

inductive RejectReason where
  | invalidPage
  | unsupportedAddress
  | guardMismatch
  | overflow
  deriving DecidableEq, Repr

def replaceSlot (slot : Option Entry) (key : StateKey)
    (replacement : Option Int) : Option Entry :=
  match slot with
  | none => none
  | some entry =>
      if entry.key = key then replacement.map fun value => ⟨key, value⟩
      else some entry

def Page.replaceExisting (page : Page) (key : StateKey)
    (replacement : Option Int) : Page :=
  { page with
    slot0 := replaceSlot page.slot0 key replacement
    slot1 := replaceSlot page.slot1 key replacement
    slot2 := replaceSlot page.slot2 key replacement
    slot3 := replaceSlot page.slot3 key replacement }

/-- Fill the first empty slot.  There is no eviction or implicit next-page
allocation at this representation boundary. -/
def Page.insert? (page : Page) (entry : Entry) : Option Page :=
  match page.slot0 with
  | none => some { page with slot0 := some entry }
  | some _ =>
      match page.slot1 with
      | none => some { page with slot1 := some entry }
      | some _ =>
          match page.slot2 with
          | none => some { page with slot2 := some entry }
          | some _ =>
              match page.slot3 with
              | none => some { page with slot3 := some entry }
              | some _ => none

def checkedPost (page : Page) : Except RejectReason Page :=
  if page.Valid then .ok page else .error .invalidPage

/-- Execute one declaration-derived checked write.  The guard compares the
exact sparse presence/value, so an absent entry is not confused with stored
zero. -/
def Page.applyWrite (page : Page) (write : CheckedWrite) :
    Except RejectReason Page :=
  if _valid : page.Valid then
    if _owned : page.Owns write.key then
      if _guard : page.lookup write.key = write.expected then
        match page.lookup write.key, write.replacement with
        | some _, replacement =>
            checkedPost (page.replaceExisting write.key replacement)
        | none, none => .ok page
        | none, some value =>
            match page.insert? ⟨write.key, value⟩ with
            | none => .error .overflow
            | some post => checkedPost post
      else .error .guardMismatch
    else .error .unsupportedAddress
  else .error .invalidPage

def Page.applyWrites : Page -> List CheckedWrite -> Except RejectReason Page
  | page, [] => .ok page
  | page, write :: writes => do
      let post <- page.applyWrite write
      post.applyWrites writes

/-! ## General correspondence with the canonical guarded-write fold -/

private theorem empty_fields_apply (key : StateKey) :
    (0 : FieldStore DeclaredTurn.effectSchema.{0, 0}) key = none := rfl

private theorem entry_install_apply
    (fields : FieldStore DeclaredTurn.effectSchema.{0, 0})
    (entry : Entry) (key : StateKey) :
    Entry.install fields entry key =
      if entry.key = key then some entry.value else fields key := by
  by_cases same : entry.key = key
  · subst key
    simpa only [if_pos rfl] using
      (FieldStore.write_self fields entry.key entry.value)
  · simpa [Entry.install, same] using
      (FieldStore.write_other fields same entry.value)

private theorem fields_assign_apply
    (fields : FieldStore DeclaredTurn.effectSchema.{0, 0})
    (key query : StateKey) (replacement : Option Int) :
    fields.assign key replacement query =
      if key = query then replacement else fields query := by
  by_cases same : key = query
  · subst query
    simpa [FieldStore.read] using
      (FieldStore.read_assign_self fields key replacement)
  · simpa [FieldStore.read, same] using
      (FieldStore.read_assign_other fields same replacement)

set_option maxHeartbeats 1600000 in
/-- Replacing a present page entry is exactly canonical sparse assignment.
This includes explicit deletion and does not depend on a closed sample page. -/
theorem Page.replaceExisting_fields (page : Page) (key : StateKey)
    (replacement : Option Int) (present : page.lookup key ≠ none) :
    (page.replaceExisting key replacement).toCanonicalState.fields =
      page.toCanonicalState.fields.assign key replacement := by
  rcases page with ⟨domain, shard, slot0, slot1, slot2, slot3⟩
  cases slot0 <;> cases slot1 <;> cases slot2 <;> cases slot3 <;>
    cases replacement <;>
    apply DFinsupp.ext <;> intro query
  all_goals
    simp only [Page.lookup, Page.toCanonicalState, Page.entries,
      Page.replaceExisting, replaceSlot, List.filterMap_cons, List.filterMap_nil,
      Option.map_none, Option.map_some, fields_assign_apply] at *
    repeat' first
      | rfl
      | fail_if_no_progress simp_all [entry_install_apply, empty_fields_apply]
      | fail_if_no_progress split_ifs at *
    all_goals exact present rfl

set_option maxHeartbeats 800000 in
/-- Insertion at an absent sparse key is the same assignment regardless of
which physical slot was free. Full pages still refuse through `insert?`. -/
theorem Page.insert_fields (page post : Page) (entry : Entry)
    (absent : page.lookup entry.key = none)
    (inserted : page.insert? entry = some post) :
    post.toCanonicalState.fields =
      page.toCanonicalState.fields.assign entry.key (some entry.value) := by
  rcases page with ⟨domain, shard, slot0, slot1, slot2, slot3⟩
  cases slot0 <;> cases slot1 <;> cases slot2 <;> cases slot3 <;>
    simp only [Page.insert?, Option.some.injEq, reduceCtorEq] at inserted
  all_goals
    subst post
    apply DFinsupp.ext
    intro query
    simp only [Page.lookup, Page.toCanonicalState, Page.entries,
      List.filterMap_cons, List.filterMap_nil, fields_assign_apply] at *
    repeat' first
      | rfl
      | fail_if_no_progress simp_all [entry_install_apply, empty_fields_apply]
      | fail_if_no_progress split_ifs at *

private theorem checkedPost_success {candidate post : Page}
    (success : checkedPost candidate = .ok post) : candidate.Valid ∧ candidate = post := by
  unfold checkedPost at success
  split at success
  · rename_i valid
    exact ⟨valid, Except.ok.inj success⟩
  · cases success

/-- Every successful physical write retains exact sparse guard values and
performs the canonical assignment. Page validity is preserved by the actual
checked execution, including the absence-to-absence case. -/
theorem Page.applyWrite_spec {page post : Page} {write : CheckedWrite}
    (success : page.applyWrite write = .ok post) :
    post.Valid ∧ page.lookup write.key = write.expected ∧
      post.toCanonicalState.fields =
        page.toCanonicalState.fields.assign write.key write.replacement := by
  unfold Page.applyWrite at success
  split at success
  · rename_i valid
    split at success
    · rename_i owned
      split at success
      · rename_i guard
        cases found : page.lookup write.key with
        | none =>
            cases replaced : write.replacement with
            | none =>
                simp only [found, replaced] at success
                have same : page = post := Except.ok.inj success
                subst post
                refine ⟨valid, by simpa only [found] using guard, ?_⟩
                apply DFinsupp.ext
                intro query
                rw [fields_assign_apply]
                split
                · rename_i sameKey
                  subst query
                  exact found
                · rfl
            | some value =>
                simp only [found, replaced] at success
                cases inserted : page.insert? ⟨write.key, value⟩ with
                | none =>
                    simp only [inserted] at success
                    cases success
                | some candidate =>
                    simp only [inserted] at success
                    obtain ⟨postValid, same⟩ := checkedPost_success success
                    subst post
                    refine ⟨postValid, by simpa only [found] using guard, ?_⟩
                    simpa only [replaced] using
                      (page.insert_fields candidate ⟨write.key, value⟩ found inserted)
        | some value =>
            simp only [found] at success
            obtain ⟨postValid, same⟩ := checkedPost_success success
            subst post
            refine ⟨postValid, by simpa only [found] using guard, ?_⟩
            apply page.replaceExisting_fields
            rw [found]
            simp
      · cases success
    · cases success
  · cases success

/-- The actual page executor reflects into the one canonical ordered guarded
fold. Repeated keys and aliased actions use each intermediate state, preserving
absence separately from stored zero. No authorization is inferred here. -/
theorem Page.applyWrites_checked {page post : Page} {writes : List CheckedWrite}
    (success : page.applyWrites writes = .ok post) :
    runCheckedWrites writes page.toCanonicalState.fields =
      some post.toCanonicalState.fields := by
  induction writes generalizing page with
  | nil =>
      have same : page = post := Except.ok.inj success
      subst post
      rfl
  | cons write writes induction =>
      cases first : page.applyWrite write with
      | error reason =>
          simp only [Page.applyWrites, first] at success
          cases success
      | ok middle =>
          have tail : middle.applyWrites writes = .ok post := by
            simpa [Page.applyWrites, first] using success
          obtain ⟨_, guard, fields⟩ := Page.applyWrite_spec first
          simp only [runCheckedWrites,
            show page.toCanonicalState.fields write.key = write.expected from guard]
          rw [← fields]
          exact induction tail

/-- Empty batches retain their input's validity; every nonempty successful
step obtains validity from the physical executor's mandatory checks. -/
theorem Page.applyWrites_valid {page post : Page} {writes : List CheckedWrite}
    (valid : page.Valid) (success : page.applyWrites writes = .ok post) :
    post.Valid := by
  induction writes generalizing page with
  | nil =>
      have same : page = post := Except.ok.inj success
      subst post
      exact valid
  | cons write writes induction =>
      cases first : page.applyWrite write with
      | error reason =>
          simp only [Page.applyWrites, first] at success
          cases success
      | ok middle =>
          have tail : middle.applyWrites writes = .ok post := by
            simpa [Page.applyWrites, first] using success
          exact induction (Page.applyWrite_spec first).1 tail

/-! ## Concrete framed materialization -/

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

/-- Stable marker: `LOOM/EFFECT/PAGE`, wire version 1, capacity 4, shard
modulus 16.  All four numbers are consensus pins. -/
def wireFrame : List UInt8 :=
  [76, 79, 79, 77, 47, 69, 70, 70, 69, 67, 84, 47, 80, 65, 71, 69,
    1, 4, 16]

def decodeState : List UInt8 -> Option (LogicalState schema)
  | 76 :: 79 :: 79 :: 77 :: 47 :: 69 :: 70 :: 70 :: 69 :: 67 :: 84 :: 47 ::
      80 :: 65 :: 71 :: 69 :: 1 :: 4 :: 16 :: payload =>
      stateStream.toLawful.decode payload
  | _ => none

def stateCodec : LawfulCodec (LogicalState schema) where
  encode state := wireFrame ++ stateStream.encode state
  decode := decodeState
  decode_encode := by
    intro state
    change stateStream.toLawful.decode (stateStream.encode state) = some state
    exact stateStream.toLawful.decode_encode state

def rootCustomization : List UInt8 :=
  [76, 79, 79, 77, 46, 69, 70, 70, 69, 67, 84, 46, 80, 65, 71, 69,
    46, 82, 79, 79, 84, 47, 118, 49]

theorem wire_and_root_domains_distinct : wireFrame ≠ rootCustomization := by
  decide

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

@[simp] theorem reject_wrong_version (payload : List UInt8) :
    decodeState
      ([76, 79, 79, 77, 47, 69, 70, 70, 69, 67, 84, 47, 80, 65, 71, 69,
        2, 4, 16] ++ payload) = none := by
  simp [decodeState]

@[simp] theorem reject_wrong_capacity (payload : List UInt8) :
    decodeState
      ([76, 79, 79, 77, 47, 69, 70, 70, 69, 67, 84, 47, 80, 65, 71, 69,
        1, 5, 16] ++ payload) = none := by
  simp [decodeState]

@[simp] theorem reject_wrong_shard_modulus (payload : List UInt8) :
    decodeState
      ([76, 79, 79, 77, 47, 69, 70, 70, 69, 67, 84, 47, 80, 65, 71, 69,
        1, 4, 32] ++ payload) = none := by
  simp [decodeState]

/-! ## Exact accepted-effect to page refinement -/

/-- A proof-relevant representation boundary.  The accepted effect remains
the semantic authority; pages merely exhibit exact finite pre/post projections
for that one transition. -/
structure AcceptedDelta
    {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M}
    {declaration : DeclaredActionLowering.Declaration target}
    (accepted : Accepted portal authState context pre declaration) where
  prePage : Page
  postPage : Page
  preValid : prePage.Valid
  executorExact :
    prePage.applyWrites declaration.checkedWrites = .ok postPage
  preCanonicalExact : prePage.toCanonicalState = pre.logical

namespace AcceptedDelta

variable
    {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M}
    {declaration : DeclaredActionLowering.Declaration target}
    {accepted : Accepted portal authState context pre declaration}

/-- The final page's validity follows from the actual checked executor, rather
than a second claim supplied alongside its successful result. -/
theorem postValid (delta : AcceptedDelta accepted) : delta.postPage.Valid :=
  Page.applyWrites_valid delta.preValid delta.executorExact

/-- Exact canonical post-state correspondence follows for every executed
declaration, using the common ordered fold rather than a sample-specific
post-state comparison. -/
theorem postCanonicalExact (delta : AcceptedDelta accepted) :
    delta.postPage.toCanonicalState = accepted.cellEffect.prepared.post.logical := by
  have fields := runCheckedWrites_post declaration.checkedWrites
    delta.prePage.toCanonicalState.fields delta.postPage.toCanonicalState.fields
    (Page.applyWrites_checked delta.executorExact)
  rw [delta.preCanonicalExact] at fields
  change delta.postPage.toCanonicalState =
    { fields := applyFieldWrites declaration.fieldWrites pre.logical.fields
      resources := applyResourceWrites [] pre.logical.resources }
  unfold Page.toCanonicalState
  congr
  funext resource
  exact Empty.elim resource

def preCell (delta : AcceptedDelta accepted) : Materialized materializer :=
  CellState.materialize materializer (stateOfOption (some delta.prePage))

def patch (delta : AcceptedDelta accepted) : Patch schema Digest where
  expectedPreRoot := delta.preCell.root
  fieldFootprint := {()}
  resourceFootprint := ∅
  fieldWrites := [{ field := (), value := some delta.postPage }]
  resourceWrites := []

theorem patch_accepted (delta : AcceptedDelta accepted) :
    ∃ validated : ValidatedPatch materializer delta.preCell delta.patch,
      validate materializer delta.preCell delta.patch =
        ValidationOutcome.accepted validated := by
  unfold validate
  rw [dif_pos (show delta.patch.expectedPreRoot = delta.preCell.root from rfl)]
  rw [dif_pos (show delta.patch.fieldFootprint = delta.patch.namedFields from rfl)]
  rw [dif_pos (show delta.patch.resourceFootprint = delta.patch.namedResources by
    simp [patch, Patch.namedResources])]
  exact ⟨_, rfl⟩

noncomputable def validated (delta : AcceptedDelta accepted) :
    ValidatedPatch materializer delta.preCell delta.patch :=
  (delta.patch_accepted).choose

noncomputable def postCell (delta : AcceptedDelta accepted) :
    Materialized materializer :=
  delta.validated.apply

@[simp] theorem postCell_page (delta : AcceptedDelta accepted) :
    pageAt delta.postCell.logical = some delta.postPage := by
  change
    (applyFieldWrites delta.patch.fieldWrites delta.preCell.logical.fields) () =
      some delta.postPage
  simp [patch, preCell, stateOfOption, applyFieldWrites, FieldStore.assign]
  rfl

@[simp] theorem postCell_bytes (delta : AcceptedDelta accepted) :
    delta.postCell.bytes = wireFrame ++ 1 :: pageStream.encode delta.postPage := by
  unfold Materialized.bytes
  rw [state_ext delta.postCell.logical, delta.postCell_page]
  rfl

@[simp] theorem postCell_root (delta : AcceptedDelta accepted) :
    delta.postCell.root =
      (Sp800185Cshake256.hash rootCustomization
        (wireFrame ++ 1 :: pageStream.encode delta.postPage)).digest := by
  rw [Materialized.root, delta.postCell_bytes]
  rfl

theorem canonical_post_exact (delta : AcceptedDelta accepted) :
    delta.postPage.toCanonicalState =
      accepted.cellEffect.prepared.post.logical :=
  delta.postCanonicalExact

/-- The bounded page consumer preserves the actual coordinate law; a raw
page executor success is not sufficient to inhabit this accepted refinement. -/
theorem balance_delta (delta : AcceptedDelta accepted)
    (account : ResourceId .account) (resource : Digest) :
    balance delta.postPage.toCanonicalState.fields account resource -
      balance delta.prePage.toCanonicalState.fields account resource =
        postingDelta declaration.postings account resource := by
  rw [delta.postCanonicalExact, delta.preCanonicalExact]
  exact accepted.balance_delta account resource

end AcceptedDelta

/-! ## Closed non-vacuous transfer and rejection teeth -/

namespace Witness

open Minidregg.Kernel.DeclaredHyperedgeWitness
open Minidregg.Theory.DeployedMaterializerWitness
open Minidregg.Theory.TypedAuthorizationWitness

def context : RequestContext where
  domain := ⟨1⟩
  semantics := ⟨2⟩
  federation := ⟨3⟩
  subject := ⟨4⟩
  subjectKeyEpoch := 0
  height := 9
  policyId := ⟨10⟩
  policyEpoch := 0

noncomputable def preLogical : LogicalState DeclaredTurn.effectSchema where
  fields := (effectCell.logical.fields.write debitKey (14 : Int)).write creditKey (0 : Int)
  resources := effectCell.logical.resources

noncomputable def preCell : Materialized effectMaterializer :=
  materialize effectMaterializer preLogical

noncomputable def declaration : DeclaredActionLowering.Declaration source where
  schemaVersion := 1
  expectedPreRoot := preCell.root
  nonce := 400
  actions := [.move source destination asset (some 14) (some 0) amount]

theorem declaration_valid : ValidAt preCell declaration where
  rootExact := rfl
  guardsAndPost := by
    simp [DeclaredActionLowering.Declaration.run,
      DeclaredActionLowering.Declaration.admissionCheck, Action.admissionCheck,
      amount,
      DeclaredActionLowering.Declaration.checkedWrites, declaration,
      Action.checkedWrites, runCheckedWrites,
      DeclaredActionLowering.Declaration.fieldWrites,
      CheckedWrite.toFieldWrite, preCell, preLogical,
      applyFieldWrites, FieldStore.assign, source, destination]
    constructor
    · change (show Option Int from preLogical.fields debitKey) = some 14
      unfold preLogical
      rw [FieldStore.write_other _ (by decide)]
      exact FieldStore.write_self _ _ _
    · rw [Function.update_of_ne (by decide)]
      change (show Option Int from preLogical.fields creditKey) = some 0
      unfold preLogical
      exact FieldStore.write_self _ _ _

def authorization : Authorized permissivePortal authState
    (context.request declaration) where
  evidence := .proof () rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

noncomputable def accepted :
    Accepted permissivePortal authState context preCell declaration :=
  accept authorization declaration_valid

def effectDomain : Digest := ⟨7001⟩
def localShard : Nat := addressShard debitKey

def debitEntry : Entry := ⟨debitKey, 14⟩
def creditEntry : Entry := ⟨creditKey, 0⟩
def debitPostEntry : Entry := ⟨debitKey, 14 - amount⟩
def creditPostEntry : Entry := ⟨creditKey, amount⟩

def prePage : Page where
  effectDomain := effectDomain
  shardNumber := localShard
  slot0 := some debitEntry
  slot1 := some creditEntry
  slot2 := none
  slot3 := none

def postPage : Page where
  effectDomain := effectDomain
  shardNumber := localShard
  slot0 := some debitPostEntry
  slot1 := some creditPostEntry
  slot2 := none
  slot3 := none

theorem source_destination_same_shard :
    addressShard debitKey = addressShard creditKey := by
  decide

theorem prePage_valid : prePage.Valid := by
  decide

theorem postPage_valid : postPage.Valid := by
  decide

def debitWrite : CheckedWrite :=
  { key := debitKey, expected := some 14, replacement := some (14 - amount) }

def creditWrite : CheckedWrite :=
  { key := creditKey, expected := some 0, replacement := some amount }

def middlePage : Page where
  effectDomain := effectDomain
  shardNumber := localShard
  slot0 := some debitPostEntry
  slot1 := some creditEntry
  slot2 := none
  slot3 := none

theorem middlePage_valid : middlePage.Valid := by
  decide

@[simp] theorem declaration_checkedWrites :
    declaration.checkedWrites = [debitWrite, creditWrite] :=
  rfl

theorem debit_step :
    prePage.applyWrite debitWrite = .ok middlePage := by
  unfold Page.applyWrite
  rw [dif_pos prePage_valid]
  rw [dif_pos (show prePage.Owns debitWrite.key by
    simpa [debitWrite] using (show prePage.Owns debitKey by decide))]
  rw [dif_pos (show prePage.lookup debitWrite.key = debitWrite.expected by
    simpa [debitWrite] using
      (show prePage.lookup debitKey = some 14 by decide))]
  simp only [debitWrite]
  change checkedPost middlePage = .ok middlePage
  unfold checkedPost
  rw [if_pos middlePage_valid]

theorem credit_step :
    middlePage.applyWrite creditWrite = .ok postPage := by
  unfold Page.applyWrite
  rw [dif_pos middlePage_valid]
  rw [dif_pos (show middlePage.Owns creditWrite.key by
    simpa [creditWrite] using (show middlePage.Owns creditKey by decide))]
  rw [dif_pos (show middlePage.lookup creditWrite.key = creditWrite.expected by
    simpa [creditWrite] using
      (show middlePage.lookup creditKey = some 0 by decide))]
  simp only [creditWrite]
  change checkedPost postPage = .ok postPage
  unfold checkedPost
  rw [if_pos postPage_valid]

theorem executor_exact :
    prePage.applyWrites declaration.checkedWrites = .ok postPage := by
  rw [declaration_checkedWrites]
  change (do
    let post <- prePage.applyWrite debitWrite
    post.applyWrites [creditWrite]) = .ok postPage
  rw [debit_step]
  change (do
    let post <- middlePage.applyWrite creditWrite
    post.applyWrites []) = .ok postPage
  rw [credit_step]
  rfl

theorem preCanonicalExact : prePage.toCanonicalState = preCell.logical := by
  simp [prePage, Page.toCanonicalState, Page.entries, Entry.install,
    debitEntry, creditEntry, preCell,
    preLogical,
    Minidregg.Theory.DeployedMaterializerWitness.effectCell,
    Minidregg.Theory.DeployedMaterializerWitness.emptyLogical,
    materialize, debitKey, creditKey]
  funext resource
  exact Empty.elim resource

def acceptedDelta : AcceptedDelta accepted where
  prePage := prePage
  postPage := postPage
  preValid := prePage_valid
  executorExact := executor_exact
  preCanonicalExact := preCanonicalExact

theorem postCanonicalExact :
    postPage.toCanonicalState = accepted.cellEffect.prepared.post.logical :=
  acceptedDelta.postCanonicalExact

/-- The second guard sees the first write's actual result, even when both
writes address the same key. -/
theorem repeated_key_sequential :
    prePage.applyWrites
      [debitWrite,
        { key := debitKey, expected := some (14 - amount), replacement := some 14 }] =
      .ok prePage := by
  decide

theorem repeated_key_reflected :
    runCheckedWrites
      [debitWrite,
        { key := debitKey, expected := some (14 - amount), replacement := some 14 }]
      prePage.toCanonicalState.fields = some prePage.toCanonicalState.fields :=
  Page.applyWrites_checked repeated_key_sequential

theorem repeated_key_stale_guard_rejected :
    prePage.applyWrites [debitWrite, debitWrite] = .error .guardMismatch := by
  decide

/-- Deleting and recreating a key uses sparse absence as the second guard;
neither step silently replaces absence with a stored zero. -/
theorem delete_then_recreate :
    prePage.applyWrites
      [{ key := debitKey, expected := some 14, replacement := none },
       { key := debitKey, expected := none, replacement := some 14 }] =
      .ok prePage := by
  decide

theorem absent_is_not_stored_zero :
    prePage.applyWrite
      { key := .accountBalance ⟨102⟩ asset
        expected := some 0, replacement := some 1 } = .error .guardMismatch := by
  decide

theorem stored_zero_is_not_absent :
    prePage.applyWrite
      { key := creditKey, expected := none, replacement := some 1 } =
      .error .guardMismatch := by
  decide

def overflowKey : StateKey := .accountBalance ⟨102⟩ asset
def overflowWrite : CheckedWrite :=
  { key := overflowKey, expected := none, replacement := some 1 }

def fullPage : Page where
  effectDomain := effectDomain
  shardNumber := localShard
  slot0 := some debitEntry
  slot1 := some creditEntry
  slot2 := some ⟨.accountBalance ⟨102⟩ asset, 0⟩
  slot3 := some ⟨.accountBalance ⟨103⟩ asset, 0⟩

theorem fullPage_valid : fullPage.Valid := by
  decide

@[simp] theorem overflow_rejected :
    fullPage.applyWrite
      { key := .accountBalance ⟨104⟩ asset
        expected := none
        replacement := some 1 } = .error .overflow := by
  unfold Page.applyWrite
  rw [dif_pos fullPage_valid]
  rw [dif_pos (show fullPage.Owns (.accountBalance ⟨104⟩ asset) by decide)]
  rw [dif_pos (show fullPage.lookup (.accountBalance ⟨104⟩ asset) = none by
    decide)]
  rfl

@[simp] theorem unsupported_address_rejected :
    prePage.applyWrite
      { key := .accountBalance ⟨104⟩ ⟨201⟩
        expected := none
        replacement := some 1 } = .error .unsupportedAddress := by
  unfold Page.applyWrite
  rw [dif_pos prePage_valid]
  rw [dif_neg (show ¬ prePage.Owns (.accountBalance ⟨104⟩ ⟨201⟩) by
    decide)]

@[simp] theorem guard_mismatch_rejected :
    prePage.applyWrite
      { key := debitKey
        expected := some 99
        replacement := some 1 } = .error .guardMismatch := by
  unfold Page.applyWrite
  rw [dif_pos prePage_valid]
  rw [dif_pos (show prePage.Owns debitKey by decide)]
  rw [dif_neg (show prePage.lookup debitKey ≠ some 99 by decide)]

theorem accepted_page_delta_nonempty : Nonempty (AcceptedDelta accepted) :=
  ⟨acceptedDelta⟩

end Witness

/-! ## Honest pair-scoped binding boundary -/

structure Collision (left right : LogicalState schema) : Prop where
  statesDifferent : left ≠ right
  bytesDifferent : stateCodec.encode left ≠ stateCodec.encode right
  rootsEqual : rootBytes (stateCodec.encode left) =
    rootBytes (stateCodec.encode right)

structure PairBindingPremise (left right : LogicalState schema) : Prop where
  noCollision : ¬ Collision left right

/-! ## Axiom audit -/

/-! The sparse finite-map equalities use the standard quotient extensionality
stack; there are no project-specific postulates or `sorry` declarations. -/
/-- info: 'Minidregg.Compiler.DeclaredEffectPageMaterializer.Page.replaceExisting_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Page.replaceExisting_fields
/-- info: 'Minidregg.Compiler.DeclaredEffectPageMaterializer.Page.insert_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Page.insert_fields
/-- info: 'Minidregg.Compiler.DeclaredEffectPageMaterializer.Page.applyWrite_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Page.applyWrite_spec
/-- info: 'Minidregg.Compiler.DeclaredEffectPageMaterializer.Page.applyWrites_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Page.applyWrites_checked
/-- info: 'Minidregg.Compiler.DeclaredEffectPageMaterializer.Page.applyWrites_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Page.applyWrites_valid
/-- info: 'Minidregg.Compiler.DeclaredEffectPageMaterializer.AcceptedDelta.postValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AcceptedDelta.postValid
/-- info: 'Minidregg.Compiler.DeclaredEffectPageMaterializer.AcceptedDelta.postCanonicalExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AcceptedDelta.postCanonicalExact
/-- info: 'Minidregg.Compiler.DeclaredEffectPageMaterializer.Witness.repeated_key_sequential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Witness.repeated_key_sequential
/-- info: 'Minidregg.Compiler.DeclaredEffectPageMaterializer.Witness.repeated_key_reflected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Witness.repeated_key_reflected
/-- info: 'Minidregg.Compiler.DeclaredEffectPageMaterializer.Witness.repeated_key_stale_guard_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Witness.repeated_key_stale_guard_rejected
/-- info: 'Minidregg.Compiler.DeclaredEffectPageMaterializer.Witness.delete_then_recreate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Witness.delete_then_recreate
/-- info: 'Minidregg.Compiler.DeclaredEffectPageMaterializer.Witness.absent_is_not_stored_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Witness.absent_is_not_stored_zero
/-- info: 'Minidregg.Compiler.DeclaredEffectPageMaterializer.Witness.stored_zero_is_not_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Witness.stored_zero_is_not_absent
/-- info: 'Minidregg.Compiler.DeclaredEffectPageMaterializer.AcceptedDelta.balance_delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AcceptedDelta.balance_delta
/-- info: 'Minidregg.Compiler.DeclaredEffectPageMaterializer.Witness.overflow_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Witness.overflow_rejected
/-- info: 'Minidregg.Compiler.DeclaredEffectPageMaterializer.Witness.unsupported_address_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Witness.unsupported_address_rejected
/-- info: 'Minidregg.Compiler.DeclaredEffectPageMaterializer.Witness.executor_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Witness.executor_exact

end Minidregg.Compiler.DeclaredEffectPageMaterializer
