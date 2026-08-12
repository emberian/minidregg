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
  postValid : postPage.Valid
  executorExact :
    prePage.applyWrites declaration.checkedWrites = .ok postPage
  preCanonicalExact : prePage.toCanonicalState = pre.logical
  postCanonicalExact :
    postPage.toCanonicalState = accepted.cellEffect.prepared.post.logical

namespace AcceptedDelta

variable
    {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M}
    {declaration : DeclaredActionLowering.Declaration target}
    {accepted : Accepted portal authState context pre declaration}

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

noncomputable def declaration : DeclaredActionLowering.Declaration source where
  schemaVersion := 1
  expectedPreRoot := preCell.root
  nonce := 400
  actions := [.move source destination asset (some 0) (some 0) amount]

theorem declaration_valid : ValidAt preCell declaration where
  rootExact := rfl
  guardsAndPost := by
    simp [DeclaredActionLowering.Declaration.run,
      DeclaredActionLowering.Declaration.checkedWrites, declaration,
      Action.checkedWrites, runCheckedWrites,
      DeclaredActionLowering.Declaration.fieldWrites,
      CheckedWrite.toFieldWrite, preCell, preLogical,
      applyFieldWrites, FieldStore.assign, source, destination]
    constructor
    · change (show Option Int from preLogical.fields debitKey) = some 0
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

def debitEntry : Entry := ⟨debitKey, 0⟩
def creditEntry : Entry := ⟨creditKey, 0⟩
def debitPostEntry : Entry := ⟨debitKey, -amount⟩
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
  { key := debitKey, expected := some 0, replacement := some (-amount) }

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
      (show prePage.lookup debitKey = some 0 by decide))]
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
    Minidregg.Kernel.DeclaredHyperedgeWitness.preCell,
    Minidregg.Kernel.DeclaredHyperedgeWitness.preLogical,
    Minidregg.Theory.DeployedMaterializerWitness.effectCell,
    Minidregg.Theory.DeployedMaterializerWitness.emptyLogical,
    materialize, debitKey, creditKey]
  congr
  funext resource
  exact Empty.elim resource

theorem postCanonicalExact :
    postPage.toCanonicalState = accepted.cellEffect.prepared.post.logical := by
  change postPage.toCanonicalState = accepted.cellEffect.validated.apply.logical
  change postPage.toCanonicalState =
    { fields := applyFieldWrites declaration.fieldWrites preCell.logical.fields
      resources := applyResourceWrites [] preCell.logical.resources }
  unfold Page.toCanonicalState
  congr
  · apply DFinsupp.ext
    intro field
    change
      (((0 : FieldStore DeclaredTurn.effectSchema.{0, 0}).write
          debitKey (-amount)).write creditKey amount) field =
        ((preCell.logical.fields.assign debitKey (some (-amount))).assign
          creditKey (some amount)) field
    by_cases credit : field = creditKey
    · subst field
      simp [FieldStore.write, FieldStore.assign]
    by_cases debit : field = debitKey
    · subst field
      change some (-amount) = some (-amount)
      rfl
    ·
      have preAbsent : preCell.logical.fields field = none := by
        change
          (((Minidregg.Theory.DeployedMaterializerWitness.effectCell.logical.fields
              .write debitKey 0).write creditKey 0) field) = none
        rw [FieldStore.write_other _ (Ne.symm credit)]
        rw [FieldStore.write_other _ (Ne.symm debit)]
        rfl
      have leftAbsent :
          (((0 : FieldStore DeclaredTurn.effectSchema.{0, 0}).write
              debitKey (-amount)).write creditKey amount) field = none := by
        rw [FieldStore.write_other _ (Ne.symm credit)]
        rw [FieldStore.write_other _ (Ne.symm debit)]
        rfl
      have rightCredit :
          ((preCell.logical.fields.assign debitKey (some (-amount))).assign
              creditKey (some amount)) field =
            (preCell.logical.fields.assign debitKey (some (-amount))) field := by
        simpa [FieldStore.read] using
          (FieldStore.read_assign_other
            (preCell.logical.fields.assign debitKey (some (-amount)))
            (field := field) (other := creditKey) (Ne.symm credit)
            (some amount))
      have rightDebit :
          (preCell.logical.fields.assign debitKey (some (-amount))) field =
            preCell.logical.fields field := by
        simpa [FieldStore.read] using
          (FieldStore.read_assign_other preCell.logical.fields
            (field := field) (other := debitKey) (Ne.symm debit)
            (some (-amount)))
      rw [leftAbsent, rightCredit, rightDebit, preAbsent]
  · funext resource
    exact Empty.elim resource

def acceptedDelta : AcceptedDelta accepted where
  prePage := prePage
  postPage := postPage
  preValid := prePage_valid
  postValid := postPage_valid
  executorExact := executor_exact
  preCanonicalExact := preCanonicalExact
  postCanonicalExact := postCanonicalExact

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
