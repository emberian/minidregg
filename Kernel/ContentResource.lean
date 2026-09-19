/-
# Source-owned mutations of canonical typed content pages

The transaction receiver supplies authenticated author and operation identity.
The command contains edits, never proposed pages or authority decisions. Exact
old atom records guard replacement; payloads remain bytes in the canonical
Hyperdocument schema. The bounded page is the existing content materializer,
not a host-side blob store. Authorization and current installed Pred evaluation
belong to the enclosing ResourceTransaction receiver.
-/
import Compiler.HyperdocumentContentPageMaterializer
import Compiler.ResourceBirthCodec

namespace Minidregg.Kernel.ContentResource

open Minidregg.Compiler
open Minidregg.Compiler.HyperdocumentCodec
open Minidregg.Compiler.HyperdocumentContentPageMaterializer
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.HyperdocumentOperations
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

inductive Action where
  | createDocument (rootElement : ElementId) (schema : Digest) (body : ElementBody)
  | createAtom (atom : AtomId) (kind : AtomKind) (payload : List UInt8)
  | editAtom (edit : EditAtomPayload)
  | link (link : LinkId) (source : Option StableRange) (target : ForwardTarget)
      (relation : Digest)
  | createRun (runId : RunId) (atoms : List AtomId)
  deriving DecidableEq, Repr

abbrev ActionWire := Sum (ElementId × Digest × ElementBody)
  (Sum (AtomId × AtomKind × List UInt8)
    (Sum EditAtomPayload
      (Sum (LinkId × Option StableRange × ForwardTarget × Digest) (RunId × List AtomId))))

def actionWireStream : StreamCodec ActionWire :=
  StreamCodec.sum
    (StreamCodec.product (identifierStream .v1 .element)
      (StreamCodec.product digestStream elementBodyStream))
    (StreamCodec.sum
      (StreamCodec.product (identifierStream .v1 .atom)
        (StreamCodec.product atomKindStream bytesStream))
      (StreamCodec.sum editAtomPayloadStream
        (StreamCodec.sum
          (StreamCodec.product (identifierStream .v1 .link)
            (StreamCodec.product (StreamCodec.option storedStableRangeStream)
              (StreamCodec.product forwardTargetStream digestStream)))
          (StreamCodec.product (identifierStream .v1 .run)
            (StreamCodec.list (identifierStream .v1 .atom))))))

def Action.toWire : Action → ActionWire
  | .createDocument root schema body => .inl (root, schema, body)
  | .createAtom atom kind payload => .inr (.inl (atom, kind, payload))
  | .editAtom edit => .inr (.inr (.inl edit))
  | .link linkId source target relation =>
      .inr (.inr (.inr (.inl (linkId, source, target, relation))))
  | .createRun runId atoms => .inr (.inr (.inr (.inr (runId, atoms))))

def Action.ofWire : ActionWire → Action
  | .inl (root, schema, body) => .createDocument root schema body
  | .inr (.inl (atom, kind, payload)) => .createAtom atom kind payload
  | .inr (.inr (.inl edit)) => .editAtom edit
  | .inr (.inr (.inr (.inl (linkId, source, target, relation)))) =>
      .link linkId source target relation
  | .inr (.inr (.inr (.inr (runId, atoms)))) => .createRun runId atoms

@[simp] theorem Action.ofWire_toWire (action : Action) :
    Action.ofWire action.toWire = action := by cases action <;> rfl

def actionStream : StreamCodec Action :=
  StreamCodec.xmap actionWireStream Action.toWire Action.ofWire Action.ofWire_toWire

structure Command where
  actions : List Action
  deriving DecidableEq, Repr

def commandStream : StreamCodec Command :=
  StreamCodec.xmap (StreamCodec.list actionStream) Command.actions
    (fun actions => ⟨actions⟩) (by intro command; rfl)

/-- Action grammar version; independent of the content page storage epoch. -/
def commandVersion : Nat := 1

def commandFrame : List UInt8 := "DREGG/CONTENT/MUTATE".toUTF8.toList ++
  [UInt8.ofNatLT commandVersion (by decide)]

def rawCommandCodec : LawfulCodec Command where
  encode command := commandFrame ++ commandStream.encode command
  decode bytes :=
    if bytes.take commandFrame.length = commandFrame then
      commandStream.toLawful.decode (bytes.drop commandFrame.length)
    else none
  decode_encode := by
    intro command
    have decoded := commandStream.toLawful.decode_encode command
    change commandStream.toLawful.decode (commandStream.encode command) = some command at decoded
    simp [decoded]

def commandCodec : LawfulCodec Command := ResourceBirthCodec.strictCodec rawCommandCodec

@[simp] theorem command_roundtrip (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command :=
  commandCodec.decode_encode command

theorem command_canonical {bytes : List UInt8} {command : Command}
    (accepted : commandCodec.decode bytes = some command) :
    commandCodec.encode command = bytes :=
  ResourceBirthCodec.strictCodec_canonical rawCommandCodec accepted

inductive Reject where
  | missingPage
  | invalidPage
  | emptyActions
  | duplicateAddress
  | full
  | staleAtom
  | wrongDocument
  | invalidPost
  | invalidPatch
  | invalidRun
  | invalidSourceRange
  deriving DecidableEq, Repr

def insert (page : Page) (entry : Entry) : Except Reject Page :=
  match page.admitInsert entry with
  | .ok post => .ok post.val
  | .error .invalidPage => .error .invalidPage
  | .error .duplicateAddress => .error .duplicateAddress
  | .error .full => .error .full

def replaceSlot (old replacement : Entry) (slot : Option Entry) : Option Entry :=
  if slot = some old then some replacement else slot

theorem unrelated_slot_unchanged (old replacement entry : Entry) (other : entry ≠ old) :
    replaceSlot old replacement (some entry) = some entry := by
  simp [replaceSlot, other]

/-- The slot is selected by exact canonical address and old record, not by a
caller-supplied physical index. All other entries remain byte-for-byte intact. -/
def replaceAtom (page : Page) (atom : AtomId) (before after : AtomRecord) :
    Except Reject Page :=
  let old := Entry.atom atom before
  let replacement := Entry.atom atom after
  if before.document ≠ page.document ∨ after.document ≠ page.document then
    .error .wrongDocument
  else if ¬page.Contains old then .error .staleAtom
  else
    let replace := replaceSlot old replacement
    .ok { page with
      slot0 := replace page.slot0
      slot1 := replace page.slot1
      slot2 := replace page.slot2
      slot3 := replace page.slot3
      overflow := page.overflow.map fun entry => if entry = old then replacement else entry }

/-- Executable membership checker for the existing canonical stored-point law. -/
def pointCheck (pre : LogicalState Hyperdocument.cellSchema) (document : DocumentId)
    (point : StablePoint) : Bool :=
  match Hyperdocument.lookup pre .runs point.run with
  | none => false
  | some run => decide (run.document = document) &&
      match point.neighbor with
      | none => decide (run.atoms = [])
      | some atomId => decide (atomId ∈ run.atoms) &&
          match Hyperdocument.lookup pre .atoms atomId with
          | none => false
          | some atom => decide (atom.document = document)

theorem pointCheck_iff (pre : LogicalState Hyperdocument.cellSchema)
    (document : DocumentId) (point : StablePoint) :
    pointCheck pre document point = true ↔
      storedPointPresentInDocument pre document point := by
  cases runFound : Hyperdocument.lookup pre .runs point.run with
  | none => simp [pointCheck, storedPointPresentInDocument, runFound]
  | some record =>
    cases neighbor : point.neighbor with
    | none => simp [pointCheck, storedPointPresentInDocument, runFound, neighbor]
    | some atomId =>
      cases atomFound : Hyperdocument.lookup pre .atoms atomId <;>
        simp [pointCheck, storedPointPresentInDocument, runFound, neighbor, atomFound]

def rangeCheck (page : Page) (range : StableRange) : Bool :=
  pointCheck page.toCanonicalState page.document range.start &&
    pointCheck page.toCanonicalState page.document range.finish

theorem rangeCheck_sound (page : Page) (range : StableRange)
    (checked : rangeCheck page range = true) :
    StoredRangeValidAt page.toCanonicalState page.document range := by
  have endpoints : pointCheck page.toCanonicalState page.document range.start = true ∧
      pointCheck page.toCanonicalState page.document range.finish = true := by
    simpa [rangeCheck] using checked
  exact ⟨rfl, (pointCheck_iff _ _ _).mp endpoints.1,
    (pointCheck_iff _ _ _).mp endpoints.2⟩

def runAtomsCheck (page : Page) (atoms : List AtomId) : Bool :=
  decide atoms.Nodup && atoms.all (fun atomId =>
    match Hyperdocument.lookup page.toCanonicalState .atoms atomId with
    | none => false
    | some atom => decide (atom.document = page.document))

def step (author : PrincipalRef) (operation : OperationId) (page : Page) :
    Action → Except Reject Page
  | .createDocument root schema body => do
      let post ← insert page (.document page.document
        ⟨root, schema, author, operation⟩)
      insert post (.element root ⟨page.document, none, body, author, operation, none⟩)
  | .createAtom atom kind payload =>
      insert page (.atom atom ⟨page.document, kind, payload, author, operation, none⟩)
  | .editAtom edit =>
      replaceAtom page edit.atomId edit.before (editAtomRecord operation edit)
  | .link link source target relation =>
      if source.all (rangeCheck page) then
        insert page (.link link ⟨page.document, source, target, relation, author, operation, none⟩)
      else .error .invalidSourceRange
  | .createRun runId atoms =>
      if runAtomsCheck page atoms then
        insert page (.run runId ⟨page.document, atoms, author, operation, none⟩)
      else .error .invalidRun

theorem accepted_link_source_stored (author : PrincipalRef) (operation : OperationId)
    (page post : Page) (linkId : LinkId) (source : StableRange)
    (target : ForwardTarget) (relation : Digest)
    (accepted : step author operation page (.link linkId (some source) target relation) =
      .ok post) : StoredRangeValidAt page.toCanonicalState page.document source := by
  by_cases checked : rangeCheck page source = true
  · exact rangeCheck_sound page source checked
  · simp [step, checked] at accepted

def run (author : PrincipalRef) (operation : OperationId) (page : Page)
    (command : Command) : Except Reject Page :=
  command.actions.foldlM (step author operation) page

/-- Identity and physical page routing never change through content edits. -/
def Frame (before after : Page) : Prop :=
  after.contentDomain = before.contentDomain ∧ after.document = before.document ∧
    after.pageNumber = before.pageNumber

instance frameDecidable (before after : Page) : Decidable (Frame before after) := by
  unfold Frame
  infer_instance

theorem replaceAtom_preserves_frame (page post : Page) (atom : AtomId)
    (before after : AtomRecord)
    (accepted : replaceAtom page atom before after = .ok post) : Frame page post := by
  unfold replaceAtom at accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  · split at accepted
    · contradiction
    · cases accepted
      exact ⟨rfl, rfl, rfl⟩

structure PreparedPage (author : PrincipalRef) (operation : OperationId)
    (before : Page) (command : Command) where
  private mk ::
  post : Page
  beforeValid : before.Valid
  postValid : post.Valid
  framed : Frame before post
  nonempty : command.actions ≠ []
  computed : run author operation before command = .ok post

def preparePage (author : PrincipalRef) (operation : OperationId)
    (before : Page) (command : Command) :
    Except Reject (PreparedPage author operation before command) :=
  if beforeValid : before.Valid then
    if nonempty : command.actions ≠ [] then
      match computed : run author operation before command with
      | .error reason => .error reason
      | .ok post =>
        if valid : post.Valid ∧ Frame before post then
          .ok ⟨post, beforeValid, valid.1, valid.2, nonempty, computed⟩
        else .error .invalidPost
    else .error .emptyActions
  else .error .invalidPage

abbrev ContentCell := Materialized HyperdocumentContentPageMaterializer.materializer

def patch (pre : ContentCell) (post : Page) :
    Patch HyperdocumentContentPageMaterializer.schema Digest where
  expectedPreRoot := pre.root
  fieldFootprint := {()}
  resourceFootprint := ∅
  fieldWrites := [⟨(), some post⟩]
  resourceWrites := []

theorem patch_applies_exactly (pre : ContentCell) (post : Page)
    (validated : ValidatedPatch HyperdocumentContentPageMaterializer.materializer pre
      (patch pre post)) :
    validated.apply.logical = stateOfOption (some post) := by
  have page : pageAt validated.apply.logical = some post := by
    change (applyFieldWrites (patch pre post).fieldWrites pre.logical.fields) () = some post
    simp [patch, applyFieldWrites, FieldStore.assign]
    rfl
  exact (state_ext validated.apply.logical).trans (congrArg stateOfOption page)

structure PreparedCell (author : PrincipalRef) (operation : OperationId)
    (pre : ContentCell) (command : Command) where
  private mk ::
  before : Page
  beforeExact : pageAt pre.logical = some before
  post : Page
  beforeValid : before.Valid
  postValid : post.Valid
  framed : Frame before post
  nonempty : command.actions ≠ []
  computed : run author operation before command = .ok post
  validated : ValidatedPatch HyperdocumentContentPageMaterializer.materializer pre (patch pre post)
  postExact : validated.apply.logical = stateOfOption (some post)

def prepareCell (author : PrincipalRef) (operation : OperationId)
    (pre : ContentCell) (command : Command) :
    Except Reject (PreparedCell author operation pre command) :=
  match present : pageAt pre.logical with
  | none => .error .missingPage
  | some before => do
    let prepared ← preparePage author operation before command
    match validate HyperdocumentContentPageMaterializer.materializer pre (patch pre prepared.post) with
    | .rejected _ => .error .invalidPatch
    | .accepted validated =>
      .ok ⟨before, present, prepared.post, prepared.beforeValid, prepared.postValid,
        prepared.framed, prepared.nonempty, prepared.computed, validated,
        patch_applies_exactly pre prepared.post validated⟩

/-- Birth contains no user-authored history; ordinary authorized commands add
content afterward. This is exactly the canonical registry's content birth shape. -/
def initialPage (domain : Digest) (target : Nat) : Page where
  contentDomain := domain
  document := ⟨⟨target⟩⟩
  pageNumber := 0
  slot0 := none
  slot1 := none
  slot2 := none
  slot3 := none

theorem initialPage_valid (domain : Digest) (target : Nat) :
    (initialPage domain target).Valid := by
  simp [Page.Valid, Page.addresses, Page.entries, initialPage]

/-- Different payload bytes have different canonical encodings. Hash equality
still needs the materializer's explicit pair-scoped collision premise. -/
theorem atom_payload_encoding_distinct (atom : AtomId) (before after : AtomRecord)
    (different : before.payload ≠ after.payload) :
    entryStream.encode (.atom atom before) ≠ entryStream.encode (.atom atom after) := by
  intro same
  have equal : Entry.atom atom before = Entry.atom atom after := by
    apply HyperdocumentContentPageMaterializer.lawfulCodec_encode_injective entryStream.toLawful
    exact same
  have records : before = after := by cases equal; rfl
  exact different (congrArg AtomRecord.payload records)

def payloadBytes : Entry → Nat
  | .atom _ record => record.payload.length
  | .element _ record => match record.body with
      | .opaque _ payload => payload.length
      | _ => 0
  | _ => 0

def contentPayloadBytes (page : Page) : Nat := (page.entries.map payloadBytes).sum

/-- Count the entire committed encoding, including typed references, authors,
identifiers and framing. A large link cannot evade a content-size policy. -/
def contentBytes (page : Page) : Nat :=
  (stateCodec.encode (stateOfOption (some page))).length

def Action.tag : Action → Nat
  | .createDocument .. => 0
  | .createAtom .. => 1
  | .editAtom .. => 2
  | .link .. => 3
  | .createRun .. => 4

def actionCount (command : Command) (tag : Nat) : Nat :=
  (command.actions.filter (fun action => action.tag == tag)).length

/-- Source-derived policy inputs count actual committed bytes; no content or
identity is reduced to a scalar identifier. Full typed pages remain observable. -/
def project (before after : Page) (command : Command) : List (String × Int) :=
  [("content/bytes/before", contentBytes before),
   ("content/bytes/after", contentBytes after),
   ("content/bytes/delta", (contentBytes after : Int) - contentBytes before),
   ("content/entries/before", before.entries.length),
   ("content/entries/after", after.entries.length),
   ("content/operations", command.actions.length),
   ("content/payload-bytes/before", contentPayloadBytes before),
   ("content/payload-bytes/after", contentPayloadBytes after),
   ("content/document-creates", actionCount command 0),
   ("content/atom-creates", actionCount command 1),
   ("content/atom-edits", actionCount command 2),
   ("content/links", actionCount command 3),
   ("content/run-creates", actionCount command 4),
   ("content/tombstones", (command.actions.filter fun action => match action with
      | .editAtom edit => edit.tombstone
      | _ => false).length)]

/-- Exact old-record mismatch refuses a write, even for an authorized caller. -/
theorem replaceAtom_stale (page : Page) (atom : AtomId) (before after : AtomRecord)
    (localBefore : before.document = page.document)
    (localAfter : after.document = page.document)
    (missing : ¬page.Contains (.atom atom before)) :
    replaceAtom page atom before after = .error .staleAtom := by
  simp [replaceAtom, localBefore, localAfter, missing]

theorem empty_command_rejected (author : PrincipalRef) (operation : OperationId)
    (before : Page) (valid : before.Valid) :
    preparePage author operation before ⟨[]⟩ = .error .emptyActions := by
  simp [preparePage, valid]

theorem prepared_preserves_identity {author : PrincipalRef} {operation : OperationId}
    {pre : ContentCell} {command : Command}
    (prepared : PreparedCell author operation pre command) :
    prepared.post.contentDomain = prepared.before.contentDomain ∧
    prepared.post.document = prepared.before.document ∧
    prepared.post.pageNumber = prepared.before.pageNumber := prepared.framed

/-- info: 'Minidregg.Kernel.ContentResource.command_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms command_roundtrip
/-- info: 'Minidregg.Kernel.ContentResource.patch_applies_exactly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms patch_applies_exactly
/-- info: 'Minidregg.Kernel.ContentResource.atom_payload_encoding_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms atom_payload_encoding_distinct
/-- info: 'Minidregg.Kernel.ContentResource.prepared_preserves_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prepared_preserves_identity

end Minidregg.Kernel.ContentResource
