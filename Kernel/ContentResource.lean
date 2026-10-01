/-
# Source-owned mutations of the canonical hyperdocument content cell

A content cell is one `Store` over `Hyperdocument.layout` at the declared
`HyperdocumentCell.contentWire` (DATAMODEL B1); the cell's identifier is the
document's identity (`documentOf`).  The transaction receiver supplies
authenticated author and operation identity.  The command contains edits,
never proposed stores or authority decisions: each action lowers to guarded
`Store.Op`s at the store its prefix produced, so exact old atom records guard
replacement and every creation is an allocation at a fresh address.  The
patch is then validated by the kernel validator at the cell's own root.

There is no capacity: a document holds any number of records (the retired
four-slot page refused the seventeenth).  Cross-page routing is gone with the
page; a link's target is the canonical `LinkTarget`.  One-document-per-cell is
the registry's `ContentLaw`, which every final cell runs.  Authorization and
current installed Pred evaluation belong to the enclosing ResourceTransaction
receiver.

Command grammar v4 (`DREGG/CONTENT/MUTATE` ++ [4]) adds `unlink`; v3 added
`annotate` and `quote`.  Version-1 commands (links carried the retired
`ForwardTarget`), version-2 commands (no annotate/quote; atoms without a
revision) and version-3 commands (no unlink; the wire's tail sum was one arm
shorter, so a v3 quote would decode as something else) refuse to decode
(`retired_command_refused`).

`unlink` retires one live link of the document: the record stays, with
`tombstonedAt` set to the retiring operation, and the backlink index
(`Kernel.LinkIndex`) drops it.

`annotate` attaches an annotation record to one atom at the revision the
annotator read and writes nothing else; `quote` writes an embed element naming
a source atom at a revision, plus a link for backlinks, and copies no source
bytes.  A reader sees quoted bytes only through its own read of the source
(`renderQuote`).
-/
import Compiler.HyperdocumentCell
import Compiler.ResourceBirthCodec

namespace Minidregg.Kernel.ContentResource

open Minidregg.Compiler
open Minidregg.Compiler.HyperdocumentCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store (Op Patch)
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.HyperdocumentOperations
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev ContentStore := Store.Store Hyperdocument.layout
abbrev ContentCell := Materialized HyperdocumentCell.contentMaterializer

/-- A content cell's document is named by the cell's identifier. -/
def documentOf (target : Nat) : DocumentId := ⟨⟨target⟩⟩

/-- Neutral content genesis: the empty document cell. -/
def initialStore : ContentStore := 0

inductive Action where
  | createDocument (rootElement : ElementId) (schema : Digest) (body : ElementBody)
  | createAtom (atom : AtomId) (kind : AtomKind) (payload : List UInt8)
  | editAtom (edit : EditAtomPayload)
  | link (link : LinkId) (source : Option StableRange) (target : LinkTarget)
      (relation : Digest)
  | createRun (runId : RunId) (atoms : List AtomId)
  /-- Annotate `atom` as last read at `revision`; refused `staleAtom` if it moved. -/
  | annotate (annotation : AnnotationId) (atom : AtomId) (revision : OperationId)
      (body : List UInt8)
  /-- Quote (`snapshot`) or transclude (`live`) a source atom: an embed element
  and a link to the source document. -/
  | quote (element : ElementId) (link : LinkId) (reference : EmbedRef)
  /-- Retire a live link of this document (`tombstonedAt := operation`). -/
  | unlink (link : LinkId)
  deriving DecidableEq

abbrev ActionWire := Sum (ElementId × Digest × ElementBody)
  (Sum (AtomId × AtomKind × List UInt8)
    (Sum EditAtomPayload
      (Sum (LinkId × Option StableRange × LinkTarget × Digest)
        (Sum (RunId × List AtomId)
          (Sum (AnnotationId × AtomId × OperationId × List UInt8)
            (Sum (ElementId × LinkId × EmbedRef) LinkId))))))

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
              (StreamCodec.product linkTargetStream digestStream)))
          (StreamCodec.sum
            (StreamCodec.product (identifierStream .v1 .run)
              (StreamCodec.list (identifierStream .v1 .atom)))
            (StreamCodec.sum
              (StreamCodec.product (identifierStream .v1 .annotation)
                (StreamCodec.product (identifierStream .v1 .atom)
                  (StreamCodec.product (identifierStream .v1 .operationIntent) bytesStream)))
              (StreamCodec.sum
                (StreamCodec.product (identifierStream .v1 .element)
                  (StreamCodec.product (identifierStream .v1 .link) embedRefStream))
                (identifierStream .v1 .link)))))))

def Action.toWire : Action → ActionWire
  | .createDocument root schema body => .inl (root, schema, body)
  | .createAtom atom kind payload => .inr (.inl (atom, kind, payload))
  | .editAtom edit => .inr (.inr (.inl edit))
  | .link linkId source target relation =>
      .inr (.inr (.inr (.inl (linkId, source, target, relation))))
  | .createRun runId atoms => .inr (.inr (.inr (.inr (.inl (runId, atoms)))))
  | .annotate annotationId atom revision body =>
      .inr (.inr (.inr (.inr (.inr (.inl (annotationId, atom, revision, body))))))
  | .quote element linkId reference =>
      .inr (.inr (.inr (.inr (.inr (.inr (.inl (element, linkId, reference)))))))
  | .unlink linkId => .inr (.inr (.inr (.inr (.inr (.inr (.inr linkId))))))

def Action.ofWire : ActionWire → Action
  | .inl (root, schema, body) => .createDocument root schema body
  | .inr (.inl (atom, kind, payload)) => .createAtom atom kind payload
  | .inr (.inr (.inl edit)) => .editAtom edit
  | .inr (.inr (.inr (.inl (linkId, source, target, relation)))) =>
      .link linkId source target relation
  | .inr (.inr (.inr (.inr (.inl (runId, atoms))))) => .createRun runId atoms
  | .inr (.inr (.inr (.inr (.inr (.inl (annotationId, atom, revision, body)))))) =>
      .annotate annotationId atom revision body
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (element, linkId, reference))))))) =>
      .quote element linkId reference
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr linkId)))))) => .unlink linkId

@[simp] theorem Action.ofWire_toWire (action : Action) :
    Action.ofWire action.toWire = action := by cases action <;> rfl

def actionStream : StreamCodec Action :=
  StreamCodec.xmap actionWireStream Action.toWire Action.ofWire Action.ofWire_toWire

structure Command where
  actions : List Action
  deriving DecidableEq

def commandStream : StreamCodec Command :=
  StreamCodec.xmap (StreamCodec.list actionStream) Command.actions
    (fun actions => ⟨actions⟩) (by intro command; rfl)

/-- Action grammar version; independent of the content cell's storage wire. -/
def commandVersion : Nat := 4

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

/-- Version-1, version-2 and version-3 command frames refuse to decode. -/
theorem retired_command_refused (version : UInt8) (retired : version = 1 ∨ version = 2 ∨ version = 3)
    (payload : List UInt8) :
    rawCommandCodec.decode ("DREGG/CONTENT/MUTATE".toUTF8.toList ++ version :: payload) = none := by
  let oldFrame : List UInt8 := "DREGG/CONTENT/MUTATE".toUTF8.toList ++ [version]
  have lengthExact : commandFrame.length = oldFrame.length := by
    simp [commandFrame, oldFrame]
  have different : oldFrame ≠ commandFrame := by
    rcases retired with rfl | rfl | rfl <;> decide +kernel
  have refused : rawCommandCodec.decode (oldFrame ++ payload) = none := by
    simp [rawCommandCodec, lengthExact, different]
  simpa only [oldFrame, List.append_assoc, List.singleton_append] using refused

inductive Reject where
  | emptyActions
  | duplicateAddress
  | staleAtom
  | wrongDocument
  | invalidPatch
  | invalidRun
  | invalidSourceRange
  /-- `unlink` named no live link of this document. -/
  | unknownLink
  deriving DecidableEq, Repr

/-! ## Lowering actions to guarded operations -/

/-- The running store and the guarded operations emitted so far. -/
abbrev Progress := ContentStore × Patch Hyperdocument.layout

/-- Allocate one fresh record; a present address is a duplicate. -/
def allocate (progress : Progress) (space : Namespace) (key : Key space)
    (value : Value space) : Except Reject Progress :=
  if progress.1 ⟨space, key⟩ = none then
    .ok (progress.1.set ⟨space, key⟩ (some value),
      progress.2 ++ [.allocate space key value])
  else .error .duplicateAddress

/-- The slot is selected by exact canonical address and old record, never by
a caller-supplied index.  Every other record is framed. -/
def replaceAtom (document : DocumentId) (progress : Progress) (atom : AtomId)
    (before after : AtomRecord) : Except Reject Progress :=
  if before.document ≠ document ∨ after.document ≠ document then
    .error .wrongDocument
  else if (show Option AtomRecord from progress.1 ⟨.atoms, atom⟩) ≠ some before then
    .error .staleAtom
  else
    .ok (progress.1.set ⟨.atoms, atom⟩ (some after),
      progress.2 ++ [.write .atoms atom before after])

/-- Retire a live link of `document`: the exact stored record guards the write,
and only `tombstonedAt` changes. -/
def retireLink (document : DocumentId) (operation : OperationId) (progress : Progress)
    (link : LinkId) : Except Reject Progress :=
  match (show Option LinkRecord from progress.1 ⟨.links, link⟩) with
  | none => .error .unknownLink
  | some before =>
      if before.sourceDocument = document ∧ before.tombstonedAt = none then
        .ok (progress.1.set ⟨.links, link⟩ (some { before with tombstonedAt := some operation }),
          progress.2 ++ [.write .links link before { before with tombstonedAt := some operation }])
      else .error .unknownLink

/-- Executable membership checker for the canonical stored-point law. -/
def pointCheck (pre : ContentStore) (document : DocumentId) (point : StablePoint) : Bool :=
  match Hyperdocument.lookup pre .runs point.run with
  | none => false
  | some run => decide (run.document = document) &&
      match point.neighbor with
      | none => decide (run.atoms = [])
      | some atomId => decide (atomId ∈ run.atoms) &&
          match Hyperdocument.lookup pre .atoms atomId with
          | none => false
          | some atom => decide (atom.document = document)

theorem pointCheck_iff (pre : ContentStore) (document : DocumentId) (point : StablePoint) :
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

def rangeCheck (pre : ContentStore) (document : DocumentId) (range : StableRange) : Bool :=
  pointCheck pre document range.start && pointCheck pre document range.finish

theorem rangeCheck_sound (pre : ContentStore) (document : DocumentId) (range : StableRange)
    (checked : rangeCheck pre document range = true) :
    StoredRangeValidAt pre document range := by
  simp only [rangeCheck, Bool.and_eq_true] at checked
  exact ⟨rfl, (pointCheck_iff _ _ _).mp checked.1, (pointCheck_iff _ _ _).mp checked.2⟩

def runAtomsCheck (pre : ContentStore) (document : DocumentId) (atoms : List AtomId) : Bool :=
  decide atoms.Nodup && atoms.all (fun atomId =>
    match Hyperdocument.lookup pre .atoms atomId with
    | none => false
    | some atom => decide (atom.document = document))

/-- The annotated atom is in this document and still at the revision the
annotator read.  A revision equal to this operation names a write of this same
command, which no reader observed, so it is refused too. -/
def pinCheck (pre : ContentStore) (document : DocumentId) (atom : AtomId)
    (revision operation : OperationId) : Bool :=
  match Hyperdocument.lookup pre .atoms atom with
  | none => false
  | some record => decide (record.document = document) && decide (record.revision = revision) &&
      decide (revision ≠ operation)

/-- A kernel annotation is a record of the cell: visible to exactly the cell's
readers, since a resource view is the whole cell.  No other value is written. -/
def cellReaders : Digest := ⟨0⟩

def annotationRecord (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (atom : AtomId) (revision : OperationId) (body : List UInt8) : AnnotationRecord :=
  ⟨document, .atom atom revision, .inline body, author, operation, cellReaders, none⟩

/-- The link relation of a quote's backlink. -/
def quoteRelation : Digest :=
  (Sp800185Cshake256.hash "DREGG/CONTENT/RELATION".toUTF8.toList "quote".toUTF8.toList).digest

def quoteElement (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (reference : EmbedRef) : ElementRecord :=
  ⟨document, none, .embed reference, author, operation, none⟩

def quoteLink (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (reference : EmbedRef) : LinkRecord :=
  ⟨document, none, .document reference.document, quoteRelation, author, operation, none⟩

def step (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (progress : Progress) : Action → Except Reject Progress
  | .createDocument root schema body => do
      let next ← allocate progress .documents document ⟨root, schema, author, operation⟩
      allocate next .elements root ⟨document, none, body, author, operation, none⟩
  | .createAtom atom kind payload =>
      allocate progress .atoms atom ⟨document, kind, payload, author, operation, operation, none⟩
  | .editAtom edit =>
      replaceAtom document progress edit.atomId edit.before (editAtomRecord operation edit)
  | .link link source target relation =>
      if source.all (rangeCheck progress.1 document) then
        allocate progress .links link
          ⟨document, source, target, relation, author, operation, none⟩
      else .error .invalidSourceRange
  | .createRun runId atoms =>
      if runAtomsCheck progress.1 document atoms then
        allocate progress .runs runId ⟨document, atoms, author, operation, none⟩
      else .error .invalidRun
  | .annotate annotationId atom revision body =>
      if pinCheck progress.1 document atom revision operation then
        allocate progress .annotations annotationId (annotationRecord author operation document atom revision body)
      else .error .staleAtom
  | .quote element link reference => do
      let next ← allocate progress .elements element (quoteElement author operation document reference)
      allocate next .links link (quoteLink author operation document reference)
  | .unlink link => retireLink document operation progress link

def run (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (pre : ContentStore) (command : Command) : Except Reject Progress :=
  command.actions.foldlM (step author operation document) (pre, [])

/-! ## The emitted patch executes exactly -/

/-- The invariant of a run from `pre`: the emitted patch is valid at `pre`
and runs to the progress store. -/
def Executes (pre : ContentStore) (progress : Progress) : Prop :=
  Patch.ValidFrom pre progress.2 ∧ Patch.run pre progress.2 = progress.1

private theorem executes_append (pre : ContentStore) (progress : Progress)
    (op : Op Hyperdocument.layout) (holds : Executes pre progress)
    (enabled : op.Enabled progress.1) :
    Executes pre (op.apply progress.1, progress.2 ++ [op]) := by
  obtain ⟨valid, ran⟩ := holds
  refine ⟨?_, ?_⟩
  · rw [Patch.validFrom_append, ran]
    exact ⟨valid, enabled, trivial⟩
  · rw [Patch.run_append, ran]
    rfl

theorem allocate_executes (pre : ContentStore) (progress next : Progress)
    (space : Namespace) (key : Key space) (value : Value space)
    (holds : Executes pre progress)
    (accepted : allocate progress space key value = .ok next) : Executes pre next := by
  unfold allocate at accepted
  split at accepted
  · rename_i fresh
    cases accepted
    exact executes_append pre progress (.allocate space key value) holds
      ⟨by simp, fresh⟩
  · cases accepted

theorem replaceAtom_executes (pre : ContentStore) (document : DocumentId)
    (progress next : Progress) (atom : AtomId) (before after : AtomRecord)
    (holds : Executes pre progress)
    (accepted : replaceAtom document progress atom before after = .ok next) :
    Executes pre next := by
  unfold replaceAtom at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · rename_i present
      cases accepted
      exact executes_append pre progress (.write .atoms atom before after) holds
        ⟨rfl, not_not.mp present⟩

theorem step_executes (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (pre : ContentStore) (progress next : Progress) (action : Action)
    (holds : Executes pre progress)
    (accepted : step author operation document progress action = .ok next) :
    Executes pre next := by
  cases action with
  | createDocument root schema body =>
      simp only [step] at accepted
      cases first : allocate progress .documents document ⟨root, schema, author, operation⟩ with
      | error reason => simp [first, bind, Except.bind] at accepted
      | ok middle =>
          simp only [first, bind, Except.bind] at accepted
          exact allocate_executes pre middle next _ _ _
            (allocate_executes pre progress middle _ _ _ holds first) accepted
  | createAtom atom kind payload =>
      exact allocate_executes pre progress next _ _ _ holds accepted
  | editAtom edit =>
      exact replaceAtom_executes pre document progress next _ _ _ holds accepted
  | link link source target relation =>
      simp only [step] at accepted
      split at accepted
      · exact allocate_executes pre progress next _ _ _ holds accepted
      · cases accepted
  | createRun runId atoms =>
      simp only [step] at accepted
      split at accepted
      · exact allocate_executes pre progress next _ _ _ holds accepted
      · cases accepted
  | annotate annotationId atom revision body =>
      simp only [step] at accepted
      split at accepted
      · exact allocate_executes pre progress next _ _ _ holds accepted
      · cases accepted
  | quote element link reference =>
      simp only [step] at accepted
      cases first : allocate progress .elements element
          (quoteElement author operation document reference) with
      | error reason => simp [first, bind, Except.bind] at accepted
      | ok middle =>
          simp only [first, bind, Except.bind] at accepted
          exact allocate_executes pre middle next _ _ _
            (allocate_executes pre progress middle _ _ _ holds first) accepted
  | unlink link =>
      simp only [step, retireLink] at accepted
      split at accepted
      · cases accepted
      · rename_i before present
        split at accepted
        · cases accepted
          exact executes_append pre progress _ holds ⟨rfl, present⟩
        · cases accepted

theorem foldlM_executes (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (pre : ContentStore) (actions : List Action) (progress next : Progress)
    (holds : Executes pre progress)
    (accepted : actions.foldlM (step author operation document) progress = .ok next) :
    Executes pre next := by
  induction actions generalizing progress with
  | nil =>
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at accepted
      exact accepted ▸ holds
  | cons action rest induction =>
      simp only [List.foldlM_cons, bind, Except.bind] at accepted
      cases stepped : step author operation document progress action with
      | error reason => simp [stepped] at accepted
      | ok middle =>
          simp only [stepped] at accepted
          exact induction middle
            (step_executes author operation document pre progress middle action holds stepped)
            accepted

/-- An accepted run emits a patch valid at `pre` whose run is its post. -/
theorem run_executes (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (pre : ContentStore) (command : Command) (next : Progress)
    (accepted : run author operation document pre command = .ok next) :
    Patch.ValidFrom pre next.2 ∧ Patch.run pre next.2 = next.1 :=
  foldlM_executes author operation document pre command.actions (pre, []) next
    ⟨trivial, rfl⟩ accepted

theorem accepted_link_source_stored (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (progress next : Progress) (linkId : LinkId)
    (source : StableRange) (target : LinkTarget) (relation : Digest)
    (accepted : step author operation document progress
      (.link linkId (some source) target relation) = .ok next) :
    StoredRangeValidAt progress.1 document source := by
  by_cases checked : rangeCheck progress.1 document source = true
  · exact rangeCheck_sound progress.1 document source checked
  · simp [step, checked] at accepted

/-! ## Preparation on the cell -/

structure PreparedCell (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (pre : ContentCell) (command : Command) where
  private mk ::
  progress : Progress
  nonempty : command.actions ≠ []
  computed : run author operation document pre.logical command = .ok progress
  validated : ValidatedPatch HyperdocumentCell.contentMaterializer pre pre.root progress.2

def PreparedCell.post {author : PrincipalRef} {operation : OperationId} {document : DocumentId}
    {pre : ContentCell} {command : Command}
    (prepared : PreparedCell author operation document pre command) : ContentCell :=
  prepared.validated.apply

/-- The validated post is exactly the store the action run computed. -/
theorem PreparedCell.post_exact {author : PrincipalRef} {operation : OperationId}
    {document : DocumentId} {pre : ContentCell} {command : Command}
    (prepared : PreparedCell author operation document pre command) :
    prepared.post.logical = prepared.progress.1 :=
  (run_executes author operation document pre.logical command _ prepared.computed).2

def prepareCell (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (pre : ContentCell) (command : Command) :
    Except Reject (PreparedCell author operation document pre command) :=
  if nonempty : command.actions ≠ [] then
    match computed : run author operation document pre.logical command with
    | .error reason => .error reason
    | .ok progress =>
        match validate HyperdocumentCell.contentMaterializer pre pre.root progress.2 with
        | .rejected _ => .error .invalidPatch
        | .accepted validated => .ok ⟨progress, nonempty, computed, validated⟩
  else .error .emptyActions

/-- Completeness: an accepted run always validates at the cell's own root, so
`invalidPatch` is unreachable for commands the lowering accepts. -/
theorem prepareCell_ok_of_run (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (pre : ContentCell) (command : Command) (progress : Progress)
    (nonempty : command.actions ≠ [])
    (computed : run author operation document pre.logical command = .ok progress) :
    ∃ prepared, prepareCell author operation document pre command = .ok prepared := by
  obtain ⟨validated, accepted⟩ := validate_accepts HyperdocumentCell.contentMaterializer pre
    pre.root progress.2 rfl (run_executes author operation document _ command progress computed).1
  unfold prepareCell
  rw [dif_pos nonempty]
  split
  · rename_i reason other
    rw [computed] at other
    cases other
  · rename_i result other
    rw [computed] at other
    cases other
    rw [accepted]
    exact ⟨_, rfl⟩

theorem empty_command_rejected (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (pre : ContentCell) :
    prepareCell author operation document pre ⟨[]⟩ = .error .emptyActions := by
  simp [prepareCell]

/-- Exact old-record mismatch refuses a write, even for an authorized caller. -/
theorem replaceAtom_stale (document : DocumentId) (progress : Progress) (atom : AtomId)
    (before after : AtomRecord)
    (localBefore : before.document = document) (localAfter : after.document = document)
    (missing : (show Option AtomRecord from progress.1 ⟨.atoms, atom⟩) ≠ some before) :
    replaceAtom document progress atom before after = .error .staleAtom := by
  simp [replaceAtom, localBefore, localAfter, missing]

/-- Different payload bytes have different canonical encodings. Hash equality
still needs the materializer's explicit pair-scoped collision premise. -/
theorem atom_payload_encoding_distinct (before after : AtomRecord)
    (different : before.payload ≠ after.payload) :
    atomRecordStream.encode before ≠ atomRecordStream.encode after := by
  intro same
  have equal : before = after :=
    Hyperdocument.lawfulCodec_encode_injective atomRecordStream.toLawful same
  exact different (congrArg AtomRecord.payload equal)

/-! ## Policy view -/

def payloadBytesAt (store : ContentStore) : Store.Address Hyperdocument.layout → Nat
  | ⟨.atoms, atom⟩ =>
      match Hyperdocument.lookup store .atoms atom with
      | some record => record.payload.length
      | none => 0
  | ⟨.elements, element⟩ =>
      match Hyperdocument.lookup store .elements element with
      | some ⟨_, _, .opaque _ payload, _, _, _⟩ => payload.length
      | _ => 0
  | _ => 0

def contentPayloadBytes (store : ContentStore) : Nat :=
  store.support.sum (payloadBytesAt store)

/-- Count the entire committed encoding, including typed references, authors,
identifiers and framing. A large link cannot evade a content-size policy. -/
def contentBytes (store : ContentStore) : Nat :=
  (HyperdocumentCell.contentMaterializer.codec.encode store).length

/-- The two fields of a content cell as a scope names them (K-FIELDS
`FieldId.body` / `FieldId.annotations`): links, marks and annotation records
are the annotations field; every other namespace is the body. -/
def annotationNamespace : Hyperdocument.Namespace → Bool
  | .links | .marks | .annotations => true
  | _ => false

/-- Addresses whose record differs between two stores, in one field. -/
def changedIn (field : Bool) (before after : ContentStore) : Finset Hyperdocument.Address :=
  (before.support ∪ after.support).filter
    (fun address => annotationNamespace address.1 = field ∧ before address ≠ after address)

/-- Records of the body that a write changed, derived from pre and post state. -/
def bodyWrites (before after : ContentStore) : Nat := (changedIn false before after).card

/-- Records of the annotations field that a write changed. -/
def annotationWrites (before after : ContentStore) : Nat := (changedIn true before after).card

def Action.tag : Action → Nat
  | .createDocument .. => 0
  | .createAtom .. => 1
  | .editAtom .. => 2
  | .link .. => 3
  | .createRun .. => 4
  | .annotate .. => 5
  | .quote .. => 6
  | .unlink .. => 7

def actionCount (command : Command) (tag : Nat) : Nat :=
  (command.actions.filter (fun action => action.tag == tag)).length

/-- Source-derived policy inputs count actual committed bytes; no content or
identity is reduced to a scalar identifier. -/
def project (before after : ContentStore) (command : Command) : List (String × Int) :=
  [("content/bytes/before", contentBytes before),
   ("content/bytes/after", contentBytes after),
   ("content/bytes/delta", (contentBytes after : Int) - contentBytes before),
   ("content/entries/before", before.support.card),
   ("content/entries/after", after.support.card),
   ("content/operations", command.actions.length),
   ("content/payload-bytes/before", contentPayloadBytes before),
   ("content/payload-bytes/after", contentPayloadBytes after),
   ("content/document-creates", actionCount command 0),
   ("content/atom-creates", actionCount command 1),
   ("content/atom-edits", actionCount command 2),
   ("content/links", actionCount command 3),
   ("content/run-creates", actionCount command 4),
   ("content/annotations", actionCount command 5),
   ("content/quotes", actionCount command 6),
   ("content/unlinks", actionCount command 7),
   ("content/writes/body", bodyWrites before after),
   ("content/writes/annotations", annotationWrites before after),
   ("content/tombstones", (command.actions.filter fun action => match action with
      | .editAtom edit => edit.tombstone
      | _ => false).length)]

/-! ## Annotations: attached to a read revision, never touching the body -/

/-- An accepted annotate allocates exactly one annotation record and changes
no other address: every record outside the annotations namespace — atoms,
runs, elements, the document — is the record it was. -/
theorem annotate_preserves_body (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (progress next : Progress) (annotationId : AnnotationId) (atom : AtomId)
    (revision : OperationId) (body : List UInt8)
    (accepted : step author operation document progress (.annotate annotationId atom revision body) = .ok next)
    (address : Hyperdocument.Address) (outside : address.1 ≠ .annotations) :
    next.1 address = progress.1 address := by
  simp only [step] at accepted
  split at accepted
  · unfold allocate at accepted
    split at accepted
    · cases accepted
      exact Store.Store.set_ne _ _ _ address (fun same => outside (congrArg Sigma.fst same))
    · cases accepted
  · cases accepted

/-- An annotate whose atom is absent, in another document, or no longer at the
named revision is refused `staleAtom`, before anything is written. -/
theorem annotate_stale_refused (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (progress : Progress) (annotationId : AnnotationId) (atom : AtomId)
    (revision : OperationId) (body : List UInt8)
    (moved : ∀ record, Hyperdocument.lookup progress.1 .atoms atom = some record →
      record.revision ≠ revision) :
    step author operation document progress (.annotate annotationId atom revision body) = .error .staleAtom := by
  have unchecked : pinCheck progress.1 document atom revision operation = false := by
    unfold pinCheck
    cases found : Hyperdocument.lookup progress.1 .atoms atom with
    | none => rfl
    | some record => simp [moved record found]
  simp [step, unchecked]

/-- Refuted pole: an atom at the named revision, written by an earlier
operation, is annotated. -/
theorem annotate_fresh_admitted (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (progress : Progress) (annotationId : AnnotationId) (atom : AtomId)
    (record : AtomRecord) (body : List UInt8)
    (found : Hyperdocument.lookup progress.1 .atoms atom = some record)
    (local_ : record.document = document) (earlier : record.revision ≠ operation)
    (fresh : progress.1 ⟨.annotations, annotationId⟩ = none) :
    ∃ next, step author operation document progress
      (.annotate annotationId atom record.revision body) = .ok next := by
  have checked : pinCheck progress.1 document atom record.revision operation = true := by
    simp [pinCheck, found, local_, earlier]
  simp only [step, checked, if_true, allocate, fresh]
  exact ⟨_, rfl⟩

/-- An edit moves the atom's revision to the editing operation. -/
@[simp] theorem editAtomRecord_revision (operation : OperationId) (edit : EditAtomPayload) :
    (editAtomRecord operation edit).revision = operation := rfl

/-- An annotation is current while its atom is still at the anchored revision. -/
def annotationFresh (store : ContentStore) (record : AnnotationRecord) : Bool :=
  match record.anchor with
  | .atom atom revision =>
      match Hyperdocument.lookup store .atoms atom with
      | some current => decide (current.revision = revision)
      | none => false
  | _ => true

/-- After an edit by another operation, an annotation anchored at the atom's
earlier revision reads as stale. -/
theorem annotation_stale_after_edit (store : ContentStore) (record : AnnotationRecord)
    (atom : AtomId) (revision operation : OperationId) (edit : EditAtomPayload)
    (anchored : record.anchor = .atom atom revision) (later : operation ≠ revision)
    (edited : Hyperdocument.lookup store .atoms atom = some (editAtomRecord operation edit)) :
    annotationFresh store record = false := by
  simp [annotationFresh, anchored, edited, later]

/-! ## The field footprint: annotate writes only the annotations field -/

private theorem changedIn_empty_of_agree (field : Bool) (before after : ContentStore)
    (agree : ∀ address : Hyperdocument.Address, annotationNamespace address.1 = field →
      after address = before address) :
    changedIn field before after = ∅ := by
  apply Finset.filter_eq_empty_iff.mpr
  intro address _ ⟨inField, differs⟩
  exact differs (agree address inField).symm

/-- Every action of the command is an annotate. -/
def Command.annotateOnly (command : Command) : Bool :=
  command.actions.all fun action => action.tag == 5

private theorem foldlM_annotate_frames (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (actions : List Action) (progress next : Progress)
    (only : actions.all (fun action => action.tag == 5) = true)
    (accepted : actions.foldlM (step author operation document) progress = .ok next)
    (address : Hyperdocument.Address) (outside : address.1 ≠ .annotations) :
    next.1 address = progress.1 address := by
  induction actions generalizing progress with
  | nil =>
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at accepted
      rw [accepted]
  | cons action rest induction =>
      simp only [List.all_cons, Bool.and_eq_true] at only
      simp only [List.foldlM_cons, bind, Except.bind] at accepted
      cases stepped : step author operation document progress action with
      | error reason => simp [stepped] at accepted
      | ok middle =>
          simp only [stepped] at accepted
          rw [induction middle only.2 accepted]
          cases action with
          | annotate annotationId atom revision body =>
              exact annotate_preserves_body author operation document progress middle
                annotationId atom revision body stepped address outside
          | _ => simp [Action.tag] at only

/-- An accepted annotate-only command changes no body record: the projected
`content/writes/body` is `0`, so a law (or a K-FIELDS scope naming only
`annotations`) that refuses body writes admits it. -/
theorem annotate_writes_no_body (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (pre : ContentStore) (command : Command) (next : Progress)
    (only : command.annotateOnly = true)
    (accepted : run author operation document pre command = .ok next) :
    bodyWrites pre next.1 = 0 := by
  unfold bodyWrites
  rw [changedIn_empty_of_agree false pre next.1]
  · rfl
  intro address body
  apply foldlM_annotate_frames author operation document command.actions (pre, []) next only
    accepted address
  intro annotations
  rw [annotations] at body
  exact Bool.noConfusion body

/-- The other pole: an edit that changes an atom record is a body write, so a
law or scope refusing body writes refuses it.  Annotate authority does not
cover edit. -/
theorem edit_is_body_write (before : ContentStore) (atom : AtomId) (old new : AtomRecord)
    (present : before ⟨.atoms, atom⟩ = some old) (changed : old ≠ new) :
    0 < bodyWrites before (before.set ⟨.atoms, atom⟩ (some new)) := by
  apply Finset.card_pos.mpr
  refine ⟨⟨.atoms, atom⟩, ?_⟩
  simp only [changedIn, Finset.mem_filter, Finset.mem_union, DFinsupp.mem_support_iff]
  refine ⟨Or.inl ?_, rfl, ?_⟩
  · rw [present]; exact Option.some_ne_none old
  · rw [Store.Store.set_eq, present]
    exact fun same => changed (Option.some.inj same)

/-! ## Quotes: pinned by revision, rendered only through the reader's own read -/

/-- What a reader sees where a quote stands. -/
inductive QuoteView where
  /-- The reader holds no read of the source document. -/
  | unavailable
  /-- A snapshot quote whose source atom has moved since it was quoted. -/
  | stale
  /-- The source bytes; `revised` says a live transclusion's atom has moved. -/
  | quoted (bytes : List UInt8) (revised : Bool)
  deriving DecidableEq, Repr

/-- Render one embed against the reader's view of its source.  `source` is
the store the reader obtained by its own signed read: the observation
controller returns a cell only for a grant whose actual observe capability
covers it (`NativeObservationController.AuthorizedIntent.query_footprint`), so
`none` is exactly "this reader cannot read the source".  The caller pairs a
view with the document it read (`documentOf target`); an atom of another
document in it is not the quoted atom. -/
def renderQuote (source : Option ContentStore) (reference : EmbedRef) : QuoteView :=
  match source with
  | none => .unavailable
  | some store =>
      match Hyperdocument.lookup store .atoms reference.atom with
        | none => .stale
        | some current =>
            if current.document ≠ reference.document then .stale
            else match reference.mode with
              | .snapshot =>
                  if current.revision = reference.revision then .quoted current.payload false
                  else .stale
              | .live => .quoted current.payload (decide (current.revision ≠ reference.revision))

/-- The reader's view of a source cell: present iff its read is covered. -/
def readerView (covered : Bool) (source : ContentStore) : Option ContentStore :=
  if covered then some source else none

/-- A reader not covered on the source sees `[quoted: unavailable]`, and what
it sees does not depend on the source's content at all. -/
theorem transclusion_respects_source_coverage (reference : EmbedRef) (left right : ContentStore) :
    renderQuote (readerView false left) reference = .unavailable ∧
      renderQuote (readerView false left) reference =
        renderQuote (readerView false right) reference :=
  ⟨rfl, rfl⟩

/-- Refuted pole: a covered reader of a fresh quote sees the source bytes,
so the gate above is not constantly `unavailable`. -/
theorem transclusion_covered_reader_sees_bytes (store : ContentStore) (reference : EmbedRef)
    (record : AtomRecord)
    (found : Hyperdocument.lookup store .atoms reference.atom = some record)
    (local_ : record.document = reference.document) (pinned : record.revision = reference.revision)
    (snapshot : reference.mode = .snapshot) :
    renderQuote (readerView true store) reference = .quoted record.payload false := by
  simp [renderQuote, readerView, found, local_, pinned, snapshot]

/-- A snapshot quote shows bytes only at the pinned revision, and then exactly
the source atom's bytes; once the atom moves it reads as stale, never as the
new bytes. -/
theorem quote_pinned_by_revision (store : ContentStore) (reference : EmbedRef)
    (snapshot : reference.mode = .snapshot) (bytes : List UInt8) (revised : Bool)
    (shown : renderQuote (some store) reference = .quoted bytes revised) :
    ∃ record, Hyperdocument.lookup store .atoms reference.atom = some record ∧
      record.revision = reference.revision ∧ record.payload = bytes := by
  cases found : Hyperdocument.lookup store .atoms reference.atom with
  | none => simp [renderQuote, found] at shown
  | some record =>
      by_cases local_ : record.document = reference.document
      · by_cases pinned : record.revision = reference.revision
        · simp [renderQuote, found, local_, pinned, snapshot] at shown
          exact ⟨record, rfl, pinned, shown.1⟩
        · simp [renderQuote, found, local_, pinned, snapshot] at shown
      · simp [renderQuote, found, local_] at shown

theorem quote_stale_after_move (store : ContentStore) (reference : EmbedRef)
    (record : AtomRecord)
    (found : Hyperdocument.lookup store .atoms reference.atom = some record)
    (local_ : record.document = reference.document) (moved : record.revision ≠ reference.revision)
    (snapshot : reference.mode = .snapshot) :
    renderQuote (some store) reference = .stale := by
  simp [renderQuote, found, local_, moved, snapshot]

/-- The quote's records hold the reference and nothing of the source: the
quoting cell is the same whatever the source holds. -/
theorem quote_writes (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (progress next : Progress) (element : ElementId) (link : LinkId) (reference : EmbedRef)
    (accepted : step author operation document progress (.quote element link reference) = .ok next) :
    next.1 = (progress.1.set ⟨.elements, element⟩
        (some (quoteElement author operation document reference))).set ⟨.links, link⟩
      (some (quoteLink author operation document reference)) := by
  simp only [step] at accepted
  cases first : allocate progress .elements element
      (quoteElement author operation document reference) with
  | error reason => simp [first, bind, Except.bind] at accepted
  | ok middle =>
      simp only [first, bind, Except.bind] at accepted
      unfold allocate at first accepted
      split at first
      · cases first
        split at accepted
        · cases accepted; rfl
        · cases accepted
      · cases first

/-- info: 'Minidregg.Kernel.ContentResource.command_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms command_roundtrip
/-- info: 'Minidregg.Kernel.ContentResource.retired_command_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retired_command_refused
/-- info: 'Minidregg.Kernel.ContentResource.run_executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_executes
/-- info: 'Minidregg.Kernel.ContentResource.PreparedCell.post_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedCell.post_exact
/-- info: 'Minidregg.Kernel.ContentResource.prepareCell_ok_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prepareCell_ok_of_run
/-- info: 'Minidregg.Kernel.ContentResource.atom_payload_encoding_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms atom_payload_encoding_distinct

/-- info: 'Minidregg.Kernel.ContentResource.annotate_preserves_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms annotate_preserves_body
/-- info: 'Minidregg.Kernel.ContentResource.annotate_stale_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms annotate_stale_refused
/-- info: 'Minidregg.Kernel.ContentResource.annotate_writes_no_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms annotate_writes_no_body
/-- info: 'Minidregg.Kernel.ContentResource.edit_is_body_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms edit_is_body_write
/-- info: 'Minidregg.Kernel.ContentResource.quote_pinned_by_revision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms quote_pinned_by_revision
/-- info: 'Minidregg.Kernel.ContentResource.transclusion_covered_reader_sees_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transclusion_covered_reader_sees_bytes

end Minidregg.Kernel.ContentResource
