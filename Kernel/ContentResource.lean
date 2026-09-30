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

Command grammar v2 (`DREGG/CONTENT/MUTATE` ++ [2]): links carry `LinkTarget`.
Version-1 commands (whose links carried the retired `ForwardTarget`) refuse
to decode (`v1_command_refused`).
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
  deriving DecidableEq

abbrev ActionWire := Sum (ElementId × Digest × ElementBody)
  (Sum (AtomId × AtomKind × List UInt8)
    (Sum EditAtomPayload
      (Sum (LinkId × Option StableRange × LinkTarget × Digest) (RunId × List AtomId))))

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
  deriving DecidableEq

def commandStream : StreamCodec Command :=
  StreamCodec.xmap (StreamCodec.list actionStream) Command.actions
    (fun actions => ⟨actions⟩) (by intro command; rfl)

/-- Action grammar version; independent of the content cell's storage wire. -/
def commandVersion : Nat := 2

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

/-- A version-1 command frame refuses to decode. -/
theorem v1_command_refused (payload : List UInt8) :
    rawCommandCodec.decode ("DREGG/CONTENT/MUTATE".toUTF8.toList ++ 1 :: payload) = none := by
  let oldFrame : List UInt8 := "DREGG/CONTENT/MUTATE".toUTF8.toList ++ [1]
  have lengthExact : commandFrame.length = oldFrame.length := by
    simp [commandFrame, oldFrame]
  have different : oldFrame ≠ commandFrame := by decide +kernel
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

def step (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (progress : Progress) : Action → Except Reject Progress
  | .createDocument root schema body => do
      let next ← allocate progress .documents document ⟨root, schema, author, operation⟩
      allocate next .elements root ⟨document, none, body, author, operation, none⟩
  | .createAtom atom kind payload =>
      allocate progress .atoms atom ⟨document, kind, payload, author, operation, none⟩
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

def Action.tag : Action → Nat
  | .createDocument .. => 0
  | .createAtom .. => 1
  | .editAtom .. => 2
  | .link .. => 3
  | .createRun .. => 4

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
   ("content/tombstones", (command.actions.filter fun action => match action with
      | .editAtom edit => edit.tombstone
      | _ => false).length)]

/-- info: 'Minidregg.Kernel.ContentResource.command_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms command_roundtrip
/-- info: 'Minidregg.Kernel.ContentResource.v1_command_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v1_command_refused
/-- info: 'Minidregg.Kernel.ContentResource.run_executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_executes
/-- info: 'Minidregg.Kernel.ContentResource.PreparedCell.post_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedCell.post_exact
/-- info: 'Minidregg.Kernel.ContentResource.prepareCell_ok_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prepareCell_ok_of_run
/-- info: 'Minidregg.Kernel.ContentResource.atom_payload_encoding_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms atom_payload_encoding_distinct

end Minidregg.Kernel.ContentResource
