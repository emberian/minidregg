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

Command grammar v8 adds protected annotation wrappers to v7, which added `mark` and `unmark` to
v6, which added `unlink` to v5, which gave a document an element tree.  `createDocument` makes the root, an empty container; `createAtom` and
`transclude` append their new leaf (an `atom` or `embed` element carrying the
record's own identifier) to the root; and `editElement` splices a detached
element into a container, moves a child within one, or removes (detaches) one,
each against the revision of the container its author read.  A line placed at
position N is a `createAtom` and a `move` to N in one command, all or nothing.  Document order is the pre-order walk of the
tree (`documentOrder`), never an identifier sort.  Versions 1–6 refuse to decode
(`retired_command_refused`): v6 had no marks and v5 no `unlink` (each tail sum
was shorter), v4 had no tree (a document's lines were ordered by
atom identifier), v3 had the atom `quote`, v2 no annotate and no atom revision,
v1 the retired `ForwardTarget`.

`unlink` retires one live link of the document: the record stays, with
`tombstonedAt` set to the retiring operation, and the backlink index
(`Kernel.LinkIndex`) drops it.

`mark` lays a `MarkRecord` on one line (atom) or element at the revision its
author read — `bold`, `italic`, `code`, `heading`, or `link`.  A link mark
also writes an ordinary `LinkRecord` (relation `markRelation`): the link record
is primary, read by backlinks and the link index; the mark names it and places
it on the line.  A mark is stale once its target moves (`markFresh`), never
re-anchored.  `unmark` retires a live mark — only its author or the document's
owner may — and a link mark's link with it.  Marks and their links are the
`annotations` field (K-FIELDS): they never touch the body.

`annotate` attaches an annotation record to one atom at the revision the
annotator read and writes nothing else.  `transclude` writes a
`TransclusionRecord` naming a range of a source cell — the opening: each live
atom of the range at its revision, and the height — plus a forward link whose
target is that transclusion, and copies no source bytes.  Disclosure is decided
at transclusion time: the action is admitted only when the same transaction
carries an observe-only read of the source cell, which the admission checks
against the transcluder's grant and the source's own policy at this height, and
whose state holds the opening (`openingHolds`).  A reader sees the transcluded
bytes only through its own read of the source, current or `at` the opening's
height (`renderTransclusion`).
-/
import Theory.AssertAxioms
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

/-! ## Transclusion requests and the admission context -/

/-- A request to transclude a range of another document.  `pins` is the
opening the transcluder read: each live atom of the range, in run order, with
its revision.  The admission checks `pins` against the source cell's own state
at this height (`openingHolds`); the host stores the opening, never the bytes. -/
structure TranscludeRequest where
  source : Nat
  range : StableRange
  mode : TransclusionMode
  pins : List (AtomId × OperationId)
  deriving DecidableEq

def pinStream : StreamCodec (AtomId × OperationId) :=
  StreamCodec.product (identifierStream .v1 .atom) (identifierStream .v1 .operationIntent)

def transcludeRequestStream : StreamCodec TranscludeRequest :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product storedStableRangeStream
      (StreamCodec.product transclusionModeStream (StreamCodec.list pinStream))))
    (fun request => (request.source, request.range, request.mode, request.pins))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro request; cases request; rfl)

/-- What the transaction admission says about one source cell.  It is present
only when the same transaction carries an observe-only read target on that
cell; the admission checks that target's observe capability, signed by the
transcluder, against the source's own policy at this height
(`DeclaredResourceController.transclude_requires_source_coverage`). -/
structure SourceRead where
  /-- The observe capability that covered the read. -/
  capability : CapabilityId
  /-- The source policy (id, epoch, revision) that admitted it. -/
  policy : Digest
  deriving DecidableEq

/-- Admission facts a content action consumes: the height whose state the
transaction reads, and the transaction's read targets. -/
structure Context where
  height : Nat
  sourceRead : Nat → Option SourceRead

/-- A context with no read targets: every transclusion refuses, so no height
is ever recorded under it. -/
def Context.closed : Context := ⟨0, fun _ => none⟩

/-! ## The element tree: placements and edits -/

/-- One edit of one container's children. -/
inductive ElementOp where
  /-- Attach a detached element as the child at `index`. -/
  | splice (index : Nat) (child : ElementId)
  /-- Move a child of this container to `index` among its children. -/
  | move (child : ElementId) (index : Nat)
  /-- Detach a child: it stays stored, in no container and not in the order. -/
  | remove (child : ElementId)
  deriving DecidableEq

abbrev ElementOpWire := Sum (Nat × ElementId) (Sum (ElementId × Nat) ElementId)

def ElementOp.toWire : ElementOp → ElementOpWire
  | .splice index child => .inl (index, child)
  | .move child index => .inr (.inl (child, index))
  | .remove child => .inr (.inr child)

def ElementOp.ofWire : ElementOpWire → ElementOp
  | .inl (index, child) => .splice index child
  | .inr (.inl (child, index)) => .move child index
  | .inr (.inr child) => .remove child

def elementOpStream : StreamCodec ElementOp :=
  StreamCodec.xmap
    (StreamCodec.sum (StreamCodec.product StreamCodec.nat (identifierStream .v1 .element))
      (StreamCodec.sum (StreamCodec.product (identifierStream .v1 .element) StreamCodec.nat)
        (identifierStream .v1 .element)))
    ElementOp.toWire ElementOp.ofWire (by intro op; cases op <;> rfl)

/-- An edit of container `element`, whose children its author read at `revision`. -/
structure EditElement where
  element : ElementId
  revision : OperationId
  op : ElementOp
  deriving DecidableEq

def editElementStream : StreamCodec EditElement :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .element)
      (StreamCodec.product (identifierStream .v1 .operationIntent) elementOpStream))
    (fun edit => (edit.element, edit.revision, edit.op))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2⟩)
    (by intro edit; cases edit; rfl)

/-- What a `mark` is laid on: one line (its atom) or one element. -/
inductive MarkTarget where
  | atom (atom : AtomId)
  | element (element : ElementId)
  deriving DecidableEq

def markTargetStream : StreamCodec MarkTarget :=
  StreamCodec.xmap (StreamCodec.sum (identifierStream .v1 .atom) (identifierStream .v1 .element))
    (fun | .atom atom => .inl atom | .element element => .inr element)
    (fun | .inl atom => .atom atom | .inr element => .element element)
    (by intro target; cases target <;> rfl)

/-- The kind a `mark` asks for.  A `link` names the fresh `LinkRecord` the
action also writes, and that link's target. -/
inductive MarkSpec where
  | bold
  | italic
  | code
  | heading
  | link (link : LinkId) (target : LinkTarget)
  deriving DecidableEq

/-- The stored kind: a link mark keeps only its link's identifier. -/
def MarkSpec.kind : MarkSpec → MarkKind
  | .bold => .bold
  | .italic => .italic
  | .code => .code
  | .heading => .heading
  | .link linkId _ => .link linkId

/-- A kind's tag (as `markKindTag`), then a link mark's link and target.  A tag
past `4` names no kind and refuses to decode. -/
def markSpecStream : StreamCodec MarkSpec where
  encode value :=
    StreamCodec.nat.encode (markKindTag value.kind) ++
      match value with
      | .link linkId target => (identifierStream .v1 .link).encode linkId ++ linkTargetStream.encode target
      | _ => []
  decodePrefix bytes := do
    let (tag, afterTag) ← StreamCodec.nat.decodePrefix bytes
    match tag with
    | 0 => some (.bold, afterTag)
    | 1 => some (.italic, afterTag)
    | 2 => some (.code, afterTag)
    | 3 => some (.heading, afterTag)
    | 4 => do
        let (linkId, afterLink) ← (identifierStream .v1 .link).decodePrefix afterTag
        let (target, suffix) ← linkTargetStream.decodePrefix afterLink
        some (.link linkId target, suffix)
    | _ => none
  decodePrefix_encode := by
    intro value suffix
    cases value <;>
      simp [MarkSpec.kind, markKindTag, List.append_assoc, StreamCodec.nat.decodePrefix_encode,
        (identifierStream .v1 .link).decodePrefix_encode, linkTargetStream.decodePrefix_encode]

/-- A mark of `target` as its author read it at `revision`. -/
structure MarkRequest where
  target : MarkTarget
  revision : OperationId
  spec : MarkSpec
  deriving DecidableEq

def markRequestStream : StreamCodec MarkRequest :=
  StreamCodec.xmap
    (StreamCodec.product markTargetStream
      (StreamCodec.product (identifierStream .v1 .operationIntent) markSpecStream))
    (fun request => (request.target, request.revision, request.spec))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2⟩)
    (by intro request; rfl)

inductive Action where
  /-- The document record and its root element, an empty container. -/
  | createDocument (rootElement : ElementId) (schema : Digest)
  /-- A new atom, and in a document its `atom` leaf, appended to the root. -/
  | createAtom (atom : AtomId) (kind : AtomKind) (payload : List UInt8)
  | editAtom (edit : EditAtomPayload)
  | rewrapAtom (atom : AtomId) (before : AtomRecord) (wrapping : List UInt8)
  | link (link : LinkId) (source : Option StableRange) (target : LinkTarget)
      (relation : Digest)
  | createRun (runId : RunId) (atoms : List AtomId)
  /-- Annotate `atom` as last read at `revision`; refused `staleAtom` if it moved. -/
  | annotate (annotation : AnnotationId) (atom : AtomId) (revision : OperationId)
      (body : AnnotationBody)
  /-- Replace only a protected annotation's key wrapping. Authored ciphertext,
  author, operation and anchor remain byte-identical under an exact record guard. -/
  | rewrapAnnotation (annotation : AnnotationId) (before : AnnotationRecord) (wrapping : List UInt8)
  /-- Transclude a range of another document (`snapshot` or `live`): a
  `TransclusionRecord` holding the opening, and a forward link to it. -/
  | transclude (transclusion : TransclusionId) (link : LinkId) (request : TranscludeRequest)
  /-- Splice, move or remove one child of one container. -/
  | editElement (edit : EditElement)
  /-- A new empty container (a section), appended to the root; refused in a
  cell that holds no document. -/
  | createContainer (element : ElementId)
  /-- Retire a live link of this document (`tombstonedAt := operation`). -/
  | unlink (link : LinkId)
  /-- Mark a line or element as its author read it at `revision`; a `link`
  mark also writes an ordinary link record. -/
  | mark (mark : MarkId) (request : MarkRequest)
  /-- Retire a live mark, and a link mark's link; its author or the document's
  owner only. -/
  | unmark (mark : MarkId)
  deriving DecidableEq

abbrev OriginalActionWire := Sum (ElementId × Digest)
  (Sum (AtomId × AtomKind × List UInt8)
    (Sum EditAtomPayload
      (Sum (LinkId × Option StableRange × LinkTarget × Digest)
        (Sum (RunId × List AtomId)
          (Sum (AnnotationId × AtomId × OperationId × AnnotationBody)
            (Sum (TransclusionId × LinkId × TranscludeRequest)
              (Sum EditElement (Sum ElementId (Sum LinkId
                (Sum (MarkId × MarkRequest) MarkId))))))))))

def originalActionWireStream : StreamCodec OriginalActionWire :=
  StreamCodec.sum
    (StreamCodec.product (identifierStream .v1 .element) digestStream)
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
                  (StreamCodec.product (identifierStream .v1 .operationIntent) HyperdocumentCell.annotationBodyStream)))
              (StreamCodec.sum
                (StreamCodec.product (identifierStream .v1 .transclusion)
                  (StreamCodec.product (identifierStream .v1 .link) transcludeRequestStream))
                (StreamCodec.sum editElementStream
                  (StreamCodec.sum (identifierStream .v1 .element)
                    (StreamCodec.sum (identifierStream .v1 .link)
                      (StreamCodec.sum
                        (StreamCodec.product (identifierStream .v1 .mark) markRequestStream)
                        (identifierStream .v1 .mark)))))))))))

abbrev ActionWire := Sum OriginalActionWire
  (Sum (AnnotationId × AnnotationRecord × List UInt8) (AtomId × AtomRecord × List UInt8))

def actionWireStream : StreamCodec ActionWire :=
  StreamCodec.sum originalActionWireStream
    (StreamCodec.sum
      (StreamCodec.product (identifierStream .v1 .annotation)
        (StreamCodec.product HyperdocumentCell.annotationRecordStream bytesStream))
      (StreamCodec.product (identifierStream .v1 .atom)
        (StreamCodec.product atomRecordStream bytesStream)))

def Action.toWire : Action → ActionWire
  | .createDocument root schema => .inl (.inl (root, schema))
  | .createAtom atom kind payload => .inl (.inr (.inl (atom, kind, payload)))
  | .editAtom edit => .inl (.inr (.inr (.inl edit)))
  | .link linkId source target relation =>
      .inl (.inr (.inr (.inr (.inl (linkId, source, target, relation)))))
  | .createRun runId atoms => .inl (.inr (.inr (.inr (.inr (.inl (runId, atoms))))))
  | .annotate annotationId atom revision body =>
      .inl (.inr (.inr (.inr (.inr (.inr (.inl (annotationId, atom, revision, body)))))))
  | .transclude transclusion linkId request =>
      .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inl (transclusion, linkId, request))))))))
  | .editElement edit => .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl edit))))))))
  | .createContainer element => .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl element)))))))))
  | .unlink linkId => .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl linkId))))))))))
  | .mark markId request =>
      .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (markId, request))))))))))))
  | .unmark markId => .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (markId))))))))))))
  | .rewrapAnnotation annotation before wrapping => .inr (.inl (annotation, before, wrapping))
  | .rewrapAtom atom before wrapping => .inr (.inr (atom, before, wrapping))

def Action.ofWire : ActionWire → Action
  | .inl (.inl (root, schema)) => .createDocument root schema
  | .inl (.inr (.inl (atom, kind, payload))) => .createAtom atom kind payload
  | .inl (.inr (.inr (.inl edit))) => .editAtom edit
  | .inl (.inr (.inr (.inr (.inl (linkId, source, target, relation))))) =>
      .link linkId source target relation
  | .inl (.inr (.inr (.inr (.inr (.inl (runId, atoms)))))) => .createRun runId atoms
  | .inl (.inr (.inr (.inr (.inr (.inr (.inl (annotationId, atom, revision, body))))))) =>
      .annotate annotationId atom revision body
  | .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inl (transclusion, linkId, request)))))))) =>
      .transclude transclusion linkId request
  | .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl edit)))))))) => .editElement edit
  | .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl element))))))))) => .createContainer element
  | .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl linkId)))))))))) => .unlink linkId
  | .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (markId, request)))))))))))) =>
      .mark markId request
  | .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (markId)))))))))))) => .unmark markId
  | .inr (.inl (annotation, before, wrapping)) => .rewrapAnnotation annotation before wrapping
  | .inr (.inr (atom, before, wrapping)) => .rewrapAtom atom before wrapping

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
def commandVersion : Nat := 9

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

/-- Version-1 through version-8 command frames refuse to decode. -/
theorem retired_command_refused (version : UInt8)
    (retired : version = 1 ∨ version = 2 ∨ version = 3 ∨ version = 4 ∨ version = 5 ∨ version = 6 ∨ version = 7 ∨ version = 8)
    (payload : List UInt8) :
    rawCommandCodec.decode ("DREGG/CONTENT/MUTATE".toUTF8.toList ++ version :: payload) = none := by
  let oldFrame : List UInt8 := "DREGG/CONTENT/MUTATE".toUTF8.toList ++ [version]
  have lengthExact : commandFrame.length = oldFrame.length := by
    simp [commandFrame, oldFrame]
  have different : oldFrame ≠ commandFrame := by
    rcases retired with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have refused : rawCommandCodec.decode (oldFrame ++ payload) = none := by
    simp [rawCommandCodec, lengthExact, different]
  simpa only [oldFrame, List.append_assoc, List.singleton_append] using refused

inductive Reject where
  | emptyActions
  | duplicateAddress
  | staleAtom
  | staleAnnotation
  | unprotectedAtom
  | unprotectedAnnotation
  | wrongDocument
  | invalidPatch
  | invalidRun
  | invalidSourceRange
  /-- A transclusion whose source this transaction does not read. -/
  | sourceNotCovered
  /-- A transclusion whose opening the source's state at this height does not hold. -/
  | staleOpening
  /-- No element of this document has that identifier. -/
  | noSuchElement
  /-- A placement or edit names a leaf where a container is required. -/
  | notAContainer
  /-- A position past the end of the container's children. -/
  | indexOutOfRange
  /-- A splice that would place an element under itself or its own descendant. -/
  | cycle
  /-- The container's children moved since the revision its editor read. -/
  | staleElement
  /-- A move or remove of an element that is not a child of the container. -/
  | notAChild
  /-- A splice of an element that already has a place (or is the document root). -/
  | attached
  /-- `unlink` named no live link of this document. -/
  | unknownLink
  /-- A mark names no atom or element of this document. -/
  | noSuchTarget
  /-- The mark's target moved since the revision its author read (or the
  revision names an unread write of this same command). -/
  | staleMark
  /-- `unmark` by a principal that is neither the mark's author nor the
  document's owner. -/
  | notMarkOwner
  /-- `unmark` named no live mark of this document. -/
  | markNotFound
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

/-- An exact source guard preserves immutable authored data; only encrypted
fragment-key custody and its source-attributed maintenance event change. -/
def rewrapAnnotation (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (progress : Progress) (annotation : AnnotationId)
    (before : AnnotationRecord) (wrapping : List UInt8) : Except Reject Progress :=
  if before.document ≠ document ∨ before.tombstonedAt ≠ none then .error .wrongDocument
  else if (show Option AnnotationRecord from progress.1 ⟨.annotations, annotation⟩) ≠ some before then
    .error .staleAnnotation
  else match before.body with
    | .sealed fragment =>
        let after := { before with body := .sealed (fragment.rewrapped author operation wrapping) }
        .ok (progress.1.set ⟨.annotations, annotation⟩ (some after),
          progress.2 ++ [.write .annotations annotation before after])
    | _ => .error .unprotectedAnnotation

/-- Key access maintenance cannot advance an atom's semantic revision. -/
def rewrapAtom (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (progress : Progress) (atom : AtomId)
    (before : AtomRecord) (wrapping : List UInt8) : Except Reject Progress :=
  if before.document ≠ document ∨ before.tombstonedAt ≠ none ∨ before.kind.validPayload before.payload ≠ true then .error .wrongDocument
  else if (show Option AtomRecord from progress.1 ⟨.atoms, atom⟩) ≠ some before then
    .error .staleAtom
  else match before.kind with
    | .sealedObject schema fragment =>
        let after := { before with kind := .sealedObject schema (fragment.rewrapped author operation wrapping) }
        .ok (progress.1.set ⟨.atoms, atom⟩ (some after),
          progress.2 ++ [.write .atoms atom before after])
    | _ => .error .unprotectedAtom

/-- Genuine edits normalize semantic author attribution. Retirement retains
its exact authored payload instead of assigning the tombstoner authorship. -/
def sourceEditAtomRecord (author : PrincipalRef) (operation : OperationId)
    (edit : EditAtomPayload) : AtomRecord :=
  editAtomRecord operation { edit with
    kind := if edit.tombstone then edit.before.kind else edit.kind.authored author operation
    payload := if edit.tombstone then edit.before.payload else edit.payload }

@[simp] theorem sourceEditAtomRecord_revision (author : PrincipalRef)
    (operation : OperationId) (edit : EditAtomPayload) :
    (sourceEditAtomRecord author operation edit).revision = operation := rfl

theorem sourceEditAtomRecord_authored (author : PrincipalRef) (operation : OperationId)
    (edit : EditAtomPayload) (schema : Digest) (fragment : AuthoredFragment)
    (fresh : edit.tombstone = false) (sealed : edit.kind = .sealedObject schema fragment) :
    (sourceEditAtomRecord author operation edit).kind =
      .sealedObject schema (fragment.authored author operation) := by
  simp [sourceEditAtomRecord, editAtomRecord, fresh, sealed, AtomKind.authored]

/-- Even a raw tombstone carrying forged ciphertext/provenance retires the
exact existing payload; caller replacement fields cannot reattribute it. -/
theorem sourceEditAtomRecord_retirement_preserves_authorship (author : PrincipalRef)
    (operation : OperationId) (edit : EditAtomPayload) (retired : edit.tombstone = true) :
    (sourceEditAtomRecord author operation edit).kind = edit.before.kind ∧
      (sourceEditAtomRecord author operation edit).payload = edit.before.payload := by
  simp [sourceEditAtomRecord, editAtomRecord, retired]

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
    (atom : AtomId) (revision : OperationId) (body : AnnotationBody) : AnnotationRecord :=
  let body := match body with
    | .sealed fragment => .sealed (fragment.authored author operation)
    | body => body
  ⟨document, .atom atom revision, body, author, operation, cellReaders, none⟩

/-! ## The stored reference: an opening, never bytes -/

def contentDigest (tag : String) (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash tag.toUTF8.toList bytes).digest

/-- The link relation of a transclusion's forward link. -/
def transcludeRelation : Digest := contentDigest "DREGG/CONTENT/RELATION" "transclude".toUTF8.toList

/-- Names `rangeOpeningStream`, the codec of `OpeningDescriptor.canonicalDescriptor`. -/
def openingCodecId : Digest :=
  contentDigest "DREGG/CONTENT/OPENING-CODEC" "range-opening/v1".toUTF8.toList

/-- Names the relation the admission checked: the pinned atoms are the range's
live atoms at their revisions, read under an observe capability. -/
def openingRelationId : Digest :=
  contentDigest "DREGG/CONTENT/OPENING-RELATION" "live-atoms-at-revisions-under-observe/v1".toUTF8.toList

/-- Source identities of this kind name a Mini cell and a height. -/
def sourceHistoryDomain : Digest :=
  contentDigest "DREGG/CONTENT/SOURCE-HISTORY" "cell-at-height/v1".toUTF8.toList

def atomDisclosureNamespace : Digest :=
  contentDigest "DREGG/CONTENT/DISCLOSURE" "atom".toUTF8.toList

def capabilityDisclosureNamespace : Digest :=
  contentDigest "DREGG/CONTENT/DISCLOSURE" "observe-capability".toUTF8.toList

/-- The opening a transclusion stores: the source cell, the range, each pinned
atom at its revision, and the height whose source state the admission checked.
It carries no bytes. -/
structure RangeOpening where
  source : Nat
  range : StableRange
  pins : List (AtomId × OperationId)
  height : Nat
  deriving DecidableEq

def rangeOpeningStream : StreamCodec RangeOpening :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product storedStableRangeStream
      (StreamCodec.product (StreamCodec.list pinStream) StreamCodec.nat)))
    (fun opening => (opening.source, opening.range, opening.pins, opening.height))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro opening; cases opening; rfl)

def RangeOpening.ofRequest (request : TranscludeRequest) (height : Nat) : RangeOpening :=
  ⟨request.source, request.range, request.pins, height⟩

def RangeOpening.descriptor (opening : RangeOpening) : List UInt8 :=
  rangeOpeningStream.encode opening

/-- The canonical `StoredTransclusionRef` of an opening.  `source` names the
cell and the height; `semanticRoot` commits the pins (atom identities and
revisions, no bytes); `disclosureScope` lists the disclosed atoms;
`capabilityCeiling` names the observe capability the admission checked. -/
def referenceOf (opening : RangeOpening) (mode : TransclusionMode) (read : SourceRead) :
    StoredTransclusionRef where
  referenceRoot := contentDigest "DREGG/CONTENT/TRANSCLUSION-REFERENCE"
    (opening.descriptor ++ transclusionModeStream.encode mode)
  source := ⟨sourceHistoryDomain, ⟨opening.source⟩, ⟨opening.height⟩,
    contentDigest "DREGG/CONTENT/OPENING-VALUE" ((StreamCodec.list pinStream).encode opening.pins)⟩
  opening := ⟨.range, openingCodecId, openingRelationId, opening.descriptor,
    contentDigest "DREGG/CONTENT/OPENING" opening.descriptor⟩
  mode := mode
  disclosureScope := (opening.pins.map fun pin =>
    (⟨atomDisclosureNamespace, (identifierStream .v1 .atom).encode pin.1⟩ : DisclosureAtom)).toFinset
  capabilityCeiling := {⟨capabilityDisclosureNamespace, StreamCodec.nat.encode read.capability.value⟩}

/-- The opening a stored reference carries. -/
def openingOfReference (reference : StoredTransclusionRef) : Option RangeOpening :=
  rangeOpeningStream.toLawful.decode reference.opening.canonicalDescriptor

/-- The Theory's transclude payload (`HyperdocumentOperations.transcludeWrites`)
for one admitted request: the record and its forward link. -/
def transcludePayload (document : DocumentId) (transclusion : TransclusionId) (link : LinkId)
    (request : TranscludeRequest) (height : Nat) (read : SourceRead) : TranscludePayload where
  id := transclusion
  forwardLinkId := link
  hostDocument := document
  source := none
  reference := referenceOf (.ofRequest request height) request.mode read
  relation := transcludeRelation
  disclosurePolicy := read.policy


/-! ## The element tree -/

/-- The element record at `element`, if any. -/
def elementAt (store : ContentStore) (element : ElementId) : Option ElementRecord :=
  Hyperdocument.lookup store .elements element

def parentOf (store : ContentStore) (element : ElementId) : Option ElementId :=
  (elementAt store element).bind ElementRecord.parent

def bodyChildren : ElementBody → List ElementId
  | .container children => children
  | _ => []

/-- A container's ordered children; a leaf or an absent element has none. -/
def childrenOf (store : ContentStore) (element : ElementId) : List ElementId :=
  match elementAt store element with
  | some record => bodyChildren record.body
  | none => []

/-- The root element of the cell's document, if the cell holds one. -/
def rootOf (store : ContentStore) (document : DocumentId) : Option ElementId :=
  (Hyperdocument.lookup store .documents document).map DocumentRecord.rootElement

/-- A line's leaf element carries its atom's identifier. -/
def atomElement (atom : AtomId) : ElementId := ⟨atom.digest⟩

/-- A transclusion's `embed` leaf carries the transclusion's identifier. -/
def transclusionElement (transclusion : TransclusionId) : ElementId := ⟨transclusion.digest⟩

/-- A container with new children, stamped with the operation that moved them. -/
def withChildren (record : ElementRecord) (children : List ElementId) (operation : OperationId) :
    ElementRecord :=
  { record with body := .container children, revision := operation }

/-- Rewrite one present element, guarded by its exact current record. -/
def rewriteElement (progress : Progress) (element : ElementId) (after : ElementRecord) :
    Except Reject Progress :=
  match elementAt progress.1 element with
  | none => .error .noSuchElement
  | some before => .ok (progress.1.set ⟨.elements, element⟩ (some after),
      progress.2 ++ [.write .elements element before after])

/-- Give one present element a new parent (`none`: detached), keeping the rest
of its current record. -/
def reparent (progress : Progress) (element : ElementId) (parent : Option ElementId) :
    Except Reject Progress :=
  match elementAt progress.1 element with
  | none => .error .noSuchElement
  | some before => .ok (progress.1.set ⟨.elements, element⟩ (some { before with parent := parent }),
      progress.2 ++ [.write .elements element before { before with parent := parent }])

/-- The container `element` of this document, whose children its editor read at
`revision`.  A container already moved by an earlier action of this same
operation is current for it: that action was itself checked. -/
def openContainer (store : ContentStore) (document : DocumentId) (element : ElementId)
    (revision operation : OperationId) : Except Reject (ElementRecord × List ElementId) :=
  match elementAt store element with
  | none => .error .noSuchElement
  | some record =>
      if record.document ≠ document then .error .noSuchElement
      else match record.body with
        | .container children =>
            if record.revision = revision ∨ record.revision = operation then .ok (record, children)
            else .error .staleElement
        | _ => .error .notAContainer

/-- The leaf record an append allocates. -/
def leafRecord (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (parent : ElementId) (body : ElementBody) : ElementRecord :=
  ⟨document, some parent, body, author, operation, operation, none⟩

/-- Append a new leaf to the document's root.  An append moves no existing
child, so the root's revision stays as it was: an edit naming a position
computed before the append still means the same position.  A cell holding no
document has no tree, so there the leaf is not created. -/
def appendLeaf (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (progress : Progress) (leaf : ElementId) (body : ElementBody) : Except Reject Progress :=
  match rootOf progress.1 document with
  | none => .ok progress
  | some root =>
      match elementAt progress.1 root with
      | none => .error .noSuchElement
      | some record =>
          match record.body with
          | .container children => do
              let next ← rewriteElement progress root
                { record with body := .container (children ++ [leaf]) }
              allocate next .elements leaf (leafRecord author operation document root body)
          | _ => .error .notAContainer

/-- `true` when the ancestors of `element`, walked up within `fuel` steps, reach
the top without meeting `child`; `false` when they meet it or the fuel runs out. -/
def clearOf : Nat → ContentStore → ElementId → ElementId → Bool
  | 0, _, _, _ => false
  | fuel + 1, store, element, child =>
      decide (element ≠ child) && match parentOf store element with
        | none => true
        | some parent => clearOf fuel store parent child

/-- How many element records the store holds.  The tree walk's fuel is counted
in elements only, so a write outside the elements namespace (a mark, a link,
an annotation) never changes how the order is computed. -/
def elementCount (store : ContentStore) : Nat :=
  (store.support.filter fun address => address.1 = .elements).card

/-- Fuel for a walk over the tree: one more than the number of stored elements. -/
def treeFuel (store : ContentStore) : Nat := elementCount store + 1

def editElementStep (operation : OperationId) (document : DocumentId) (progress : Progress)
    (edit : EditElement) : Except Reject Progress := do
  let (record, children) ← openContainer progress.1 document edit.element edit.revision operation
  match edit.op with
  | .splice index child =>
      if index ≤ children.length then
        match elementAt progress.1 child with
        | none => .error .noSuchElement
        | some childRecord =>
            if childRecord.document ≠ document then .error .noSuchElement
            else if childRecord.parent.isSome || decide (rootOf progress.1 document = some child) then
              .error .attached
            else if clearOf (treeFuel progress.1) progress.1 edit.element child then do
              let next ← rewriteElement progress edit.element
                (withChildren record (children.insertIdx index child) operation)
              reparent next child (some edit.element)
            else .error .cycle
      else .error .indexOutOfRange
  | .move child index =>
      if child ∈ children then
        if index < children.length then
          rewriteElement progress edit.element
            (withChildren record ((children.erase child).insertIdx index child) operation)
        else .error .indexOutOfRange
      else .error .notAChild
  | .remove child =>
      if child ∈ children then do
        let next ← rewriteElement progress edit.element
          (withChildren record (children.erase child) operation)
        reparent next child none
      else .error .notAChild

/-- The pre-order walk from `element`, `fuel` levels deep. -/
def walk : Nat → ContentStore → ElementId → List ElementId
  | 0, _, _ => []
  | fuel + 1, store, element => element :: (childrenOf store element).flatMap (walk fuel store)

/-- Document order: the pre-order walk of the tree below the document's root.
This is the canonical line order; a client renders its leaves and never sorts. -/
def documentOrder (store : ContentStore) (document : DocumentId) : List ElementId :=
  match rootOf store document with
  | none => []
  | some root => (walk (treeFuel store) store root).tail

/-! ## Marks: laid on a line or element at a read revision, in the annotations field -/

/-- The revision `target` stands at, when it is an atom or element of `document`. -/
def markTargetRevision (store : ContentStore) (document : DocumentId) :
    MarkTarget → Option OperationId
  | .atom atom =>
      match Hyperdocument.lookup store .atoms atom with
      | some record => if record.document = document then some record.revision else none
      | none => none
  | .element element =>
      match elementAt store element with
      | some record => if record.document = document then some record.revision else none
      | none => none

def MarkTarget.anchor : MarkTarget → OperationId → MarkAnchor
  | .atom line, revision => .atom line revision
  | .element target, revision => .element target revision

/-- The link relation of a link mark's link record. -/
def markRelation : Digest := contentDigest "DREGG/CONTENT/RELATION" "mark".toUTF8.toList

def markRecordOf (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (request : MarkRequest) : MarkRecord :=
  ⟨document, request.target.anchor request.revision, request.spec.kind, author, operation,
    cellReaders, none⟩

/-- A link mark's link: an ordinary forward link of the document, with no
source range (its place on the line is the mark's anchor). -/
def markLinkRecord (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (target : LinkTarget) : LinkRecord :=
  ⟨document, none, target, markRelation, author, operation, none⟩

def markLinkStep (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (progress : Progress) : MarkSpec → Except Reject Progress
  | .link link target => allocate progress .links link (markLinkRecord author operation document target)
  | _ => .ok progress

/-- The target is an atom or element of this document, still at the revision
the marker read; a revision equal to this operation names an unread write of
this same command and is stale too. -/
def markStep (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (progress : Progress) (mark : MarkId) (request : MarkRequest) : Except Reject Progress :=
  match markTargetRevision progress.1 document request.target with
  | none => .error .noSuchTarget
  | some current =>
      if current = request.revision ∧ request.revision ≠ operation then do
        let next ← allocate progress .marks mark (markRecordOf author operation document request)
        markLinkStep author operation document next request.spec
      else .error .staleMark

/-- The principal that created `document`. -/
def documentOwner (store : ContentStore) (document : DocumentId) : Option PrincipalRef :=
  (Hyperdocument.lookup store .documents document).map DocumentRecord.createdBy

/-- Is the link already retired (by an `unlink` of it)? -/
def linkRetired (store : ContentStore) (link : LinkId) : Bool :=
  match Hyperdocument.lookup store .links link with
  | some record => record.tombstonedAt.isSome
  | none => false

/-- A link mark's link leaves with the mark (unless an `unlink` already retired it). -/
def retireMarkLink (document : DocumentId) (operation : OperationId) (progress : Progress) :
    MarkKind → Except Reject Progress
  | .link link =>
      if linkRetired progress.1 link then .ok progress
      else retireLink document operation progress link
  | _ => .ok progress

/-- Retire a live mark of `document`: the exact stored record guards the
write and only `tombstonedAt` changes.  Only the mark's author or the
document's owner may. -/
def unmarkStep (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (progress : Progress) (mark : MarkId) : Except Reject Progress :=
  match (show Option MarkRecord from progress.1 ⟨.marks, mark⟩) with
  | none => .error .markNotFound
  | some before =>
      if before.document = document ∧ before.tombstonedAt = none then
        if author = before.author ∨ documentOwner progress.1 document = some author then
          retireMarkLink document operation
            (progress.1.set ⟨.marks, mark⟩ (some { before with tombstonedAt := some operation }),
              progress.2 ++ [.write .marks mark before { before with tombstonedAt := some operation }])
            before.kind
        else .error .notMarkOwner
      else .error .markNotFound

/-- A mark is fresh while its target still stands at the anchored revision (a
range mark: while its endpoints are stored in its document).  A stale mark is
shown struck, never re-anchored. -/
def markFresh (store : ContentStore) (record : MarkRecord) : Bool :=
  match record.anchor with
  | .atom atom revision => decide (markTargetRevision store record.document (.atom atom) = some revision)
  | .element element revision =>
      decide (markTargetRevision store record.document (.element element) = some revision)
  | .range range => rangeCheck store record.document range

def step (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (context : Context) (progress : Progress) : Action → Except Reject Progress
  | .createDocument root schema => do
      let next ← allocate progress .documents document ⟨root, schema, author, operation⟩
      allocate next .elements root ⟨document, none, .container [], author, operation, operation, none⟩
  | .createAtom atom kind payload =>
      if kind.validPayload payload then do
        let next ← allocate progress .atoms atom
          ⟨document, kind.authored author operation, payload, author, operation, operation, none⟩
        appendLeaf author operation document next (atomElement atom) (.atom atom)
      else .error .invalidPatch
  | .editAtom edit =>
      if (sourceEditAtomRecord author operation edit).kind.validPayload
          (sourceEditAtomRecord author operation edit).payload then
        replaceAtom document progress edit.atomId edit.before (sourceEditAtomRecord author operation edit)
      else .error .invalidPatch
  | .rewrapAtom atom before wrapping => rewrapAtom author operation document progress atom before wrapping
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
  | .rewrapAnnotation annotation before wrapping =>
      rewrapAnnotation author operation document progress annotation before wrapping
  | .transclude transclusion link request =>
      match context.sourceRead request.source with
      | none => .error .sourceNotCovered
      | some read => do
          let payload := transcludePayload document transclusion link request context.height read
          let next ← allocate progress .transclusions transclusion
            (transclusionRecord operation author payload)
          let next ← allocate next .links link (transclusionForwardLink operation author payload)
          appendLeaf author operation document next (transclusionElement transclusion)
            (.embed transclusion)
  | .editElement edit => editElementStep operation document progress edit
  | .createContainer element =>
      match rootOf progress.1 document with
      | none => .error .noSuchElement
      | some _ => appendLeaf author operation document progress element (.container [])
  | .unlink link => retireLink document operation progress link
  | .mark mark request => markStep author operation document progress mark request
  | .unmark mark => unmarkStep author operation document progress mark

def run (author : PrincipalRef) (operation : OperationId) (document : DocumentId) (context : Context)
    (pre : ContentStore) (command : Command) : Except Reject Progress :=
  command.actions.foldlM (step author operation document context) (pre, [])

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


theorem bind_eq_ok {α β : Type} {x : Except Reject α} {f : α → Except Reject β} {b : β}
    (accepted : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error reason => simp [bind, Except.bind] at accepted
  | ok a => exact ⟨a, rfl, accepted⟩

theorem allocate_ok {progress next : Progress} {space : Namespace} {key : Key space}
    {value : Value space} (accepted : allocate progress space key value = .ok next) :
    progress.1 ⟨space, key⟩ = none ∧
      next = (progress.1.set ⟨space, key⟩ (some value), progress.2 ++ [.allocate space key value]) := by
  unfold allocate at accepted
  split at accepted
  · rename_i fresh
    cases accepted
    exact ⟨fresh, rfl⟩
  · cases accepted

theorem rewriteElement_ok {progress next : Progress} {element : ElementId} {after : ElementRecord}
    (accepted : rewriteElement progress element after = .ok next) :
    ∃ before, elementAt progress.1 element = some before ∧
      next = (progress.1.set ⟨.elements, element⟩ (some after),
        progress.2 ++ [.write .elements element before after]) := by
  unfold rewriteElement at accepted
  split at accepted
  · cases accepted
  · rename_i before found
    cases accepted
    exact ⟨before, found, rfl⟩

/-- `next` extends `progress` by guarded writes and allocations of elements only. -/
def ElementStep (progress next : Progress) : Prop :=
  (∀ pre, Executes pre progress → Executes pre next) ∧
    ∀ address : Hyperdocument.Address, address.1 ≠ .elements → next.1 address = progress.1 address

theorem ElementStep.refl (progress : Progress) : ElementStep progress progress :=
  ⟨fun _ holds => holds, fun _ _ => rfl⟩

theorem ElementStep.trans {first second third : Progress}
    (left : ElementStep first second) (right : ElementStep second third) :
    ElementStep first third :=
  ⟨fun pre holds => right.1 pre (left.1 pre holds),
    fun address other => (right.2 address other).trans (left.2 address other)⟩

theorem allocate_element_step {progress next : Progress} {key : ElementId} {value : ElementRecord}
    (accepted : allocate progress .elements key value = .ok next) : ElementStep progress next := by
  refine ⟨fun pre holds => allocate_executes pre progress next _ _ _ holds accepted, ?_⟩
  obtain ⟨_, rfl⟩ := allocate_ok accepted
  intro address other
  exact Store.Store.set_ne _ _ _ address (fun same => other (congrArg Sigma.fst same))

theorem rewriteElement_step {progress next : Progress} {element : ElementId} {after : ElementRecord}
    (accepted : rewriteElement progress element after = .ok next) : ElementStep progress next := by
  obtain ⟨before, found, rfl⟩ := rewriteElement_ok accepted
  refine ⟨fun pre holds => executes_append pre progress (.write .elements element before after)
    holds ⟨rfl, found⟩, ?_⟩
  intro address other
  exact Store.Store.set_ne _ _ _ address (fun same => other (congrArg Sigma.fst same))

theorem reparent_ok {progress next : Progress} {element : ElementId} {parent : Option ElementId}
    (accepted : reparent progress element parent = .ok next) :
    ∃ before, elementAt progress.1 element = some before ∧
      next = (progress.1.set ⟨.elements, element⟩ (some { before with parent := parent }),
        progress.2 ++ [.write .elements element before { before with parent := parent }]) := by
  unfold reparent at accepted
  split at accepted
  · cases accepted
  · rename_i before found
    cases accepted
    exact ⟨before, found, rfl⟩

theorem reparent_step {progress next : Progress} {element : ElementId} {parent : Option ElementId}
    (accepted : reparent progress element parent = .ok next) : ElementStep progress next := by
  obtain ⟨before, found, rfl⟩ := reparent_ok accepted
  refine ⟨fun pre holds => executes_append pre progress
    (.write .elements element before { before with parent := parent }) holds ⟨rfl, found⟩, ?_⟩
  intro address other
  exact Store.Store.set_ne _ _ _ address (fun same => other (congrArg Sigma.fst same))

theorem appendLeaf_step (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    {progress next : Progress} {leaf : ElementId} {body : ElementBody}
    (accepted : appendLeaf author operation document progress leaf body = .ok next) :
    ElementStep progress next := by
  unfold appendLeaf at accepted
  split at accepted
  · cases accepted
    exact ElementStep.refl _
  · split at accepted
    · cases accepted
    · split at accepted
      · obtain ⟨middle, first, rest⟩ := bind_eq_ok accepted
        exact (rewriteElement_step first).trans (allocate_element_step rest)
      · cases accepted

theorem openContainer_ok {store : ContentStore} {document : DocumentId} {element : ElementId}
    {revision operation : OperationId} {record : ElementRecord} {children : List ElementId}
    (opened : openContainer store document element revision operation = .ok (record, children)) :
    elementAt store element = some record ∧ record.document = document ∧
      record.body = .container children ∧ (record.revision = revision ∨ record.revision = operation) := by
  unfold openContainer at opened
  split at opened
  · cases opened
  · rename_i found
    split at opened
    · cases opened
    · rename_i local_
      split at opened
      · rename_i list body
        split at opened
        · rename_i current
          cases opened
          exact ⟨found, not_not.mp local_, body, current⟩
        · cases opened
      · cases opened

theorem editElementStep_step (operation : OperationId) (document : DocumentId)
    {progress next : Progress} {edit : EditElement}
    (accepted : editElementStep operation document progress edit = .ok next) :
    ElementStep progress next := by
  unfold editElementStep at accepted
  obtain ⟨⟨record, children⟩, _, rest⟩ := bind_eq_ok accepted
  cases operation_ : edit.op with
  | splice index child =>
      simp only [operation_] at rest
      split at rest
      · split at rest
        · cases rest
        · split at rest
          · cases rest
          · split at rest
            · cases rest
            · split at rest
              · obtain ⟨middle, first, last⟩ := bind_eq_ok rest
                exact (rewriteElement_step first).trans (reparent_step last)
              · cases rest
      · cases rest
  | move child index =>
      simp only [operation_] at rest
      split at rest
      · split at rest
        · exact rewriteElement_step rest
        · cases rest
      · cases rest
  | remove child =>
      simp only [operation_] at rest
      split at rest
      · obtain ⟨middle, first, last⟩ := bind_eq_ok rest
        exact (rewriteElement_step first).trans (reparent_step last)
      · cases rest

/-! ### Mark steps: they write only marks and links -/

/-- A step whose writes are confined to the marks and links namespaces and
which executes as emitted. -/
def MarkStep (progress next : Progress) : Prop :=
  (∀ pre, Executes pre progress → Executes pre next) ∧
    ∀ address : Hyperdocument.Address, address.1 ≠ .marks → address.1 ≠ .links →
      next.1 address = progress.1 address

theorem MarkStep.refl (progress : Progress) : MarkStep progress progress :=
  ⟨fun _ holds => holds, fun _ _ _ => rfl⟩

theorem MarkStep.trans {first second third : Progress}
    (left : MarkStep first second) (right : MarkStep second third) : MarkStep first third :=
  ⟨fun pre holds => right.1 pre (left.1 pre holds),
    fun address notMarks notLinks =>
      (right.2 address notMarks notLinks).trans (left.2 address notMarks notLinks)⟩

theorem allocate_markStep {progress next : Progress} {space : Namespace} {key : Key space}
    {value : Value space} (inside : space = .marks ∨ space = .links)
    (accepted : allocate progress space key value = .ok next) : MarkStep progress next := by
  refine ⟨fun pre holds => allocate_executes pre progress next _ _ _ holds accepted, ?_⟩
  obtain ⟨_, rfl⟩ := allocate_ok accepted
  intro address notMarks notLinks
  refine Store.Store.set_ne _ _ _ address (fun same => ?_)
  have first := congrArg Sigma.fst same
  rcases inside with rfl | rfl
  · exact notMarks first
  · exact notLinks first

theorem retireLink_ok {document : DocumentId} {operation : OperationId} {progress next : Progress}
    {link : LinkId} (accepted : retireLink document operation progress link = .ok next) :
    ∃ before, (show Option LinkRecord from progress.1 ⟨.links, link⟩) = some before ∧
      before.sourceDocument = document ∧ before.tombstonedAt = none ∧
      next = (progress.1.set ⟨.links, link⟩ (some { before with tombstonedAt := some operation }),
        progress.2 ++ [.write .links link before { before with tombstonedAt := some operation }]) := by
  unfold retireLink at accepted
  split at accepted
  · cases accepted
  · rename_i before present
    split at accepted
    · rename_i live
      cases accepted
      exact ⟨before, present, live.1, live.2, rfl⟩
    · cases accepted

theorem retireLink_markStep {document : DocumentId} {operation : OperationId}
    {progress next : Progress} {link : LinkId}
    (accepted : retireLink document operation progress link = .ok next) : MarkStep progress next := by
  obtain ⟨before, present, _, _, rfl⟩ := retireLink_ok accepted
  refine ⟨fun pre holds => executes_append pre progress _ holds ⟨rfl, present⟩, ?_⟩
  intro address _ notLinks
  exact Store.Store.set_ne _ _ _ address (fun same => notLinks (congrArg Sigma.fst same))

theorem markLinkStep_markStep {author : PrincipalRef} {operation : OperationId}
    {document : DocumentId} {progress next : Progress} {spec : MarkSpec}
    (accepted : markLinkStep author operation document progress spec = .ok next) :
    MarkStep progress next := by
  cases spec with
  | link link target => exact allocate_markStep (Or.inr rfl) accepted
  | bold | italic | code | heading =>
      simp only [markLinkStep, Except.ok.injEq] at accepted
      subst accepted
      exact MarkStep.refl _

theorem markStep_ok {author : PrincipalRef} {operation : OperationId} {document : DocumentId}
    {progress next : Progress} {mark : MarkId} {request : MarkRequest}
    (accepted : markStep author operation document progress mark request = .ok next) :
    markTargetRevision progress.1 document request.target = some request.revision ∧
      request.revision ≠ operation ∧
      ∃ middle, allocate progress .marks mark (markRecordOf author operation document request) =
          .ok middle ∧ markLinkStep author operation document middle request.spec = .ok next := by
  unfold markStep at accepted
  split at accepted
  · cases accepted
  · rename_i current found
    split at accepted
    · rename_i fresh
      obtain ⟨middle, first, rest⟩ := bind_eq_ok accepted
      exact ⟨fresh.1 ▸ found, fresh.2, middle, first, rest⟩
    · cases accepted

theorem markStep_markStep {author : PrincipalRef} {operation : OperationId} {document : DocumentId}
    {progress next : Progress} {mark : MarkId} {request : MarkRequest}
    (accepted : markStep author operation document progress mark request = .ok next) :
    MarkStep progress next := by
  obtain ⟨_, _, middle, first, rest⟩ := markStep_ok accepted
  exact (allocate_markStep (Or.inl rfl) first).trans (markLinkStep_markStep rest)

theorem retireMarkLink_markStep {document : DocumentId} {operation : OperationId}
    {progress next : Progress} {kind : MarkKind}
    (accepted : retireMarkLink document operation progress kind = .ok next) :
    MarkStep progress next := by
  cases kind with
  | link link =>
      simp only [retireMarkLink] at accepted
      split at accepted
      · cases accepted
        exact MarkStep.refl _
      · exact retireLink_markStep accepted
  | bold | italic | code | heading =>
      simp only [retireMarkLink, Except.ok.injEq] at accepted
      subst accepted
      exact MarkStep.refl _

theorem unmarkStep_ok {author : PrincipalRef} {operation : OperationId} {document : DocumentId}
    {progress next : Progress} {mark : MarkId}
    (accepted : unmarkStep author operation document progress mark = .ok next) :
    ∃ before, (show Option MarkRecord from progress.1 ⟨.marks, mark⟩) = some before ∧
      before.document = document ∧ before.tombstonedAt = none ∧
      (author = before.author ∨ documentOwner progress.1 document = some author) ∧
      retireMarkLink document operation
        (progress.1.set ⟨.marks, mark⟩ (some { before with tombstonedAt := some operation }),
          progress.2 ++ [.write .marks mark before { before with tombstonedAt := some operation }])
        before.kind = .ok next := by
  unfold unmarkStep at accepted
  split at accepted
  · cases accepted
  · rename_i before present
    split at accepted
    · rename_i live
      split at accepted
      · rename_i may
        exact ⟨before, present, live.1, live.2, may, accepted⟩
      · cases accepted
    · cases accepted

theorem unmarkStep_markStep {author : PrincipalRef} {operation : OperationId}
    {document : DocumentId} {progress next : Progress} {mark : MarkId}
    (accepted : unmarkStep author operation document progress mark = .ok next) :
    MarkStep progress next := by
  obtain ⟨before, present, _, _, _, rest⟩ := unmarkStep_ok accepted
  have first : MarkStep progress
      (progress.1.set ⟨.marks, mark⟩ (some { before with tombstonedAt := some operation }),
        progress.2 ++ [.write .marks mark before { before with tombstonedAt := some operation }]) := by
    refine ⟨fun pre holds => executes_append pre progress _ holds ⟨rfl, present⟩, ?_⟩
    intro address notMarks _
    exact Store.Store.set_ne _ _ _ address (fun same => notMarks (congrArg Sigma.fst same))
  exact first.trans (retireMarkLink_markStep rest)


/-- A raw request cannot hide a second body beside a typed sealed fragment. -/
theorem createAtom_sealed_nonempty_refused (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) (progress : Progress) (atom : AtomId)
    (schema : Digest) (fragment : AuthoredFragment) (byte : UInt8) (rest : List UInt8) :
    step author operation document context progress
      (.createAtom atom (.sealedObject schema fragment) (byte :: rest)) = .error .invalidPatch := rfl

theorem step_executes (author : PrincipalRef) (operation : OperationId) (document : DocumentId) (context : Context)
    (pre : ContentStore) (progress next : Progress) (action : Action)
    (holds : Executes pre progress)
    (accepted : step author operation document context progress action = .ok next) :
    Executes pre next := by
  cases action with
  | createDocument root schema =>
      simp only [step] at accepted
      obtain ⟨middle, first, rest⟩ := bind_eq_ok accepted
      exact allocate_executes pre middle next _ _ _
        (allocate_executes pre progress middle _ _ _ holds first) rest
  | createAtom atom kind payload =>
      simp only [step] at accepted
      split at accepted
      · obtain ⟨middle, first, rest⟩ := bind_eq_ok accepted
        exact (appendLeaf_step author operation document rest).1 pre
          (allocate_executes pre progress middle _ _ _ holds first)
      · cases accepted
  | editAtom edit =>
      simp only [step] at accepted
      split at accepted
      · exact replaceAtom_executes pre document progress next _ _ _ holds accepted
      · cases accepted
  | rewrapAtom atom before wrapping =>
      simp only [step, rewrapAtom] at accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted
        · rename_i present
          cases shape : before.kind with
          | text => simp [shape] at accepted
          | inlineObject schema => simp [shape] at accepted
          | sealedObject schema fragment =>
              simp only [shape] at accepted
              cases accepted
              exact executes_append pre progress _ holds ⟨rfl, not_not.mp present⟩
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
  | rewrapAnnotation annotation before wrapping =>
      simp only [step, rewrapAnnotation] at accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted
        · rename_i present
          cases shape : before.body with
          | inline bytes => simp [shape] at accepted
          | reference source => simp [shape] at accepted
          | sealed fragment =>
              simp only [shape] at accepted
              cases accepted
              exact executes_append pre progress _ holds ⟨rfl, not_not.mp present⟩
  | transclude transclusion link request =>
      cases covered : context.sourceRead request.source with
      | none => simp [step, covered] at accepted
      | some read =>
          simp only [step, covered] at accepted
          obtain ⟨first, firstOk, rest⟩ := bind_eq_ok accepted
          obtain ⟨second, secondOk, last⟩ := bind_eq_ok rest
          exact (appendLeaf_step author operation document last).1 pre
            (allocate_executes pre first second _ _ _
              (allocate_executes pre progress first _ _ _ holds firstOk) secondOk)
  | editElement edit =>
      exact (editElementStep_step operation document accepted).1 pre holds
  | createContainer element =>
      simp only [step] at accepted
      split at accepted
      · cases accepted
      · exact (appendLeaf_step author operation document accepted).1 pre holds
  | unlink link =>
      simp only [step, retireLink] at accepted
      split at accepted
      · cases accepted
      · rename_i before present
        split at accepted
        · cases accepted
          exact executes_append pre progress _ holds ⟨rfl, present⟩
        · cases accepted
  | mark mark request =>
      simp only [step] at accepted
      exact (markStep_markStep accepted).1 pre holds
  | unmark mark =>
      simp only [step] at accepted
      exact (unmarkStep_markStep accepted).1 pre holds

theorem foldlM_executes (author : PrincipalRef) (operation : OperationId) (document : DocumentId) (context : Context)
    (pre : ContentStore) (actions : List Action) (progress next : Progress)
    (holds : Executes pre progress)
    (accepted : actions.foldlM (step author operation document context) progress = .ok next) :
    Executes pre next := by
  induction actions generalizing progress with
  | nil =>
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at accepted
      exact accepted ▸ holds
  | cons action rest induction =>
      simp only [List.foldlM_cons, bind, Except.bind] at accepted
      cases stepped : step author operation document context progress action with
      | error reason => simp [stepped] at accepted
      | ok middle =>
          simp only [stepped] at accepted
          exact induction middle
            (step_executes author operation document context pre progress middle action holds stepped)
            accepted

/-- An accepted run emits a patch valid at `pre` whose run is its post. -/
theorem run_executes (author : PrincipalRef) (operation : OperationId) (document : DocumentId) (context : Context)
    (pre : ContentStore) (command : Command) (next : Progress)
    (accepted : run author operation document context pre command = .ok next) :
    Patch.ValidFrom pre next.2 ∧ Patch.run pre next.2 = next.1 :=
  foldlM_executes author operation document context pre command.actions (pre, []) next
    ⟨trivial, rfl⟩ accepted

theorem accepted_link_source_stored (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) (progress next : Progress) (linkId : LinkId)
    (source : StableRange) (target : LinkTarget) (relation : Digest)
    (accepted : step author operation document context progress
      (.link linkId (some source) target relation) = .ok next) :
    StoredRangeValidAt progress.1 document source := by
  by_cases checked : rangeCheck progress.1 document source = true
  · exact rangeCheck_sound progress.1 document source checked
  · simp [step, checked] at accepted

/-! ## Preparation on the cell -/

structure PreparedCell (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) (pre : ContentCell) (command : Command) where
  private mk ::
  progress : Progress
  nonempty : command.actions ≠ []
  computed : run author operation document context pre.logical command = .ok progress
  validated : ValidatedPatch HyperdocumentCell.contentMaterializer pre pre.root progress.2

def PreparedCell.post {author : PrincipalRef} {operation : OperationId} {document : DocumentId} {context : Context}
    {pre : ContentCell} {command : Command}
    (prepared : PreparedCell author operation document context pre command) : ContentCell :=
  prepared.validated.apply

/-- The validated post is exactly the store the action run computed. -/
theorem PreparedCell.post_exact {author : PrincipalRef} {operation : OperationId}
    {document : DocumentId} {context : Context} {pre : ContentCell} {command : Command}
    (prepared : PreparedCell author operation document context pre command) :
    prepared.post.logical = prepared.progress.1 :=
  (run_executes author operation document context pre.logical command _ prepared.computed).2

def prepareCell (author : PrincipalRef) (operation : OperationId) (document : DocumentId) (context : Context)
    (pre : ContentCell) (command : Command) :
    Except Reject (PreparedCell author operation document context pre command) :=
  if nonempty : command.actions ≠ [] then
    match computed : run author operation document context pre.logical command with
    | .error reason => .error reason
    | .ok progress =>
        match validate HyperdocumentCell.contentMaterializer pre pre.root progress.2 with
        | .rejected _ => .error .invalidPatch
        | .accepted validated => .ok ⟨progress, nonempty, computed, validated⟩
  else .error .emptyActions

/-- Completeness: an accepted run always validates at the cell's own root, so
`invalidPatch` is unreachable for commands the lowering accepts. -/
theorem prepareCell_ok_of_run (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) (pre : ContentCell) (command : Command) (progress : Progress)
    (nonempty : command.actions ≠ [])
    (computed : run author operation document context pre.logical command = .ok progress) :
    ∃ prepared, prepareCell author operation document context pre command = .ok prepared := by
  obtain ⟨validated, accepted⟩ := validate_accepts HyperdocumentCell.contentMaterializer pre
    pre.root progress.2 rfl (run_executes author operation document context _ command progress computed).1
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
    (document : DocumentId) (context : Context) (pre : ContentCell) :
    prepareCell author operation document context pre ⟨[]⟩ = .error .emptyActions := by
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
      | some record => match record.kind with
          | .sealedObject _ fragment => fragment.ciphertext.length + fragment.wrapping.length
          | _ => record.payload.length
      | none => 0
  | ⟨.elements, element⟩ =>
      match Hyperdocument.lookup store .elements element with
      | some ⟨_, _, .opaque _ payload, _, _, _, _⟩ => payload.length
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
  | .transclude .. => 6
  | .editElement .. => 7
  | .createContainer .. => 8
  | .unlink .. => 9
  | .mark .. => 10
  | .unmark .. => 11
  | .rewrapAnnotation .. => 12
  | .rewrapAtom .. => 13

def actionCount (command : Command) (tag : Nat) : Nat :=
  (command.actions.filter (fun action => action.tag == tag)).length

/-- The atom identifiers a command creates or edits, in command order. -/
def touchedAtoms (command : Command) : List Nat :=
  command.actions.filterMap fun action => match action with
    | .createAtom atom _ _ => some atom.digest.value
    | .editAtom edit => some edit.atomId.digest.value
    | .rewrapAtom atom .. => some atom.digest.value
    | _ => none

/-- The least / greatest of `f` over the touched atom identifiers; `-1` when the
command touches no atom (an identifier is a natural, so `-1` names none). -/
def touchedMin (f : Nat → Nat) (command : Command) : Int :=
  match touchedAtoms command with
  | [] => -1
  | first :: rest => ((rest.map f).foldl min (f first) : Nat)

def touchedMax (f : Nat → Nat) (command : Command) : Int :=
  match touchedAtoms command with
  | [] => -1
  | first :: rest => ((rest.map f).foldl max (f first) : Nat)

/-- An atom identifier's high and low 64-bit halves.  A law that partitions a
cell's atoms by identifier (a private room's keys cell: wraps above, each
member's own encryption-key record at its subject number below 2^64) reads the
range of the halves a write touches. -/
def atomHigh (id : Nat) : Nat := id / 2 ^ 64
def atomLow (id : Nat) : Nat := id % 2 ^ 64

/-- The store a content law sees: the cell without its hiding key, so every
count and byte measure is of content alone. -/
def lawStore (store : ContentStore) : ContentStore :=
  Minidregg.Theory.Store.Store.set store ⟨.blinding, ()⟩ none

/-- The reserved external-link scheme for room-index names. Names remain actual
bytes in ordinary hyperdocument links; neither a local hint nor a hash of a name
is a namespace binding. -/
def sharedNameScheme : List UInt8 := "mini-name".toUTF8.toList

/-- A live shared name at one link slot; all other content is irrelevant. -/
def sharedNameAt (store : ContentStore) : Store.Address Hyperdocument.layout → Option (List UInt8)
  | ⟨.links, link⟩ =>
      match Hyperdocument.lookup store .links link with
      | some record =>
          match record.target with
          | .external scheme name _ =>
              if scheme = sharedNameScheme ∧ record.tombstonedAt = none then some name else none
          | _ => none
      | none => none
  | _ => none

/-- Names are unique across the whole final cell, including two links created
in one command. Retired links do not reserve names forever; atomic unlink/link
can rename or replace a binding. This is a law-visible property, not a rule
imposed on every document. -/
def sharedNames (store : ContentStore) : List (List UInt8) :=
  (StoreCodec.sortedSupport HyperdocumentCell.contentWire store).filterMap (sharedNameAt store)

def sharedNamesUnique (store : ContentStore) : Bool :=
  decide (sharedNames store).Nodup

theorem sharedNamesUnique_iff (store : ContentStore) :
    sharedNamesUnique store = true ↔ (sharedNames store).Nodup := by
  simp [sharedNamesUnique]

/-- Source-derived policy inputs count actual committed bytes; no content or
identity is reduced to a scalar identifier. -/
def project (before' after' : ContentStore) (command : Command) : List (String × Int) :=
  let before := lawStore before'
  let after := lawStore after'
  [("content/names/unique", if sharedNamesUnique after then 1 else 0),
   ("content/bytes/before", contentBytes before),
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
   ("content/transclusions", actionCount command 6),
   ("content/element-edits", actionCount command 7),
   ("content/container-creates", actionCount command 8),
   ("content/unlinks", actionCount command 9),
   ("content/marks", actionCount command 10),
   ("content/unmarks", actionCount command 11),
   ("content/writes/body", bodyWrites before after),
   ("content/writes/annotations", annotationWrites before after),
   ("content/tombstones", (command.actions.filter fun action => match action with
      | .editAtom edit => edit.tombstone
      | _ => false).length),
   ("content/atoms/high-min", touchedMin atomHigh command),
   ("content/atoms/high-max", touchedMax atomHigh command),
   ("content/atoms/low-min", touchedMin atomLow command),
   ("content/atoms/low-max", touchedMax atomLow command)]

/-- Maintenance requires the exact complete prior record and preserves every
original provenance field and immutable ciphertext. Only key custody changes. -/
theorem rewrapAnnotation_guarded_post (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (progress next : Progress) (annotation : AnnotationId)
    (before : AnnotationRecord) (wrapping : List UInt8)
    (accepted : rewrapAnnotation author operation document progress annotation before wrapping = .ok next) :
    progress.1 ⟨.annotations, annotation⟩ = some before ∧
      ∃ fragment, before.body = .sealed fragment ∧
        next = (progress.1.set ⟨.annotations, annotation⟩
          (some { before with body := .sealed (fragment.rewrapped author operation wrapping) }),
          progress.2 ++ [.write .annotations annotation before
            { before with body := .sealed (fragment.rewrapped author operation wrapping) }]) := by
  unfold rewrapAnnotation at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · rename_i present
      cases shape : before.body with
      | inline bytes => simp [shape] at accepted
      | reference source => simp [shape] at accepted
      | sealed fragment =>
          simp only [shape] at accepted
          cases accepted
          exact ⟨not_not.mp present, fragment, rfl, rfl⟩

theorem rewrapAnnotation_preserves_body (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (progress next : Progress) (annotation : AnnotationId)
    (before : AnnotationRecord) (wrapping : List UInt8)
    (accepted : rewrapAnnotation author operation document progress annotation before wrapping = .ok next)
    (address : Hyperdocument.Address) (outside : address.1 ≠ .annotations) :
    next.1 address = progress.1 address := by
  obtain ⟨_, fragment, _, post⟩ :=
    rewrapAnnotation_guarded_post author operation document progress next annotation before wrapping accepted
  rw [post]
  exact Store.Store.set_ne _ _ _ address (fun same => outside (congrArg Sigma.fst same))

/-- Exact prior record and byte-identical authored payload/origin. -/
theorem rewrapAtom_guarded_post (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (progress next : Progress) (atom : AtomId)
    (before : AtomRecord) (wrapping : List UInt8)
    (accepted : rewrapAtom author operation document progress atom before wrapping = .ok next) :
    progress.1 ⟨.atoms, atom⟩ = some before ∧
      ∃ schema fragment, before.kind = .sealedObject schema fragment ∧
        next = (progress.1.set ⟨.atoms, atom⟩
          (some { before with kind := .sealedObject schema (fragment.rewrapped author operation wrapping) }),
          progress.2 ++ [.write .atoms atom before
            { before with kind := .sealedObject schema (fragment.rewrapped author operation wrapping) }]) := by
  unfold rewrapAtom at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · rename_i present
      cases shape : before.kind with
      | text => simp [shape] at accepted
      | inlineObject schema => simp [shape] at accepted
      | sealedObject schema fragment =>
          simp only [shape] at accepted
          cases accepted
          exact ⟨not_not.mp present, schema, fragment, rfl, rfl⟩

/-- Authorization maintenance preserves the exact semantic revision used by
annotations, stable ranges and marks. -/
theorem rewrapAtom_preserves_revision (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (progress next : Progress) (atom : AtomId)
    (before : AtomRecord) (wrapping : List UInt8)
    (accepted : rewrapAtom author operation document progress atom before wrapping = .ok next) :
    ∃ after, next.1 ⟨.atoms, atom⟩ = some after ∧ after.revision = before.revision ∧
      after.payload = before.payload ∧ after.createdBy = before.createdBy ∧
      after.createdAt = before.createdAt ∧ after.tombstonedAt = before.tombstonedAt := by
  obtain ⟨_, schema, fragment, _, post⟩ :=
    rewrapAtom_guarded_post author operation document progress next atom before wrapping accepted
  rw [post]
  exact ⟨_, Store.Store.set_eq _ _ _, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Annotations: attached to a read revision, never touching the body -/

/-- An accepted annotate allocates exactly one annotation record and changes
no other address: every record outside the annotations namespace — atoms,
runs, elements, the document — is the record it was. -/
theorem annotate_preserves_body (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) (progress next : Progress) (annotationId : AnnotationId) (atom : AtomId)
    (revision : OperationId) (body : AnnotationBody)
    (accepted : step author operation document context progress (.annotate annotationId atom revision body) = .ok next)
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
    (document : DocumentId) (context : Context) (progress : Progress) (annotationId : AnnotationId) (atom : AtomId)
    (revision : OperationId) (body : AnnotationBody)
    (moved : ∀ record, Hyperdocument.lookup progress.1 .atoms atom = some record →
      record.revision ≠ revision) :
    step author operation document context progress (.annotate annotationId atom revision body) = .error .staleAtom := by
  have unchecked : pinCheck progress.1 document atom revision operation = false := by
    unfold pinCheck
    cases found : Hyperdocument.lookup progress.1 .atoms atom with
    | none => rfl
    | some record => simp [moved record found]
  simp [step, unchecked]

/-- Refuted pole: an atom at the named revision, written by an earlier
operation, is annotated. -/
theorem annotate_fresh_admitted (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) (progress : Progress) (annotationId : AnnotationId) (atom : AtomId)
    (record : AtomRecord) (body : AnnotationBody)
    (found : Hyperdocument.lookup progress.1 .atoms atom = some record)
    (local_ : record.document = document) (earlier : record.revision ≠ operation)
    (fresh : progress.1 ⟨.annotations, annotationId⟩ = none) :
    ∃ next, step author operation document context progress
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

theorem changedIn_empty_of_agree (field : Bool) (before after : ContentStore)
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
    (document : DocumentId) (context : Context) (actions : List Action) (progress next : Progress)
    (only : actions.all (fun action => action.tag == 5) = true)
    (accepted : actions.foldlM (step author operation document context) progress = .ok next)
    (address : Hyperdocument.Address) (outside : address.1 ≠ .annotations) :
    next.1 address = progress.1 address := by
  induction actions generalizing progress with
  | nil =>
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at accepted
      rw [accepted]
  | cons action rest induction =>
      simp only [List.all_cons, Bool.and_eq_true] at only
      simp only [List.foldlM_cons, bind, Except.bind] at accepted
      cases stepped : step author operation document context progress action with
      | error reason => simp [stepped] at accepted
      | ok middle =>
          simp only [stepped] at accepted
          rw [induction middle only.2 accepted]
          cases action with
          | annotate annotationId atom revision body =>
              exact annotate_preserves_body author operation document context progress middle
                annotationId atom revision body stepped address outside
          | _ => simp [Action.tag] at only

/-- An accepted annotate-only command changes no body record: the projected
`content/writes/body` is `0`, so a law (or a K-FIELDS scope naming only
`annotations`) that refuses body writes admits it. -/
theorem annotate_writes_no_body (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) (pre : ContentStore) (command : Command) (next : Progress)
    (only : command.annotateOnly = true)
    (accepted : run author operation document context pre command = .ok next) :
    bodyWrites pre next.1 = 0 := by
  unfold bodyWrites
  rw [changedIn_empty_of_agree false pre next.1]
  · rfl
  intro address body
  apply foldlM_annotate_frames author operation document context command.actions (pre, []) next only
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

/-! ## Ranges in the source, under endpoint death

A kernel run is an immutable list of atoms, and a tombstoned atom keeps its
slot, so the run is the committed neighbor order.  An endpoint names an atom
of one run and a side; if that atom is dead its declared policy decides: no
cut (`invalidate`), the dead slot itself (`keepTombstone`), or the nearest live
slot in the named direction of the committed run. -/

/-- A slot is live when its atom is present in the document and not tombstoned. -/
def slotLive (store : ContentStore) (document : DocumentId) (atom : AtomId) : Bool :=
  match Hyperdocument.lookup store .atoms atom with
  | some record => decide (record.document = document) && record.tombstonedAt.isNone
  | none => false

def cutAt (bias : AnchorBias) (position : Nat) : Nat :=
  match bias with
  | .before => position
  | .after => position + 1

/-- The nearest live slot strictly before `position`. -/
def previousLive (alive : List Bool) (position : Nat) : Option Nat :=
  (List.range position).reverse.find? fun index => alive.getD index false

/-- The nearest live slot strictly after `position`. -/
def nextLive (alive : List Bool) (position : Nat) : Option Nat :=
  ((List.range alive.length).filter fun index => decide (position < index)).find?
    fun index => alive.getD index false

def replacementSlot (alive : List Bool) (position : Nat) : EndpointDeathPolicy → Option Nat
  | .invalidate | .keepTombstone => none
  | .preferPrevious => previousLive alive position
  | .preferNext => nextLive alive position
  | .preferPreviousThenNext => (previousLive alive position).orElse fun _ => nextLive alive position
  | .preferNextThenPrevious => (nextLive alive position).orElse fun _ => previousLive alive position

inductive PointResolution where
  | cut (index : Nat)
  | invalidated
  | unresolved
  deriving DecidableEq, Repr

def resolvePoint (order : List AtomId) (alive : List Bool) (point : StablePoint) : PointResolution :=
  match point.neighbor with
  | none => .unresolved
  | some atom =>
      match order.findIdx? (· == atom) with
      | none => .unresolved
      | some position =>
          if alive.getD position false then .cut (cutAt point.bias position)
          else match point.death with
            | .invalidate => .invalidated
            | .keepTombstone => .cut (cutAt point.bias position)
            | policy => match replacementSlot alive position policy with
              | some index => .cut (cutAt point.bias index)
              | none => .unresolved

inductive RangeResolution where
  | slots (atoms : List AtomId)
  | invalidated
  | unresolved
  deriving DecidableEq, Repr

/-- The range's slots in run order: both endpoints on one run of the document. -/
def resolveRange (store : ContentStore) (document : DocumentId) (range : StableRange) :
    RangeResolution :=
  if range.start.run ≠ range.finish.run then .unresolved else
  match Hyperdocument.lookup store .runs range.start.run with
  | none => .unresolved
  | some run =>
      if run.document ≠ document then .unresolved else
      let alive := run.atoms.map (slotLive store document)
      match resolvePoint run.atoms alive range.start, resolvePoint run.atoms alive range.finish with
      | .cut start, .cut stop =>
          if start ≤ stop then .slots ((run.atoms.drop start).take (stop - start)) else .unresolved
      | .invalidated, _ => .invalidated
      | _, .invalidated => .invalidated
      | _, _ => .unresolved

/-- The live atoms among `atoms`, each with its current revision. -/
def livePins (store : ContentStore) (document : DocumentId) (atoms : List AtomId) :
    List (AtomId × OperationId) :=
  atoms.filterMap fun atom =>
    match Hyperdocument.lookup store .atoms atom with
    | some record =>
        if record.document = document ∧ record.tombstonedAt = none then some (atom, record.revision)
        else none
    | none => none

def endpointsLive (store : ContentStore) (document : DocumentId) (range : StableRange) : Bool :=
  match range.start.neighbor, range.finish.neighbor with
  | some first, some last => slotLive store document first && slotLive store document last
  | _, _ => false

/-- The disclosure check, run on the source cell's state at this height: both
endpoints are live atoms of one run of the source document, and the range's
live atoms are exactly the pinned atoms at the pinned revisions. -/
def openingHolds (store : ContentStore) (request : TranscludeRequest) : Bool :=
  let document := documentOf request.source
  endpointsLive store document request.range &&
    match resolveRange store document request.range with
    | .slots atoms => decide (livePins store document atoms = request.pins)
    | _ => false

/-! ## Rendering, over the reader's own read of the source -/

/-- What a reader sees where a transclusion stands. -/
inductive TransclusionView where
  /-- The reader holds no read of the source: only the opening's shape. -/
  | unavailable (atoms : Nat) (source : Nat)
  /-- A snapshot whose pinned atoms all stand at their pinned revisions. -/
  | snapshot (lines : List (List UInt8))
  /-- A snapshot whose pins no longer hold in the view supplied; the source
  read `at` this height (the opening's) holds them. -/
  | moved (height : Nat)
  /-- The range's current live atoms; `revised` when they differ from the pins. -/
  | live (lines : List (List UInt8)) (revised : Bool)
  /-- An endpoint died under `invalidate`. -/
  | invalidated
  /-- An endpoint died with no committed replacement, or the range is gone. -/
  | unresolved
  deriving DecidableEq, Repr

def semanticAtom (store : ContentStore) (atom : AtomId) : Option AtomRecord :=
  (Hyperdocument.lookup store .atoms atom).map AtomRecord.semantic

/-- Every semantic source lookup stays identical through custody maintenance. -/
theorem rewrapAtom_preserves_semantic (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (progress next : Progress) (atom target : AtomId)
    (before : AtomRecord) (wrapping : List UInt8)
    (accepted : rewrapAtom author operation document progress atom before wrapping = .ok next) :
    semanticAtom next.1 target = semanticAtom progress.1 target := by
  obtain ⟨present, schema, fragment, shape, post⟩ :=
    rewrapAtom_guarded_post author operation document progress next atom before wrapping accepted
  rw [post]
  unfold semanticAtom Hyperdocument.lookup
  by_cases same : target = atom
  · subst target
    rw [Store.Store.set_eq, present]
    simp only [Option.map]
    simp [AtomRecord.semantic, shape, AuthoredFragment.rewrapped]
  · rw [Store.Store.set_ne _ _ _ _ (fun eq => same (by cases eq; rfl))]

def pinHolds (store : ContentStore) (document : DocumentId) (pin : AtomId × OperationId) : Bool :=
  match semanticAtom store pin.1 with
  | some record => decide (record.document = document) && decide (record.revision = pin.2) &&
      record.tombstonedAt.isNone
  | none => false

def pinnedBytes (store : ContentStore) (pin : AtomId × OperationId) : List UInt8 :=
  match semanticAtom store pin.1 with
  | some record => record.bodyBytes
  | none => []

def renderSnapshot (store : ContentStore) (opening : RangeOpening) : TransclusionView :=
  if opening.pins.all (pinHolds store (documentOf opening.source)) then
    .snapshot (opening.pins.map (pinnedBytes store))
  else .moved opening.height

def renderLive (store : ContentStore) (opening : RangeOpening) : TransclusionView :=
  let document := documentOf opening.source
  match resolveRange store document opening.range with
  | .slots atoms =>
      let current := livePins store document atoms
      .live (current.map (pinnedBytes store)) (decide (current ≠ opening.pins))
  | .invalidated => .invalidated
  | .unresolved => .unresolved

/-- Render against the reader's view of the source cell.  `source` is a store
the reader obtained by its own signed read (current, or `at` a height): the
observation controller returns a cell only to a grant whose observe capability
covers it, so `none` is exactly "this reader cannot read the source". -/
def renderTransclusion (source : Option ContentStore) (opening : RangeOpening)
    (mode : TransclusionMode) : TransclusionView :=
  match source with
  | none => .unavailable opening.pins.length opening.source
  | some store =>
      match mode with
      | .snapshot => renderSnapshot store opening
      | .live => renderLive store opening

/-! ## Theorems -/

private theorem all_congr_mem {α : Type} (l : List α) (f g : α → Bool)
    (agree : ∀ x ∈ l, f x = g x) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons x xs induction =>
      simp only [List.all_cons, agree x (by simp),
        induction (fun y member => agree y (List.mem_cons_of_mem _ member))]

private theorem map_congr_mem {α β : Type} (l : List α) (f g : α → β)
    (agree : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons x xs induction =>
      simp only [List.map_cons, agree x (by simp),
        induction (fun y member => agree y (List.mem_cons_of_mem _ member))]

private theorem filterMap_congr_mem {α β : Type} (l : List α) (f g : α → Option β)
    (agree : ∀ x ∈ l, f x = g x) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons x xs induction =>
      simp only [List.filterMap_cons, agree x (by simp),
        induction (fun y member => agree y (List.mem_cons_of_mem _ member))]

/-- No read target on the source in this transaction: the transclusion is
refused `sourceNotCovered`, before anything is written. -/
theorem transclude_uncovered_refused (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) (progress : Progress)
    (transclusion : TransclusionId) (link : LinkId) (request : TranscludeRequest)
    (uncovered : context.sourceRead request.source = none) :
    step author operation document context progress (.transclude transclusion link request) =
      .error .sourceNotCovered := by
  simp [step, uncovered]

private theorem allocate_post (progress next : Progress) (space : Namespace) (key : Key space)
    (value : Value space) (accepted : allocate progress space key value = .ok next) :
    next.1 = progress.1.set ⟨space, key⟩ (some value) := by
  unfold allocate at accepted
  split at accepted
  · cases accepted; rfl
  · cases accepted

/-- The host's post holds the record and its forward link, computed from the
request, the height and the read's capability and policy: no source store is an
input of the host's computation, so no source byte reaches the host.  The only
other writes are the element tree's (the `embed` leaf naming the record, and
its parent's children); every other address of the host (atoms, runs, the
document, annotations) is framed. -/
theorem no_bytes_in_host (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) (progress next : Progress)
    (transclusion : TransclusionId) (link : LinkId) (request : TranscludeRequest)
    (read : SourceRead) (covered : context.sourceRead request.source = some read)
    (accepted : step author operation document context progress
      (.transclude transclusion link request) = .ok next) :
    Hyperdocument.lookup next.1 .transclusions transclusion = some (transclusionRecord operation author
        (transcludePayload document transclusion link request context.height read)) ∧
    Hyperdocument.lookup next.1 .links link = some (transclusionForwardLink operation author
        (transcludePayload document transclusion link request context.height read)) ∧
    ∀ address : Hyperdocument.Address, address.1 ≠ .transclusions → address.1 ≠ .links →
      address.1 ≠ .elements → next.1 address = progress.1 address := by
  simp only [step, covered] at accepted
  obtain ⟨first, firstOk, rest⟩ := bind_eq_ok accepted
  obtain ⟨second, secondOk, last⟩ := bind_eq_ok rest
  have frame := (appendLeaf_step author operation document last).2
  have secondPost := allocate_post first second _ _ _ secondOk
  have firstPost := allocate_post progress first _ _ _ firstOk
  refine ⟨?_, ?_, ?_⟩
  · unfold Hyperdocument.lookup
    rw [frame ⟨.transclusions, transclusion⟩ (by simp), secondPost,
      Store.Store.set_ne _ _ _ _ (fun same => absurd (congrArg Sigma.fst same) (by simp)),
      firstPost, Store.Store.set_eq]
    try exact rfl
  · unfold Hyperdocument.lookup
    rw [frame ⟨.links, link⟩ (by simp), secondPost, Store.Store.set_eq]
    try exact rfl
  · intro address notRecord notLink notElement
    rw [frame address notElement, secondPost,
      Store.Store.set_ne _ _ _ _ (fun same => notLink (congrArg Sigma.fst same)), firstPost,
      Store.Store.set_ne _ _ _ _ (fun same => notRecord (congrArg Sigma.fst same))]

/-- A reader without a read of the source learns only that a transclusion
stands and its shape (how many atoms, of which cell); what it sees does not
depend on the source at all. -/
theorem uncovered_reader_sees_shape (opening : RangeOpening) (mode : TransclusionMode) :
    renderTransclusion none opening mode = .unavailable opening.pins.length opening.source := rfl

/-! ### Snapshots are pinned -/

/-- Every atom standing at `revision` retains the same semantic record.
Only fragment-key custody and its maintenance provenance may differ. -/
def KeepsAt (revision : OperationId) (before after : ContentStore) : Prop :=
  ∀ atom (record : AtomRecord), Hyperdocument.lookup after .atoms atom = some record →
    record.revision = revision → ∃ previous,
      Hyperdocument.lookup before .atoms atom = some previous ∧ previous.semantic = record.semantic

theorem KeepsAt.refl (revision : OperationId) (store : ContentStore) :
    KeepsAt revision store store := fun _ record found _ => ⟨record, found, rfl⟩

theorem KeepsAt.trans {revision : OperationId} {first second third : ContentStore}
    (left : KeepsAt revision first second) (right : KeepsAt revision second third) :
    KeepsAt revision first third := by
  intro atom record found pinned
  obtain ⟨middle, middleFound, middleSame⟩ := right atom record found pinned
  have middleRevision : middle.revision = revision := by
    have equal := congrArg AtomRecord.revision middleSame
    simpa only [AtomRecord.semantic_revision, pinned] using equal
  obtain ⟨previous, previousFound, previousSame⟩ := left atom middle middleFound middleRevision
  exact ⟨previous, previousFound, previousSame.trans middleSame⟩

private theorem keepsAt_set_other (revision : OperationId) (store : ContentStore)
    (space : Namespace) (key : Key space) (value : Value space) (other : space ≠ .atoms) :
    KeepsAt revision store (store.set ⟨space, key⟩ (some value)) := by
  intro atom record found _
  refine ⟨record, ?_, rfl⟩
  unfold Hyperdocument.lookup at found ⊢
  rwa [Store.Store.set_ne _ _ _ _ (fun same => other (congrArg Sigma.fst same).symm)] at found

private theorem keepsAt_set_atom (revision : OperationId) (store : ContentStore) (key : AtomId)
    (value : AtomRecord) (stamped : value.revision ≠ revision) :
    KeepsAt revision store (store.set ⟨.atoms, key⟩ (some value)) := by
  intro atom record found pinned
  unfold Hyperdocument.lookup at found
  by_cases same : atom = key
  · subst same
    rw [Store.Store.set_eq] at found
    cases found
    exact absurd pinned stamped
  · refine ⟨record, ?_, rfl⟩
    unfold Hyperdocument.lookup
    rwa [Store.Store.set_ne _ _ _ _ (fun eq => same (by cases eq; rfl))] at found

private theorem keepsAt_allocate_other (revision : OperationId) (progress next : Progress)
    (space : Namespace) (key : Key space) (value : Value space)
    (accepted : allocate progress space key value = .ok next) (other : space ≠ .atoms) :
    KeepsAt revision progress.1 next.1 := by
  rw [allocate_post progress next space key value accepted]
  exact keepsAt_set_other revision progress.1 space key value other

private theorem keepsAt_of_markStep (revision : OperationId) {progress next : Progress}
    (stepped : MarkStep progress next) : KeepsAt revision progress.1 next.1 := by
  intro atom record found _
  refine ⟨record, ?_, rfl⟩
  unfold Hyperdocument.lookup at found ⊢
  rwa [stepped.2 ⟨.atoms, atom⟩ (by simp) (by simp)] at found

/-- A step by an operation other than `revision` changes no atom that stands at
`revision` afterwards: every atom it creates or edits is stamped with the
operation itself. -/
private theorem keepsAt_of_elementStep (revision : OperationId) {progress next : Progress}
    (stepped : ElementStep progress next) : KeepsAt revision progress.1 next.1 := by
  intro atom record found _
  refine ⟨record, ?_, rfl⟩
  unfold Hyperdocument.lookup at found ⊢
  rwa [stepped.2 ⟨.atoms, atom⟩ (by simp)] at found

/-- A step by an operation other than `revision` changes no atom that stands at
`revision` afterwards: every atom it creates or edits is stamped with the
operation itself. -/
theorem step_keepsAt (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (context : Context) (progress next : Progress) (action : Action) (revision : OperationId)
    (other : operation ≠ revision)
    (accepted : step author operation document context progress action = .ok next) :
    KeepsAt revision progress.1 next.1 := by
  cases action with
  | createDocument root schema =>
      simp only [step] at accepted
      obtain ⟨middle, first, rest⟩ := bind_eq_ok accepted
      exact (keepsAt_allocate_other revision progress middle _ _ _ first (by decide)).trans
        (keepsAt_allocate_other revision middle next _ _ _ rest (by decide))
  | createAtom atom kind payload =>
      simp only [step] at accepted
      split at accepted
      · obtain ⟨middle, first, rest⟩ := bind_eq_ok accepted
        have atomKept : KeepsAt revision progress.1 middle.1 := by
          rw [allocate_post progress middle _ _ _ first]
          exact keepsAt_set_atom revision progress.1 atom _ other
        exact atomKept.trans
          (keepsAt_of_elementStep revision (appendLeaf_step author operation document rest))
      · cases accepted
  | editAtom edit =>
      simp only [step] at accepted
      split at accepted
      · unfold replaceAtom at accepted
        split at accepted
        · cases accepted
        · split at accepted
          · cases accepted
          · cases accepted
            exact keepsAt_set_atom revision progress.1 _ _ (by rw [sourceEditAtomRecord_revision]; exact other)
      · cases accepted
  | rewrapAtom atom before wrapping =>
      obtain ⟨present, schema, fragment, shape, post⟩ :=
        rewrapAtom_guarded_post author operation document progress next atom before wrapping accepted
      rw [post]
      intro target record found pinned
      unfold Hyperdocument.lookup at found ⊢
      by_cases same : target = atom
      · subst target
        rw [Store.Store.set_eq] at found
        cases found
        exact ⟨before, present, by simp [AtomRecord.semantic, shape, AuthoredFragment.rewrapped]⟩
      · refine ⟨record, ?_, rfl⟩
        rwa [Store.Store.set_ne _ _ _ _ (fun eq => same (by cases eq; rfl))] at found
  | link link source target relation =>
      simp only [step] at accepted
      split at accepted
      · exact keepsAt_allocate_other revision progress next _ _ _ accepted (by decide)
      · cases accepted
  | createRun runId atoms =>
      simp only [step] at accepted
      split at accepted
      · exact keepsAt_allocate_other revision progress next _ _ _ accepted (by decide)
      · cases accepted
  | annotate annotationId atom pinned body =>
      simp only [step] at accepted
      split at accepted
      · exact keepsAt_allocate_other revision progress next _ _ _ accepted (by decide)
      · cases accepted
  | rewrapAnnotation annotation before wrapping =>
      simp only [step, rewrapAnnotation] at accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted
        · cases shape : before.body with
          | inline bytes => simp [shape] at accepted
          | reference source => simp [shape] at accepted
          | sealed fragment =>
              simp only [shape] at accepted
              cases accepted
              exact keepsAt_set_other revision progress.1 .annotations annotation _ (by decide)
  | transclude transclusion link request =>
      cases covered : context.sourceRead request.source with
      | none => simp [step, covered] at accepted
      | some read =>
          simp only [step, covered] at accepted
          obtain ⟨first, firstOk, rest⟩ := bind_eq_ok accepted
          obtain ⟨second, secondOk, last⟩ := bind_eq_ok rest
          exact ((keepsAt_allocate_other revision progress first _ _ _ firstOk (by decide)).trans
            (keepsAt_allocate_other revision first second _ _ _ secondOk (by decide))).trans
            (keepsAt_of_elementStep revision (appendLeaf_step author operation document last))
  | editElement edit =>
      exact keepsAt_of_elementStep revision (editElementStep_step operation document accepted)
  | createContainer element =>
      simp only [step] at accepted
      split at accepted
      · cases accepted
      · exact keepsAt_of_elementStep revision (appendLeaf_step author operation document accepted)
  | unlink link =>
      simp only [step, retireLink] at accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted
          exact keepsAt_set_other revision progress.1 .links link _ (by decide)
        · cases accepted
  | mark mark request =>
      simp only [step] at accepted
      exact keepsAt_of_markStep revision (markStep_markStep accepted)
  | unmark mark =>
      simp only [step] at accepted
      exact keepsAt_of_markStep revision (unmarkStep_markStep accepted)

theorem run_keepsAt (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (context : Context) (pre : ContentStore) (command : Command) (next : Progress)
    (revision : OperationId) (other : operation ≠ revision)
    (accepted : run author operation document context pre command = .ok next) :
    KeepsAt revision pre next.1 := by
  suffices general : ∀ (actions : List Action) (progress : Progress),
      actions.foldlM (step author operation document context) progress = .ok next →
        KeepsAt revision progress.1 next.1 from general command.actions (pre, []) accepted
  intro actions
  induction actions with
  | nil =>
      intro progress done
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at done
      rw [done]; exact KeepsAt.refl _ _
  | cons action rest induction =>
      intro progress done
      simp only [List.foldlM_cons, bind, Except.bind] at done
      cases stepped : step author operation document context progress action with
      | error reason => simp [stepped] at done
      | ok middle =>
          simp only [stepped] at done
          exact (step_keepsAt author operation document context progress middle action revision
            other stepped).trans (induction middle done)

/-- `later` is reached from `earlier` by accepted content runs with these operations. -/
inductive Reaches : ContentStore → ContentStore → List OperationId → Prop
  | refl (store : ContentStore) : Reaches store store []
  | step {earlier later : ContentStore} {operations : List OperationId}
      (author : PrincipalRef) (operation : OperationId) (document : DocumentId) (context : Context)
      (command : Command) (progress : Progress)
      (accepted : run author operation document context earlier command = .ok progress)
      (rest : Reaches progress.1 later operations) :
      Reaches earlier later (operation :: operations)

theorem Reaches.keepsAt {earlier later : ContentStore} {operations : List OperationId}
    (reached : Reaches earlier later operations) (revision : OperationId)
    (fresh : revision ∉ operations) : KeepsAt revision earlier later := by
  induction reached with
  | refl store => exact KeepsAt.refl _ _
  | step author operation document context command progress accepted rest induction =>
      have notHead : operation ≠ revision := fun same => fresh (by simp [same])
      have notTail : revision ∉ _ := fun member => fresh (List.mem_cons_of_mem _ member)
      exact (run_keepsAt author operation document context _ command progress revision notHead
        accepted).trans (induction notTail)

private theorem pinHolds_found {store : ContentStore} {document : DocumentId}
    {pin : AtomId × OperationId} (holds : pinHolds store document pin = true) :
    ∃ record : AtomRecord, Hyperdocument.lookup store .atoms pin.1 = some record ∧
      record.revision = pin.2 := by
  unfold pinHolds semanticAtom at holds
  cases found : Hyperdocument.lookup store .atoms pin.1 with
  | none => simp [found, Option.map] at holds
  | some record =>
      simp only [found, Option.map, AtomRecord.semantic, Bool.and_eq_true, decide_eq_true_eq] at holds
      exact ⟨record, rfl, holds.1.2⟩

private theorem renderSnapshot_congr (earlier later : ContentStore) (opening : RangeOpening)
    (agree : ∀ pin ∈ opening.pins, semanticAtom later pin.1 = semanticAtom earlier pin.1) :
    renderSnapshot later opening = renderSnapshot earlier opening := by
  have holds := all_congr_mem opening.pins (pinHolds later (documentOf opening.source))
    (pinHolds earlier (documentOf opening.source))
    (fun pin member => by simp only [pinHolds, agree pin member])
  have bytes := map_congr_mem opening.pins (pinnedBytes later) (pinnedBytes earlier)
    (fun pin member => by simp only [pinnedBytes, agree pin member])
  simp only [renderSnapshot, holds, bytes]

private theorem livePins_mem {store : ContentStore} {document : DocumentId} {atoms : List AtomId}
    {pin : AtomId × OperationId} (member : pin ∈ livePins store document atoms) :
    pin.1 ∈ atoms ∧ pinHolds store document pin = true := by
  unfold livePins at member
  obtain ⟨atom, inside, produced⟩ := List.mem_filterMap.mp member
  cases found : Hyperdocument.lookup store .atoms atom with
  | none => simp [found] at produced
  | some record =>
      simp only [found] at produced
      split at produced
      · rename_i live
        cases produced
        exact ⟨inside, by simp [pinHolds, semanticAtom, Option.map, AtomRecord.semantic, found, live.1, live.2]⟩
      · cases produced

/-- Snapshot transclusions are pinned.  At the opening's height (the state the
admission checked, which a reader recovers by reading the source `at` that
height) the snapshot shows exactly the pinned atoms' bytes.  At any later state
reached by accepted runs whose operations are not the pinned revisions, it
shows those same bytes or says `moved` — never other bytes. -/
theorem transclusion_pinned (earlier later : ContentStore) (operations : List OperationId)
    (request : TranscludeRequest) (height : Nat)
    (admitted : openingHolds earlier request = true)
    (reached : Reaches earlier later operations)
    (fresh : ∀ pin ∈ request.pins, pin.2 ∉ operations) :
    renderSnapshot earlier (.ofRequest request height) =
        .snapshot (request.pins.map (pinnedBytes earlier)) ∧
      (renderSnapshot later (.ofRequest request height) =
          .snapshot (request.pins.map (pinnedBytes earlier)) ∨
        renderSnapshot later (.ofRequest request height) = .moved height) := by
  have atOpening : renderSnapshot earlier (.ofRequest request height) =
      .snapshot (request.pins.map (pinnedBytes earlier)) := by
    have all : request.pins.all (pinHolds earlier (documentOf request.source)) = true := by
      unfold openingHolds at admitted
      simp only [Bool.and_eq_true] at admitted
      obtain ⟨_, resolved⟩ := admitted
      split at resolved
      · rename_i atoms _
        have equal := of_decide_eq_true resolved
        apply List.all_eq_true.mpr
        intro pin member
        rw [← equal] at member
        exact (livePins_mem member).2
      · cases resolved
    simp only [renderSnapshot, RangeOpening.ofRequest, all, if_true]
  refine ⟨atOpening, ?_⟩
  by_cases holds : request.pins.all (pinHolds later (documentOf request.source)) = true
  · left
    rw [← atOpening]
    apply renderSnapshot_congr
    intro pin member
    obtain ⟨record, found, pinned⟩ := pinHolds_found (List.all_eq_true.mp holds pin member)
    obtain ⟨previous, previousFound, same⟩ := reached.keepsAt pin.2 (fresh pin member) pin.1 record found pinned
    simp only [semanticAtom, found, previousFound, Option.map, same]
  · right
    simp [renderSnapshot, RangeOpening.ofRequest, holds]

/-! ### Live transclusions follow the range -/

private theorem resolveRange_congr (earlier later : ContentStore) (document : DocumentId)
    (range : StableRange)
    (sameRun : Hyperdocument.lookup later .runs range.start.run =
      Hyperdocument.lookup earlier .runs range.start.run)
    (sameAtoms : ∀ run, Hyperdocument.lookup earlier .runs range.start.run = some run →
      ∀ atom ∈ run.atoms, Hyperdocument.lookup later .atoms atom =
        Hyperdocument.lookup earlier .atoms atom) :
    resolveRange later document range = resolveRange earlier document range := by
  cases found : Hyperdocument.lookup earlier .runs range.start.run with
  | none => simp only [resolveRange, sameRun, found]
  | some run =>
      have alive := map_congr_mem run.atoms (slotLive later document) (slotLive earlier document)
        (fun atom member => by simp only [slotLive, sameAtoms run found atom member])
      simp only [resolveRange, sameRun, found, alive]

private theorem resolveRange_slots (store : ContentStore) (document : DocumentId)
    (range : StableRange) (atoms : List AtomId)
    (resolved : resolveRange store document range = .slots atoms) :
    ∃ run : RunRecord, Hyperdocument.lookup store .runs range.start.run = some run ∧
      ∀ atom ∈ atoms, atom ∈ run.atoms := by
  cases found : Hyperdocument.lookup store .runs range.start.run with
  | none =>
      unfold resolveRange at resolved
      simp only [found] at resolved
      split at resolved <;> cases resolved
  | some run =>
      refine ⟨run, rfl, ?_⟩
      unfold resolveRange at resolved
      simp only [found] at resolved
      split at resolved
      · cases resolved
      · split at resolved
        · cases resolved
        · split at resolved
          · split at resolved
            · cases resolved
              exact fun atom member => List.mem_of_mem_drop (List.mem_of_mem_take member)
            · cases resolved
          all_goals cases resolved

/-- A live rendering reads only the range's run and that run's atoms: an edit
anywhere else in the source (another run's atoms, links, annotations, other
documents) leaves it exactly as it was. -/
theorem live_reads_only_its_run (earlier later : ContentStore) (opening : RangeOpening)
    (sameRun : Hyperdocument.lookup later .runs opening.range.start.run =
      Hyperdocument.lookup earlier .runs opening.range.start.run)
    (sameAtoms : ∀ run, Hyperdocument.lookup earlier .runs opening.range.start.run = some run →
      ∀ atom ∈ run.atoms, Hyperdocument.lookup later .atoms atom =
        Hyperdocument.lookup earlier .atoms atom) :
    renderLive later opening = renderLive earlier opening := by
  have same := resolveRange_congr earlier later (documentOf opening.source) opening.range sameRun
    sameAtoms
  cases resolved : resolveRange earlier (documentOf opening.source) opening.range with
  | slots atoms =>
      obtain ⟨run, found, inside⟩ := resolveRange_slots earlier _ _ atoms resolved
      have agree : ∀ atom ∈ atoms, Hyperdocument.lookup later .atoms atom =
          Hyperdocument.lookup earlier .atoms atom :=
        fun atom member => sameAtoms run found atom (inside atom member)
      have pins : livePins later (documentOf opening.source) atoms =
          livePins earlier (documentOf opening.source) atoms := by
        unfold livePins
        exact filterMap_congr_mem atoms _ _ (fun atom member => by simp only [agree atom member])
      have bytes := map_congr_mem (livePins earlier (documentOf opening.source) atoms)
        (pinnedBytes later) (pinnedBytes earlier)
        (fun pin member => by simp only [pinnedBytes, semanticAtom, agree pin.1 (livePins_mem member).1])
      simp only [renderLive, same, resolved]
      rw [pins, bytes]
  | invalidated => simp only [renderLive, same, resolved]
  | unresolved => simp only [renderLive, same, resolved]


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

/-- info: 'Minidregg.Kernel.ContentResource.transclude_uncovered_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transclude_uncovered_refused
/-- info: 'Minidregg.Kernel.ContentResource.no_bytes_in_host' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_bytes_in_host
/-- info: 'Minidregg.Kernel.ContentResource.uncovered_reader_sees_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uncovered_reader_sees_shape
/-- info: 'Minidregg.Kernel.ContentResource.transclusion_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transclusion_pinned
/-- info: 'Minidregg.Kernel.ContentResource.live_reads_only_its_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms live_reads_only_its_run
/-- info: 'Minidregg.Kernel.ContentResource.step_keepsAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_keepsAt
/-- info: 'Minidregg.Kernel.ContentResource.Reaches.keepsAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Reaches.keepsAt

#assert_axioms sourceEditAtomRecord_authored
#assert_axioms createAtom_sealed_nonempty_refused
#assert_axioms sourceEditAtomRecord_retirement_preserves_authorship
#assert_axioms rewrapAtom_guarded_post
#assert_axioms rewrapAtom_preserves_revision
#assert_axioms rewrapAtom_preserves_semantic
#assert_axioms rewrapAnnotation_guarded_post
#assert_axioms rewrapAnnotation_preserves_body

end Minidregg.Kernel.ContentResource
