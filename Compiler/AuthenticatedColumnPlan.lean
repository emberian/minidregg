/-
# Compiler.AuthenticatedColumnPlan -- typed authenticated-column control

This is one Lean-owned, multi-phase controller spine.  A plan fixes typed
column ports, commitment roots, transcript order, opaque work, openings,
representation-equality edges, and the final check.  Native code returns only
fallible byte buffers.  Successful bytes are decoded and checked against an
output already selected by Lean; they are never passed to a continuation.

Every challenge constructor requires a nonempty root anchor.  The only draw
function belongs to the single domain-separated transcript portal, so roots
precede challenges structurally rather than by a timestamp comparison.
-/

import Compiler.NativeKernelPlan
import Compiler.SemanticManifest
import Loom.Commitment
import Theory.IndexedProgram

namespace Minidregg.Compiler.AuthenticatedColumnPlan

open Minidregg.Compiler.NativeKernelPlan (WorkKind)
open Minidregg.Compiler.SemanticManifest
open Minidregg.Loom
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-! ## Typed ports, commitments, and openings -/

inductive ColumnRole where
  | semanticTrace
  | lookupAddress
  | lookupWeight
  | lookupTable
  | accumulator
  | checkpoint
  | auxiliary
deriving DecidableEq, Repr

structure RootSlot where
  slotId : Digest
  role : ColumnRole
  semanticTypeId : Digest
  representationId : Digest
  carrierProfileId : Digest
  semanticCodecId : Digest
  representationCodecId : Digest
  domainId : Digest
  domainCodecId : Digest
  commitmentSuiteId : Digest
deriving DecidableEq, Repr

structure RootRecord where
  slot : RootSlot
  root : Digest
deriving DecidableEq, Repr

/-- The three type parameters prevent a semantic value, its representation,
and its index domain from being silently identified. -/
structure ColumnPort (Semantic Representation Domain : Type) where
  slotId : Digest
  role : ColumnRole
  semanticTypeId : Digest
  representationId : Digest
  carrier : CarrierProfile
  semanticCodecPin : CodecPin
  representationCodecPin : CodecPin
  domainId : Digest
  domainCodecPin : CodecPin
  semanticCodec : LawfulCodec Semantic
  representationCodec : LawfulCodec Representation
  domainCodec : LawfulCodec Domain
  represent : Semantic -> Representation

/-- Executable commitment/opening data. Honest opening generation and
completeness are part of the scheme; binding remains the separate property
below because a deployed Merkle realization prices it through collision
resistance. -/
structure CommitmentScheme
    {Semantic Representation Domain : Type}
    (port : ColumnPort Semantic Representation Domain) where
  suiteId : Digest
  proofCodecPin : CodecPin
  commit : (Domain -> Representation) -> Digest
  openAt : (Domain -> Representation) -> Domain -> List UInt8
  verifyOpening : Digest -> Domain -> Representation -> List UInt8 -> Bool
  verifyOpening_commit : forall column index,
    verifyOpening (commit column) index (column index) (openAt column index) = true

/-- Position binding for the exact executable opening checker. It is not
derived from completeness: a deployed hash commitment must supply this under
its collision-resistance assumption. -/
def CommitmentScheme.PositionBinding
    {Semantic Representation Domain : Type}
    {port : ColumnPort Semantic Representation Domain}
    (scheme : CommitmentScheme port) : Prop :=
  forall root index left right leftProof rightProof,
    scheme.verifyOpening root index left leftProof = true ->
    scheme.verifyOpening root index right rightProof = true ->
    left = right

/-- The authenticated-column commitment carrying the same position-binding
property consumed by Loom accumulation and extraction. -/
structure BindingCommitmentScheme
    {Semantic Representation Domain : Type}
    (port : ColumnPort Semantic Representation Domain)
    extends CommitmentScheme port where
  binding : toCommitmentScheme.PositionBinding

/-- Literal adapter from the controller's executable scheme to Loom's opening
relation. No root, index, value, or proof codec is changed. -/
def CommitmentScheme.toLoomOpeningScheme
    {Semantic Representation Domain : Type}
    {port : ColumnPort Semantic Representation Domain}
    (scheme : CommitmentScheme port) :
    OpeningScheme Digest Representation Domain (List UInt8) where
  commit := scheme.commit
  openAt := scheme.openAt
  verifyOpen := fun root index value proof =>
    scheme.verifyOpening root index value proof = true
  verifyOpen_commit := scheme.verifyOpening_commit

/-- A binding authenticated-column scheme is exactly a Loom binding
commitment. This closes the formerly duplicated commitment interface between
controller transcripts and proof-carrying history. -/
def BindingCommitmentScheme.toLoom
    {Semantic Representation Domain : Type}
    {port : ColumnPort Semantic Representation Domain}
    (scheme : BindingCommitmentScheme port) :
    BindingCommitment Digest Representation Domain (List UInt8) where
  toOpeningScheme := scheme.toCommitmentScheme.toLoomOpeningScheme
  binding := scheme.binding

@[simp] theorem BindingCommitmentScheme.toLoom_commit
    {Semantic Representation Domain : Type}
    {port : ColumnPort Semantic Representation Domain}
    (scheme : BindingCommitmentScheme port)
    (column : Domain -> Representation) :
    scheme.toLoom.commit column = scheme.commit column :=
  rfl

@[simp] theorem BindingCommitmentScheme.toLoom_openAt
    {Semantic Representation Domain : Type}
    {port : ColumnPort Semantic Representation Domain}
    (scheme : BindingCommitmentScheme port)
    (column : Domain -> Representation) (index : Domain) :
    scheme.toLoom.openAt column index = scheme.openAt column index :=
  rfl

theorem BindingCommitmentScheme.toLoom_verifyOpen_iff
    {Semantic Representation Domain : Type}
    {port : ColumnPort Semantic Representation Domain}
    (scheme : BindingCommitmentScheme port)
    (root : Digest) (index : Domain) (value : Representation)
    (proof : List UInt8) :
    scheme.toLoom.verifyOpen root index value proof <->
      scheme.verifyOpening root index value proof = true :=
  Iff.rfl

def ColumnPort.rootSlot
    {Semantic Representation Domain : Type}
    (port : ColumnPort Semantic Representation Domain)
    (scheme : CommitmentScheme port) : RootSlot where
  slotId := port.slotId
  role := port.role
  semanticTypeId := port.semanticTypeId
  representationId := port.representationId
  carrierProfileId := port.carrier.id
  semanticCodecId := port.semanticCodecPin.codecId
  representationCodecId := port.representationCodecPin.codecId
  domainId := port.domainId
  domainCodecId := port.domainCodecPin.codecId
  commitmentSuiteId := scheme.suiteId

/-- The root is derived from a pointwise exact representation; it is not an
imported root field. -/
structure BoundColumn
    {Semantic Representation Domain : Type}
    (port : ColumnPort Semantic Representation Domain)
    (scheme : CommitmentScheme port) where
  semantic : Domain -> Semantic
  represented : Domain -> Representation
  representationExact : forall index,
    represented index = port.represent (semantic index)

def BoundColumn.root
    {Semantic Representation Domain : Type}
    {port : ColumnPort Semantic Representation Domain}
    {scheme : CommitmentScheme port}
    (column : BoundColumn port scheme) : Digest :=
  scheme.commit column.represented

def BoundColumn.rootRecord
    {Semantic Representation Domain : Type}
    {port : ColumnPort Semantic Representation Domain}
    {scheme : CommitmentScheme port}
    (column : BoundColumn port scheme) : RootRecord :=
  ⟨port.rootSlot scheme, column.root⟩

structure OpeningRecord where
  openingSlotId : Digest
  root : RootRecord
  indexBytes : List UInt8
  semanticValueBytes : List UInt8
  representationValueBytes : List UInt8
  proofCodecId : Digest
  proofBytes : List UInt8
deriving DecidableEq, Repr

structure ColumnOpening
    {Semantic Representation Domain : Type}
    {port : ColumnPort Semantic Representation Domain}
    {scheme : CommitmentScheme port}
    (column : BoundColumn port scheme) where
  openingSlotId : Digest
  index : Domain
  semanticValue : Semantic
  representationValue : Representation
  proofBytes : List UInt8
  semanticExact : semanticValue = column.semantic index
  representationExact : representationValue = column.represented index
  verified : scheme.verifyOpening column.root index representationValue proofBytes = true

/-- The canonical honest opening for a bound column. -/
def BoundColumn.honestOpening
    {Semantic Representation Domain : Type}
    {port : ColumnPort Semantic Representation Domain}
    {scheme : CommitmentScheme port}
    (column : BoundColumn port scheme)
    (openingSlotId : Digest) (index : Domain) : ColumnOpening column where
  openingSlotId := openingSlotId
  index := index
  semanticValue := column.semantic index
  representationValue := column.represented index
  proofBytes := scheme.openAt column.represented index
  semanticExact := rfl
  representationExact := rfl
  verified := scheme.verifyOpening_commit column.represented index

/-- A controller-accepted opening is the identical Loom opening relation for
the adapted scheme. -/
theorem ColumnOpening.verifiesInLoom
    {Semantic Representation Domain : Type}
    {port : ColumnPort Semantic Representation Domain}
    {scheme : CommitmentScheme port}
    {column : BoundColumn port scheme}
    (opening : ColumnOpening column) :
    scheme.toLoomOpeningScheme.verifyOpen column.root opening.index
      opening.representationValue opening.proofBytes :=
  opening.verified

def ColumnOpening.record
    {Semantic Representation Domain : Type}
    {port : ColumnPort Semantic Representation Domain}
    {scheme : CommitmentScheme port}
    {column : BoundColumn port scheme}
    (opening : ColumnOpening column) : OpeningRecord where
  openingSlotId := opening.openingSlotId
  root := column.rootRecord
  indexBytes := port.domainCodec.encode opening.index
  semanticValueBytes := port.semanticCodec.encode opening.semanticValue
  representationValueBytes :=
    port.representationCodec.encode opening.representationValue
  proofCodecId := scheme.proofCodecPin.codecId
  proofBytes := opening.proofBytes

/-! ## Typed same-opening / representation-equality edges -/

inductive ReprEqRole where
  | representationEquality
  | sameOpening
deriving DecidableEq, Repr

/-- A bridge is an executable Lean relation over two typed semantic values. -/
structure ReprEqSpec (Source Target : Type) where
  bridgeId : Digest
  role : ReprEqRole
  check : Source -> Target -> Bool

structure ReprEqRecord where
  bridgeId : Digest
  role : ReprEqRole
  sourceOpeningSlotId : Digest
  targetOpeningSlotId : Digest
deriving DecidableEq, Repr

structure ReprEqEdge
    {SourceSemantic SourceRepresentation SourceDomain : Type}
    {sourcePort : ColumnPort SourceSemantic SourceRepresentation SourceDomain}
    {sourceScheme : CommitmentScheme sourcePort}
    {sourceColumn : BoundColumn sourcePort sourceScheme}
    {TargetSemantic TargetRepresentation TargetDomain : Type}
    {targetPort : ColumnPort TargetSemantic TargetRepresentation TargetDomain}
    {targetScheme : CommitmentScheme targetPort}
    {targetColumn : BoundColumn targetPort targetScheme}
    (spec : ReprEqSpec SourceSemantic TargetSemantic)
    (source : ColumnOpening sourceColumn)
    (target : ColumnOpening targetColumn) where
  checked : spec.check source.semanticValue target.semanticValue = true

def ReprEqEdge.record
    {SourceSemantic SourceRepresentation SourceDomain : Type}
    {sourcePort : ColumnPort SourceSemantic SourceRepresentation SourceDomain}
    {sourceScheme : CommitmentScheme sourcePort}
    {sourceColumn : BoundColumn sourcePort sourceScheme}
    {TargetSemantic TargetRepresentation TargetDomain : Type}
    {targetPort : ColumnPort TargetSemantic TargetRepresentation TargetDomain}
    {targetScheme : CommitmentScheme targetPort}
    {targetColumn : BoundColumn targetPort targetScheme}
    {spec : ReprEqSpec SourceSemantic TargetSemantic}
    {source : ColumnOpening sourceColumn}
    {target : ColumnOpening targetColumn}
    (_edge : ReprEqEdge spec source target) : ReprEqRecord :=
  ⟨spec.bridgeId, spec.role, source.openingSlotId, target.openingSlotId⟩

def sameOpeningSpec (Value : Type) [DecidableEq Value]
    (bridgeId : Digest) : ReprEqSpec Value Value where
  bridgeId := bridgeId
  role := .sameOpening
  check := fun left right => decide (left = right)

theorem sameOpeningSpec_checked_iff
    {Value : Type} [DecidableEq Value]
    (bridgeId : Digest) (left right : Value) :
    (sameOpeningSpec Value bridgeId).check left right = true <-> left = right := by
  simp [sameOpeningSpec]

/-! ## Opaque work: declared output, canonical decoder, fixed continuation -/

structure NativeCall where
  Input : Type
  Output : Type
  outputDecidableEq : DecidableEq Output
  callSlotId : Digest
  kind : WorkKind
  carrierProfileId : Digest
  inputCodecPin : CodecPin
  outputCodecPin : CodecPin
  inputCodec : LawfulCodec Input
  outputCodec : LawfulCodec Output
  input : Input
  claimedOutput : Output
  leanCheck : Input -> Output -> Bool

structure NativeRecord where
  callSlotId : Digest
  kind : WorkKind
  carrierProfileId : Digest
  inputCodecId : Digest
  outputCodecId : Digest
  inputBytes : List UInt8
  outputBytes : List UInt8
deriving DecidableEq, Repr

def NativeCall.record (call : NativeCall) : NativeRecord :=
  ⟨call.callSlotId, call.kind, call.carrierProfileId,
    call.inputCodecPin.codecId, call.outputCodecPin.codecId,
    call.inputCodec.encode call.input,
    call.outputCodec.encode call.claimedOutput⟩

def NativeCall.acceptsReply (call : NativeCall) (bytes : List UInt8) : Bool :=
  letI : DecidableEq call.Output := call.outputDecidableEq
  decide (bytes = call.outputCodec.encode call.claimedOutput) &&
    decide (call.outputCodec.decode bytes = some call.claimedOutput) &&
    call.leanCheck call.input call.claimedOutput

abbrev NativeRunner (Error : Type) :=
  (call : NativeCall) -> Except Error (List UInt8)

/-! ## One global domain-separated transcript -/

inductive DrawRole where
  | roundChallenge
  | queryChallenge
deriving DecidableEq, Repr

structure GlobalDrawLabel where
  transcriptDomain : Digest
  role : DrawRole
  ordinal : Nat
deriving DecidableEq, Repr

structure DrawRecord where
  label : GlobalDrawLabel
  coin : Digest
deriving DecidableEq, Repr

inductive GlobalFrame where
  | publicContext (transcriptDomain : Digest) (bytes : List UInt8)
  | root (record : RootRecord)
  | nativeReply (record : NativeRecord)
  | opening (record : OpeningRecord)
  | representationEdge (record : ReprEqRecord)
deriving DecidableEq, Repr

structure GlobalTranscriptPortal (State : Type) where
  absorb : State -> GlobalFrame -> State
  squeeze : State -> GlobalDrawLabel -> Digest × State
  xof : State -> GlobalDrawLabel -> Digest
  squeeze_xof_law : forall state label,
    (squeeze state label).1 = xof state label

structure DerivedChallenge {State : Type}
    (portal : GlobalTranscriptPortal State) where
  preState : State
  label : GlobalDrawLabel
  coin : Digest
  portalLaw : coin = portal.xof preState label

def DerivedChallenge.record
    {State : Type} {portal : GlobalTranscriptPortal State}
    (draw : DerivedChallenge portal) : DrawRecord :=
  ⟨draw.label, draw.coin⟩

structure TranscriptState {State : Type}
    (portal : GlobalTranscriptPortal State) where
  sponge : State
  frames : List GlobalFrame
  draws : List (DerivedChallenge portal)

def TranscriptState.initial {State : Type}
    (portal : GlobalTranscriptPortal State) (seed : State) :
    TranscriptState portal := ⟨seed, [], []⟩

def TranscriptState.absorb {State : Type}
    {portal : GlobalTranscriptPortal State}
    (state : TranscriptState portal) (frame : GlobalFrame) :
    TranscriptState portal :=
  ⟨portal.absorb state.sponge frame, state.frames ++ [frame], state.draws⟩

def TranscriptState.draw {State : Type}
    {portal : GlobalTranscriptPortal State}
    (state : TranscriptState portal) (label : GlobalDrawLabel) :
    DerivedChallenge portal × TranscriptState portal :=
  let result := portal.squeeze state.sponge label
  let draw : DerivedChallenge portal :=
    ⟨state.sponge, label, result.1,
      portal.squeeze_xof_law state.sponge label⟩
  (draw, ⟨result.2, state.frames, state.draws ++ [draw]⟩)

/-! ## Exact first-order ledger and intrinsically ordered plan -/

structure Ledger where
  roots : List RootRecord
  draws : List DrawRecord
  native : List NativeRecord
  openings : List OpeningRecord
  edges : List ReprEqRecord
deriving DecidableEq, Repr

def Ledger.empty : Ledger := ⟨[], [], [], [], []⟩
def Ledger.addRoot (l : Ledger) (r : RootRecord) : Ledger :=
  { l with roots := l.roots ++ [r] }
def Ledger.addDraw (l : Ledger) (r : DrawRecord) : Ledger :=
  { l with draws := l.draws ++ [r] }
def Ledger.addNative (l : Ledger) (r : NativeRecord) : Ledger :=
  { l with native := l.native ++ [r] }
def Ledger.addOpening (l : Ledger) (r : OpeningRecord) : Ledger :=
  { l with openings := l.openings ++ [r] }
def Ledger.addEdge (l : Ledger) (r : ReprEqRecord) : Ledger :=
  { l with edges := l.edges ++ [r] }

structure RootAnchor (ledger : Ledger) where
  root : RootRecord
  present : root ∈ ledger.roots

inductive Phase where
  | start
  | publicBound (ledger : Ledger)
  | rooted (round : Nat) (ledger : Ledger) (anchor : RootAnchor ledger)
  | roundChallenged (round : Nat) (ledger : Ledger)
  | queryChallenged (rounds : Nat) (ledger : Ledger)
  | openings (rounds : Nat) (ledger : Ledger)

def Phase.ledger : Phase -> Ledger
  | .start => .empty
  | .publicBound ledger => ledger
  | .rooted _ ledger _ => ledger
  | .roundChallenged _ ledger => ledger
  | .queryChallenged _ ledger => ledger
  | .openings _ ledger => ledger

/-- The final checker retains the exact proposition decided by its Boolean.
The proposition is selected by the Lean-authored plan before execution; native
reply bytes cannot alter it.  Keeping the reflection theorem in the terminal
object prevents an accepted trace from degenerating into an untyped `true`. -/
structure FinalChecker (ledger : Ledger) where
  checkerId : Digest
  Statement : Prop
  check : Bool
  check_iff : check = true <-> Statement

/-- Native constructors have one fixed `next`; reply bytes do not occur in its
type.  Only controller-derived challenge values may index a continuation. -/
inductive Plan (transcriptDomain : Digest) : Phase -> Type 1 where
  | bindPublic (context : List UInt8)
      (next : Plan transcriptDomain (.publicBound .empty)) :
      Plan transcriptDomain .start
  | bindFirstRoot
      {Semantic Representation Domain : Type}
      {port : ColumnPort Semantic Representation Domain}
      {scheme : CommitmentScheme port}
      (column : BoundColumn port scheme)
      (next : Plan transcriptDomain
        (.rooted 0 (Ledger.empty.addRoot column.rootRecord)
          ⟨column.rootRecord, by simp [Ledger.addRoot, Ledger.empty]⟩)) :
      Plan transcriptDomain (.publicBound .empty)
  | bindAdditionalRoot
      {round : Nat} {ledger : Ledger} {anchor : RootAnchor ledger}
      {Semantic Representation Domain : Type}
      {port : ColumnPort Semantic Representation Domain}
      {scheme : CommitmentScheme port}
      (column : BoundColumn port scheme)
      (next : Plan transcriptDomain
        (.rooted round (ledger.addRoot column.rootRecord)
          ⟨column.rootRecord, by simp [Ledger.addRoot]⟩)) :
      Plan transcriptDomain (.rooted round ledger anchor)
  | drawRound
      {round : Nat} {ledger : Ledger} {anchor : RootAnchor ledger}
      (next : (coin : Digest) -> Plan transcriptDomain
        (.roundChallenged round (ledger.addDraw
          ⟨⟨transcriptDomain, .roundChallenge, ledger.draws.length⟩, coin⟩))) :
      Plan transcriptDomain (.rooted round ledger anchor)
  | runRoundNative
      {round : Nat} {ledger : Ledger} (call : NativeCall)
      (next : Plan transcriptDomain
        (.roundChallenged round (ledger.addNative call.record))) :
      Plan transcriptDomain (.roundChallenged round ledger)
  | bindNextRoundRoot
      {round : Nat} {ledger : Ledger}
      {Semantic Representation Domain : Type}
      {port : ColumnPort Semantic Representation Domain}
      {scheme : CommitmentScheme port}
      (column : BoundColumn port scheme)
      (next : Plan transcriptDomain
        (.rooted (round + 1) (ledger.addRoot column.rootRecord)
          ⟨column.rootRecord, by simp [Ledger.addRoot]⟩)) :
      Plan transcriptDomain (.roundChallenged round ledger)
  | drawQuery
      {round : Nat} {ledger : Ledger} {anchor : RootAnchor ledger}
      (next : (coin : Digest) -> Plan transcriptDomain
        (.queryChallenged round (ledger.addDraw
          ⟨⟨transcriptDomain, .queryChallenge, ledger.draws.length⟩, coin⟩))) :
      Plan transcriptDomain (.rooted round ledger anchor)
  | runQueryNative
      {rounds : Nat} {ledger : Ledger} (call : NativeCall)
      (next : Plan transcriptDomain
        (.queryChallenged rounds (ledger.addNative call.record))) :
      Plan transcriptDomain (.queryChallenged rounds ledger)
  | bindFirstOpening
      {rounds : Nat} {ledger : Ledger}
      {Semantic Representation Domain : Type}
      {port : ColumnPort Semantic Representation Domain}
      {scheme : CommitmentScheme port}
      {column : BoundColumn port scheme}
      (opening : ColumnOpening column)
      (rootPresent : column.rootRecord ∈ ledger.roots)
      (next : Plan transcriptDomain
        (.openings rounds (ledger.addOpening opening.record))) :
      Plan transcriptDomain (.queryChallenged rounds ledger)
  | bindAdditionalOpening
      {rounds : Nat} {ledger : Ledger}
      {Semantic Representation Domain : Type}
      {port : ColumnPort Semantic Representation Domain}
      {scheme : CommitmentScheme port}
      {column : BoundColumn port scheme}
      (opening : ColumnOpening column)
      (rootPresent : column.rootRecord ∈ ledger.roots)
      (next : Plan transcriptDomain
        (.openings rounds (ledger.addOpening opening.record))) :
      Plan transcriptDomain (.openings rounds ledger)
  | bindReprEq
      {rounds : Nat} {ledger : Ledger}
      {SourceSemantic SourceRepresentation SourceDomain : Type}
      {sourcePort : ColumnPort SourceSemantic SourceRepresentation SourceDomain}
      {sourceScheme : CommitmentScheme sourcePort}
      {sourceColumn : BoundColumn sourcePort sourceScheme}
      {TargetSemantic TargetRepresentation TargetDomain : Type}
      {targetPort : ColumnPort TargetSemantic TargetRepresentation TargetDomain}
      {targetScheme : CommitmentScheme targetPort}
      {targetColumn : BoundColumn targetPort targetScheme}
      {spec : ReprEqSpec SourceSemantic TargetSemantic}
      {source : ColumnOpening sourceColumn}
      {target : ColumnOpening targetColumn}
      (edge : ReprEqEdge spec source target)
      (sourcePresent : source.record ∈ ledger.openings)
      (targetPresent : target.record ∈ ledger.openings)
      (next : Plan transcriptDomain
        (.openings rounds (ledger.addEdge edge.record))) :
      Plan transcriptDomain (.openings rounds ledger)
  | finalize {rounds : Nat} {ledger : Ledger}
      (checker : FinalChecker ledger) :
      Plan transcriptDomain (.openings rounds ledger)

/-! ## Execution trace and terminal attestation -/

/-- This indexed trace is the provenance object.  Its constructors record the
typed root/opening/edge witnesses and exact checked native call which created
each terminal slot. -/
inductive ExecutionTrace
    {State : Type} (portal : GlobalTranscriptPortal State)
    (transcriptDomain : Digest) :
    TranscriptState portal -> Ledger -> Prop where
  | initial (seed : State) :
      ExecutionTrace portal transcriptDomain
        (TranscriptState.initial portal seed) .empty
  | absorbPublic
      {transcript : TranscriptState portal} {ledger : Ledger}
      (prior : ExecutionTrace portal transcriptDomain transcript ledger)
      (context : List UInt8) :
      ExecutionTrace portal transcriptDomain
        (transcript.absorb (.publicContext transcriptDomain context)) ledger
  | root
      {transcript : TranscriptState portal} {ledger : Ledger}
      (prior : ExecutionTrace portal transcriptDomain transcript ledger)
      {Semantic Representation Domain : Type}
      {port : ColumnPort Semantic Representation Domain}
      {scheme : CommitmentScheme port}
      (column : BoundColumn port scheme) :
      ExecutionTrace portal transcriptDomain
        (transcript.absorb (.root column.rootRecord))
        (ledger.addRoot column.rootRecord)
  | draw
      {transcript : TranscriptState portal} {ledger : Ledger}
      (prior : ExecutionTrace portal transcriptDomain transcript ledger)
      (role : DrawRole) (ordinal : Nat)
      (draw : DerivedChallenge portal) (next : TranscriptState portal)
      (resultExact : transcript.draw ⟨transcriptDomain, role, ordinal⟩ =
        (draw, next)) :
      ExecutionTrace portal transcriptDomain next (ledger.addDraw draw.record)
  | native
      {transcript : TranscriptState portal} {ledger : Ledger}
      (prior : ExecutionTrace portal transcriptDomain transcript ledger)
      (call : NativeCall) (bytes : List UInt8)
      (accepted : call.acceptsReply bytes = true) :
      ExecutionTrace portal transcriptDomain
        (transcript.absorb (.nativeReply call.record))
        (ledger.addNative call.record)
  | opening
      {transcript : TranscriptState portal} {ledger : Ledger}
      (prior : ExecutionTrace portal transcriptDomain transcript ledger)
      {Semantic Representation Domain : Type}
      {port : ColumnPort Semantic Representation Domain}
      {scheme : CommitmentScheme port}
      {column : BoundColumn port scheme}
      (opening : ColumnOpening column)
      (rootPresent : column.rootRecord ∈ ledger.roots) :
      ExecutionTrace portal transcriptDomain
        (transcript.absorb (.opening opening.record))
        (ledger.addOpening opening.record)
  | reprEq
      {transcript : TranscriptState portal} {ledger : Ledger}
      (prior : ExecutionTrace portal transcriptDomain transcript ledger)
      {SourceSemantic SourceRepresentation SourceDomain : Type}
      {sourcePort : ColumnPort SourceSemantic SourceRepresentation SourceDomain}
      {sourceScheme : CommitmentScheme sourcePort}
      {sourceColumn : BoundColumn sourcePort sourceScheme}
      {TargetSemantic TargetRepresentation TargetDomain : Type}
      {targetPort : ColumnPort TargetSemantic TargetRepresentation TargetDomain}
      {targetScheme : CommitmentScheme targetPort}
      {targetColumn : BoundColumn targetPort targetScheme}
      {spec : ReprEqSpec SourceSemantic TargetSemantic}
      {source : ColumnOpening sourceColumn}
      {target : ColumnOpening targetColumn}
      (edge : ReprEqEdge spec source target)
      (sourcePresent : source.record ∈ ledger.openings)
      (targetPresent : target.record ∈ ledger.openings) :
      ExecutionTrace portal transcriptDomain
        (transcript.absorb (.representationEdge edge.record))
        (ledger.addEdge edge.record)

structure RuntimeState
    {State : Type} (portal : GlobalTranscriptPortal State)
    (transcriptDomain : Digest) (ledger : Ledger) where
  transcript : TranscriptState portal
  trace : ExecutionTrace portal transcriptDomain transcript ledger

def RuntimeState.ledger
    {State : Type} {portal : GlobalTranscriptPortal State}
    {transcriptDomain : Digest} {ledger : Ledger}
    (_state : RuntimeState portal transcriptDomain ledger) : Ledger :=
  ledger

def RuntimeState.initial {State : Type}
    (portal : GlobalTranscriptPortal State) (transcriptDomain : Digest)
    (seed : State) : RuntimeState portal transcriptDomain .empty :=
  ⟨TranscriptState.initial portal seed, .initial seed⟩

structure TerminalAttestation
    {State : Type} (portal : GlobalTranscriptPortal State)
    (transcriptDomain : Digest)
    (roots : List RootRecord) (draws : List DrawRecord)
    (native : List NativeRecord) (openings : List OpeningRecord)
    (edges : List ReprEqRecord) where
  transcript : TranscriptState portal
  trace : ExecutionTrace portal transcriptDomain transcript
    ⟨roots, draws, native, openings, edges⟩
  checker : FinalChecker ⟨roots, draws, native, openings, edges⟩
  finalAccepted : checker.check = true

/-- The terminal proposition actually proved by an accepted controller run. -/
def TerminalAttestation.FinalStatement
    {State : Type} {portal : GlobalTranscriptPortal State}
    {transcriptDomain : Digest}
    {roots : List RootRecord} {draws : List DrawRecord}
    {native : List NativeRecord} {openings : List OpeningRecord}
    {edges : List ReprEqRecord}
    (attestation : TerminalAttestation portal transcriptDomain
      roots draws native openings edges) : Prop :=
  attestation.checker.Statement

/-- Acceptance carries semantic evidence, not only a successful Boolean. -/
theorem TerminalAttestation.finalStatement_proved
    {State : Type} {portal : GlobalTranscriptPortal State}
    {transcriptDomain : Digest}
    {roots : List RootRecord} {draws : List DrawRecord}
    {native : List NativeRecord} {openings : List OpeningRecord}
    {edges : List ReprEqRecord}
    (attestation : TerminalAttestation portal transcriptDomain
      roots draws native openings edges) :
    attestation.FinalStatement :=
  attestation.checker.check_iff.mp attestation.finalAccepted

inductive CheckFailure where
  | nativeReplyRejected (callSlotId : Digest)
  | finalCheckRejected (checkerId : Digest)
deriving DecidableEq, Repr

inductive Outcome (Error : Type) {State : Type}
    (portal : GlobalTranscriptPortal State) (transcriptDomain : Digest) where
  | blocked (error : Error)
  | rejected (reason : CheckFailure)
  | verified
      {roots : List RootRecord} {draws : List DrawRecord}
      {native : List NativeRecord} {openings : List OpeningRecord}
      {edges : List ReprEqRecord}
      (attestation : TerminalAttestation portal transcriptDomain
        roots draws native openings edges)

def Outcome.IsVerified
    {Error State : Type} {portal : GlobalTranscriptPortal State}
    {transcriptDomain : Digest} : Outcome Error portal transcriptDomain -> Prop
  | .verified _ => True
  | _ => False

/-- The recursive call always receives the syntactically fixed continuation.
Only the Lean-owned draw result is exposed to a continuation. -/
def run
    {Error State : Type}
    (portal : GlobalTranscriptPortal State) (runner : NativeRunner Error)
    (transcriptDomain : Digest) :
    {phase : Phase} -> Plan transcriptDomain phase ->
      RuntimeState portal transcriptDomain phase.ledger ->
      Outcome Error portal transcriptDomain
  | _, .bindPublic context next, state =>
      run portal runner transcriptDomain next
        ⟨state.transcript.absorb (.publicContext transcriptDomain context),
          .absorbPublic state.trace context⟩
  | _, .bindFirstRoot column next, state =>
      run portal runner transcriptDomain next
        ⟨state.transcript.absorb (.root column.rootRecord),
          .root state.trace column⟩
  | _, .bindAdditionalRoot column next, state =>
      run portal runner transcriptDomain next
        ⟨state.transcript.absorb (.root column.rootRecord),
          .root state.trace column⟩
  | _, .drawRound next, state =>
      let result := state.transcript.draw
        ⟨transcriptDomain, .roundChallenge, state.ledger.draws.length⟩
      run portal runner transcriptDomain (next result.1.coin)
        ⟨result.2, .draw state.trace .roundChallenge
          state.ledger.draws.length result.1 result.2 rfl⟩
  | _, .runRoundNative call next, state =>
      match runner call with
      | .error error => .blocked error
      | .ok bytes =>
          if accepted : call.acceptsReply bytes = true then
            run portal runner transcriptDomain next
              ⟨state.transcript.absorb (.nativeReply call.record),
                .native state.trace call bytes accepted⟩
          else .rejected (.nativeReplyRejected call.callSlotId)
  | _, .bindNextRoundRoot column next, state =>
      run portal runner transcriptDomain next
        ⟨state.transcript.absorb (.root column.rootRecord),
          .root state.trace column⟩
  | _, .drawQuery next, state =>
      let result := state.transcript.draw
        ⟨transcriptDomain, .queryChallenge, state.ledger.draws.length⟩
      run portal runner transcriptDomain (next result.1.coin)
        ⟨result.2, .draw state.trace .queryChallenge
          state.ledger.draws.length result.1 result.2 rfl⟩
  | _, .runQueryNative call next, state =>
      match runner call with
      | .error error => .blocked error
      | .ok bytes =>
          if accepted : call.acceptsReply bytes = true then
            run portal runner transcriptDomain next
              ⟨state.transcript.absorb (.nativeReply call.record),
                .native state.trace call bytes accepted⟩
          else .rejected (.nativeReplyRejected call.callSlotId)
  | _, .bindFirstOpening opening rootPresent next, state =>
      run portal runner transcriptDomain next
        ⟨state.transcript.absorb (.opening opening.record),
          .opening state.trace opening rootPresent⟩
  | _, .bindAdditionalOpening opening rootPresent next, state =>
      run portal runner transcriptDomain next
        ⟨state.transcript.absorb (.opening opening.record),
          .opening state.trace opening rootPresent⟩
  | _, .bindReprEq edge sourcePresent targetPresent next, state =>
      run portal runner transcriptDomain next
        ⟨state.transcript.absorb (.representationEdge edge.record),
          .reprEq state.trace edge sourcePresent targetPresent⟩
  | _, .finalize checker, state =>
      if accepted : checker.check = true then
        .verified
          { transcript := state.transcript
            trace := state.trace
            checker := checker
            finalAccepted := accepted }
      else .rejected (.finalCheckRejected checker.checkerId)

def execute
    {Error State : Type}
    (portal : GlobalTranscriptPortal State) (runner : NativeRunner Error)
    (transcriptDomain : Digest) (plan : Plan transcriptDomain .start)
    (seed : State) : Outcome Error portal transcriptDomain :=
  run portal runner transcriptDomain plan
    (RuntimeState.initial portal transcriptDomain seed)

/-! ## Structural teeth -/

theorem empty_has_no_root_anchor : ¬ Nonempty (RootAnchor Ledger.empty) := by
  rintro ⟨anchor⟩
  simpa [Ledger.empty] using anchor.present

theorem challenge_before_root_unrepresentable :
    ¬ Nonempty (RootAnchor Ledger.empty) :=
  empty_has_no_root_anchor

@[simp] theorem native_error_blocks_query
    {Error State : Type}
    {portal : GlobalTranscriptPortal State} {runner : NativeRunner Error}
    {transcriptDomain : Digest} {rounds : Nat} {ledger : Ledger}
    (call : NativeCall)
    (next : Plan transcriptDomain
      (.queryChallenged rounds (ledger.addNative call.record)))
    (state : RuntimeState portal transcriptDomain ledger)
    (error : Error) (failed : runner call = .error error) :
    run portal runner transcriptDomain (.runQueryNative call next) state =
      .blocked error := by
  simp [run, failed]

theorem native_error_cannot_accept_query
    {Error State : Type}
    {portal : GlobalTranscriptPortal State} {runner : NativeRunner Error}
    {transcriptDomain : Digest} {rounds : Nat} {ledger : Ledger}
    (call : NativeCall)
    (next : Plan transcriptDomain
      (.queryChallenged rounds (ledger.addNative call.record)))
    (state : RuntimeState portal transcriptDomain ledger)
    (error : Error) (failed : runner call = .error error) :
    ¬ (run portal runner transcriptDomain
      (.runQueryNative call next) state).IsVerified := by
  rw [native_error_blocks_query call next state error failed]
  simp [Outcome.IsVerified]

/-! ## Tower256-shaped executable non-vacuity schedule -/

namespace Tower256Example

abbrev Tower256Value := Fin (2 ^ 256)
abbrev SingletonDomain := Fin 1

def finUnaryCodec (size : Nat) : LawfulCodec (Fin size) where
  encode value := List.replicate value.val 0
  decode bytes :=
    if bytes.all (fun byte => byte == 0) then
      if inBounds : bytes.length < size then some ⟨bytes.length, inBounds⟩ else none
    else none
  decode_encode := by
    intro value
    simp [value.isLt]

def digestUnaryCodec : LawfulCodec Digest where
  encode value := List.replicate value.value 0
  decode bytes :=
    if bytes.all (fun byte => byte == 0) then some ⟨bytes.length⟩ else none
  decode_encode := by intro value; simp

def id (value : Nat) : Digest := ⟨value⟩

def towerCarrier : CarrierProfile :=
  .gf2Tower (id 7205) (id 7210) (id 7211) (id 7212) 256

def towerCodecPin : CodecPin := ⟨id 7221, id 7231, 1⟩
def singletonCodecPin : CodecPin := ⟨id 7222, id 7232, 1⟩

def towerPort : ColumnPort Tower256Value Tower256Value SingletonDomain where
  slotId := id 7240
  role := .checkpoint
  semanticTypeId := id 7231
  representationId := id 7212
  carrier := towerCarrier
  semanticCodecPin := towerCodecPin
  representationCodecPin := towerCodecPin
  domainId := id 7241
  domainCodecPin := singletonCodecPin
  semanticCodec := finUnaryCodec (2 ^ 256)
  representationCodec := finUnaryCodec (2 ^ 256)
  domainCodec := finUnaryCodec 1
  represent := fun value => value

def towerCommitment : CommitmentScheme towerPort where
  suiteId := id 7250
  proofCodecPin := towerCodecPin
  commit := fun column => id ((column ⟨0, by decide⟩).val + 1)
  openAt := fun _ _ => []
  verifyOpening := fun root _ value proof =>
    decide (root = id (value.val + 1) ∧ proof = [])
  verifyOpening_commit := by
    intro column index
    have hindex : index = (0 : SingletonDomain) := Subsingleton.elim _ _
    subst index
    simp

/-- The tiny executable example also carries a proved position-binding law,
so the controller-to-Loom adapter is inhabited rather than premise-only. -/
def towerBindingCommitment : BindingCommitmentScheme towerPort where
  toCommitmentScheme := towerCommitment
  binding := by
    intro root index left right leftProof rightProof hleft hright
    have leftBound :
        root = id (left.val + 1) ∧ leftProof = [] := by
      simpa [towerCommitment] using hleft
    have rightBound :
        root = id (right.val + 1) ∧ rightProof = [] := by
      simpa [towerCommitment] using hright
    have hroot : id (left.val + 1) = id (right.val + 1) :=
      leftBound.1.symm.trans rightBound.1
    have hnat : left.val + 1 = right.val + 1 :=
      congrArg Digest.value hroot
    have hvalue : left.val = right.val := by
      omega
    exact Fin.ext hvalue

theorem towerBinding_toLoom_commit_exact
    (column : SingletonDomain -> Tower256Value) :
    towerBindingCommitment.toLoom.commit column =
      towerCommitment.commit column :=
  rfl

def zeroColumn : BoundColumn towerPort towerCommitment where
  semantic := fun _ => 0
  represented := fun _ => 0
  representationExact := fun _ => rfl

def zeroOpening : ColumnOpening zeroColumn :=
  zeroColumn.honestOpening (id 7260) 0

def zeroSameOpening : ReprEqEdge
    (sameOpeningSpec Tower256Value (id 7301)) zeroOpening zeroOpening where
  checked := by decide

def nativeCall (challenge : Digest) : NativeCall where
  Input := Digest
  Output := Tower256Value
  outputDecidableEq := inferInstance
  callSlotId := id 7270
  kind := .transform
  carrierProfileId := towerCarrier.id
  inputCodecPin := ⟨id 7223, id 7233, 1⟩
  outputCodecPin := towerCodecPin
  inputCodec := digestUnaryCodec
  outputCodec := finUnaryCodec (2 ^ 256)
  input := challenge
  claimedOutput := 0
  leanCheck := fun _ output => decide (output = 0)

def transcriptDomain : Digest := id 7280

def finalChecker (ledger : Ledger) : FinalChecker ledger where
  checkerId := id 7290
  Statement :=
    ledger.roots.length = 1 ∧ ledger.draws.length = 1 ∧
      ledger.native.length = 1 ∧ ledger.openings.length = 1 ∧
      ledger.edges.length = 1
  check := decide
    (ledger.roots.length = 1 ∧ ledger.draws.length = 1 ∧
      ledger.native.length = 1 ∧ ledger.openings.length = 1 ∧
      ledger.edges.length = 1)
  check_iff := by simp

def plan : Plan transcriptDomain .start :=
  .bindPublic [] <|
  .bindFirstRoot zeroColumn <|
  .drawQuery fun challenge =>
  .runQueryNative (nativeCall challenge) <|
  .bindFirstOpening zeroOpening
    (by simp [Ledger.addRoot, Ledger.addDraw, Ledger.addNative, Ledger.empty]) <|
  .bindReprEq zeroSameOpening
    (by simp [Ledger.addOpening])
    (by simp [Ledger.addOpening]) <|
  .finalize (finalChecker _)

def portal : GlobalTranscriptPortal (List GlobalFrame) where
  absorb state frame := state ++ [frame]
  squeeze state label :=
    (id (state.length + label.ordinal +
      match label.role with
      | .roundChallenge => 1
      | .queryChallenge => 2), state)
  xof state label := id (state.length + label.ordinal +
    match label.role with
    | .roundChallenge => 1
    | .queryChallenge => 2)
  squeeze_xof_law := by intros; rfl

def runner : NativeRunner Empty := fun call =>
  .ok (call.outputCodec.encode call.claimedOutput)

/-- Commitment -> controller challenge -> checked opaque work -> authenticated
opening -> typed same-opening edge -> Lean terminal attestation. -/
theorem concrete_schedule_is_nonvacuous :
    (execute portal runner transcriptDomain plan []).IsVerified := by
  simp [execute, plan, run, runner, NativeCall.acceptsReply, nativeCall,
    finUnaryCodec, finalChecker, Outcome.IsVerified, RuntimeState.ledger,
    Ledger.empty, Ledger.addRoot, Ledger.addDraw, Ledger.addNative,
    Ledger.addOpening, Ledger.addEdge]

end Tower256Example

#print axioms challenge_before_root_unrepresentable
#print axioms native_error_cannot_accept_query
#print axioms Tower256Example.towerBinding_toLoom_commit_exact
#print axioms Tower256Example.concrete_schedule_is_nonvacuous

end Minidregg.Compiler.AuthenticatedColumnPlan
