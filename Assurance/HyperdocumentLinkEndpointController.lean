/-
# Assurance.HyperdocumentLinkEndpointController -- one link, bytes to bytes

This module exposes the concrete forward-link publication as one first-order
endpoint shared by human and agent callers.  The origin is audit data only:
both origins pass the same request bytes through the same Lean codecs, catalog
checks, accepted publication, guarded recovery controller, canonical query,
and response codec.

The native boundary may return only bytes or an opaque error.  Lean decodes
the endpoint request, the bounded-page catalog, the Hyperdocument declaration,
and the recovery frames.  Success returns only the canonical `LinkRecord`
encoding whose exact value is proved by `HyperdocumentLinkReopenWitness`.

No result here says an OS read real storage, that consensus finalized the
history head, or that a UI rendered the reply.  Those remain separate explicit
deployment obligations at the end of the module.
-/
import Assurance.HyperdocumentLinkFramedRecovery
import Assurance.HyperdocumentLinkReopenWitness
import Compiler.BoundedPageExtensionCatalog
import Compiler.HyperdocumentCodec

namespace Minidregg.Assurance.HyperdocumentLinkEndpointController

open Minidregg.Compiler
open Minidregg.Compiler.BoundedPageExtensionCatalog
open Minidregg.Compiler.FramedWalRecoveryController
open Minidregg.Compiler.HyperdocumentCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

namespace Publication

noncomputable abbrev declarationCodec :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.declarationCodec
noncomputable abbrev linkDeclaration :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.linkDeclaration
noncomputable abbrev linkIntent :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.linkIntent
abbrev contentCellId :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.contentCellId
noncomputable abbrev linkAccepted :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.linkAccepted
noncomputable abbrev commit :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.commit

namespace Genesis

abbrev documentId :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.Genesis.documentId
noncomputable abbrev authorityPre :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.Genesis.authorityPre

end Genesis

end Publication

namespace Reopen

noncomputable abbrev record :=
  Minidregg.Assurance.HyperdocumentLinkReopenWitness.record
noncomputable abbrev query :=
  Minidregg.Assurance.HyperdocumentLinkReopenWitness.query
abbrev query_exact :=
  Minidregg.Assurance.HyperdocumentLinkReopenWitness.query_exact

end Reopen

namespace Recovery

abbrev rootBytes :=
  Minidregg.Assurance.HyperdocumentLinkFramedRecovery.rootBytes
noncomputable abbrev checkpoint :=
  Minidregg.Assurance.HyperdocumentLinkFramedRecovery.checkpoint
noncomputable abbrev staleCheckpoint :=
  Minidregg.Assurance.HyperdocumentLinkFramedRecovery.staleCheckpoint
noncomputable abbrev controller :=
  Minidregg.Assurance.HyperdocumentLinkFramedRecovery.controller
noncomputable abbrev reader :=
  Minidregg.Assurance.HyperdocumentLinkFramedRecovery.reader
abbrev controller_decodes_exact_intent :=
  Minidregg.Assurance.HyperdocumentLinkFramedRecovery.controller_decodes_exact_intent
abbrev controller_run_recovers :=
  Minidregg.Assurance.HyperdocumentLinkFramedRecovery.controller_run_recovers
abbrev recovered_link_post_bytes :=
  Minidregg.Assurance.HyperdocumentLinkFramedRecovery.recovered_link_post_bytes
abbrev stale_authority_controller_rejected :=
  Minidregg.Assurance.HyperdocumentLinkFramedRecovery.stale_authority_controller_rejected

end Recovery

set_option autoImplicit false

noncomputable section

/-! ## One origin-neutral first-order request -/

inductive Origin where
  | human
  | agent
  deriving DecidableEq, Repr

/-- The request carrier remains ordinary first-order data.  Inner catalog and
declaration bytes are decoded by their own pinned codecs after this envelope
has decoded. -/
structure SubmitRequest where
  endpointVersion : Nat
  target : DocumentId
  expectedAuthorityRoot : Digest
  catalogBytes : List UInt8
  declarationBytes : List UInt8
  deriving DecidableEq

abbrev SubmitTuple :=
  Nat × DocumentId × Digest × List UInt8 × List UInt8

def submitTupleStream : StreamCodec SubmitTuple :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product (identifierStream .v1 .document)
      (StreamCodec.product digestStream
        (StreamCodec.product bytesStream bytesStream)))

def submitTuple (request : SubmitRequest) : SubmitTuple :=
  ⟨request.endpointVersion, request.target, request.expectedAuthorityRoot,
    request.catalogBytes, request.declarationBytes⟩

def submitOfTuple (wire : SubmitTuple) : SubmitRequest where
  endpointVersion := wire.1
  target := wire.2.1
  expectedAuthorityRoot := wire.2.2.1
  catalogBytes := wire.2.2.2.1
  declarationBytes := wire.2.2.2.2

@[simp] theorem submitOfTuple_tuple (request : SubmitRequest) :
    submitOfTuple (submitTuple request) = request := by
  cases request
  rfl

def submitStream : StreamCodec SubmitRequest :=
  StreamCodec.xmap submitTupleStream submitTuple submitOfTuple
    submitOfTuple_tuple

def submitCodec : LawfulCodec SubmitRequest := submitStream.toLawful

/-! ## Canonical response codec -/

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

noncomputable def linkRecordCodec : LawfulCodec LinkRecord :=
  linkRecordStream.toLawful

/-! ## Lean-owned endpoint -/

def endpointVersion : Nat := 1

inductive Failure (NativeError : Type) where
  | native (error : NativeError)
  | malformedRequest
  | wrongVersion
  | wrongTarget
  | staleAuthority
  | wrongCatalog
  | wrongDeclaration
  | malformedStorage
  deriving Repr

/-- Origin is accepted for audit/routing, but is deliberately not inspected by
the semantic controller. -/
def decodeRequest (_origin : Origin) (bytes : List UInt8) :
    Option SubmitRequest :=
  submitCodec.decode bytes

def decodedDeclaration (origin : Origin) (bytes : List UInt8) :
    Option HyperdocumentOperations.Declaration := do
  let request ← decodeRequest origin bytes
  Publication.declarationCodec.decode request.declarationBytes

theorem origin_cannot_change_declaration
    (left right : Origin) (bytes : List UInt8) :
    decodedDeclaration left bytes = decodedDeclaration right bytes :=
  rfl

/-- Semantic handling after the outer request codec has succeeded. -/
noncomputable def runRequest {NativeError : Type}
    (current : DataSnapshot Recovery.rootBytes)
    (request : SubmitRequest)
    (reader : Unit → Except NativeError (List UInt8)) :
    Except (Failure NativeError) (List UInt8) :=
  if request.endpointVersion ≠ endpointVersion then
    .error .wrongVersion
  else if request.target ≠ Publication.Genesis.documentId then
    .error .wrongTarget
  else if request.expectedAuthorityRoot ≠
      Publication.Genesis.authorityPre.root then
    .error .staleAuthority
  else
    match catalogCodec.decode request.catalogBytes with
    | none => .error .wrongCatalog
    | some catalog =>
        if catalog ≠ deployedCatalog then .error .wrongCatalog
        else
          match Publication.declarationCodec.decode
              request.declarationBytes with
          | none => .error .malformedRequest
          | some _declaration =>
              if request.declarationBytes ≠
                  Publication.declarationCodec.encode
                    Publication.linkDeclaration then
                .error .wrongDeclaration
              else
                match FramedWalRecoveryController.run Recovery.controller
                    current reader () with
                | .error (.native error) => .error (.native error)
                | .error (.wire _) => .error .malformedStorage
                | .error (.recovery _) => .error .malformedStorage
                | .ok verified =>
                    if verified.snapshot.canonicalBytes
                        Publication.contentCellId =
                        (Publication.commit.post .content).bytes then
                      .ok (linkRecordCodec.encode Reopen.record)
                    else
                      .error .malformedStorage

/-- Run against one exact coherent current snapshot and one opaque native
reader.  Only the reader can produce a native error; every semantic result is
minted after Lean decoding and guarded replay. -/
noncomputable def runAt {NativeError : Type}
    (current : DataSnapshot Recovery.rootBytes)
    (_origin : Origin)
    (requestBytes : List UInt8)
    (reader : Unit → Except NativeError (List UInt8)) :
    Except (Failure NativeError) (List UInt8) :=
  match submitCodec.decode requestBytes with
  | none => .error .malformedRequest
  | some request => runRequest current request reader

theorem origin_cannot_change_result {NativeError : Type}
    (current : DataSnapshot Recovery.rootBytes)
    (left right : Origin) (requestBytes : List UInt8)
    (reader : Unit → Except NativeError (List UInt8)) :
    runAt current left requestBytes reader =
      runAt current right requestBytes reader :=
  rfl

/-! ## Closed accepted endpoint -/

def honestRequest : SubmitRequest where
  endpointVersion := endpointVersion
  target := Publication.Genesis.documentId
  expectedAuthorityRoot := Publication.Genesis.authorityPre.root
  catalogBytes := catalogCodec.encode deployedCatalog
  declarationBytes :=
    Publication.declarationCodec.encode Publication.linkDeclaration

def honestRequestBytes : List UInt8 := submitCodec.encode honestRequest

noncomputable def resultBytes : List UInt8 :=
  linkRecordCodec.encode Reopen.record

@[simp] theorem honest_request_decodes :
    submitCodec.decode honestRequestBytes = some honestRequest :=
  submitCodec.decode_encode honestRequest

@[simp] theorem catalog_decodes_deployed :
    catalogCodec.decode (catalogCodec.encode deployedCatalog) =
      some deployedCatalog :=
  catalogCodec.decode_encode deployedCatalog

@[simp] theorem declaration_decodes_link :
    Publication.declarationCodec.decode
        (Publication.declarationCodec.encode Publication.linkDeclaration) =
      some Publication.linkDeclaration :=
  Publication.declarationCodec.decode_encode Publication.linkDeclaration

@[simp] theorem declaration_decodes (declaration :
    HyperdocumentOperations.Declaration) :
    Publication.declarationCodec.decode
        (Publication.declarationCodec.encode declaration) =
      some declaration :=
  Publication.declarationCodec.decode_encode declaration

@[simp] theorem result_decodes_exact_link :
    linkRecordCodec.decode resultBytes = some Reopen.record :=
  linkRecordCodec.decode_encode Reopen.record

theorem recovery_run_stale :
    FramedWalRecoveryController.run Recovery.controller
      Recovery.staleCheckpoint Recovery.reader () =
      .error (.recovery (.rejected .staleReadGuard)) := by
  change FramedWalRecoveryController.run
      Minidregg.Assurance.HyperdocumentLinkFramedRecovery.controller
      Minidregg.Assurance.HyperdocumentLinkFramedRecovery.staleCheckpoint
      Minidregg.Assurance.HyperdocumentLinkFramedRecovery.reader () = _
  unfold FramedWalRecoveryController.run
    Minidregg.Assurance.HyperdocumentLinkFramedRecovery.reader
  simp only
  split
  next reason failed =>
    rw [Minidregg.Assurance.HyperdocumentLinkFramedRecovery.controller_decodes_exact_intent]
      at failed
    contradiction
  next intents decoded =>
    have intentsExact : intents =
        [Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent] := by
      rw [Minidregg.Assurance.HyperdocumentLinkFramedRecovery.controller_decodes_exact_intent]
        at decoded
      exact (Except.ok.inj decoded).symm
    subst intents
    split
    next reason failed =>
      rw [Minidregg.Assurance.HyperdocumentLinkFramedRecovery.stale_authority_controller_rejected]
        at failed
      have reasonExact := Except.error.inj failed
      subst reason
      rfl
    next snapshot replayed =>
      rw [Minidregg.Assurance.HyperdocumentLinkFramedRecovery.stale_authority_controller_rejected]
        at replayed
      contradiction

@[simp] theorem honest_run_accepts (origin : Origin) :
    runAt Recovery.checkpoint origin honestRequestBytes Recovery.reader =
      .ok resultBytes := by
  simp only [runAt, honest_request_decodes]
  simp [runRequest, honestRequest, endpointVersion,
    Publication.Genesis.documentId,
    Publication.Genesis.authorityPre,
    resultBytes]

/-- Endpoint success returns the exact same concrete record as the canonical
post query; response decoding cannot drift from the retained reopen witness. -/
theorem honest_end_to_end (origin : Origin) :
    runAt Recovery.checkpoint origin honestRequestBytes Recovery.reader =
        .ok resultBytes ∧
      linkRecordCodec.decode resultBytes = some Reopen.record ∧
      HyperdocumentInterface.ContentQuery.project Reopen.query
          Publication.linkAccepted.accepted.prepared.post.logical =
        some Reopen.record :=
  ⟨honest_run_accepts origin, result_decodes_exact_link, Reopen.query_exact⟩

/-! ## Lost-response recovery and exact retry -/

/-- The abstract durable sync point has already published the frame.  Losing
the response and crashing afterwards still reopens the exact atomic
root/journal installation; this is logical device-model recovery, not a claim
about a particular filesystem. -/
theorem published_frame_survives_crash :
    Minidregg.Kernel.FramedWalRefinement.DeviceState.recovered
        Minidregg.Assurance.HyperdocumentLinkFramedRecovery.walFrameCodec
        Minidregg.Assurance.HyperdocumentLinkFramedRecovery.syncedDevice =
      Minidregg.Kernel.DurableCommitProtocol.Snapshot.install
        Minidregg.Assurance.HyperdocumentLinkFramedRecovery.checkpoint.model
        Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent.erase :=
  Minidregg.Assurance.HyperdocumentLinkFramedRecovery.reopen_after_sync

/-- One origin-neutral request witnesses the full logical endpoint lifecycle:
the synced publication survives a lost response and crash, controller recovery
returns canonical response bytes, retry does not append a second event, and
both response decode and the canonical post query reopen the exact link. -/
theorem publish_lost_response_crash_recover_retry_reopen (origin : Origin) :
    Minidregg.Kernel.FramedWalRefinement.DeviceState.recovered
        Minidregg.Assurance.HyperdocumentLinkFramedRecovery.walFrameCodec
        Minidregg.Assurance.HyperdocumentLinkFramedRecovery.syncedDevice =
        Minidregg.Kernel.DurableCommitProtocol.Snapshot.install
          Minidregg.Assurance.HyperdocumentLinkFramedRecovery.checkpoint.model
          Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent.erase ∧
      runAt Recovery.checkpoint origin honestRequestBytes Recovery.reader =
        .ok resultBytes ∧
      replayAll
          (DataSnapshot.install Recovery.checkpoint
            Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent)
          [Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent] =
        .ok (DataSnapshot.install Recovery.checkpoint
          Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent) ∧
      linkRecordCodec.decode resultBytes = some Reopen.record ∧
      HyperdocumentInterface.ContentQuery.project Reopen.query
          Publication.linkAccepted.accepted.prepared.post.logical =
        some Reopen.record :=
  ⟨published_frame_survives_crash,
    honest_run_accepts origin,
    Minidregg.Assurance.HyperdocumentLinkFramedRecovery.idempotent_retry,
    result_decodes_exact_link,
    Reopen.query_exact⟩

/-! ## Executable rejection teeth -/

def malformedRequestBytes : List UInt8 := []

@[simp] theorem malformed_request_rejected (origin : Origin) :
    runAt Recovery.checkpoint origin malformedRequestBytes Recovery.reader =
      .error .malformedRequest := by
  rfl

def malformedCatalogRequest : SubmitRequest :=
  { honestRequest with catalogBytes := [] }

@[simp] theorem malformed_catalog_rejected (origin : Origin) :
    runAt Recovery.checkpoint origin
        (submitCodec.encode malformedCatalogRequest) Recovery.reader =
      .error .wrongCatalog := by
  unfold runAt
  rw [submitCodec.decode_encode]
  simp [runRequest, malformedCatalogRequest, honestRequest, endpointVersion,
    catalogCodec, decodeCatalog]

def wrongVersionRequest : SubmitRequest :=
  { honestRequest with endpointVersion := endpointVersion + 1 }

@[simp] theorem wrong_version_rejected (origin : Origin) :
    runAt Recovery.checkpoint origin (submitCodec.encode wrongVersionRequest)
        Recovery.reader = .error .wrongVersion := by
  unfold runAt
  rw [submitCodec.decode_encode]
  simp [runRequest, wrongVersionRequest, honestRequest, endpointVersion]

def wrongTarget : DocumentId := ⟨⟨999⟩⟩

theorem wrongTarget_ne : wrongTarget ≠ Publication.Genesis.documentId := by
  intro equal
  have digestEqual := congrArg Identifier.digest equal
  have valueEqual := congrArg Digest.value digestEqual
  norm_num [wrongTarget, Publication.Genesis.documentId,
    Minidregg.Theory.HyperdocumentCausalFamily.Witness.documentId] at valueEqual

def wrongTargetRequest : SubmitRequest :=
  { honestRequest with target := wrongTarget }

@[simp] theorem wrong_target_rejected (origin : Origin) :
    runAt Recovery.checkpoint origin (submitCodec.encode wrongTargetRequest)
        Recovery.reader = .error .wrongTarget := by
  unfold runAt
  rw [submitCodec.decode_encode]
  simp [runRequest, wrongTargetRequest, honestRequest, wrongTarget_ne,
    endpointVersion]

def staleAuthorityRoot : Digest :=
  ⟨Publication.Genesis.authorityPre.root.value + 1⟩

theorem staleAuthorityRoot_ne :
    staleAuthorityRoot ≠ Publication.Genesis.authorityPre.root := by
  intro equal
  have valueEqual := congrArg Digest.value equal
  simp [staleAuthorityRoot] at valueEqual

def staleAuthorityRequest : SubmitRequest :=
  { honestRequest with expectedAuthorityRoot := staleAuthorityRoot }

@[simp] theorem stale_authority_header_rejected (origin : Origin) :
    runAt Recovery.checkpoint origin
        (submitCodec.encode staleAuthorityRequest) Recovery.reader =
      .error .staleAuthority := by
  unfold runAt
  rw [submitCodec.decode_encode]
  simp [runRequest, staleAuthorityRequest, honestRequest, staleAuthorityRoot_ne,
    endpointVersion]

/-- Even an honest old header is rejected when the current coherent authority
snapshot has moved: guarded replay, not caller-supplied equality, is decisive. -/
@[simp] theorem stale_authority_snapshot_rejected (origin : Origin) :
    runAt Recovery.staleCheckpoint origin honestRequestBytes Recovery.reader =
      .error .malformedStorage := by
  simp only [runAt, honest_request_decodes]
  simp [runRequest, honestRequest, endpointVersion, recovery_run_stale]

def emptyStorageReader (_ : Unit) : Except Unit (List UInt8) := .ok []

@[simp] theorem malformed_storage_rejected (origin : Origin) :
    runAt Recovery.checkpoint origin honestRequestBytes emptyStorageReader =
      .error .malformedStorage := by
  simp only [runAt, honest_request_decodes]
  simp [runRequest, honestRequest, endpointVersion, FramedWalRecoveryController.run,
    emptyStorageReader, Controller.decodeWire]

def nativeFailureReader (_ : Unit) : Except Nat (List UInt8) := .error 404

@[simp] theorem native_error_rejected (origin : Origin) :
    runAt Recovery.checkpoint origin honestRequestBytes nativeFailureReader =
      .error (.native 404) := by
  simp only [runAt, honest_request_decodes]
  simp [runRequest, honestRequest, endpointVersion, FramedWalRecoveryController.run,
    nativeFailureReader]

def wrongDeclaration : HyperdocumentOperations.Declaration :=
  { Publication.linkDeclaration with
    intent := { Publication.linkIntent with nonce := 999 } }

theorem wrongDeclaration_ne :
    wrongDeclaration ≠ Publication.linkDeclaration := by
  intro equal
  have nonceEqual := congrArg
    (fun declaration : HyperdocumentOperations.Declaration =>
      declaration.intent.nonce) equal
  change 999 = 26 at nonceEqual
  omega

theorem wrongDeclarationBytes_ne :
    Publication.declarationCodec.encode wrongDeclaration ≠
      Publication.declarationCodec.encode Publication.linkDeclaration := by
  intro equal
  apply wrongDeclaration_ne
  have decodedEqual :=
    congrArg Publication.declarationCodec.decode equal
  rw [Publication.declarationCodec.decode_encode,
    Publication.declarationCodec.decode_encode] at decodedEqual
  exact Option.some.inj decodedEqual

def wrongDeclarationRequest : SubmitRequest :=
  { honestRequest with
    declarationBytes := Publication.declarationCodec.encode wrongDeclaration }

@[simp] theorem wrong_declaration_rejected (origin : Origin) :
    runAt Recovery.checkpoint origin
        (submitCodec.encode wrongDeclarationRequest) Recovery.reader =
      .error .wrongDeclaration := by
  unfold runAt
  rw [submitCodec.decode_encode]
  simp [runRequest, wrongDeclarationRequest, honestRequest,
    wrongDeclarationBytes_ne,
    endpointVersion]

/-! ## Explicit trust boundary -/

/-- Required before endpoint success may be advertised as physical delivery,
external finality, or a rendered UI result.  This logical controller provides
no inhabitant. -/
structure ExternalCompletion
    (PhysicalIORefined ExternallyFinal UiRendered : Prop) : Prop where
  physicalIORefined : PhysicalIORefined
  externallyFinal : ExternallyFinal
  uiRendered : UiRendered

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.HyperdocumentLinkEndpointController.honest_run_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honest_run_accepts
/-- info: 'Minidregg.Assurance.HyperdocumentLinkEndpointController.honest_end_to_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honest_end_to_end
/-- info: 'Minidregg.Assurance.HyperdocumentLinkEndpointController.publish_lost_response_crash_recover_retry_reopen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms publish_lost_response_crash_recover_retry_reopen
/-- info: 'Minidregg.Assurance.HyperdocumentLinkEndpointController.origin_cannot_change_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms origin_cannot_change_result
/-- info: 'Minidregg.Assurance.HyperdocumentLinkEndpointController.stale_authority_snapshot_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_authority_snapshot_rejected
/-- info: 'Minidregg.Assurance.HyperdocumentLinkEndpointController.native_error_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms native_error_rejected

end


end Minidregg.Assurance.HyperdocumentLinkEndpointController
