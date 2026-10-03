/- Receipt-backed continuation of an opaque governed BFV result.
This proves native candidate identity/current observation lineage only. Neither
ciphertext noise/bitness nor source/compiler correctness follows from custody. -/
import Host.BendSessionDriverJson

namespace Minidregg.Host.BendSessionCursor
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Kernel
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Host.BendSessionDriver
set_option autoImplicit false

structure Cursor where
  publication : BendOpaqueResultReceiver.Publication
  signedStorage : SignedCommand
  storageReceipt : NativeHostCodec.Receipt
  release : BendReturnRelease.Ingress
  releaseReceipt : NativeHostCodec.Receipt

/-- Private constructor: decoded cursor claims must pass actual journal receipt
readback and a current admitted native observation before they can continue. -/
structure Admitted where
  private mk ::
  previous : BendInvocation.Result
  currentResultRoot : Digest
  nextNonce : Nat

def freshNonce (domain : Digest) (subject : SubjectId) (previous : BendInvocation.Result)
    (oldNonce : Nat) : Nat :=
  (Sp800185Cshake256.hash "DREGG.BEND.OPAQUE-SESSION-SUCCESSOR-NONCE/v1".toUTF8.toList
    ((StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat StreamCodec.nat)))).encode
      (domain,subject,BendInvocation.resultId previous,oldNonce,previous.result.generation))).digest.value

def confirmedExactly (config : NativeHost.Config) (receipt : NativeHostCodec.Receipt) :
    IO Bool := do
  match ← NativeHost.confirmed config .replayed receipt.transactionId receipt.eventId with
  | .confirmed _ actual => return actual == receipt
  | _ => return false

def admit (config : NativeHost.Config) (session : Session) (signer : Signer)
    (cursor : Cursor) : IO (Except String Admitted) := do
  let publication := cursor.publication
  let previous := publication.candidate
  let command := BendOpaqueResultReceiver.command publication
  let release := cursor.release
  unless previous.effects.isEmpty &&
      previous.result.valueSchema == BendOpaqueResultReceiver.opaqueValueSchema &&
      previous.result.recipient == session.subject &&
      previous.result.audience == session.audience &&
      previous.result.keyEpoch == session.keyAtom.digest &&
      previous.definition.artifact == session.sourceAtom.digest &&
      publication.subject == session.subject &&
      publication.resultResource == session.resultResource &&
      cursor.signedStorage.commandBytes == commandCodec.encode command &&
      cursor.storageReceipt.transactionId ==
        DeclaredResourceController.transactionId config.deployment.domain config.profile.semantics command &&
      cursor.storageReceipt.eventId ==
        (DeclaredResourceController.invocationEvent config.deployment.domain config.profile.semantics
          command cursor.signedStorage).eventId &&
      release.spec.domain == config.deployment.domain &&
      release.spec.semantics == config.profile.semantics &&
      release.spec.subject == session.subject &&
      release.spec.source.resource == session.resultResource &&
      release.spec.source.result == BendInvocation.resultId previous &&
      release.spec.destination.recipient == previous.result.recipient &&
      release.spec.destination.keyEpoch == previous.result.keyEpoch &&
      release.spec.destination.audience == previous.result.audience &&
      release.spec.destination.generation == previous.result.generation &&
      release.spec.destination.purpose == session.purpose &&
      cursor.releaseReceipt.transactionId == BendReturnRelease.transactionId release.spec &&
      cursor.releaseReceipt.eventId == (BendReturnRelease.event release).eventId do
    return .error "cursor canonical predecessor/storage/release identity differs"
  unless ← confirmedExactly config cursor.storageReceipt do
    return .error "cursor original storage receipt is not in verified native history"
  unless ← confirmedExactly config cursor.releaseReceipt do
    return .error "cursor original release receipt is not in verified native history"
  let .ok opened ← NativeHost.openExisting config
    | return .error "cursor current native image unavailable"
  if BendReturnRelease.replay opened release != some (.ok {
      transactionId := cursor.releaseReceipt.transactionId
      eventId := cursor.releaseReceipt.eventId }) then
    return .error "cursor canonical release event replay differs"
  let read : Command := {
    subject := session.subject, nonce := session.nonce
    targets := [{
      kind := .object, target := session.resultResource, capability := session.resultCapability
      schemaVersion := ContentResource.commandVersion
      expectedTargetRoot := session.resultRoot, payload := .read }]
    run := none }
  let .ok signed ← signCommand config opened signer read
    | return .error "cursor current result read signing refused"
  return ← withAcceptedLoadedFrom config.deployment config.profile
    ⟨config.federation,NativeHost.logicalHeight config opened.durable⟩
    config.signature opened.durable (some opened.directory) signed
    (fun {command} prepared _shape _accepted => do
      if positive : 0 < command.targets.length then
        let index : Fin command.targets.length := ⟨0,positive⟩
        let target := command.targets[index]
        let some store := target.contentStore? (prepared.targets index).pre
          | return .error "cursor current result is not readable content"
        let some current := BendOpaqueResultReceiver.lookup store ⟨BendInvocation.resultId previous⟩
          | return .error "cursor predecessor exact atom is unavailable"
        unless BendInvocation.encode current == BendInvocation.encode previous do
          return .error "cursor predecessor canonical bytes changed"
        return .ok ⟨current,target.expectedTargetRoot,
          freshNonce config.deployment.domain session.subject current release.spec.nonce⟩
      else return .error "cursor result read layout refused")
    (fun _ => pure (.error "cursor current result read authority refused"))

def nextSession (session : Session) (cursor : Admitted) : Session :=
  { session with nonce := cursor.nextNonce, generation := cursor.previous.result.generation + 1
    predecessor := BendInvocation.resultId cursor.previous
    resultRoot := cursor.currentResultRoot }

theorem successor_exact_predecessor (session : Session) (cursor : Admitted) :
    (nextSession session cursor).predecessor = BendInvocation.resultId cursor.previous := rfl
theorem successor_exact_generation (session : Session) (cursor : Admitted) :
    (nextSession session cursor).generation = cursor.previous.result.generation + 1 := rfl

#assert_axioms successor_exact_predecessor
#assert_axioms successor_exact_generation
end Minidregg.Host.BendSessionCursor
