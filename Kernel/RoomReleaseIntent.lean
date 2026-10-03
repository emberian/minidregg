/- Source event67 intent construction, before chronological head selection.
Both the ordinary current mutation and separately signed current release method
must succeed on exactly the same Prepared source image. All native posts and
ordinary claims/charges survive; complete recipient/method guards are added with
checked write discharge. Draft is deliberately not an Applied release permit. -/
import Kernel.RoomReleaseAuthority
namespace Minidregg.Kernel.RoomReleaseIntent
open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false

structure Ingress where
  body : RoomKeyReleaseCodec.Request
  signedMutation : List UInt8
  releaseEnvelope : List UInt8
  deriving DecidableEq

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product RoomKeyReleaseCodec.requestStream
    (StreamCodec.product bytesStream bytesStream))
    (fun s => (s.body,s.signedMutation,s.releaseEnvelope))
    (fun (r,s,e) => ⟨r,s,e⟩) (by intro s; cases s; rfl)
def frame : List UInt8 := "DREGG.PRIVATE.ROOM.RELEASE.SOURCE".toUTF8.toList ++ [1]
def ingressCodec : LawfulCodec Ingress :=
  ResourceBirthCodec.strictCodec (NativeHostCodec.framed frame ingressStream)

def decisionSchema : Digest :=
  (Sp800185Cshake256.hash "DREGG.PRIVATE-CELL.SCHEMA/v1".toUTF8.toList
    (CurrentRecipientRecord.bigEndian 8 "DREGG/PRIVATE-ROOM/RELEASE-DECISION/v1".toUTF8.size ++
      "DREGG/PRIVATE-ROOM/RELEASE-DECISION/v1".toUTF8.toList)).digest

def operationAtom (body : RoomKeyReleaseCodec.Request) : AtomId :=
  ⟨⟨CurrentRecipientRecord.readBigEndian body.operation⟩⟩

def mutationMatches (body : RoomKeyReleaseCodec.Request) (command : Command) : Bool :=
  command.subject == body.actor && command.run.isNone &&
  match command.targets with
  | [target] => target.kind == .object && target.target == body.keysCell &&
      target.expectedTargetRoot == body.keysRoot &&
      target.schemaVersion == ContentResource.commandVersion &&
      target.payload == .content ⟨[.createAtom (operationAtom body) (.inlineObject decisionSchema)
        (RoomKeyReleaseCodec.encode body)]⟩
  | _ => false

def event (deployment : Deployment) (source : Ingress) : StableEvent :=
  ⟨67,deployment.domain,
    (Sp800185Cshake256.hash "DREGG.PRIVATE.ROOM.RELEASE.EVENT/v1".toUTF8.toList
      (ingressCodec.encode source)).digest,ingressCodec.encode source⟩

variable {F : Type} [Field F] [DecidableEq F]
  {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
  {ambient : Ambient} {durable : Durable} {command : Command}
  {prepared : PreparedInvocation deployment profile ambient durable command}
  {signed : SignedCommand} {shape : PhysicalShape prepared}

structure Draft (genesisHeight : Nat)
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (signed : SignedCommand) (shape : PhysicalShape prepared)
    (accepted : AcceptedInvocation prepared signed) (source : Ingress) where
  private mk ::
  intent : DataIntent ResourceBirthCodec.rootBytes
  sourceExact : source.signedMutation = signedBytes deployment.domain profile.semantics signed
  mutationExact : mutationMatches source.body command = true
  recipients : (i : Fin source.body.deliveries.length) →
    RoomReleaseCurrent.Recipient genesisHeight prepared source.body source.body.deliveries[i]
  method : RoomReleaseAuthority.Prepared (RoomReleaseCurrent.context prepared) profile
    ambient.federation ambient.height source.body
  methodChecked : RoomReleaseAuthority.Checked method source.releaseEnvelope
  writesExact : intent.writes = (accepted.dataIntent shape).writes
  claimsExact : intent.nullifiers = (accepted.dataIntent shape).nullifiers
  subjectExact : intent.subject = (accepted.dataIntent shape).subject
  eventExact : intent.event = event deployment source
  dependencies : List ReadGuard
  retained : ∀ guard ∈ dependencies, RoomReleaseCurrent.guardHeld intent guard
  preservesCharge : ∀ lane, (accepted.dataIntent shape).exactCharge lane ≤ intent.exactCharge lane

def build (native : CredentialSignatureIO.NativeConfig) (genesisHeight : Nat)
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (signed : SignedCommand) (shape : PhysicalShape prepared)
    (accepted : AcceptedInvocation prepared signed) (source : Ingress) :
    IO (Except String (Draft genesisHeight prepared signed shape accepted source)) := do
  if sourceExact : source.signedMutation = signedBytes deployment.domain profile.semantics signed then
    if mutationExact : mutationMatches source.body command = true then
      let ordinary := accepted.dataIntent shape
      let some method := RoomReleaseAuthority.prepare (RoomReleaseCurrent.context prepared)
          profile ambient.federation ambient.height source.body
        | return .error "current source release method preparation refused"
      let some methodChecked ← RoomReleaseAuthority.check native method source.releaseEnvelope
        | return .error "current source release permission refused"
      match ← RoomReleaseCurrent.checkRecipients native genesisHeight prepared source.body with
      | .error reason => return .error reason
      | .ok recipients =>
        let some methodGuards := RoomReleaseAuthority.lawReadGuards method
          | return .error "current release law dependencies unavailable"
        let dependencies := methodGuards ++ RoomReleaseCurrent.dependencies genesisHeight prepared source.body recipients
        if roots : ∀ guard ∈ dependencies, guard.expectedRoot = durable.snapshot.model.roots guard.cellId then
          if discharge : ∀ guard ∈ dependencies, ∀ write ∈ ordinary.writes,
              guard.cellId = write.cellId → guard.expectedRoot = write.expectedPre then
            let extra := dependencies.filter (fun guard =>
              !(decide (guard.cellId ∈ ordinary.writes.map DataWrite.cellId)))
            let overhead : ResourceCost.Charge := fun lane => match lane with
              | .incidences => source.body.deliveries.length + 1
              | .memoryTouches => dependencies.length
              | .turnBytes | .witnessBytes => (ingressCodec.encode source).length
              | .proofWork => source.body.deliveries.length + 1
              | .storageBytes | .networkBytes | .feeDebit | .sideEffectCount | .leaseByteBlocks => 0
            let intent : DataIntent ResourceBirthCodec.rootBytes :=
              { ordinary with
                readGuards := ordinary.readGuards ++ extra
                exactCharge := ordinary.exactCharge + overhead
                event := event deployment source
                guardsReadOnly := by
                  intro guard member
                  rcases List.mem_append.mp member with old | added
                  · exact ordinary.guardsReadOnly guard old
                  · have selected := (List.mem_filter.mp added).2
                    simpa using selected }
            if preflight : intent.preflight durable.snapshot = .ok () then
              let retained : ∀ guard ∈ dependencies, RoomReleaseCurrent.guardHeld intent guard := by
                intro guard member
                by_cases written : guard.cellId ∈ ordinary.writes.map DataWrite.cellId
                · obtain ⟨write,writeMember,cellExact⟩ := List.mem_map.mp written
                  exact Or.inr ⟨write,writeMember,cellExact,
                    (discharge guard member write writeMember cellExact.symm).symm⟩
                · exact Or.inl (List.mem_append_right _ (List.mem_filter.mpr
                    ⟨member,by simp [written]⟩))
              return .ok ⟨intent,sourceExact,mutationExact,recipients,method,methodChecked,
                rfl,rfl,rfl,rfl,dependencies,retained,by intro lane; exact Nat.le_add_right _ _⟩
            else return .error "room release exact funded native intent refused"
          else return .error "room release write does not hold recipient law pre-root"
        else return .error "room release law guard differs from source snapshot"
    else return .error "room decision command differs from exact create-only request"
  else return .error "room decision signed command differs from retained ingress"

theorem draft_keeps_native_writes (genesisHeight : Nat)
    (accepted : AcceptedInvocation prepared signed) (source : Ingress)
    (draft : Draft genesisHeight prepared signed shape accepted source) :
    draft.intent.writes = (accepted.dataIntent shape).writes := draft.writesExact

#assert_axioms draft_keeps_native_writes
end Minidregg.Kernel.RoomReleaseIntent
