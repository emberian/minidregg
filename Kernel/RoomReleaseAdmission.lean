/- Original-prefix native event67 derivation. Candidate is current admission,
not ciphertext authority: its parsed lineage is merely metadata until the
chronological receiver has validated the preceding history and this exact
intent has been ordered, durably appended and read back. Historical certificate
reuse does not require a revoked old signer to become current again. -/
import Kernel.RoomReleaseLineage
namespace Minidregg.Kernel.RoomReleaseAdmission
open Minidregg.Compiler
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false
attribute [local irreducible] NativeHost.Config.profile CanonicalRuntimeProfile.Profile.compilerProfile

structure Candidate (config : Config) (opened : Opened config) where
  private mk ::
  source : RoomReleaseIntent.Ingress
  command : Command
  signed : SignedCommand
  prepared : PreparedInvocation config.deployment config.profile
    ⟨config.federation,logicalHeight config opened.durable⟩ opened.durable command
  shape : PhysicalShape prepared
  ordinary : AcceptedInvocation prepared signed
  draft : RoomReleaseIntent.Draft config.genesisHeight prepared signed shape ordinary source
  epoch : RoomKeyReleaseCodec.Epoch
  decodedEpoch : RoomKeyReleaseCodec.decodeEpoch source.body.certificate = some epoch
  previous : Option RoomReleaseLineage.Claim
  previousExact : RoomReleaseLineage.latest opened.durable.image.accepted
    source.body.room source.body.keysCell = .ok previous
  fresh : Bool
  nextExact : RoomReleaseLineage.nextKind previous source epoch = some fresh
  /-- Only NEW epoch issuance uses today's actor key. Reuse is exact old
  certificate metadata from the already admitted prefix, never fresh rights. -/
  issuance : fresh = true → NativeCurrentSigningKey.Verified prepared.authority epoch.signer
    epoch.signerEpoch epoch.signerPublic epoch.statement epoch.signature

def Candidate.intent {config : Config} {opened : Opened config}
    (candidate : Candidate config opened) := candidate.draft.intent

def admit (config : Config) (opened : Opened config) (bytes : List UInt8) :
    IO (Except String (Candidate config opened)) := do
  let some source := RoomReleaseIntent.ingressCodec.decode bytes
    | return .error "noncanonical room release source"
  let ⟨epoch, decodedEpoch⟩ ← match decodedAs : RoomKeyReleaseCodec.decodeEpoch source.body.certificate with
    | none => return .error "invalid room epoch certificate"
    | some epoch => pure (⟨epoch, decodedAs⟩ :
        {epoch // RoomKeyReleaseCodec.decodeEpoch source.body.certificate = some epoch})
  if !(decide (source.body.deliveries.length > 0 ∧ source.body.deliveries.length ≤ 64 ∧
      (source.body.deliveries.map RoomKeyReleaseCodec.Delivery.member).Nodup ∧
      (source.body.deliveries.map RoomKeyReleaseCodec.Delivery.atom).Nodup ∧
      source.body.operation.length = 32)) then
    return .error "invalid bounded room release recipients or operation"
  let previous ← match previousExact : RoomReleaseLineage.latest opened.durable.image.accepted
      source.body.room source.body.keysCell with
    | .error reason => return .error reason
    | .ok previous => pure (⟨previous,previousExact⟩ :
        {previous // RoomReleaseLineage.latest opened.durable.image.accepted
          source.body.room source.body.keysCell = .ok previous})
  let ⟨fresh, nextExact⟩ ← match nextAs : RoomReleaseLineage.nextKind previous.val source epoch with
    | none => return .error "room release fork, stale head or skipped epoch"
    | some fresh => pure (⟨fresh, nextAs⟩ :
        {fresh // RoomReleaseLineage.nextKind previous.val source epoch = some fresh})
  let some (domain,semantics,signed) := decodeSignedBytes source.signedMutation
    | return .error "invalid signed room decision mutation"
  if domain != config.deployment.domain || semantics != config.profile.semantics then
    return .error "signed room decision scope mismatch"
  let some command := commandCodec.decode signed.commandBytes
    | return .error "invalid room decision command"
  match prepare config.deployment config.profile
      ⟨config.federation,logicalHeight config opened.durable⟩ opened.ground command with
  | .error reason => return .error s!"current room mutation preparation refused: {repr reason}"
  | .ok prepared =>
    if shape : PhysicalShape prepared then
      match ← DeclaredResourceController.admit config.signature prepared signed with
      | .error reason => return .error s!"current room mutation admission refused: {repr reason}"
      | .ok ordinary =>
        match config.sourceGate none opened.durable.snapshot (ordinary.dataIntent shape) with
        | .error _ => return .error "room mutation conflicts with protected source facet"
        | .ok () => pure ()
        match ← RoomReleaseIntent.build config.signature config.genesisHeight
            prepared signed shape ordinary source with
        | .error reason => return .error reason
        | .ok draft =>
          if isFresh : fresh = true then
            match ← NativeCurrentSigningKey.verify config.signature prepared.authority epoch.signer
                epoch.signerEpoch epoch.signerPublic epoch.statement epoch.signature with
            | .error reason => return .error reason
            | .ok issuance =>
              return .ok ⟨source,command,signed,prepared,shape,ordinary,draft,epoch,decodedEpoch,
                previous.val,previous.property,fresh,nextExact,fun _ => issuance⟩
          else
            return .ok ⟨source,command,signed,prepared,shape,ordinary,draft,epoch,decodedEpoch,
              previous.val,previous.property,fresh,nextExact,fun impossible => False.elim (isFresh impossible)⟩
    else return .error "room decision native physical shape refused"

theorem current_mutation_retained (config : Config) (opened : Opened config)
    (candidate : Candidate config opened) : candidate.intent.writes =
    (candidate.ordinary.dataIntent candidate.shape).writes := candidate.draft.writesExact

#assert_axioms current_mutation_retained
end Minidregg.Kernel.RoomReleaseAdmission
