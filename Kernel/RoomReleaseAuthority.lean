/- Independent current room-release authority. A normal keys-cell mutation is
not a disclosure permit. This method checks a separate native delegation/release
request whose args/effects bind the complete exact digest-only release body.
The actor's scoped current capability and the keys resource's complete current
law both admit that request. The same snapshot is used by the ordinary mutation
and recipient checks. Only the later event67 durable Applied may release bytes. -/
import Kernel.RoomReleaseCurrent
import Kernel.PhysicalResourceReadGuard

namespace Minidregg.Kernel.RoomReleaseAuthority
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false
set_option profiler true
set_option profiler.threshold 100
set_option maxHeartbeats 400000

variable {F : Type} [Field F] [DecidableEq F]
  {deployment : DeclaredResourceController.Deployment}
  {durable : DeclaredResourceController.Durable}

def marker (request : RoomKeyReleaseCodec.Request) : Nat :=
  (Sp800185Cshake256.hash "DREGG.PRIVATE.ROOM.RELEASE.AUTHORITY/v1".toUTF8.toList
    (RoomKeyReleaseCodec.encode request)).digest.value

def wanted (context : ResourceObservationAdmission.Context deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId)
    (height : Nat) (body : RoomKeyReleaseCodec.Request) : Request .object where
  domain := deployment.domain
  semantics := profile.semantics
  federation := federation
  subject := body.actor
  subjectKeyEpoch := context.authority.authState.subjectKeyEpoch body.actor
  target := ⟨body.keysCell⟩
  verb := .delegateObject
  argsDigest := ⟨marker body⟩
  effectsDigest := ⟨marker body⟩
  nonce := marker body
  height := height
  preStateRoot := body.keysRoot
  policyId := ⟨body.keysCell⟩
  policyEpoch := context.authority.authState.policyEpoch ⟨body.keysCell⟩
  policyRevision := context.authority.authState.policyRevision ⟨body.keysCell⟩
  cost := (RoomKeyReleaseCodec.encode body).length

attribute [irreducible] wanted

structure Prepared (context : ResourceObservationAdmission.Context deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId)
    (height : Nat) (body : RoomKeyReleaseCodec.Request) where
  private mk ::
  observed : ResourceTargetAdmission.Observed deployment context.directory
    .object body.keysCell body.keysRoot
  physicalCurrent : ResourceBirthCodec.physicalRoot (.live observed.before) =
    durable.snapshot.model.roots ⟨body.keysCell⟩
  authorityExact : context.authorityReadGuard.expectedRoot = body.authorityRoot
  oneCell : body.decisionCell = body.keysCell ∧ body.decisionRoot = body.keysRoot
  clock : ClockCellDomain.Loaded deployment durable.snapshot

def prepare (context : ResourceObservationAdmission.Context deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId)
    (height : Nat) (body : RoomKeyReleaseCodec.Request) : Option (Prepared context profile federation height body) := do
  let observed ← ResourceTargetAdmission.observe deployment context.directory
    .object body.keysCell body.keysRoot
  let physicalCurrent := PhysicalResourceReadGuard.current context.directory body.keysCell
    observed.before observed.present
  if authorityExact : context.authorityReadGuard.expectedRoot = body.authorityRoot then
    if oneCell : body.decisionCell = body.keysCell ∧ body.decisionRoot = body.keysRoot then
      let clock ← ClockCellDomain.load deployment durable.snapshot
      some ⟨observed,physicalCurrent,authorityExact,oneCell,clock⟩
    else none
  else none

variable {context : ResourceObservationAdmission.Context deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {federation : FederationId}
  {height : Nat} {body : RoomKeyReleaseCodec.Request}

def project (prepared : Prepared context profile federation height body)
    (logical : Store.Store (CanonicalCellRegistry.layout prepared.observed.before.kind)) :
    Minidregg.Pred.State :=
  ⟨[("room/release/version",1),("room/release/room",Int.ofNat body.room)] ++
    ClockCell.slots prepared.clock.clock ++
    WorldKindLawDependencies.targetSelectorSlots context.directory body.keysCell ++
    CanonicalRuntimeProfile.requestSlots (wanted context profile federation height body) ++
    ResourceAuthorityProjection.bytesSlots "context/bytes" 0 (RoomKeyReleaseCodec.encode body) ++
    ResourceAuthorityProjection.bytesSlots "resource/bytes" 0
      ((CanonicalCellRegistry.materializer prepared.observed.before.kind).codec.encode logical) ++
    ResourceObservationAdmission.resourceSlots body.actor body.keysCell prepared.observed.before.kind logical⟩

attribute [irreducible] project

def step (prepared : Prepared context profile federation height body) : PolicyStepContext :=
  PolicyStepContext.ofCandidate (project prepared) profile.semantics
    (ResourceObservationAdmission.readCandidate (wanted context profile federation height body)
      prepared.observed.before.kind prepared.observed.before.payload (by
        simpa [wanted] using prepared.observed.rootExact))

attribute [irreducible] step

def kindDependencies (_prepared : Prepared context profile federation height body) :
    Option WorldKindLawDependencies.Dependencies :=
  WorldKindLawDependencies.loadTarget deployment context.directory body.keysCell

def lawReadGuards (prepared : Prepared context profile federation height body) : Option (List ReadGuard) := do
  let structural ← kindDependencies prepared
  let sources ← PhysicalLawResolution.readGuards context.authority
    context.directory profile.semantics body.keysCell structural.additional
  pure (context.authorityReadGuards ++ [prepared.clock.readGuard,
    ⟨⟨body.keysCell⟩,durable.snapshot.model.roots ⟨body.keysCell⟩⟩] ++
    (sources ++ structural.readGuards).map (fun g => ⟨⟨g.1⟩,g.2⟩))

def policyConfig (prepared : Prepared context profile federation height body) :
    ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile context.authority
    context.directory (sourceCapabilityPortal context.authority (marker body))
    (step prepared) body.keysCell ((kindDependencies prepared).map (·.additional) |>.getD [])


def portal (prepared : Prepared context profile federation height body) : Portal :=
  (policyConfig prepared).portal

attribute [irreducible] portal

def authorize (prepared : Prepared context profile federation height body)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority) :
    Option (Authorized (portal prepared) context.authority.authState
      (wanted context profile federation height body)) := by
  unfold portal
  exact do
   let config := policyConfig prepared
   let _ ← lawReadGuards prepared
   let evidence ← (config.capabilityEvidenceChecked (wanted context profile federation height body)
     ⟨body.capability⟩ () signature () (fun _ => ())).toOption
   let law ← config.resolve?
   ComposedPolicyAdmission.admit config (wanted context profile federation height body) evidence law.witness
     (.policy ⟨body.keysCell⟩ (wanted context profile federation height body).policyRevision) (by unfold wanted; rfl) (by unfold wanted; rfl)

attribute [irreducible] policyConfig

structure Checked (prepared : Prepared context profile federation height body) (envelope : List UInt8) where
  private mk ::
  signature : CredentialSignatureAdmission.CheckedSignature context.authority
  envelopeExact : signature.envelopeBytes = envelope
  authorization : Authorized (portal prepared) context.authority.authState
    (wanted context profile federation height body)
  authorized : authorize prepared signature = some authorization

def check (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared context profile federation height body) (envelope : List UInt8) :
    IO (Option (Checked prepared envelope)) := do
  match ← CredentialSignatureAdmission.verifyNative native context.authority (marker body)
      (wanted context profile federation height body) envelope with
  | .error _ => return none
  | .ok signature =>
    if envelopeExact : signature.envelopeBytes = envelope then
      match authorized : authorize prepared signature with
      | none => return none
      | some authorization => return some ⟨signature,envelopeExact,authorization,authorized⟩
    else return none

theorem exact_source_root (prepared : Prepared context profile federation height body) :
    ResourceBirthCodec.physicalRoot (.live prepared.observed.before) =
      durable.snapshot.model.roots ⟨body.keysCell⟩ := prepared.physicalCurrent

#assert_axioms exact_source_root
end Minidregg.Kernel.RoomReleaseAuthority
