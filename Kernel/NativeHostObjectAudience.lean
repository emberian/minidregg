/- Signed source and device-catalog observations for protected document epochs.
These helpers use the common observation admission and never confer mutation authority. -/
import Kernel.NativeHostContext
import Kernel.NativeHostReplay
import Kernel.NativeObservationController
import Kernel.AudienceRosterBinding

namespace Minidregg.Kernel.NativeHost
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.NativeHostCodec
set_option autoImplicit false
attribute [local irreducible] Config.profile CanonicalRuntimeProfile.Profile.compilerProfile

/-- A current source-owned audience view. It can only be selected after the
ordinary signed resource observation authorizes the same image. -/
structure ObjectAudienceView where
  subject : SubjectId
  object : Nat
  worldRoot : Digest
  policyAddress : Digest
  policyEpoch : Nat
  policyRevision : Nat
  sourceBytes : List UInt8
  sourceRecord : CanonicalPolicyAdmission.PolicyRecord
  currentAuthorityRoot : Digest
  currentObjectRoot : Digest
  audience : Option Minidregg.Theory.ObjectAudience.State
  deriving Repr

/-- Historical replay establishes image provenance; current observation
establishes disclosure authority. Neither a key cache nor caller epoch enters. -/
def objectAudienceLoaded (config : Config) (target : Durable)
    (_verified : NativeHostReplay.Verified config target)
    (signedObservationBytes : List UInt8) : IO (Except Refusal ObjectAudienceView) := do
  let .ok opened := validateLoaded config target
    | return .error (.of .malformed)
  let some signed := NativeObservationCodec.signedCodec.decode signedObservationBytes
    | return .error (.of .malformed)
  let .query query := signed.challenge.intent.purpose
    | return .error (.of .malformed)
  if query.kind != .object || query.view != .resource then
    return .error (.of .malformed)
  match ← NativeObservationController.authorize config.signature
      (Minidregg.Compiler.ServedBasis.Ground.full _ opened.directory opened.authority) config.profile config.federation
      config.genesisHeight signed with
  | .error refusal => return .error refusal
  | .ok _ =>
    let snapshot := opened.authority.snapshot
    let revision := snapshot.authState.policyRevision ⟨query.target⟩
    let address := snapshot.authState.policyAddress ⟨query.target⟩ revision
    let some source := CanonicalCellRegistry.loadPolicySource snapshot.domain
        opened.directory.directory address
      | return .error (.of .operationRejected)
    let audience := source.record.audience
    if let some protectedState := audience then
      if protectedState.object != query.target then return .error (.of .operationRejected)
    let .present objectCell := opened.directory.directory.slots query.target
      | return .error (.of .operationRejected)
    return .ok ⟨signed.challenge.intent.subject, query.target, target.worldRoot,
      address, snapshot.authState.policyEpoch ⟨query.target⟩, revision,
      source.canonicalBytes, source.record, snapshot.cell.root, objectCell.payload.root, audience⟩

/-- Device catalog material is disclosed only through its own current signed
observation. The roster checker binds that exact image to the planned phase. -/
def objectAudienceRosterLoaded (config : Config) (target : Durable)
    (verified : NativeHostReplay.Verified config target)
    (sourceObservation catalogObservation rosterBytes : List UInt8)
    (planned : Minidregg.Theory.ObjectAudience.State) :
    IO (Except String (Minidregg.Theory.ObjectAudience.State ×
      Minidregg.Theory.ObjectAudienceRoster.Roster)) := do
  let view ← match ← objectAudienceLoaded config target verified sourceObservation with
    | .error reason => return .error s!"source observation refused: {repr reason}"
    | .ok view => pure view
  let opened := verified.opened
  let some signed := NativeObservationCodec.signedCodec.decode catalogObservation
    | return .error "catalog observation malformed"
  let .query query := signed.challenge.intent.purpose
    | return .error "catalog observation is not a query"
  unless query.kind == .object && query.view == .resource &&
      signed.challenge.intent.subject == view.subject && planned.object == view.object do
    return .error "catalog observation subject/view mismatch"
  match ← NativeObservationController.authorize config.signature
      (Minidregg.Compiler.ServedBasis.Ground.full _ opened.directory opened.authority) config.profile config.federation config.genesisHeight signed with
  | .error reason => return .error s!"catalog observation refused: {repr reason}"
  | .ok _ =>
    let some grant := signed.challenge.intent.grants.head?
      | return .error "catalog observation has no authorizing grant"
    let some capability := CredentialAuthorityState.readCapability opened.authority.snapshot.cell
        grant.kind grant.capability
      | return .error "catalog observation capability absent"
    unless decide (CellField.NamedBy capability.head.scope.fields .body) do
      return .error "catalog observation does not disclose device records"
    let state := { planned with deviceSnapshot := (target.snapshot.model.roots ⟨query.target⟩).value }
    let some bound := AudienceRosterBinding.checkBytes (Minidregg.Compiler.ServedBasis.Ground.full _ opened.directory opened.authority) state rosterBytes
      | return .error "roster does not bind exact current device catalog"
    unless bound.checked.source == query.target do
      return .error "catalog observation names a different device source"
    return .ok (state, bound.roster)

end Minidregg.Kernel.NativeHost
