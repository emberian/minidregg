/- Signed source and device-catalog observations for protected document epochs.
These helpers use the common observation admission and never confer mutation authority. -/
module

public import Kernel.NativeHostContext
public import Kernel.NativeHostReplay
public import Kernel.NativeObservationController
public import Kernel.AudienceRosterBinding

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

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

/-- Historical replay or served basis establishes image provenance; current observation
establishes disclosure authority. Neither a key cache nor caller epoch enters. -/
def objectAudienceOn (config : Config) (ground : Minidregg.Compiler.ServedBasis.Ground config.deployment)
    (signedObservationBytes : List UInt8) : IO (Except Refusal ObjectAudienceView) := do
  let some signed := NativeObservationCodec.signedCodec.decode signedObservationBytes
    | return .error (.of .malformed)
  let .query query := signed.challenge.intent.purpose
    | return .error (.of .malformed)
  if query.kind != .object || query.view != .resource then
    return .error (.of .malformed)
  match ← NativeObservationController.authorize config.signature
      ground config.profile config.federation
      config.genesisHeight signed with
  | .error refusal => return .error refusal
  | .ok _ =>
    let snapshot := ground.authority
    let revision := snapshot.authState.policyRevision ⟨query.target⟩
    let address := snapshot.authState.policyAddress ⟨query.target⟩ revision
    let some source := CanonicalCellRegistry.loadPolicySource snapshot.domain
        ground.directory address
      | return .error (.of .operationRejected)
    let audience := source.record.audience
    if let some protectedState := audience then
      if protectedState.object != query.target then return .error (.of .operationRejected)
    let .present objectCell := ground.directory.slots query.target
      | return .error (.of .operationRejected)
    return .ok ⟨signed.challenge.intent.subject, query.target, ground.worldRoot,
      address, snapshot.authState.policyEpoch ⟨query.target⟩, revision,
      source.canonicalBytes, source.record, snapshot.cell.root, objectCell.payload.root, audience⟩

def objectAudienceLoaded (config : Config) (target : Durable)
    (verified : NativeHostReplay.Verified config target)
    (signedObservationBytes : List UInt8) : IO (Except Refusal ObjectAudienceView) :=
  objectAudienceOn config (.full target verified.opened.directory verified.opened.authority)
    signedObservationBytes

/-- Device catalog material is disclosed only through its own current signed
observation. The roster checker binds that exact image to the planned phase. -/
def objectAudienceRosterOn (config : Config) (ground : Minidregg.Compiler.ServedBasis.Ground config.deployment)
    (sourceObservation catalogObservation rosterBytes : List UInt8)
    (planned : Minidregg.Theory.ObjectAudience.State) :
    IO (Except String (Minidregg.Theory.ObjectAudience.State ×
      Minidregg.Theory.ObjectAudienceRoster.Roster)) := do
  let view ← match ← objectAudienceOn config ground sourceObservation with
    | .error reason => return .error s!"source observation refused: {repr reason}"
    | .ok view => pure view
  let some signed := NativeObservationCodec.signedCodec.decode catalogObservation
    | return .error "catalog observation malformed"
  let .query query := signed.challenge.intent.purpose
    | return .error "catalog observation is not a query"
  unless query.kind == .object && query.view == .resource &&
      signed.challenge.intent.subject == view.subject && planned.object == view.object do
    return .error "catalog observation subject/view mismatch"
  match ← NativeObservationController.authorize config.signature
      ground config.profile config.federation config.genesisHeight signed with
  | .error reason => return .error s!"catalog observation refused: {repr reason}"
  | .ok _ =>
    let some grant := signed.challenge.intent.grants.head?
      | return .error "catalog observation has no authorizing grant"
    let some capability := CredentialAuthorityState.readCapability ground.authority.cell
        grant.kind grant.capability
      | return .error "catalog observation capability absent"
    unless decide (CellField.NamedBy capability.head.scope.fields .body) do
      return .error "catalog observation does not disclose device records"
    let state := { planned with deviceSnapshot := (ground.view.model.roots ⟨query.target⟩).value }
    let some bound := AudienceRosterBinding.checkBytes ground state rosterBytes
      | return .error "roster does not bind exact current device catalog"
    unless bound.checked.source == query.target do
      return .error "catalog observation names a different device source"
    return .ok (state, bound.roster)

def objectAudienceRosterLoaded (config : Config) (target : Durable)
    (verified : NativeHostReplay.Verified config target)
    (sourceObservation catalogObservation rosterBytes : List UInt8)
    (planned : Minidregg.Theory.ObjectAudience.State) :
    IO (Except String (Minidregg.Theory.ObjectAudience.State ×
      Minidregg.Theory.ObjectAudienceRoster.Roster)) :=
  objectAudienceRosterOn config (.full target verified.opened.directory verified.opened.authority)
    sourceObservation catalogObservation rosterBytes planned

end Minidregg.Kernel.NativeHost
