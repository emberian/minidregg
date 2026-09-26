/-
Signed observation and private preparation over one exact loaded native image.
The challenge discloses only the explicitly public routing, clock, commitment,
policy and public enrollment coordinates. Its response is not read authority:
every selected resource requires its own actual observe capability, native
request signature and current compiled policy. Mutating capabilities do not
implicitly grant observation. Blind submissions remain a separate receiver API.

The policy candidate is an empty patch on the actual selected resource page.
Account views add only that account's sparse balance cut from the same image;
neither the policy projection nor the returned value contains the shared Book.
This is a snapshot read, not a timing-noninterference or malicious-host claim.
-/
import Compiler.NativeObservationCodec
import Kernel.ResourceObservationAdmission

namespace Minidregg.Kernel.NativeObservationController

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.NativeObservationCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Registry := CanonicalCellRegistry.registry

abbrev Context := ResourceObservationAdmission.Context

variable {deployment : Deployment} {durable : Durable}

private def refused : String := "observation refused"

/-- Source contract named by the deployed profile: exact role selection,
schema-native unchanged views, explicit observation grants for the entire
joint target list, and the one loaded image throughout authorization. -/
abbrev observationProjectionVersion := CanonicalRuntimeProfile.observationProjectionVersion

private def need {α : Type} : Option α → Except String α
  | none => .error refused
  | some value => .ok value

private def require (condition : Bool) : Except String Unit :=
  if condition then .ok () else .error refused

abbrev observeVerb := ResourceObservationAdmission.observeVerb
abbrev book (context : Context deployment durable) := ResourceObservationAdmission.book context
abbrev accountBalanceMap := CanonicalAccountView.accountBalanceMap
abbrev accountCut := CanonicalAccountView.accountCut
abbrev balanceStream := CanonicalAccountView.balanceStream

theorem accountBalanceMap_exact (value : CanonicalResourceKernel.Book) (account asset : Nat) :
    accountBalanceMap value account asset = value.balance account asset :=
  CanonicalAccountView.accountBalanceMap_exact value account asset

theorem accountCut_noninterference (left right : CanonicalResourceKernel.Book) (account : Nat)
    (same : ∀ asset, left.balance account asset = right.balance account asset) :
    accountCut left account = accountCut right account :=
  CanonicalAccountView.accountCut_noninterference left right account same

def balances (context : Context deployment durable) (grant : GrantRef) : Option (List (Nat × Int)) :=
  ResourceObservationAdmission.balances context grant.kind grant.target

abbrev Target := ResourceKind × Nat

def declaredKind (context : Context deployment durable) (target : Nat) : Option ResourceKind :=
  match context.directory.directory.slots target with
  | .present packed => ResourceTargetAdmission.externalKind packed.kind
  | _ => none

/-- This analysis never runs a mutating preparation. Existing Book account
membership is public routing metadata. AccountSupported, enforced by the
loaded Book law, makes fresh registrations incapable of probing hidden funds.
An existing account cannot be hidden merely by listing it as a proposed birth.
All debit sources are included, even when the eventual operation would fail
its factory fee/funding checks. Recipient credits confer no read obligation. -/
def requiredTargets (context : Context deployment durable) (intent : Intent) :
    Except String (List Target) := do
  match intent.purpose with
  | .query query => pure [(query.kind, query.target)]
  | .prepare (.invoke bytes) =>
      let command ← need (DeclaredResourceController.commandCodec.decode bytes)
      require (command.subject == intent.subject)
      require command.targetsWellFormed
      pure (command.targets.map fun target => (target.kind, target.target))
  | .prepare (.delegate bytes) =>
      let command ← need (CapabilityDelegationController.commandCodec.decode bytes)
      require (command.2.subject == intent.subject)
      -- Observing another grant must not expose this named parent's lineage.
      require (intent.grants.all fun grant => grant.capability == command.2.declaration.parentId)
      pure [(command.1, command.2.declaration.target.value)]
  | .prepare (.revoke bytes) =>
      let command ← need (CapabilityRevocationController.commandCodec.decode bytes)
      require (command.2.subject == intent.subject)
      -- Observing the resource is separate from exercising its management
      -- grant. The signing plan exposes no stored victim/lineage payload.
      pure [(command.1, command.2.target.value)]
  | .prepare (.install subject _ bytes) =>
      require (subject == intent.subject)
      let declaration ← need (PolicyInstallController.decodeDeclaration bytes)
      let kind ← need (declaredKind context declaration.source.policyId.value)
      pure [(kind, declaration.source.policyId.value)]
  | .prepare (.birth bytes _) =>
      let descriptor ← need (CanonicalCellRegistry.sourceEncoding.codec.decode bytes)
      require (descriptor.creator == intent.subject)
      let current ← need (book context)
      let sources := descriptor.resourceBatch.operations.filterMap fun operation =>
        if operation.posting.source ∈ current.accounts then
          some (.account, operation.posting.source) else none
      pure ((.object, descriptor.factory.value) :: sources).eraseDups

def footprintExact (context : Context deployment durable) (intent : Intent) : Except String Unit :=
  match requiredTargets context intent with
  | .error reason => .error reason
  | .ok required =>
      if intent.grants.map (fun grant => (grant.kind, grant.target)) = required then .ok ()
      else .error refused

/-- Missing, additional, reordered or wrong-kind read selections are all
refused before any selected values can be returned. -/
theorem footprint_mismatch_refused (context : Context deployment durable) (intent : Intent)
    (required : List Target) (derived : requiredTargets context intent = .ok required)
    (different : intent.grants.map (fun grant => (grant.kind, grant.target)) ≠ required) :
    footprintExact context intent = .error refused := by
  simp [footprintExact, derived, different]

theorem footprint_success_exact (context : Context deployment durable) (intent : Intent)
    (required : List Target) (derived : requiredTargets context intent = .ok required)
    (accepted : footprintExact context intent = .ok ()) :
    intent.grants.map (fun grant => (grant.kind, grant.target)) = required := by
  by_contra different
  rw [footprint_mismatch_refused context intent required derived different] at accepted
  cases accepted

private def bindingBytesAt (deployment : Deployment) (boundary semantics : Digest)
    (intent : Intent) (grant : GrantRef) : List UInt8 :=
  (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream grantStream)))).encode
      (deployment.domain, semantics,
        boundary, intentIdentity intent, grant)

def bindingBytes (_context : Context deployment durable) (semantics : Digest)
    (intent : Intent) (grant : GrantRef) : List UInt8 :=
  bindingBytesAt deployment (NativeHostCodec.imageBoundary deployment.domain semantics durable.image)
    semantics intent grant

private def effectIdentityAt (deployment : Deployment) (boundary semantics : Digest)
    (intent : Intent) (grant : GrantRef) : Digest :=
  (Sp800185Cshake256.hash "DREGG.NATIVE-HOST.OBSERVE-EFFECT/v3".toUTF8.toList
    (bindingBytesAt deployment boundary semantics intent grant)).digest

def effectIdentity (context : Context deployment durable) (semantics : Digest)
    (intent : Intent) (grant : GrantRef) : Digest :=
  effectIdentityAt deployment (NativeHostCodec.imageBoundary deployment.domain semantics durable.image)
    semantics intent grant

private def markerAt (deployment : Deployment) (boundary semantics : Digest)
    (intent : Intent) (grant : GrantRef) : Nat :=
  (Sp800185Cshake256.hash "DREGG.NATIVE-HOST.OBSERVE-SIGNATURE/v3".toUTF8.toList
    (bindingBytesAt deployment boundary semantics intent grant)).digest.value

def marker (context : Context deployment durable) (semantics : Digest)
    (intent : Intent) (grant : GrantRef) : Nat :=
  markerAt deployment (NativeHostCodec.imageBoundary deployment.domain semantics durable.image)
    semantics intent grant

theorem bindingBytesAt_exact (context : Context deployment durable) (semantics : Digest)
    (intent : Intent) (grant : GrantRef) :
    bindingBytesAt deployment (NativeHostCodec.imageBoundary deployment.domain semantics durable.image)
      semantics intent grant = bindingBytes context semantics intent grant := rfl

private def requestAt (context : Context deployment durable) (boundary semantics : Digest)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (preRoot : Digest) : Request grant.kind where
  domain := deployment.domain
  semantics := semantics
  federation := federation
  subject := intent.subject
  subjectKeyEpoch := context.authority.snapshot.authState.subjectKeyEpoch intent.subject
  target := ⟨grant.target⟩
  verb := observeVerb grant.kind
  argsDigest := intentIdentity intent
  effectsDigest := effectIdentityAt deployment boundary semantics intent grant
  nonce := intent.nonce
  height := genesisHeight + durable.image.accepted.length
  preStateRoot := preRoot
  policyId := ⟨grant.target⟩
  policyEpoch := context.authority.snapshot.authState.policyEpoch ⟨grant.target⟩
  policyRevision := context.authority.snapshot.authState.policyRevision ⟨grant.target⟩
  cost := (intentCodec.encode intent).length

def request (context : Context deployment durable) (semantics : Digest)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (preRoot : Digest) : Request grant.kind :=
  requestAt context (NativeHostCodec.imageBoundary deployment.domain semantics durable.image)
    semantics federation genesisHeight intent grant preRoot

theorem requestAt_exact (context : Context deployment durable) (semantics : Digest)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (preRoot : Digest) :
    requestAt context (NativeHostCodec.imageBoundary deployment.domain semantics durable.image)
      semantics federation genesisHeight intent grant preRoot =
      request context semantics federation genesisHeight intent grant preRoot := rfl

abbrev readPatch := ResourceObservationAdmission.readPatch

def readFamily (context : Context deployment durable) (semantics : Digest)
    (federation : FederationId) (genesisHeight : Nat) (grant : GrantRef)
    (kind : CanonicalCellRegistry.Kind)
    (pre : Materialized (CanonicalCellRegistry.materializer kind)) (intent : Intent) :=
  ResourceObservationAdmission.readFamily
    (request context semantics federation genesisHeight intent grant pre.root) kind pre

def readCandidate (context : Context deployment durable) (semantics : Digest)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (kind : CanonicalCellRegistry.Kind)
    (pre : Materialized (CanonicalCellRegistry.materializer kind)) :=
  ResourceObservationAdmission.readCandidate
    (request context semantics federation genesisHeight intent grant pre.root) kind pre rfl

/-- Authority kinds select concrete resource roles, never another role sharing
the same representation. Content is an object; the shared Book and authority
planes are never observation targets through this protocol. -/
def observableKind (kind : ResourceKind) (physical : CanonicalCellRegistry.Kind) : Bool :=
  decide (ResourceTargetAdmission.externalKind physical = some kind)

theorem observable_roles_exact (kind : ResourceKind) (physical : CanonicalCellRegistry.Kind) :
    observableKind kind physical = true ↔
      (kind = .object ∧ (physical = .declaredObject ∨ physical = .content)) ∨
      (kind = .account ∧ physical = .accountMetadata) ∨
      (kind = .program ∧ physical = .declaredProgram) := by
  cases kind <;> cases physical <;> simp [observableKind, ResourceTargetAdmission.externalKind]

theorem content_observation_is_object (kind : ResourceKind) :
    observableKind kind .content = true ↔ kind = .object := by
  cases kind <;> simp [observableKind, ResourceTargetAdmission.externalKind]

theorem shared_book_is_not_observable (kind : ResourceKind) :
    observableKind kind .resourceBook = false := by
  cases kind <;> rfl

theorem authority_shard_is_not_observable (kind : ResourceKind) :
    observableKind kind .authorityShard = false := by
  cases kind <;> rfl

structure Selected (context : Context deployment durable) (grant : GrantRef) where
  private mk ::
  packed : PackedCell Registry
  present : context.directory.directory.slots grant.target = .present packed
  law : CanonicalCellRegistry.CellLaw deployment grant.target packed
  role : observableKind grant.kind packed.kind = true
  accountBalances : List (Nat × Int)
  balancesExact : balances context grant = some accountBalances

def select (context : Context deployment durable) (grant : GrantRef) : Option (Selected context grant) :=
  match present : context.directory.directory.slots grant.target with
  | .absent => none
  | .present packed =>
      if law : CanonicalCellRegistry.CellLaw deployment grant.target packed then
        if role : observableKind grant.kind packed.kind = true then
          match exact : balances context grant with
          | none => none
          | some values => some ⟨packed, present, law, role, values, exact⟩
        else none
      else none

variable {F : Type} [Field F] [DecidableEq F]

abbrev ReadPreparation (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (selected : Selected context grant) :=
  ResourceObservationAdmission.Prepared context profile
    (request context profile.semantics federation genesisHeight intent grant selected.packed.payload.root)
    (marker context profile.semantics intent grant) grant.capability (intentCodec.encode intent)

/-- The retained lower admission is the same resource-local no-op policy gate
used before exposing participants to foreign policies in joint submission. -/
structure CheckedGrant (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent) (grant : GrantRef) where
  private mk ::
  selected : Selected context grant
  preparation : ReadPreparation context profile federation genesisHeight intent grant selected
  selectedExact : preparation.observed.before = selected.packed
  balancesExact : preparation.accountBalances = selected.accountBalances
  envelope : List UInt8
  checked : ResourceObservationAdmission.Checked preparation envelope

private def headerAt (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (boundary : Digest)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent) (grant : GrantRef) :
    Except String CredentialSignedEnvelopeController.SignedHeader := do
  let selected ← need (select context grant)
  (CredentialSignatureAdmission.signingHeader context.authority.snapshot
    (markerAt deployment boundary profile.semantics intent grant)
    ⟨grant.kind, requestAt context boundary profile.semantics federation genesisHeight
      intent grant selected.packed.payload.root⟩).mapError
      (fun _ => refused)

def header (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent) (grant : GrantRef) :
    Except String CredentialSignedEnvelopeController.SignedHeader :=
  headerAt context profile
    (NativeHostCodec.imageBoundary deployment.domain profile.semantics durable.image)
    federation genesisHeight intent grant

theorem headerAt_exact (context : Context deployment durable)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId)
    (genesisHeight : Nat) (intent : Intent) (grant : GrantRef) :
    headerAt context profile
      (NativeHostCodec.imageBoundary deployment.domain profile.semantics durable.image)
      federation genesisHeight intent grant =
      header context profile federation genesisHeight intent grant := rfl

/-- The success payload contains no field values, balances or policy source.
The selected public KeyRecord is reversibly encoded in the existing registry
binding in each header; this binding is not claimed to hide enrollment data. -/
def challenge (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent) : Except String Challenge := do
  let boundary := NativeHostCodec.imageBoundary deployment.domain profile.semantics durable.image
  footprintExact context intent
  let headers ← intent.grants.mapM fun grant => do
    let value ← headerAt context profile boundary federation genesisHeight intent grant
    pure (CredentialSignedEnvelopeController.headerCodec.encode value)
  pure ⟨intent, deployment.domain, profile.semantics, federation,
    boundary,
    genesisHeight + durable.image.accepted.length, headers⟩

def checkGrant (native : CredentialSignatureIO.NativeConfig)
    (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (signature : List UInt8) :
    IO (Except String (CheckedGrant context profile federation genesisHeight intent grant)) := do
  let some selected := select context grant | return .error refused
  let boundary := NativeHostCodec.imageBoundary deployment.domain profile.semantics durable.image
  let wanted := requestAt context boundary profile.semantics federation genesisHeight
    intent grant selected.packed.payload.root
  let .ok prepared := ResourceObservationAdmission.prepare context profile wanted
      (markerAt deployment boundary profile.semantics intent grant) grant.capability
      (intentCodec.encode intent)
    | return .error refused
  let .ok actualHeader := headerAt context profile boundary federation genesisHeight intent grant
    | return .error refused
  let envelope := CredentialSignatureAdmission.canonicalEnvelopeCodec.encode ⟨actualHeader, signature⟩
  match ← ResourceObservationAdmission.check native prepared envelope with
  | .error _ => return .error refused
  | .ok checked =>
      have selectedExact : prepared.observed.before = selected.packed := by
        have same := prepared.observed.present.symm.trans selected.present
        injection same
      have balancesExact : prepared.accountBalances = selected.accountBalances := by
        exact Option.some.inj (prepared.balancesExact.symm.trans selected.balancesExact)
      return .ok ⟨selected, prepared, selectedExact, balancesExact, envelope, checked⟩

structure AuthorizedIntent (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent) where
  private mk ::
  suppliedChallenge : Challenge
  challengeExact : challenge context profile federation genesisHeight intent = .ok suppliedChallenge
  footprint : footprintExact context intent = .ok ()
  grants : (index : Fin intent.grants.length) →
    CheckedGrant context profile federation genesisHeight intent (intent.grants.get index)

/-- A successful query has exactly one observation incidence, for precisely
the requested resource and authority kind. Additional granted resources cannot
be smuggled into the response selection. -/
theorem AuthorizedIntent.query_footprint
    {context : Context deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {federation : FederationId} {height : Nat} {intent : Intent}
    (accepted : AuthorizedIntent context profile federation height intent)
    (query : Query) (purpose : intent.purpose = .query query) :
    intent.grants.map (fun grant => (grant.kind, grant.target)) = [(query.kind, query.target)] :=
  footprint_success_exact context intent [(query.kind, query.target)]
    (by simp only [requiredTargets, purpose]; rfl) accepted.footprint

private def checkGrants (native : CredentialSignatureIO.NativeConfig)
    (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grants : List GrantRef) (signatures : List (List UInt8)) :
    IO (Except String ((index : Fin grants.length) →
      CheckedGrant context profile federation genesisHeight intent (grants.get index))) := do
  match grants, signatures with
  | [], [] => return .ok (fun index => Fin.elim0 index)
  | grant :: rest, signature :: remaining =>
      match ← checkGrant native context profile federation genesisHeight intent grant signature with
      | .error _ => return .error refused
      | .ok first =>
          match ← checkGrants native context profile federation genesisHeight intent rest remaining with
          | .error _ => return .error refused
          | .ok tail => return .ok (Fin.cases first tail)
  | _, _ => return .error refused

/-- Stale challenges are refused against the current exact loaded image.
No grant means no successful footprint. No callback can mint a read token. -/
def authorize (native : CredentialSignatureIO.NativeConfig)
    (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (signed : Signed) :
    IO (Except String (AuthorizedIntent context profile federation genesisHeight signed.challenge.intent)) := do
  let intent := signed.challenge.intent
  match derived : challenge context profile federation genesisHeight intent with
  | .error _ => return .error refused
  | .ok expected =>
      if same : expected = signed.challenge then
        if footprint : footprintExact context intent = .ok () then
          match ← checkGrants native context profile federation genesisHeight intent intent.grants signed.signatures with
          | .error _ => return .error refused
          | .ok grants => return .ok ⟨signed.challenge,
                derived.trans (congrArg Except.ok same), footprint, grants⟩
        else return .error refused
      else return .error refused

/-- This codec is a read view, not a writable Book/registry payload. -/
def resourceViewStream : StreamCodec (List UInt8 × List (Nat × Int)) :=
  StreamCodec.product bytesStream balanceStream

def resourceViewFrame : List UInt8 := "DREGG/NATIVE-HOST/RESOURCE-VIEW/v2".toUTF8.toList

def resourceViewCodec : IndexedProgram.LawfulCodec (List UInt8 × List (Nat × Int)) :=
  NativeHostCodec.framed resourceViewFrame resourceViewStream

def AuthorizedIntent.queryResult
    {context : Context deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {federation : FederationId} {genesisHeight : Nat} {intent : Intent}
    (accepted : AuthorizedIntent context profile federation genesisHeight intent) : Option (List UInt8) := do
  let .query query := intent.purpose | none
  if present : 0 < intent.grants.length then
    let grant := intent.grants.get ⟨0, present⟩
    let checked := accepted.grants ⟨0, present⟩
    match query.view with
    | .resource => some (resourceViewCodec.encode
        (PackedCell.bytes CanonicalCellRegistry.registry checked.selected.packed,
          checked.selected.accountBalances))
    | .policy => do
        let address := context.authority.snapshot.authState.policyAddress ⟨grant.target⟩
          (context.authority.snapshot.authState.policyRevision ⟨grant.target⟩)
        let source ← CanonicalCellRegistry.loadPolicySource deployment.domain context.directory.directory address
        some (PolicyRecordCodec.encode source.record)
    | .capability => do
        let stored ← CredentialAuthorityState.readCapability context.authority.snapshot.cell grant.kind grant.capability
        some ((CredentialAuthorityEntryCodec.storedCapabilityStream grant.kind).encode stored)
  else none

theorem observation_request_actual_root (context : Context deployment durable)
    (semantics : Digest) (federation : FederationId) (height : Nat) (intent : Intent)
    (grant : GrantRef) (kind : CanonicalCellRegistry.Kind)
    (pre : Materialized (CanonicalCellRegistry.materializer kind)) :
    (request context semantics federation height intent grant pre.root).preStateRoot = pre.root := rfl

theorem observation_preserves_resource (context : Context deployment durable)
    (semantics : Digest) (federation : FederationId) (height : Nat) (intent : Intent)
    (grant : GrantRef) (kind : CanonicalCellRegistry.Kind)
    (pre : Materialized (CanonicalCellRegistry.materializer kind)) :
    (readCandidate context semantics federation height intent grant kind pre).post.logical = pre.logical :=
  (readCandidate context semantics federation height intent grant kind pre).postcondition

omit [DecidableEq F] in
theorem observation_policy_views_equal (context : Context deployment durable)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId) (height : Nat)
    (intent : Intent) (grant : GrantRef) (selected : Selected context grant)
    (prepared : ReadPreparation context profile federation height intent grant selected) :
    (ResourceObservationAdmission.step prepared).oldState =
      (ResourceObservationAdmission.step prepared).newState :=
  ResourceObservationAdmission.policy_views_equal prepared

theorem CheckedGrant.current_generation_and_source
    {context : Context deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {federation : FederationId} {height : Nat} {intent : Intent} {grant : GrantRef}
    (checked : CheckedGrant context profile federation height intent grant) :
    let wanted := request context profile.semantics federation height intent grant checked.selected.packed.payload.root
    wanted.policyEpoch = context.authority.snapshot.authState.policyEpoch wanted.policyId ∧
      wanted.policyRevision = context.authority.snapshot.authState.policyRevision wanted.policyId :=
  ⟨checked.checked.authorization.policyEpochExact, checked.checked.authorization.policyRevisionExact⟩

theorem resourceView_roundtrip (view : List UInt8 × List (Nat × Int)) :
    resourceViewCodec.decode (resourceViewCodec.encode view) = some view :=
  resourceViewCodec.decode_encode view

theorem resourceView_canonical {bytes : List UInt8} {view : List UInt8 × List (Nat × Int)}
    (decoded : resourceViewCodec.decode bytes = some view) :
    resourceViewCodec.encode view = bytes :=
  NativeHostCodec.framed_canonical _ _ decoded

theorem accepted_footprint_exact
    {context : Context deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {federation : FederationId} {height : Nat} {intent : Intent}
    (accepted : AuthorizedIntent context profile federation height intent) :
    footprintExact context intent = .ok () := accepted.footprint

end Minidregg.Kernel.NativeObservationController
