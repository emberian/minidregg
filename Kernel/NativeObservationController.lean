/-
Signed observation and private preparation over one exact loaded native image.
The challenge discloses only the explicitly public routing, clock, commitment,
policy and public enrollment coordinates. Its response is not read authority:
every selected resource requires its own actual observe capability, native
request signature and current compiled policy. Mutating capabilities do not
implicitly grant observation. Blind submissions remain a separate receiver API.

The policy candidate is an empty patch on the actual selected resource cell.
A resource view returns that cell's packed store bytes; a capability view reads
one address of the authority cell's capability plane.
Account views add only that account's sparse balance cut from the same image;
neither the policy projection nor the returned value contains the shared Book.
This is a snapshot read, not a timing-noninterference or malicious-host claim.
-/
import Compiler.NativeObservationCodec
import Compiler.GrainResourceBirthHostCodec
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
      if let some source := GrainResourceBirthHostCodec.sourceCodec.decode bytes then
        require (source.birth.creator == intent.subject)
        let current ← need (book context)
        let sources : List Target := source.birth.resourceBatch.operations.filterMap fun operation =>
          if operation.posting.source ∈ current.accounts then
            some (.account, operation.posting.source) else none
        pure (((ResourceKind.object, source.birth.factory.value) :: sources) ++
          [(ResourceKind.object, source.toolTask),
            (ResourceKind.object, source.parentTask)]).eraseDups
      else
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

private def bindingBytesAt (deployment : Deployment) (worldRoot semantics : Digest)
    (intent : Intent) (grant : GrantRef) : List UInt8 :=
  (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream grantStream)))).encode
      (deployment.domain, semantics,
        worldRoot, intentIdentity intent, grant)

def bindingBytes (_context : Context deployment durable) (semantics : Digest)
    (intent : Intent) (grant : GrantRef) : List UInt8 :=
  bindingBytesAt deployment (durable.worldRoot)
    semantics intent grant

private def effectIdentityAt (deployment : Deployment) (worldRoot semantics : Digest)
    (intent : Intent) (grant : GrantRef) : Digest :=
  (Sp800185Cshake256.hash "DREGG.NATIVE-HOST.OBSERVE-EFFECT/v4".toUTF8.toList
    (bindingBytesAt deployment worldRoot semantics intent grant)).digest

def effectIdentity (context : Context deployment durable) (semantics : Digest)
    (intent : Intent) (grant : GrantRef) : Digest :=
  effectIdentityAt deployment (durable.worldRoot)
    semantics intent grant

private def markerAt (deployment : Deployment) (worldRoot semantics : Digest)
    (intent : Intent) (grant : GrantRef) : Nat :=
  (Sp800185Cshake256.hash "DREGG.NATIVE-HOST.OBSERVE-SIGNATURE/v4".toUTF8.toList
    (bindingBytesAt deployment worldRoot semantics intent grant)).digest.value

def marker (context : Context deployment durable) (semantics : Digest)
    (intent : Intent) (grant : GrantRef) : Nat :=
  markerAt deployment (durable.worldRoot)
    semantics intent grant

theorem effectIdentity_exact (context : Context deployment durable) (semantics : Digest)
    (intent : Intent) (grant : GrantRef) :
    effectIdentity context semantics intent grant =
      effectIdentityAt deployment
        (durable.worldRoot)
        semantics intent grant := by
  rfl

theorem marker_exact (context : Context deployment durable) (semantics : Digest)
    (intent : Intent) (grant : GrantRef) :
    marker context semantics intent grant =
      markerAt deployment
        (durable.worldRoot)
        semantics intent grant := by
  rfl

theorem bindingBytesAt_exact (context : Context deployment durable) (semantics : Digest)
    (intent : Intent) (grant : GrantRef) :
    bindingBytesAt deployment (durable.worldRoot)
      semantics intent grant = bindingBytes context semantics intent grant := by
  rfl

private def requestAt (context : Context deployment durable) (worldRoot semantics : Digest)
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
  effectsDigest := effectIdentityAt deployment worldRoot semantics intent grant
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
  requestAt context (durable.worldRoot)
    semantics federation genesisHeight intent grant preRoot

theorem requestAt_exact (context : Context deployment durable) (semantics : Digest)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (preRoot : Digest) :
    requestAt context (durable.worldRoot)
      semantics federation genesisHeight intent grant preRoot =
      request context semantics federation genesisHeight intent grant preRoot := by
  rfl

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
the same representation. Content is an object; the shared Book and the
authority cell are never observation targets through this protocol. -/
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

theorem authority_cell_is_not_observable (kind : ResourceKind) :
    observableKind kind .authority = false := by
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
    (worldRoot : Digest)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent) (grant : GrantRef) :
    Except String CredentialSignedEnvelopeController.SignedHeader := do
  let selected ← need (select context grant)
  (CredentialSignatureAdmission.signingHeader context.authority.snapshot
    (markerAt deployment worldRoot profile.semantics intent grant)
    ⟨grant.kind, requestAt context worldRoot profile.semantics federation genesisHeight
      intent grant selected.packed.payload.root⟩).mapError
      (fun _ => refused)

def header (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent) (grant : GrantRef) :
    Except String CredentialSignedEnvelopeController.SignedHeader :=
  headerAt context profile
    (durable.worldRoot)
    federation genesisHeight intent grant

theorem headerAt_exact (context : Context deployment durable)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId)
    (genesisHeight : Nat) (intent : Intent) (grant : GrantRef) :
    headerAt context profile
      (durable.worldRoot)
      federation genesisHeight intent grant =
      header context profile federation genesisHeight intent grant := by
  rfl

/-- The success payload contains no field values, balances or policy source.
The selected public KeyRecord is reversibly encoded in the existing registry
binding in each header; this binding is not claimed to hide enrollment data. -/
def challenge (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent) : Except String Challenge := do
  let worldRoot := durable.worldRoot
  footprintExact context intent
  let headers ← intent.grants.mapM fun grant => do
    let value ← headerAt context profile worldRoot federation genesisHeight intent grant
    pure (CredentialSignedEnvelopeController.headerCodec.encode value)
  pure ⟨intent, deployment.domain, profile.semantics, federation,
    worldRoot, context.authority.snapshot.cell.root,
    genesisHeight + durable.image.accepted.length, headers⟩

def checkGrant (native : CredentialSignatureIO.NativeConfig)
    (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (signature : List UInt8) :
    IO (Except String (CheckedGrant context profile federation genesisHeight intent grant)) := do
  let some selected := select context grant | return .error refused
  let worldRoot := durable.worldRoot
  let wanted := requestAt context worldRoot profile.semantics federation genesisHeight
    intent grant selected.packed.payload.root
  let .ok prepared := ResourceObservationAdmission.prepare context profile wanted
      (markerAt deployment worldRoot profile.semantics intent grant) grant.capability
      (intentCodec.encode intent)
    | return .error refused
  let .ok actualHeader := headerAt context profile worldRoot federation genesisHeight intent grant
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

/-- Version 3: the viewed bytes are the packed store cell (StoreCodec frames),
not a page. -/
def resourceViewFrame : List UInt8 := "DREGG/NATIVE-HOST/RESOURCE-VIEW/v3".toUTF8.toList

def resourceViewCodec : IndexedProgram.LawfulCodec (List UInt8 × List (Nat × Int)) :=
  NativeHostCodec.framed resourceViewFrame resourceViewStream

/-! ## Presence and past views (PLACE §2.5 K-INDEX, §4.5 K-HISTORY-READ)

`who`, `since` and `at` are ordinary queries: the footprint is the one target
and its grant is checked by the same source-owned observation admission as a
current read (`presence_views_share_footprint`). What they reveal is then cut
by the reader's own grant: only cells under the room that grant covers. -/

/-- The capability ids of one kind held in the authority cell. -/
def capabilityIds (logical : Minidregg.Theory.Store.Store CredentialAuthorityState.layout) (kind : ResourceKind) :
    Finset CapabilityId :=
  logical.support.biUnion fun address =>
    match address with
    | ⟨.capability held, named⟩ => if held = kind then {named} else ∅
    | _ => ∅

/-- A capability that currently lets its holder observe `room`: it covers the
room, carries the observe verb, is inside its window at `height`, and nothing
in its lineage is revoked or out of epoch. `Capability.Admissible` minus the
request (the holder is whoever it names). -/
def standing {kind : ResourceKind} (state : AuthState) (height room : Nat)
    (cap : Capability kind) : Bool :=
  decide (cap.scope.targets.Covers state.parent ⟨room⟩) &&
    decide (observeVerb kind ∈ cap.scope.verbs) &&
    decide (cap.notBefore ≤ height) && decide (height ≤ cap.notAfter) &&
    decide (cap.policyEpoch = state.policyEpoch cap.policyId) &&
    decide (cap.issuerEpoch = state.issuerEpoch cap.issuer) &&
    decide (RevocationKey.capability cap.id ∉ state.revoked) &&
    decide (∀ ancestor ∈ cap.ancestors, RevocationKey.capability ancestor ∉ state.revoked) &&
    decide (∀ channel ∈ cap.channels, RevocationKey.channel channel ∉ state.revoked)

/-- The members of `room`: the subjects holding a standing capability over it,
in subject order. Membership is what the room's grants say, not who acted. -/
def members (context : Context deployment durable) (kind : ResourceKind) (room height : Nat) :
    List SubjectId :=
  let state := context.authority.snapshot.authState
  let cell := context.authority.snapshot.cell
  let held : Finset Nat := (capabilityIds cell.logical kind).biUnion fun named =>
    match CredentialAuthorityState.readCapability cell kind named with
    | some stored =>
        match stored.head.holder with
        | .subject subject => if standing state height room stored.head then {subject.value} else ∅
        | .bearer => ∅
    | none => ∅
  (held.sort (· ≤ ·)).map SubjectId.mk

/-- A cell the reader may learn about: under the room, and covered by the
reader's own grant (a member with an explicit `{R}` grant learns nothing
about cells born in `R` it cannot read). -/
def sees {kind : ResourceKind} (parentage : Parentage) (reader : Capability kind) (room : Nat)
    (cell : DurableDataIntent.CellId) : Bool :=
  decide (parentage.Descends cell.value room) &&
    decide (reader.scope.targets.Covers parentage ⟨cell.value⟩)

def maxOf : List Nat → Option Nat
  | [] => none
  | height :: rest => some ((maxOf rest).elim height (max height))

theorem mem_of_maxOf : ∀ {heights : List Nat} {top : Nat}, maxOf heights = some top → top ∈ heights
  | [], _, found => by simp [maxOf] at found
  | height :: rest, top, found => by
      simp only [maxOf, Option.some.injEq] at found
      cases below : maxOf rest with
      | none => simp [below] at found; simp [found]
      | some other =>
          simp only [below, Option.elim_some] at found
          rcases Nat.le_total height other with le | ge
          · rw [Nat.max_eq_right le] at found
            exact List.mem_cons_of_mem _ (found ▸ mem_of_maxOf below)
          · rw [Nat.max_eq_left ge] at found
            simp [found]

/-- The greatest log height at which `subject` wrote a cell the reader sees. -/
def whoSeen (index : PresenceIndex.Index) (visible : DurableDataIntent.CellId → Bool)
    (subject : SubjectId) : Option Nat :=
  maxOf (index.touched.filterMap fun entry =>
    if visible entry.1 then index.lastSeenAt entry.1 subject else none)

/-- **`who` reveals only visible cells**: a reported height is the index's
`lastSeen` of a cell the reader sees. -/
theorem whoSeen_sound {index : PresenceIndex.Index} {visible : DurableDataIntent.CellId → Bool}
    {subject : SubjectId} {height : Nat} (seen : whoSeen index visible subject = some height) :
    ∃ cell, visible cell = true ∧ index.lastSeenAt cell subject = some height := by
  obtain ⟨entry, _, found⟩ := List.mem_filterMap.mp (mem_of_maxOf seen)
  by_cases shown : visible entry.1 = true
  · rw [if_pos shown] at found
    exact ⟨entry.1, shown, found⟩
  · rw [if_neg shown] at found
    cases found

/-- **`who` is refutable against the log**: on the loaded index, a reported
height is a height at which a record signed by that subject wrote a cell the
reader sees (`PresenceIndex.lastSeen_exact`). -/
theorem whoSeen_exact {visible : DurableDataIntent.CellId → Bool} {subject : SubjectId}
    {height : Nat} (seen : whoSeen durable.index visible subject = some height) :
    ∃ cell, visible cell = true ∧
      PresenceIndex.Occurs (PresenceIndex.SignedWrite cell subject) durable.image.accepted height ∧
      ∀ other, PresenceIndex.Occurs (PresenceIndex.SignedWrite cell subject)
        durable.image.accepted other → other ≤ height := by
  obtain ⟨cell, shown, last⟩ := whoSeen_sound seen
  rw [durable.indexExact] at last
  exact ⟨cell, shown, (PresenceIndex.lastSeen_exact _ cell subject height).mp last⟩

/-- One `since` entry: its absolute height, signer, transaction and the
visible cells it wrote (the others are not named). -/
structure SinceEntry where
  height : Nat
  subject : Option Nat
  transaction : Nat
  cells : List Nat
  deriving DecidableEq, Repr

def sinceFrom (visible : DurableDataIntent.CellId → Bool) (after : Nat) :
    Nat → List DurableReceiver.IntentRecord → List SinceEntry
  | _, [] => []
  | height, record :: rest =>
      let cells := (PresenceIndex.cellsOf record).filter visible
      (if after < height ∧ cells ≠ [] then
        [⟨height, record.subject.map (·.value), record.transactionId.value, cells.map (·.value)⟩]
      else []) ++ sinceFrom visible after (height + 1) rest

/-- **`since` is exact about what it names**: every entry is a record above
`after`, at its own height, with its own signer, naming only visible cells
that record wrote. -/
theorem sinceFrom_sound {visible : DurableDataIntent.CellId → Bool} {after : Nat} :
    ∀ {start : Nat} {log : List DurableReceiver.IntentRecord} {entry : SinceEntry},
      entry ∈ sinceFrom visible after start log →
        after < entry.height ∧ ∃ index record, log[index]? = some record ∧
          entry.height = start + index ∧ entry.subject = record.subject.map (·.value) ∧
          ∀ cell ∈ entry.cells, ∃ written ∈ PresenceIndex.cellsOf record,
            written.value = cell ∧ visible written = true
  | _, [], _, member => by simp [sinceFrom] at member
  | start, record :: rest, entry, member => by
      simp only [sinceFrom, List.mem_append] at member
      rcases member with here | later
      · split at here
        next above =>
          simp only [List.mem_singleton] at here
          subst here
          refine ⟨above.1, 0, record, rfl, by simp, rfl, fun cell inCells => ?_⟩
          obtain ⟨written, kept, rfl⟩ := List.mem_map.mp inCells
          obtain ⟨wrote, shown⟩ := List.mem_filter.mp kept
          exact ⟨written, wrote, rfl, shown⟩
        next => simp at here
      · obtain ⟨above, index, found, at_, height, subject, cells⟩ := sinceFrom_sound later
        exact ⟨above, index + 1, found, by simp; exact at_, by rw [height]; omega, subject, cells⟩

/-- **`since` is complete about what it names**: every record above `after`
that wrote a visible cell has an entry at its own height, with its own signer
and transaction, naming that cell. (K-DOC-HISTORY; K-INDEX proved soundness.) -/
theorem sinceFrom_complete {visible : DurableDataIntent.CellId → Bool} {after : Nat} :
    ∀ {start : Nat} {log : List DurableReceiver.IntentRecord} {index : Nat}
      {record : DurableReceiver.IntentRecord},
      log[index]? = some record → after < start + index →
      ∀ written ∈ PresenceIndex.cellsOf record, visible written = true →
        ∃ entry ∈ sinceFrom visible after start log, entry.height = start + index ∧
          entry.subject = record.subject.map (·.value) ∧
          entry.transaction = record.transactionId.value ∧ written.value ∈ entry.cells
  | _, [], _, _, found, _, _, _, _ => by simp at found
  | start, head :: rest, 0, record, found, above, written, wrote, shown => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      have kept : written ∈ (PresenceIndex.cellsOf head).filter visible :=
        List.mem_filter.mpr ⟨wrote, shown⟩
      refine ⟨⟨start, head.subject.map (·.value), head.transactionId.value,
        ((PresenceIndex.cellsOf head).filter visible).map (·.value)⟩, ?_, rfl, rfl, rfl,
        List.mem_map.mpr ⟨written, kept, rfl⟩⟩
      simp only [sinceFrom, List.mem_append]
      left
      split
      · simp
      · rename_i no
        exact absurd ⟨by simpa using above, List.ne_nil_of_mem kept⟩ no
  | start, head :: rest, index + 1, record, found, above, written, wrote, shown => by
      simp only [List.getElem?_cons_succ] at found
      obtain ⟨entry, member, height, subject, transaction, cell⟩ :=
        sinceFrom_complete (visible := visible) (after := after) (start := start + 1) (index := index) found (by omega) written wrote shown
      refine ⟨entry, ?_, by omega, subject, transaction, cell⟩
      simp only [sinceFrom, List.mem_append]
      exact Or.inr member

/-- `history DOC` (K-DOC-HISTORY): the `since` entries that wrote the document
cell itself. On the host this is `since DOC 0` cut to `DOC`, so it is K-INDEX's
`who` rule: only cells the reader's current grant covers. -/
def historyOf (target : Nat) (entries : List SinceEntry) : List SinceEntry :=
  entries.filter fun entry => entry.cells.contains target

/-- **Every history row is an accepted action on that cell**: a record of the
log at that row's height, signed by that row's subject, that wrote the cell. -/
theorem history_sound {visible : DurableDataIntent.CellId → Bool} {after start target : Nat}
    {log : List DurableReceiver.IntentRecord} {row : SinceEntry}
    (member : row ∈ historyOf target (sinceFrom visible after start log)) :
    after < row.height ∧ ∃ index record, log[index]? = some record ∧
      row.height = start + index ∧ row.subject = record.subject.map (·.value) ∧
      ∃ written ∈ PresenceIndex.cellsOf record, written.value = target ∧ visible written = true := by
  obtain ⟨inSince, names⟩ := List.mem_filter.mp member
  obtain ⟨above, index, record, found, height, subject, cells⟩ := sinceFrom_sound inSince
  exact ⟨above, index, record, found, height, subject, cells target (by simpa using names)⟩

/-- **Every accepted action on a visible cell is a history row**, at its height,
with its signer and transaction. -/
theorem history_complete {visible : DurableDataIntent.CellId → Bool} {after start target : Nat}
    {log : List DurableReceiver.IntentRecord} {index : Nat} {record : DurableReceiver.IntentRecord}
    (found : log[index]? = some record) (above : after < start + index)
    {written : DurableDataIntent.CellId} (wrote : written ∈ PresenceIndex.cellsOf record)
    (named : written.value = target) (shown : visible written = true) :
    ∃ row ∈ historyOf target (sinceFrom visible after start log), row.height = start + index ∧
      row.subject = record.subject.map (·.value) ∧ row.transaction = record.transactionId.value := by
  obtain ⟨entry, member, height, subject, transaction, cell⟩ :=
    sinceFrom_complete found above written wrote shown
  refine ⟨entry, List.mem_filter.mpr ⟨member, ?_⟩, height, subject, transaction⟩
  rw [← named]
  simpa using cell

/-- The canonical bytes of `target` as of absolute height `height`; refused
above the current height and below the genesis height (the retention floor:
the Store keeps every record since the seed). -/
def atBytes (genesisHeight height target : Nat) : Option (List UInt8) :=
  if genesisHeight ≤ height ∧ height - genesisHeight ≤ durable.height then
    (durable.atPrefix (height - genesisHeight)).map fun snapshot => snapshot.canonicalBytes ⟨target⟩
  else none

theorem atBytes_current (genesisHeight target : Nat) :
    atBytes (durable := durable) genesisHeight (genesisHeight + durable.height) target =
      some (durable.snapshot.canonicalBytes ⟨target⟩) := by
  unfold atBytes
  rw [if_pos ⟨Nat.le_add_right _ _, by omega⟩, Nat.add_sub_cancel_left, durable.atPrefix_current]
  rfl

theorem atBytes_above_refused {genesisHeight height : Nat} (target : Nat)
    (above : genesisHeight + durable.height < height) :
    atBytes (durable := durable) genesisHeight height target = none := by
  unfold atBytes
  rw [if_neg (by omega)]

theorem atBytes_below_floor {genesisHeight height : Nat} (target : Nat)
    (below : height < genesisHeight) :
    atBytes (durable := durable) genesisHeight height target = none := by
  unfold atBytes
  rw [if_neg (by omega)]

/-- **`at` is a fold of the prefix**: below the loaded checkpoint, the bytes
are the genesis replay of the first `height - genesisHeight` records
(`Loaded.atPrefix_below`; above it, `Loaded.atPrefix_from_checkpoint`). -/
theorem at_is_fold_prefix {genesisHeight height : Nat} (target : Nat)
    (floor : genesisHeight ≤ height)
    (below : height - genesisHeight < durable.baseHeight) :
    atBytes (durable := durable) genesisHeight height target =
      ((durable.prefixImage (height - genesisHeight)).restore ResourceBirthCodec.rootBytes).map
        fun snapshot => snapshot.canonicalBytes ⟨target⟩ := by
  unfold atBytes
  rw [if_pos ⟨floor, Nat.le_trans (Nat.le_of_lt below) durable.withinLog⟩, durable.atPrefix_below below]

/-- **At the current height, `at` is the ordinary read**: the lifecycle bytes
of exactly the packed cell a current resource read returns. -/
theorem at_current_eq_read (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    {target : Nat} {packed : PackedCell Registry}
    (present : directory.directory.slots target = .present packed) (genesisHeight : Nat) :
    atBytes (durable := durable) genesisHeight (genesisHeight + durable.height) target =
      some (ResourceBirthCodec.LifecycleImage.bytes Registry (.live packed)) := by
  rw [atBytes_current, ← directory.bytes_exact target]
  simp [ResourceBirthCodec.LifecycleImage.view, present]

def whoViewStream : StreamCodec (List (Nat × Option Nat)) :=
  StreamCodec.list (StreamCodec.product StreamCodec.nat (StreamCodec.option StreamCodec.nat))

def whoViewFrame : List UInt8 := "DREGG/NATIVE-HOST/WHO-VIEW/v1".toUTF8.toList

def whoViewCodec : IndexedProgram.LawfulCodec (List (Nat × Option Nat)) :=
  NativeHostCodec.framed whoViewFrame whoViewStream

def sinceEntryStream : StreamCodec SinceEntry :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product (StreamCodec.option StreamCodec.nat)
      (StreamCodec.product StreamCodec.nat (StreamCodec.list StreamCodec.nat))))
    (fun entry => (entry.height, entry.subject, entry.transaction, entry.cells))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro entry; cases entry; rfl)

def sinceViewFrame : List UInt8 := "DREGG/NATIVE-HOST/SINCE-VIEW/v1".toUTF8.toList

def sinceViewCodec : IndexedProgram.LawfulCodec (List SinceEntry) :=
  NativeHostCodec.framed sinceViewFrame (StreamCodec.list sinceEntryStream)

def atViewFrame : List UInt8 := "DREGG/NATIVE-HOST/AT-VIEW/v1".toUTF8.toList

/-- `(height, lifecycle bytes)`: the cell's canonical stored bytes at that height. -/
def atViewCodec : IndexedProgram.LawfulCodec (Nat × List UInt8) :=
  NativeHostCodec.framed atViewFrame (StreamCodec.product StreamCodec.nat bytesStream)

/-! ## Coverage at the asked height (K-DOC-HISTORY)

`at h` is answered only to a grant that stood at `h`. The authority state at
`h` is reconstructible: it is the authority cell of the same prefix replay that
produces the bytes, loaded by the one `loadDeployment` route. So a reader added
at height 30 is refused `at 29` — the room as it was had no such member. -/

/-- A holder names `subject` (a bearer capability names anyone). -/
def holderNames (subject : SubjectId) : Holder → Bool
  | .bearer => true
  | .subject bound => decide (bound = subject)

theorem holderNames_covers {subject : SubjectId} {holder : Holder}
    (names : holderNames subject holder = true) : holder.Covers subject := by
  cases holder with
  | bearer => trivial
  | subject bound => simpa [holderNames, Holder.Covers] using names

/-- The grant as the authority cell of `snapshot` holds it: present, naming
`subject`, and `standing` over `target` at `height` (window, epochs,
revocations and parentage all read from that same snapshot). -/
def grantStandingIn (snapshot : CredentialAuthorityDomainReceiver.PhysicalSnapshot)
    (subject : SubjectId) (grant : GrantRef) (height target : Nat) : Bool :=
  match CredentialAuthorityDomainReceiver.loadDeployment deployment snapshot with
  | none => false
  | some authority =>
      match CredentialAuthorityState.readCapability authority.snapshot.cell grant.kind grant.capability with
      | none => false
      | some stored => holderNames subject stored.head.holder &&
          standing authority.snapshot.authState height target stored.head

/-- `at height`, answered against the grants as they stood at `height`. -/
def atCovered (genesisHeight height : Nat) (subject : SubjectId) (grant : GrantRef) (target : Nat) :
    Except String (List UInt8) :=
  if height > genesisHeight + durable.height then
    .error s!"history read refused: height {height} is above the current height {genesisHeight + durable.height}"
  else if height < genesisHeight then
    .error s!"history read refused: height {height} is below the retention floor {genesisHeight}"
  else
    match durable.atPrefix (height - genesisHeight) with
    | none => .error refused
    | some snapshot =>
        if grantStandingIn (deployment := deployment) snapshot subject grant height target then
          .ok (atViewCodec.encode (height, snapshot.canonicalBytes ⟨target⟩))
        else
          .error s!"history read refused: this grant did not cover {target} at height {height}"

/-- **`at` answers only a grant that stood at that height**: the bytes are
K-INDEX's `atBytes` (the fold of the prefix), and the authority cell of that
same prefix holds the grant's capability, naming the reader and standing over
the target at that height. -/
theorem atCovered_sound {genesisHeight height : Nat} {subject : SubjectId} {grant : GrantRef}
    {target : Nat} {out : List UInt8}
    (answered : atCovered (deployment := deployment) (durable := durable)
      genesisHeight height subject grant target = .ok out) :
    ∃ snapshot authority stored,
      durable.atPrefix (height - genesisHeight) = some snapshot ∧
      CredentialAuthorityDomainReceiver.loadDeployment deployment snapshot = some authority ∧
      CredentialAuthorityState.readCapability authority.snapshot.cell grant.kind grant.capability =
        some stored ∧
      stored.head.holder.Covers subject ∧
      standing authority.snapshot.authState height target stored.head = true ∧
      atBytes (durable := durable) genesisHeight height target =
        some (snapshot.canonicalBytes ⟨target⟩) ∧
      out = atViewCodec.encode (height, snapshot.canonicalBytes ⟨target⟩) := by
  unfold atCovered at answered
  split at answered
  · cases answered
  rename_i notAbove
  split at answered
  · cases answered
  rename_i notBelow
  split at answered
  · cases answered
  rename_i snapshot found
  split at answered
  · rename_i covered
    unfold grantStandingIn at covered
    split at covered
    · cases covered
    rename_i authority loaded
    split at covered
    · cases covered
    rename_i stored read
    simp only [Bool.and_eq_true] at covered
    cases answered
    refine ⟨snapshot, authority, stored, found, loaded, read, holderNames_covers covered.1,
      covered.2, ?_, rfl⟩
    unfold atBytes
    rw [if_pos ⟨by omega, by omega⟩, found]
    rfl
  · cases answered

/-- Refuting pole: a grant whose capability the authority cell at that height
does not hold (a reader added later) is refused, with the height named. -/
theorem atCovered_refused_before_grant {genesisHeight height : Nat} {subject : SubjectId}
    {grant : GrantRef} {target : Nat}
    {snapshot : CredentialAuthorityDomainReceiver.PhysicalSnapshot}
    {authority : CredentialAuthorityDomainReceiver.Loaded deployment snapshot}
    (floor : genesisHeight ≤ height) (within : height ≤ genesisHeight + durable.height)
    (found : durable.atPrefix (height - genesisHeight) = some snapshot)
    (loaded : CredentialAuthorityDomainReceiver.loadDeployment deployment snapshot = some authority)
    (absent : CredentialAuthorityState.readCapability authority.snapshot.cell grant.kind
      grant.capability = none) :
    atCovered (deployment := deployment) (durable := durable) genesisHeight height subject grant target =
      .error s!"history read refused: this grant did not cover {target} at height {height}" := by
  unfold atCovered
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [found]
  rw [if_neg]
  simp [grantStandingIn, loaded, absent]

/-- Satisfiable pole: a grant standing at that height is answered, with the prefix's bytes. -/
theorem atCovered_answers_standing {genesisHeight height : Nat} {subject : SubjectId}
    {grant : GrantRef} {target : Nat}
    {snapshot : CredentialAuthorityDomainReceiver.PhysicalSnapshot}
    (floor : genesisHeight ≤ height) (within : height ≤ genesisHeight + durable.height)
    (found : durable.atPrefix (height - genesisHeight) = some snapshot)
    (stands : grantStandingIn (deployment := deployment) snapshot subject grant height target = true) :
    atCovered (deployment := deployment) (durable := durable) genesisHeight height subject grant target =
      .ok (atViewCodec.encode (height, snapshot.canonicalBytes ⟨target⟩)) := by
  unfold atCovered
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [found, stands, if_true]

/-- Every query view, `who`/`since`/`at` included, has the same one-target
footprint as a current read of that target: the same grant, the same check. -/
theorem presence_views_share_footprint (context : Context deployment durable)
    (subject : SubjectId) (nonce : Nat) (query : Query) (grants : List GrantRef) :
    requiredTargets context ⟨subject, nonce, .query query, grants⟩ = .ok [(query.kind, query.target)] :=
  rfl

/-! ## Links and backlinks (K-DOC-INDEX)

`backlinks` and `links` are ordinary queries with the one-target footprint
(`presence_views_share_footprint`). `links` is the target's own forward index,
part of the cell the grant already reads. `backlinks` names SOURCE cells, so
each row is cut by what the reader may observe now: a source cell is shown
only if a standing capability the reader holds (the `who` membership test,
`standing`) covers it. This is the coverage of "the documents this reader can
read", not of the one presented grant: the presented grant authorizes asking
about the target, and the reader's other standing grants decide which sources
it may learn about. -/

/-- A stored object capability names `reader` and currently lets it observe `cell`. -/
def holdsStanding (context : Context deployment durable) (reader : SubjectId) (height cell : Nat)
    (named : CapabilityId) : Bool :=
  match CredentialAuthorityState.readCapability context.authority.snapshot.cell .object named with
  | some stored => decide (stored.head.holder = .subject reader) &&
      standing context.authority.snapshot.authState height cell stored.head
  | none => false

/-- A cell the reader may observe at `height`: some standing capability it holds covers it. -/
def readable (context : Context deployment durable) (reader : SubjectId) (height : Nat)
    (cell : DurableDataIntent.CellId) : Bool :=
  decide (∃ named ∈ capabilityIds context.authority.snapshot.cell.logical .object,
    holdsStanding context reader height cell.value named = true)

theorem readable_sound {context : Context deployment durable} {reader : SubjectId} {height : Nat}
    {cell : DurableDataIntent.CellId} (shown : readable context reader height cell = true) :
    ∃ named stored, CredentialAuthorityState.readCapability context.authority.snapshot.cell .object named =
        some stored ∧ stored.head.holder = .subject reader ∧
      standing context.authority.snapshot.authState height cell.value stored.head = true := by
  obtain ⟨named, _, holds⟩ := of_decide_eq_true shown
  unfold holdsStanding at holds
  split at holds
  · rename_i stored found
    simp only [Bool.and_eq_true, decide_eq_true_eq] at holds
    exact ⟨named, stored, found, holds.1, holds.2⟩
  · cases holds

/-- One link row: source cell, link id, the source range's start atom, the
link's revision (the operation that wrote it), the absolute height from which
it has been live, the target's kind and id, and the relation. -/
structure LinkRow where
  source : Nat
  link : Nat
  anchor : Option Nat
  revision : Nat
  height : Nat
  kind : Nat
  target : Nat
  relation : Nat
  deriving DecidableEq, Repr

def linkRow (genesisHeight : Nat) (pair : DurableDataIntent.CellId × LinkIndex.Entry) : LinkRow :=
  ⟨pair.1.value, pair.2.link.digest.value,
    (pair.2.record.source.bind fun range => range.start.neighbor).map (·.digest.value),
    pair.2.record.operation.digest.value, genesisHeight + pair.2.height,
    LinkIndex.targetKind pair.2.record.target, LinkIndex.targetId pair.2.record.target,
    pair.2.record.relation.value⟩

def linkRowStream : StreamCodec LinkRow :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product (StreamCodec.option StreamCodec.nat) (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))))
    (fun row => (row.source, row.link, row.anchor, row.revision, row.height, row.kind, row.target,
      row.relation))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1, wire.2.2.2.2.1, wire.2.2.2.2.2.1,
      wire.2.2.2.2.2.2.1, wire.2.2.2.2.2.2.2⟩)
    (by intro row; cases row; rfl)

def linkViewFrame : List UInt8 := "DREGG/NATIVE-HOST/LINK-VIEW/v1".toUTF8.toList

/-- `(backlinks?, rows)`: which view, then its rows. -/
def linkViewCodec : IndexedProgram.LawfulCodec (Bool × List LinkRow) :=
  NativeHostCodec.framed linkViewFrame
    (StreamCodec.product StreamCodec.bool (StreamCodec.list linkRowStream))

/-- The keys a target cell answers to: its document, and its elements when it
is a content cell. -/
def targetKeys (packed : PackedCell Registry) (target : Nat) : List LinkIndex.TargetKey :=
  match packed with
  | ⟨.content, payload⟩ => LinkIndex.documentKeys ⟨⟨target⟩⟩ payload.logical
  | _ => [.document ⟨⟨target⟩⟩]

/-- **A backlinks view is exact about what it shows**: every row's source cell
satisfies the reader's coverage, points at an asked key, is live in its source
cell's latest accepted write, and has been live since its height
(`LinkIndex.backlinks_sound` on the loaded index, `linksExact`). -/
theorem backlinks_view_sound {visible : DurableDataIntent.CellId → Bool}
    {keys : List LinkIndex.TargetKey} {pair : DurableDataIntent.CellId × LinkIndex.Entry}
    (member : pair ∈ durable.links.backlinks visible keys) :
    visible pair.1 = true ∧ LinkIndex.TargetKey.of pair.2.record.target ∈ keys ∧
      pair.2.key ∈ LinkIndex.latestLinks pair.1 durable.image.accepted ∧
      PresenceIndex.Occurs (LinkIndex.WroteLink pair.1 pair.2.key) durable.image.accepted
        pair.2.height := by
  rw [durable.linksExact] at member
  exact LinkIndex.backlinks_sound _ _ _ member

/-- **A reader sees only backlinks from cells it may observe**: each row of
the view a reader gets names a source cell that some standing capability the
reader holds covers. -/
theorem backlinks_covered (context : Context deployment durable) (reader : SubjectId)
    (height : Nat) (keys : List LinkIndex.TargetKey) {pair : DurableDataIntent.CellId × LinkIndex.Entry}
    (member : pair ∈ durable.links.backlinks (readable context reader height) keys) :
    ∃ named stored, CredentialAuthorityState.readCapability context.authority.snapshot.cell .object named =
        some stored ∧ stored.head.holder = .subject reader ∧
      standing context.authority.snapshot.authState height pair.1.value stored.head = true :=
  readable_sound (LinkIndex.backlinks_covered _ _ _ member)

/-- **A links view is the cell's latest live links.** -/
theorem links_view_exact (cell : DurableDataIntent.CellId) :
    (durable.links.links cell).map LinkIndex.Entry.key = LinkIndex.latestLinks cell durable.image.accepted := by
  rw [durable.linksExact]
  exact LinkIndex.links_exact _ cell

/-- info: 'Minidregg.Kernel.NativeObservationController.readable_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.readable_sound
/-- info: 'Minidregg.Kernel.NativeObservationController.backlinks_view_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.backlinks_view_sound
/-- info: 'Minidregg.Kernel.NativeObservationController.backlinks_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.backlinks_covered
/-- info: 'Minidregg.Kernel.NativeObservationController.links_view_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.links_view_exact

def AuthorizedIntent.queryResult
    {context : Context deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {federation : FederationId} {genesisHeight : Nat} {intent : Intent}
    (accepted : AuthorizedIntent context profile federation genesisHeight intent) :
    Except String (List UInt8) := do
  let .query query := intent.purpose | throw "signed observation purpose is not a query"
  if present : 0 < intent.grants.length then
    let grant := intent.grants.get ⟨0, present⟩
    let checked := accepted.grants ⟨0, present⟩
    let state := context.authority.snapshot.authState
    let reader := CredentialAuthorityState.readCapability context.authority.snapshot.cell
      grant.kind grant.capability
    match query.view with
    | .resource => pure (resourceViewCodec.encode
        (PackedCell.bytes CanonicalCellRegistry.registry checked.selected.packed,
          checked.selected.accountBalances))
    | .policy => do
        let address := state.policyAddress ⟨grant.target⟩ (state.policyRevision ⟨grant.target⟩)
        let some source := CanonicalCellRegistry.loadPolicySource deployment.domain
            context.directory.directory address | throw refused
        pure (PolicyRecordCodec.encode source.record)
    | .capability => do
        let some stored := reader | throw refused
        pure ((CredentialAuthorityEntryCodec.storedCapabilityStream grant.kind).encode stored)
    | .who => do
        let some stored := reader | throw refused
        let visible := sees state.parent stored.head query.target
        let height := genesisHeight + durable.height
        pure (whoViewCodec.encode ((members context grant.kind query.target height).map fun subject =>
          (subject.value, (whoSeen durable.index visible subject).map (genesisHeight + ·))))
    | .since after => do
        let some stored := reader | throw refused
        let visible := sees state.parent stored.head query.target
        pure (sinceViewCodec.encode (sinceFrom visible after (genesisHeight + 1) durable.image.accepted))
    | .atHeight height =>
        atCovered (deployment := deployment) (durable := durable) genesisHeight height intent.subject
          grant query.target
    | .backlinks =>
        let visible := readable context intent.subject (genesisHeight + durable.height)
        let keys := targetKeys checked.selected.packed grant.target
        pure (linkViewCodec.encode (true,
          (durable.links.backlinks visible keys).map (linkRow genesisHeight)))
    | .links =>
        pure (linkViewCodec.encode (false,
          (durable.links.links ⟨grant.target⟩).map fun entry => linkRow genesisHeight (⟨grant.target⟩, entry)))
  else throw refused

/-- info: 'Minidregg.Kernel.NativeObservationController.whoSeen_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.whoSeen_sound
/-- info: 'Minidregg.Kernel.NativeObservationController.whoSeen_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.whoSeen_exact
/-- info: 'Minidregg.Kernel.NativeObservationController.sinceFrom_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.sinceFrom_sound
/-- info: 'Minidregg.Kernel.NativeObservationController.atBytes_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.atBytes_current
/-- info: 'Minidregg.Kernel.NativeObservationController.atBytes_above_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.atBytes_above_refused
/-- info: 'Minidregg.Kernel.NativeObservationController.atBytes_below_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.atBytes_below_floor
/-- info: 'Minidregg.Kernel.NativeObservationController.at_is_fold_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.at_is_fold_prefix
/-- info: 'Minidregg.Kernel.NativeObservationController.at_current_eq_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.at_current_eq_read
/-- info: 'Minidregg.Kernel.NativeObservationController.presence_views_share_footprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.presence_views_share_footprint

/-- The `at` view of a signed query is `atCovered` over the query's first grant. -/
theorem AuthorizedIntent.queryResult_at
    {context : Context deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {federation : FederationId} {genesisHeight : Nat} {intent : Intent}
    (accepted : AuthorizedIntent context profile federation genesisHeight intent)
    {query : Query} {height : Nat} (purpose : intent.purpose = .query query)
    (view : query.view = .atHeight height) (present : 0 < intent.grants.length) :
    accepted.queryResult = atCovered (deployment := deployment) (durable := durable)
      genesisHeight height intent.subject (intent.grants.get ⟨0, present⟩) query.target := by
  unfold AuthorizedIntent.queryResult
  simp only [purpose, view, dif_pos present]

/-- **`at_respects_coverage_at_height`**: a signed `at h` query that is
answered was answered to a grant the authority cell at `h` held, naming the
signer and standing over the target at `h`; the answer is the fold of the
prefix. A reader who was not in the room at `h` gets nothing at `h`. -/
theorem at_respects_coverage_at_height
    {context : Context deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {federation : FederationId} {genesisHeight : Nat} {intent : Intent}
    (accepted : AuthorizedIntent context profile federation genesisHeight intent)
    {query : Query} {height : Nat} {out : List UInt8} (purpose : intent.purpose = .query query)
    (view : query.view = .atHeight height) (answered : accepted.queryResult = .ok out) :
    ∃ present : 0 < intent.grants.length, ∃ snapshot : CredentialAuthorityDomainReceiver.PhysicalSnapshot,
      ∃ authority : CredentialAuthorityDomainReceiver.Loaded deployment snapshot, ∃ stored,
      durable.atPrefix (height - genesisHeight) = some snapshot ∧
      CredentialAuthorityDomainReceiver.loadDeployment deployment snapshot = some authority ∧
      CredentialAuthorityState.readCapability authority.snapshot.cell
        (intent.grants.get ⟨0, present⟩).kind (intent.grants.get ⟨0, present⟩).capability =
        some stored ∧
      stored.head.holder.Covers intent.subject ∧
      standing authority.snapshot.authState height query.target stored.head = true ∧
      out = atViewCodec.encode (height, snapshot.canonicalBytes ⟨query.target⟩) := by
  by_cases present : 0 < intent.grants.length
  · rw [accepted.queryResult_at purpose view present] at answered
    obtain ⟨snapshot, authority, stored, found, loaded, read, holder, stands, _, encoded⟩ :=
      atCovered_sound answered
    exact ⟨present, snapshot, authority, stored, found, loaded, read, holder, stands, encoded⟩
  · unfold AuthorizedIntent.queryResult at answered
    simp only [purpose, dif_neg present] at answered
    cases answered

/-- info: 'Minidregg.Kernel.NativeObservationController.sinceFrom_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.sinceFrom_complete
/-- info: 'Minidregg.Kernel.NativeObservationController.history_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.history_sound
/-- info: 'Minidregg.Kernel.NativeObservationController.history_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.history_complete
/-- info: 'Minidregg.Kernel.NativeObservationController.atCovered_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.atCovered_sound
/-- info: 'Minidregg.Kernel.NativeObservationController.atCovered_refused_before_grant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.atCovered_refused_before_grant
/-- info: 'Minidregg.Kernel.NativeObservationController.atCovered_answers_standing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.atCovered_answers_standing
/-- info: 'Minidregg.Kernel.NativeObservationController.at_respects_coverage_at_height' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.at_respects_coverage_at_height

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

/-- **Challenge binding (DATAMODEL §3.4).**  A challenge carries the world root
and the height of the one loaded image it was computed from. -/
theorem challenge_bound {context : Context deployment durable}
    {profile : CanonicalRuntimeProfile.Profile F} {federation : FederationId}
    {genesisHeight : Nat} {intent : Intent} {issued : Challenge}
    (h : challenge context profile federation genesisHeight intent = .ok issued) :
    issued.worldRoot = durable.worldRoot ∧
      issued.height = genesisHeight + NativeHostCodec.height durable.image := by
  unfold challenge at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · simp only [Except.ok.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩

/-- info: 'Minidregg.Kernel.NativeObservationController.challenge_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms challenge_bound


end Minidregg.Kernel.NativeObservationController
