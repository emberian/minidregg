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

/-- What an unauthenticated requester may be told. Before its signature has
verified, a refusal names only facts the challenge endpoint already publishes:
whether the named subject has an enrolled key (the challenge's public
enrollment coordinate) and whether the signed challenge's world root is current
(the world root is a public challenge field). Every other pre-signature
failure -- an absent or unobservable target, a footprint that does not match
the state-dependent required set -- is the uniform `undisclosed`. -/
def preAuthentication (refusal : Refusal) : Refusal :=
  match refusal.reason with
  | .unknownKey => refusal
  | .staleRoot => refusal
  | _ => .of .undisclosed

theorem preAuthentication_reasons (refusal : Refusal) :
    (preAuthentication refusal).reason = .unknownKey ∨
      (preAuthentication refusal).reason = .staleRoot ∨
      preAuthentication refusal = .of .undisclosed := by
  unfold preAuthentication
  split <;> simp_all

theorem preAuthentication_noGrant :
    preAuthentication (.of .noGrant) = .of .undisclosed := rfl

theorem preAuthentication_unknownKey :
    preAuthentication (.of .unknownKey) = .of .unknownKey := rfl

/-- Source contract named by the deployed profile: exact role selection,
schema-native unchanged views, explicit observation grants for the entire
joint target list, and the one loaded image throughout authorization. -/
abbrev observationProjectionVersion := CanonicalRuntimeProfile.observationProjectionVersion

private def need {α : Type} (reason : RefusalReason) : Option α → Except Refusal α
  | none => .error (.of reason)
  | some value => .ok value

private def require (reason : RefusalReason) (condition : Bool) : Except Refusal Unit :=
  if condition then .ok () else .error (.of reason)

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
    Except Refusal (List Target) := do
  match intent.purpose with
  | .query query => pure [(query.kind, query.target)]
  | .prepare (.invoke bytes) =>
      let command ← need .malformed (DeclaredResourceController.commandCodec.decode bytes)
      require .malformed (command.subject == intent.subject)
      require .malformed command.targetsWellFormed
      pure (command.targets.map fun target => (target.kind, target.target))
  | .prepare (.delegate bytes) =>
      let command ← need .malformed (CapabilityDelegationController.commandCodec.decode bytes)
      require .malformed (command.2.subject == intent.subject)
      -- Observing another grant must not expose this named parent's lineage.
      require .malformed (intent.grants.all fun grant => grant.capability == command.2.declaration.parentId)
      pure [(command.1, command.2.declaration.target.value)]
  | .prepare (.revoke bytes) =>
      let command ← need .malformed (CapabilityRevocationController.commandCodec.decode bytes)
      require .malformed (command.2.subject == intent.subject)
      -- Observing the resource is separate from exercising its management
      -- grant. The signing plan exposes no stored victim/lineage payload.
      pure [(command.1, command.2.target.value)]
  | .prepare (.install subject _ bytes) =>
      require .malformed (subject == intent.subject)
      let declaration ← need .malformed (PolicyInstallController.decodeDeclaration bytes)
      let kind ← need .noGrant (declaredKind context declaration.source.policyId.value)
      pure [(kind, declaration.source.policyId.value)]
  | .prepare (.birth bytes _) =>
      if let some source := GrainResourceBirthHostCodec.sourceCodec.decode bytes then
        require .malformed (source.birth.creator == intent.subject)
        let current ← need .noGrant (book context)
        let sources : List Target := source.birth.resourceBatch.operations.filterMap fun operation =>
          if operation.posting.source ∈ current.accounts then
            some (.account, operation.posting.source) else none
        pure (((ResourceKind.object, source.birth.factory.value) :: sources) ++
          [(ResourceKind.object, source.toolTask),
            (ResourceKind.object, source.parentTask)]).eraseDups
      else
        let descriptor ← need .malformed (CanonicalCellRegistry.sourceEncoding.codec.decode bytes)
        require .malformed (descriptor.creator == intent.subject)
        let current ← need .noGrant (book context)
        let sources := descriptor.resourceBatch.operations.filterMap fun operation =>
          if operation.posting.source ∈ current.accounts then
            some (.account, operation.posting.source) else none
        pure ((.object, descriptor.factory.value) :: sources).eraseDups

def footprintExact (context : Context deployment durable) (intent : Intent) : Except Refusal Unit :=
  match requiredTargets context intent with
  | .error reason => .error reason
  | .ok required =>
      if intent.grants.map (fun grant => (grant.kind, grant.target)) = required then .ok ()
      else .error (.of .malformed)

/-- Missing, additional, reordered or wrong-kind read selections are all
refused before any selected values can be returned. -/
theorem footprint_mismatch_refused (context : Context deployment durable) (intent : Intent)
    (required : List Target) (derived : requiredTargets context intent = .ok required)
    (different : intent.grants.map (fun grant => (grant.kind, grant.target)) ≠ required) :
    footprintExact context intent = .error (.of .malformed) := by
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
the same representation. Content and streams are objects; the shared Book and the
authority cell are never observation targets through this protocol. -/
def observableKind (kind : ResourceKind) (physical : CanonicalCellRegistry.Kind) : Bool :=
  decide (ResourceTargetAdmission.externalKind physical = some kind)

theorem observable_roles_exact (kind : ResourceKind) (physical : CanonicalCellRegistry.Kind) :
    observableKind kind physical = true ↔
      (kind = .object ∧ (physical = .declaredObject ∨ physical = .content ∨ physical = .stream)) ∨
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
    Except Refusal CredentialSignedEnvelopeController.SignedHeader := do
  let selected ← need .noGrant (select context grant)
  (CredentialSignatureAdmission.signingHeader context.authority.snapshot
    (markerAt deployment worldRoot profile.semantics intent grant)
    ⟨grant.kind, requestAt context worldRoot profile.semantics federation genesisHeight
      intent grant selected.packed.payload.root⟩).mapError
      (fun reason => .of (RefusalReason.ofSignature reason))

def header (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent) (grant : GrantRef) :
    Except Refusal CredentialSignedEnvelopeController.SignedHeader :=
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
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent) : Except Refusal Challenge := do
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
    IO (Except Refusal (CheckedGrant context profile federation genesisHeight intent grant)) := do
  let some selected := select context grant | return .error (preAuthentication (.of .noGrant))
  let worldRoot := durable.worldRoot
  let wanted := requestAt context worldRoot profile.semantics federation genesisHeight
    intent grant selected.packed.payload.root
  match ResourceObservationAdmission.prepare context profile wanted
      (markerAt deployment worldRoot profile.semantics intent grant) grant.capability
      (intentCodec.encode intent) with
  | .error reason => return .error (preAuthentication reason)
  | .ok prepared =>
  match headerAt context profile worldRoot federation genesisHeight intent grant with
  | .error reason => return .error (preAuthentication reason)
  | .ok actualHeader =>
  let envelope := CredentialSignatureAdmission.canonicalEnvelopeCodec.encode ⟨actualHeader, signature⟩
  -- From here the refusal is the signed requester's own: its signature is
  -- checked first, then its capability and the resource's current law.
  match ← ResourceObservationAdmission.check native prepared envelope with
  | .error reason => return .error reason
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
    IO (Except Refusal ((index : Fin grants.length) →
      CheckedGrant context profile federation genesisHeight intent (grants.get index))) := do
  match grants, signatures with
  | [], [] => return .ok (fun index => Fin.elim0 index)
  | grant :: rest, signature :: remaining =>
      match ← checkGrant native context profile federation genesisHeight intent grant signature with
      | .error reason => return .error reason
      | .ok first =>
          match ← checkGrants native context profile federation genesisHeight intent rest remaining with
          | .error reason => return .error reason
          | .ok tail => return .ok (Fin.cases first tail)
  | _, _ => return .error (preAuthentication (.of .malformed))

/-- A supplied challenge that differs from the current one is stale exactly
when it names another world root, authority root or height (all public
challenge fields); any other difference is a request that was never issued by
this Host, and is not described. -/
def challengeMismatch (expected supplied : Challenge) : Refusal :=
  if expected.worldRoot ≠ supplied.worldRoot ∨ expected.authorityRoot ≠ supplied.authorityRoot ∨
      expected.height ≠ supplied.height then
    .of .staleRoot
  else .of .undisclosed

theorem challengeMismatch_stale (expected supplied : Challenge)
    (moved : expected.worldRoot ≠ supplied.worldRoot) :
    challengeMismatch expected supplied = .of .staleRoot := by
  simp [challengeMismatch, moved]

theorem challengeMismatch_same_root (expected supplied : Challenge)
    (world : expected.worldRoot = supplied.worldRoot)
    (authority : expected.authorityRoot = supplied.authorityRoot)
    (height : expected.height = supplied.height) :
    challengeMismatch expected supplied = .of .undisclosed := by
  simp [challengeMismatch, world, authority, height]

/-- Stale challenges are refused against the current world root.
No grant means no successful footprint. No callback can mint a read token.
Before the signature verifies only `preAuthentication` reasons are named. -/
def authorize (native : CredentialSignatureIO.NativeConfig)
    (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (signed : Signed) :
    IO (Except Refusal (AuthorizedIntent context profile federation genesisHeight signed.challenge.intent)) := do
  let intent := signed.challenge.intent
  match derived : challenge context profile federation genesisHeight intent with
  | .error reason => return .error (preAuthentication reason)
  | .ok expected =>
      if same : expected = signed.challenge then
        if footprint : footprintExact context intent = .ok () then
          match ← checkGrants native context profile federation genesisHeight intent intent.grants signed.signatures with
          | .error reason => return .error reason
          | .ok grants => return .ok ⟨signed.challenge,
                derived.trans (congrArg Except.ok same), footprint, grants⟩
        else return .error (preAuthentication (.of .malformed))
      else return .error (challengeMismatch expected signed.challenge)

/-- A resource view: the cell's own root, the packed cell as the reader's
scope narrows it, and its narrowed account cut. -/
abbrev ResourceView := Digest × List UInt8 × List (Nat × Int)

/-- This codec is a read view, not a writable Book/registry payload. -/
def resourceViewStream : StreamCodec ResourceView :=
  StreamCodec.product digestStream (StreamCodec.product bytesStream balanceStream)

/-- Version 4 (K-FIELDS): the cell root leads, because the packed cell is the
cell narrowed to the reader's `Scope.fields` and its own root is not the
cell's.  Version 3 (the whole packed cell, no root) refuses. -/
def resourceViewFrame : List UInt8 := "DREGG/NATIVE-HOST/RESOURCE-VIEW/v4".toUTF8.toList

def resourceViewCodec : IndexedProgram.LawfulCodec ResourceView :=
  NativeHostCodec.framed resourceViewFrame resourceViewStream

/-- A stream window: the cell root, its next sequence position, and the
recorded entries in the window. -/
def tailViewStream : StreamCodec (Digest × Nat × List (Nat × StreamCell.StreamRecord)) :=
  StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat
    (StreamCodec.list (StreamCodec.product StreamCodec.nat StreamCell.recordStream)))

def tailViewFrame : List UInt8 := "DREGG/NATIVE-HOST/STREAM-TAIL/v1".toUTF8.toList

def tailViewCodec : IndexedProgram.LawfulCodec (Digest × Nat × List (Nat × StreamCell.StreamRecord)) :=
  NativeHostCodec.framed tailViewFrame tailViewStream

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

/-- `(height, root, lifecycle bytes)`: the cell's root at that height (none
when it was not live) and its lifecycle bytes, a live cell narrowed to the
reader's `Scope.fields` exactly as a current read is (K-FIELDS): a reader
restricted to some fields learns no other field of the cell's past either. -/
def atViewCodec : IndexedProgram.LawfulCodec (Nat × Option Digest × List UInt8) :=
  NativeHostCodec.framed atViewFrame
    (StreamCodec.product StreamCodec.nat (StreamCodec.product (StreamCodec.option digestStream) bytesStream))

/-- The at-height view of stored lifecycle bytes under `fields`. -/
def atView (fields : Option (Finset CellField)) (bytes : List UInt8) : Option Digest × List UInt8 :=
  match ResourceBirthCodec.LifecycleImage.rawDecode CanonicalCellRegistry.registry bytes with
  | some (.live packed) => (some packed.payload.root,
      ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry
        (.live (ResourceObservationAdmission.narrowPacked fields packed)))
  | _ => (none, bytes)

/-- The at-height view of a live cell is the cell narrowed exactly as a
current read narrows it (`resourceView` uses the same `narrowPacked`). -/
theorem atView_live (fields : Option (Finset CellField)) (packed : PackedCell CanonicalCellRegistry.registry) :
    atView fields (ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry (.live packed)) =
      (some packed.payload.root, ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry
        (.live (ResourceObservationAdmission.narrowPacked fields packed))) := by
  unfold atView
  rw [ResourceBirthCodec.LifecycleImage.rawDecode_bytes]

/-- Every query view, `who`/`since`/`at` included, has the same one-target
footprint as a current read of that target: the same grant, the same check. -/
theorem presence_views_share_footprint (context : Context deployment durable)
    (subject : SubjectId) (nonce : Nat) (query : Query) (grants : List GrantRef) :
    requiredTargets context ⟨subject, nonce, .query query, grants⟩ = .ok [(query.kind, query.target)] :=
  rfl

/-- What a reader under `fields` receives of a selected cell: its root, the
cell with every unnamed field absent, and the named balances. -/
def resourceView (fields : Option (Finset CellField))
    (packed : PackedCell CanonicalCellRegistry.registry) (balances : List (Nat × Int)) :
    ResourceView :=
  (packed.payload.root,
    PackedCell.bytes CanonicalCellRegistry.registry
      (ResourceObservationAdmission.narrowPacked fields packed),
    ResourceObservationAdmission.narrowBalances fields balances)

/-- The query's view bytes. A history read outside the log window (above the
current height, or below the retention floor) is `operationRejected`; a query
that does not fit its authorized target (a `tail` of a non-stream cell, a
purpose that is not a query) is `malformed`. -/
def AuthorizedIntent.queryResult
    {context : Context deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {federation : FederationId} {genesisHeight : Nat} {intent : Intent}
    (accepted : AuthorizedIntent context profile federation genesisHeight intent) :
    Except RefusalReason (List UInt8) := do
  let .query query := intent.purpose | throw .malformed
  if present : 0 < intent.grants.length then
    let grant := intent.grants.get ⟨0, present⟩
    let checked := accepted.grants ⟨0, present⟩
    let state := context.authority.snapshot.authState
    let reader := CredentialAuthorityState.readCapability context.authority.snapshot.cell
      grant.kind grant.capability
    match query.view with
    | .resource => do
        -- The authorizing capability (the one this grant names) narrows the view.
        let some stored := reader | throw .malformed
        pure (resourceViewCodec.encode (resourceView stored.head.scope.fields
          checked.selected.packed checked.selected.accountBalances))
    | .policy => do
        let address := state.policyAddress ⟨grant.target⟩ (state.policyRevision ⟨grant.target⟩)
        let some source := CanonicalCellRegistry.loadPolicySource deployment.domain
            context.directory.directory address | throw .malformed
        pure (PolicyRecordCodec.encode source.record)
    | .capability => do
        let some stored := reader | throw .malformed
        pure ((CredentialAuthorityEntryCodec.storedCapabilityStream grant.kind).encode stored)
    | .who => do
        let some stored := reader | throw .malformed
        let visible := sees state.parent stored.head query.target
        let height := genesisHeight + durable.height
        pure (whoViewCodec.encode ((members context grant.kind query.target height).map fun subject =>
          (subject.value, (whoSeen durable.index visible subject).map (genesisHeight + ·))))
    | .since after => do
        let some stored := reader | throw .malformed
        let visible := sees state.parent stored.head query.target
        pure (sinceViewCodec.encode (sinceFrom visible after (genesisHeight + 1) durable.image.accepted))
    | .atHeight height =>
        if height > genesisHeight + durable.height then
          throw .operationRejected
        else if height < genesisHeight then
          throw .operationRejected
        else
          let some stored := reader | throw .malformed
          match atBytes (durable := durable) genesisHeight height query.target with
          | some bytes => pure (atViewCodec.encode (height, atView stored.head.scope.fields bytes))
          | none => throw .malformed
    | .tail start count =>
        match checked.selected.packed with
        | ⟨.stream, payload⟩ => pure (tailViewCodec.encode (payload.root,
            StreamCell.nextSeq payload.logical, StreamCell.tail payload.logical start count))
        | _ => throw .malformed
  else throw .malformed

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

/-- A version-3 resource view (the whole packed cell, no leading root)
refuses: its frame is not the v4 frame. -/
theorem v3_view_refused (payload : List UInt8) :
    resourceViewCodec.decode ("DREGG/NATIVE-HOST/RESOURCE-VIEW/v3".toUTF8.toList ++ payload) =
      none := by
  have len : ("DREGG/NATIVE-HOST/RESOURCE-VIEW/v3".toUTF8.toList).length =
      resourceViewFrame.length := by decide +kernel
  have ne : "DREGG/NATIVE-HOST/RESOURCE-VIEW/v3".toUTF8.toList ≠ resourceViewFrame := by
    decide +kernel
  simp only [resourceViewCodec, NativeHostCodec.framed, ResourceBirthCodec.strictCodec,
    NativeHostCodec.framedRaw, ← len, List.take_left', ne, if_false]
  rfl

theorem resourceView_roundtrip (view : ResourceView) :
    resourceViewCodec.decode (resourceViewCodec.encode view) = some view :=
  resourceViewCodec.decode_encode view

theorem resourceView_canonical {bytes : List UInt8} {view : ResourceView}
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
/-- info: 'Minidregg.Kernel.NativeObservationController.v3_view_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.v3_view_refused
