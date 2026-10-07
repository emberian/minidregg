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
import Compiler.StoreHiding
import Kernel.CapabilityRenounce
import Kernel.StreamWrite
import Kernel.RunComputeView
import Compiler.DurableIndexFamilies

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
open Minidregg.Compiler.DurableIndex (LinkRow LinkRow.of linkRowStream)

set_option autoImplicit false

abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Registry := CanonicalCellRegistry.registry

abbrev Context := ResourceObservationAdmission.Context

variable {deployment : Deployment} {durable : Durable}

/-- What a requester may be told before its header signatures verify. (Before that, the
request itself is authenticated by the intent signature -- `authenticated`, FIX-DISCLOSE --
so this reaches only the subject's own key.) A refusal here names only facts the challenge
endpoint already publishes:
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
abbrev book (context : Context deployment) := ResourceObservationAdmission.book context
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

def balances (context : Context deployment) (grant : GrantRef) : Option (List (Nat × Int)) :=
  ResourceObservationAdmission.balances context grant.kind grant.target

abbrev Target := ResourceKind × Nat

def declaredKind (context : Context deployment) (target : Nat) : Option ResourceKind :=
  match context.directory.slots target with
  | .present packed => ResourceTargetAdmission.externalKind packed.kind
  | _ => none

/-- This analysis never runs a mutating preparation. Existing Book account
membership is public routing metadata. AccountSupported, enforced by the
loaded Book law, makes fresh registrations incapable of probing hidden funds.
An existing account cannot be hidden merely by listing it as a proposed birth.
All debit sources are included, even when the eventual operation would fail
its factory fee/funding checks. Recipient credits confer no read obligation. -/
def requiredTargets (context : Context deployment) (intent : Intent) :
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
  | .prepare (.renounce bytes) =>
      let command ← need .malformed (CapabilityRenounce.commandCodec.decode bytes)
      require .malformed (command.subject == intent.subject)
      -- A renounce reads nothing through a grant: its plan consults only the
      -- signer key record (public), and the holder gate runs after the
      -- signature verifies (`CapabilityRenounce.admitNative`).
      pure []
  | .prepare (.install subject _ bytes) =>
      require .malformed (subject == intent.subject)
      let declaration ← need .malformed (PolicyInstallController.decodeDeclaration bytes)
      let kind ← need .noGrant (declaredKind context declaration.source.policyId.value)
      pure [(kind, declaration.source.policyId.value)]
  | .prepare (.installWithRoster subject _ bytes _) =>
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

def footprintExact (context : Context deployment) (intent : Intent) : Except Refusal Unit :=
  match requiredTargets context intent with
  | .error reason => .error reason
  | .ok required =>
      if intent.grants.map (fun grant => (grant.kind, grant.target)) = required then .ok ()
      else .error (.of .malformed)

/-- Missing, additional, reordered or wrong-kind read selections are all
refused before any selected values can be returned. -/
theorem footprint_mismatch_refused (context : Context deployment) (intent : Intent)
    (required : List Target) (derived : requiredTargets context intent = .ok required)
    (different : intent.grants.map (fun grant => (grant.kind, grant.target)) ≠ required) :
    footprintExact context intent = .error (.of .malformed) := by
  simp [footprintExact, derived, different]

theorem footprint_success_exact (context : Context deployment) (intent : Intent)
    (required : List Target) (derived : requiredTargets context intent = .ok required)
    (accepted : footprintExact context intent = .ok ()) :
    intent.grants.map (fun grant => (grant.kind, grant.target)) = required := by
  by_contra different
  rw [footprint_mismatch_refused context intent required derived different] at accepted
  cases accepted

def bindingBytesAt (deployment : Deployment) (worldRoot semantics : Digest)
    (intent : Intent) (grant : GrantRef) : List UInt8 :=
  (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream grantStream)))).encode
      (deployment.domain, semantics,
        worldRoot, intentIdentity intent, grant)

def bindingBytes (context : Context deployment) (semantics : Digest)
    (intent : Intent) (grant : GrantRef) : List UInt8 :=
  bindingBytesAt deployment (context.worldRoot)
    semantics intent grant

def effectIdentityAt (deployment : Deployment) (worldRoot semantics : Digest)
    (intent : Intent) (grant : GrantRef) : Digest :=
  (Sp800185Cshake256.hash "DREGG.NATIVE-HOST.OBSERVE-EFFECT/v4".toUTF8.toList
    (bindingBytesAt deployment worldRoot semantics intent grant)).digest

def effectIdentity (context : Context deployment) (semantics : Digest)
    (intent : Intent) (grant : GrantRef) : Digest :=
  effectIdentityAt deployment (context.worldRoot)
    semantics intent grant

def markerAt (deployment : Deployment) (worldRoot semantics : Digest)
    (intent : Intent) (grant : GrantRef) : Nat :=
  (Sp800185Cshake256.hash "DREGG.NATIVE-HOST.OBSERVE-SIGNATURE/v4".toUTF8.toList
    (bindingBytesAt deployment worldRoot semantics intent grant)).digest.value

def marker (context : Context deployment) (semantics : Digest)
    (intent : Intent) (grant : GrantRef) : Nat :=
  markerAt deployment (context.worldRoot)
    semantics intent grant

theorem effectIdentity_exact (context : Context deployment) (semantics : Digest)
    (intent : Intent) (grant : GrantRef) :
    effectIdentity context semantics intent grant =
      effectIdentityAt deployment
        (context.worldRoot)
        semantics intent grant := by
  rfl

theorem marker_exact (context : Context deployment) (semantics : Digest)
    (intent : Intent) (grant : GrantRef) :
    marker context semantics intent grant =
      markerAt deployment
        (context.worldRoot)
        semantics intent grant := by
  rfl

theorem bindingBytesAt_exact (context : Context deployment) (semantics : Digest)
    (intent : Intent) (grant : GrantRef) :
    bindingBytesAt deployment (context.worldRoot)
      semantics intent grant = bindingBytes context semantics intent grant := by
  rfl

private def requestAt (context : Context deployment) (worldRoot semantics : Digest)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (preRoot : Digest) : Request grant.kind where
  domain := deployment.domain
  semantics := semantics
  federation := federation
  subject := intent.subject
  subjectKeyEpoch := context.authority.authState.subjectKeyEpoch intent.subject
  target := ⟨grant.target⟩
  verb := observeVerb grant.kind
  argsDigest := intentIdentity intent
  effectsDigest := effectIdentityAt deployment worldRoot semantics intent grant
  nonce := intent.nonce
  height := genesisHeight + context.height
  preStateRoot := preRoot
  policyId := ⟨grant.target⟩
  policyEpoch := context.authority.authState.policyEpoch ⟨grant.target⟩
  policyRevision := context.authority.authState.policyRevision ⟨grant.target⟩
  cost := (intentCodec.encode intent).length

def request (context : Context deployment) (semantics : Digest)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (preRoot : Digest) : Request grant.kind :=
  requestAt context (context.worldRoot)
    semantics federation genesisHeight intent grant preRoot

theorem requestAt_exact (context : Context deployment) (semantics : Digest)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (preRoot : Digest) :
    requestAt context (context.worldRoot)
      semantics federation genesisHeight intent grant preRoot =
      request context semantics federation genesisHeight intent grant preRoot := by
  rfl

abbrev readPatch := ResourceObservationAdmission.readPatch

def readFamily (context : Context deployment) (semantics : Digest)
    (federation : FederationId) (genesisHeight : Nat) (grant : GrantRef)
    (kind : CanonicalCellRegistry.Kind)
    (pre : Materialized (CanonicalCellRegistry.materializer kind)) (intent : Intent) :=
  ResourceObservationAdmission.readFamily
    (request context semantics federation genesisHeight intent grant pre.root) kind pre

def readCandidate (context : Context deployment) (semantics : Digest)
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
      (kind = .object ∧ (physical = .declaredObject ∨ physical = .content ∨ physical = .stream ∨
        physical = .worldKind ∨ physical = .worldInstance)) ∨
      (kind = .account ∧ physical = .accountMetadata) ∨
      (kind = .program ∧ (physical = .declaredProgram ∨ physical = .pay)) := by
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

/-- The fields the grant's capability names (`none`: every field). -/
def narrowedFields (context : Context deployment) (grant : GrantRef) :
    Option (Finset CellField) :=
  match CredentialAuthorityState.readCapability context.authority.cell grant.kind
      grant.capability with
  | some stored => stored.head.scope.fields
  | none => none

/-- K-NARROW-HIDE.  A reader whose capability names fields is served only a
cell whose root hides what it may not read: a blinded cell.  Every query's
signing header carries the cell root (`requestAt … preStateRoot`), so the
refusal is at selection, before any challenge leaves the host. -/
def HidingReady (context : Context deployment) (grant : GrantRef)
    (packed : PackedCell Registry) : Prop :=
  narrowedFields context grant = none ∨
    CanonicalCellRegistry.blinded packed.kind packed.payload.logical = true

instance hidingReadyDecidable (context : Context deployment) (grant : GrantRef)
    (packed : PackedCell Registry) : Decidable (HidingReady context grant packed) := by
  unfold HidingReady; infer_instance

structure Selected (context : Context deployment) (grant : GrantRef) where
  private mk ::
  packed : PackedCell Registry
  present : context.directory.slots grant.target = .present packed
  law : CanonicalCellRegistry.CellLaw deployment grant.target packed
  role : observableKind grant.kind packed.kind = true
  hides : HidingReady context grant packed
  accountBalances : List (Nat × Int)
  balancesExact : balances context grant = some accountBalances

def select (context : Context deployment) (grant : GrantRef) : Option (Selected context grant) :=
  match present : context.directory.slots grant.target with
  | .absent => none
  | .present packed =>
      if law : CanonicalCellRegistry.CellLaw deployment grant.target packed then
        if role : observableKind grant.kind packed.kind = true then
          if hides : HidingReady context grant packed then
            match exact : balances context grant with
            | none => none
            | some values => some ⟨packed, present, law, role, hides, values, exact⟩
          else none
        else none
      else none

/-- **A narrowed reader is served only a blinded cell.** -/
theorem selected_narrowed_is_blinded {context : Context deployment} {grant : GrantRef}
    (selected : Selected context grant) {fields : Finset CellField}
    (narrowed : narrowedFields context grant = some fields) :
    CanonicalCellRegistry.blinded selected.packed.kind selected.packed.payload.logical = true := by
  rcases selected.hides with whole | blinded
  · rw [narrowed] at whole; cases whole
  · exact blinded

variable {F : Type} [Field F] [DecidableEq F]

abbrev ReadPreparation (context : Context deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (selected : Selected context grant) :=
  ResourceObservationAdmission.Prepared context profile
    (request context profile.semantics federation genesisHeight intent grant selected.packed.payload.root)
    (marker context profile.semantics intent grant) grant.capability (intentCodec.encode intent)

/-- The retained lower admission is the same resource-local no-op policy gate
used before exposing participants to foreign policies in joint submission. -/
structure CheckedGrant (context : Context deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent) (grant : GrantRef) where
  private mk ::
  selected : Selected context grant
  preparation : ReadPreparation context profile federation genesisHeight intent grant selected
  selectedExact : preparation.observed.before = selected.packed
  balancesExact : preparation.accountBalances = selected.accountBalances
  envelope : List UInt8
  checked : ResourceObservationAdmission.Checked preparation envelope

private def headerAt (context : Context deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (worldRoot : Digest)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent) (grant : GrantRef) :
    Except Refusal CredentialSignedEnvelopeController.SignedHeader := do
  let selected ← need .noGrant (select context grant)
  (CredentialSignatureAdmission.signingHeader context.authority
    (markerAt deployment worldRoot profile.semantics intent grant)
    ⟨grant.kind, requestAt context worldRoot profile.semantics federation genesisHeight
      intent grant selected.packed.payload.root⟩).mapError
      (fun reason => .of (RefusalReason.ofSignature reason))

def header (context : Context deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent) (grant : GrantRef) :
    Except Refusal CredentialSignedEnvelopeController.SignedHeader :=
  headerAt context profile
    (context.worldRoot)
    federation genesisHeight intent grant

theorem headerAt_exact (context : Context deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId)
    (genesisHeight : Nat) (intent : Intent) (grant : GrantRef) :
    headerAt context profile
      (context.worldRoot)
      federation genesisHeight intent grant =
      header context profile federation genesisHeight intent grant := by
  rfl

/-! ## Authentication before any target is read (FIX-DISCLOSE)

The challenge used to be unauthenticated: for an intent naming a present target it issued
headers, for an absent one it refused `undisclosed`, so a key that was never enrolled
learned whether an id exists by naming any enrolled subject. Now every observation request
carries the subject's signature over the intent's bytes, and the Host checks it against the
subject's current key before it reads anything about the intent's targets. A request that
does not authenticate is refused on one path that reads only the subject's key standing:
`unknownKey` for a subject with no current live Ed25519 key (a public enrollment
coordinate), `badSignature` otherwise. -/

/-- The key an observation request must be signed by: the subject's current signing key,
registered and not revoked, Ed25519. A subject without one is `unknownKey`. -/
def intentKey (context : Context deployment) (subject : SubjectId) :
    Except Refusal (List UInt8) :=
  match CredentialAuthorityState.currentSigningKey context.authority.logical subject with
  | none => .error (.of .unknownKey)
  | some key =>
      if CredentialAuthorityState.keyStanding context.authority.cell
          (CredentialAuthorityState.signingKeyRevocation key) = .live ∧
          key.algorithm = CredentialSignatureAdmission.ed25519Algorithm ∧
          key.publicKey.length = 32 then
        .ok key.publicKey
      else .error (.of .unknownKey)

/-- The native verdict on an intent signature: the subject's key over the intent's own
framed bytes. It is given no target, no directory and no Book. A subject without a key
is not verified at all. -/
def intentVerdict {m : Type → Type} [Monad m] (native : CredentialSignatureIO.Oracle m)
    (key : Except Refusal (List UInt8)) (intent : Intent) (signature : List UInt8) :
    m (Except CredentialSignatureIO.Error Bool) :=
  match key with
  | .error _ => pure (.ok false)
  | .ok publicKey => native.check publicKey (intentCodec.encode intent) signature

/-- The authentication decision: only the exact positive verdict under a selected key
authenticates; every other verdict is `badSignature`. -/
def authenticated (key : Except Refusal (List UInt8))
    (verdict : Except CredentialSignatureIO.Error Bool) : Except Refusal Unit :=
  match key with
  | .error refusal => .error refusal
  | .ok _ =>
      match verdict with
      | .ok true => .ok ()
      | _ => .error (.of .badSignature)

/-- An unauthenticated request's refusal is a function of the subject's key alone: any
two verdicts that are not the exact positive one give the same refusal. -/
theorem authenticated_unverified (key : Except Refusal (List UInt8))
    (left right : Except CredentialSignatureIO.Error Bool)
    (leftFails : left ≠ .ok true) (rightFails : right ≠ .ok true) :
    authenticated key left = authenticated key right := by
  cases key with
  | error refusal => rfl
  | ok publicKey =>
      rcases left with _ | (_ | _) <;> rcases right with _ | (_ | _) <;>
        simp_all [authenticated]

/-- Only the exact positive verdict authenticates. -/
theorem authenticated_ok_iff (key : Except Refusal (List UInt8))
    (verdict : Except CredentialSignatureIO.Error Bool) :
    authenticated key verdict = .ok () ↔ (∃ publicKey, key = .ok publicKey) ∧ verdict = .ok true := by
  cases key with
  | error refusal => simp [authenticated]
  | ok publicKey => rcases verdict with _ | (_ | _) <;> simp [authenticated]

/-- A subject's key is selected, or refused `unknownKey`. -/
theorem intentKey_refusal (context : Context deployment) (subject : SubjectId)
    (refusal : Refusal) (refused : intentKey context subject = .error refusal) :
    refusal = .of .unknownKey := by
  unfold intentKey at refused
  split at refused
  · cases refused; rfl
  · split at refused
    · cases refused
    · cases refused; rfl

/-- An unauthenticated refusal names only `unknownKey` or `badSignature`. -/
theorem authenticated_refusal (context : Context deployment) (subject : SubjectId)
    (verdict : Except CredentialSignatureIO.Error Bool) (refusal : Refusal)
    (refused : authenticated (intentKey context subject) verdict = .error refusal) :
    refusal = .of .unknownKey ∨ refusal = .of .badSignature := by
  cases selected : intentKey context subject with
  | error reason =>
      rw [selected] at refused
      cases refused
      exact Or.inl (intentKey_refusal context subject _ selected)
  | ok publicKey =>
      rw [selected] at refused
      rcases verdict with _ | (_ | _) <;> simp [authenticated] at refused <;>
        (subst refused; exact Or.inr rfl)

/-- The challenge at a given clock: the one the read's law is judged at is the
loaded snapshot's (`challenge`). -/
def challengeAt (context : Context deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (clock : ClockCell.Clock) (intentSignature : List UInt8) : Except Refusal Challenge := do
  let worldRoot := context.worldRoot
  footprintExact context intent
  let headers ← intent.grants.mapM fun grant => do
    let value ← headerAt context profile worldRoot federation genesisHeight intent grant
    pure (CredentialSignedEnvelopeController.headerCodec.encode value)
  pure ⟨intent, deployment.domain, profile.semantics, federation,
    worldRoot, context.authority.cell.root,
    genesisHeight + context.height, clock.now, clock.slot, headers, intentSignature⟩

/-- The success payload contains no field values, balances or policy source.
The selected public KeyRecord is reversibly encoded in the existing registry
binding in each header; this binding is not claimed to hide enrollment data.
The clock it names is public (the clock view publishes it). -/
def challenge (context : Context deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent) (intentSignature : List UInt8) : Except Refusal Challenge := do
  let clock ← need .operationRejected (ClockCellDomain.load deployment context.cells)
  challengeAt context profile federation genesisHeight intent clock.clock intentSignature

def checkGrant {m : Type → Type} [Monad m] (native : CredentialSignatureIO.Oracle m)
    (context : Context deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (signature : List UInt8) :
    m (Except Refusal (CheckedGrant context profile federation genesisHeight intent grant)) := do
  let some selected := select context grant | return .error (preAuthentication (.of .noGrant))
  let worldRoot := context.worldRoot
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

structure AuthorizedIntent (context : Context deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent) where
  private mk ::
  suppliedChallenge : Challenge
  challengeExact : challenge context profile federation genesisHeight intent
    suppliedChallenge.intentSignature = .ok suppliedChallenge
  footprint : footprintExact context intent = .ok ()
  grants : (index : Fin intent.grants.length) →
    CheckedGrant context profile federation genesisHeight intent (intent.grants.get index)

/-- A successful query has exactly one observation incidence, for precisely
the requested resource and authority kind. Additional granted resources cannot
be smuggled into the response selection. -/
theorem AuthorizedIntent.query_footprint
    {context : Context deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {federation : FederationId} {height : Nat} {intent : Intent}
    (accepted : AuthorizedIntent context profile federation height intent)
    (query : Query) (purpose : intent.purpose = .query query) :
    intent.grants.map (fun grant => (grant.kind, grant.target)) = [(query.kind, query.target)] :=
  footprint_success_exact context intent [(query.kind, query.target)]
    (by simp only [requiredTargets, purpose]; rfl) accepted.footprint

private def checkGrants {m : Type → Type} [Monad m] (native : CredentialSignatureIO.Oracle m)
    (context : Context deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grants : List GrantRef) (signatures : List (List UInt8)) :
    m (Except Refusal ((index : Fin grants.length) →
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

/-- The authorization of an AUTHENTICATED signed observation: stale challenges are
refused against the current world root; no grant means no successful footprint; no
callback can mint a read token. Before the header signatures verify only
`preAuthentication` reasons are named. Reached only through `authorize`, after the
intent signature verified (`authenticated`). -/
def authorizeAuthenticated {m : Type → Type} [Monad m] (native : CredentialSignatureIO.Oracle m)
    (context : Context deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (signed : Signed) :
    m (Except Refusal (AuthorizedIntent context profile federation genesisHeight signed.challenge.intent)) := do
  let intent := signed.challenge.intent
  match derived : challenge context profile federation genesisHeight intent
      signed.challenge.intentSignature with
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

/-- **Every signed observation authenticates before it reads a target.** The intent
signature the challenge carries is checked against the subject's current key
(`intentVerdict`, reading only the subject's key, the intent's bytes and the signature);
only an authenticated request reaches the target-reading authorization. -/
def authorize {m : Type → Type} [Monad m] (native : CredentialSignatureIO.Oracle m)
    (context : Context deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (signed : Signed) :
    m (Except Refusal (AuthorizedIntent context profile federation genesisHeight signed.challenge.intent)) := do
  let key := intentKey context signed.challenge.intent.subject
  let verdict ← intentVerdict native key signed.challenge.intent signed.challenge.intentSignature
  match authenticated key verdict with
  | .error refusal => return .error refusal
  | .ok () => authorizeAuthenticated native context profile federation genesisHeight signed

/-- The signed path is the authentication, then the target-reading authorization. -/
theorem authorize_authenticates_first {m : Type → Type} [Monad m] (native : CredentialSignatureIO.Oracle m)
    (context : Context deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (signed : Signed) :
    authorize (m := m) native context profile federation genesisHeight signed = (do
      let verdict ← intentVerdict (m := m) native (intentKey context signed.challenge.intent.subject)
        signed.challenge.intent signed.challenge.intentSignature
      match authenticated (intentKey context signed.challenge.intent.subject) verdict with
      | .error refusal => return Except.error refusal
      | .ok () => authorizeAuthenticated native context profile federation genesisHeight signed) :=
  rfl

/-- **`unenrolled_signed_refusal_independent_of_target`.** A signed observation whose
intent signature does not verify under the subject's current key (a key that was never
enrolled, or any wrong key) is refused by `authenticated` alone, with the same refusal
whatever its intent names: two such requests by one subject are refused identically. -/
theorem unenrolled_signed_refusal_independent_of_target (context : Context deployment)
    (left right : Signed)
    (subject : left.challenge.intent.subject = right.challenge.intent.subject)
    (leftVerdict rightVerdict : Except CredentialSignatureIO.Error Bool)
    (leftFails : leftVerdict ≠ .ok true) (rightFails : rightVerdict ≠ .ok true) :
    authenticated (intentKey context left.challenge.intent.subject) leftVerdict =
      authenticated (intentKey context right.challenge.intent.subject) rightVerdict := by
  rw [subject]
  exact authenticated_unverified _ _ _ leftFails rightFails
/-- The opening of a cell root: the store frame and one item per entry
(`StoreHiding.items`), opened where the reader may see it.  A kind without a
store wire has none. -/
abbrev OpeningView := List UInt8 × List StoreHiding.Item

def openingStream : StreamCodec OpeningView :=
  StreamCodec.product bytesStream (StreamCodec.list StoreHiding.itemStream)

/-- A resource view: the cell's own root, the packed cell as the reader's
scope narrows it, its narrowed account cut, and the opening of the root. -/
abbrev ResourceView := Digest × List UInt8 × List (Nat × Int) × OpeningView ×
  Option RunComputeView.ComputeQuote

/-- This codec is a read view, not a writable Book/registry payload. -/
def resourceViewStream : StreamCodec ResourceView :=
  StreamCodec.product digestStream
    (StreamCodec.product bytesStream (StreamCodec.product balanceStream
      (StreamCodec.product openingStream (StreamCodec.option RunComputeView.computeQuoteStream))))

/-- Field coverage is projected from the very grant that admitted this resource
view. No second snapshot or authority lookup is accepted from the client. -/
abbrev ResourceScopeView := ResourceKind × Nat × Option (Finset CellField) × ResourceView

def resourceScopeViewStream : StreamCodec ResourceScopeView :=
  StreamCodec.product ResourceBirthCodec.resourceKindStream
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product (StreamCodec.option CredentialAuthorityEntryCodec.fieldSetStream)
        resourceViewStream))

def resourceScopeViewCodec : IndexedProgram.LawfulCodec ResourceScopeView :=
  NativeHostCodec.framed "DREGG/NATIVE-HOST/RESOURCE-SCOPE-VIEW/v1".toUTF8.toList
    resourceScopeViewStream

theorem resourceScopeView_roundtrip (view : ResourceScopeView) :
    resourceScopeViewCodec.decode (resourceScopeViewCodec.encode view) = some view :=
  resourceScopeViewCodec.decode_encode view

/-- Version 6 retains salted openings and appends the authenticated reader's
optional compute quote. Version 5 has no quote and refuses at this frame gate. -/
def resourceViewFrame : List UInt8 := WorldExecutionContract.resourceViewFrame

def resourceViewCodec : IndexedProgram.LawfulCodec ResourceView :=
  NativeHostCodec.framed resourceViewFrame resourceViewStream

/-- The bytes a stream record's append carried, read from the accepted signed
ingress of the record's own transaction, and shown only when they reproduce the
digest the cell committed. The cell keeps the digest and the signed command
keeps the bytes (K-STREAM); this is how a reader who may observe the stream
gets the text. The lookup is a scan of the accepted log, like `since`. -/
def streamPayload (accepted : List DurableReceiver.IntentRecord) (target : Nat)
    (record : StreamCell.StreamRecord) : Option (List UInt8) := do
  let intent ← accepted.find? (fun intent => decide (intent.transactionId = record.transaction))
  let (_, _, signed) ← DeclaredResourceController.decodeSignedBytes intent.event.canonicalBytes
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  let written ← command.targets.find? (fun written => decide (written.target = target))
  match written.payload with
  | .append request =>
      if StreamCell.payloadDigest request.payload = record.entry.payloadDigest then
        some request.payload
      else none
  | _ => none

/-- **A shown payload is the signed append of that record's transaction.** The
bytes reproduce the committed digest, and they are the append payload of the
target `target` in the command of an accepted record whose transaction id is the
one the stream record binds. -/
theorem streamPayload_sound {accepted : List DurableReceiver.IntentRecord} {target : Nat}
    {record : StreamCell.StreamRecord} {bytes : List UInt8}
    (shown : streamPayload accepted target record = some bytes) :
    StreamCell.payloadDigest bytes = record.entry.payloadDigest ∧
      ∃ intent ∈ accepted, intent.transactionId = record.transaction ∧
        ∃ ingress command written request,
          DeclaredResourceController.decodeSignedBytes intent.event.canonicalBytes = some ingress ∧
          DeclaredResourceController.commandCodec.decode ingress.2.2.commandBytes = some command ∧
          written ∈ command.targets ∧ written.target = target ∧
          written.payload = .append request ∧ request.payload = bytes := by
  unfold streamPayload at shown
  cases found : accepted.find? (fun intent => decide (intent.transactionId = record.transaction)) with
  | none => simp [found] at shown
  | some intent =>
    cases decoded : DeclaredResourceController.decodeSignedBytes intent.event.canonicalBytes with
    | none => simp [found, decoded] at shown
    | some ingress =>
      obtain ⟨domain, semantics, signed⟩ := ingress
      cases commanded : DeclaredResourceController.commandCodec.decode signed.commandBytes with
      | none => simp [found, decoded, commanded] at shown
      | some command =>
        cases writtenFound : command.targets.find? (fun written => decide (written.target = target)) with
        | none => simp [found, decoded, commanded, writtenFound] at shown
        | some written =>
          simp only [found, decoded, commanded, writtenFound, Option.bind_some, bind] at shown
          cases append : written.payload with
          | scalar _ => simp [append] at shown
          | content _ => simp [append] at shown
          | world _ => simp [append] at shown
          | kindDefinition _ => simp [append] at shown
          | kindRead => simp [append] at shown
          | read => simp [append] at shown
          | computeFunding _ => simp [append] at shown
          | moneyConsent _ => simp [append] at shown
          | append request =>
            simp only [append] at shown
            by_cases digestEq : StreamCell.payloadDigest request.payload = record.entry.payloadDigest
            · simp only [digestEq, if_true, Option.some.injEq] at shown
              subst shown
              have sameTx := List.find?_some found
              have sameTarget := List.find?_some writtenFound
              simp only [decide_eq_true_eq] at sameTx sameTarget
              exact ⟨digestEq, intent, List.mem_of_find?_eq_some found,
                sameTx,
                (domain, semantics, signed), command, written, request,
                decoded, commanded, List.mem_of_find?_eq_some writtenFound,
                sameTarget, append, rfl⟩
            · simp [digestEq] at shown

/-- A stream window: the head cell's root, its next sequence position, and the
recorded entries in the window, each read back from its own entry cell
(`StreamWrite.window`) with the payload `streamPayload` found for it. -/
def tailViewStream :
    StreamCodec (Digest × Nat × List (Nat × StreamCell.StreamRecord × Option (List UInt8))) :=
  StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat
    (StreamCodec.list (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCell.recordStream (StreamCodec.option bytesStream)))))

/-- v2 carries each entry's payload; a v1 window (records only) refuses
(`v1_tail_view_refused`). -/
def tailViewFrame : List UInt8 := "DREGG/NATIVE-HOST/STREAM-TAIL/v2".toUTF8.toList

def tailViewCodec :
    IndexedProgram.LawfulCodec (Digest × Nat × List (Nat × StreamCell.StreamRecord × Option (List UInt8))) :=
  NativeHostCodec.framed tailViewFrame tailViewStream

theorem v1_tail_view_refused (payload : List UInt8) :
    tailViewCodec.decode ("DREGG/NATIVE-HOST/STREAM-TAIL/v1".toUTF8.toList ++ payload) = none := by
  have len : ("DREGG/NATIVE-HOST/STREAM-TAIL/v1".toUTF8.toList).length =
      tailViewFrame.length := by decide +kernel
  have ne : "DREGG/NATIVE-HOST/STREAM-TAIL/v1".toUTF8.toList ≠ tailViewFrame := by
    decide +kernel
  simp only [tailViewCodec, NativeHostCodec.framed, ResourceBirthCodec.strictCodec,
    NativeHostCodec.framedRaw, ← len, List.take_left', ne, if_false]
  rfl

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

/-- Whether `subject` holds a standing observe capability over `target` that
reads the WHOLE cell (no field narrowing): the filter thin consent's served
views pass (a narrowed view's root is not the cell's), and the one under which a
refused signed invocation may name a moved target to its signer. -/
def observesWhole (context : Context deployment) (kind : ResourceKind)
    (subject : SubjectId) (target height : Nat) : Bool :=
  let state := context.authority.authState
  let cell := context.authority.cell
  let reads : CapabilityId → Bool := fun named =>
    match CredentialAuthorityState.readCapability cell kind named with
    | some stored => decide (stored.head.holder = .subject subject) &&
        standing state height target stored.head && decide (stored.head.scope.fields = none)
    | none => false
  decide ((capabilityIds cell.logical kind).filter fun named => reads named = true).Nonempty

/-- The members of `room`: the subjects holding a standing capability over it,
in subject order. Membership is what the room's grants say, not who acted. -/
def members (context : Context deployment) (kind : ResourceKind) (room height : Nat) :
    List SubjectId :=
  let state := context.authority.authState
  let cell := context.authority.cell
  let held : Finset Nat := (capabilityIds cell.logical kind).biUnion fun named =>
    match CredentialAuthorityState.readCapability cell kind named with
    | some stored =>
        match stored.head.holder with
        | .subject subject => if standing state height room stored.head then {subject.value} else ∅
        | .bearer => ∅
    | none => ∅
  (held.sort (· ≤ ·)).map SubjectId.mk

/-- A capability reaches into `room` when its targets are `under X` or name a
cell `X` with `X` in the room's subtree (the room itself, a cell born in it,
a cell born in one of those). -/
def reachesInto {kind : ResourceKind} (parentage : Parentage) (room : Nat)
    (cap : Capability kind) : Bool :=
  match cap.scope.targets with
  | .under cell => decide (parentage.Descends cell room)
  | .explicit cells => decide (∃ cell ∈ cells, parentage.Descends cell.value room)

/-- A capability that can still admit something in `room`: it reaches into the
room, has not expired at `height` (a grant whose window has not opened yet
counts), is current, and nothing in its lineage is revoked. -/
def liveIn {kind : ResourceKind} (state : AuthState) (height room : Nat)
    (cap : Capability kind) : Bool :=
  reachesInto state.parent room cap &&
    decide (height ≤ cap.notAfter) &&
    decide (cap.policyEpoch = state.policyEpoch cap.policyId) &&
    decide (cap.issuerEpoch = state.issuerEpoch cap.issuer) &&
    decide (RevocationKey.capability cap.id ∉ state.revoked) &&
    decide (∀ ancestor ∈ cap.ancestors, RevocationKey.capability ancestor ∉ state.revoked) &&
    decide (∀ channel ∈ cap.channels, RevocationKey.channel channel ∉ state.revoked)

/-- Every live capability in `room` that `subject` holds, as (capability id,
policy id), in id order: what a kick must revoke for the room to stop
admitting the subject anywhere in it — the founder's invite, a concierge's
window, a grant on one cell under the room (a private room's keys cell), any
other, whoever issued it. The policy id names the resource whose control
grant revokes it. -/
def grantsOf (context : Context deployment) (kind : ResourceKind) (room height : Nat)
    (subject : SubjectId) : List (Nat × Nat) :=
  let state := context.authority.authState
  let cell := context.authority.cell
  let held : Finset Nat := (capabilityIds cell.logical kind).biUnion fun named =>
    match CredentialAuthorityState.readCapability cell kind named with
    | some stored =>
        if stored.head.holder = .subject subject ∧ liveIn state height room stored.head = true then
          {named.value} else ∅
    | none => ∅
  (held.sort (· ≤ ·)).filterMap fun named =>
    (CredentialAuthorityState.readCapability cell kind ⟨named⟩).map fun stored =>
      (named, stored.head.policyId.value)

/-- The subjects holding a live capability anywhere in `room`, in subject
order: `members` and everyone else a kick could still have to reach. -/
def holders (context : Context deployment) (kind : ResourceKind) (room height : Nat) :
    List SubjectId :=
  let state := context.authority.authState
  let cell := context.authority.cell
  let held : Finset Nat := (capabilityIds cell.logical kind).biUnion fun named =>
    match CredentialAuthorityState.readCapability cell kind named with
    | some stored =>
        match stored.head.holder with
        | .subject subject => if liveIn state height room stored.head then {subject.value} else ∅
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

/-- One holder: subject, last seen, whether it is a member (a standing
capability over the room itself, `members`), and every live capability it
holds in the room with its policy id (`grantsOf`). -/
def whoViewStream : StreamCodec (List (Nat × Option Nat × Bool × List (Nat × Nat))) :=
  StreamCodec.list (StreamCodec.product StreamCodec.nat
    (StreamCodec.product (StreamCodec.option StreamCodec.nat)
      (StreamCodec.product StreamCodec.bool
        (StreamCodec.list (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))

def whoViewFrame : List UInt8 := "DREGG/NATIVE-HOST/WHO-VIEW/v2".toUTF8.toList

def whoViewCodec : IndexedProgram.LawfulCodec (List (Nat × Option Nat × Bool × List (Nat × Nat))) :=
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

def atViewFrame : List UInt8 := "DREGG/NATIVE-HOST/AT-VIEW/v3".toUTF8.toList

/-- The opening of a packed cell's root under `fields`. -/
def openingView (fields : Option (Finset CellField))
    (packed : PackedCell CanonicalCellRegistry.registry) : OpeningView :=
  match CanonicalCellRegistry.wire? packed.kind with
  | some wire => (StoreCodec.frame wire,
      StoreHiding.items wire (ResourceObservationAdmission.Visible fields packed.kind)
        packed.payload.logical)
  | none => ([], [])

/-- **The root a reader receives opens.**  For every kind with a store wire,
the view's root is recomputed from the opening's frame and items alone. -/
theorem root_opens (fields : Option (Finset CellField))
    (packed : PackedCell CanonicalCellRegistry.registry)
    {wire : StoreCodec.Wire (CanonicalCellRegistry.layout packed.kind)}
    (selected : CanonicalCellRegistry.wire? packed.kind = some wire) :
    packed.payload.root = StoreHiding.rootOfItems wire (openingView fields packed).2 ∧
      (openingView fields packed).1 = StoreCodec.frame wire := by
  have root : packed.payload.root =
      (CanonicalCellRegistry.materializer packed.kind).rootOf packed.payload.logical := rfl
  rw [CanonicalCellRegistry.materializer_of_wire selected, StoreCodec.materializer_rootOf] at root
  unfold openingView
  rw [selected]
  refine ⟨?_, rfl⟩
  rw [root]
  exact StoreHiding.view_root_recomputes wire _ packed.payload.logical

/-- `(height, root, lifecycle bytes, opening)`: the cell's root at that height
(none when it was not live), its lifecycle bytes, a live cell narrowed to the
reader's `Scope.fields` exactly as a current read is (K-FIELDS), and the
opening of that root (K-NARROW-HIDE).  Version 1 (no opening) refuses. -/
def atViewCodec : IndexedProgram.LawfulCodec (Nat × Option Digest × List UInt8 × OpeningView) :=
  NativeHostCodec.framed atViewFrame
    (StreamCodec.product StreamCodec.nat (StreamCodec.product (StreamCodec.option digestStream)
      (StreamCodec.product bytesStream openingStream)))

/-- A v1 at-height view (either line's shape) refuses to decode. -/
theorem v2_at_view_refused (payload : List UInt8) :
    atViewCodec.decode ("DREGG/NATIVE-HOST/AT-VIEW/v2".toUTF8.toList ++ payload) = none := by
  have len : ("DREGG/NATIVE-HOST/AT-VIEW/v2".toUTF8.toList).length = atViewFrame.length := by
    decide +kernel
  have ne : "DREGG/NATIVE-HOST/AT-VIEW/v2".toUTF8.toList ≠ atViewFrame := by
    decide +kernel
  simp only [atViewCodec, NativeHostCodec.framed, ResourceBirthCodec.strictCodec,
    NativeHostCodec.framedRaw, ← len, List.take_left', ne, if_false]
  rfl

/-- info: 'Minidregg.Kernel.NativeObservationController.v2_at_view_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v2_at_view_refused

/-- The at-height view of stored lifecycle bytes under `fields`. -/
def atView (fields : Option (Finset CellField)) (bytes : List UInt8) :
    Option Digest × List UInt8 × OpeningView :=
  match ResourceBirthCodec.LifecycleImage.rawDecode CanonicalCellRegistry.registry bytes with
  | some (.live packed) => (some packed.payload.root,
      ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry
        (.live (ResourceObservationAdmission.narrowPacked fields packed)),
      openingView fields packed)
  | _ => (none, bytes, ([], []))

/-- The at-height view of a live cell is the cell narrowed exactly as a
current read narrows it (`resourceView` uses the same `narrowPacked`). -/
theorem atView_live (fields : Option (Finset CellField)) (packed : PackedCell CanonicalCellRegistry.registry) :
    atView fields (ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry (.live packed)) =
      (some packed.payload.root, ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry
        (.live (ResourceObservationAdmission.narrowPacked fields packed)), openingView fields packed) := by
  unfold atView
  rw [ResourceBirthCodec.LifecycleImage.rawDecode_bytes]

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

/-- The grant as the authority cell of `snapshot` holds it — present, naming
`subject`, and `standing` over `target` at `height` (window, epochs,
revocations and parentage all read from that same snapshot) — as its field
scope (what an `at` answer to it is narrowed to); `none` when it did not stand. -/
def grantStanding (snapshot : CredentialAuthorityDomainReceiver.PhysicalSnapshot)
    (subject : SubjectId) (grant : GrantRef) (height target : Nat) : Option (Option (Finset CellField)) :=
  match CredentialAuthorityDomainReceiver.loadDeployment deployment snapshot with
  | none => none
  | some authority =>
      match CredentialAuthorityState.readCapability authority.snapshot.cell grant.kind grant.capability with
      | none => none
      | some stored => if holderNames subject stored.head.holder &&
          standing authority.snapshot.authState height target stored.head then
            some stored.head.scope.fields else none

/-- `at height`, answered against the grants as they stood at `height`, and
narrowed to that grant's `Scope.fields` exactly as a current read is
(K-FIELDS, `atView`). A height above the current one or below the retention
floor is `operationRejected`; a grant that did not stand over the target at
that height is `noGrant`: the reader's current grant was verified, and a
capability failure at the asked height discloses no more than a missing grant
does (`RefusalReason`'s disclosure order). -/
def atCovered (genesisHeight height : Nat) (subject : SubjectId) (grant : GrantRef) (target : Nat) :
    Except RefusalReason (List UInt8) :=
  if height > genesisHeight + durable.height then
    .error .operationRejected
  else if height < genesisHeight then
    .error .operationRejected
  else
    match durable.atPrefix (height - genesisHeight) with
    | none => .error .malformed
    | some snapshot =>
        match grantStanding (deployment := deployment) snapshot subject grant height target with
        | some fields => .ok (atViewCodec.encode (height, atView fields (snapshot.canonicalBytes ⟨target⟩)))
        | none => .error .noGrant

/-- **`at` answers only a grant that stood at that height**: the bytes are
K-INDEX's `atBytes` (the fold of the prefix), narrowed to that grant's fields,
and the authority cell of that same prefix holds the grant's capability, naming
the reader and standing over the target at that height. -/
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
      out = atViewCodec.encode (height,
        atView stored.head.scope.fields (snapshot.canonicalBytes ⟨target⟩)) := by
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
  · rename_i fields stands
    unfold grantStanding at stands
    split at stands
    · cases stands
    rename_i authority loaded
    split at stands
    · cases stands
    rename_i stored read
    split at stands
    · rename_i covered
      simp only [Bool.and_eq_true] at covered
      cases stands
      cases answered
      refine ⟨snapshot, authority, stored, found, loaded, read, holderNames_covers covered.1,
        covered.2, ?_, rfl⟩
      unfold atBytes
      rw [if_pos ⟨by omega, by omega⟩, found]
      rfl
    · cases stands
  · cases answered

/-- Refuting pole: a grant whose capability the authority cell at that height
does not hold (a reader added later) is refused `noGrant`. -/
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
      .error .noGrant := by
  unfold atCovered
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [found]
  simp [grantStanding, loaded, absent]

/-- Satisfiable pole: a grant standing at that height is answered, with the
prefix's bytes narrowed to the grant's fields. -/
theorem atCovered_answers_standing {genesisHeight height : Nat} {subject : SubjectId}
    {grant : GrantRef} {target : Nat} {fields : Option (Finset CellField)}
    {snapshot : CredentialAuthorityDomainReceiver.PhysicalSnapshot}
    (floor : genesisHeight ≤ height) (within : height ≤ genesisHeight + durable.height)
    (found : durable.atPrefix (height - genesisHeight) = some snapshot)
    (stands : grantStanding (deployment := deployment) snapshot subject grant height target = some fields) :
    atCovered (deployment := deployment) (durable := durable) genesisHeight height subject grant target =
      .ok (atViewCodec.encode (height, atView fields (snapshot.canonicalBytes ⟨target⟩))) := by
  unfold atCovered
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [found, stands]

/-- Every query view, `who`/`since`/`at` included, has the same one-target
footprint as a current read of that target: the same grant, the same check. -/
theorem presence_views_share_footprint (context : Context deployment)
    (subject : SubjectId) (nonce : Nat) (query : Query) (grants : List GrantRef) :
    requiredTargets context ⟨subject, nonce, .query query, grants⟩ = .ok [(query.kind, query.target)] :=
  rfl

/-- What a reader under `fields` receives of a selected cell: its root, the
cell with every unnamed field absent, and the named balances. -/
def resourceView (fields : Option (Finset CellField))
    (packed : PackedCell CanonicalCellRegistry.registry) (balances : List (Nat × Int))
    (computeQuote : Option RunComputeView.ComputeQuote := none) : ResourceView :=
  (packed.payload.root,
    PackedCell.bytes CanonicalCellRegistry.registry
      (ResourceObservationAdmission.narrowPacked fields packed),
    ResourceObservationAdmission.narrowBalances fields balances,
    openingView fields packed, computeQuote)


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
def holdsStanding (context : Context deployment) (reader : SubjectId) (height cell : Nat)
    (named : CapabilityId) : Bool :=
  match CredentialAuthorityState.readCapability context.authority.cell .object named with
  | some stored => decide (stored.head.holder = .subject reader) &&
      standing context.authority.authState height cell stored.head
  | none => false

/-- A cell the reader may observe at `height`: some standing capability it holds covers it. -/
def readable (context : Context deployment) (reader : SubjectId) (height : Nat)
    (cell : DurableDataIntent.CellId) : Bool :=
  decide (∃ named ∈ capabilityIds context.authority.cell.logical .object,
    holdsStanding context reader height cell.value named = true)

theorem readable_sound {context : Context deployment} {reader : SubjectId} {height : Nat}
    {cell : DurableDataIntent.CellId} (shown : readable context reader height cell = true) :
    ∃ named stored, CredentialAuthorityState.readCapability context.authority.cell .object named =
        some stored ∧ stored.head.holder = .subject reader ∧
      standing context.authority.authState height cell.value stored.head = true := by
  obtain ⟨named, _, holds⟩ := of_decide_eq_true shown
  unfold holdsStanding at holds
  split at holds
  · rename_i stored found
    simp only [Bool.and_eq_true, decide_eq_true_eq] at holds
    exact ⟨named, stored, found, holds.1, holds.2⟩
  · cases holds

/-- One link row as the view renders it (`DurableIndex.LinkRow`, the family-5
value): the index keeps the RELATIVE live-since height, the row shows the
absolute one. -/
def linkRow (genesisHeight : Nat) (pair : DurableDataIntent.CellId × LinkIndex.Entry) : LinkRow :=
  LinkRow.of pair.1 pair.2.link pair.2.record (genesisHeight + pair.2.height)

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

/-- **A transclusion of the asked document is one of its backlinks**: the
backlinks view asks the transclusion keys that read the target document
(`LinkIndex.Index.transclusionKeys`) before the target's own keys, so every live
transclusion of it in a cell the reader sees is a row
(`LinkIndex.transclusion_backlink_complete` on the loaded index). -/
theorem transclusion_backlinks_view_complete {visible : DurableDataIntent.CellId → Bool}
    {keys : List LinkIndex.TargetKey} {document : Minidregg.Theory.Hyperdocument.DocumentId}
    {cell : DurableDataIntent.CellId} {key : LinkIndex.LinkKey}
    (live : key ∈ LinkIndex.latestLinks cell durable.image.accepted) (shown : visible cell = true)
    (reads : LinkIndex.transcludedDocument key.2.target = some document) :
    ∃ entry, entry.key = key ∧
      (cell, entry) ∈ durable.links.backlinks visible (durable.links.transclusionKeys document ++ keys) := by
  rw [durable.linksExact]
  exact LinkIndex.transclusion_backlink_complete _ _ _ live shown reads

/-- **A reader sees only backlinks from cells it may observe**: each row of
the view a reader gets names a source cell that some standing capability the
reader holds covers. -/
theorem backlinks_covered (context : Context deployment) (reader : SubjectId)
    (height : Nat) (keys : List LinkIndex.TargetKey) {pair : DurableDataIntent.CellId × LinkIndex.Entry}
    (member : pair ∈ durable.links.backlinks (readable context reader height) keys) :
    ∃ named stored, CredentialAuthorityState.readCapability context.authority.cell .object named =
        some stored ∧ stored.head.holder = .subject reader ∧
      standing context.authority.authState height pair.1.value stored.head = true :=
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

/-- The query's view bytes. A history read outside the log window (above the
current height, or below the retention floor) is `operationRejected`; one whose
grant did not stand at that height is `noGrant` (`atCovered`); a query that
does not fit its authorized target (a `tail` of a non-stream cell, a purpose
that is not a query) is `malformed`. -/
def AuthorizedIntent.queryResult
    {context : Context deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {federation : FederationId} {genesisHeight : Nat} {intent : Intent}
    (accepted : AuthorizedIntent context profile federation genesisHeight intent)
    (history : Durable) (_bound : context.sourceImage = some history.image) :
    Except RefusalReason (List UInt8) := do
  let .query query := intent.purpose | throw .malformed
  if present : 0 < intent.grants.length then
    let grant := intent.grants.get ⟨0, present⟩
    let checked := accepted.grants ⟨0, present⟩
    let state := context.authority.authState
    let reader := CredentialAuthorityState.readCapability context.authority.cell
      grant.kind grant.capability
    match query.view with
    | .resource => do
        -- The authorizing capability (the one this grant names) narrows the view.
        let some stored := reader | throw .malformed
        pure (resourceViewCodec.encode (resourceView stored.head.scope.fields
          checked.selected.packed checked.selected.accountBalances
          (if query.kind = .account then
            RunComputeView.load deployment context.view intent.subject else none)))
    | .resourceScope => do
        let some stored := reader | throw .malformed
        pure (resourceScopeViewCodec.encode (grant.kind, grant.capability.value,
          stored.head.scope.fields, resourceView stored.head.scope.fields
            checked.selected.packed checked.selected.accountBalances
            (if query.kind = .account then
              RunComputeView.load deployment context.view intent.subject else none)))
    | .policy => do
        let address := state.policyAddress ⟨grant.target⟩ (state.policyRevision ⟨grant.target⟩)
        let some source := CanonicalCellRegistry.loadPolicySource deployment.domain
            context.directory address | throw .malformed
        pure (PolicyRecordCodec.encode source.record)
    | .capability => do
        let some stored := reader | throw .malformed
        pure ((CredentialAuthorityEntryCodec.storedCapabilityStream grant.kind).encode stored)
    | .who => do
        let some stored := reader | throw .malformed
        let visible := sees state.parent stored.head query.target
        let height := genesisHeight + context.height
        let roster := members context grant.kind query.target height
        pure (whoViewCodec.encode ((holders context grant.kind query.target height).map fun subject =>
          (subject.value, (whoSeen history.index visible subject).map (genesisHeight + ·),
            decide (subject ∈ roster), grantsOf context grant.kind query.target height subject)))
    | .since after => do
        let some stored := reader | throw .malformed
        let visible := sees state.parent stored.head query.target
        pure (sinceViewCodec.encode (sinceFrom visible after (genesisHeight + 1) history.image.accepted))
    | .atHeight height =>
        atCovered (deployment := deployment) (durable := history) genesisHeight height intent.subject
          grant query.target
    | .tail start count =>
        match checked.selected.packed with
        | ⟨.stream, payload⟩ => do
            let some head := StreamCell.headOf payload.logical | throw .malformed
            pure (tailViewCodec.encode (payload.root, head.nextSeq,
              (StreamWrite.window deployment context.directory query.target head start count).map
                fun (sequence, entry) =>
                  (sequence, entry.record, streamPayload history.image.accepted query.target entry.record)))
        | _ => throw .malformed
    | .backlinks =>
        let visible := readable context intent.subject (genesisHeight + context.height)
        let keys := history.links.transclusionKeys ⟨⟨grant.target⟩⟩ ++
          targetKeys checked.selected.packed grant.target
        pure (linkViewCodec.encode (true,
          (history.links.backlinks visible keys).map (linkRow genesisHeight)))
    | .links =>
        pure (linkViewCodec.encode (false,
          (history.links.links ⟨grant.target⟩).map fun entry => linkRow genesisHeight (⟨grant.target⟩, entry)))
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

/-- The scope and narrowed payload come from the exact selected grant in the
admitted current observation context, rather than two separately read heads. -/
theorem AuthorizedIntent.queryResult_resourceScope
    {context : Context deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {federation : FederationId} {genesisHeight : Nat} {intent : Intent}
    (accepted : AuthorizedIntent context profile federation genesisHeight intent)
    {history : Durable} {bound : context.sourceImage = some history.image}
    (query : Query) (purpose : intent.purpose = .query query)
    (view : query.view = .resourceScope) (present : 0 < intent.grants.length)
    (stored : CredentialAuthorityState.StoredCapability (intent.grants.get ⟨0, present⟩).kind)
    (read : CredentialAuthorityState.readCapability context.authority.cell
      (intent.grants.get ⟨0, present⟩).kind
      (intent.grants.get ⟨0, present⟩).capability = some stored) :
    accepted.queryResult history bound = .ok (resourceScopeViewCodec.encode
      ((intent.grants.get ⟨0, present⟩).kind,
       (intent.grants.get ⟨0, present⟩).capability.value,
       stored.head.scope.fields,
       resourceView stored.head.scope.fields
         (accepted.grants ⟨0, present⟩).selected.packed
         (accepted.grants ⟨0, present⟩).selected.accountBalances
         (if query.kind = .account then
           RunComputeView.load deployment context.view intent.subject else none))) := by
  unfold AuthorizedIntent.queryResult
  simp only [purpose, view, dif_pos present, read]
  rfl

/-- The `at` view of a signed query is `atCovered` over the query's first grant. -/
theorem AuthorizedIntent.queryResult_at
    {context : Context deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {federation : FederationId} {genesisHeight : Nat} {intent : Intent}
    (accepted : AuthorizedIntent context profile federation genesisHeight intent)
    {history : Durable} {bound : context.sourceImage = some history.image}
    {query : Query} {height : Nat} (purpose : intent.purpose = .query query)
    (view : query.view = .atHeight height) (present : 0 < intent.grants.length) :
    accepted.queryResult history bound = atCovered (deployment := deployment) (durable := history)
      genesisHeight height intent.subject (intent.grants.get ⟨0, present⟩) query.target := by
  unfold AuthorizedIntent.queryResult
  simp only [purpose, view, dif_pos present]

/-- **`at_respects_coverage_at_height`**: a signed `at h` query that is
answered was answered to a grant the authority cell at `h` held, naming the
signer and standing over the target at `h`; the answer is the fold of the
prefix. A reader who was not in the room at `h` gets nothing at `h`. -/
theorem at_respects_coverage_at_height
    {context : Context deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {federation : FederationId} {genesisHeight : Nat} {intent : Intent}
    (accepted : AuthorizedIntent context profile federation genesisHeight intent)
    {history : Durable} {bound : context.sourceImage = some history.image}
    {query : Query} {height : Nat} {out : List UInt8} (purpose : intent.purpose = .query query)
    (view : query.view = .atHeight height) (answered : accepted.queryResult history bound = .ok out) :
    ∃ present : 0 < intent.grants.length, ∃ snapshot : CredentialAuthorityDomainReceiver.PhysicalSnapshot,
      ∃ authority : CredentialAuthorityDomainReceiver.Loaded deployment snapshot, ∃ stored,
      history.atPrefix (height - genesisHeight) = some snapshot ∧
      CredentialAuthorityDomainReceiver.loadDeployment deployment snapshot = some authority ∧
      CredentialAuthorityState.readCapability authority.snapshot.cell
        (intent.grants.get ⟨0, present⟩).kind (intent.grants.get ⟨0, present⟩).capability =
        some stored ∧
      stored.head.holder.Covers intent.subject ∧
      standing authority.snapshot.authState height query.target stored.head = true ∧
      out = atViewCodec.encode (height,
        atView stored.head.scope.fields (snapshot.canonicalBytes ⟨query.target⟩)) := by
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

theorem observation_request_actual_root (context : Context deployment)
    (semantics : Digest) (federation : FederationId) (height : Nat) (intent : Intent)
    (grant : GrantRef) (kind : CanonicalCellRegistry.Kind)
    (pre : Materialized (CanonicalCellRegistry.materializer kind)) :
    (request context semantics federation height intent grant pre.root).preStateRoot = pre.root := rfl

theorem observation_preserves_resource (context : Context deployment)
    (semantics : Digest) (federation : FederationId) (height : Nat) (intent : Intent)
    (grant : GrantRef) (kind : CanonicalCellRegistry.Kind)
    (pre : Materialized (CanonicalCellRegistry.materializer kind)) :
    (readCandidate context semantics federation height intent grant kind pre).post.logical = pre.logical :=
  (readCandidate context semantics federation height intent grant kind pre).postcondition

omit [DecidableEq F] in
theorem observation_policy_views_equal (context : Context deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId) (height : Nat)
    (intent : Intent) (grant : GrantRef) (selected : Selected context grant)
    (prepared : ReadPreparation context profile federation height intent grant selected) :
    (ResourceObservationAdmission.step prepared).oldState =
      (ResourceObservationAdmission.step prepared).newState :=
  ResourceObservationAdmission.policy_views_equal prepared

theorem CheckedGrant.current_generation_and_source
    {context : Context deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {federation : FederationId} {height : Nat} {intent : Intent} {grant : GrantRef}
    (checked : CheckedGrant context profile federation height intent grant) :
    let wanted := request context profile.semantics federation height intent grant checked.selected.packed.payload.root
    wanted.policyEpoch = context.authority.authState.policyEpoch wanted.policyId ∧
      wanted.policyRevision = context.authority.authState.policyRevision wanted.policyId :=
  ⟨checked.checked.authorization.policyEpochExact, checked.checked.authorization.policyRevisionExact⟩

/-- A version-5 resource view (no compute quote) refuses: its
frame is not the v6 frame. -/
theorem v5_view_refused (payload : List UInt8) :
    resourceViewCodec.decode ("DREGG/NATIVE-HOST/RESOURCE-VIEW/v5".toUTF8.toList ++ payload) =
      none := by
  have len : ("DREGG/NATIVE-HOST/RESOURCE-VIEW/v5".toUTF8.toList).length =
      resourceViewFrame.length := by decide +kernel
  have ne : "DREGG/NATIVE-HOST/RESOURCE-VIEW/v5".toUTF8.toList ≠ resourceViewFrame := by
    decide +kernel
  simp only [resourceViewCodec, NativeHostCodec.framed, ResourceBirthCodec.strictCodec,
    NativeHostCodec.framedRaw, ← len, List.take_left', ne, if_false]
  rfl

/-- A version-4 resource view (an unsalted root, no opening) refuses: its
frame is not the v6 frame. -/
theorem v4_view_refused (payload : List UInt8) :
    resourceViewCodec.decode ("DREGG/NATIVE-HOST/RESOURCE-VIEW/v4".toUTF8.toList ++ payload) =
      none := by
  have len : ("DREGG/NATIVE-HOST/RESOURCE-VIEW/v4".toUTF8.toList).length =
      resourceViewFrame.length := by decide +kernel
  have ne : "DREGG/NATIVE-HOST/RESOURCE-VIEW/v4".toUTF8.toList ≠ resourceViewFrame := by
    decide +kernel
  simp only [resourceViewCodec, NativeHostCodec.framed, ResourceBirthCodec.strictCodec,
    NativeHostCodec.framedRaw, ← len, List.take_left', ne, if_false]
  rfl

/-- The earlier unsalted v3 resource view also cannot decode as the current view. -/
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

/-- A version-1 at-height view (no opening) refuses. -/
theorem v1_at_view_refused (payload : List UInt8) :
    atViewCodec.decode ("DREGG/NATIVE-HOST/AT-VIEW/v1".toUTF8.toList ++ payload) = none := by
  have len : ("DREGG/NATIVE-HOST/AT-VIEW/v1".toUTF8.toList).length = atViewFrame.length := by
    decide +kernel
  have ne : "DREGG/NATIVE-HOST/AT-VIEW/v1".toUTF8.toList ≠ atViewFrame := by
    decide +kernel
  simp only [atViewCodec, NativeHostCodec.framed, ResourceBirthCodec.strictCodec,
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
    {context : Context deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {federation : FederationId} {height : Nat} {intent : Intent}
    (accepted : AuthorizedIntent context profile federation height intent) :
    footprintExact context intent = .ok () := accepted.footprint

/-- A grant naming an absent slot is not selected. -/
theorem select_absent (context : Context deployment) (grant : GrantRef)
    (absent : context.directory.slots grant.target = .absent) :
    select context grant = none := by
  unfold select
  split
  · rfl
  · rename_i packed present
    rw [absent] at present
    cases present

/-- **The refuting pole, kept as the authenticated half.** The challenge itself still reads
the target: for a single-grant intent whose footprint matches, an absent target is refused
(`noGrant`, told as `undisclosed` by `preAuthentication`), while a present one is issued.
Before FIX-DISCLOSE this was op 4's whole answer, to any key; now only an authenticated
subject reaches it (`authorize`, `NativeHost.challengeAnswer`). -/
theorem challenge_absent_target_refused (context : Context deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId)
    (genesisHeight : Nat) (intent : Intent) (intentSignature : List UInt8) (grant : GrantRef)
    (single : intent.grants = [grant]) (foot : footprintExact context intent = .ok ())
    (clock : ClockCellDomain.Loaded deployment context.cells)
    (clockLoaded : ClockCellDomain.load deployment context.cells = some clock)
    (absent : context.directory.slots grant.target = .absent) :
    (challenge context profile federation genesisHeight intent intentSignature).mapError
      preAuthentication = .error (.of .undisclosed) := by
  unfold challenge
  simp only [clockLoaded, need, bind, Except.bind]
  unfold challengeAt
  simp only [foot, single, headerAt, select_absent context grant absent, need, List.mapM_cons,
    bind, Except.bind, Except.mapError, pure, Except.pure]
  rfl

/-- **Challenge binding (DATAMODEL §3.4).**  A challenge carries the world root
and the height of the one loaded image it was computed from. -/
theorem challengeAt_bound {context : Context deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {federation : FederationId}
    {genesisHeight : Nat} {intent : Intent} {clock : ClockCell.Clock} {issued : Challenge} {intentSignature : List UInt8}
    (h : challengeAt context profile federation genesisHeight intent clock intentSignature = .ok issued) :
    issued.worldRoot = context.worldRoot ∧
      issued.height = genesisHeight + context.height ∧
      issued.clockNow = clock.now ∧ issued.clockSlot = clock.slot := by
  unfold challengeAt at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · simp only [Except.ok.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl, rfl⟩

/-- The clock a successful challenge names is the loaded snapshot's clock cell. -/
theorem challenge_names_clock {context : Context deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {federation : FederationId}
    {genesisHeight : Nat} {intent : Intent} {issued : Challenge} {intentSignature : List UInt8}
    (h : challenge context profile federation genesisHeight intent intentSignature = .ok issued) :
    ∃ clock, ClockCellDomain.load deployment context.cells = some clock ∧
      issued.worldRoot = context.worldRoot ∧
      issued.height = genesisHeight + context.height ∧
      issued.clockNow = clock.clock.now ∧ issued.clockSlot = clock.clock.slot := by
  unfold challenge at h
  cases loaded : ClockCellDomain.load deployment context.cells with
  | none => simp [need, loaded, bind, Except.bind] at h
  | some clock =>
    simp only [need, loaded, bind, Except.bind] at h
    exact ⟨clock, rfl, challengeAt_bound h⟩

theorem challenge_bound {context : Context deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {federation : FederationId}
    {genesisHeight : Nat} {intent : Intent} {issued : Challenge} {intentSignature : List UInt8}
    (h : challenge context profile federation genesisHeight intent intentSignature = .ok issued) :
    issued.worldRoot = context.worldRoot ∧
      issued.height = genesisHeight + context.height := by
  obtain ⟨_, _, world, height, _⟩ := challenge_names_clock h
  exact ⟨world, height⟩

/-- **`read_judged_at_named_clock`**: every grant of an authorized read was
judged by its law at exactly the clock its challenge names (the clock cell of
the snapshot at the challenge's world root and height).  With
`ResourceObservationAdmission.read_law_sees_clock`, the answer names the
`clock/now` and `clock/slot` the law saw. -/
theorem read_judged_at_named_clock {context : Context deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {federation : FederationId}
    {genesisHeight : Nat} {intent : Intent}
    (accepted : AuthorizedIntent context profile federation genesisHeight intent)
    (index : Fin intent.grants.length) :
    (accepted.grants index).preparation.clock.clock.now = accepted.suppliedChallenge.clockNow ∧
      (accepted.grants index).preparation.clock.clock.slot = accepted.suppliedChallenge.clockSlot := by
  obtain ⟨clock, loaded, _, _, now, slot⟩ := challenge_names_clock accepted.challengeExact
  have same : (accepted.grants index).preparation.clock = clock :=
    Option.some.inj ((accepted.grants index).preparation.clockLoaded.symm.trans loaded)
  rw [same, now, slot]
  exact ⟨rfl, rfl⟩

#assert_axioms resourceScopeView_roundtrip
#assert_axioms AuthorizedIntent.queryResult_resourceScope
#assert_axioms challenge_names_clock
#assert_axioms read_judged_at_named_clock

/-- info: 'Minidregg.Kernel.NativeObservationController.challenge_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms challenge_bound

/-- info: 'Minidregg.Kernel.NativeObservationController.transclusion_backlinks_view_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.transclusion_backlinks_view_complete

end Minidregg.Kernel.NativeObservationController
/-- info: 'Minidregg.Kernel.NativeObservationController.v4_view_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.v4_view_refused
/-- info: 'Minidregg.Kernel.NativeObservationController.v1_at_view_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.v1_at_view_refused
/-- info: 'Minidregg.Kernel.NativeObservationController.root_opens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.root_opens
/-- info: 'Minidregg.Kernel.NativeObservationController.selected_narrowed_is_blinded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.selected_narrowed_is_blinded
/-- info: 'Minidregg.Kernel.NativeObservationController.streamPayload_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.streamPayload_sound
/-- info: 'Minidregg.Kernel.NativeObservationController.v1_tail_view_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.v1_tail_view_refused
/-- info: 'Minidregg.Kernel.NativeObservationController.v3_view_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeObservationController.v3_view_refused
