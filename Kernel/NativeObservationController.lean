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
abbrev PageCell := DeclaredResourceController.PageCell

/-- Both source loaders retain their provenance from precisely this image. -/
structure Context (deployment : Deployment) (durable : Durable) where
  directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded deployment.authorityAnchor durable.snapshot

variable {deployment : Deployment} {durable : Durable}

private def refused : String := "observation refused"

private def need {α : Type} : Option α → Except String α
  | none => .error refused
  | some value => .ok value

private def require (condition : Bool) : Except String Unit :=
  if condition then .ok () else .error refused

def observeVerb : (kind : ResourceKind) → Verb kind
  | .object => .observeObject
  | .account => .observeAccount
  | .program => .observeProgram

def book (context : Context deployment durable) : Option CanonicalResourceKernel.Book := do
  let observed ← ResourceBirthController.Concrete.observeCell deployment
    context.directory.directory deployment.resourceBookId .resourceBook
  CanonicalResourcePageMaterializer.bookAt observed.payload.logical

/-- A computable restriction whose value at each asset is definitionally the
selected account's balance, with no dependence on any other account's value. -/
def accountBalanceMap (value : CanonicalResourceKernel.Book) (account : Nat) : Π₀ _ : Nat, Int :=
  DFinsupp.comapDomain' (fun asset => (account, asset))
    (h' := Prod.snd) (fun _ => rfl) value.balances

/-- Canonical sparse entries sorted by asset. Zero has the Book's ordinary
sparse meaning; the tuple contains no other account identifier. -/
def accountCut (value : CanonicalResourceKernel.Book) (account : Nat) : List (Nat × Int) :=
  CanonicalResourcePageMaterializer.entries (accountBalanceMap value account)

theorem accountBalanceMap_exact (value : CanonicalResourceKernel.Book) (account asset : Nat) :
    accountBalanceMap value account asset = value.balance account asset := rfl

/-- Arbitrary changes to every other balance, account list and lease record
cannot change the selected private account view. -/
theorem accountCut_noninterference (left right : CanonicalResourceKernel.Book) (account : Nat)
    (same : ∀ asset, left.balance account asset = right.balance account asset) :
    accountCut left account = accountCut right account := by
  have equal : accountBalanceMap left account = accountBalanceMap right account := by
    ext asset
    exact same asset
  unfold accountCut
  rw [equal]

def balanceStream : StreamCodec (List (Nat × Int)) :=
  StreamCodec.list (StreamCodec.product StreamCodec.nat CanonicalResourcePageMaterializer.intStream)

def balances (context : Context deployment durable) (grant : GrantRef) : Option (List (Nat × Int)) :=
  if grant.kind = .account then do
    let value ← book context
    some (accountCut value grant.target)
  else some []

abbrev Target := ResourceKind × Nat

def declaredKind (context : Context deployment durable) (target : Nat) : Option ResourceKind :=
  match context.directory.directory.slots target with
  | .present ⟨.declaredObject, _⟩ => some .object
  | .present ⟨.accountMetadata, _⟩ => some .account
  | .present ⟨.declaredProgram, _⟩ => some .program
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
      pure [(command.kind, command.target)]
  | .prepare (.delegate bytes) =>
      let command ← need (CapabilityDelegationController.commandCodec.decode bytes)
      require (command.2.subject == intent.subject)
      -- Observing another grant must not expose this named parent's lineage.
      require (intent.grants.all fun grant => grant.capability == command.2.declaration.parentId)
      pure [(command.1, command.2.declaration.target.value)]
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

def footprintExact (context : Context deployment durable) (intent : Intent) : Except String Unit := do
  let required ← requiredTargets context intent
  require (intent.grants.map (fun grant => (grant.kind, grant.target)) == required)

def bindingBytes (context : Context deployment durable) (semantics : Digest)
    (intent : Intent) (grant : GrantRef) : List UInt8 :=
  (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream grantStream)))).encode
      (deployment.domain, semantics,
        NativeHostCodec.imageBoundary deployment.domain semantics durable.image,
        intentIdentity intent, grant)

def effectIdentity (context : Context deployment durable) (semantics : Digest)
    (intent : Intent) (grant : GrantRef) : Digest :=
  (Sp800185Cshake256.hash "DREGG.NATIVE-HOST.OBSERVE-EFFECT/v1".toUTF8.toList
    (bindingBytes context semantics intent grant)).digest

def marker (context : Context deployment durable) (semantics : Digest)
    (intent : Intent) (grant : GrantRef) : Nat :=
  (Sp800185Cshake256.hash "DREGG.NATIVE-HOST.OBSERVE-SIGNATURE/v1".toUTF8.toList
    (bindingBytes context semantics intent grant)).digest.value

def request (context : Context deployment durable) (semantics : Digest)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (pre : PageCell) : Request grant.kind where
  domain := deployment.domain
  semantics := semantics
  federation := federation
  subject := intent.subject
  subjectKeyEpoch := context.authority.snapshot.authState.subjectKeyEpoch intent.subject
  target := ⟨grant.target⟩
  verb := observeVerb grant.kind
  argsDigest := intentIdentity intent
  effectsDigest := effectIdentity context semantics intent grant
  nonce := intent.nonce
  height := genesisHeight + durable.image.accepted.length
  preStateRoot := pre.root
  policyId := ⟨grant.target⟩
  policyEpoch := context.authority.snapshot.authState.policyEpoch ⟨grant.target⟩
  policyRevision := context.authority.snapshot.authState.policyRevision ⟨grant.target⟩
  cost := (intentCodec.encode intent).length

def readFamily (context : Context deployment durable) (semantics : Digest)
    (federation : FederationId) (genesisHeight : Nat) (grant : GrantRef) (pre : PageCell) :
    SemanticEffectFamily DeclaredEffectPageMaterializer.schema
      DeclaredEffectPageMaterializer.materializer Unit where
  Declaration := Intent
  declarationCodec := intentCodec
  pre := pre
  request := fun intent => ⟨grant.kind, request context semantics federation genesisHeight intent grant pre⟩
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => CredentialAuthorityEffects.unitCodec
  ModeEvidence := fun _ _ => Unit
  Postcondition := fun _ _ logical => logical = pre.logical
  effectDigest := fun intent => effectIdentity context semantics intent grant
  patch := fun _ _ => ResourceBirthPolicyController.factoryPatch pre
  nullifier := fun _ _ => none
  Release := fun _ _ => Empty
  DeclassificationAuthority := fun _ _ => Empty
  ReleaseAuthorization := fun _ _ _ => Empty
  DisclosureAllowed := fun _ _ _ => True

def readCandidate (context : Context deployment durable) (semantics : Digest)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (pre : PageCell) :
    PolicyInstall.Candidate (readFamily context semantics federation genesisHeight grant pre) pre intent () :=
  match checked : validate DeclaredEffectPageMaterializer.materializer pre
      (ResourceBirthPolicyController.factoryPatch pre) with
  | .accepted validated =>
      { preStateBound := rfl, modeEvidence := (), validated := validated
        postcondition := by
          change ({ fields := pre.logical.fields, resources := pre.logical.resources } :
            LogicalState DeclaredEffectPageMaterializer.schema) = pre.logical
          rfl }
  | .rejected _ => False.elim (by
      simp [validate, ResourceBirthPolicyController.factoryPatch, Patch.namedFields,
        Patch.namedResources] at checked)

structure Selected (context : Context deployment durable) (grant : GrantRef) where
  private mk ::
  packed : PackedCell CanonicalCellRegistry.registry
  present : context.directory.directory.slots grant.target = .present packed
  page : PageCell
  selected : CanonicalCellRegistry.selectDeclared deployment grant.target grant.kind packed = some page
  accountBalances : List (Nat × Int)
  balancesExact : balances context grant = some accountBalances

def select (context : Context deployment durable) (grant : GrantRef) : Option (Selected context grant) :=
  match present : context.directory.directory.slots grant.target with
  | .absent => none
  | .present packed =>
      match selected : CanonicalCellRegistry.selectDeclared deployment grant.target grant.kind packed with
      | none => none
      | some page =>
          match exact : balances context grant with
          | none => none
          | some values => some ⟨packed, present, page, selected, values, exact⟩

def project (context : Context deployment durable) (semantics : Digest)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (selected : Selected context grant)
    (logical : LogicalState DeclaredEffectPageMaterializer.schema) : Minidregg.Pred.State :=
  ⟨CanonicalRuntimeProfile.requestSlots
      (request context semantics federation genesisHeight intent grant selected.page) ++
    DeclaredResourceController.bytesSlots "intent/bytes" 0 (intentCodec.encode intent) ++
    DeclaredResourceController.bytesSlots "resource/bytes" 0
      (DeclaredEffectPageMaterializer.materializer.codec.encode logical) ++
    DeclaredResourceController.bytesSlots "account/bytes" 0 (balanceStream.encode selected.accountBalances) ++
    selected.accountBalances.map (fun pair => (s!"account/balance/{pair.1}", pair.2))⟩

def step (context : Context deployment durable) (semantics : Digest)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (selected : Selected context grant) : PolicyStepContext :=
  PolicyStepContext.ofCandidate
    (project context semantics federation genesisHeight intent grant selected) semantics
    (readCandidate context semantics federation genesisHeight intent grant selected.page)

variable {F : Type} [Field F] [DecidableEq F]

def policyConfig (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (selected : Selected context grant) : CanonicalPolicyConfig F :=
  CredentialAuthorityPolicyRegistry.config profile.compilerProfile context.authority.snapshot
    (DeclaredResourceController.sourceStore deployment.domain context.directory.directory)
    (sourceCapabilityPortal context.authority.snapshot (marker context profile.semantics intent grant))
    (step context profile.semantics federation genesisHeight intent grant selected)

def portal (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (selected : Selected context grant) : Portal :=
  (policyConfig context profile federation genesisHeight intent grant selected).portal

def authorizeSelected (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (selected : Selected context grant)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot) :
    Except String (Authorized (portal context profile federation genesisHeight intent grant selected)
      context.authority.snapshot.authState
      (request context profile.semantics federation genesisHeight intent grant selected.page)) := do
  let wanted := request context profile.semantics federation genesisHeight intent grant selected.page
  let config := policyConfig context profile federation genesisHeight intent grant selected
  let evidence ← need (sourceCapabilityOnlyEvidence profile.compilerProfile context.authority.snapshot
    (DeclaredResourceController.sourceStore deployment.domain context.directory.directory)
    (marker context profile.semantics intent grant)
    (step context profile.semantics federation genesisHeight intent grant selected)
    wanted grant.capability signature)
  let committed ← need (config.registry.resolve wanted.policyId wanted.policyRevision)
  let witness := canonicalWitness profile.compilerProfile.compiler committed
    (step context profile.semantics federation genesisHeight intent grant selected).oldState
    (step context profile.semantics federation genesisHeight intent grant selected).newState
  need (CanonicalPolicyAdmission.admit config context.authority.snapshot.authState wanted
    evidence witness (.policy wanted.policyId wanted.policyRevision) rfl rfl)

attribute [irreducible] portal

structure CheckedGrant (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent) (grant : GrantRef) where
  private mk ::
  selected : Selected context grant
  signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot
  authorization : Authorized (portal context profile federation genesisHeight intent grant selected)
    context.authority.snapshot.authState
    (request context profile.semantics federation genesisHeight intent grant selected.page)
  authorized : authorizeSelected context profile federation genesisHeight intent grant selected signature = .ok authorization

def header (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent) (grant : GrantRef) :
    Except String CredentialSignedEnvelopeController.SignedHeader := do
  let selected ← need (select context grant)
  (CredentialSignatureAdmission.signingHeader context.authority.snapshot
    (marker context profile.semantics intent grant)
    ⟨grant.kind, request context profile.semantics federation genesisHeight intent grant selected.page⟩).mapError
      (fun _ => refused)

/-- The success payload contains no field values, balances or policy source.
The selected public KeyRecord is reversibly encoded in the existing registry
binding in each header; this binding is not claimed to hide enrollment data. -/
def challenge (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent) : Except String Challenge := do
  footprintExact context intent
  let headers ← intent.grants.mapM fun grant => do
    let value ← header context profile federation genesisHeight intent grant
    pure (CredentialSignedEnvelopeController.headerCodec.encode value)
  pure ⟨intent, deployment.domain, profile.semantics, federation,
    NativeHostCodec.imageBoundary deployment.domain profile.semantics durable.image,
    genesisHeight + durable.image.accepted.length, headers⟩

def checkGrant (native : CredentialSignatureIO.NativeConfig)
    (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent)
    (grant : GrantRef) (signature : List UInt8) :
    IO (Except String (CheckedGrant context profile federation genesisHeight intent grant)) := do
  let some selected := select context grant | return .error refused
  let .ok actualHeader := header context profile federation genesisHeight intent grant | return .error refused
  let envelope := CredentialSignatureAdmission.canonicalEnvelopeCodec.encode ⟨actualHeader, signature⟩
  match ← CredentialSignatureAdmission.verifyNative native context.authority.snapshot
      (marker context profile.semantics intent grant)
      (request context profile.semantics federation genesisHeight intent grant selected.page) envelope with
  | .error _ => return .error refused
  | .ok receipt =>
      match exact : authorizeSelected context profile federation genesisHeight intent grant selected receipt with
      | .error _ => return .error refused
      | .ok authorization => return .ok ⟨selected, receipt, authorization, exact⟩

structure AuthorizedIntent (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (federation : FederationId) (genesisHeight : Nat) (intent : Intent) where
  private mk ::
  suppliedChallenge : Challenge
  challengeExact : challenge context profile federation genesisHeight intent = .ok suppliedChallenge
  footprint : footprintExact context intent = .ok ()
  grants : (index : Fin intent.grants.length) →
    CheckedGrant context profile federation genesisHeight intent (intent.grants.get index)

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
          | .ok grants => return .ok ⟨signed.challenge, same ▸ derived, footprint, grants⟩
        else return .error refused
      else return .error refused

/-- This codec is a read view, not a writable Book/registry payload. -/
def resourceViewStream : StreamCodec (List UInt8 × List (Nat × Int)) :=
  StreamCodec.product bytesStream balanceStream

def resourceViewFrame : List UInt8 := "DREGG/NATIVE-HOST/RESOURCE-VIEW/v1".toUTF8.toList

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
    (grant : GrantRef) (pre : PageCell) :
    (request context semantics federation height intent grant pre).preStateRoot = pre.root := rfl

theorem observation_preserves_resource (context : Context deployment durable)
    (semantics : Digest) (federation : FederationId) (height : Nat) (intent : Intent)
    (grant : GrantRef) (pre : PageCell) :
    (readCandidate context semantics federation height intent grant pre).post.logical = pre.logical :=
  (readCandidate context semantics federation height intent grant pre).postcondition

theorem observation_policy_views_equal (context : Context deployment durable)
    (semantics : Digest) (federation : FederationId) (height : Nat) (intent : Intent)
    (grant : GrantRef) (selected : Selected context grant) :
    (step context semantics federation height intent grant selected).oldState =
      (step context semantics federation height intent grant selected).newState := by
  change project context semantics federation height intent grant selected selected.page.logical =
    project context semantics federation height intent grant selected
      (readCandidate context semantics federation height intent grant selected.page).post.logical
  rw [observation_preserves_resource]

theorem CheckedGrant.current_generation_and_source
    {context : Context deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {federation : FederationId} {height : Nat} {intent : Intent} {grant : GrantRef}
    (checked : CheckedGrant context profile federation height intent grant) :
    let wanted := request context profile.semantics federation height intent grant checked.selected.page
    wanted.policyEpoch = context.authority.snapshot.authState.policyEpoch wanted.policyId ∧
      wanted.policyRevision = context.authority.snapshot.authState.policyRevision wanted.policyId :=
  ⟨checked.authorization.policyEpochExact, checked.authorization.policyRevisionExact⟩

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
